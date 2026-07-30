#!/usr/bin/env python3
"""
Deterministic ELF/DWARF/CFG -> Elfling Program generator (milestone 4, generator+emission chunk).

Reads the validated DWARF sidecars (decoder/allocator/sink built strip=false; runtime built -g, each
byte-identical to the canonical stripped object), enumerates every emitted subprogram and every
inlined_subroutine, maps object-relative ranges to canonical-ELF PCs via the linker-map bases,
resolves readArray widths from DWARF call_line -> pinned source, matches function_instances to live catalog
FunctionIds, folds non-cataloged glue into the nearest cataloged ancestor (glue PCs already lie
inside that ancestor's ranges), builds the inline nesting from the cataloged-ancestor chain, and
emits deterministic JSON, a generated Lean `Program` module, and a Markdown source/function/CFG index.

Determinism: DWARF DIE order is fixed; ranges verbatim; PC map is a per-object constant add; catalog
match is by pinned name/width; output ordering is sorted. The Nix derivation runs it twice and
requires byte-identical output.
"""
import argparse, hashlib, json, re, subprocess, os

# The object -> objkind mapping used both to place `.text` from the canonical linker map and to key
# the sidecars. Basenames are the linked input objects as they appear in the pinned map.
MAP_OBJKIND = {"zesu-raw-ssz-allocator.o": "allocator",
               "zesu-raw-ssz-decoder.o": "decoder",
               "zesu-raw-ssz-sink.o": "sink"}
RUNTIME_MAP_OBJ = "riscv64_runtime.o"

def parse_linker_map(path):
    """Canonical object placement, parsed from the pinned linked ELF's linker map — never hardcoded.

    Returns (text_bases, runtime_func_base, bss_bases, symbol_addrs):
      * text_bases[objkind]         = the linked address of that object's `.text` section;
      * runtime_func_base[funcname] = the linked address of the runtime object's `.text.<funcname>`
                                      per-function section (each runtime routine is its own section);
      * bss_bases[objkind]          = the linked address of that object's `.bss` section (where its
                                      private statics — the decoder globals — are placed);
      * symbol_addrs[name]          = the linked address of a defined global symbol (e.g. the exported
                                      `zesu_raw_result`/`zesu_raw_error` accessors), used to locate the
                                      accessor instructions whose global references are Lean-checked.
    Only the placed sections under `Linker script and memory map` are read, so the discarded-input
    block (address 0, e.g. gc-sectioned `.text.memset`/`.text.memcmp`) is ignored. Relinking at a
    different text base changes only these numbers; the identities the generator emits do not depend
    on them, which is what the relocation acceptance test checks."""
    text_bases, runtime_func_base, bss_bases, symbol_addrs = {}, {}, {}, {}
    sect_re = re.compile(r'^\s+(\.(?:text|bss)(?:\.[\w.]+)?)\s+0x([0-9a-f]+)\s+0x([0-9a-f]+)\s+(\S+\.o)\s*$')
    # A defined symbol row: address then bare name, no size and no object path (the placement rows
    # for symbols the linker resolved, e.g. `                0x...13780                zesu_raw_error`).
    sym_re = re.compile(r'^\s+0x([0-9a-f]+)\s+([A-Za-z_]\w*)\s*$')
    started = False
    for ln in open(path):
        if not started:
            if ln.startswith("Linker script and memory map"): started = True
            continue
        m = sect_re.match(ln)
        if m:
            sect, addr, size, obj = m.group(1), int(m.group(2), 16), int(m.group(3), 16), os.path.basename(m.group(4))
            if sect == ".text" and obj in MAP_OBJKIND:
                text_bases[MAP_OBJKIND[obj]] = addr
            elif sect == ".bss" and obj in MAP_OBJKIND:
                bss_bases[MAP_OBJKIND[obj]] = (addr, size)
            elif sect.startswith(".text.") and obj == RUNTIME_MAP_OBJ:
                runtime_func_base[sect[len(".text."):]] = addr
            continue
        s = sym_re.match(ln)
        if s:
            symbol_addrs[s.group(2)] = int(s.group(1), 16)
    return text_bases, runtime_func_base, bss_bases, symbol_addrs

SRC_PREFIX = "/build/source/"
FILES = {"decoder": "src/stateless/stateless/ssz_raw.zig", "root": "src/zkvm/raw_decoder_root.zig",
         "allocator": "src/zkvm/raw_allocator.zig", "runtime": "targets/common/riscv64_runtime.c"}
EXTRACTOR_VERSION = "elfling-generator-v1"
DECODER_TEXT_SHA = "f946b25ea2a0d19ee82ade02ef14eebce363e16190bf54a117eea7eec7805d3b"

def source_file_of(qual):
    if qual.startswith("ssz_raw."): return FILES["decoder"]
    if qual.startswith("raw_decoder_root."): return FILES["root"]
    if qual.startswith("raw_allocator."): return FILES["allocator"]
    if qual in ("memcpy", "memmove"): return FILES["runtime"]
    return None

def excluded_category(qual):
    """Category for a reachable-but-uncovered emitted glue routine, or None to skip it.

    The two categories carry DIFFERENT soundness reasons (see the Lean reachable-partition module):
      reachableCleanupNoOp: a `*.deinit` error-path cleanup routine; the freestanding zkVM's allocator
        free is a no-op, so deinit never changes the accept/reject outcome.
      reachableStdlib: std/mem/math implementation reachable through the allocator vtable, whose net
        behavior is captured by the cataloged allocator contracts.
    Anything else (e.g. the unreachable `raw_sink.*` object) is not part of the reachable-excluded
    taxonomy and is skipped; the Lean partition proof is the guardrail that catches an over-narrow
    filter (a reachable PC that is neither covered nor emitted here fails the partition)."""
    if ".deinit" in qual:
        return "reachableCleanupNoOp"
    if qual.startswith("mem.") or qual.startswith("std.") or qual.startswith("math."):
        return "reachableStdlib"
    return None

def build_catalog():
    dec, root, alloc, rt = FILES["decoder"], FILES["root"], FILES["allocator"], FILES["runtime"]
    C, decl = set(), {}
    decs = ["decode","decodeRaw","decodeNewPayloadRequest","decodeExecutionPayload","decodeExecutionRequests",
            "decodeExecutionWitness","decodeChainConfig","decodeForkConfig","decodeForkActivation","decodeOptionalU64",
            "decodeOptionalBlobSchedule","decodeVersionedHashes","decodeWithdrawals","decodeDepositRequests",
            "decodeWithdrawalRequests","decodeConsolidationRequests","decodePublicKeys","decodeByteListList",
            "requireCanonicalOffsets","requireU32Length","readOffset","readU32","readU64","readU256","bytesAt",
            "hasExactErePrefix"]
    for n in decs: C.add((dec, "ssz_raw." + n, ()))
    for w in [20,32,48,65,96,256]: C.add((dec, "ssz_raw.readArray", (str(w),)))
    C.add((root, "raw_decoder_root.zesu_decode_raw", ()))
    C.add((root, "raw_decoder_root.zesu_raw_result", ())); C.add((root, "raw_decoder_root.zesu_raw_error", ()))
    C.add((alloc, "raw_allocator.zesu_raw_alloc", ())); C.add((rt, "memcpy", ())); C.add((rt, "memmove", ()))
    for n in ["allocatorAlloc","allocatorResize","allocatorRemap","allocatorFree","allocator"]:
        C.add((root, "raw_decoder_root." + n, ()))
    return C

CATALOG = build_catalog()

def intof(v):
    m = re.search(r'-?\d+', v or ""); return int(m.group()) if m else 0

# Value extractors for readelf `--debug-dump=info` attribute text.
def attr_name(v):
    # `(indirect string, offset: 0x...): NAME`  or  `NAME`
    return v.rsplit(": ", 1)[-1].strip()
def attr_ref(v):
    m = re.search(r'<0x([0-9a-f]+)>', v or ""); return int(m.group(1), 16) if m else None
def attr_hex(v):
    m = re.search(r'0x[0-9a-f]+|\b\d+\b', v or ""); return int(m.group(), 0) if m else None

class DIE:
    __slots__ = ("off","depth","tag","attrs","parent")
    def __init__(s, off, depth, tag): s.off, s.depth, s.tag, s.attrs, s.parent = off, depth, tag, {}, None

def parse_readelf(readelf, obj):
    """Returns (dies, name_of_off, ranges_map). Offline-safe: only needs `readelf`."""
    info = subprocess.run([readelf, "--debug-dump=info", obj], capture_output=True, text=True).stdout
    dies, stack, cur = [], [], None
    for ln in info.splitlines():
        m = re.match(r'\s*<(\d+)><([0-9a-f]+)>:\s*Abbrev Number:\s*\d+\s*\((DW_TAG_\w+)\)', ln)
        if m:
            depth = int(m.group(1)); d = DIE(int(m.group(2), 16), depth, m.group(3))
            while stack and stack[-1].depth >= depth: stack.pop()
            if stack: d.parent = stack[-1]
            stack.append(d); dies.append(d); cur = d
        elif cur is not None:
            am = re.match(r'\s*<[0-9a-f]+>\s+(DW_AT_\w+)\s*:\s*(.*)$', ln)
            if am: cur.attrs[am.group(1)] = am.group(2)
    name_of_off, declline_of_off = {}, {}
    for d in dies:
        nm = d.attrs.get("DW_AT_linkage_name") or d.attrs.get("DW_AT_name")
        if nm is not None: name_of_off[d.off] = attr_name(nm)
        if "DW_AT_decl_line" in d.attrs: declline_of_off[d.off] = intof(d.attrs["DW_AT_decl_line"])
    # range lists: `<offset> <lo> <hi>` grouped by the leading list offset
    ranges_map = {}
    rng = subprocess.run([readelf, "--debug-dump=Ranges", obj], capture_output=True, text=True).stdout
    for ln in rng.splitlines():
        m = re.match(r'\s*([0-9a-f]{8})\s+([0-9a-f]{16})\s+([0-9a-f]{16})\s*$', ln)
        if m:
            ranges_map.setdefault(int(m.group(1), 16), []).append((int(m.group(2), 16), int(m.group(3), 16)))
    return dies, name_of_off, ranges_map, declline_of_off

def decl_line_of(d, declline_of_off):
    """Real declaration line: an inlined_subroutine has none of its own, so read the concrete/abstract
    subprogram it originates from (via DW_AT_abstract_origin) — never a placeholder."""
    if "DW_AT_decl_line" in d.attrs: return intof(d.attrs["DW_AT_decl_line"])
    if "DW_AT_abstract_origin" in d.attrs:
        return declline_of_off.get(attr_ref(d.attrs["DW_AT_abstract_origin"]), 0)
    return 0

def function_instance_name(d, name_of_off):
    if d.tag == "DW_TAG_subprogram":
        nm = d.attrs.get("DW_AT_linkage_name") or d.attrs.get("DW_AT_name")
        return attr_name(nm) if nm is not None else None
    if d.tag == "DW_TAG_inlined_subroutine" and "DW_AT_abstract_origin" in d.attrs:
        return name_of_off.get(attr_ref(d.attrs["DW_AT_abstract_origin"]))
    return None

def die_ranges(d, ranges_map):
    if "DW_AT_ranges" in d.attrs:
        off = attr_hex(d.attrs["DW_AT_ranges"])
        return list(ranges_map.get(off, []))
    if "DW_AT_low_pc" in d.attrs and "DW_AT_high_pc" in d.attrs:
        lo = attr_hex(d.attrs["DW_AT_low_pc"]); hi = attr_hex(d.attrs["DW_AT_high_pc"])
        # readelf prints high_pc in the DWARF4 constant (offset-from-low_pc) form, so the end is lo+hi
        return [(lo, lo + hi)] if lo is not None and hi is not None else []
    return []

def canon(objkind, name, rs, text_bases, runtime_func_base):
    if objkind == "runtime":
        base = runtime_func_base.get(name)
        return None if base is None else [{"start": base+a, "size": b-a} for a,b in rs]
    base = text_bases.get(objkind)
    return None if base is None else [{"start": base+a, "size": b-a} for a,b in rs]

def readarray_width(d, srclines, consts):
    cl = intof(d.attrs.get("DW_AT_call_line"))
    if cl == 0 or cl > len(srclines): return None
    m = re.search(r'readArray\(\s*([A-Za-z0-9_]+)', srclines[cl-1])
    if not m: return None
    tok = m.group(1); return int(tok) if tok.isdigit() else consts.get(tok)

def norm_identity(name, d, srclines, consts):
    """(qualifiedName, specialization-tuple) or None if width unresolved."""
    if name.startswith("ssz_raw.readArray__anon"):
        w = readarray_width(d, srclines, consts)
        return None if w is None else ("ssz_raw.readArray", (str(w),))
    return (name, ())

# ---- CFG analysis (control-flow interface, area #2) --------------------------------------------
# The generator PROPOSES entries/exits/external-calls/basic-blocks/direct-edges from an objdump of the
# canonical linked ELF; the Lean validation checks every one against the Sail-decoded
# `controlFlowNodes` (the trusted source of truth). Classification mirrors `DecodedWord.controlTransfer`
# / `ControlTransfer.directTargets` exactly so the Lean completeness checks hold. RV64IM_Zicclsm has no
# compressed instructions, so every instruction is 4 bytes and the previous word is always at addr-4.
BRANCH_MNEMONICS = {'beq','bne','blt','bge','bltu','bgeu','bgt','ble','bgtu','bleu',
                    'beqz','bnez','bltz','bgez','blez','bgtz'}

def disassemble(objdump, elf):
    """addr -> (mnemonic, operands, comment_addr?) over every disassembled instruction."""
    txt = subprocess.run([objdump, "-d", "--no-show-raw-insn", elf], capture_output=True, text=True).stdout
    insns = {}
    for ln in txt.splitlines():
        m = re.match(r'^\s*([0-9a-f]+):\s+(\S+)\s*(.*)$', ln)
        if not m: continue
        addr, mnem, rest = int(m.group(1), 16), m.group(2), m.group(3)
        comment = None
        if '#' in rest:
            body, cmt = rest.split('#', 1)
            cm = re.search(r'([0-9a-f]+)', cmt); comment = int(cm.group(1), 16) if cm else None
            rest = body
        insns[addr] = (mnem, rest.strip(), comment)
    return insns

def _operand_target(ops):
    m = re.search(r'\b([0-9a-f]+)\s+<[^>]+>', ops)
    return int(m.group(1), 16) if m else None

def classify(addr, insns):
    """(kind, directTargets, callTarget?) mirroring the Lean control-transfer model. `directTargets`
    is exactly `ControlTransfer.directTargets`, so a resolved call yields [target, addr+4], an
    indirect/return/terminal yields [], a conditional yields [taken, addr+4]."""
    mnem, ops, comment = insns[addr]; nxt = addr + 4
    if mnem in BRANCH_MNEMONICS:
        t = _operand_target(ops); return ('conditional', [t, nxt] if t is not None else [nxt], None)
    if mnem == 'j':                                  # jal zero, target
        t = _operand_target(ops); return ('jump', [t] if t is not None else [], None)
    if mnem == 'jal':                                # jal ra, target  (rd = ra -> call)
        t = _operand_target(ops); return ('call', [t, nxt] if t is not None else [nxt], t)
    if mnem == 'ret':                                # jalr zero, 0(ra)
        return ('return', [], None)
    if mnem in ('jr', 'jalr'):
        # Decode rd/rs/imm and mirror `DecodedWord.controlTransfer` exactly:
        #   rd = zero: resolved -> jump [target]; imm==0 -> return []; else indirect [].
        #   rd != zero: resolved -> call [target, addr+4]; else indirectCall [].
        # (`jr rs` is `jalr zero, 0(rs)`, which Sail models as `.return_` — a transfer-out, not a
        # fall-through — so it MUST be classified as `return`, else exits are under-reported.)
        if mnem == 'jr':
            rd, imm = 'zero', 0
            sm = re.search(r'\b([a-z][a-z0-9]*)\b', ops); src = sm.group(1) if sm else None
        else:
            m = re.match(r'\s*(?:([a-z][a-z0-9]*)\s*,\s*)?(-?\d+)?\(([a-z][a-z0-9]*)\)', ops)
            if m:
                rd = m.group(1) or 'ra'; imm = int(m.group(2) or '0'); src = m.group(3)
            else:
                m2 = re.match(r'\s*([a-z][a-z0-9]*)\s*,\s*([a-z][a-z0-9]*)\s*$', ops)  # jalr rd,rs
                if m2:
                    rd, imm, src = m2.group(1), 0, m2.group(2)
                else:
                    rd, imm, src = 'ra', 0, ops.strip()                                 # jalr rs
        prev = insns.get(addr - 4)
        resolved = (prev is not None and prev[0] == 'auipc'
                    and prev[1].split(',')[0].strip() == src and comment is not None)
        if rd in ('zero', 'x0'):
            if resolved: return ('jump', [comment], None)
            if imm == 0:  return ('return', [], None)
            return ('indirect', [], None)
        if resolved: return ('call', [comment, nxt], comment)
        return ('indirectCall', [], None)            # unresolved indirect call: no direct targets
    if mnem in ('ecall', 'ebreak', 'mret', 'sret', 'wfi', 'unimp'):
        return ('terminal', [], None)
    return ('fallthrough', [nxt], None)

def region_pcs(regions):
    """Every 4-byte instruction PC in a list of {start,size} regions."""
    out = []
    for r in regions:
        out += list(range(r["start"], r["start"] + r["size"], 4))
    return out

def reachable_witnesses(entry, insns):
    """BFS the decoded direct-edge graph from `entry`, mirroring `directReachable`. Returns a list of
    {addr, distance, predecessor} rows (entry's predecessor is itself), sorted by address. Each row's
    `distance` strictly exceeds its predecessor's, so the predecessor chain is an acyclic path back to
    the entry — the witness that every reachable address is ACTUALLY reachable (the minimality that,
    with closure, makes the reachable set EXACT, not an over-approximation)."""
    from collections import deque
    dist = {entry: 0}; pred = {entry: entry}; q = deque([entry])
    while q:
        a = q.popleft()
        if a not in insns: continue
        _, tgts, _ = classify(a, insns)
        for t in tgts:
            if t not in dist:
                dist[t] = dist[a] + 1; pred[t] = a; q.append(t)
    return [{"addr": a, "distance": dist[a], "predecessor": pred[a]} for a in sorted(dist)]

def compute_function_instance_cfg(function_instances_sorted, insns):
    """Fill each function instance with generated CFG data proposed from the disassembly:
      exits          — PCs whose control leaves the function instance's regions (return/terminal, or a
                       CONTINUATION outside the regions); the real exits, never `max(endpoints)`. A
                       resolved call's continuation is its FALL-THROUGH, not its callee: control comes
                       back, so a call is an exit only in tail position;
      blocks         — an exact basic-block partition of the function instance's regions, split at fragment
                       starts, branch/jump/call/terminal successors, and in-region branch targets;
      edges          — every direct successor edge from a DEEPEST-owned PC (each edge attributed once);
      externalCalls  — resolved call sites DEEPEST-owned by the function instance, each -> the entry PC of the
                       emitted/excluded function_instance it targets (Q1: deepest-inline owner, emitted callee).
    Returns entry_to_callee so unresolved call targets can be surfaced as defects."""
    region_pc_sets = [set(region_pcs(function_instance["regions"])) for function_instance in function_instances_sorted]
    for i, function_instance in enumerate(function_instances_sorted):
        children_pcs = set()
        for c in function_instance["children"]:
            children_pcs |= region_pc_sets[c]
        R = region_pc_sets[i]
        owned = R - children_pcs

        exits = []
        for pc in sorted(R):
            if pc not in insns: continue
            kind, tgts, _ = classify(pc, insns)
            # A resolved call's continuation is its fall-through: control comes back. Counting the
            # callee edge here would make EVERY call site an exit, and `FunctionTrace.step` carries
            # `¬ exit pc`, so the caller's trace could never run past its own first call.
            cont = [pc + 4] if kind == 'call' else tgts
            if kind in ('return', 'terminal') or any(t not in R for t in cont):
                exits.append(pc)
        function_instance["exits"] = exits

        edges = []
        for pc in sorted(owned):
            if pc not in insns: continue
            _, tgts, _ = classify(pc, insns)
            for t in tgts:
                edges.append({"source": pc, "target": t})
        function_instance["edges"] = edges

    return region_pc_sets

def function_instance_blocks(function_instance, insns):
    """Exact basic-block partition of the function instance's regions (Q2): every region PC in exactly one
    block, blocks contiguous within a single fragment, no gaps/overlaps."""
    blocks = []
    for r in function_instance["regions"]:
        lo, hi = r["start"], r["start"] + r["size"]
        leaders = {lo}
        for pc in range(lo, hi, 4):
            if pc not in insns: continue
            kind, tgts, _ = classify(pc, insns)
            if kind == 'fallthrough':
                continue                                 # a fall-through never starts a new block
            if pc + 4 < hi:
                leaders.add(pc + 4)                      # instruction after a transfer starts a block
            for t in tgts:
                if t != pc + 4 and lo <= t < hi:
                    leaders.add(t)                       # an in-fragment branch/jump/call target
        cuts = sorted(leaders) + [hi]
        for a, b in zip(cuts, cuts[1:]):
            blocks.append({"start": a, "size": b - a})
    return blocks

def sibling_overlap_defects(function_instances_sorted):
    """Attribution defects decidable from the inline tree: two function instances claiming a common PC without
    one being inlined within the other. Inline nesting legitimately overlaps (a child's PCs lie inside
    its parent's), so ancestor/descendant pairs are excluded; anything else sharing a PC is ambiguous
    ownership the deepest-inline rule cannot resolve, surfaced as `overlappingOwnership` rather than
    dropped. Pure over the function instance list (no ELF/DWARF access) so it is directly unit-testable."""
    ancestors = [set() for _ in function_instances_sorted]
    for i, r in enumerate(function_instances_sorted):
        k = r["parentIdx"]
        while k is not None:
            ancestors[i].add(k); k = function_instances_sorted[k]["parentIdx"]
    def overlap_addr(a, b):
        for r in a["regions"]:
            for q in b["regions"]:
                if r["start"] < q["start"]+q["size"] and q["start"] < r["start"]+r["size"]:
                    return max(r["start"], q["start"])
        return None
    out = []
    for i in range(len(function_instances_sorted)):
        for j in range(i+1, len(function_instances_sorted)):
            if j in ancestors[i] or i in ancestors[j]: continue
            function_instance = overlap_addr(function_instances_sorted[i], function_instances_sorted[j])
            if function_instance is not None:
                out.append({"kind":"overlappingOwnership", "address":function_instance, "firstIdx":i, "secondIdx":j,
                            "first":function_instances_sorted[i]["qualified"], "second":function_instances_sorted[j]["qualified"]})
    return out

# ---- Decoder-global extraction -----------------------------------------------------------------
# The decoder keeps three observable private globals plus one internal flag in its `.bss`:
#   raw_decoder_root.attempted        (1 byte)  — set once a decode has been attempted
#   raw_decoder_root.allocator_state  (1 byte)  — internal allocator flag
#   raw_decoder_root.last_status      (4 bytes) — the 32-bit status `zesu_raw_error` returns
#   raw_decoder_root.stored_result  (848 bytes) — the result buffer `zesu_raw_result` points at
# Their offsets come from the sidecar decoder object's symbol table; their canonical linked addresses
# come from the pinned `.bss` base in the linker map. Nothing is hardcoded.
DECODER_GLOBAL_NAMES = ["raw_decoder_root.attempted", "raw_decoder_root.allocator_state",
                        "raw_decoder_root.last_status", "raw_decoder_root.stored_result"]
ACCESSOR_SYMBOLS = ["zesu_raw_error", "zesu_raw_result"]

def bss_section_index(readelf, obj):
    txt = subprocess.run([readelf, "-SW", obj], capture_output=True, text=True).stdout
    for ln in txt.splitlines():
        m = re.match(r'^\s*\[\s*(\d+)\]\s+(\.\S+)\s', ln)
        if m and m.group(2) == ".bss": return m.group(1)
    return None

def read_decoder_globals(readelf, decoder_obj, bss_base):
    """(name, canonical linked address, size) for each decoder global, offset from the sidecar symbol
    table and placed at the pinned `.bss` base. Emitted in the fixed `DECODER_GLOBAL_NAMES` order."""
    bss_idx = bss_section_index(readelf, decoder_obj)
    txt = subprocess.run([readelf, "-sW", decoder_obj], capture_output=True, text=True).stdout
    found = {}
    for ln in txt.splitlines():
        p = ln.split()
        if len(p) < 8 or p[3] != "OBJECT": continue
        if p[7] not in DECODER_GLOBAL_NAMES: continue
        if bss_idx is not None and p[6] != bss_idx: continue
        found[p[7]] = (int(p[1], 16), int(p[2], 0))  # (offset-in-.bss, size)
    missing = [n for n in DECODER_GLOBAL_NAMES if n not in found]
    if missing: raise SystemExit(f"decoder globals missing from sidecar symbol table: {missing}")
    return [(n, bss_base + found[n][0], found[n][1]) for n in DECODER_GLOBAL_NAMES]

def read_words(objdump, elf, lo, hi):
    """(pc -> (word, resolved-target?)) over a disassembled range of the pinned linked ELF."""
    txt = subprocess.run([objdump, "-d", f"--start-address={lo}", f"--stop-address={hi}", elf],
                         capture_output=True, text=True).stdout
    words = {}
    for ln in txt.splitlines():
        m = re.match(r'^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s+\S+\s*(.*)$', ln)
        if not m: continue
        rest, tgt = m.group(3), None
        cm = re.search(r'#\s*([0-9a-f]+)', rest)
        if cm: tgt = int(cm.group(1), 16)
        words[int(m.group(1), 16)] = (int(m.group(2), 16), tgt)
    return words

RISCV_RET = 0x00008067   # `ret` = `jalr x0, 0(x1)`, the terminating instruction of each accessor.

def read_accessor_refs(objdump, elf, symbol_addrs, bss_lo, bss_hi):
    """The exported accessors' instructions that reference the decoder `.bss`, as
    (accessor, pc, 32-bit word, resolved global target), from the pinned linked ELF. Each accessor is
    scanned from its symbol address up to and including its terminating `ret`, so one accessor's scan
    never bleeds into the next function. The Lean check re-reads each word from the canonical image
    and ties its resolved target to a generated global."""
    refs = []
    for sym in ACCESSOR_SYMBOLS:
        base = symbol_addrs.get(sym)
        if base is None: raise SystemExit(f"accessor symbol {sym} absent from linker map")
        words = read_words(objdump, elf, base, base + 0x40)
        for pc in sorted(words):
            word, tgt = words[pc]
            if tgt is not None and bss_lo <= tgt < bss_hi:
                refs.append((sym, pc, word, tgt))
            if word == RISCV_RET: break
    refs.sort(key=lambda r: (r[0], r[1]))
    return refs

# The allocator/heap runtime globals, read directly from the pinned linked ELF symbol table (defined
# symbols with fixed addresses): the heap region and the bump cursor/limit the allocator mutates.
RUNTIME_GLOBAL_NAMES = ["ZKVM_HEAP_TOP", "ZKVM_HEAP_POS", "heap"]

def read_runtime_globals(readelf, elf):
    """(name, canonical linked address, size) for each allocator/heap runtime global, from the pinned
    linked ELF's symbol table. Emitted in the fixed `RUNTIME_GLOBAL_NAMES` order."""
    txt = subprocess.run([readelf, "-sW", elf], capture_output=True, text=True).stdout
    found = {}
    for ln in txt.splitlines():
        p = ln.split()
        if len(p) < 8 or p[3] != "OBJECT": continue
        if p[7] not in RUNTIME_GLOBAL_NAMES: continue
        found[p[7]] = (int(p[1], 16), int(p[2], 0))
    missing = [n for n in RUNTIME_GLOBAL_NAMES if n not in found]
    if missing: raise SystemExit(f"runtime globals missing from ELF symbol table: {missing}")
    return [(n, found[n][0], found[n][1]) for n in RUNTIME_GLOBAL_NAMES]

# ---- Per-function_instance ABI/binding extraction (from DWARF .debug_loc) ------------------------------
# Every function instance's formal parameters have an entry-time location — the register, stack slot, or
# memory the argument lives in when the function instance is entered. Emitted function instances carry their real
# (optimized) ABI; inlined function instances carry function-instance-specific locations that may not be the source
# ABI. Both are resolved from `.debug_loc`, which in this relocatable object shares the object-relative
# PC space of the DIE ranges (verified: a loclist entry begins at the same offset as its function instance's
# range). An argument with no location valid at entry is a first-class `unresolved` binding.

def decode_loc_expr(expr):
    """A single DWARF location expression -> (kind, reg, offset).
    kind in {reg, fbreg, addr, breg, const, other}; reg is a DWARF/RISC-V x-register number (0-31)."""
    m = re.match(r'DW_OP_reg(\d+)\b', expr)
    if m: return ("reg", int(m.group(1)), 0)
    m = re.match(r'DW_OP_fbreg:\s*(-?\d+)', expr)
    if m: return ("fbreg", -1, int(m.group(1)))     # reg filled from the frame base by the caller
    m = re.match(r'DW_OP_addr\s+0x([0-9a-f]+)', expr)
    if m: return ("addrValue" if "stack_value" in expr else "addr", -1, int(m.group(1), 16))
    m = re.match(r'DW_OP_breg(\d+)\s*\([^)]*\):\s*(-?\d+)', expr)
    if m:
        return ("bregValue" if "stack_value" in expr else "breg",
                int(m.group(1)), int(m.group(2)))
    # Preserve the value of a genuine constant.  Merely calling every stack-value expression
    # `const` loses information: DWARF also uses DW_OP_stack_value for register-plus-offset values.
    m = re.fullmatch(r'DW_OP_lit(\d+);\s*DW_OP_stack_value', expr)
    if m: return ("const", -1, int(m.group(1)))
    m = re.fullmatch(r'DW_OP_const[us]:\s*(-?\d+);\s*DW_OP_stack_value', expr)
    if m: return ("const", -1, int(m.group(1)))
    return ("other", -1, 0)

def parse_debug_loc(readelf, obj):
    """loclist-key -> [(begin, end, expr)] over `.debug_loc`. A loclist is keyed by the offset of its
    first entry; entries accumulate until `<End of list>`. PCs are object-relative."""
    txt = subprocess.run([readelf, "--debug-dump=loc", obj], capture_output=True, text=True).stdout
    locs, key = {}, None
    for ln in txt.splitlines():
        m = re.match(r'^\s*([0-9a-f]{8})\s+([0-9a-f]{16})\s+([0-9a-f]{16})\s+\((.*)\)\s*$', ln)
        if m:
            off, begin, end, expr = int(m.group(1),16), int(m.group(2),16), int(m.group(3),16), m.group(4)
            if key is None: key = off
            locs.setdefault(key, []).append((begin, end, expr))
        elif re.search(r'<End of list>', ln):
            key = None
    return locs

def frame_base_reg_of(d):
    """The x-register the function instance's frame is based on, from the enclosing concrete subprogram's
    `DW_AT_frame_base` (a `DW_OP_regN`); -1 if it is the CFA or otherwise not a plain register."""
    p = d
    while p is not None:
        fb = p.attrs.get("DW_AT_frame_base")
        if fb is not None:
            m = re.search(r'DW_OP_reg(\d+)\b', fb)
            return int(m.group(1)) if m else -1
        p = p.parent
    return -1

# ---- Binding PROVENANCE -------------------------------------------------------------------------
#
# HOW a raw binding row's location was obtained, recorded beside the row so a consumer can refuse one
# it does not trust. The generator used to record all four of the located cases identically, which
# made a SUBSTITUTED location indistinguishable from one DWARF actually stated at the entry PC.
#
# The substitution is real and load-bearing: when no location-list entry covers the function
# instance's ENTRY PC, `resolve_binding` falls back to the earliest entry merely OVERLAPPING its
# ranges. That expression is what the compiler said somewhere INSIDE the instance, not at its entry.
# For a compile-time constant that is usually — but not provably — the same value; for a register
# expression (`DW_OP_breg27 (s11): 88; DW_OP_stack_value`) the base register need not still hold the
# same value at entry, so the row states a machine fact the artifact never established.
#
# These values are mutually exclusive and total over the raw table: every row carries exactly one.
PROV_AT_ENTRY   = "dwarfLocationAtEntry"        # a location-list entry covers the entry PC
PROV_SINGLE     = "dwarfSingleLocation"         # one DW_AT_location expression, valid over the whole scope
PROV_NOT_AT_ENTRY = "dwarfLocationNotAtEntry"   # SUBSTITUTED: earliest merely-OVERLAPPING loclist entry
PROV_LOCLIST_UNREADABLE = "dwarfLoclistUnreadable"  # DW_AT_location names a list this extractor read as empty
PROV_LOCATION_ABSENT = "dwarfLocationAbsent"    # the concrete parameter DIE carries no DW_AT_location
PROV_PARAMETER_ABSENT = "dwarfParameterAbsent"  # the concrete instance omits the parameter DIE entirely
PROV_UNPARSED   = "dwarfLocationUnparsed"       # DW_AT_location present, neither a loclist nor a parsable block

# The provenances under which the row carries NO location at all, i.e. exactly the `callerProvided`
# rows. Kept here so the Lean inventory can check the two tables agree instead of assuming it.
PROV_ABSENCES = (PROV_LOCLIST_UNREADABLE, PROV_LOCATION_ABSENT, PROV_PARAMETER_ABSENT, PROV_UNPARSED)

def resolve_binding(loc_attr, locs, function_instance_ranges, frame_reg):
    """(kind, reg, offset, provenance) of one parameter over the function instance.

    Prefer the location valid exactly at the entry PC; else the earliest location overlapping the
    function instance's ranges; else `callerProvided` (the optimizer emitted no location — the
    argument flows from the caller). `fbreg` is rewritten to the enclosing frame-base register.
    `unresolved` is reserved for an undecodable expression.

    The substituted case is NOT dropped and NOT silently promoted: it keeps whatever the overlapping
    entry said, tagged `dwarfLocationNotAtEntry` so the count stays auditable and a consumer that
    requires an entry-time fact can refuse it."""
    def finish(k, r, function_instance, prov):
        if k == "other": return ("unresolved", r, function_instance, prov)
        return (k, frame_reg if k == "fbreg" else r, function_instance, prov)
    entry_obj = function_instance_ranges[0][0]
    if "location list" in loc_attr:
        entries = locs.get(int(loc_attr.split()[0], 0), [])
        covering = [x for (b, e, x) in entries if b <= entry_obj < e]
        if covering: return finish(*decode_loc_expr(covering[0]), PROV_AT_ENTRY)
        overlap = sorted([(b, x) for (b, e, x) in entries
                          if any(b < re2 and rb < e for (rb, re2) in function_instance_ranges)])
        if overlap: return finish(*decode_loc_expr(overlap[0][1]), PROV_NOT_AT_ENTRY)
        return ("callerProvided", -1, 0, PROV_LOCLIST_UNREADABLE)
    m = re.search(r'\((DW_OP_[^)]*(?:\([^)]*\)[^)]*)*)\)\s*$', loc_attr)   # inline "N byte block: .. (DW_OP_..)"
    if m: return finish(*decode_loc_expr(m.group(1)), PROV_SINGLE)
    return ("callerProvided", -1, 0, PROV_UNPARSED)

def index_dies(dies):
    """(offset -> DIE, id(parent) -> [children]) so a function instance can reach its abstract origin's
    formal parameters. DIEs carry a `parent` link but no child list."""
    by_off, children = {}, {}
    for d in dies:
        by_off[d.off] = d
        if d.parent is not None:
            children.setdefault(id(d.parent), []).append(d)
    return by_off, children


def signature_params(d, dies_by_off, children_of, name_of_off):
    """The COMPLETE formal parameter list of the routine function instance `d` realizes, in signature order,
    taken from its abstract-origin subprogram DIE.

    An optimized concrete function instance may omit a `DW_TAG_formal_parameter` child entirely — not merely
    leave it without a location. Enumerating only the concrete function instance's children therefore produced a
    binding table that was silently SHORT: four `bytesAt` function_instances had no `offset` row and the
    `readU64`/`readArray` function_instances enclosing them had no rows at all, so Row A recorded them as
    "paramless" when their routines plainly take parameters. The abstract origin always carries the
    full signature, so it is the authority for WHICH parameters exist; the concrete function instance is the
    authority for WHERE each one lives."""
    origin = d
    if "DW_AT_abstract_origin" in d.attrs:
        origin = dies_by_off.get(attr_ref(d.attrs["DW_AT_abstract_origin"]), d)
    names = []
    for c in children_of.get(id(origin), ()):
        if c.tag != "DW_TAG_formal_parameter":
            continue
        nm = c.attrs.get("DW_AT_name")
        if nm is not None:
            names.append(attr_name(nm))
        elif "DW_AT_abstract_origin" in c.attrs:
            names.append(name_of_off.get(attr_ref(c.attrs["DW_AT_abstract_origin"]), f"arg{len(names)}"))
        else:
            names.append(f"arg{len(names)}")
    return names


def function_instance_bindings(d, dies, name_of_off, locs, function_instance_ranges, dies_by_off=None, children_of=None):
    """The entry-time (name, kind, reg, offset, provenance) of every formal parameter of the routine
    function instance `d` REALIZES — one row per signature parameter, never a short table.

    A parameter the concrete function instance located is resolved from `.debug_loc`. A parameter the concrete
    function instance carries WITHOUT a location is `callerProvided`. A parameter the concrete function instance omits
    entirely is ALSO `callerProvided` — a declared row the recovery pass can act on, rather than an
    absence that later stages cannot distinguish from a genuinely paramless routine.

    The fifth field says HOW the location was obtained (see `PROV_*`). It is what separates a
    location DWARF stated at the ENTRY PC from one substituted from elsewhere in the instance, and it
    distinguishes the two shapes of absence the caller-provided rows collapse together."""
    frame_reg = frame_base_reg_of(d)
    out, seen = [], {}
    for i, c in enumerate(dies):
        if c.parent is not d or c.tag != "DW_TAG_formal_parameter": continue
        nm = c.attrs.get("DW_AT_name")
        pname = attr_name(nm) if nm is not None else (
            name_of_off.get(attr_ref(c.attrs["DW_AT_abstract_origin"]), f"arg{i}")
            if "DW_AT_abstract_origin" in c.attrs else f"arg{i}")
        loc = c.attrs.get("DW_AT_location")
        if loc is None:
            row = (pname, "callerProvided", -1, 0, PROV_LOCATION_ABSENT)
        else:
            row = (pname, *resolve_binding(loc, locs, function_instance_ranges, frame_reg))
        seen[pname] = row
        out.append(row)
    if children_of is None or dies_by_off is None:
        return out
    # Re-emit in signature order, inserting a declared row for every parameter the function instance omitted.
    sig = signature_params(d, dies_by_off, children_of, name_of_off)
    if not sig:
        return out
    ordered = [seen.get(p, (p, "callerProvided", -1, 0, PROV_PARAMETER_ABSENT)) for p in sig]
    ordered += [r for r in out if r[0] not in sig]     # never drop a row DWARF did emit
    return ordered

# The pinned Zig call sites recover values that optimized DWARF omits.  These are deliberately
# narrow: only the reader chain used by this decoder and the emitted C memmove ABI are accepted.
# A new missing-location shape fails generation instead of acquiring a guessed source ABI.
READER_ARG_INDEX = {
    "ssz_raw.readOffset": {"offset": 1},
    "ssz_raw.readU32": {"offset": 1},
    "ssz_raw.readU64": {"offset": 1},
    "ssz_raw.readU256": {"offset": 1},
    "ssz_raw.readArray": {"offset": 2},
    "ssz_raw.bytesAt": {"offset": 1, "len": 2},
}

def source_call_args(srclines, line, column):
    """Top-level argument strings for the call beginning at DWARF line/column.

    Zig call sites in the reader chain are small, but some span lines.  Start at the DWARF column,
    find the first `(`, then split commas while tracking nested (), [], and {}.  Strings do not occur
    in these calls; rejecting an unterminated call is safer than guessing.
    """
    if line <= 0 or line > len(srclines): return None
    text = "\n".join(srclines[line - 1:line + 12])
    start = max(column - 1, 0)
    op = text.find("(", start)
    if op < 0: return None
    args, token = [], []
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack = []
    for ch in text[op + 1:]:
        if ch in pairs:
            stack.append(pairs[ch]); token.append(ch)
        elif stack and ch == stack[-1]:
            stack.pop(); token.append(ch)
        elif ch == ")" and not stack:
            args.append("".join(token).strip())
            return args
        elif ch == "," and not stack:
            args.append("".join(token).strip()); token = []
        else:
            token.append(ch)
    return None

# NOTE: completing a signature from the pinned Zig source was tried and REJECTED. A function instance's
# `declLine` does not reliably point at its own `fn` declaration — `zesu_raw_result`'s resolves into a
# different file at an unrelated function — so parsing `fn name(...)` there invents parameters that do
# not exist. Inventing a parameter is strictly worse than omitting one, so the signature authority is
# DWARF's abstract origin (see `signature_params`) and nothing else. Where the abstract origin lists no
# formal parameters, the function instance is recorded as DWARF-paramless and that limitation is stated,
# rather than papered over with a guess.

# ---- Loop-derived reader offsets (the `decodeWithdrawals` reader chain) -------------------------
#
# `readU64(data, offset + 8)` inside `for (result, 0..) |*entry, index| { const offset = index *
# WITHDRAWAL_SIZE; ... }` has an argument that is neither a compile-time constant nor a location DWARF
# recorded: it is the loop's running byte offset. Recording it as an absent/`unlocated` row is NOT
# adequate — a consumer that quantifies over the rows to build the function instance's entry PRECONDITION then
# gets an unsatisfiable conjunct, and every implication out of that precondition becomes vacuous.
#
# The offset is not unknown, though: the compiler keeps `index * STRIDE` in a loop-carried register, so
# the argument's real relation `index * STRIDE + k` IS realized by the machine. These rules recover
# that register from the loaded image so the row can say exactly what holds:
#
#   * the loop is the natural loop (over the disassembled direct-edge CFG) whose body contains the
#     function instance's entry PC and is the smallest such;
#   * a candidate register is written EXACTLY once in that loop, by `addi r, r, STRIDE` — a basic
#     induction variable stepping by the pinned source stride;
#   * the candidate must be ZERO on entry to the loop, established on every incoming edge either by a
#     literal-zero definition or by a `bnez r` / `beqz r` guard whose taken edge leads into the loop;
#   * exactly one candidate must survive — an ambiguous or absent one is a generation FAILURE, never a
#     guess.
#
# A call site is taken to clobber exactly the caller-saved registers, i.e. the RISC-V C ABI holds across
# it — the same assumption `riscvCAbiArg2` already relies on. Without it no candidate survives a loop
# containing a call (this one calls `memmove`), and with a weaker assumption the analysis would be
# unsound rather than merely silent.
#
# The recovered row is `("derived", register, k)`; `derivedBindings` records the stride, the pinned
# source constant it came from, and the loop, so the derivation is auditable rather than asserted.
ABI_REG_NUMBER = {
    "zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7, "s0": 8, "fp": 8,
    "s1": 9, "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15, "a6": 16, "a7": 17,
    "s2": 18, "s3": 19, "s4": 20, "s5": 21, "s6": 22, "s7": 23, "s8": 24, "s9": 25, "s10": 26,
    "s11": 27, "t3": 28, "t4": 29, "t5": 30, "t6": 31,
}
# Registers the RISC-V C ABI requires a callee to preserve; every other register is assumed clobbered
# across a call site.
CALLEE_SAVED_REGS = {"sp", "gp", "tp", "s0", "fp", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8",
                     "s9", "s10", "s11"}
STORE_MNEMONICS = {"sb", "sh", "sw", "sd", "fsw", "fsd", "sc.w", "sc.d"}
NO_DEST_MNEMONICS = STORE_MNEMONICS | BRANCH_MNEMONICS | {
    "j", "ret", "jr", "nop", "ecall", "ebreak", "unimp", "fence", "fence.i", "mret", "sret", "wfi"}

def written_regs(addr, insns):
    """The ABI register names an instruction may write, or `None` when that cannot be decided.

    `None` (rather than an empty set) is the conservative answer: a caller treating an undecodable
    instruction as writing nothing would silently keep a candidate the instruction may have clobbered."""
    mnem, ops, _ = insns[addr]
    if mnem in NO_DEST_MNEMONICS:
        return set()
    if mnem in ("jal", "jalr"):
        # A call: the link register plus every caller-saved register. `j`/`jr`/`ret` are already
        # handled above (they link to `zero`).
        return (set(ABI_REG_NUMBER) - CALLEE_SAVED_REGS)
    dest = ops.split(",", 1)[0].strip()
    if dest in ABI_REG_NUMBER:
        return {dest}
    return None

def _direct_preds(insns):
    """pc -> set of pcs whose decoded direct targets include it (the same edges `classify` proposes)."""
    preds = {}
    for a in insns:
        for t in classify(a, insns)[1]:
            preds.setdefault(t, set()).add(a)
    return preds

def _natural_loop_body(header, latch, preds):
    """The natural loop of back edge `latch -> header`: the header plus every node that reaches the
    latch without passing through the header."""
    body = {header, latch}
    stack = [latch]
    while stack:
        n = stack.pop()
        for p in preds.get(n, ()):
            if p not in body:
                body.add(p)
                stack.append(p)
    return body

def innermost_loop(entry_pc, insns, preds):
    """(header, latch, body) of the smallest natural loop containing `entry_pc`, or None."""
    best = None
    for latch in sorted(insns):
        for header in classify(latch, insns)[1]:
            if header > latch or header not in insns:
                continue                       # only a backward transfer can close a loop
            body = _natural_loop_body(header, latch, preds)
            if entry_pc in body and (best is None or len(body) < len(best[2])):
                best = (header, latch, body)
    return best

def _branch_register(mnem, ops):
    """The register a zero-test branch compares, and whether the TAKEN edge means `reg == 0`."""
    parts = [p.strip() for p in ops.split(",")]
    if mnem == "beqz" and len(parts) == 2:
        return parts[0], True
    if mnem == "bnez" and len(parts) == 2:
        return parts[0], False
    if mnem in ("beq", "bne") and len(parts) == 3:
        if parts[1] in ("zero", "x0"):
            return parts[0], mnem == "beq"
        if parts[0] in ("zero", "x0"):
            return parts[1], mnem == "beq"
    return None, None

def _writes_literal_zero(mnem, ops, reg):
    """Whether the instruction definitely assigns the literal 0 to `reg`."""
    parts = [p.strip() for p in ops.split(",")]
    if not parts or parts[0] != reg:
        return False
    if mnem == "li" and len(parts) == 2 and parts[1] == "0":
        return True
    if mnem == "mv" and len(parts) == 2 and parts[1] in ("zero", "x0"):
        return True
    if mnem in ("addi", "add") and len(parts) == 3 and parts[1] in ("zero", "x0") \
            and parts[2] in ("0", "zero", "x0"):
        return True
    return False

def zero_on_entry_edge(reg, source, header, insns, preds, limit=4096):
    """Whether `reg == 0` holds on the edge `source -> header`, walking back along a straight line.

    Two sound witnesses are accepted: a definition that assigns the literal 0, and a zero-test branch
    whose outgoing edge we took. The walk stops (conservatively answering False) at the first join
    point, the first undecodable instruction, or any other definition of `reg`."""
    pc, nxt, steps = source, header, 0
    while steps < limit and pc in insns:
        mnem, ops, _ = insns[pc]
        breg, taken_is_zero = _branch_register(mnem, ops)
        if breg == reg:
            target = _operand_target(ops)
            took_taken_edge = (target == nxt)
            if took_taken_edge == taken_is_zero:
                return True
            return False                       # the edge we took proves reg != 0
        if _writes_literal_zero(mnem, ops, reg):
            return True
        w = written_regs(pc, insns)
        if w is None or reg in w:
            return False                       # some other (or undecodable) definition reaches here
        prev = pc - 4
        if preds.get(pc, set()) != {prev} or prev not in insns:
            return False                       # a join point: the straight-line walk is over
        if nxt not in classify(prev, insns)[1] and pc not in classify(prev, insns)[1]:
            return False
        pc, nxt, steps = prev, pc, steps + 1
    return False

def loop_stride_register(entry_pc, stride, insns, preds):
    """The unique loop-carried register holding `index * stride` at `entry_pc`, or (None, reason)."""
    loop = innermost_loop(entry_pc, insns, preds)
    if loop is None:
        return None, "no natural loop contains the function instance's entry pc"
    header, latch, body = loop
    writes = {}
    for pc in sorted(body):
        w = written_regs(pc, insns)
        if w is None:
            return None, f"undecodable instruction at {pc} in the loop body"
        for r in w:
            writes.setdefault(r, []).append(pc)
    candidates = []
    for r, sites in sorted(writes.items()):
        if len(sites) != 1:
            continue
        mnem, ops, _ = insns[sites[0]]
        parts = [p.strip() for p in ops.split(",")]
        if mnem == "addi" and len(parts) == 3 and parts[0] == r and parts[1] == r \
                and parts[2] == str(stride):
            candidates.append(r)
    entries = sorted(p for p in preds.get(header, ()) if p not in body)
    if not entries:
        return None, "the loop header has no entry edge from outside the loop"
    zeroed = [r for r in candidates
              if all(zero_on_entry_edge(r, p, header, insns, preds) for p in entries)]
    if len(zeroed) != 1:
        return None, (f"expected exactly one zero-initialized +{stride} induction register in the loop "
                      f"[{header},{latch}]; found {zeroed} among candidates {candidates}")
    return (ABI_REG_NUMBER[zeroed[0]], header, latch), None

LOOP_OFFSET_EXPR = re.compile(r"^\s*(\w+)\s*(?:\+\s*(\d+)\s*)?$")

def loop_offset_source(expr, call_line, srclines, consts):
    """`(variable, stride, stride-constant name, constant)` for a reader argument of the pinned shape
    `<var>` / `<var> + <int>` where the enclosing Zig function defines `const <var> = <x> * <STRIDE>;`.

    Anything else returns None: the recovery is deliberately narrow, so a new missing-location shape
    fails generation instead of acquiring a guessed relation."""
    if not expr:
        return None
    m = LOOP_OFFSET_EXPR.match(expr)
    if not m:
        return None
    var, addend = m.group(1), int(m.group(2) or 0)
    line = call_line
    if line <= 0 or line > len(srclines):
        return None
    pattern = re.compile(r"^\s*(?:const|var)\s+" + re.escape(var) + r"\s*(?::[^=]+)?=\s*"
                         r"(\w+)\s*\*\s*(\w+)\s*;")
    for idx in range(line - 1, max(line - 60, 0) - 1, -1):
        text = srclines[idx]
        if re.match(r"^\s*(?:pub\s+)?fn\s", text):
            return None                         # left the enclosing function without a definition
        m2 = pattern.match(text)
        if not m2:
            continue
        rhs = m2.group(2)
        stride = consts.get(rhs, int(rhs) if rhs.isdigit() else None)
        if stride is None or stride <= 0:
            return None
        return (var, stride, rhs if not rhs.isdigit() else "", addend)
    return None

def recover_missing_bindings(function_instances_sorted, srclines, consts, insns):
    """Return per-function-instance effective bindings and an audit table of every recovery.

    A recovered constant is represented as `(const, -1, value)`; a recovered machine register as
    `(reg, register, 0)`.  Forwarded reader parameters are solved by a fixed point over the generated
    parent relation.  This makes the resolved table usable by function instance preconditions while retaining
    the raw DWARF table separately.
    """
    effective = [list(function_instance.get("bindings", [])) for function_instance in function_instances_sorted]
    recoveries = []
    derived = {}                # (function_instance, parameter) -> audit row
    preds = _direct_preds(insns)
    loop_cache = {}

    def known(i, name):
        for pn, kind, reg, off in effective[i]:
            if pn == name and kind != "callerProvided": return (kind, reg, off)
        return None

    def derive_from_loop(i, function_instance, pname, expr):
        """The loop-carried `index * STRIDE` register realizing this reader's `offset` argument."""
        src = loop_offset_source(expr, function_instance["callLine"], srclines, consts)
        if src is None:
            return None
        var, stride, stride_name, addend = src
        key = (function_instance["entryPc"], stride)
        if key not in loop_cache:
            loop_cache[key] = loop_stride_register(function_instance["entryPc"], stride, insns, preds)
        found, why = loop_cache[key]
        if found is None:
            raise SystemExit(
                f"GENERATION FAILURE: function_instance {i} ({function_instance['qualified']}) takes `{pname} = {expr}` with "
                f"`{var} = index * {stride}` from the pinned source, but the loop-induction recovery "
                f"could not pin the register: {why}")
        reg, header, latch = found
        derived[(i, pname)] = (i, pname, reg, stride, addend, expr, stride_name, header, latch)
        return ("derived", reg, addend)

    changed = True
    while changed:
        changed = False
        for i, function_instance in enumerate(function_instances_sorted):
            for j, (pname, kind, reg, off) in enumerate(effective[i]):
                if kind != "callerProvided": continue
                resolved = None
                reason = None
                if function_instance["qualified"] == "memmove" and pname == "n" and function_instance["kind"] == "emitted":
                    resolved, reason = ("reg", 12, 0), "riscvCAbiArg2"
                elif function_instance["qualified"] in READER_ARG_INDEX:
                    args = source_call_args(srclines, function_instance["callLine"], function_instance["callColumn"])
                    arg_idx = READER_ARG_INDEX[function_instance["qualified"]].get(pname)
                    expr = args[arg_idx].strip() if args is not None and arg_idx is not None and arg_idx < len(args) else None
                    if expr is not None and re.fullmatch(r"\d+", expr):
                        resolved, reason = ("const", -1, int(expr)), "sourceLiteral"
                    elif expr == "N" and function_instance["parentIdx"] is not None:
                        parent = function_instances_sorted[function_instance["parentIdx"]]
                        if parent["qualified"] == "ssz_raw.readArray" and parent["specialization"]:
                            resolved, reason = ("const", -1, int(parent["specialization"][0])), "readArrayWidth"
                    elif expr is not None and function_instance["parentIdx"] is not None:
                        inherited = known(function_instance["parentIdx"], expr)
                        if inherited is not None:
                            resolved, reason = inherited, "forwardedParentParam"
                            if inherited[0] == "derived":
                                # The parent's argument IS this parameter, so the child inherits the
                                # same loop register, stride and constant — audited under its own key.
                                p = derived[(function_instance["parentIdx"], expr)]
                                derived[(i, pname)] = (i, pname) + p[2:]
                    if resolved is None and expr is not None:
                        # Not a constant, not forwarded from an already-resolved parent: the last
                        # narrow rule is the loop-carried `index * STRIDE` induction register.
                        resolved = derive_from_loop(i, function_instance, pname, expr)
                        reason = "loopInductionOffset" if resolved is not None else None
                if resolved is not None:
                    effective[i][j] = (pname, *resolved)
                    recoveries.append((i, pname, reason, resolved[0], resolved[1], resolved[2]))
                    changed = True

    # EVERY declared parameter must now carry a machine meaning: a concrete DWARF location, a recovered
    # constant/register, or a `derived` loop relation. A row that survives to here would silently make
    # the function instance's generated entry PRECONDITION unsatisfiable in the consumer, so it is a hard
    # generation failure — never an artifact with a hole in it.
    stuck = [(i, function_instances_sorted[i]["qualified"], pname, kind)
             for i, rows in enumerate(effective)
             for (pname, kind, _r, _o) in rows if kind in ("callerProvided", "unresolved")]
    if stuck:
        raise SystemExit("GENERATION FAILURE: parameters with no machine meaning after recovery: "
                         + json.dumps(stuck))
    return effective, sorted(recoveries), sorted(derived.values())

def emit_globals_lean(bss_base, bss_size, globals_, accessor_refs, runtime_globals, decoder_sha):
    L = ["-- GENERATED FILE: produced by tools/generate_elfling_program.py (--out-globals). DO NOT EDIT.",
         "-- Untrusted extracted data: the decoder's private globals and the allocator/heap runtime",
         "-- globals (canonical linked addresses and sizes), plus the accessor instructions that",
         "-- reference the decoder globals. Validated in Lean by",
         "-- BinaryFv/SSZ/Zesu/Elfling/GeneratedDecoderGlobals.lean against the pinned canonical image.",
         "namespace BinaryFv.SSZ.Zesu.Elfling.GeneratedDecoderGlobals",
         f"def decoderTextSha : String := {lean_str(decoder_sha)}",
         f"def bssBase : Nat := {bss_base}",
         f"def bssSize : Nat := {bss_size}",
         "/-- (symbol name, canonical linked address, size in bytes), in declaration order. -/",
         "def globals : List (String × Nat × Nat) :="]
    L.append("  [" + ", ".join(f'({lean_str(n)}, {a}, {s})' for (n, a, s) in globals_) + "]")
    L.append("/-- (allocator/heap runtime symbol, canonical linked address, size in bytes). -/")
    L.append("def runtimeGlobals : List (String × Nat × Nat) :=")
    L.append("  [" + ", ".join(f'({lean_str(n)}, {a}, {s})' for (n, a, s) in runtime_globals) + "]")
    L.append("/-- (accessor symbol, instruction pc, 32-bit little-endian word, resolved global target). -/")
    L.append("def accessorRefs : List (String × Nat × Nat × Nat) :=")
    L.append("  [" + ", ".join(f'({lean_str(acc)}, {pc}, {w}, {t})' for (acc, pc, w, t) in accessor_refs) + "]")
    L.append("end BinaryFv.SSZ.Zesu.Elfling.GeneratedDecoderGlobals")
    return "\n".join(L) + "\n"

def emit_bindings_lean(function_instances_sorted, effective, recoveries, derived):
    L = ["-- GENERATED FILE: produced by tools/generate_elfling_program.py (--out-bindings). DO NOT EDIT.",
         "-- Untrusted extracted data: the entry-time ABI/binding of every function instance's formal",
         "-- parameters, resolved from DWARF .debug_loc at each function instance's entry PC. Validated in",
         "-- Lean by BinaryFv/SSZ/Zesu/Elfling/GeneratedBindings.lean.",
         "namespace BinaryFv.SSZ.Zesu.Elfling.GeneratedBindings",
         "-- Rows are (function_instance index, parameter name, location kind, register-or-address,",
         "-- offset-or-value). The final field is the concrete value for const and the base offset",
         "-- otherwise.",
         "/-- Raw DWARF rows, retained so recovery never hides what the compiler actually emitted. -/",
         "def rawBindings : List (Nat × String × String × Int × Int) :="]
    rows = [f'({i}, {lean_str(pname)}, {lean_str(kind)}, {reg}, {off})'
            for i, function_instance in enumerate(function_instances_sorted)
            for (pname, kind, reg, off) in function_instance.get("bindings", [])]
    L.append("  [" + ",\n   ".join(rows) + "]")
    L.extend(["/-- Effective rows after deterministic pinned-source/ABI recovery. For `const`, the",
              "final field is the concrete value; for `reg`, the fourth field is the register. -/"])
    L.append("def bindings : List (Nat × String × String × Int × Int) :=")
    rows = [f'({i}, {lean_str(pname)}, {lean_str(kind)}, {reg}, {off})'
            for i, bs in enumerate(effective) for (pname, kind, reg, off) in bs]
    L.append("  [" + ",\n   ".join(rows) + "]")
    L.append("/-- Parameters whose source argument is a LOOP-DERIVED value `index * stride + constant`.")
    L.append("DWARF recorded no location for them, but the compiled loop keeps `index * stride` in a")
    L.append("loop-carried register, so the row states that relation instead of leaving a hole. Fields:")
    L.append("(function_instance, parameter, register, stride, constant, pinned source expression, the pinned")
    L.append("source constant the stride came from, loop header pc, loop latch pc). -/")
    L.append("def derivedBindings : List (Nat × String × Nat × Nat × Nat × String × String × Nat × Nat) :=")
    rows = [f'({i}, {lean_str(p)}, {reg}, {stride}, {const}, {lean_str(expr)}, {lean_str(sname)}, '
            f'{header}, {latch})'
            for (i, p, reg, stride, const, expr, sname, header, latch) in derived]
    L.append("  [" + ",\n   ".join(rows) + "]")
    L.append("/-- (function_instance, parameter, recovery reason, effective kind, register, value/offset). -/")
    L.append("def recoveredBindings : List (Nat × String × String × String × Int × Int) :=")
    rows = [f'({i}, {lean_str(p)}, {lean_str(reason)}, {lean_str(kind)}, {reg}, {off})'
            for (i, p, reason, kind, reg, off) in recoveries]
    L.append("  [" + ",\n   ".join(rows) + "]")
    L.append("/-- **How each raw row's location was obtained**, in the SAME order as `rawBindings` and")
    L.append("with the same `(function_instance, parameter)` key, so no row is dropped and the counts")
    L.append("stay auditable. `dwarfLocationNotAtEntry` is the SUBSTITUTED case: no location-list entry")
    L.append("covered the function instance's entry PC, so the extractor used the earliest entry merely")
    L.append("OVERLAPPING its ranges. That is what the compiler said somewhere inside the instance, not")
    L.append("at its entry — a consumer that needs an entry-time fact must refuse it rather than read")
    L.append("it as DWARF evidence. -/")
    L.append("def rawBindingProvenance : List (Nat × String × String) :=")
    rows = [f'({i}, {lean_str(pname)}, {lean_str(prov)})'
            for i, function_instance in enumerate(function_instances_sorted)
            for (pname, prov) in function_instance.get("bindingProvenance", [])]
    L.append("  [" + ",\n   ".join(rows) + "]")
    L.append("/-- The provenances under which the row carries no location at all — exactly the")
    L.append("`callerProvided` raw rows. -/")
    L.append("def absenceProvenances : List String :=")
    L.append("  [" + ", ".join(lean_str(p) for p in PROV_ABSENCES) + "]")
    L.append("/-- The provenances under which DWARF stated the location AT the entry PC: a location-list")
    L.append("entry covering it, or a single expression valid over the whole scope. -/")
    L.append("def atEntryProvenances : List String :=")
    L.append("  [" + ", ".join(lean_str(p) for p in (PROV_AT_ENTRY, PROV_SINGLE)) + "]")
    L.append("end BinaryFv.SSZ.Zesu.Elfling.GeneratedBindings")
    return "\n".join(L) + "\n"

def emit_bindings_json(function_instances_sorted, effective, recoveries, derived):
    """The SAME binding tables as `--out-bindings`, as JSON.

    `program.json`'s per-function-instance `bindings` are the RAW DWARF rows, which still carry the 61
    `callerProvided` gaps. Any consumer that wants the *effective* entry placement of a function instance's
    parameters — Row C's production-ELF binding validator, for one — must read the recovered table, not
    the raw one, or it silently validates against a location DWARF never gave. Emitting it here keeps
    one generator as the single source of truth for both the Lean inventory and the binary evidence."""
    return json.dumps({
        "raw": [{"function_instance": i, "name": p, "kind": k, "reg": r, "value": v}
                for i, function_instance in enumerate(function_instances_sorted) for (p, k, r, v) in function_instance.get("bindings", [])],
        "effective": [{"function_instance": i, "name": p, "kind": k, "reg": r, "value": v}
                      for i, bs in enumerate(effective) for (p, k, r, v) in bs],
        "recovered": [{"function_instance": i, "name": p, "reason": reason, "kind": k, "reg": r, "value": v}
                      for (i, p, reason, k, r, v) in recoveries],
        "derived": [{"function_instance": i, "name": p, "register": reg, "stride": stride,
                     "constant": const, "sourceExpr": expr, "strideConstant": sname,
                     "loopHeader": header, "loopLatch": latch}
                    for (i, p, reg, stride, const, expr, sname, header, latch) in derived],
        # HOW each raw row's location was obtained, keyed the same way as `raw` and in the same
        # order. `dwarfLocationNotAtEntry` marks a location the extractor SUBSTITUTED from elsewhere
        # in the instance because none covered its entry PC.
        "provenance": [{"function_instance": i, "name": p, "provenance": prov}
                       for i, function_instance in enumerate(function_instances_sorted)
                       for (p, prov) in function_instance.get("bindingProvenance", [])],
    }, indent=1, sort_keys=True) + "\n"

def main():
    ap = argparse.ArgumentParser()
    for k in ["readelf","decoder","allocator","sink","runtime","source"]: ap.add_argument("--"+k, required=True)
    # the runtime C source lives in the proof repo (targets/common/riscv64_runtime.c), not the zesu
    # source tree, so its content hash is supplied separately.
    ap.add_argument("--runtime-c", required=True)
    # canonical placement comes from the pinned linked ELF's linker map, never hardcoded bases.
    ap.add_argument("--map", required=True)
    # the canonical linked ELF + its objdump drive the control-flow interface (entries/exits/calls/
    # blocks/edges), proposed here and validated in Lean against the Sail-decoded CFG.
    ap.add_argument("--elf", required=True)
    ap.add_argument("--objdump", required=True)
    for k in ["out-json","out-lean","out-md","out-globals","out-bindings","out-bindings-json",
              "out-manifest","out-manifest-md"]:
        ap.add_argument("--"+k)
    a = ap.parse_args()

    text_bases, runtime_func_base, bss_bases, symbol_addrs = parse_linker_map(a.map)

    ssz = os.path.join(a.source, FILES["decoder"]); srctext = open(ssz).read(); srclines = srctext.splitlines()
    consts = {m.group(1): int(m.group(2)) for m in re.finditer(r'(?:pub\s+)?const\s+(\w+)\s*(?::[^=]+)?=\s*(\d+)\s*;', srctext)}
    file_hash = {p: hashlib.sha256(open(os.path.join(a.source, p),"rb").read()).hexdigest()
                 for p in FILES.values() if os.path.exists(os.path.join(a.source, p))}
    file_hash[FILES["runtime"]] = hashlib.sha256(open(a.runtime_c, "rb").read()).hexdigest()

    objects = [("decoder", a.decoder), ("allocator", a.allocator), ("sink", a.sink), ("runtime", a.runtime)]
    # The ACTUAL SHA-256 of each sidecar object the extractor read, so a function instance's `sidecarHash`
    # pins the exact debug-bearing object it came from — never a single decoder `.text` hash reused for
    # every function instance (review blocker #5).
    object_sha = {objkind: hashlib.sha256(open(obj, "rb").read()).hexdigest() for objkind, obj in objects}
    function_instances = []            # function instance records
    die_to_idx = {}     # id(DIE) -> function_instances index (cataloged function instances only)
    excluded_occ = []   # reachable-but-uncovered emitted glue (auditable exclusion taxonomy)
    defects = []

    for objkind, obj in objects:
        dies, name_of_off, ranges_map, declline_of_off = parse_readelf(a.readelf, obj)
        dies_by_off, children_of = index_dies(dies)
        locs = parse_debug_loc(a.readelf, obj)
        for d in dies:
            name = function_instance_name(d, name_of_off)
            if name is None: continue
            if d.tag == "DW_TAG_subprogram" and "DW_AT_low_pc" not in d.attrs: continue  # abstract only
            rs = die_ranges(d, ranges_map)
            if not rs: continue
            ident = norm_identity(name, d, srclines, consts)
            if ident is None:
                base = runtime_func_base.get(name) if objkind == "runtime" else text_bases.get(objkind)
                addr = (base + rs[0][0]) if base is not None else rs[0][0]
                defects.append({"kind":"ambiguousAttribution", "address":addr, "candidates":[],
                                "name":name, "reason":"readArray width unresolved"}); continue
            qual, spec = ident
            sf = source_file_of(qual)
            if (sf, qual, spec) not in CATALOG:
                # Non-cataloged. Emitted subprograms matching the exclusion patterns are the
                # reachable-but-uncovered glue the optimizer emitted as its own function (rather than
                # inlining it into a cataloged ancestor, which would already cover its PCs). Surface
                # them as auditable exclusion data; inlined glue and the unreachable sink are skipped.
                if d.tag == "DW_TAG_subprogram":
                    cat = excluded_category(qual)
                    if cat is not None:
                        ecr = canon(objkind, name, rs, text_bases, runtime_func_base)
                        if ecr is not None:
                            excluded_occ.append({"qualified": qual, "category": cat, "regions": ecr,
                                                 "entryPc": min(r["start"] for r in ecr), "dieOffset": d.off})
                continue    # glue: folded into cataloged ancestor's ranges
            cr = canon(objkind, name, rs, text_bases, runtime_func_base)
            if cr is None:
                defects.append({"kind":"unmappedRegion", "range":{"start":rs[0][0], "size":rs[0][1]-rs[0][0]},
                                "name":name, "obj":objkind}); continue
            # `bindings` keeps its four-field shape (every downstream consumer reads it positionally);
            # `bindingProvenance` is the parallel, same-order record of HOW each row's location was
            # obtained, so a substituted location can be refused without the row being dropped.
            brows = function_instance_bindings(d, dies, name_of_off, locs, rs, dies_by_off, children_of)
            rec = {"objkind":objkind, "qualified":qual, "specialization":list(spec), "sourceFile":sf,
                   "sourceFileHash":file_hash.get(sf,""), "declLine":decl_line_of(d, declline_of_off),
                   "kind":("emitted" if d.tag=="DW_TAG_subprogram" else "inlined"),
                   "regions":cr, "entryPc":min(r["start"] for r in cr),
                   "exitPc":max(r["start"]+r["size"] for r in cr), "dieOffset":d.off,
                   "callLine":intof(d.attrs.get("DW_AT_call_line")), "callColumn":intof(d.attrs.get("DW_AT_call_column")),
                   "bindings":[r[:4] for r in brows],
                   "bindingProvenance":[(r[0], r[4]) for r in brows],
                   "_die":d}
            die_to_idx[id(d)] = len(function_instances); function_instances.append(rec)

    # nesting + inline stack from the cataloged-ancestor chain (glue transparently skipped)
    def cataloged_ancestors(d):
        chain = []; p = d.parent
        while p is not None:
            if id(p) in die_to_idx: chain.append(p)
            p = p.parent
        chain.reverse()   # outermost-first
        return chain
    for rec in function_instances:
        d = rec["_die"]; anc = cataloged_ancestors(d)
        rec["parentIdx"] = die_to_idx[id(anc[-1])] if anc else None
        # frames outermost..this: [A_0(emitted root), ..., A_m, this]; callers=[A_0..A_m], sites=[A_1.call..this.call]
        frames = anc + [d]
        stack = []
        for i in range(1, len(frames)):
            caller = function_instances[die_to_idx[id(frames[i-1])]]
            site_die = frames[i]
            csite = intof(site_die.attrs.get("DW_AT_call_line"))
            ccol = intof(site_die.attrs.get("DW_AT_call_column"))
            stack.append({"callerFile": caller["sourceFile"], "callerQualified": caller["qualified"],
                          "line": csite, "column": ccol})
        rec["inlineStack"] = stack
    for rec in function_instances: rec["children"] = []
    for i, rec in enumerate(function_instances):
        if rec["parentIdx"] is not None: function_instances[rec["parentIdx"]]["children"].append(i)

    # Regression oracle: the independently hand-verified milestone-3 `decodeOptionalBlobSchedule`
    # slice (BlobScheduleFunctionInstance.lean). The generator must reproduce it exactly, so a silent drift
    # in ranges/entry/exit/decl-line/inline-stack/nesting fails generation rather than the proof.
    #
    # Stated in RELOCATION-INVARIANT form: the object-relative entry (offset into the decoder `.text`),
    # each region's offset from the entry and its size, the exit's offset from the entry, and the
    # DWARF facts (decl line, child count, inline stack). Absolute PCs shift with the text base, so
    # pinning them would spuriously fail the relocation acceptance test; the relative layout is exactly
    # what must stay fixed under relinking.
    bs = next((function_instance for function_instance in function_instances if function_instance["qualified"] == "ssz_raw.decodeOptionalBlobSchedule"), None)
    dbase = text_bases.get("decoder")
    ORACLE = {
        "entryOffset": 0x29a8,
        "regionsRel": [(0, 8), (48, 48), (100, 268)],
        "exitRel": 368, "declLine": 396, "nchildren": 3,
        "inlineStack": [("ssz_raw.decodeRaw", 211, 48), ("ssz_raw.decodeChainConfig", 355, 44),
                        ("ssz_raw.decodeForkConfig", 371, 56)],
    }
    if bs is None:
        raise SystemExit("REGRESSION: no decodeOptionalBlobSchedule function instance generated")
    if dbase is None:
        raise SystemExit("REGRESSION: decoder .text base absent from linker map")
    got = {"entryOffset": bs["entryPc"] - dbase,
           "regionsRel": [(r["start"] - bs["entryPc"], r["size"]) for r in bs["regions"]],
           "exitRel": bs["exitPc"] - bs["entryPc"], "declLine": bs["declLine"],
           "nchildren": len(bs["children"]),
           "inlineStack": [(s["callerQualified"], s["line"], s["column"]) for s in bs["inlineStack"]]}
    if got != ORACLE:
        raise SystemExit(f"REGRESSION: generated decodeOptionalBlobSchedule != milestone-3 slice.\n"
                         f"  expected {ORACLE}\n  got      {got}")

    # entry function instance — the program cannot be emitted without one (Lean references function_instances<entry>Id), so a
    # missing entry is a hard failure, not a surfaced defect.
    entry_idx = next((i for i,r in enumerate(function_instances) if r["qualified"]=="raw_decoder_root.zesu_decode_raw" and r["kind"]=="emitted"), None)
    if entry_idx is None:
        raise SystemExit("GENERATION FAILURE: no emitted zesu_decode_raw entry function instance")

    for r in function_instances: del r["_die"]
    # stable order (does not affect identity; makes output deterministic + reviewable)
    order = sorted(range(len(function_instances)), key=lambda i:(function_instances[i]["entryPc"], function_instances[i]["qualified"], tuple(function_instances[i]["specialization"]), function_instances[i]["dieOffset"]))
    reindex = {old:new for new,old in enumerate(order)}
    function_instances_sorted = []
    for old in order:
        r = dict(function_instances[old]); r["parentIdx"] = reindex[r["parentIdx"]] if r["parentIdx"] is not None else None
        r["children"] = sorted(reindex[c] for c in r["children"]); function_instances_sorted.append(r)
    entry_idx = reindex[entry_idx]

    # Attribution defects decidable from the inline tree alone (uncovered-reachable PCs are a CFG
    # property proved in the Lean reachable partition, not decidable here).
    defects.extend(sibling_overlap_defects(function_instances_sorted))

    # Per-routine resolved declaration line (from DWARF `DW_AT_decl_line` via abstract origin). Every
    # function instance of a routine must resolve to the SAME declaration; a disagreement is an ambiguous
    # attribution. The Lean provenance check proves each function instance's declSpan equals this resolved
    # line, so declSpan is validated against the routine's resolved declaration, not merely `> 0`.
    decl_by_q = {}
    for function_instance in function_instances_sorted:
        decl_by_q.setdefault(function_instance["qualified"], set()).add(function_instance["declLine"])
    for q, lines in sorted(decl_by_q.items()):
        if len(lines) != 1:
            defects.append({"kind":"ambiguousAttribution", "address":0, "candidates":[], "name":q,
                            "reason":f"inconsistent decl lines {sorted(lines)}"})
    decl_lines = [{"qualified":q, "declLine":sorted(lines)[0]} for q, lines in sorted(decl_by_q.items())]

    # Reachable-but-excluded emitted glue, sorted for determinism (entry PC, then name, then DIE).
    excluded_sorted = sorted(excluded_occ, key=lambda x:(x["entryPc"], x["qualified"], x["dieOffset"]))
    for x in excluded_sorted:
        del x["dieOffset"]
        # excluded routines are genuine call targets (allocator vtable / cleanup), so they carry an
        # emitted identity the externalCalls can reference.
        x["sourceFile"] = source_file_of(x["qualified"]) or "<zig-std>"

    # --- Control-flow interface (area #2): propose entries/exits/blocks/edges/external-calls from the
    # canonical ELF's disassembly; Lean validates every one against the Sail-decoded `controlFlowNodes`.
    insns = disassemble(a.objdump, a.elf)

    # Resolve every DWARF-absent reader/ABI parameter from the pinned Zig call site, the explicit
    # RISC-V C ABI rule, or — for a loop-carried reader offset — the induction register recovered from
    # this disassembly. Raw rows remain in the output beside these effective rows for auditability.
    effective_bindings, recovered_bindings, derived_bindings = recover_missing_bindings(
        function_instances_sorted, srclines, consts, insns)

    region_pc_sets = compute_function_instance_cfg(function_instances_sorted, insns)   # fills function_instance["exits"], function_instance["edges"]
    for function_instance in function_instances_sorted:
        function_instance["blocks"] = function_instance_blocks(function_instance, insns)
    # entry PC -> callee: only EMITTED function_instances and excluded routines are call targets (inlined
    # callees are not "called"). Resolve each deepest-owned call site to the callee's emitted identity.
    entry_to_callee = {}
    for i, function_instance in enumerate(function_instances_sorted):
        if function_instance["kind"] == "emitted":
            entry_to_callee.setdefault(function_instance["entryPc"], ("function_instance", i))
    for j, x in enumerate(excluded_sorted):
        entry_to_callee.setdefault(x["entryPc"], ("excl", j))
    for i, function_instance in enumerate(function_instances_sorted):
        children_pcs = set()
        for c in function_instance["children"]:
            children_pcs |= region_pc_sets[c]
        owned = region_pc_sets[i] - children_pcs
        callees, seen = [], set()
        for pc in sorted(owned):
            if pc not in insns: continue
            kind, _, ct = classify(pc, insns)
            if kind == 'call' and ct is not None:
                callee = entry_to_callee.get(ct)
                if callee is None:
                    defects.append({"kind":"unmappedRegion", "range":{"start":ct, "size":0},
                                    "name":f"unresolved call target from {function_instance['qualified']}", "obj":"call"})
                elif callee not in seen:
                    seen.add(callee); callees.append(callee)
        function_instance["externalCalls"] = callees   # list of ("function_instance"|"excl", idx)

    # Reachability witnesses (area #5): the reachable set from the entry with a BFS distance and
    # predecessor per address, so Lean can prove R = directReachable in BOTH directions.
    reachable = reachable_witnesses(function_instances_sorted[entry_idx]["entryPc"], insns)

    # Independently generated pinned-source manifest: each cataloged source file mapped to the SHA-256
    # of its pinned content, computed here from the exact source the extractor read. The handwritten
    # row-1 `pinnedSourceManifest` is CHECKED against this (review blocker #5) rather than trusted.
    source_manifest = sorted(({"path": pth, "sha256": file_hash[pth]} for pth in set(file_hash)),
                             key=lambda e: e["path"])

    program = {"decoderTextSha256":DECODER_TEXT_SHA, "extractorVersion":EXTRACTOR_VERSION,
               "textBases":text_bases, "runtimeFuncBase":runtime_func_base, "objectSha256":object_sha,
               "sourceManifest":source_manifest, "declLines":decl_lines,
               "entryIndex":entry_idx, "function_instances":function_instances_sorted, "excludedRoutines":excluded_sorted,
               "reachable":reachable, "reachableEntry":function_instances_sorted[entry_idx]["entryPc"],
               "defects":sorted(defects, key=lambda x:json.dumps(x,sort_keys=True))}
    if a.out_json: open(a.out_json,"w").write(json.dumps(program, indent=2, sort_keys=True) + "\n")
    if a.out_lean: open(a.out_lean,"w").write(emit_lean(program))
    if a.out_md: open(a.out_md,"w").write(emit_md(program))
    if a.out_globals:
        if "decoder" not in bss_bases: raise SystemExit("decoder .bss placement absent from linker map")
        dec_bss_base, dec_bss_size = bss_bases["decoder"]
        globs = read_decoder_globals(a.readelf, a.decoder, dec_bss_base)
        refs = read_accessor_refs(a.objdump, a.elf, symbol_addrs, dec_bss_base, dec_bss_base + dec_bss_size)
        runtime_globs = read_runtime_globals(a.readelf, a.elf)
        open(a.out_globals, "w").write(
            emit_globals_lean(dec_bss_base, dec_bss_size, globs, refs, runtime_globs, object_sha["decoder"]))
    if a.out_bindings:
        open(a.out_bindings, "w").write(
            emit_bindings_lean(
                function_instances_sorted, effective_bindings, recovered_bindings, derived_bindings
            ))
    if a.out_bindings_json:
        open(a.out_bindings_json, "w").write(
            emit_bindings_json(
                function_instances_sorted, effective_bindings, recovered_bindings, derived_bindings
            ))
    if a.out_manifest or a.out_manifest_md:
        mrows = manifest_rows(program, {"effective": effective_bindings})
        if a.out_manifest:
            open(a.out_manifest, "w").write(emit_manifest_lean(program, mrows))
        if a.out_manifest_md:
            open(a.out_manifest_md, "w").write(emit_manifest_md(program, mrows))
    routines = {
        (function_instance["qualified"], tuple(function_instance["specialization"]))
        for function_instance in function_instances_sorted
    }
    print(f"function instances={len(function_instances_sorted)} routines={len(routines)}/43 "
          f"defects={len(program['defects'])} "
          f"entry={entry_idx} excluded={len(excluded_sorted)}")
    # Generation FAILS when unresolved defects remain (review blocker #1): the outputs above are still
    # written (the emitted Lean carries the authoritative defect list — never a hardcoded `#[]`), but the
    # nonzero exit fails the Nix derivation so an incomplete extraction can never reach the proof. The
    # Lean `coverage` obligation independently re-checks `defects = #[]`, so both generation and
    # validation reject a defective program.
    if program["defects"]:
        summary = ", ".join(d["kind"] for d in program["defects"])
        raise SystemExit(f"GENERATION FAILURE: {len(program['defects'])} unresolved attribution "
                         f"defect(s): {summary}")

# ---- Lean emission -----------------------------------------------------------------------------
def lean_str(s): return '"' + s.replace('\\','\\\\').replace('"','\\"') + '"'

def defect_lean(d):
    """Render one generator defect as its `BinaryFv.Binary.Elfling.AttributionDefect` term. Overlap
    defects reference the emitted `functionInstance<i>Id` identities, which are defined above the program."""
    k = d["kind"]
    if k == "ambiguousAttribution":
        cands = "[" + ", ".join(str(c) for c in d.get("candidates", [])) + "]"
        return f'AttributionDefect.ambiguousAttribution {d["address"]} {cands}'
    if k == "unmappedRegion":
        r = d["range"]
        return f'AttributionDefect.unmappedRegion {{ start := {r["start"]}, size := {r["size"]} }}'
    if k == "overlappingOwnership":
        return (f'AttributionDefect.overlappingOwnership {d["address"]} '
                f'functionInstance{d["firstIdx"]}Id functionInstance{d["secondIdx"]}Id')
    if k == "uncovered":
        return f'AttributionDefect.uncovered {d["address"]}'
    raise SystemExit(f"defect_lean: unknown defect kind {k!r}")
def lean_id(function_instance):
    decl = f'{{ file := {{ path := {lean_str(function_instance["sourceFile"])} }}, qualifiedName := {lean_str(function_instance["qualified"])} }}'
    spec = "#[" + ", ".join(lean_str(s) for s in function_instance["specialization"]) + "]"
    stack = "[" + ", ".join(
        f'{{ caller := {{ file := {{ path := {lean_str(s["callerFile"])} }}, qualifiedName := {lean_str(s["callerQualified"])} }},'
        f' callSite := {{ line := {s["line"]}, column := {s["column"]} }} }}' for s in function_instance["inlineStack"]) + "]"
    return f'{{ function := {{ declaration := {decl}, specialization := {spec} }}, inlineStack := {stack} }}'

def excl_id_lean(x):
    """The emitted (non-inlined) FunctionInstanceId of an excluded routine — it is a genuine call target, so
    externalCalls can reference it and the validation can resolve calls to it."""
    decl = f'{{ file := {{ path := {lean_str(x["sourceFile"])} }}, qualifiedName := {lean_str(x["qualified"])} }}'
    return f'{{ function := {{ declaration := {decl}, specialization := #[] }}, inlineStack := [] }}'

def callee_ref(c):
    kind, idx = c
    return f'functionInstance{idx}Id' if kind == "function_instance" else f'excl{idx}Id'

def blocks_lean(function_instance):
    return "#[" + ", ".join(f'{{ range := {{ start := {b["start"]}, size := {b["size"]} }} }}'
                            for b in function_instance["blocks"]) + "]"

def edges_lean(function_instance):
    return "#[" + ", ".join(f'{{ source := {e["source"]}, target := {e["target"]} }}'
                            for e in function_instance["edges"]) + "]"

def emit_lean(p):
    L = ["-- GENERATED FILE: produced by tools/generate_elfling_program.py. DO NOT EDIT.",
         "import BinaryFv.Binary.Elfling.FunctionInstance", "",
         "/-!", "# Generated Elfling program (milestone 4)", "",
         "Deterministically generated from the validated DWARF sidecars by",
         "`tools/generate_elfling_program.py`. Address-bearing, UNTRUSTED: the Lean validation",
         "(`ProgramValidation.lean`) checks every range/word against the canonical ELF and discharges",
         "`coverage` / `sourceProvenanceRecorded` / `IsCanonicalGeneratedProgram`. Object `.text` bases,",
         "readArray widths (from `DW_AT_call_line` -> pinned source), and glue-folding are recorded in the",
         "companion JSON. Regenerating is byte-deterministic (checked twice in the derivation).", "-/", "",
         "-- the chunked reachability witness table is assembled by a many-fold `++`; elaborating it",
         "-- exceeds the default recursion depth.",
         "set_option maxRecDepth 8000", "",
         "namespace BinaryFv.SSZ.Zesu.Elfling.Generated", "",
         "open BinaryFv.Binary (AddressRange)", "open BinaryFv.Binary.Elfling", ""]
    prov = lambda function_instance: (
        f'{{ sidecarHash := {lean_str(p["objectSha256"][function_instance["objkind"]])}, '
        f'entryOffset := {function_instance["dieOffset"]}, '
        f'extractorVersion := {lean_str(p["extractorVersion"])} }}'
    )
    # All address-free identities first (they reference nothing), so the FunctionInstances below can
    # forward-reference each other's ids for parent?/children (which form a mutual parent/child graph).
    L.append("/-! ### Function instance identities (address-free). -/")
    for i, function_instance in enumerate(p["function_instances"]):
        L.append(
            f'def functionInstance{i}Id : FunctionInstanceId := {lean_id(function_instance)}'
        )
    L.append("")
    L.append("/-! ### Excluded-routine identities (address-free call targets). -/")
    for j, x in enumerate(p["excludedRoutines"]):
        L.append(f'def excl{j}Id : FunctionInstanceId := {excl_id_lean(x)}')
    L.append("")
    L.append("/-! ### Function instances (address-bearing). -/")
    for i, function_instance in enumerate(p["function_instances"]):
        regions = "#[" + ", ".join(
            f'{{ start := {r["start"]}, size := {r["size"]} }}'
            for r in function_instance["regions"]
        ) + "]"
        parent = (
            "none"
            if function_instance["parentIdx"] is None
            else f'some functionInstance{function_instance["parentIdx"]}Id'
        )
        children = "#[" + ", ".join(
            f'functionInstance{child}Id' for child in function_instance["children"]
        ) + "]"
        exits = "#[" + ", ".join(str(exit_pc) for exit_pc in function_instance["exits"]) + "]"
        extcalls = "#[" + ", ".join(
            callee_ref(callee) for callee in function_instance["externalCalls"]
        ) + "]"
        specialization = (
            "[" + ",".join(function_instance["specialization"]) + "]"
            if function_instance["specialization"] else ""
        )
        L.append(
            f'/-- function instance {i}: {function_instance["qualified"]}{specialization}'
            f' ({function_instance["kind"]}, entry 0x{function_instance["entryPc"]:x}). -/'
        )
        L.append(f'def functionInstance{i} : FunctionInstance :=')
        L.append(
            f'  {{ id := functionInstance{i}Id, regions := {regions}, '
            f'entryPc := {function_instance["entryPc"]}, exitPcs := {exits},'
        )
        L.append(f'    parent? := {parent}, children := {children}, externalCalls := {extcalls},')
        L.append(
            f'    blocks := {blocks_lean(function_instance)}, '
            f'edges := {edges_lean(function_instance)},'
        )
        L.append(
            f'    declProvenance := {{ sourceFileHash := '
            f'{lean_str(function_instance["sourceFileHash"])}, '
            f'declSpan := {{ line := {function_instance["declLine"]}, column := 1 }} }},'
        )
        L.append(f'    provenance := {prov(function_instance)}, symbol? := none }}')
        L.append("")
    L.append("/-- Every generated function instance. -/")
    L.append("def generatedFunctionInstances : Array FunctionInstance :=")
    L.append("  #[" + ", ".join(
        f'functionInstance{i}' for i in range(len(p["function_instances"]))
    ) + "]")
    L.append("")
    # Reachable-but-excluded taxonomy (auditable data the reachable-partition proof consumes).
    L.append("/-! ### Reachable-but-excluded emitted routines (auditable exclusion taxonomy). -/")
    L.append("")
    L.append("/-- Every reachable-but-excluded emitted routine: emitted identity, DWARF name, category,")
    L.append("canonical regions. The identity lets a resolved external call target an excluded routine. -/")
    L.append("def generatedExcludedFunctionInstances : Array ExcludedFunctionInstance :=")
    if p["excludedRoutines"]:
        items = []
        for j, x in enumerate(p["excludedRoutines"]):
            regions = "#[" + ", ".join(f'{{ start := {r["start"]}, size := {r["size"]} }}' for r in x["regions"]) + "]"
            items.append(f'  {{ id := excl{j}Id, qualifiedName := {lean_str(x["qualified"])}, '
                         f'category := {lean_str(x["category"])}, regions := {regions} }}')
        L.append("  #[" + ",\n   ".join(items) + "]")
    else:
        L.append("  #[]")
    L.append("")
    ei = p["entryIndex"]
    L.append(
        f'/-- The complete generated program: entry `zesu_decode_raw` '
        f'(function instance {ei}), all reachable'
    )
    L.append("    function instances, and the surfaced attribution defects. -/")
    # Authoritative: the emitted defect list is exactly the generator's, never a hardcoded `#[]`. The
    # derivation additionally FAILS when this list is nonempty, so in a released program it is `#[]`
    # because there were no defects — not because emission discarded them.
    defects = "#[" + ", ".join(defect_lean(d) for d in p["defects"]) + "]"
    L.append("def generatedProgram : Program :=")
    L.append(
        f'  {{ entry := functionInstance{ei}Id, '
        f'functionInstances := generatedFunctionInstances, defects := {defects},'
    )
    L.append(f'    provenance := {prov(p["function_instances"][ei])},')
    L.append("    excludedFunctionInstances := generatedExcludedFunctionInstances }")
    L.append("")
    # Independently generated pinned-source manifest (path -> content SHA-256), for cross-checking the
    # handwritten row-1 `pinnedSourceManifest` rather than trusting it.
    L.append("/-! ### Independently generated pinned-source manifest. -/")
    L.append("")
    L.append("/-- Each cataloged source file's path mapped to the SHA-256 of its pinned content, computed")
    L.append("by the generator from the exact source it read. `GeneratedProvenanceCheck` proves the")
    L.append("handwritten `pinnedSourceManifest` equals this, so the row-1 hashes are validated. -/")
    L.append("def generatedSourceManifest : List (String × String) :=")
    sm = ", ".join(f'({lean_str(e["path"])}, {lean_str(e["sha256"])})' for e in p["sourceManifest"])
    L.append("  [" + sm + "]")
    L.append("")
    L.append("/-- Each routine's resolved declaration line (DWARF `DW_AT_decl_line`), one entry per routine")
    L.append("qualified name. `GeneratedProvenanceCheck` proves every function instance's declSpan line equals its")
    L.append("routine's resolved line here, so declSpan is checked against the resolved declaration. -/")
    L.append("def generatedDeclLines : List (String × Nat) :=")
    dl = ", ".join(f'({lean_str(e["qualified"])}, {e["declLine"]})' for e in p["declLines"])
    L.append("  [" + dl + "]")
    L.append("")
    # Reachability set + BFS distance/predecessor witnesses (area #5): the exact reachable set from the
    # entry with, per address, the BFS distance and a predecessor whose distance is one less and which
    # has a real decoded edge to it. Lean validates these against the decoded CFG and proves
    # R = directReachable in BOTH directions (closure forward; witness path induction reverse).
    L.append("/-! ### Reachability witnesses (area #5). -/")
    L.append("")
    L.append("/-- One reachable address with its BFS distance from the entry and its predecessor on a")
    L.append("shortest path (the entry's predecessor is itself). -/")
    L.append("structure ReachStep where")
    L.append("  addr : Nat")
    L.append("  distance : Nat")
    L.append("  predecessor : Nat")
    L.append("deriving Repr, Inhabited, DecidableEq")
    L.append("")
    L.append(f'/-- The entry address reachability is computed from (the emitted `zesu_decode_raw`). -/')
    L.append(f'def reachableEntry : Nat := {p["reachableEntry"]}')
    L.append("")
    # Chunk the witness table into <=128-row pieces: a single 3369-element array literal exceeds the
    # elaborator's recursion depth (the same reason the reachability certificate is chunked), and the
    # bounded pieces are exactly the "<=128 shape" the plan wants so the monolith cannot return.
    reach = p["reachable"]
    CHUNK = 128
    nchunks = (len(reach) + CHUNK - 1) // CHUNK
    L.append(f"/-- Reachability witness table, chunked into {nchunks} bounded (<={CHUNK}-row) pieces. -/")
    for c in range(nchunks):
        body = ",\n   ".join(
            f'{{ addr := {e["addr"]}, distance := {e["distance"]}, predecessor := {e["predecessor"]} }}'
            for e in reach[c*CHUNK:(c+1)*CHUNK])
        L.append(f'def reachWitnessChunk{c} : Array ReachStep :=')
        L.append("  #[" + body + "]")
        L.append("")
    L.append("/-- Every reachable address with its distance/predecessor witness, sorted by address. -/")
    L.append("def reachableWitness : Array ReachStep :=")
    L.append("  " + " ++ ".join(f'reachWitnessChunk{c}' for c in range(nchunks)))
    L.append("")
    L.append("/-- The reachable set (addresses only). -/")
    L.append("def reachableAddresses : Array Nat := reachableWitness.map (·.addr)")
    L.append("")
    L.append("end BinaryFv.SSZ.Zesu.Elfling.Generated")
    L.append("")
    return "\n".join(L)

def emit_md(p):
    M = ["# Generated Elfling program — source/function/CFG index", "",
         f"Deterministically generated from the DWARF sidecars. {len(p['function_instances'])} function instances over "
         f"{len({(function_instance['qualified'],tuple(function_instance['specialization'])) for function_instance in p['function_instances']})}/43 catalog routines; "
         f"{len(p['defects'])} attribution defect(s).", ""]
    function_instances = p["function_instances"]
    tot = lambda k: sum(len(function_instance.get(k, [])) for function_instance in function_instances)
    overlaps = [d for d in p["defects"] if d.get("kind") == "overlappingOwnership"]
    M += [f"Totals: {sum(len(function_instance['regions']) for function_instance in function_instances)} regions, {tot('blocks')} basic blocks, "
          f"{tot('edges')} direct edges, {tot('exits')} exit PCs, {tot('externalCalls')} external-call "
          f"edges, {len(overlaps)} overlaps; {len(p.get('reachable', []))} reachable PCs "
          f"(gaps between cataloged function instances are the excluded routines below). "
          f"Every field is validated against the Sail-decoded CFG in Lean.", "",
          "## Functions (function_instances)", "",
          "| # | routine | spec | src line | kind | entry | exits | regions | blocks | edges | calls | parent | inline |",
          "|--:|---------|------|--------:|------|------:|-----:|-------:|------:|-----:|----:|-------:|------:|"]
    for i, function_instance in enumerate(function_instances):
        spec = ",".join(function_instance["specialization"]) or "—"
        par = "—" if function_instance["parentIdx"] is None else str(function_instance["parentIdx"])
        exits = ",".join(f"0x{e:x}" for e in function_instance.get("exits", [])) or "—"
        M.append(f"| {i} | `{function_instance['qualified']}` | {spec} | {function_instance['declLine']} | {function_instance['kind']} | "
                 f"0x{function_instance['entryPc']:x} | {exits} | {len(function_instance['regions'])} | {len(function_instance.get('blocks', []))} | "
                 f"{len(function_instance.get('edges', []))} | {len(function_instance.get('externalCalls', []))} | {par} | {len(function_instance['inlineStack'])} |")
    # Inline call stacks (deepest attribution provenance) for the inlined function instances.
    inlined = [(i, function_instance) for i, function_instance in enumerate(function_instances) if function_instance["inlineStack"]]
    if inlined:
        M += ["", "## Inline call stacks", ""]
        for i, function_instance in inlined:
            stack = " → ".join(f"{s['callerQualified']}@{s['line']}:{s['column']}" for s in function_instance["inlineStack"])
            M.append(f"- function_instances {i} `{function_instance['qualified']}`: {stack} → **{function_instance['qualified'].split('.')[-1]}**")
    ex = p.get("excludedRoutines", [])
    if ex:
        total = sum((r["size"] // 4) for x in ex for r in x["regions"])
        M += ["", f"## Reachable-but-excluded routines ({len(ex)} routines, {total} region words)", "",
              "Emitted glue reachable from `zesu_decode_raw` that carries no cataloged function instance. "
              "The Lean reachable-partition validation proves these exactly account for the reachable "
              "PCs no cataloged function instance covers.", "",
              "| # | routine | category | regions | words |",
              "|--:|---------|----------|--------:|------:|"]
        for i, x in enumerate(ex):
            w = sum(r["size"] // 4 for r in x["regions"])
            M.append(f"| {i} | `{x['qualified']}` | {x['category']} | {len(x['regions'])} | {w} |")
    if p["defects"]:
        M += ["", "## Attribution defects", ""] + [f"- `{json.dumps(d)}`" for d in p["defects"]]
    M.append("")
    return "\n".join(M)


# ---------------------------------------------------------------------------
# Function instance manifest (row D1)
# ---------------------------------------------------------------------------
#
# The single source of both the Lean manifest and the Markdown work-assignment view, so the two can
# never disagree. Everything emitted here is PROPOSED by the generator and CHECKED in Lean against
# `generatedProgram` and the handwritten catalog (`GeneratedManifest.lean`): the routine tag against
# `catalogEntryFor`, the kind/parent/children/calls/entry/exits against the function instance record, and
# the row set against `generatedProgram.functionInstances` in both directions.
#
# Deliberately NOT emitted: the numeric step bound. It lives in exactly one place — the contract the
# function instance's `RoutineTag` selects through `routineContract` — and copying it into generated data
# would create an unchecked second copy of a proof-relevant constant. The manifest carries the tag,
# which is what determines it.

# qualified name -> RoutineTag constructor, PROPOSED here and checked in Lean against the catalog.
ROUTINE_TAGS = {
    "raw_decoder_root.zesu_decode_raw": "zesuDecodeRaw",
    "ssz_raw.decode": "decode",
    "ssz_raw.decodeRaw": "decodeRaw",
    "ssz_raw.decodeNewPayloadRequest": "newPayloadRequest",
    "ssz_raw.decodeExecutionPayload": "executionPayload",
    "ssz_raw.decodeExecutionRequests": "executionRequests",
    "ssz_raw.decodeExecutionWitness": "executionWitness",
    "ssz_raw.decodeChainConfig": "chainConfig",
    "ssz_raw.decodeForkConfig": "forkConfig",
    "ssz_raw.decodeForkActivation": "forkActivation",
    "ssz_raw.decodeOptionalU64": "optionalU64",
    "ssz_raw.decodeOptionalBlobSchedule": "optionalBlobSchedule",
    "ssz_raw.decodeVersionedHashes": "versionedHashes",
    "ssz_raw.decodeWithdrawals": "withdrawals",
    "ssz_raw.decodeDepositRequests": "depositRequests",
    "ssz_raw.decodeWithdrawalRequests": "withdrawalRequests",
    "ssz_raw.decodeConsolidationRequests": "consolidationRequests",
    "ssz_raw.decodePublicKeys": "publicKeys",
    "ssz_raw.decodeByteListList": "byteListList",
    "ssz_raw.requireCanonicalOffsets": "requireCanonicalOffsets",
    "ssz_raw.requireU32Length": "requireU32Length",
    "ssz_raw.readOffset": "readOffset",
    "ssz_raw.readU32": "readU32",
    "ssz_raw.readU64": "readU64",
    "ssz_raw.readU256": "readU256",
    "ssz_raw.readArray": "readArray",
    "ssz_raw.bytesAt": "bytesAt",
    "ssz_raw.hasExactErePrefix": "hasExactErePrefix",
    "raw_allocator.zesu_raw_alloc": "rawAlloc",
    "memcpy": "memcpy",
    "memmove": "memmove",
    "raw_decoder_root.zesu_raw_result": "rawResult",
    "raw_decoder_root.zesu_raw_error": "rawError",
    "raw_decoder_root.allocatorAlloc": "allocatorAlloc",
    "raw_decoder_root.allocatorResize": "allocatorResize",
    "raw_decoder_root.allocatorRemap": "allocatorRemap",
    "raw_decoder_root.allocatorFree": "allocatorFree",
    "raw_decoder_root.allocator": "allocatorCtor",
}

# RoutineTag -> the plan row that owns its local proofs. Row E is the blob-schedule vertical slice,
# F the leaves/options/runtime, G the collections, H the containers and decodeRaw/decode, I the
# exported wrapper.
OWNING_ROW = {
    "optionalBlobSchedule": "E",
    "optionalU64": "F", "requireCanonicalOffsets": "F", "requireU32Length": "F",
    "readOffset": "F", "readU32": "F", "readU64": "F", "readU256": "F", "readArray": "F",
    "bytesAt": "F", "hasExactErePrefix": "F", "rawAlloc": "F", "memcpy": "F", "memmove": "F",
    "rawResult": "F", "rawError": "F", "allocatorAlloc": "F", "allocatorResize": "F",
    "allocatorRemap": "F", "allocatorFree": "F", "allocatorCtor": "F",
    "versionedHashes": "G", "withdrawals": "G", "depositRequests": "G",
    "withdrawalRequests": "G", "consolidationRequests": "G", "publicKeys": "G",
    "byteListList": "G",
    "newPayloadRequest": "H", "executionPayload": "H", "executionRequests": "H",
    "executionWitness": "H", "chainConfig": "H", "forkConfig": "H", "forkActivation": "H",
    "decodeRaw": "H", "decode": "H",
    "zesuDecodeRaw": "I",
}

# Human-readable rendering of each routine's step bound, for the MANIFEST.md view ONLY. This is
# DOCUMENTATION, not a proof input: it is never emitted into GeneratedManifest.lean and no proof or
# check consumes it. The authoritative source of every step bound is the Lean contract the row's
# RoutineTag selects through `routineContract` (BinaryFv/SSZ/Zesu/Contracts/*.lean); this dict mirrors
# those `stepBound` fields for the human backlog view, and must be kept in step with them by hand.
# `|input|` is the input byte size, `|offsets|`/`|len|` an argument length, `N` a readArray width.
STEP_BOUND_EXPR = {
    "zesuDecodeRaw": "2·(16384 + 512·|input|) + 1024",
    "decode": "2·(16384 + 512·|input|)",
    "decodeRaw": "16384 + 512·|input|",
    "newPayloadRequest": "8192 + 256·|input|",
    "executionPayload": "4096 + 256·|input|",
    "executionRequests": "1024 + 256·|input|",
    "executionWitness": "1024 + 256·|input|",
    "chainConfig": "2048",
    "forkConfig": "1024",
    "forkActivation": "512",
    "optionalU64": "128",
    "optionalBlobSchedule": "256",
    "versionedHashes": "128 + 64·(|input|/32 + 1)",
    "withdrawals": "128 + 256·(|input|/44 + 1)",
    "depositRequests": "128 + 512·(|input|/192 + 1)",
    "withdrawalRequests": "128 + 256·(|input|/76 + 1)",
    "consolidationRequests": "128 + 256·(|input|/116 + 1)",
    "publicKeys": "128 + 128·(|input|/65 + 1)",
    "byteListList": "256 + 256·(|input|/4 + 1)",
    "requireCanonicalOffsets": "32 + 32·|offsets|",
    "requireU32Length": "32",
    "readOffset": "64",
    "readU32": "64",
    "readU64": "96",
    "readU256": "128",
    "readArray": "32 + 4·N",
    "bytesAt": "32",
    "hasExactErePrefix": "64",
    "rawAlloc": "128",
    "memcpy": "64 + 8·|len|",
    "memmove": "64 + 16·|len|",
    "rawResult": "32",
    "rawError": "16",
    "allocatorAlloc": "128",
    "allocatorResize": "8",
    "allocatorRemap": "8",
    "allocatorFree": "8",
    "allocatorCtor": "16",
}


def step_bound_expr(tag, specialization):
    """Human step-bound string for a routine, substituting the concrete readArray width for N."""
    expr = STEP_BOUND_EXPR.get(tag)
    if expr is None:
        raise SystemExit(f"MANIFEST: tag {tag} has no step-bound expression")
    if tag == "readArray" and specialization:
        expr = expr.replace("N", specialization[0])
    return expr


def manifest_rows(p, bindings):
    """One row per generated function instance, in function-instance-index order."""
    function_instances = p["function_instances"]
    by_id = {}
    for i, function_instance in enumerate(function_instances):
        by_id[(
            function_instance["qualified"],
            tuple(function_instance["specialization"]),
            tuple(
                (s["callerQualified"], s["line"], s["column"])
                for s in function_instance["inlineStack"]
            ),
        )] = i
    # Binding rows keyed by function-instance index, from the same effective table Lean validates.
    brows = {}
    for i, bs in enumerate(bindings.get("effective", [])):
        for (name, kind, _reg, _value) in bs:
            brows.setdefault(i, []).append(f"{name}:{kind}")
    rows = []
    for i, function_instance in enumerate(function_instances):
        tag = ROUTINE_TAGS.get(function_instance["qualified"])
        if tag is None:
            raise SystemExit(
                f"MANIFEST: function instance {i} `{function_instance['qualified']}` "
                "has no routine tag"
            )
        row_owner = OWNING_ROW.get(tag)
        if row_owner is None:
            raise SystemExit(f"MANIFEST: tag {tag} has no owning row")
        calls = [
            callee[1]
            for callee in function_instance["externalCalls"]
            if callee[0] == "function_instance"
        ]
        absorbed = [
            callee[1]
            for callee in function_instance["externalCalls"]
            if callee[0] != "function_instance"
        ]
        rows.append({
            "index": i,
            "qualified": function_instance["qualified"],
            "specialization": list(function_instance["specialization"]),
            "tag": tag,
            "kind": function_instance["kind"],
            "parent": function_instance.get("parentIdx"),
            "children": list(function_instance["children"]),
            "externalCalls": calls,
            "absorbed": absorbed,
            "entryPc": function_instance["entryPc"],
            "exitPcs": list(function_instance["exits"]),
            "bindingRows": sorted(brows.get(i, [])),
            "dependencies": sorted(set(list(function_instance["children"]) + calls)),
            "theoremName": f"localContract_functionInstance{i}",
            "owningRow": row_owner,
            "proofStatus": "pending",
        })
    # Manifest integrity, enforced at generation time: one row per function instance, one function instance per
    # row, in index order, with distinct theorem names. Any omission, duplication or reorder aborts.
    if len(rows) != len(function_instances):
        raise SystemExit("MANIFEST: row count does not match function-instance count")
    if [r["index"] for r in rows] != list(range(len(function_instances))):
        raise SystemExit("MANIFEST: rows are not in function-instance-index order")
    if len({r["index"] for r in rows}) != len(rows):
        raise SystemExit("MANIFEST: duplicated function-instance index")
    if len({r["theoremName"] for r in rows}) != len(rows):
        raise SystemExit("MANIFEST: duplicated theorem name")
    for r in rows:
        if r["qualified"] != function_instances[r["index"]]["qualified"]:
            raise SystemExit(
                f"MANIFEST: row {r['index']} names the wrong function instance"
            )
        for d in r["dependencies"]:
            if not (0 <= d < len(function_instances)):
                raise SystemExit(
                    f"MANIFEST: row {r['index']} depends on nonexistent function instance {d}"
                )
    return rows


def emit_manifest_lean(p, rows):
    def nats(xs): return "#[" + ", ".join(str(x) for x in xs) + "]"
    def strs(xs): return "#[" + ", ".join(lean_str(x) for x in xs) + "]"
    L = ["-- GENERATED FILE: produced by tools/generate_elfling_program.py (--out-manifest). DO NOT EDIT.",
         "import GeneratedProgram", "",
         "/-!", "# The function-instance manifest (row D1)", "",
         "One row per generated function instance, in function-instance-index order. Emitted from the same data as",
         "`MANIFEST.md`, so the work-assignment view and the Lean-visible backlog cannot drift.",
         "",
         "UNTRUSTED, like every generated artifact: `GeneratedManifest.lean` in the proof tree checks",
         "each row against `generatedProgram` and the handwritten catalog, in both directions.",
         "",
         "The numeric step bound is deliberately absent: it lives in the contract the row's",
         "`routineTag` selects, and a copy here would be an unchecked second source for a",
         "proof-relevant constant.",
         "-/", "",
         "namespace BinaryFv.SSZ.Zesu.Elfling.Generated", "",
         "open BinaryFv.Binary.Elfling", "",
         "/-- One manifest row. `routineTag` is the constructor name of the `RoutineTag` the proof",
         "layer checks against `catalogEntryFor`; keeping it a `String` here is what stops the",
         "generated file from importing the handwritten catalog. -/",
         "structure ManifestRow where",
         "  index : Nat",
         "  id : FunctionInstanceId",
         "  qualifiedName : String",
         "  routineTag : String",
         "  kind : String",
         "  parent : Option Nat",
         "  children : Array Nat",
         "  externalCalls : Array Nat",
         "  absorbed : Array Nat",
         "  entryPc : Nat",
         "  exitPcs : Array Nat",
         "  bindingRows : Array String",
         "  dependencies : Array Nat",
         "  theoremName : String",
         "  owningRow : String",
         "  proofStatus : String",
         "deriving Repr, Inhabited, DecidableEq", "",
         "/-- The complete manifest: exactly one row per generated function instance, in index order. -/",
         "def generatedManifest : Array ManifestRow :=", "  #["]
    items = []
    for r in rows:
        parent = "none" if r["parent"] is None else f'some {r["parent"]}'
        items.append(
            f'    {{ index := {r["index"]}, id := functionInstance{r["index"]}Id, '
            f'qualifiedName := {lean_str(r["qualified"])}, routineTag := {lean_str(r["tag"])},\n'
            f'      kind := {lean_str(r["kind"])}, parent := {parent}, '
            f'children := {nats(r["children"])}, externalCalls := {nats(r["externalCalls"])},\n'
            f'      absorbed := {nats(r["absorbed"])}, entryPc := {r["entryPc"]}, '
            f'exitPcs := {nats(r["exitPcs"])},\n'
            f'      bindingRows := {strs(r["bindingRows"])}, '
            f'dependencies := {nats(r["dependencies"])},\n'
            f'      theoremName := {lean_str(r["theoremName"])}, '
            f'owningRow := {lean_str(r["owningRow"])}, '
            f'proofStatus := {lean_str(r["proofStatus"])} }}')
    L.append(",\n".join(items))
    L += ["  ]", "", "end BinaryFv.SSZ.Zesu.Elfling.Generated", ""]
    return "\n".join(L)


def emit_manifest_md(p, rows):
    function_instances = p["function_instances"]
    by_row = {}
    for r in rows:
        by_row.setdefault(r["owningRow"], []).append(r)
    by_routine = {}
    for r in rows:
        key = r["qualified"] + ("[" + ",".join(r["specialization"]) + "]" if r["specialization"] else "")
        by_routine.setdefault(key, []).append(r)
    M = ["# Function instance manifest — the Row D local-proof backlog", "",
         "GENERATED by `tools/generate_elfling_program.py`. Do not edit; regenerate.",
         "",
         "Emitted from the same rows as `GeneratedManifest.lean`, so this view and the Lean-visible",
         "backlog cannot drift. The Lean side checks every row against `generatedProgram` and the",
         "handwritten catalog in both directions.",
         "",
         "The **step bound** shown per routine is a human-readable mirror of that routine's Lean",
         "contract bound; the authoritative source is the contract the row's `RoutineTag` selects",
         "through `routineContract` (`BinaryFv/SSZ/Zesu/Contracts/*.lean`). It is documentation only —",
         "not emitted into `GeneratedManifest.lean` and not consumed by any proof — so nothing here",
         "introduces a second proof-relevant source for the bound. `|input|` is the input byte size.",
         "",
         f"**{len(rows)} function instances** across **{len(by_routine)} source routines**.",
         "",
         "## By owning plan row", "",
         "| row | function instances | routines |", "|---|--:|--:|"]
    for row_owner in sorted(by_row):
        rs = by_row[row_owner]
        routines = {r["qualified"] for r in rs}
        M.append(f"| {row_owner} | {len(rs)} | {len(routines)} |")
    M += ["", "## By source routine", "",
          "Each group is one source routine; every function instance of it must be proved locally, and no",
          "function instance inherits its sibling's proof.", ""]
    for key in sorted(by_routine):
        rs = by_routine[key]
        bound = step_bound_expr(rs[0]["tag"], rs[0]["specialization"])
        M += [f"### `{key}` — {len(rs)} function instance(s), row {rs[0]['owningRow']}", "",
              f"Step bound (from `routineContract`, human mirror): `{bound}`", "",
              "| function instance | kind | entry | exits | deps | binding rows | theorem | status |",
              "|--:|---|---|--:|---|---|---|---|"]
        for r in rs:
            deps = ",".join(str(d) for d in r["dependencies"]) or "—"
            brs = ", ".join(f"`{b}`" for b in r["bindingRows"]) or "—"
            M.append(f'| {r["index"]} | {r["kind"]} | `0x{r["entryPc"]:x}` | {len(r["exitPcs"])} | '
                     f'{deps} | {brs} | `{r["theoremName"]}` | {r["proofStatus"]} |')
        M.append("")
    del function_instances
    return "\n".join(M) + "\n"

if __name__ == "__main__":
    main()
