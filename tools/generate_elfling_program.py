#!/usr/bin/env python3
"""
Deterministic ELF/DWARF/CFG -> Elfling Program generator (milestone 4, generator+emission chunk).

Reads the validated DWARF sidecars (decoder/allocator/sink built strip=false; runtime built -g, each
byte-identical to the canonical stripped object), enumerates every emitted subprogram and every
inlined_subroutine, maps object-relative ranges to canonical-ELF PCs via the linker-map bases,
resolves readArray widths from DWARF call_line -> pinned source, matches occurrences to live catalog
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

    Returns (text_bases, runtime_func_base):
      * text_bases[objkind]         = the linked address of that object's `.text` section;
      * runtime_func_base[funcname] = the linked address of the runtime object's `.text.<funcname>`
                                      per-function section (each runtime routine is its own section).
    Only the placed sections under `Linker script and memory map` are read, so the discarded-input
    block (address 0, e.g. gc-sectioned `.text.memset`/`.text.memcmp`) is ignored. Relinking at a
    different text base changes only these numbers; the identities the generator emits do not depend
    on them, which is what the relocation acceptance test checks."""
    text_bases, runtime_func_base = {}, {}
    line_re = re.compile(r'^\s+(\.text(?:\.[\w.]+)?)\s+0x([0-9a-f]+)\s+0x[0-9a-f]+\s+(\S+\.o)\s*$')
    started = False
    for ln in open(path):
        if not started:
            if ln.startswith("Linker script and memory map"): started = True
            continue
        m = line_re.match(ln)
        if not m: continue
        sect, addr, obj = m.group(1), int(m.group(2), 16), os.path.basename(m.group(3))
        if sect == ".text" and obj in MAP_OBJKIND:
            text_bases[MAP_OBJKIND[obj]] = addr
        elif sect.startswith(".text.") and obj == RUNTIME_MAP_OBJ:
            runtime_func_base[sect[len(".text."):]] = addr
    return text_bases, runtime_func_base

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

def occ_name(d, name_of_off):
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

def sibling_overlap_defects(occ_sorted):
    """Attribution defects decidable from the inline tree: two occurrences claiming a common PC without
    one being inlined within the other. Inline nesting legitimately overlaps (a child's PCs lie inside
    its parent's), so ancestor/descendant pairs are excluded; anything else sharing a PC is ambiguous
    ownership the deepest-inline rule cannot resolve, surfaced as `overlappingOwnership` rather than
    dropped. Pure over the occurrence list (no ELF/DWARF access) so it is directly unit-testable."""
    ancestors = [set() for _ in occ_sorted]
    for i, r in enumerate(occ_sorted):
        k = r["parentIdx"]
        while k is not None:
            ancestors[i].add(k); k = occ_sorted[k]["parentIdx"]
    def overlap_addr(a, b):
        for r in a["regions"]:
            for q in b["regions"]:
                if r["start"] < q["start"]+q["size"] and q["start"] < r["start"]+r["size"]:
                    return max(r["start"], q["start"])
        return None
    out = []
    for i in range(len(occ_sorted)):
        for j in range(i+1, len(occ_sorted)):
            if j in ancestors[i] or i in ancestors[j]: continue
            o = overlap_addr(occ_sorted[i], occ_sorted[j])
            if o is not None:
                out.append({"kind":"overlappingOwnership", "address":o, "firstIdx":i, "secondIdx":j,
                            "first":occ_sorted[i]["qualified"], "second":occ_sorted[j]["qualified"]})
    return out

def main():
    ap = argparse.ArgumentParser()
    for k in ["readelf","decoder","allocator","sink","runtime","source"]: ap.add_argument("--"+k, required=True)
    # the runtime C source lives in the proof repo (targets/common/riscv64_runtime.c), not the zesu
    # source tree, so its content hash is supplied separately.
    ap.add_argument("--runtime-c", required=True)
    # canonical placement comes from the pinned linked ELF's linker map, never hardcoded bases.
    ap.add_argument("--map", required=True)
    for k in ["out-json","out-lean","out-md"]: ap.add_argument("--"+k)
    a = ap.parse_args()

    text_bases, runtime_func_base = parse_linker_map(a.map)

    ssz = os.path.join(a.source, FILES["decoder"]); srctext = open(ssz).read(); srclines = srctext.splitlines()
    consts = {m.group(1): int(m.group(2)) for m in re.finditer(r'(?:pub\s+)?const\s+(\w+)\s*(?::[^=]+)?=\s*(\d+)\s*;', srctext)}
    file_hash = {p: hashlib.sha256(open(os.path.join(a.source, p),"rb").read()).hexdigest()
                 for p in FILES.values() if os.path.exists(os.path.join(a.source, p))}
    file_hash[FILES["runtime"]] = hashlib.sha256(open(a.runtime_c, "rb").read()).hexdigest()

    objects = [("decoder", a.decoder), ("allocator", a.allocator), ("sink", a.sink), ("runtime", a.runtime)]
    # The ACTUAL SHA-256 of each sidecar object the extractor read, so an occurrence's `sidecarHash`
    # pins the exact debug-bearing object it came from — never a single decoder `.text` hash reused for
    # every occurrence (review blocker #5).
    object_sha = {objkind: hashlib.sha256(open(obj, "rb").read()).hexdigest() for objkind, obj in objects}
    occ = []            # occurrence records
    die_to_idx = {}     # id(DIE) -> occ index (cataloged occurrences only)
    excluded_occ = []   # reachable-but-uncovered emitted glue (auditable exclusion taxonomy)
    defects = []

    for objkind, obj in objects:
        dies, name_of_off, ranges_map, declline_of_off = parse_readelf(a.readelf, obj)
        for d in dies:
            name = occ_name(d, name_of_off)
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
            rec = {"objkind":objkind, "qualified":qual, "specialization":list(spec), "sourceFile":sf,
                   "sourceFileHash":file_hash.get(sf,""), "declLine":decl_line_of(d, declline_of_off),
                   "kind":("emitted" if d.tag=="DW_TAG_subprogram" else "inlined"),
                   "regions":cr, "entryPc":min(r["start"] for r in cr),
                   "exitPc":max(r["start"]+r["size"] for r in cr), "dieOffset":d.off,
                   "callLine":intof(d.attrs.get("DW_AT_call_line")), "callColumn":intof(d.attrs.get("DW_AT_call_column")),
                   "_die":d}
            die_to_idx[id(d)] = len(occ); occ.append(rec)

    # nesting + inline stack from the cataloged-ancestor chain (glue transparently skipped)
    def cataloged_ancestors(d):
        chain = []; p = d.parent
        while p is not None:
            if id(p) in die_to_idx: chain.append(p)
            p = p.parent
        chain.reverse()   # outermost-first
        return chain
    for rec in occ:
        d = rec["_die"]; anc = cataloged_ancestors(d)
        rec["parentIdx"] = die_to_idx[id(anc[-1])] if anc else None
        # frames outermost..this: [A_0(emitted root), ..., A_m, this]; callers=[A_0..A_m], sites=[A_1.call..this.call]
        frames = anc + [d]
        stack = []
        for i in range(1, len(frames)):
            caller = occ[die_to_idx[id(frames[i-1])]]
            site_die = frames[i]
            csite = intof(site_die.attrs.get("DW_AT_call_line"))
            ccol = intof(site_die.attrs.get("DW_AT_call_column"))
            stack.append({"callerFile": caller["sourceFile"], "callerQualified": caller["qualified"],
                          "line": csite, "column": ccol})
        rec["inlineStack"] = stack
    for rec in occ: rec["children"] = []
    for i, rec in enumerate(occ):
        if rec["parentIdx"] is not None: occ[rec["parentIdx"]]["children"].append(i)

    # Regression oracle: the independently hand-verified milestone-3 `decodeOptionalBlobSchedule`
    # slice (BlobScheduleInstance.lean). The generator must reproduce it exactly, so a silent drift
    # in ranges/entry/exit/decl-line/inline-stack/nesting fails generation rather than the proof.
    #
    # Stated in RELOCATION-INVARIANT form: the object-relative entry (offset into the decoder `.text`),
    # each region's offset from the entry and its size, the exit's offset from the entry, and the
    # DWARF facts (decl line, child count, inline stack). Absolute PCs shift with the text base, so
    # pinning them would spuriously fail the relocation acceptance test; the relative layout is exactly
    # what must stay fixed under relinking.
    bs = next((o for o in occ if o["qualified"] == "ssz_raw.decodeOptionalBlobSchedule"), None)
    dbase = text_bases.get("decoder")
    ORACLE = {
        "entryOffset": 0x29a8,
        "regionsRel": [(0, 8), (48, 48), (100, 268)],
        "exitRel": 368, "declLine": 396, "nchildren": 3,
        "inlineStack": [("ssz_raw.decodeRaw", 211, 48), ("ssz_raw.decodeChainConfig", 355, 44),
                        ("ssz_raw.decodeForkConfig", 371, 56)],
    }
    if bs is None:
        raise SystemExit("REGRESSION: no decodeOptionalBlobSchedule occurrence generated")
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

    # entry occurrence — the program cannot be emitted without one (Lean references occ<entry>Id), so a
    # missing entry is a hard failure, not a surfaced defect.
    entry_idx = next((i for i,r in enumerate(occ) if r["qualified"]=="raw_decoder_root.zesu_decode_raw" and r["kind"]=="emitted"), None)
    if entry_idx is None:
        raise SystemExit("GENERATION FAILURE: no emitted zesu_decode_raw entry occurrence")

    for r in occ: del r["_die"]
    # stable order (does not affect identity; makes output deterministic + reviewable)
    order = sorted(range(len(occ)), key=lambda i:(occ[i]["entryPc"], occ[i]["qualified"], tuple(occ[i]["specialization"]), occ[i]["dieOffset"]))
    reindex = {old:new for new,old in enumerate(order)}
    occ_sorted = []
    for old in order:
        r = dict(occ[old]); r["parentIdx"] = reindex[r["parentIdx"]] if r["parentIdx"] is not None else None
        r["children"] = sorted(reindex[c] for c in r["children"]); occ_sorted.append(r)
    entry_idx = reindex[entry_idx]

    # Attribution defects decidable from the inline tree alone (uncovered-reachable PCs are a CFG
    # property proved in the Lean reachable partition, not decidable here).
    defects.extend(sibling_overlap_defects(occ_sorted))

    # Per-routine resolved declaration line (from DWARF `DW_AT_decl_line` via abstract origin). Every
    # occurrence of a routine must resolve to the SAME declaration; a disagreement is an ambiguous
    # attribution. The Lean provenance check proves each occurrence's declSpan equals this resolved
    # line, so declSpan is validated against the routine's resolved declaration, not merely `> 0`.
    decl_by_q = {}
    for o in occ_sorted:
        decl_by_q.setdefault(o["qualified"], set()).add(o["declLine"])
    for q, lines in sorted(decl_by_q.items()):
        if len(lines) != 1:
            defects.append({"kind":"ambiguousAttribution", "address":0, "candidates":[], "name":q,
                            "reason":f"inconsistent decl lines {sorted(lines)}"})
    decl_lines = [{"qualified":q, "declLine":sorted(lines)[0]} for q, lines in sorted(decl_by_q.items())]

    # Reachable-but-excluded emitted glue, sorted for determinism (entry PC, then name, then DIE).
    excluded_sorted = sorted(excluded_occ, key=lambda x:(x["entryPc"], x["qualified"], x["dieOffset"]))
    for x in excluded_sorted: del x["dieOffset"]

    # Independently generated pinned-source manifest: each cataloged source file mapped to the SHA-256
    # of its pinned content, computed here from the exact source the extractor read. The handwritten
    # row-1 `pinnedSourceManifest` is CHECKED against this (review blocker #5) rather than trusted.
    source_manifest = sorted(({"path": pth, "sha256": file_hash[pth]} for pth in set(file_hash)),
                             key=lambda e: e["path"])

    program = {"decoderTextSha256":DECODER_TEXT_SHA, "extractorVersion":EXTRACTOR_VERSION,
               "textBases":text_bases, "runtimeFuncBase":runtime_func_base, "objectSha256":object_sha,
               "sourceManifest":source_manifest, "declLines":decl_lines,
               "entryIndex":entry_idx, "occurrences":occ_sorted, "excludedRoutines":excluded_sorted,
               "defects":sorted(defects, key=lambda x:json.dumps(x,sort_keys=True))}
    if a.out_json: open(a.out_json,"w").write(json.dumps(program, indent=2, sort_keys=True) + "\n")
    if a.out_lean: open(a.out_lean,"w").write(emit_lean(program))
    if a.out_md: open(a.out_md,"w").write(emit_md(program))
    routines = {(o["qualified"], tuple(o["specialization"])) for o in occ_sorted}
    print(f"occurrences={len(occ_sorted)} routines={len(routines)}/43 defects={len(program['defects'])} "
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
    defects reference the emitted `occ<i>Id` identities, which are defined above the program."""
    k = d["kind"]
    if k == "ambiguousAttribution":
        cands = "[" + ", ".join(str(c) for c in d.get("candidates", [])) + "]"
        return f'AttributionDefect.ambiguousAttribution {d["address"]} {cands}'
    if k == "unmappedRegion":
        r = d["range"]
        return f'AttributionDefect.unmappedRegion {{ start := {r["start"]}, size := {r["size"]} }}'
    if k == "overlappingOwnership":
        return (f'AttributionDefect.overlappingOwnership {d["address"]} '
                f'occ{d["firstIdx"]}Id occ{d["secondIdx"]}Id')
    if k == "uncovered":
        return f'AttributionDefect.uncovered {d["address"]}'
    raise SystemExit(f"defect_lean: unknown defect kind {k!r}")
def lean_id(o):
    decl = f'{{ file := {{ path := {lean_str(o["sourceFile"])} }}, qualifiedName := {lean_str(o["qualified"])} }}'
    spec = "#[" + ", ".join(lean_str(s) for s in o["specialization"]) + "]"
    stack = "[" + ", ".join(
        f'{{ caller := {{ file := {{ path := {lean_str(s["callerFile"])} }}, qualifiedName := {lean_str(s["callerQualified"])} }},'
        f' callSite := {{ line := {s["line"]}, column := {s["column"]} }} }}' for s in o["inlineStack"]) + "]"
    return f'{{ function := {{ declaration := {decl}, specialization := {spec} }}, inlineStack := {stack} }}'

def emit_lean(p):
    L = ["import BinaryFv.Binary.Elfling.Instance", "",
         "/-!", "# Generated Elfling program (milestone 4)", "",
         "Deterministically generated from the validated DWARF sidecars by",
         "`docs/ai/plan/artifacts/generate_program.py`. Address-bearing, UNTRUSTED: the Lean validation",
         "(`ProgramValidation.lean`) checks every range/word against the canonical ELF and discharges",
         "`coverage` / `sourceProvenanceRecorded` / `IsCanonicalGeneratedProgram`. Object `.text` bases,",
         "readArray widths (from `DW_AT_call_line` -> pinned source), and glue-folding are recorded in the",
         "companion JSON. Regenerating is byte-deterministic (checked twice in the derivation).", "-/", "",
         "namespace BinaryFv.SSZ.Zesu.Elfling.Generated", "",
         "open BinaryFv.Binary (AddressRange)", "open BinaryFv.Binary.Elfling", ""]
    prov = lambda o: (f'{{ sidecarHash := {lean_str(p["objectSha256"][o["objkind"]])}, entryOffset := {o["dieOffset"]},'
                      f' extractorVersion := {lean_str(p["extractorVersion"])} }}')
    # All address-free identities first (they reference nothing), so the FunctionInstances below can
    # forward-reference each other's ids for parent?/children (which form a mutual parent/child graph).
    L.append("/-! ### Occurrence identities (address-free). -/")
    for i, o in enumerate(p["occurrences"]):
        L.append(f'def occ{i}Id : InstanceId := {lean_id(o)}')
    L.append("")
    L.append("/-! ### Occurrence instances (address-bearing). -/")
    for i, o in enumerate(p["occurrences"]):
        regions = "#[" + ", ".join(f'{{ start := {r["start"]}, size := {r["size"]} }}' for r in o["regions"]) + "]"
        parent = "none" if o["parentIdx"] is None else f'some occ{o["parentIdx"]}Id'
        children = "#[" + ", ".join(f'occ{c}Id' for c in o["children"]) + "]"
        L.append(f'/-- occ {i}: {o["qualified"]}{("["+",".join(o["specialization"])+"]") if o["specialization"] else ""}'
                 f' ({o["kind"]}, entry 0x{o["entryPc"]:x}). -/')
        L.append(f'def occ{i} : FunctionInstance :=')
        L.append(f'  {{ id := occ{i}Id, regions := {regions}, entryPc := {o["entryPc"]}, exitPcs := #[{o["exitPc"]}],')
        L.append(f'    parent? := {parent}, children := {children}, externalCalls := #[],')
        L.append(f'    declProvenance := {{ sourceFileHash := {lean_str(o["sourceFileHash"])}, declSpan := {{ line := {o["declLine"]}, column := 1 }} }},')
        L.append(f'    provenance := {prov(o)}, symbol? := none }}')
        L.append("")
    L.append("/-- Every generated occurrence. -/")
    L.append("def generatedInstances : Array FunctionInstance :=")
    L.append("  #[" + ", ".join(f'occ{i}' for i in range(len(p["occurrences"]))) + "]")
    L.append("")
    ei = p["entryIndex"]
    L.append(f'/-- The complete generated program: entry `zesu_decode_raw` (occ {ei}), all reachable')
    L.append("    occurrences, and the surfaced attribution defects. -/")
    # Authoritative: the emitted defect list is exactly the generator's, never a hardcoded `#[]`. The
    # derivation additionally FAILS when this list is nonempty, so in a released program it is `#[]`
    # because there were no defects — not because emission discarded them.
    defects = "#[" + ", ".join(defect_lean(d) for d in p["defects"]) + "]"
    L.append("def generatedProgram : Program :=")
    L.append(f'  {{ entry := occ{ei}Id, instances := generatedInstances, defects := {defects},')
    L.append(f'    provenance := {prov(p["occurrences"][ei])} }}')
    L.append("")
    # Reachable-but-excluded taxonomy (auditable data the reachable-partition proof consumes).
    L.append("/-! ### Reachable-but-excluded emitted routines (auditable exclusion taxonomy). -/")
    L.append("")
    L.append("/-- A reachable code routine carrying no cataloged occurrence: emitted glue the optimizer")
    L.append("did not fold into a cataloged ancestor. Address-bearing, untrusted auditable data; the Lean")
    L.append("reachable-partition validation checks these regions exactly tile `reachable \\ covered`. -/")
    L.append("structure ExcludedOccurrence where")
    L.append("  qualifiedName : String")
    L.append("  category : String")
    L.append("  regions : Array AddressRange")
    L.append("deriving Repr, Inhabited, DecidableEq")
    L.append("")
    L.append("/-- Every reachable-but-excluded emitted routine: DWARF name, category, canonical regions. -/")
    L.append("def generatedExcludedOccurrences : Array ExcludedOccurrence :=")
    if p["excludedRoutines"]:
        items = []
        for x in p["excludedRoutines"]:
            regions = "#[" + ", ".join(f'{{ start := {r["start"]}, size := {r["size"]} }}' for r in x["regions"]) + "]"
            items.append(f'  {{ qualifiedName := {lean_str(x["qualified"])}, category := {lean_str(x["category"])},'
                         f' regions := {regions} }}')
        L.append("  #[" + ",\n   ".join(items) + "]")
    else:
        L.append("  #[]")
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
    L.append("qualified name. `GeneratedProvenanceCheck` proves every occurrence's declSpan line equals its")
    L.append("routine's resolved line here, so declSpan is checked against the resolved declaration. -/")
    L.append("def generatedDeclLines : List (String × Nat) :=")
    dl = ", ".join(f'({lean_str(e["qualified"])}, {e["declLine"]})' for e in p["declLines"])
    L.append("  [" + dl + "]")
    L.append("")
    L.append("end BinaryFv.SSZ.Zesu.Elfling.Generated")
    L.append("")
    return "\n".join(L)

def emit_md(p):
    M = ["# Generated Elfling program — source/function/CFG index", "",
         f"Deterministically generated from the DWARF sidecars. {len(p['occurrences'])} occurrences over "
         f"{len({(o['qualified'],tuple(o['specialization'])) for o in p['occurrences']})}/43 catalog routines; "
         f"{len(p['defects'])} attribution defect(s).", "",
         "| # | routine | spec | kind | entry PC | regions | parent | inline depth |",
         "|--:|---------|------|------|---------:|--------:|-------:|-------------:|"]
    for i, o in enumerate(p["occurrences"]):
        spec = ",".join(o["specialization"]) or "—"
        par = "—" if o["parentIdx"] is None else str(o["parentIdx"])
        M.append(f"| {i} | `{o['qualified']}` | {spec} | {o['kind']} | 0x{o['entryPc']:x} | "
                 f"{len(o['regions'])} | {par} | {len(o['inlineStack'])} |")
    ex = p.get("excludedRoutines", [])
    if ex:
        total = sum((r["size"] // 4) for x in ex for r in x["regions"])
        M += ["", f"## Reachable-but-excluded routines ({len(ex)} routines, {total} region words)", "",
              "Emitted glue reachable from `zesu_decode_raw` that carries no cataloged occurrence. "
              "The Lean reachable-partition validation proves these exactly account for the reachable "
              "PCs no cataloged occurrence covers.", "",
              "| # | routine | category | regions | words |",
              "|--:|---------|----------|--------:|------:|"]
        for i, x in enumerate(ex):
            w = sum(r["size"] // 4 for r in x["regions"])
            M.append(f"| {i} | `{x['qualified']}` | {x['category']} | {len(x['regions'])} | {w} |")
    if p["defects"]:
        M += ["", "## Attribution defects", ""] + [f"- `{json.dumps(d)}`" for d in p["defects"]]
    M.append("")
    return "\n".join(M)

if __name__ == "__main__":
    main()
