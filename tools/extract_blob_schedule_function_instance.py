#!/usr/bin/env python3
"""
Deterministic vertical-slice extractor for `decodeOptionalBlobSchedule` (milestone 3).

Reads the DWARF *sidecar* decoder object (validated byte-identical to the canonical stripped object,
so its debug info describes the canonical bytes), identifies the single inline function instance of
`ssz_raw.decodeOptionalBlobSchedule`, its inline call stack, and its nested child inline function instances,
maps every object-relative range to a canonical-ELF PC (`+TEXT_BASE`), and emits deterministic JSON.

Milestone-3 slice only (one function). The milestone-4 generator generalizes it. Determinism: DWARF
DIE order is fixed; ranges are read verbatim; the PC map is a constant add.
"""
import json, re, subprocess, sys

# Options that take a following value. Bare args are positional (the sidecar object).
_OPTS_WITH_VAL = {"--dwarfdump", "--out-lean"}
def _opt(name, default=None):
    a = sys.argv
    for i, x in enumerate(a):
        if x == name and i + 1 < len(a): return a[i + 1]
        if x.startswith(name + "="): return x[len(name) + 1:]
    return default
_pos, _skip = [], False
for x in sys.argv[1:]:
    if _skip: _skip = False; continue
    if x in _OPTS_WITH_VAL: _skip = True; continue
    if x.startswith("--"): continue
    _pos.append(x)

# The nix derivation always passes --dwarfdump; the pinned path is only a fallback default.
DWARFDUMP = _opt("--dwarfdump",
                 "/nix/store/l25n688gmqircnpypip13wy99ndycwbj-llvm-21.1.8/bin/llvm-dwarfdump")
SIDE = _pos[0] if _pos else \
    "/nix/store/rnv92qsn9b0kmpgvy0k5894zvsh9mbwi-zesu-raw-ssz-rv64im-sidecar-96f1621/obj/zesu-raw-ssz-decoder.o"
OUT_LEAN = _opt("--out-lean", "BinaryFv/SSZ/Zesu/Elfling/BlobScheduleFunctionInstance.lean")
TEXT_BASE = 0x102b0          # decoder object .text base in the canonical linked ELF (Amendment A)
SRC_PREFIX = "/build/source/"

def dwdump(*args):
    return subprocess.run([DWARFDUMP, *args, SIDE], capture_output=True, text=True).stdout

def norm(p): return p[len(SRC_PREFIX):] if p and p.startswith(SRC_PREFIX) else p
def qname(v):
    m = re.search(r'"([^"]+)"', v or ""); return m.group(1) if m else None
def canon(rs): return [{"start": TEXT_BASE + a, "size": b - a} for (a, b) in rs]

def die_offset_of_instance():
    """Deterministically find the DIE offset of the single decodeOptionalBlobSchedule inline."""
    lines = dwdump("--debug-info").splitlines()
    for i, ln in enumerate(lines):
        if ln.strip().endswith("DW_TAG_inlined_subroutine"):
            off = re.match(r'(0x[0-9a-f]+):', ln)
            if off and i + 1 < len(lines) and \
               qname(lines[i + 1]) == "ssz_raw.decodeOptionalBlobSchedule" and \
               "DW_AT_abstract_origin" in lines[i + 1]:
                return off.group(1)
    raise SystemExit("decodeOptionalBlobSchedule inline function instance not found")

def parse_ranges(block_lines):
    return [(int(a, 16), int(b, 16))
            for (a, b) in re.findall(r'\[0x([0-9a-f]+), 0x([0-9a-f]+)\)', "\n".join(block_lines))]

off = die_offset_of_instance()

# Parents (inline call stack, outermost-first).
plines = dwdump(f"--debug-info={off}", "--show-parents", "--parent-recurse-depth=12").splitlines()
frames = []            # ordered: subprogram then inlined ancestors then the function instance
i = 0
while i < len(plines):
    m = re.match(r'0x[0-9a-f]+:\s*(DW_TAG_(?:subprogram|inlined_subroutine))', plines[i])
    if m:
        attrs = {}
        j = i + 1
        while j < len(plines) and not re.match(r'0x[0-9a-f]+:\s*DW_TAG_', plines[j]):
            am = re.search(r'(DW_AT_\w+)\s*\((.*)\)\s*$', plines[j])
            if am: attrs[am.group(1)] = am.group(2)
            j += 1
        frames.append((m.group(1), attrs)); i = j
    else:
        i += 1
sub = next(a for t, a in frames if t == "DW_TAG_subprogram")
enclosing = qname(sub.get("DW_AT_name"))
inlined = [(t, a) for t, a in frames if t == "DW_TAG_inlined_subroutine"]
callers = [enclosing] + [qname(a["DW_AT_abstract_origin"]).split(".", 1)[-1] for _, a in inlined[:-1]]
inline_stack = []
for caller, (_, a) in zip(callers, inlined):
    inline_stack.append({
        "callerQualified": "ssz_raw." + caller,
        "callLine": int(re.search(r'\d+', a["DW_AT_call_line"]).group()),
        "callColumn": int(re.search(r'\d+', a.get("DW_AT_call_column", "0")).group()),
    })

# Function instance subtree (ranges + immediate children).
_all = dwdump(f"--debug-info={off}", "--show-children").splitlines()
root_idx = next(i for i, l in enumerate(_all) if l.strip().startswith(off + ":"))
slines = _all[root_idx:]
root_indent = len(re.match(r'0x[0-9a-f]+:(\s*)', slines[0]).group(1))
# collect all range brackets belonging to the root's own DW_AT_ranges (before first child DIE)
inst_ranges, k = [], 1
while k < len(slines) and not re.match(r'0x[0-9a-f]+:\s*DW_TAG_inlined_subroutine', slines[k]):
    inst_ranges += re.findall(r'\[0x([0-9a-f]+), 0x([0-9a-f]+)\)', slines[k]); k += 1
inst_ranges = [(int(a, 16), int(b, 16)) for a, b in inst_ranges]

children = []
i = 0
for i, ln in enumerate(slines):
    cm = re.match(r'0x[0-9a-f]+:(\s*)DW_TAG_inlined_subroutine', ln)
    if not cm or i == 0: continue
    indent = len(cm.group(1))
    # immediate children sit exactly one nesting level deeper than the root's attrs
    if i + 1 < len(slines) and "DW_AT_abstract_origin" in slines[i + 1]:
        attrs, rngs, j = {}, [], i + 1
        while j < len(slines) and not re.match(r'0x[0-9a-f]+:\s*DW_TAG_', slines[j]):
            am = re.search(r'(DW_AT_\w+)\s*\((.*)\)\s*$', slines[j])
            if am: attrs[am.group(1)] = am.group(2)
            rngs += re.findall(r'\[0x([0-9a-f]+), 0x([0-9a-f]+)\)', slines[j]); j += 1
        q = qname(attrs.get("DW_AT_abstract_origin"))
        # only record the direct (shallowest) children of the function instance
        if indent == root_indent + 2:
            children.append({
                "qualified": q,
                "callLine": int(re.search(r'\d+', attrs.get("DW_AT_call_line", "0")).group()),
                "callColumn": int(re.search(r'\d+', attrs.get("DW_AT_call_column", "0")).group()),
                "regions": canon([(int(a, 16), int(b, 16)) for a, b in rngs]),
            })

result = {
    "textBase": TEXT_BASE,
    "sidecar": SIDE,
    "dieOffset": off,
    "function": {"file": "src/stateless/stateless/ssz_raw.zig",
                 "qualified": "ssz_raw.decodeOptionalBlobSchedule"},
    "inlineStack": inline_stack,
    "regions": canon(inst_ranges),
    "children": children,
}

# --- Lean emission (milestone-3 generated data module) -----------------------------------------
def emit_lean(d, src_hash="ea5a1b36f72c888a0bcb73f2ea1f2bf7ebf00c63c6460c84015d0f6783a1d131"):
    SF = 'decoderSourceFile'
    def sdecl(q): return f'{{ file := {SF}, qualifiedName := "{q}" }}'
    def rng(r): return f'{{ start := {r["start"]}, size := {r["size"]} }}'
    def regions(rs): return "#[" + ", ".join(rng(r) for r in rs) + "]"
    def stack(sites):
        return "[" + ", ".join(
            f'{{ caller := {sdecl(s["callerQualified"])}, callSite := {{ line := {s["callLine"]}, column := {s["callColumn"]} }} }}'
            for s in sites) + "]"
    L = []
    L.append("-- GENERATED FILE: produced by tools/extract_blob_schedule_function_instance.py. DO NOT EDIT.")
    L.append("import BinaryFv.Binary.Elfling.FunctionInstance")
    L.append("")
    L.append("/-!")
    L.append("# Generated Elfling data — `decodeOptionalBlobSchedule` vertical slice (milestone 3)")
    L.append("")
    L.append("Deterministically extracted from the validated DWARF sidecar")
    L.append(f"(`{d['sidecar'].split('/')[-1]}`, decoder `.text` sha256 f946b25e…, DIE {d['dieOffset']}) by")
    L.append("`tools/extract_blob_schedule_function_instance.py`. Object-relative DWARF ranges are")
    L.append("mapped to canonical-ELF PCs by `+0x102b0` (the decoder object `.text` base, Amendment A).")
    L.append("This is address-bearing generated data (untrusted); `BlobScheduleMapping.lean` validates it")
    L.append("against the canonical trace and binds it to the address-free catalog identity and contract.")
    L.append("-/")
    L.append("")
    L.append("namespace BinaryFv.SSZ.Zesu.Elfling")
    L.append("")
    L.append("open BinaryFv.Binary.Elfling")
    L.append("")
    L.append(f'def {SF} : SourceFile := {{ path := "{d["function"]["file"]}" }}')
    L.append("")
    prov = (f'{{ sidecarHash := "f946b25ea2a0d19ee82ade02ef14eebce363e16190bf54a117eea7eec7805d3b",'
            f' entryOffset := {int(d["dieOffset"],16)}, extractorVersion := "blob-schedule-slice-v1" }}')
    # primary function instance identity
    L.append("/-- Address-free identity of the single inline function instance of `decodeOptionalBlobSchedule`. -/")
    L.append(f'def blobScheduleFunctionInstanceId : FunctionInstanceId :=')
    L.append(f'  {{ function := {{ declaration := {sdecl(d["function"]["qualified"])}, specialization := #[] }},')
    L.append(f'    inlineStack := {stack(d["inlineStack"])} }}')
    L.append("")
    # parent (decodeForkConfig function instance) identity — referenced only, not materialized
    L.append("/-- The enclosing function instance (`decodeForkConfig`) this function instance is inlined into. -/")
    L.append(f'def blobScheduleParentId : FunctionInstanceId :=')
    L.append(f'  {{ function := {{ declaration := {sdecl("ssz_raw.decodeForkConfig")}, specialization := #[] }},')
    L.append(f'    inlineStack := {stack(d["inlineStack"][:-1])} }}')
    L.append("")
    # child readU64 function instance ids
    child_ids = []
    for n, c in enumerate(d["children"]):
        cid = f'readU64Field{n}Id'
        child_ids.append(cid)
        site = f'{{ caller := {sdecl(d["function"]["qualified"])}, callSite := {{ line := {c["callLine"]}, column := {c["callColumn"]} }} }}'
        L.append(f'/-- `readU64` reading blob-schedule field {n} (source line {c["callLine"]}). -/')
        L.append(f'def {cid} : FunctionInstanceId :=')
        L.append(f'  {{ function := {{ declaration := {sdecl(c["qualified"])}, specialization := #[] }},')
        L.append(f'    inlineStack := {stack(d["inlineStack"])} ++ [{site}] }}')
        L.append("")
    # child function instances
    for n, c in enumerate(d["children"]):
        rs = c["regions"]; entry = min(r["start"] for r in rs); last = max(r["start"]+r["size"] for r in rs)
        L.append(f'def readU64Field{n}FunctionInstance : FunctionInstance :=')
        L.append(f'  {{ id := readU64Field{n}Id, regions := {regions(rs)}, entryPc := {entry}, exitPcs := #[{last}],')
        L.append(f'    parent? := some blobScheduleFunctionInstanceId, children := #[], externalCalls := #[],')
        L.append(f'    declProvenance := {{ sourceFileHash := "{src_hash}", declSpan := {{ line := 563, column := 1 }} }},')
        L.append(f'    provenance := {prov}, symbol? := none }}')
        L.append("")
    # primary function instance
    rs = d["regions"]; entry = min(r["start"] for r in rs); last = max(r["start"]+r["size"] for r in rs)
    L.append("/-- The generated `decodeOptionalBlobSchedule` function instance: three discontiguous canonical-ELF")
    L.append("    fragments, three nested `readU64` field reads, inlined into `decodeForkConfig`. -/")
    L.append("def blobScheduleFunctionInstance : FunctionInstance :=")
    L.append(f'  {{ id := blobScheduleFunctionInstanceId, regions := {regions(rs)}, entryPc := {entry}, exitPcs := #[{last}],')
    L.append(f'    parent? := some blobScheduleParentId, children := #[{", ".join(child_ids)}], externalCalls := #[],')
    L.append(f'    declProvenance := {{ sourceFileHash := "{src_hash}", declSpan := {{ line := 396, column := 1 }} }},')
    L.append(f'    provenance := {prov}, symbol? := none }}')
    L.append("")
    L.append("/-- The function instance together with its nested children, as extracted. -/")
    L.append(f'def blobScheduleFunctionInstances : Array FunctionInstance :=')
    L.append(f'  #[blobScheduleFunctionInstance, {", ".join(c+"FunctionInstance" for c in ["readU64Field%d"%n for n in range(len(d["children"]))])}]')
    L.append("")
    L.append("end BinaryFv.SSZ.Zesu.Elfling")
    return "\n".join(L)

if "--json" in sys.argv:
    print(json.dumps(result, indent=2))
if "--lean" in sys.argv:
    open(OUT_LEAN, "w").write(emit_lean(result) + "\n")
    sys.stderr.write(f"wrote {OUT_LEAN}\n")
