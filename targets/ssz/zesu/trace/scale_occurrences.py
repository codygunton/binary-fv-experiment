#!/usr/bin/env python3
"""Row C: scale the per-occurrence production-ELF validation from the blob-schedule vertical slice to
ALL occurrences in `program.json`.

Coverage is PER OCCURRENCE — an occurrence is validated only on evidence in which its OWN region
executes, never inherited from another occurrence of the same source routine. Every check that cannot
be evaluated for an occurrence is recorded as an EXPLICIT gap, never silently counted as a pass.

Evidence: the UNCHANGED production `zesu-ssz` ELF run under pinned `qemu-riscv64` with the diagnostic
trace plugin (`qemu_trace_plugin.so`). The plugin is self-contained — each store carries the stack
pointer — so write classification needs no separate GDB register capture, which is what makes a single
full-run trace cover ~all occurrences at once. Nothing is rebuilt, relinked, patched, or instrumented.

The generic per-occurrence checks (apply to all occurrences, trace-only):
  entryReached          the first in-region PC executed is the declared entryPc (the occurrence is
                        entered at its binding entry); invocations are counted by entryPc executions
  controlFlowIntegrity  execution enters the occurrence's own code ONLY at a declared basic-block
                        boundary — every non-fallthrough transfer into an in-region PC lands on a
                        `blocks[].start`. (The `edges` list is a non-exhaustive subset of the true CFG;
                        the `blocks` partition IS exhaustive, so it is the sound reference. Undeclared
                        but block-aligned internal edges and out-of-region call/return targets are
                        recorded as facts, and validated on their own by the child/callee occurrences.)
  withinStepBound       max per-invocation instruction count <= the routine's contract step bound
                        (const bounds + readArray's specialization width; input-dependent bounds = gap)
  allocationConsistent  a NON-allocating routine never bumps the allocator cursor (.sbss); the
                        allocation ACT is a cursor store. Heap stores alone are allowed — a
                        non-allocating routine may fill a buffer a caller allocated (and memcpy/memmove
                        copy into the heap by design).
  inputPreserved        no store into the read-only SSZ input buffer
  codePreserved         no store into the .text code region
  writesClassified      every in-region store lands in a known region (code/cursor/heap/input/global/
                        stack, sp taken from the store record itself) — no unclassified writes
  meaningTie            routine-specific: for scalar/offset/slice leaf readers the value read from the
                        input is faithfully carried to a result store. Claimed PASS only on a clean
                        tie; otherwise an EXPLICIT gap (never a failure — a missed heuristic tie is not
                        evidence of a binding violation). The rigorous per-value meaning check is the
                        kernel-checked vertical slice (occurrence 116), not this lightweight scan.

This is diagnostic-only evidence and is NEVER imported by the theorem graph.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Pinned production memory layout (from the zesu-ssz ELF section headers / symbols; see STATUS).
TEXT = (65768, 81704)            # code — read-only (code preservation)
CURSOR = (86032, 86048)          # .sbss allocator cursor (ZKVM_HEAP_TOP@86032, ZKVM_HEAP_POS@86040)
HEAP = (86048, 67194912)         # bump heap (allocated blocks)
INPUT = (67194912, 69292064)     # SSZ input buffer — read-only (input preservation)
GLOBALS = (69292064, 69292928)   # decoder statics (stored_result / last_status / attempted / ...)
STACK_WINDOW = 1 << 16           # a store is "stack" if within this of its own recorded sp


def classify_write(addr: int, sp: int) -> str:
    if TEXT[0] <= addr < TEXT[1]:
        return "code"
    if CURSOR[0] <= addr < CURSOR[1]:
        return "allocator-cursor"
    if HEAP[0] <= addr < HEAP[1]:
        return "heap"
    if INPUT[0] <= addr < INPUT[1]:
        return "input"
    if GLOBALS[0] <= addr < GLOBALS[1]:
        return "decoder-global"
    if sp - STACK_WINDOW <= addr <= sp + STACK_WINDOW:
        return "stack"
    return "unclassified"


def parse_trace(path: Path):
    """Parse the self-contained plugin trace into (executed, loads, stores).
    executed: [pc]; loads: [(pc,addr,w,v)]; stores: [(pc,addr,w,v,sp)]."""
    executed, loads, stores = [], [], []
    with open(path) as fh:
        for line in fh:
            p = line.split()
            if not p:
                continue
            if p[0] == "E":
                executed.append(int(p[1]))
            elif p[0] == "L":
                loads.append((int(p[1]), int(p[2]), int(p[3]), int(p[4])))
            elif p[0] == "S":
                # S <pc> <addr> <width> <value> <sp>  (sp appended by the register-reading plugin)
                sp = int(p[5]) if len(p) > 5 else 0
                stores.append((int(p[1]), int(p[2]), int(p[3]), int(p[4]), sp))
    return executed, loads, stores


def step_bound_for(short: str, occ, catalog, arglb: dict):
    """Resolve a CONCRETE numeric step bound for an occurrence, or None (an explicit gap) if the
    contract argument is not observable from the occurrence's own trace.

    Input-dependent contract bounds have the shape `bound(arg) = C + K*(arg//D + E)`, monotonic
    non-decreasing in `arg`. Verifying `maxInsn <= bound(actualArg)` needs a value of `arg`, but a
    SOUND LOWER bound `argLB <= actualArg` suffices: since `bound` is non-decreasing,
    `bound(argLB) <= bound(actualArg)`, so `maxInsn <= bound(argLB)` implies `maxInsn <= bound(actualArg)`.
    The sound lower bounds (in `arglb`):
      inputLen   the whole-input byte length (entry routines: their slice IS the whole input — exact);
      inputBytes the count of distinct in-region input-buffer bytes the occurrence read (a decoder reads
                 only within its own slice, so this is <= the slice length);
      copyLen    the in-region store count (memcpy/memmove store <= `length` bytes, one chunk per store).
    `unobservable` args (e.g. requireCanonicalOffsets' caller-passed offsets.length) stay explicit gaps.
    readArray's `32 + 4*width` is fixed per-occurrence by its comptime element width (specialization)."""
    meta = catalog.get(short)
    if not meta:
        return None, "no catalog entry", None
    sb = meta["stepBound"]
    if "const" in sb:
        return sb["const"], None, {"kind": "const"}
    if short == "readArray":
        spec = occ.get("specialization") or []
        if spec and str(spec[0]).isdigit():
            width = int(spec[0])
            return 32 + 4 * width, None, {"kind": "readArray", "width": width}
        return None, "readArray width not in specialization", None
    form = meta.get("stepBoundForm")
    if form:
        src = form["arg"]
        if src == "unobservable":
            return None, "input-dependent bound; argument not observable: " + form.get("interfaceNote", ""), None
        argv = arglb.get(src)
        if argv is None:
            return None, f"input-dependent bound; {src} not available", None
        C, K, D, E = form["C"], form["K"], form["D"], form["E"]
        bound = C + K * (argv // D + E)
        return bound, None, {"kind": "form", "C": C, "K": K, "D": D, "E": E,
                             "arg": src, "argLB": argv, "bound": bound}
    if "inputDependent" in sb:
        return None, f"input-dependent bound: {sb['inputDependent']}", None
    return None, sb.get("unknown", "unknown bound"), None


STORE_SUMMARY_TIES = {"raw"}  # memcpy/memmove: summarize the (large) destination-buffer write set


def reduce_occurrence(occ, short, catalog, executed, loads, stores, input_len=0):
    """Extract the COMPACT, deterministic per-occurrence facts the checker consumes — observed facts
    only; the expected binding/bound/layout live in the checker. This is the reduction that BOTH the
    Python oracle (`evaluate_facts`) and the generated Lean checker evaluate identically."""
    ranges = [(r["start"], r["start"] + r["size"]) for r in occ["regions"]]
    entry_pc = occ["entryPc"]
    block_starts = sorted({b["start"] for b in occ["blocks"]})
    bs_set = set(block_starts)

    def in_region(pc):
        return any(a <= pc < b for a, b in ranges)

    in_region_idx = [i for i, pc in enumerate(executed) if in_region(pc)]
    meta = catalog.get(short, {})
    f: dict[str, object] = {
        "index": occ.get("index"),
        "qualified": occ["qualified"], "routine": short,
        "entryPc": entry_pc, "covered": len(in_region_idx) > 0,
        "allocates": meta.get("allocates", False),
        "meaningTieKind": meta.get("meaningTie", "structural"),
    }
    if not in_region_idx:
        return f

    f["firstInRegion"] = executed[in_region_idx[0]]
    entry_idxs = [i for i, pc in enumerate(executed) if pc == entry_pc]
    f["invocations"] = len(entry_idxs)
    if entry_idxs:
        bounds = entry_idxs + [len(executed)]
        per_inv = [sum(1 for pc in executed[a:b] if in_region(pc)) for a, b in zip(bounds, bounds[1:])]
    else:
        per_inv = [len(in_region_idx)]
    f["maxInsnPerInvocation"] = max(per_inv)

    # non-fallthrough transfers that LAND in-region → their targets must be declared block-starts.
    land_targets, out_targets = set(), set()
    for i in range(len(executed) - 1):
        s, t = executed[i], executed[i + 1]
        if t == s + 2 or t == s + 4:
            continue
        if in_region(t):
            land_targets.add(t)
        elif in_region(s):
            out_targets.add(t)
    f["blockStarts"] = block_starts
    f["landingTargets"] = sorted(land_targets)
    f["offBlockLandings"] = sorted(t for t in land_targets if t not in bs_set)
    f["outOfRegionTargets"] = sorted(out_targets)

    tie = f["meaningTieKind"]

    # Classify every in-region store with its OWN recorded sp. Stack addresses are environment-dependent
    # (the guest stack base shifts between hosts even under `setarch -R`), so they are NOT carried as
    # absolute values; only their (benign) "stack" class is summarized via `hadStackStore`. Every other
    # region (code/cursor/heap/input/global) sits at a FIXED vaddr in the static -no-pie ELF, so those
    # addresses are deterministic and are carried for the Lean checker to re-classify.
    reg_stores = [(addr, sp) for (pc, addr, w, v, sp) in stores if in_region(pc)]
    f["storeCount"] = len(reg_stores)
    nonstack, had_stack, all_classes = [], False, set()
    for (addr, sp) in reg_stores:
        cls = classify_write(addr, sp)
        all_classes.add(cls)
        if cls == "stack":
            had_stack = True
        else:
            nonstack.append(addr)
    f["hadStackStore"] = had_stack
    f["storeClasses"] = sorted(all_classes)
    if tie in STORE_SUMMARY_TIES:
        # raw mem primitive: the write set is the (large) destination buffer; carry only the class set.
        f["storesSummarized"] = True
        f["inRegionStores"] = []
    else:
        # carry the deterministic non-stack store addresses; the Lean checker re-classifies each.
        f["storesSummarized"] = False
        f["inRegionStores"] = sorted(set(nonstack))

    # meaning-tie witness: a value the routine both LOADED from input and STORED (scalar carried through).
    in_input_loads = [(addr, v) for (pc, addr, w, v) in loads if in_region(pc) and INPUT[0] <= addr < INPUT[1]]
    in_load_vals = sorted({v for (_, v) in in_input_loads})
    store_vals = {v for (pc, addr, w, v, sp) in stores if in_region(pc)}
    f["inputLoadVals"] = in_load_vals
    f["storeHasInputPtr"] = any(INPUT[0] <= v < INPUT[1] for v in store_vals)
    f["scalarCarried"] = any(v in store_vals for v in in_load_vals)

    # Step bound: resolve the (possibly input-dependent) contract bound to a concrete number using SOUND
    # lower bounds on its argument (see step_bound_for). inputBytes = distinct in-region input bytes read
    # (<= the routine's slice length); copyLen = in-region store count (<= bytes copied); inputLen = the
    # whole-input length (entry routines). requireCanonicalOffsets' offsets.length is unobservable -> gap.
    arglb = {
        "inputLen": input_len,
        "inputBytes": len({addr for (addr, _) in in_input_loads}),
        "copyLen": f["storeCount"],
    }
    bound, reason, deriv = step_bound_for(short, occ, catalog, arglb)
    f["stepBound"] = bound
    f["stepBoundGap"] = None if bound is not None else reason
    f["stepBoundDeriv"] = deriv
    return f


def classes_of(f):
    """The distinct write classes for an occurrence — recomputed from the carried non-stack addresses
    (classified with sp=0; they are never stack) plus the summarized `stack` flag, or the summarized set
    for raw mem primitives. Mirrors the Lean checker exactly and equals the reducer's `storeClasses`."""
    if f.get("storesSummarized"):
        return set(f["storeClasses"])
    cls = {classify_write(a, 0) for a in f["inRegionStores"]}
    if f.get("hadStackStore"):
        cls.add("stack")
    return cls


def evaluate_facts(f):
    """The reference oracle: evaluate the generic per-occurrence checks from the compact facts. Returns
    a dict mapping each check to True / False / None (None = explicit gap). The Lean checker computes the
    same booleans on the same facts."""
    checks: dict[str, object] = {}
    gaps: dict[str, str] = {}
    if not f.get("covered"):
        for name in CHECK_NAMES:
            checks[name], gaps[name] = None, "occurrence region not executed by any arm"
        return checks, gaps

    checks["entryReached"] = f["firstInRegion"] == f["entryPc"]
    checks["controlFlowIntegrity"] = len(f["offBlockLandings"]) == 0

    bound = f["stepBound"]
    if bound is None:
        checks["withinStepBound"], gaps["withinStepBound"] = None, f["stepBoundGap"]
    else:
        checks["withinStepBound"] = f["maxInsnPerInvocation"] <= bound

    classes = classes_of(f)
    checks["writesClassified"] = "unclassified" not in classes
    checks["inputPreserved"] = "input" not in classes
    checks["codePreserved"] = "code" not in classes
    checks["allocationConsistent"] = True if f["allocates"] else ("allocator-cursor" not in classes)

    tie = f["meaningTieKind"]
    if tie in ("scalarLE", "offset") and f["scalarCarried"]:
        checks["meaningTie"] = True
    elif tie == "slice" and f["storeHasInputPtr"]:
        checks["meaningTie"] = True
    else:
        checks["meaningTie"] = None
        gaps["meaningTie"] = (f"{tie}: no clean input-to-result value tie in this region "
                              "(deep meaning is validated for occurrence 116 in the Lean checker)")
    return checks, gaps


def run_full_trace(qemu, plugin, elf, input_path, out_path):
    """Run the UNCHANGED ELF under pinned QEMU with the trace plugin (no PC window: whole run).
    setarch -R disables host ASLR for a deterministic guest stack. Returns the ELF decision (0/1)."""
    cmd = ["setarch", "-R", qemu, "-plugin", f"{plugin},out={out_path}", elf]
    with open(input_path, "rb") as fh:
        r = subprocess.run(cmd, stdin=fh, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if r.returncode >= 2:
        raise SystemExit(f"ELF faulted under QEMU on {input_path} (exit {r.returncode})")
    return r.returncode


CHECK_NAMES = ("entryReached", "controlFlowIntegrity", "withinStepBound", "allocationConsistent",
               "inputPreserved", "codePreserved", "writesClassified", "meaningTie")


# --- Lean emission --------------------------------------------------------------------------------

def _oi(n):  # Option Nat
    return "none" if n is None else f"(some {n})"


def _ob(b):  # Option Bool  (None gap / True pass / False fail)
    return "none" if b is None else ("(some true)" if b else "(some false)")


def _ln(xs):  # List Nat
    return "[" + ", ".join(str(x) for x in xs) + "]"


def _lp(xs):  # List (Nat × Nat)
    return "[" + ", ".join(f"({a}, {b})" for a, b in xs) + "]"


def _ls(xs):  # List String
    return "[" + ", ".join('"' + str(s).replace('"', '\\"') + '"' for s in xs) + "]"


def _b(x):
    return "true" if x else "false"


def _str(s):
    return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'


def occ_to_lean(rec) -> str:
    """One `(OccScaleEvidence × ScaleChecks)` tuple literal, deterministic."""
    f, c = rec["facts"], rec["checks"]
    ev = (
        f"{{ index := {rec['index']}, qualified := {_str(f['qualified'])}, "
        f"routine := {_str(f['routine'])}, arm := {_str(rec.get('arm') or '')}, "
        f"entryPc := {f['entryPc']}, covered := {_b(f.get('covered'))}, "
        f"firstInRegion := {f.get('firstInRegion', 0)}, "
        f"maxInsnPerInvocation := {f.get('maxInsnPerInvocation', 0)}, "
        f"blockStarts := {_ln(f.get('blockStarts', []))}, "
        f"landingTargets := {_ln(f.get('landingTargets', []))}, "
        f"stepBound := {_oi(f.get('stepBound'))}, allocates := {_b(f.get('allocates', False))}, "
        f"meaningTieKind := {_str(f.get('meaningTieKind', 'structural'))}, "
        f"storesSummarized := {_b(f.get('storesSummarized', False))}, "
        f"inRegionStores := {_ln(f.get('inRegionStores', []))}, "
        f"hadStackStore := {_b(f.get('hadStackStore', False))}, "
        f"storeClasses := {_ls(f.get('storeClasses', []))}, "
        f"scalarCarried := {_b(f.get('scalarCarried', False))}, "
        f"storeHasInputPtr := {_b(f.get('storeHasInputPtr', False))} }}"
    )
    ck = (
        f"{{ entryReached := {_ob(c['entryReached'])}, "
        f"controlFlowIntegrity := {_ob(c['controlFlowIntegrity'])}, "
        f"withinStepBound := {_ob(c['withinStepBound'])}, "
        f"allocationConsistent := {_ob(c['allocationConsistent'])}, "
        f"inputPreserved := {_ob(c['inputPreserved'])}, "
        f"codePreserved := {_ob(c['codePreserved'])}, "
        f"writesClassified := {_ob(c['writesClassified'])}, "
        f"meaningTie := {_ob(c['meaningTie'])} }}"
    )
    return f"  (\n    {ev},\n    {ck})"


# Occurrences no input exercises, each STATICALLY classified as unreachable in this ELF's control flow
# (see classify_uncovered.py / UNCOVERED_CLASSIFICATION.md — a CFG proof, not "N test runs missed it").
DOCUMENTED_UNCOVERED = {
    "allocatorRemap": "std.mem.Allocator remap slot (vtable+16); STATIC: the vtable is indexed only at "
                      "offsets 0 (alloc) and 24 (free) by any indirect call and no direct jal targets it, "
                      "so the decoder never calls allocator.remap (exact-size bump allocations never grow).",
    "allocatorResize": "std.mem.Allocator resize slot (vtable+8); STATIC: the vtable is never indexed at "
                       "offset 8 by any indirect call and no direct jal targets it, so the decoder never "
                       "calls allocator.resize.",
    "zesu_raw_error": "exported raw-ABI error getter (auipc/lw/ret); STATIC: no jal/jalr/data pointer in "
                      "the binary references its entry, so the sealed _start harness never calls it (it "
                      "discriminates success/failure via zesu_raw_result's null return). No callable ABI "
                      "surface on the sealed executable to invoke it without relinking (forbidden).",
}


def emit_report(records, summary) -> str:
    """A compact, deterministic per-occurrence coverage report (markdown). Gaps are shown explicitly."""
    sym = {True: "P", False: "F", None: "-"}
    short = {"entryReached": "entry", "controlFlowIntegrity": "cfg", "withinStepBound": "step",
             "allocationConsistent": "alloc", "inputPreserved": "inp", "codePreserved": "code",
             "writesClassified": "wr", "meaningTie": "mean"}
    L = ["# Row C — scaled per-occurrence production-ELF coverage (GENERATED)",
         "",
         "Regenerated by `targets/ssz/zesu/trace/scale_occurrences.py` from the UNCHANGED production",
         "`zesu-ssz` ELF under pinned `qemu-riscv64`. Diagnostic-only; never imported by the proof.",
         "Coverage is PER OCCURRENCE (never inherited from a sibling of the same routine). `P`=pass,",
         "`F`=fail, `-`=explicit gap (never counted as a pass).",
         "",
         "**Step bounds**: input-dependent contract bounds `C + K*(arg//D + E)` are resolved to a concrete",
         "number using a SOUND LOWER bound on `arg` (whole-input length for entry routines; distinct",
         "in-region input bytes read — <= the slice length — for containers/collections; in-region store",
         "count — <= bytes copied — for memcpy/memmove). Since the bound is monotonic, `maxInsn <=`",
         "`bound(argLB)` implies `maxInsn <= bound(actualArg)`. `requireCanonicalOffsets` is the one",
         "unresolved bound (its `offsets.length` is a caller-passed argument, not in the occurrence's",
         "input reads) — an explicit gap with the required interface change noted below.",
         "",
         "**Uncovered occurrences** are STATICALLY classified as unreachable in this ELF's control flow",
         "(`UNCOVERED_CLASSIFICATION.md` / `classify_uncovered.py`), not merely untested. Row C's",
         "conclusions exclude them and the one unresolved step bound.",
         "",
         f"**{summary['covered']}/{summary['occurrences']} occurrences covered** by the present /",
         "malformed / absent arms. Per-check totals:",
         "",
         "| check | pass | fail | gap |", "|---|---:|---:|---:|"]
    for n in CHECK_NAMES:
        d = summary["byCheck"][n]
        L.append(f"| {n} | {d['pass']} | {d['fail']} | {d['gap']} |")
    uncovered = [r for r in records if not r["facts"].get("covered")]
    if uncovered:
        L += ["", "## Uncovered occurrences (documented gaps, not passes)", ""]
        for r in uncovered:
            reason = DOCUMENTED_UNCOVERED.get(r["routine"], "not exercised by any tested arm")
            L.append(f"- occ {r['index']} `{r['qualified']}` — {reason}")
    L += ["",
          "Header abbreviations: " + ", ".join(f"{short[n]}={n}" for n in CHECK_NAMES) + ".",
          "",
          "| idx | routine | arm | " + " | ".join(short[n] for n in CHECK_NAMES) + " | gaps |",
          "|---:|---|---|" + "|".join(["---"] * len(CHECK_NAMES)) + "|---|"]
    for r in records:
        cells = " | ".join(sym[r["checks"].get(n)] for n in CHECK_NAMES)
        gap = "; ".join(sorted(f"{short.get(k, k)}: {v}" for k, v in r.get("gaps", {}).items()))
        L.append(f"| {r['index']} | {r['routine']} | {r.get('arm') or '-'} | {cells} | {gap} |")
    return "\n".join(L) + "\n"


def emit_lean(records) -> str:
    head = [
        "-- GENERATED — do not edit. Regenerated by targets/ssz/zesu/trace/scale_occurrences.py from the",
        "-- UNCHANGED production zesu-ssz ELF under pinned qemu-riscv64. Diagnostic-only evidence;",
        "-- the validation-import guard forbids the theorem graph from importing this.",
        "import BinaryFv.SSZ.Zesu.Validation.ScaleOccurrenceTypes",
        "",
        "namespace BinaryFv.SSZ.Zesu.Validation.GeneratedScaleEvidence",
        "open BinaryFv.SSZ.Zesu.Validation",
        "",
        "/-- Compact per-occurrence production-ELF evidence paired with the Python oracle's check result,",
        "for every occurrence in program.json. Coverage is per occurrence; `none` checks are explicit gaps. -/",
        "def allOccs : List (OccScaleEvidence × ScaleChecks) :=",
    ]
    body = "[\n" + ",\n".join(occ_to_lean(r) for r in records) + "]"
    tail = ["", "end BinaryFv.SSZ.Zesu.Validation.GeneratedScaleEvidence", ""]
    return "\n".join(head) + "\n" + body + "\n" + "\n".join(tail)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qemu", required=True)
    ap.add_argument("--plugin", required=True)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--program", required=True)
    ap.add_argument("--catalog", default=str(HERE / "routine_catalog.json"))
    ap.add_argument("--scratch", required=True)
    # each arm: name=path/to/input.bin ; occurrences are assigned to the first arm (in order) that covers them
    ap.add_argument("--arm", action="append", required=True, metavar="NAME=INPUT")
    ap.add_argument("--out-json", required=True)
    ap.add_argument("--out-lean")
    ap.add_argument("--out-report")
    args = ap.parse_args()

    program = json.loads(Path(args.program).read_text())
    occ = program["occurrences"]
    catalog = json.loads(Path(args.catalog).read_text())
    scratch = Path(args.scratch)
    scratch.mkdir(parents=True, exist_ok=True)

    # Capture one full-run trace per arm, then parse.
    arm_traces = {}
    for spec in args.arm:
        name, _, ipath = spec.partition("=")
        log = scratch / f"full_{name}.log"
        decision = run_full_trace(args.qemu, args.plugin, args.elf, ipath, log)
        arm_traces[name] = (parse_trace(log), decision, ipath)

    records = []
    for idx, o in enumerate(occ):
        o = {**o, "index": idx}
        short = o["qualified"].split(".")[-1]
        chosen = None
        for spec in args.arm:
            name = spec.split("=", 1)[0]
            (executed, loads, stores), _, _ = arm_traces[name]
            ranges = [(r["start"], r["start"] + r["size"]) for r in o["regions"]]
            if any(any(a <= pc < b for a, b in ranges) for pc in executed):
                chosen = name
                break
        if chosen is None:
            facts = reduce_occurrence(o, short, catalog, [], [], [])  # covered=False
        else:
            (executed, loads, stores), _, ipath = arm_traces[chosen]
            input_len = Path(ipath).stat().st_size
            facts = reduce_occurrence(o, short, catalog, executed, loads, stores, input_len)
        checks, gaps = evaluate_facts(facts)
        records.append({
            "index": idx, "qualified": o["qualified"], "routine": short,
            "arm": chosen, "checks": checks, "gaps": gaps, "facts": facts,
        })

    # Aggregate coverage.
    passed = {n: sum(1 for r in records if r["checks"].get(n) is True) for n in CHECK_NAMES}
    failed = {n: sum(1 for r in records if r["checks"].get(n) is False) for n in CHECK_NAMES}
    gapped = {n: sum(1 for r in records if r["checks"].get(n) is None) for n in CHECK_NAMES}
    summary = {
        "occurrences": len(occ),
        "covered": sum(1 for r in records if r["facts"].get("covered")),
        "byCheck": {n: {"pass": passed[n], "fail": failed[n], "gap": gapped[n]} for n in CHECK_NAMES},
        "arms": {name: {"decision": arm_traces[name][1], "input": arm_traces[name][2]} for name in arm_traces},
    }
    out = {"summary": summary, "occurrences": records}
    Path(args.out_json).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    if args.out_lean:
        Path(args.out_lean).write_text(emit_lean(records))
    if args.out_report:
        Path(args.out_report).write_text(emit_report(records, summary))

    # Human-readable digest to stderr.
    any_fail = sum(failed.values())
    print(f"occurrences={len(occ)} covered={summary['covered']}", file=sys.stderr)
    for n in CHECK_NAMES:
        print(f"  {n:22s} pass={passed[n]:3d} fail={failed[n]:3d} gap={gapped[n]:3d}", file=sys.stderr)
    if any_fail:
        print("FAILURES:", file=sys.stderr)
        for r in records:
            bad = [n for n in CHECK_NAMES if r["checks"].get(n) is False]
            if bad:
                print(f"  occ {r['index']:3d} {r['qualified']:55s} {bad}", file=sys.stderr)
    return 1 if any_fail else 0


if __name__ == "__main__":
    raise SystemExit(main())
