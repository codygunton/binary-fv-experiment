#!/usr/bin/env python3
"""Row C: map production-ELF evidence to a generated Elfling occurrence and evaluate its Row A binding
and effects. Stop/go for the `decodeOptionalBlobSchedule` vertical slice (occurrence 116 + nested
readU64 children 117/118/119).

Evidence is the UNCHANGED production ELF observed under pinned QEMU (plugin trace of executed PCs +
loads/stores) and batch GDB (registers/memory at the binding boundaries). Nothing is rebuilt/patched.
The evaluation is deterministic and emits a JSON evidence+result summary; a generated Lean data module
for the Lean diagnostic checker is added next. Diagnostic-only; never imported by the proof.

Checks (per the plan): occurrence entry reached; nested readU64 const-offset bindings realized by the
load addresses; `RoutineSpec.meaning` (the decoded RawBlobSchedule from the actual loads); result +
exit binding (result slot written); instruction count vs step bound; allocation ledger; and code/input
preservation + a classified write frame (decoder global / allocator cursor / heap / stack / input /
code / unclassified).
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
CURSOR = (86032, 86048)          # .sbss: ZKVM_HEAP_TOP@86032, ZKVM_HEAP_POS@86040 (allocator cursor)
HEAP = (86048, 67194912)         # bump heap (allocated blocks)
INPUT = (67194912, 69292064)     # SSZ input buffer — read-only (input preservation)
GLOBALS = (69292064, 69292928)   # decoder statics (stored_result / last_status / attempted / ...)


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
    # Stack: a window below the entry SP (RV64 stack grows down; frame is a bounded span around SP).
    if sp - (1 << 16) <= addr <= sp + (1 << 16):
        return "stack"
    return "unclassified"


def run_capture(qemu, gdb, plugin, elf, input_path, lo, hi, boundary_pcs, mem_specs, scratch):
    """Capture the windowed plugin trace and the boundary GDB registers/memory for one input."""
    trace = scratch / "trace.log"
    gdbout = scratch / "gdb.json"
    # capture_trace returns the ELF decision (0 accept / 1 reject); both are valid, only >=2 is a fault.
    cap = subprocess.run([sys.executable, str(HERE / "capture_trace.py"), "--qemu", qemu, "--plugin",
                          plugin, "--elf", elf, "--input", str(input_path), "--out", str(trace),
                          "--lo", str(lo), "--hi", str(hi)])
    if cap.returncode >= 2:
        raise SystemExit(f"capture_trace faulted ({cap.returncode})")
    cmd = [sys.executable, str(HERE / "gdb_capture.py"), "--qemu", qemu, "--gdb", gdb, "--elf", elf,
           "--input", str(input_path), "--out", str(gdbout)]
    for pc in boundary_pcs:
        cmd += ["--pc", str(pc)]
    for m in mem_specs:
        cmd += ["--mem", m]
    subprocess.run(cmd, check=True)
    records = []
    for line in trace.read_text().splitlines():
        parts = line.split()
        if parts[0] == "E":
            records.append(("E", int(parts[1])))
        else:  # L / S <pc> <addr> <width> <value>
            records.append((parts[0], int(parts[1]), int(parts[2]), int(parts[3]), int(parts[4])))
    return records, json.loads(gdbout.read_text())["stops"]


CHILD_ENTRY = {117: 76988, 118: 77020, 119: 77120}
CHILD_OFFSETS = {117: 0, 118: 8, 119: 16}  # Row A const-offset bindings for the three readU64 children
STEP_BOUND = 256                             # contractOptionalBlobSchedule.stepBound


def reduce_evidence(occ, records, stops, arm):
    """Reduce raw QEMU/GDB evidence to a compact, deterministic per-occurrence structure that BOTH the
    Python oracle and the Lean checker evaluate identically. Only observed facts go here; the expected
    binding / meaning / layout live in the checker."""
    region_ranges = [(r["start"], r["start"] + r["size"]) for r in occ["regions"]]

    def in_regions(pc):
        return any(a <= pc < b for a, b in region_ranges)

    executed = [pc for k, pc in ((r[0], r[1]) for r in records) if k == "E"]
    edges = {(executed[i], executed[i + 1]) for i in range(len(executed) - 1)
             if executed[i + 1] != executed[i] + 2 and executed[i + 1] != executed[i] + 4}
    loads = [tuple(r[1:]) for r in records if r[0] == "L"]
    stores = [tuple(r[1:]) for r in records if r[0] == "S"]
    entry = {s["pc"]: s for s in stops}.get(occ["entryPc"])
    return {
        "occ": occ["index"] if "index" in occ else 116,
        "arm": arm,
        "qualified": occ["qualified"],
        "entryPc": occ["entryPc"],
        "exitPc": occ["exitPc"],
        "regions": sorted([a, b] for a, b in region_ranges),
        "declaredEdges": sorted([e["source"], e["target"]] for e in occ["edges"]),
        "firstExecuted": executed[0] if executed else None,
        "occInsnCount": sum(1 for pc in executed if in_regions(pc)),
        "occExecEdges": sorted([s, t] for (s, t) in edges if in_regions(s)),
        "inRegionStores": sorted([pc, addr, w, v] for (pc, addr, w, v) in stores if in_regions(pc)),
        "inputByteLoads": sorted([addr, v] for (pc, addr, w, v) in loads
                                 if INPUT[0] <= addr < INPUT[1] and w == 1),
        "entryRegs": {str(n): (entry["registers"][f"x{n}"] if entry else 0) for n in range(32)},
    }


def evaluate_compact(ev, mutate=None):
    """Evaluate the compact evidence against the FIXED Row A binding / meaning / layout. `mutate` is an
    optional dict overwriting evidence fields (for negative tests). Returns a dict of check booleans.
    This is the reference oracle; the Lean checker computes the same booleans on the same evidence."""
    ev = {**ev, **(mutate or {})}
    arm = ev["arm"]
    in_regions = lambda pc: any(a <= pc < b for a, b in ev["regions"])
    declared = {(s, t) for s, t in ev["declaredEdges"]}
    sp = ev["entryRegs"]["2"]
    a0 = ev["entryRegs"]["10"]

    checks = {}
    checks["entry_reached"] = ev["firstExecuted"] == ev["entryPc"]
    checks["edges_subset_of_cfg"] = all((s, t) in declared for s, t in ev["occExecEdges"])

    # Nested readU64 const offsets: the input byte loads must be EXACTLY the 8-byte windows at
    # slice_ptr + {0,8,16} (the Row A const-offset bindings) — no gap, no extra, no shift. This ties the
    # observed load addresses to the generated binding; a +8 ABI error or a dropped field breaks it.
    by_addr = {addr: v for addr, v in ev["inputByteLoads"]}
    slice_ptr = min(by_addr) if by_addr else None
    if arm == "present":
        expect_addrs = ({slice_ptr + off + j for off in CHILD_OFFSETS.values() for j in range(8)}
                        if slice_ptr is not None else set())
        realized = slice_ptr is not None and set(by_addr) == expect_addrs
        checks["child_offsets_from_loads"] = realized
        checks["decoded_blob_schedule"] = (
            [sum(by_addr[slice_ptr + CHILD_OFFSETS[idx] + j] << (8 * j) for j in range(8))
             for idx in (117, 118, 119)] if realized else None)
    else:
        checks["child_offsets_from_loads"] = None
        checks["decoded_blob_schedule"] = None

    checks["result_slot_on_stack"] = classify_write(a0, sp) == "stack"
    checks["insn_count"] = ev["occInsnCount"]
    checks["step_bound"] = STEP_BOUND
    checks["within_step_bound"] = ev["occInsnCount"] <= STEP_BOUND

    classes = {}
    for (pc, addr, w, v) in ev["inRegionStores"]:
        c = classify_write(addr, sp)
        classes[c] = classes.get(c, 0) + 1
    checks["write_classes"] = classes
    checks["no_allocation"] = classes.get("heap", 0) == 0 and classes.get("allocator-cursor", 0) == 0
    checks["input_preserved"] = classes.get("input", 0) == 0
    checks["code_preserved"] = classes.get("code", 0) == 0
    checks["no_unclassified_writes"] = classes.get("unclassified", 0) == 0
    return checks


def evaluate(occ, records, stops, arm, mutate=None):
    return evaluate_compact(reduce_evidence(occ, records, stops, arm), mutate)


def capture_arms(qemu, gdb, plugin, elf, program_json, arms, scratch):
    """Capture + reduce the compact evidence for `arms` = {name: input_path}. Returns [compact, ...]."""
    occ = json.load(open(program_json))["occurrences"][116]
    assert occ["qualified"] == "ssz_raw.decodeOptionalBlobSchedule", occ["qualified"]
    occ = {**occ, "index": 116}
    lo, hi = occ["entryPc"], occ["exitPc"]
    boundary = [occ["entryPc"], 76988, 77020, 77120] + occ["exits"]
    scratch = Path(scratch)
    scratch.mkdir(parents=True, exist_ok=True)
    evidence = []
    for arm, path in arms.items():
        sub = scratch / arm
        sub.mkdir(exist_ok=True)
        records, stops = run_capture(qemu, gdb, plugin, elf, path, lo, hi, boundary, ["$x10:24"], sub)
        evidence.append(reduce_evidence(occ, records, stops, arm))
    return evidence


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qemu", required=True)
    ap.add_argument("--gdb", required=True)
    ap.add_argument("--plugin", required=True)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--program-json", required=True)
    ap.add_argument("--present", required=True)
    ap.add_argument("--absent", required=True)
    ap.add_argument("--malformed", required=True)
    ap.add_argument("--scratch", required=True)
    ap.add_argument("--out-json", required=True)
    a = ap.parse_args()

    evidence = capture_arms(a.qemu, a.gdb, a.plugin, a.elf, a.program_json,
                            {"present": a.present, "absent": a.absent, "malformed": a.malformed},
                            a.scratch)
    arms = [{"evidence": ev, "checks": evaluate_compact(ev)} for ev in evidence]
    report = {"occurrence": 116, "qualified": "ssz_raw.decodeOptionalBlobSchedule", "arms": arms}
    Path(a.out_json).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    for r in arms:
        c = r["checks"]
        print(f"[{r['evidence']['arm']:9s}] entry={c['entry_reached']} "
              f"insns={c['insn_count']}/{c['step_bound']} no_alloc={c['no_allocation']} "
              f"input_ok={c['input_preserved']} code_ok={c['code_preserved']} "
              f"unclassified=0:{c['no_unclassified_writes']} classes={c['write_classes']} "
              f"blob={c['decoded_blob_schedule']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
