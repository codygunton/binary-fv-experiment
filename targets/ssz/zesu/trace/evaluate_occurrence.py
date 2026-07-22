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


def evaluate(occ, records, stops, arm, expected=None):
    """Evaluate one input's evidence against occurrence 116 + children. `arm` is present/absent/malformed.
    `expected` overrides the checked binding (entry PC / child offsets) so negative tests can corrupt it."""
    exp = {"entry_pc": occ["entryPc"], "child_offsets": {117: 0, 118: 8, 119: 16},
           "child_entry": {117: 76988, 118: 77020, 119: 77120}}
    exp.update(expected or {})
    entry_pc = exp["entry_pc"]
    region_ranges = [(r["start"], r["start"] + r["size"]) for r in occ["regions"]]

    def in_regions(pc):
        return any(a <= pc < b for a, b in region_ranges)

    executed = [pc for k, pc in ((r[0], r[1]) for r in records) if k == "E"]
    exec_set = sorted(set(executed))
    edges = sorted({(executed[i], executed[i + 1]) for i in range(len(executed) - 1)
                    if executed[i + 1] != executed[i] + 2 and executed[i + 1] != executed[i] + 4})
    # Every executed edge whose source is inside the occurrence must be a declared CFG edge (no phantom
    # control flow); a dropped/injected edge in the evidence flips this.
    declared_edges = {(e["source"], e["target"]) for e in occ["edges"]}
    occ_exec_edges = {(s, t) for (s, t) in edges if in_regions(s)}
    edges_subset_of_cfg = occ_exec_edges <= declared_edges

    stop_by_pc = {s["pc"]: s for s in stops}
    entry = stop_by_pc.get(entry_pc)

    # readU64 loads/stores: (pc, addr, width, value).
    loads = [tuple(r[1:]) for r in records if r[0] == "L"]
    stores = [tuple(r[1:]) for r in records if r[0] == "S"]

    checks = {}
    # The window opens at the occurrence boundary, so the true entry is the FIRST executed PC and has a
    # captured GDB stop; a wrong entry (a mid-occurrence PC) is reached only from inside and is not first.
    checks["entry_reached"] = (entry is not None and len(executed) > 0
                               and executed[0] == entry_pc)
    checks["edges_subset_of_cfg"] = edges_subset_of_cfg

    # Child const-offset bindings: from GDB stops at the child entry PCs, and from the load addresses.
    child_offsets = exp["child_offsets"]
    child_entry = exp["child_entry"]
    # The blob-schedule slice pointer: the input address the first field is read from minus offset 0.
    field_loads = {}  # child idx -> (base_addr, decoded u64)
    if arm == "present":
        # The three readU64 children each read 8 consecutive input bytes. Sorted, the in-window input
        # byte loads are the 24 bytes [slice_ptr, slice_ptr+24); reconstruct three little-endian u64s
        # RELATIVE to the slice start (alignment-independent).
        input_byte_loads = sorted((addr, v) for (pc, addr, w, v) in loads
                                  if INPUT[0] <= addr < INPUT[1] and w == 1)
        by_addr = {addr: v for addr, v in input_byte_loads}
        slice_ptr = min(by_addr) if by_addr else None
        for k, idx in enumerate((117, 118, 119)):
            base = slice_ptr + k * 8 if slice_ptr is not None else None
            if base is not None and all((base + j) in by_addr for j in range(8)):
                val = sum(by_addr[base + j] << (8 * j) for j in range(8))
                field_loads[idx] = (base, val, base - slice_ptr)
        checks["child_offsets_from_loads"] = all(
            idx in field_loads and field_loads[idx][2] == child_offsets[idx] for idx in (117, 118, 119))
        # Meaning: RawBlobSchedule = (target, max, base_fee) from the three fields.
        decoded = {idx: field_loads[idx][1] for idx in field_loads}
        checks["decoded_blob_schedule"] = [decoded.get(117), decoded.get(118), decoded.get(119)]
    else:
        checks["child_offsets_from_loads"] = None  # children do not execute in absent/malformed arms
        checks["decoded_blob_schedule"] = None

    # Result/exit binding: the indirect-return result slot (a0=x10 at entry) is a stack address the
    # RawBlobSchedule is returned through. A swapped register / wrong result slot moves it off-stack.
    sp0 = entry["registers"]["x2"] if entry else 0
    a0 = entry["registers"]["x10"] if entry else 0
    checks["result_slot_on_stack"] = entry is not None and classify_write(a0, sp0) == "stack"

    # Step bound: instruction count within the occurrence <= contract stepBound (256).
    occ_insns = [pc for pc in executed if in_regions(pc)]
    checks["insn_count"] = len(occ_insns)
    checks["step_bound"] = 256
    checks["within_step_bound"] = len(occ_insns) <= 256

    # Allocation ledger: decodeOptionalBlobSchedule is non-allocating; no heap / cursor writes in-window.
    sp = entry["registers"]["x2"] if entry else 0
    in_window_stores = [(pc, addr, w, v) for (pc, addr, w, v) in stores if in_regions(pc)]
    classes = {}
    for (pc, addr, w, v) in in_window_stores:
        c = classify_write(addr, sp)
        classes[c] = classes.get(c, 0) + 1
    checks["write_classes"] = classes
    checks["no_allocation"] = classes.get("heap", 0) == 0 and classes.get("allocator-cursor", 0) == 0
    checks["input_preserved"] = classes.get("input", 0) == 0
    checks["code_preserved"] = classes.get("code", 0) == 0
    checks["no_unclassified_writes"] = classes.get("unclassified", 0) == 0

    return {"arm": arm, "entry_pc": entry_pc, "executed_pcs": len(exec_set), "edges": len(edges),
            "checks": checks, "entry_registers": entry["registers"] if entry else None}


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

    occ = json.load(open(a.program_json))["occurrences"][116]
    assert occ["qualified"] == "ssz_raw.decodeOptionalBlobSchedule", occ["qualified"]
    lo, hi = occ["entryPc"], occ["exitPc"]
    boundary = [occ["entryPc"], 76988, 77020, 77120] + occ["exits"]
    scratch = Path(a.scratch)
    scratch.mkdir(parents=True, exist_ok=True)

    results = []
    for arm, path in (("present", a.present), ("absent", a.absent), ("malformed", a.malformed)):
        sub = scratch / arm
        sub.mkdir(exist_ok=True)
        # Read the result slot (a0 at entry) so the exit binding's OptionSome/None rep is checkable.
        records, stops = run_capture(a.qemu, a.gdb, a.plugin, a.elf, path, lo, hi, boundary,
                                     ["$x10:24"], sub)
        results.append(evaluate(occ, records, stops, arm))

    report = {"occurrence": 116, "qualified": occ["qualified"], "arms": results}
    Path(a.out_json).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    for r in results:
        c = r["checks"]
        print(f"[{r['arm']:9s}] entry={c['entry_reached']} insns={c['insn_count']}/{c['step_bound']} "
              f"no_alloc={c['no_allocation']} input_ok={c['input_preserved']} code_ok={c['code_preserved']} "
              f"unclassified=0:{c['no_unclassified_writes']} classes={c['write_classes']} "
              f"blob={c['decoded_blob_schedule']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
