#!/usr/bin/env python3
"""Row C: negative (temporary-copy) tests for the decodeOptionalBlobSchedule stop/go slice.

Capture the real present-arm evidence once, then apply each corruption to a COPY of the evidence or the
expected binding and require the relevant check to flip to FAIL. This proves the evaluation is
discriminating rather than vacuous — mutation SURVIVAL blocks the row. The production ELF is never
modified; only the in-memory evidence/expected copies are corrupted.

Corruptions (per the plan): swapped register / wrong result slot; a +8 ABI offset error; wrong
occurrence entry; a reassigned (phantom) edge; a wrong allocation fact; an out-of-frame (unclassified)
write; plus input- and code-preservation violations.
"""
from __future__ import annotations

import argparse
import copy
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
import evaluate_occurrence as ev  # noqa: E402  (same directory)


def capture_present(qemu, gdb, plugin, elf, program_json, present, scratch):
    occ = json.load(open(program_json))["occurrences"][116]
    lo, hi = occ["entryPc"], occ["exitPc"]
    boundary = [occ["entryPc"], 76988, 77020, 77120] + occ["exits"]
    sub = Path(scratch) / "present"
    sub.mkdir(parents=True, exist_ok=True)
    records, stops = ev.run_capture(qemu, gdb, plugin, elf, present, lo, hi, boundary, ["$x10:24"], sub)
    return occ, records, stops


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qemu", required=True)
    ap.add_argument("--gdb", required=True)
    ap.add_argument("--plugin", required=True)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--program-json", required=True)
    ap.add_argument("--present", required=True)
    ap.add_argument("--scratch", required=True)
    a = ap.parse_args()

    occ, records, stops = capture_present(a.qemu, a.gdb, a.plugin, a.elf, a.program_json, a.present,
                                          a.scratch)

    # Baseline: the honest present-arm evidence passes every check.
    base = ev.evaluate(occ, records, stops, "present")["checks"]
    good = ["entry_reached", "edges_subset_of_cfg", "child_offsets_from_loads", "result_slot_on_stack",
            "within_step_bound", "no_allocation", "input_preserved", "code_preserved",
            "no_unclassified_writes"]
    failures = [f"baseline check {k} did not pass" for k in good if base.get(k) is not True]

    entry_pc = occ["entryPc"]
    a_region_pc = occ["regions"][0]["start"] + 2  # a PC inside the occurrence

    def store(pc, addr):
        return ("S", pc, addr, 8, 0)

    # (label, mutated records, mutated stops, expected override, the check that must flip to non-True)
    cases = []
    # wrong occurrence entry PC -> entry not reached
    cases.append(("wrong-occurrence-entry", records, stops, {"entry_pc": entry_pc + 4}, "entry_reached"))
    # +8 ABI offset error on the first readU64 child -> child offsets no longer match the loads
    cases.append(("plus-8-abi-offset", records, stops,
                  {"child_offsets": {117: 8, 118: 8, 119: 16}}, "child_offsets_from_loads"))
    # swapped register / wrong result slot -> result slot moved off-stack (a0 -> a heap address)
    stops_swapped = copy.deepcopy(stops)
    for s in stops_swapped:
        if s["pc"] == entry_pc:
            s["registers"]["x10"] = ev.HEAP[0] + 16
    cases.append(("wrong-result-slot", records, stops_swapped, None, "result_slot_on_stack"))
    # reassigned (phantom) edge -> executed control flow that is not in the CFG
    cases.append(("phantom-edge", records + [("E", a_region_pc), ("E", 999999)], stops, None,
                  "edges_subset_of_cfg"))
    # wrong allocation fact -> a heap store inside the occurrence (a non-allocating routine must not)
    cases.append(("injected-heap-alloc", records + [store(a_region_pc, ev.HEAP[0] + 32)], stops, None,
                  "no_allocation"))
    # out-of-frame (unclassified) write inside the occurrence
    cases.append(("out-of-frame-write", records + [store(a_region_pc, 0xDEAD0000)], stops, None,
                  "no_unclassified_writes"))
    # input-preservation violation -> a store into the input buffer
    cases.append(("input-write", records + [store(a_region_pc, ev.INPUT[0] + 8)], stops, None,
                  "input_preserved"))
    # code-preservation violation -> a store into .text
    cases.append(("code-write", records + [store(a_region_pc, ev.TEXT[0] + 8)], stops, None,
                  "code_preserved"))

    for label, recs, sts, exp, check in cases:
        result = ev.evaluate(occ, recs, sts, "present", expected=exp)["checks"]
        if result.get(check) is True:
            failures.append(f"mutation '{label}' NOT caught: check '{check}' still passed")

    if failures:
        print(f"NEGATIVE TESTS FAILED ({len(failures)}):", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        return 1
    print(f"negative tests OK: baseline passes all {len(good)} checks; "
          f"all {len(cases)} corruptions caught (swapped reg / +8 ABI / wrong occurrence / phantom edge "
          f"/ wrong allocation / out-of-frame / input / code)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
