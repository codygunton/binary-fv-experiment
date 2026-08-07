#!/usr/bin/env python3
"""Negative temporary-copy tests for the decodeOptionalBlobSchedule evidence slice.

Capture the real present-arm COMPACT evidence once, then corrupt COPIES of it and require the relevant
check to flip. These are mutations to the GENERATED EVIDENCE (the same shape the Lean checker consumes),
so the identical mutation classes port across the boundary. Mutation survival blocks the row; the
production ELF is never modified.
"""
from __future__ import annotations

import argparse
import sys

import evaluate_occurrence as ev  # same directory


# The eight mutation classes, as edits to the compact evidence, and the check each must flip to False.
def mutations(evi):
    slice_ptr = min((a for a, _ in evi["inputByteLoads"]), default=0)
    a_region_pc = evi["regions"][0][0] + 2
    def with_store(addr):
        return {"inRegionStores": evi["inRegionStores"] + [[a_region_pc, addr, 8, 0]]}
    return [
        # wrong occurrence entry: the first executed PC is not the declared entry
        ("wrong-occurrence-entry", {"firstExecuted": evi["entryPc"] + 4}, "entry_reached"),
        # +8 ABI error: field 0 read at slice_ptr+8..15 instead of +0..7 (loads no longer realize 0/8/16)
        ("plus-8-abi-offset",
         {"inputByteLoads": [[a + 8 if a < slice_ptr + 8 else a, v] for a, v in evi["inputByteLoads"]]},
         "child_offsets_from_loads"),
        # swapped register / wrong result slot: a0 result slot moved off-stack (into the heap)
        ("wrong-result-slot", {"entryRegs": {**evi["entryRegs"], "10": ev.HEAP[0] + 16}},
         "result_slot_on_stack"),
        # reassigned (phantom) edge: executed control flow not in the generated CFG
        ("phantom-edge", {"occExecEdges": evi["occExecEdges"] + [[a_region_pc, 999999]]},
         "edges_subset_of_cfg"),
        # wrong allocation fact: an injected heap store in a non-allocating source_function
        ("injected-heap-alloc", with_store(ev.HEAP[0] + 32), "no_allocation"),
        # out-of-frame (unclassified) write
        ("out-of-frame-write", with_store(0xDEAD0000), "no_unclassified_writes"),
        # input-preservation violation
        ("input-write", with_store(ev.INPUT[0] + 8), "input_preserved"),
        # code-preservation violation
        ("code-write", with_store(ev.TEXT[0] + 8), "code_preserved"),
    ]


def normalization_failures():
    """The same stack-relative facts must serialize identically under two host stack bases."""
    failures = []
    bases = (140737136016832, 140737194737072)
    for offset in (0, 3592, 4096):
        got = {ev.normalize_stack_address(sp + offset, sp) for sp in bases}
        if got != {ev.CANONICAL_SP + offset}:
            failures.append(f"stack normalization drift at offset {offset}: {sorted(got)}")
    fixed = ev.INPUT[0] + 8
    if any(ev.normalize_stack_address(fixed, sp) != fixed for sp in bases):
        failures.append("stack normalization changed a fixed input address")
    return failures


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

    (evi,) = ev.capture_arms(a.qemu, a.gdb, a.plugin, a.elf, a.program_json, {"present": a.present},
                             a.scratch)

    good = ["entry_reached", "edges_subset_of_cfg", "child_offsets_from_loads", "result_slot_on_stack",
            "within_step_bound", "no_allocation", "input_preserved", "code_preserved",
            "no_unclassified_writes"]
    base = ev.evaluate_compact(evi)
    failures = normalization_failures()
    failures += [f"baseline check {k} did not pass" for k in good if base.get(k) is not True]

    cases = mutations(evi)
    for label, mut, check in cases:
        if ev.evaluate_compact(evi, mutate=mut).get(check) is True:
            failures.append(f"mutation '{label}' NOT caught: check '{check}' still passed")

    if failures:
        print(f"NEGATIVE TESTS FAILED ({len(failures)}):", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        return 1
    print(f"negative tests OK: stack normalization is cross-host stable; baseline passes all "
          f"{len(good)} checks; all {len(cases)} evidence "
          f"corruptions caught (swapped reg / +8 ABI / wrong occurrence / phantom edge / wrong "
          f"allocation / out-of-frame / input / code)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
