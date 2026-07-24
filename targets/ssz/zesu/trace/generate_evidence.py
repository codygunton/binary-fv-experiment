#!/usr/bin/env python3
"""Row C: generate the deterministic Lean evidence module for the decodeOptionalBlobSchedule slice.

Captures the compact per-function-instance evidence for the present / absent / malformed arms (via the QEMU
plugin trace + batch GDB), runs the Python oracle over it, and emits:

  * `--out-json`   : the evidence + oracle check results (for drift comparison and the Python side);
  * `--out-lean`   : a generated Lean data module (FunctionInstanceEvidence + expected CheckResult per arm) the Lean
                     diagnostic checker consumes.

Only observed, reduced facts go into the evidence (executed-PC/edge summary, in-region stores, input
byte loads, entry sp/a0). Fixed guest addresses stay exact; host-selected stack addresses are
serialized as offsets from a stable synthetic SP, preserving the checked frame relations across
hosts. The evidence is compact and deterministic, so it is committed and drift-checked rather than
shipping the raw multi-MB trace. Diagnostic-only; never imported by the proof.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import evaluate_function_instance as ev  # same directory


def _pairs(xs):
    return "[" + ", ".join(f"({a}, {b})" for a, b in xs) + "]"


def _quads(xs):
    return "[" + ", ".join(f"({a}, {b}, {c}, {d})" for a, b, c, d in xs) + "]"


def _lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def evidence_to_lean(evi) -> str:
    return (
        "{ arm := " + _lean_str(evi["arm"])
        + ", entryPc := " + str(evi["entryPc"])
        + ", regions := " + _pairs(evi["regions"])
        + ", declaredEdges := " + _pairs(evi["declaredEdges"])
        + ", firstExecuted := " + str(evi["firstExecuted"])
        + ", functionInstanceInsnCount := " + str(evi["functionInstanceInsnCount"])
        + ", functionInstanceExecEdges := " + _pairs(evi["functionInstanceExecEdges"])
        + ", inRegionStores := " + _quads(evi["inRegionStores"])
        + ", inputByteLoads := " + _pairs(evi["inputByteLoads"])
        + ", sp := " + str(evi["entryRegs"]["2"])
        + ", a0 := " + str(evi["entryRegs"]["10"])
        + " }"
    )


def checks_to_lean(c) -> str:
    def ob(x):
        return "none" if x is None else ("some true" if x else "some false")

    def ol(x):
        return "none" if x is None else "some [" + ", ".join(str(v) for v in x) + "]"

    return (
        "{ entryReached := " + str(c["entry_reached"]).lower()
        + ", edgesSubsetOfCfg := " + str(c["edges_subset_of_cfg"]).lower()
        + ", childOffsetsFromLoads := " + ob(c["child_offsets_from_loads"])
        + ", decodedBlobSchedule := " + ol(c["decoded_blob_schedule"])
        + ", resultSlotOnStack := " + str(c["result_slot_on_stack"]).lower()
        + ", withinStepBound := " + str(c["within_step_bound"]).lower()
        + ", noAllocation := " + str(c["no_allocation"]).lower()
        + ", inputPreserved := " + str(c["input_preserved"]).lower()
        + ", codePreserved := " + str(c["code_preserved"]).lower()
        + ", noUnclassifiedWrites := " + str(c["no_unclassified_writes"]).lower()
        + " }"
    )


def emit_lean(arms) -> str:
    lines = [
        "-- GENERATED FILE: produced by targets/ssz/zesu/trace/generate_evidence.py --out-lean. DO NOT EDIT.",
        "-- Deterministic production-ELF evidence for the decodeOptionalBlobSchedule slice (function instance 116),",
        "-- consumed by BinaryFv/SSZ/Zesu/Validation/BinaryFunctionInstanceCheck.lean. Diagnostic-only; the",
        "-- validation-import guard forbids the theorem graph from importing this.",
        "import BinaryFv.SSZ.Zesu.Validation.BinaryFunctionInstanceTypes",
        "namespace BinaryFv.SSZ.Zesu.Validation.GeneratedBinaryEvidence",
        "open BinaryFv.SSZ.Zesu.Validation",
        "",
    ]
    names = []
    for arm in arms:
        nm = arm["evidence"]["arm"]
        names.append(nm)
        lines.append(f"def {nm}Evidence : FunctionInstanceEvidence :=\n  {evidence_to_lean(arm['evidence'])}")
        lines.append(f"def {nm}Expected : CheckResult :=\n  {checks_to_lean(arm['checks'])}")
        lines.append("")
    tuples = ", ".join(f"({nm}Evidence, {nm}Expected)" for nm in names)
    lines.append(f"/-- Each arm's evidence paired with the Python oracle's expected check result. -/")
    lines.append(f"def allArms : List (FunctionInstanceEvidence × CheckResult) :=\n  [{tuples}]")
    lines.append("end BinaryFv.SSZ.Zesu.Validation.GeneratedBinaryEvidence")
    return "\n".join(lines) + "\n"


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
    ap.add_argument("--out-json")
    ap.add_argument("--out-lean")
    a = ap.parse_args()

    evidence = ev.capture_arms(a.qemu, a.gdb, a.plugin, a.elf, a.program_json,
                               {"present": a.present, "absent": a.absent, "malformed": a.malformed},
                               a.scratch)
    arms = [{"evidence": e, "checks": ev.evaluate_compact(e)} for e in evidence]
    if a.out_json:
        Path(a.out_json).write_text(json.dumps({"function_instance": 116, "arms": arms},
                                               indent=2, sort_keys=True) + "\n")
    if a.out_lean:
        Path(a.out_lean).write_text(emit_lean(arms))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
