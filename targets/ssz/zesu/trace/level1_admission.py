#!/usr/bin/env python3
"""Level 1 admission evidence for the eight named root-theorem conditions.

This deliberately combines, without conflating, two independent channels:

* generic control-flow/frame observations from the unchanged production ELF; and
* typed semantic vectors run against the pinned-source host probe.

The output never promotes a missing observation to a pass. In particular, source-probe meaning does
not certify the production machine boundary, and an unexecuted production instance remains a gap.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

import scale_occurrences as scale


SPECS = (
    ("zesuDecodeRaw", "raw_decoder_root.zesu_decode_raw"),
    ("rawResult", "raw_decoder_root.zesu_raw_result"),
    ("rawError", "raw_decoder_root.zesu_raw_error"),
    ("requireCanonicalOffsets", "ssz_raw.requireCanonicalOffsets"),
    ("allocatorResize", "raw_decoder_root.allocatorResize"),
    ("allocatorAlloc", "raw_decoder_root.allocatorAlloc"),
    ("memcpy", "memcpy"),
    ("memmove", "memmove"),
)

PRODUCTION_CHECKS = (
    "entryReached", "controlFlowIntegrity", "exitsRespected", "withinStepBound",
    "allocationConsistent", "inputPreserved", "codePreserved", "writesClassified",
)

INTERFACE_AUDIT = {
    "zesuDecodeRaw": (True, "LLVM `i32 (ptr, i64)` agrees with the Lean input base/length registers"),
    "rawResult": (True, "LLVM and Lean both take no arguments"),
    "rawError": (True, "LLVM and Lean both take no arguments"),
    "requireCanonicalOffsets": (
        False,
        "LLVM is `i16 (i64 data_len, i64 fixed_size, ptr offsets, i64 offsets_len)` after "
        "optimization; the Lean precondition instead binds x10/x11 as a byte slice, x12 as "
        "fixed_size, and does not bind offsets to machine state",
    ),
    "allocatorResize": (True, "the contract ignores all arguments and specifies the constant result"),
    "allocatorAlloc": (
        False,
        "LLVM is `ptr (ptr context, i64 len, i6 alignment_log2, i64 return_address)`; the reused "
        "raw-allocation contract instead binds x10/x11 directly as byte count/alignment",
    ),
    "memcpy": (True, "generated DWARF binds destination/source/length to x10/x11/x12"),
    "memmove": (True, "generated DWARF binds destination/source/length to x10/x11/x12"),
}


def read_jsonl(path: str) -> list[dict]:
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def instances(program: dict) -> list[dict]:
    rows = program.get("function_instances")
    if rows is None:
        raise SystemExit("Level 1 admission requires the named function_instances schema")
    return rows


def select_named(rows: list[dict]) -> list[tuple[str, int, dict]]:
    selected = []
    for condition, qualified in SPECS:
        matches = [(i, row) for i, row in enumerate(rows) if row["qualified"] == qualified]
        if len(matches) != 1:
            raise SystemExit(f"expected exactly one named instance {qualified!r}, found {len(matches)}")
        index, row = matches[0]
        if row.get("kind") != "emitted":
            raise SystemExit(f"Level 1 instance {qualified!r} is not emitted")
        selected.append((condition, index, row))
    return selected


def structural_facts(index: int, row: dict, all_rows: list[dict]) -> dict:
    ranges = [(r["start"], r["start"] + r["size"]) for r in row["regions"]]
    in_region = lambda pc: any(lo <= pc < hi for lo, hi in ranges)
    children = row.get("children") or []
    return {
        "uniqueNamedInstance": True,
        "emitted": row.get("kind") == "emitted",
        "entryInRegion": in_region(row["entryPc"]),
        "hasExit": bool(row.get("exits")),
        "exitsInRegion": all(in_region(pc) for pc in row.get("exits") or []),
        "childIndexesValid": all(isinstance(i, int) and 0 <= i < len(all_rows) for i in children),
        "nonemptyBlocks": bool(row.get("blocks")),
        "index": index,
        "entryPc": row["entryPc"],
        "exits": row.get("exits") or [],
        "regions": row["regions"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qemu", required=True)
    ap.add_argument("--plugin", required=True)
    ap.add_argument("--objdump", required=True)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--program", required=True)
    ap.add_argument("--llvm-ir", required=True)
    ap.add_argument("--catalog", default=str(scale.HERE / "routine_catalog.json"))
    ap.add_argument("--scratch", required=True)
    ap.add_argument("--arm", action="append", required=True, metavar="NAME=INPUT")
    ap.add_argument("--routine-vectors", required=True)
    ap.add_argument("--routine-outcomes", required=True)
    ap.add_argument("--out-json", required=True)
    ap.add_argument("--out-report", required=True)
    a = ap.parse_args()

    program = json.loads(Path(a.program).read_text())
    llvm_ir = Path(a.llvm_ir).read_text()
    rows = instances(program)
    selected = select_named(rows)
    catalog = json.loads(Path(a.catalog).read_text())
    vectors = read_jsonl(a.routine_vectors)
    outcomes = read_jsonl(a.routine_outcomes)
    outcomes_by_id = {o["id"]: o for o in outcomes}

    scratch = Path(a.scratch)
    scratch.mkdir(parents=True, exist_ok=True)
    arm_traces = {}
    for spec in a.arm:
        name, sep, input_path = spec.partition("=")
        if not sep:
            raise SystemExit(f"bad --arm {spec!r}; expected NAME=INPUT")
        log = scratch / f"level1_{name}.log"
        decision = scale.run_full_trace(a.qemu, a.plugin, a.elf, input_path, log)
        arm_traces[name] = (scale.parse_trace(log), decision, input_path)

    def region_pcs(row):
        pcs = set()
        for region in row["regions"]:
            pcs.update(range(region["start"], region["start"] + region["size"], 2))
        return pcs

    all_pcs = [region_pcs(row) for row in rows]
    dynamic_pcs = scale.dynamic_transfer_pcs(a.objdump, a.elf)
    records = []
    for condition, index, row in selected:
        llvm_name = re.escape(row["qualified"])
        llvm_lines = [line.strip() for line in llvm_ir.splitlines()
                      if re.search(rf"(?:define|alias).*@{llvm_name}(?:\W|$)", line)]
        interface_ok, interface_reason = INTERFACE_AUDIT[condition]
        call_targets = []
        for ref in row.get("externalCalls") or []:
            if isinstance(ref, list) and len(ref) == 2 and ref[0] == "function_instance":
                call_targets.append(rows[ref[1]]["entryPc"])
        row = {**row, "callTargetPcs": call_targets}
        child_pcs = set()
        for child in row.get("children") or []:
            child_pcs.update(all_pcs[child])
        chosen = None
        for spec in a.arm:
            name = spec.split("=", 1)[0]
            (executed, _, _), _, _ = arm_traces[name]
            if any(pc in all_pcs[index] for pc in executed):
                chosen = name
                break
        if chosen is None:
            facts = scale.reduce_occurrence(
                {**row, "index": index}, row["qualified"].split(".")[-1], catalog,
                [], [], [], children_pcs=child_pcs, dynamic_pcs=dynamic_pcs,
            )
        else:
            (executed, loads, stores), _, input_path = arm_traces[chosen]
            facts = scale.reduce_occurrence(
                {**row, "index": index}, row["qualified"].split(".")[-1], catalog,
                executed, loads, stores, Path(input_path).stat().st_size, child_pcs, dynamic_pcs,
            )
        production, production_gaps = scale.evaluate_facts(facts)
        production = {name: production[name] for name in PRODUCTION_CHECKS}
        production_gaps = {name: reason for name, reason in production_gaps.items()
                           if name in PRODUCTION_CHECKS}

        routine_vectors = [v for v in vectors if v["routine"] == row["qualified"]]
        semantic = []
        for vector in routine_vectors:
            outcome = outcomes_by_id.get(vector["id"])
            semantic.append({
                "id": vector["id"],
                "coverage": vector["coverage"],
                "observed": outcome is not None,
                "matches": None if outcome is None else bool(outcome.get("match")),
                "ledgerMatches": None if outcome is None else outcome.get("ledger_match"),
            })

        records.append({
            "condition": condition,
            "qualified": row["qualified"],
            "structural": structural_facts(index, row, rows),
            "productionArm": chosen,
            "production": production,
            "productionGaps": production_gaps,
            "sourceProbe": semantic,
            "sourceMeaningPasses": bool(semantic) and all(v["matches"] is True for v in semantic),
            "llvmDeclarations": llvm_lines,
            "interfaceCompatible": interface_ok,
            "interfaceReason": interface_reason,
            # This remains false until production entry/exit values are related to the exact Lean
            # pre/postcondition. Generic trace checks and source meaning are deliberately insufficient.
            "exactMachineMeaningChecked": False,
            "admitted": False,
        })

    result = {
        "schema": "zesu-level1-admission-v1",
        "provenance": {
            "machine": "unchanged production ELF under pinned QEMU observe-only plugin",
            "meaning": "pinned Zig source rebuilt with validation-only private-routine exports",
            "identity": "source-derived function_instances qualified names",
        },
        "conditions": records,
        "summary": {
            "conditions": len(records),
            "structurallyWellFormed": sum(all(v is True for k, v in r["structural"].items()
                                              if isinstance(v, bool)) for r in records),
            "productionExercised": sum(r["productionArm"] is not None for r in records),
            "productionFailures": sum(value is False for r in records
                                      for value in r["production"].values()),
            "sourceMeaningPasses": sum(r["sourceMeaningPasses"] for r in records),
            "interfaceCompatible": sum(r["interfaceCompatible"] for r in records),
            "exactMachineMeaningChecked": sum(r["exactMachineMeaningChecked"] for r in records),
            "admitted": sum(r["admitted"] for r in records),
        },
    }
    Path(a.out_json).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")

    lines = [
        "# Level 1 admission evidence (generated)", "",
        "Named conditions only. `P` is observed pass, `-` is an explicit gap. Source-probe meaning",
        "does not certify production-machine meaning.", "",
        "| condition | instance | production | source vectors | interface | exact machine meaning | admitted |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    interface_failures = []
    for record in records:
        prod = sum(v is True for v in record["production"].values())
        prod_total = len(record["production"])
        source = sum(v["matches"] is True for v in record["sourceProbe"])
        lines.append(
            f"| {record['condition']} | `{record['qualified']}` | {prod}/{prod_total} | "
            f"{source}/{len(record['sourceProbe'])} | "
            f"{'P' if record['interfaceCompatible'] else 'F'} | - | - |"
        )
        if not record["interfaceCompatible"]:
            interface_failures.append(
                f"- **{record['condition']} interface failure:** {record['interfaceReason']}"
            )
    lines += ["", "## Interface failures", "", *interface_failures, "",
              json.dumps(result["summary"], sort_keys=True), ""]
    Path(a.out_report).write_text("\n".join(lines))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
