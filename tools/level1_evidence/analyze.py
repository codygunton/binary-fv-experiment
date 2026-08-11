#!/usr/bin/env python3
"""Reduce production traces to explicit Level 1 admission evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def parse_trace(path: Path) -> dict:
    executed, executions, registers, loads, stores = [], [], {}, [], []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        parts = line.split()
        if not parts:
            continue
        try:
            if parts[0] == "E" and len(parts) == 2:
                pc = int(parts[1])
                executed.append(pc)
                executions.append({"pc": pc, "registers": None})
            elif parts[0] == "R" and len(parts) == 35:
                pc = int(parts[1])
                snapshot = {
                    "available": int(parts[2]),
                    "values": [int(value) for value in parts[3:]],
                }
                if not executions or executions[-1]["pc"] != pc or executions[-1]["registers"] is not None:
                    raise ValueError
                executions[-1]["registers"] = snapshot
                registers.setdefault(pc, []).append(snapshot)
            elif parts[0] in {"L", "S"} and len(parts) == 5:
                record = [int(value) for value in parts[1:]]
                (loads if parts[0] == "L" else stores).append(record)
            else:
                raise ValueError
        except ValueError as error:
            raise ValueError(f"{path}:{number}: malformed trace record") from error
    return {"executed": executed, "executions": executions, "registers": registers,
            "loads": loads, "stores": stores}


def reduce_trace(manifest: dict, trace: dict, label: str) -> dict:
    result = []
    for instance in manifest["instances"]:
        extent = set(instance["executionPcs"])
        exits_expected = set(instance["exitPcs"])
        entries = trace["registers"].get(instance["entryPc"], [])
        for snapshot in entries:
            if snapshot["available"] != 2 ** 32 - 1:
                raise ValueError(f"unavailable register in snapshot for {instance['id']}")
        observed_owned, observed_extent = set(), set()
        transitions, exits = [], []
        active = False
        executions = trace["executions"]
        for index, current in enumerate(executions):
            if not active and current["pc"] == instance["entryPc"] and current["registers"] is not None:
                active = True
            if not active:
                continue
            if current["pc"] not in extent:
                raise ValueError(f"active occurrence left extent for {instance['id']}")
            observed_extent.add(current["pc"])
            if current["pc"] in instance["instructionPcs"]:
                observed_owned.add(current["pc"])
            if index + 1 == len(executions):
                if current["pc"] not in exits_expected:
                    raise ValueError(f"unterminated occurrence for {instance['id']}")
                active = False
                continue
            after = executions[index + 1]
            if after["pc"] in extent:
                continue
            if after["pc"] not in exits_expected:
                raise ValueError(
                    f"unexpected exit {current['pc']} -> {after['pc']} for {instance['id']}")
            snapshot = after["registers"]
            if snapshot is None or snapshot["available"] != 2 ** 32 - 1:
                raise ValueError(f"missing exit register snapshot for {instance['id']}")
            transitions.append((current["pc"], after["pc"]))
            exits.append({"beforePc": current["pc"], "afterPc": after["pc"],
                          "afterRegisters": snapshot})
            active = False
        memory = [
            {"kind": kind, "pc": record[0], "address": record[1],
             "width": record[2], "value": record[3]}
            for kind, records in (("load", trace["loads"]), ("store", trace["stores"]))
            for record in records if record[0] in extent
        ]
        result.append({
            "id": instance["id"],
            "qualified": instance["qualified"],
            "entryReached": bool(entries),
            "entryRegisters": entries,
            "executedOwnedPcs": sorted(observed_owned),
            "executedExtentPcs": sorted(observed_extent),
            "observedExitTransitions": [list(pair) for pair in sorted(set(transitions))],
            "observedExits": exits,
            "memoryAccesses": memory,
        })
    return {"label": label, "instances": result}


def validate_bindings(manifest: dict, bindings: dict, vectors: list[dict],
                      inputs: dict[str, Path]) -> dict:
    if bindings["artifact"] != manifest["artifact"]:
        raise ValueError("boundary bindings and manifest artifacts differ")
    expected = {row["id"] for row in manifest["instances"]}
    actual = {row["id"] for row in bindings["instances"]}
    if actual != expected:
        raise ValueError("boundary bindings and manifest instances differ")
    decode_binding = next(row for row in bindings["instances"]
                          if row["qualified"] == "ssz.decode")
    registers = {row["name"]: row["machineRegister"]
                 for row in decode_binding["bindings"]}
    if registers.get("input_ptr") != 23 or registers.get("input_size") != 18:
        raise ValueError("unexpected optimized ssz.decode input bindings")
    checks = []
    for vector in vectors:
        if vector["label"] not in inputs:
            raise ValueError(f"missing input fixture for {vector['label']}")
        decode = next(row for row in vector["instances"] if row["qualified"] == "ssz.decode")
        if not decode["entryReached"]:
            continue
        size = inputs[vector["label"]].stat().st_size
        for snapshot in decode["entryRegisters"]:
            pointer = snapshot["values"][23]
            if snapshot["values"][18] != size:
                raise ValueError(f"ssz.decode input_size mismatch for {vector['label']}")
            if not any(access["kind"] == "load" and access["address"] == pointer
                       for access in decode["memoryAccesses"]):
                raise ValueError(f"ssz.decode input_ptr was not observed as a load base for {vector['label']}")
        checks.append({
            "vector": vector["label"],
            "inputSize": size,
            "snapshots": len(decode["entryRegisters"]),
            "inputPointerRegister": 23,
            "inputSizeRegister": 18,
        })
    return {"source": "same-ELF DWARF checked against QEMU entry snapshots and loads",
            "sszDecodeInputBindings": checks}


def validate_decode_runs(manifest: dict, traces: list[tuple[str, dict]]) -> list[dict]:
    """Check the observed decode entry-to-outcome interval without claiming universality."""
    entries = {row["qualified"]: row["entryPc"] for row in manifest["instances"]}
    required = {"ssz.decode", "ssz_decode_observation.writeSuccess",
                "ssz_decode_observation.writeFailure"}
    if not required <= entries.keys():
        raise ValueError("manifest lacks the typed ssz.decode outcome boundaries")
    decode_pc = entries["ssz.decode"]
    success_pc = entries["ssz_decode_observation.writeSuccess"]
    failure_pc = entries["ssz_decode_observation.writeFailure"]
    reports = []
    for label, trace in traces:
        executed = trace["executed"]
        try:
            start = executed.index(decode_pc)
        except ValueError as error:
            raise ValueError(f"ssz.decode entry absent from {label}") from error
        outcomes = [(index, pc) for index, pc in enumerate(executed[start + 1:], start + 1)
                    if pc in {success_pc, failure_pc}]
        if not outcomes:
            raise ValueError(f"ssz.decode outcome boundary absent from {label}")
        finish, outcome_pc = outcomes[0]
        entry_snapshots = trace["registers"].get(decode_pc, [])
        exit_snapshots = trace["registers"].get(outcome_pc, [])
        if len(entry_snapshots) != 1 or len(exit_snapshots) != 1:
            raise ValueError(f"expected one decode and outcome snapshot for {label}")
        before = entry_snapshots[0]["values"]
        after = exit_snapshots[0]["values"]
        reports.append({
            "vector": label,
            "outcome": "success" if outcome_pc == success_pc else "failure",
            "outcomeEntryPc": outcome_pc,
            "observedStepCount": finish - start,
            "changedIntegerRegisters": [index for index, pair in enumerate(zip(before, after))
                                        if pair[0] != pair[1]],
            "successResultAddress": after[10] if outcome_pc == success_pc else None,
        })
    return reports


def make_report(manifest: dict, elf: Path, traces: list[tuple[str, Path]],
                bindings: dict | None = None, inputs: dict[str, Path] | None = None) -> dict:
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    if digest != manifest["artifact"]["sha256"]:
        raise ValueError("manifest and observed ELF digests differ")
    parsed_traces = [(label, parse_trace(path)) for label, path in traces]
    vectors = [reduce_trace(manifest, trace, label) for label, trace in parsed_traces]
    reached = {
        instance["id"] for vector in vectors for instance in vector["instances"]
        if instance["entryReached"]
    }
    expected = {instance["id"] for instance in manifest["instances"]}
    if reached != expected:
        missing = sorted(expected - reached)
        raise ValueError(f"Level 1 entry coverage is incomplete: {missing}")
    report = {
        "schemaVersion": 1,
        "artifact": manifest["artifact"],
        "level": 1,
        "vectors": vectors,
        "entryCoverage": {"observed": sorted(reached), "complete": True},
        "sszDecodeObservedRuns": validate_decode_runs(manifest, parsed_traces),
        "unmeasuredClauses": [
            "universal path coverage",
            "universal step bounds",
            "complete register write frames",
            "complete memory write frames",
            "semantic result relation",
        ],
    }
    if bindings is not None:
        report["boundaryBindingValidation"] = validate_bindings(
            manifest, bindings, vectors, inputs or {})
    return report


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--elf", required=True, type=Path)
    parser.add_argument("--trace", action="append", required=True,
                        help="LABEL=PATH")
    parser.add_argument("--bindings", type=Path)
    parser.add_argument("--input", action="append", default=[], help="LABEL=PATH")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    traces = []
    for value in args.trace:
        label, separator, path = value.partition("=")
        if not separator or not label:
            raise ValueError("--trace must be LABEL=PATH")
        traces.append((label, Path(path)))
    inputs = {}
    for value in args.input:
        label, separator, path = value.partition("=")
        if not separator or not label:
            raise ValueError("--input must be LABEL=PATH")
        inputs[label] = Path(path)
    bindings = json.loads(args.bindings.read_text()) if args.bindings else None
    report = make_report(json.loads(args.manifest.read_text()), args.elf, traces,
                         bindings, inputs)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
