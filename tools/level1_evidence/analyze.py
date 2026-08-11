#!/usr/bin/env python3
"""Reduce production traces to explicit Level 1 admission evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def parse_trace(path: Path) -> dict:
    executed, registers, loads, stores = [], {}, [], []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        parts = line.split()
        if not parts:
            continue
        try:
            if parts[0] == "E" and len(parts) == 2:
                executed.append(int(parts[1]))
            elif parts[0] == "R" and len(parts) == 35:
                registers.setdefault(int(parts[1]), []).append({
                    "available": int(parts[2]),
                    "values": [int(value) for value in parts[3:]],
                })
            elif parts[0] in {"L", "S"} and len(parts) == 5:
                record = [int(value) for value in parts[1:]]
                (loads if parts[0] == "L" else stores).append(record)
            else:
                raise ValueError
        except ValueError as error:
            raise ValueError(f"{path}:{number}: malformed trace record") from error
    return {"executed": executed, "registers": registers, "loads": loads, "stores": stores}


def reduce_trace(manifest: dict, trace: dict, label: str) -> dict:
    executed = trace["executed"]
    observed = set(executed)
    result = []
    for instance in manifest["instances"]:
        extent = set(instance["executionPcs"])
        entries = trace["registers"].get(instance["entryPc"], [])
        for snapshot in entries:
            if snapshot["available"] != 2 ** 32 - 1:
                raise ValueError(f"unavailable register in snapshot for {instance['id']}")
        transitions = sorted({
            (before, after) for before, after in zip(executed, executed[1:])
            if before in extent and after not in extent
        })
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
            "executedOwnedPcs": sorted(observed & set(instance["instructionPcs"])),
            "executedExtentPcs": sorted(observed & extent),
            "observedExitTransitions": [list(pair) for pair in transitions],
            "memoryAccesses": memory,
        })
    return {"label": label, "instances": result}


def make_report(manifest: dict, elf: Path, traces: list[tuple[str, Path]]) -> dict:
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    if digest != manifest["artifact"]["sha256"]:
        raise ValueError("manifest and observed ELF digests differ")
    vectors = [reduce_trace(manifest, parse_trace(path), label) for label, path in traces]
    reached = {
        instance["id"] for vector in vectors for instance in vector["instances"]
        if instance["entryReached"]
    }
    expected = {instance["id"] for instance in manifest["instances"]}
    if reached != expected:
        missing = sorted(expected - reached)
        raise ValueError(f"Level 1 entry coverage is incomplete: {missing}")
    return {
        "schemaVersion": 1,
        "artifact": manifest["artifact"],
        "level": 1,
        "vectors": vectors,
        "entryCoverage": {"observed": sorted(reached), "complete": True},
        "unmeasuredClauses": [
            "universal path coverage",
            "universal step bounds",
            "complete register write frames",
            "complete memory write frames",
            "semantic result relation",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--elf", required=True, type=Path)
    parser.add_argument("--trace", action="append", required=True,
                        help="LABEL=PATH")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    traces = []
    for value in args.trace:
        label, separator, path = value.partition("=")
        if not separator or not label:
            raise ValueError("--trace must be LABEL=PATH")
        traces.append((label, Path(path)))
    report = make_report(json.loads(args.manifest.read_text()), args.elf, traces)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
