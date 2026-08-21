#!/usr/bin/env python3
"""Build the contract-review matrix for the proposed hLevel3 boundary."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path


COMMON_CLAUSES = {
    "machine-boundary", "entry-state", "execution-access", "exit-state",
    "frames-and-termination",
}
FAMILY_CLAUSES = {
    "host-write": "output-bytes", "allocator-alloc": "allocation-result",
    "allocator-dupe": "duplicate-result", "read-integer": "little-endian-result",
    "write-integer": "little-endian-write", "transaction-decode": "transaction-result",
    "byte-list-list-decode": "slice-result",
    "checked-slice-selection": "checked-slice-result", "fork-name": "fork-result",
    "encoder-collection": "encoded-collection", "encoder-integer": "encoded-integer",
    "encoder-optional": "encoded-optional", "encoder-raw": "encoded-bytes",
}


def observations(evidence: dict) -> dict[str, dict]:
    result: dict[str, dict] = defaultdict(lambda: {
        "vectors": set(), "entries": 0, "exits": set(), "owned": set(),
        "extent": set(), "loads": 0, "stores": 0, "hostWrites": 0,
        "occurrences": 0,
    })
    for vector in evidence["vectors"]:
        for row in vector["instances"]:
            slot = result[row["id"]]
            if row["entryReached"]:
                slot["vectors"].add(vector["label"])
                slot["entries"] += len(row["entryRegisters"])
            slot["exits"].update(tuple(edge) for edge in row["observedExitTransitions"])
            slot["owned"].update(row["executedOwnedPcs"])
            slot["extent"].update(row["executedExtentPcs"])
            slot["loads"] += row["memoryAccessSummary"]["loads"]
            slot["stores"] += row["memoryAccessSummary"]["stores"]
            slot["hostWrites"] += len(row["hostWrites"])
            slot["occurrences"] += len(row["occurrences"])
    return result


def schema_index(registry: dict) -> dict[str, tuple[str, dict]]:
    if registry.get("schemaVersion") != 1:
        raise ValueError("invalid hLevel3 contract schema registry")
    common = {row["id"] for row in registry["commonClauses"]}
    if common != COMMON_CLAUSES:
        raise ValueError(f"invalid common contract clauses: {sorted(common)}")
    if set(registry["families"]) != set(FAMILY_CLAUSES):
        raise ValueError("invalid hLevel3 contract family set")
    result = {}
    for name, family in registry["families"].items():
        extra = {row["id"] for row in family.get("extraClauses", [])}
        if extra != {FAMILY_CLAUSES[name]}:
            raise ValueError(f"invalid semantic clauses for {name}: {sorted(extra)}")
        for qualified in family["qualified"]:
            if qualified in result:
                raise ValueError(f"duplicate qualified function in contract schemas: {qualified}")
            result[qualified] = (name, family)
    return result


def validate_fork_dispatch(proposed: list[dict], evidence: dict) -> None:
    contract = next(row for row in proposed
                    if row["qualified"] == "ssz.forkNameFromSchemaByte")
    cases = contract.get("jumpTableTargets", [])
    rejected = sorted(set(contract["exitPcs"]) - set(cases))
    if len(cases) != 21 or len(rejected) != 1:
        raise ValueError("fork-name dispatch does not have 21 cases and one rejection exit")
    rejection = rejected[0]
    vectors = {row["label"]: row for row in evidence["vectors"]}
    for schema in range(23):
        label = f"fork-schema-{schema:02x}"
        if label not in vectors:
            raise ValueError(f"missing fork-name evidence vector {label}")
        row = next(instance for instance in vectors[label]["instances"]
                   if instance["id"] == contract["instanceId"])
        expected = ([contract["entryPc"] + 8, rejection] if schema in {0, 22}
                    else [contract["entryPc"] + 44, cases[schema - 1]])
        if row["observedExitTransitions"] != [expected]:
            raise ValueError(f"fork-name evidence route mismatch for {label}")
        if not row["entryRegisters"] or any(
                snapshot["values"][10] != schema for snapshot in row["entryRegisters"]):
            raise ValueError(f"fork-name entry byte mismatch for {label}")


def build(inventory: dict, evidence: dict, bindings: dict, registry: dict) -> dict:
    if inventory["artifact"] != evidence["artifact"] or inventory["artifact"] != bindings["artifact"]:
        raise ValueError("hLevel3 admission inputs describe different ELFs")
    proposed = inventory["proposedLevel3Contracts"]
    validate_fork_dispatch(proposed, evidence)
    expected_count = inventory["summary"]["level3ContractCount"]
    if len(proposed) != expected_count:
        raise ValueError("hLevel3 admission contract count disagrees with its inventory")
    binding_by_id = {row["id"]: row for row in bindings["instances"]}
    if len(binding_by_id) != len(bindings["instances"]):
        raise ValueError("duplicate Level 3 boundary binding")
    observed = observations(evidence)
    schemas = schema_index(registry)
    qualified = {row["qualified"] for row in proposed}
    missing_schema = sorted(qualified - set(schemas))
    unused_schema = sorted(set(schemas) - qualified)
    if missing_schema or unused_schema:
        raise ValueError(
            f"contract schemas do not cover the exact hLevel3 boundary: "
            f"missing={missing_schema} unused={unused_schema}")

    rows = []
    unsupported_measurable = []
    for contract in proposed:
        identifier = contract["instanceId"]
        if identifier not in binding_by_id:
            raise ValueError(f"missing boundary bindings for {identifier}")
        boundary = binding_by_id[identifier]
        if (boundary["entryPc"] != contract["entryPc"] or
                boundary["qualified"] != contract["qualified"]):
            raise ValueError(f"boundary identity disagrees with {identifier}")
        family_name, family = schemas[contract["qualified"]]
        capture = observed[identifier]
        invalid_exits = sorted(
            edge for edge in capture["exits"]
            if edge[0] not in contract["executionPcs"] or edge[1] not in contract["exitPcs"])
        if invalid_exits:
            raise ValueError(f"observed exits disagree with {identifier}: {invalid_exits}")
        generated_complete = bool(contract["executionPcs"] and
                                  contract["entryPc"] in contract["executionPcs"] and
                                  set(contract["ownedPcs"]) <= set(contract["executionPcs"]))
        empirical = {
            "entryObserved": capture["entries"] > 0,
            "exitObserved": bool(capture["exits"]),
            "hostWriteObserved": capture["hostWrites"] > 0,
            "ownedInstructionCoverage": (
                len(set(capture["owned"]) & set(contract["ownedPcs"])) /
                len(contract["ownedPcs"]) if contract["ownedPcs"] else 1.0),
        }
        clauses = []
        for clause in [*registry["commonClauses"], *family.get("extraClauses", [])]:
            support = clause["support"]
            if support == "generated":
                status = "passed" if generated_complete else "failed"
            elif support == "proof":
                status = "staged-proof"
            elif support == "empirical-and-proof":
                status = "measured" if empirical["entryObserved"] and empirical["exitObserved"] else "evidence-needed"
            elif support == "source-oracle-and-proof":
                status = "source-oracle-needed"
            else:
                raise ValueError(f"unknown clause support class: {support}")
            if clause["id"] == "output-bytes" and not empirical["hostWriteObserved"]:
                status = "evidence-needed"
            clauses.append({**clause, "status": status})
            if status == "failed":
                unsupported_measurable.append({"instanceId": identifier, "clause": clause["id"]})
        rows.append({
            **contract,
            "contractFamily": family_name,
            "semanticReview": {
                "operation": family["semanticOperation"],
                "reference": family["reference"],
                "status": "review-required",
            },
            "boundaryBindings": boundary["bindings"],
            "empirical": {
                **empirical,
                "vectors": sorted(capture["vectors"]),
                "entrySnapshotCount": capture["entries"],
                "occurrenceCount": capture["occurrences"],
                "observedExitTransitions": [list(edge) for edge in sorted(capture["exits"])],
                "loadCount": capture["loads"],
                "storeCount": capture["stores"],
                "hostWriteCount": capture["hostWrites"],
            },
            "clauses": clauses,
            "contractStatus": "prepared-not-admitted",
        })
    if unsupported_measurable:
        raise ValueError(f"failed generated contract requirements: {unsupported_measurable}")
    status_counts: dict[str, int] = defaultdict(int)
    for row in rows:
        for clause in row["clauses"]:
            status_counts[clause["status"]] += 1
    return {
        "schemaVersion": 1,
        "artifact": inventory["artifact"],
        "summary": {
            "instanceCount": len(rows),
            "familyCount": len({row["contractFamily"] for row in rows}),
            "clauseCount": sum(len(row["clauses"]) for row in rows),
            "clauseStatusCounts": dict(sorted(status_counts.items())),
            "entryObservedCount": sum(row["empirical"]["entryObserved"] for row in rows),
            "exitObservedCount": sum(row["empirical"]["exitObserved"] for row in rows),
            "admittedContractCount": 0,
        },
        "instances": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    for name in ("inventory", "evidence", "bindings", "registry", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    result = build(*(json.loads(getattr(args, name).read_text())
                     for name in ("inventory", "evidence", "bindings", "registry")))
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
