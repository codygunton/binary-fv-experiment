#!/usr/bin/env python3
"""Empirical admission evidence for the reviewed Level 4 ``decodeRaw`` boundaries.

This program checks executions of the unchanged RV64 production ELF.  Its inventory is deliberately
an input, rather than a copy of hierarchy-generator logic: the hierarchy stream owns which 18 local
boundaries/15 function families Level 4 selects, while this program owns how those boundaries are
observed and falsified.  A legacy four-reader/four-decoder inventory is rejected.

The report distinguishes observed facts from contract clauses that the present QEMU plugin cannot
measure.  In particular, instruction PCs can establish sampled entry and exit observations, but do
not bind optimized argument/result registers, prove a caller frame, or establish a universal bound.
Passing this program is admission evidence only; it is never a premise of the Lean compliance proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import ssz_differential_audit as fixtures


EXPECTED_BOUNDARIES = 18
EXPECTED_FAMILIES = 15
UNMEASURED_CLAUSES = (
    "optimized argument locations",
    "optimized result carrier",
    "complete write set or frame condition",
    "caller-frame preservation",
    "universal step bound",
)


@dataclass(frozen=True)
class Boundary:
    identifier: str
    kind: str
    qualified: str
    entry_pc: int
    instruction_pcs: tuple[int, ...]
    exits: tuple[int, ...]
    parent: str
    identity: str | None
    calls: tuple[tuple[int, int], ...]
    stores: tuple[dict[str, int], ...]


def int_field(value: object, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    return value


def exit_pc(value: object, name: str) -> int:
    if isinstance(value, dict):
        value = value.get("pc", value.get("sourcePc", value.get("source")))
    return int_field(value, name)


def load_inventory(path: Path) -> tuple[Boundary, ...]:
    """Load only the stable reviewed-inventory boundary schema.

    The hierarchy producer may retain additional JSON fields.  This reader intentionally ignores
    them, so a hierarchy/UI change cannot silently alter the evidence semantics.
    """
    document = json.loads(path.read_text())
    if not isinstance(document, dict):
        raise ValueError("Level 4 inventory must be a JSON object")
    rows = document.get("boundaries")
    if not isinstance(rows, list):
        raise ValueError("Level 4 inventory lacks a boundaries list")
    boundaries: list[Boundary] = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"boundary {index} is not an object")
        try:
            identifier = row["id"]
            kind = row["kind"]
            qualified = row["qualified"]
            parent = row["parent"]
            entry = int_field(row["entryPc"], f"boundary {index} entryPc")
            pcs = tuple(int_field(pc, f"boundary {index} instructionPcs") for pc in row["instructionPcs"])
            exits = tuple(exit_pc(pc, f"boundary {index} exits") for pc in row["exits"])
        except KeyError as error:
            raise ValueError(f"boundary {index} lacks {error.args[0]}") from error
        if not all(isinstance(value, str) and value for value in (identifier, kind, qualified, parent)):
            raise ValueError(f"boundary {index} has an empty id, kind, qualified, or parent")
        if not pcs or entry not in pcs:
            raise ValueError(f"boundary {identifier} must include its entry in instructionPcs")
        if len(set(pcs)) != len(pcs) or len(set(exits)) != len(exits):
            raise ValueError(f"boundary {identifier} repeats an instruction or exit PC")
        identity = row.get("functionInstanceIdentity")
        if identity is not None and (not isinstance(identity, str) or not identity):
            raise ValueError(f"boundary {identifier} has an invalid functionInstanceIdentity")
        calls = tuple(
            (int_field(call["sourcePc"], f"boundary {identifier} call sourcePc"),
             int_field(call["targetPc"], f"boundary {identifier} call targetPc"))
            for call in row.get("calls", [])
        )
        if any(source not in pcs for source, _target in calls):
            raise ValueError(f"boundary {identifier} declares a call outside instructionPcs")
        stores = tuple(row.get("stores", []))
        for store in stores:
            if not isinstance(store, dict) or not {"pc", "address", "width", "value"} <= store.keys():
                raise ValueError(f"boundary {identifier} store needs pc, address, width, and value")
            if int_field(store["pc"], f"boundary {identifier} store pc") not in pcs:
                raise ValueError(f"boundary {identifier} declares a store outside instructionPcs")
            for field in ("address", "width", "value"):
                int_field(store[field], f"boundary {identifier} store {field}")
        boundaries.append(Boundary(identifier, kind, qualified, entry, pcs, exits, parent, identity,
                                   calls, stores))

    if len(boundaries) != EXPECTED_BOUNDARIES:
        raise ValueError(f"Level 4 inventory has {len(boundaries)} boundaries, expected {EXPECTED_BOUNDARIES}")
    if len({boundary.identifier for boundary in boundaries}) != EXPECTED_BOUNDARIES:
        raise ValueError("Level 4 inventory repeats a boundary id")
    if len({boundary.qualified for boundary in boundaries}) != EXPECTED_FAMILIES:
        raise ValueError(
            f"Level 4 inventory has {len({boundary.qualified for boundary in boundaries})} function families, "
            f"expected {EXPECTED_FAMILIES}"
        )
    return tuple(boundaries)


def parse_trace(path: Path) -> tuple[list[int], list[dict[str, int]]]:
    pcs: list[int] = []
    stores: list[dict[str, int]] = []
    for line in path.read_text().splitlines():
        fields = line.split()
        if not fields:
            continue
        if fields[0] == "E" and len(fields) == 2:
            pcs.append(int(fields[1], 0))
        elif fields[0] == "S" and len(fields) == 6:
            pc, address, width, value, sp = (int(field, 0) for field in fields[1:])
            stores.append({"pc": pc, "address": address, "width": width, "value": value, "sp": sp})
    return pcs, stores


def observation(boundary: Boundary, pcs: list[int], stores: list[dict[str, int]]) -> dict[str, Any]:
    owned = set(boundary.instruction_pcs)
    edges = set(zip(pcs, pcs[1:]))
    declared_stores = [
        store for store in boundary.stores
        if any(all(observed[field] == store[field] for field in store) for observed in stores)
    ]
    return {
        "entryReached": boundary.entry_pc in pcs,
        "exitReached": sorted(set(boundary.exits).intersection(pcs)),
        "instructionEvents": sum(pc in owned for pc in pcs),
        "declaredCallsReached": [
            {"sourcePc": source, "targetPc": target}
            for source, target in boundary.calls if (source, target) in edges
        ],
        "declaredStoresReached": declared_stores,
        "observedStores": [store for store in stores if store["pc"] in owned],
    }


def validate_observation(boundary: Boundary, record: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if not record["entryReached"]:
        failures.append("entry was not observed")
    if not record["exitReached"]:
        failures.append("no declared exit was observed")
    if record["instructionEvents"] <= 0:
        failures.append("no owned instruction was observed")
    if boundary.calls and len(record["declaredCallsReached"]) != len(boundary.calls):
        failures.append("a declared call edge was not observed")
    if boundary.stores and len(record["declaredStoresReached"]) != len(boundary.stores):
        failures.append("a declared store address, width, or value was not observed")
    return failures


def mutation_checks(boundary: Boundary, record: dict[str, Any]) -> dict[str, bool]:
    """Show the checker rejects corruption of every currently measurable clause."""
    mutations = {
        "entry": {**record, "entryReached": False},
        "exit": {**record, "exitReached": []},
        "instruction-count": {**record, "instructionEvents": 0},
    }
    if boundary.calls:
        mutations["call-edge"] = {**record, "declaredCallsReached": []}
    if boundary.stores:
        mutations["store-address-width-value"] = {**record, "declaredStoresReached": []}
    return {name: bool(validate_observation(boundary, mutated)) for name, mutated in mutations.items()}


def run(command: list[str], data: bytes) -> fixtures.Outcome:
    return fixtures.run(command, data)


def run_oracles(args: argparse.Namespace, name: str, data: bytes, accepted: bool) -> dict[str, Any]:
    outcomes = {
        "executionSpecs": run([str(args.reference_python), str(args.reference_program)], data),
        "leanSsz": fixtures.run_lean(args.lean_binary, data),
        "sourceProbe": run([str(args.zesu_value_binary)], data),
    }
    failures: list[str] = []
    if accepted:
        for oracle, outcome in outcomes.items():
            if outcome.returncode != 0:
                failures.append(f"{oracle} rejected accepted vector")
            elif not fixtures.valid_protocol(outcome.stdout):
                failures.append(f"{oracle} emitted malformed ssz-value-v1")
        if len({outcome.stdout for outcome in outcomes.values()}) != 1:
            failures.append("execution-specs, Lean SSZ, and source probe disagree")
    elif any(outcome.returncode == 0 for outcome in outcomes.values()):
        failures.append("an oracle accepted rejected vector")
    return {
        "name": name,
        "accepted": accepted,
        "outcomes": {
            oracle: {"returncode": result.returncode, "sha256": hashlib.sha256(result.stdout).hexdigest()}
            for oracle, result in outcomes.items()
        },
        "failures": failures,
    }


def run_production_trace(args: argparse.Namespace, data: bytes, trace: Path) -> fixtures.Outcome:
    return run(
        ["setarch", "-R", str(args.qemu), "-plugin", f"{args.plugin},out={trace}", str(args.rv64_binary)],
        data,
    )


def default_vectors() -> tuple[tuple[str, bytes, bool], ...]:
    """Focused PR #77 vectors, retained as data rather than its obsolete contract surface."""
    rich = fixtures.make_rich_v4()
    layout = fixtures.layout(rich)
    return (
        ("new-payload-rich", rich, True),
        ("new-payload-noncanonical-offset", fixtures.make_v4(npr_padding=1), False),
        ("new-payload-malformed-deposits", fixtures.make_v4(
            requests=fixtures.execution_requests(deposits=b"X")), False),
        ("execution-witness-rich", rich, True),
        ("execution-witness-empty", fixtures.make_v4(witness_bytes=fixtures.witness((), (), ())), True),
        ("execution-witness-noncanonical-offset", fixtures.set_u32(rich, layout["witness"], 0), False),
        ("chain-config-rich", rich, True),
        ("chain-config-absent-blob-schedule", fixtures.make_v4(
            chain_bytes=fixtures.chain_config(blob_schedule=None)), True),
        ("chain-config-unknown-fork", fixtures.make_v4(chain_bytes=fixtures.chain_config(fork=21)), False),
        ("chain-config-noncanonical-offset", fixtures.set_u32(rich, layout["chain"] + 8, 0), False),
        ("public-keys-rich", rich, True),
        ("public-keys-empty", fixtures.make_v4(public_keys=b""), True),
        ("public-keys-one", fixtures.make_v4(public_keys=b"\x04" + bytes(range(64))), True),
        ("public-keys-nondivisible", fixtures.make_v4(public_keys=bytes(64)), False),
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--reference-python", type=Path, required=True)
    parser.add_argument("--reference-program", type=Path, required=True)
    parser.add_argument("--lean-binary", type=Path, required=True)
    parser.add_argument("--zesu-value-binary", type=Path, required=True)
    parser.add_argument("--qemu", type=Path, required=True)
    parser.add_argument("--plugin", type=Path, required=True)
    parser.add_argument("--rv64-binary", type=Path, required=True)
    parser.add_argument("--out-json", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    boundaries = load_inventory(args.inventory)
    vectors = default_vectors()
    oracle_records = [run_oracles(args, *vector) for vector in vectors]
    failures = [failure for record in oracle_records for failure in record["failures"]]
    vector_observations: list[dict[str, Any]] = []
    all_pcs: list[int] = []
    all_stores: list[dict[str, int]] = []
    with tempfile.TemporaryDirectory(prefix="level4-evidence-") as temporary:
        for name, data, accepted in vectors:
            trace = Path(temporary) / f"{name}.trace"
            production = run_production_trace(args, data, trace)
            expected_return = 0 if accepted else 1
            if production.returncode != expected_return:
                failures.append(f"production ELF returned {production.returncode} for {name}, expected {expected_return}")
            if accepted and not production.stdout.startswith(b"ok "):
                failures.append(f"production ELF accepted {name} without an ok checksum")
            if not accepted and production.stdout != b"invalid\n":
                failures.append(f"production ELF rejected {name} with unexpected output")
            pcs, stores = parse_trace(trace)
            all_pcs.extend(pcs)
            all_stores.extend(stores)
            vector_observations.append({
                "name": name,
                "accepted": accepted,
                "returncode": production.returncode,
                "traceEvents": len(pcs),
                "stores": len(stores),
                "boundaries": {
                    boundary.identifier: observation(boundary, pcs, stores) for boundary in boundaries
                },
            })
    records = []
    for boundary in boundaries:
        record = observation(boundary, all_pcs, all_stores)
        clause_failures = validate_observation(boundary, record)
        mutations = mutation_checks(boundary, record)
        if not all(mutations.values()):
            clause_failures.append("a measurable-clause mutation was accepted")
        failures.extend(f"{boundary.identifier}: {failure}" for failure in clause_failures)
        records.append({
            "boundary": asdict(boundary),
            "observation": record,
            "measuredClauses": [
                "entry", "exit", "owned instruction execution",
                *( ["declared call targets"] if boundary.calls else [] ),
                *( ["declared store address, width, and value"] if boundary.stores else [] ),
            ],
            "unmeasuredClauses": [
                *UNMEASURED_CLAUSES,
                *( ["declared call targets"] if not boundary.calls else [] ),
                *( ["declared store address, width, and value"] if not boundary.stores else [] ),
            ],
            "mutationRejected": mutations,
            "failures": clause_failures,
        })
    report = {
        "schemaVersion": 1,
        "claim": "finite production-ELF evidence; not a proof premise",
        "inventory": {"boundaries": len(boundaries), "functionFamilies": len({b.qualified for b in boundaries})},
        "vectors": oracle_records,
        "productionVectors": vector_observations,
        "production": {"traceEvents": len(all_pcs), "stores": len(all_stores)},
        "boundaries": records,
        "unmeasuredClauses": list(UNMEASURED_CLAUSES),
        "passed": not failures,
        "failures": failures,
    }
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    if failures:
        print("Level 4 contract evidence failed:", file=sys.stderr)
        print("\n".join(f"- {failure}" for failure in failures), file=sys.stderr)
        return 1
    print("Level 4 contract evidence: 18 boundary observations, 15 families, mutations rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
