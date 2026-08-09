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
        boundaries.append(Boundary(identifier, kind, qualified, entry, pcs, exits, parent, identity))

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
    return {
        "entryReached": boundary.entry_pc in pcs,
        "exitReached": sorted(set(boundary.exits).intersection(pcs)),
        "instructionEvents": sum(pc in owned for pc in pcs),
        "observedWrites": [store for store in stores if store["pc"] in owned],
    }


def validate_observation(boundary: Boundary, record: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if not record["entryReached"]:
        failures.append("entry was not observed")
    if not record["exitReached"]:
        failures.append("no declared exit was observed")
    if record["instructionEvents"] <= 0:
        failures.append("no owned instruction was observed")
    return failures


def mutation_checks(boundary: Boundary, record: dict[str, Any]) -> dict[str, bool]:
    """Show the checker rejects corruption of every currently measurable clause."""
    mutations = {
        "entry": {**record, "entryReached": False},
        "exit": {**record, "exitReached": []},
        "instruction-count": {**record, "instructionEvents": 0},
    }
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
    rich = fixtures.make_rich_v4()
    # Removing the SSZ schema id gives every oracle and the production executable a small malformed input.
    return (("accepted-rich", rich, True), ("rejected-missing-schema", rich[1:], False))


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
    oracle_records = [run_oracles(args, *vector) for vector in default_vectors()]
    failures = [failure for record in oracle_records for failure in record["failures"]]
    accepted = default_vectors()[0][1]
    with tempfile.TemporaryDirectory(prefix="level4-evidence-") as temporary:
        trace = Path(temporary) / "accepted.trace"
        production = run_production_trace(args, accepted, trace)
        if production.returncode != 0 or not production.stdout.startswith(b"ok "):
            failures.append("production ELF rejected accepted vector")
        pcs, stores = parse_trace(trace)
    records = []
    for boundary in boundaries:
        record = observation(boundary, pcs, stores)
        clause_failures = validate_observation(boundary, record)
        mutations = mutation_checks(boundary, record)
        if not all(mutations.values()):
            clause_failures.append("a measurable-clause mutation was accepted")
        failures.extend(f"{boundary.identifier}: {failure}" for failure in clause_failures)
        records.append({
            "boundary": asdict(boundary),
            "observation": record,
            "measuredClauses": ["entry", "exit", "owned instruction execution"],
            "unmeasuredClauses": list(UNMEASURED_CLAUSES),
            "mutationRejected": mutations,
            "failures": clause_failures,
        })
    report = {
        "schemaVersion": 1,
        "claim": "finite production-ELF evidence; not a proof premise",
        "inventory": {"boundaries": len(boundaries), "functionFamilies": len({b.qualified for b in boundaries})},
        "vectors": oracle_records,
        "production": {"returncode": production.returncode, "traceEvents": len(pcs), "stores": len(stores)},
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
