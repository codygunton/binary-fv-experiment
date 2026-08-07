#!/usr/bin/env python3
"""Contract-specific vectors for the deepest conditions exposed below ``decodeRaw``.

Every vector runs the pinned execution-specs reference, the executable Lean specification, the
host Zesu value formatter, and the unchanged RV64 production executable.  The QEMU trace must enter
the compiled function instance named by the vector, so agreement at the exported decoder cannot be
mistaken for evidence about a child that never ran.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

import ssz_differential_audit as fixtures


DIRECT_READ_OFFSET_LINES = (199, 200, 201, 202)


@dataclass(frozen=True)
class ContractVector:
    name: str
    qualified: str
    claim: str
    data: bytes
    valid: bool


def vectors() -> tuple[ContractVector, ...]:
    rich = fixtures.make_rich_v4()
    rich_layout = fixtures.layout(rich)
    return (
        ContractVector(
            "new-payload-rich",
            "ssz_raw.decodeNewPayloadRequest",
            "accepted value carries the payload, versioned hashes, parent root, and requests",
            rich,
            True,
        ),
        ContractVector(
            "new-payload-noncanonical-offset",
            "ssz_raw.decodeNewPayloadRequest",
            "noncanonical first offset is rejected",
            fixtures.make_v4(npr_padding=1),
            False,
        ),
        ContractVector(
            "new-payload-malformed-deposits",
            "ssz_raw.decodeNewPayloadRequest",
            "malformed execution-request element width is rejected",
            fixtures.make_v4(requests=fixtures.execution_requests(deposits=b"X")),
            False,
        ),
        ContractVector(
            "execution-witness-rich",
            "ssz_raw.decodeExecutionWitness",
            "accepted value carries all state, code, and header byte lists",
            rich,
            True,
        ),
        ContractVector(
            "execution-witness-empty",
            "ssz_raw.decodeExecutionWitness",
            "three empty witness collections are accepted as empty arrays",
            fixtures.make_v4(witness_bytes=fixtures.witness((), (), ())),
            True,
        ),
        ContractVector(
            "execution-witness-noncanonical-offset",
            "ssz_raw.decodeExecutionWitness",
            "noncanonical witness collection offset is rejected",
            fixtures.set_u32(rich, rich_layout["witness"], 0),
            False,
        ),
        ContractVector(
            "chain-config-rich",
            "ssz_raw.decodeChainConfig",
            "accepted value carries chain id, fork, activation, and blob schedule",
            rich,
            True,
        ),
        ContractVector(
            "chain-config-absent-blob-schedule",
            "ssz_raw.decodeChainConfig",
            "an absent optional blob schedule is accepted as none",
            fixtures.make_v4(chain_bytes=fixtures.chain_config(blob_schedule=None)),
            True,
        ),
        ContractVector(
            "chain-config-unknown-fork",
            "ssz_raw.decodeChainConfig",
            "an unknown fork index is rejected",
            fixtures.make_v4(chain_bytes=fixtures.chain_config(fork=21)),
            False,
        ),
        ContractVector(
            "chain-config-noncanonical-offset",
            "ssz_raw.decodeChainConfig",
            "a noncanonical fork offset is rejected",
            fixtures.set_u32(rich, rich_layout["chain"] + 8, 0),
            False,
        ),
        ContractVector(
            "public-keys-rich",
            "ssz_raw.decodePublicKeys",
            "accepted value carries every 65-byte public key",
            rich,
            True,
        ),
        ContractVector(
            "public-keys-empty",
            "ssz_raw.decodePublicKeys",
            "an empty public-key list is accepted as an empty array",
            fixtures.make_v4(public_keys=b""),
            True,
        ),
        ContractVector(
            "public-keys-one",
            "ssz_raw.decodePublicKeys",
            "one 65-byte public key is accepted unchanged",
            fixtures.make_v4(public_keys=b"\x04" + bytes(range(64))),
            True,
        ),
        ContractVector(
            "public-keys-nondivisible",
            "ssz_raw.decodePublicKeys",
            "a byte length not divisible by 65 is rejected",
            fixtures.make_v4(public_keys=bytes(64)),
            False,
        ),
    )


def function_entries(program: dict) -> dict[str, int]:
    entries: dict[str, list[int]] = {}
    for function_instance in program["function_instances"]:
        entries.setdefault(function_instance["qualified"], []).append(function_instance["entryPc"])
    result = {}
    for qualified in {vector.qualified for vector in vectors()}:
        candidates = entries.get(qualified, [])
        if len(candidates) != 1:
            raise ValueError(f"{qualified} has {len(candidates)} compiled instances, expected one")
        result[qualified] = candidates[0]
    return result


def direct_read_offset_entries(program: dict) -> tuple[int, ...]:
    """Return the four `decodeRaw`-direct `readOffset` entries in source call order.

    The production trace cannot observe the value passed between inlined instructions, but it can
    prove that every vector reached each selected occurrence.  Match the full one-frame inline
    stack so nested `readOffset` instances in the four selected decoders are not credited here.
    """
    entries = []
    for line in DIRECT_READ_OFFSET_LINES:
        candidates = [
            occurrence["entryPc"]
            for occurrence in program["function_instances"]
            if occurrence["qualified"] == "ssz_raw.readOffset"
            and occurrence["inlineStack"] == [
                {
                    "callerFile": "src/stateless/stateless/ssz_raw.zig",
                    "callerQualified": "ssz_raw.decodeRaw",
                    "line": line,
                    "column": 23,
                }
            ]
        ]
        if len(candidates) != 1:
            raise ValueError(
                f"decodeRaw line {line} has {len(candidates)} direct readOffset instances, expected one"
            )
        entries.append(candidates[0])
    return tuple(entries)


def executed_pcs(trace: Path) -> set[int]:
    return {
        int(parts[1])
        for line in trace.read_text().splitlines()
        if (parts := line.split()) and parts[0] == "E"
    }


def run_production(
    vector: ContractVector, qemu: Path, plugin: Path, binary: Path, scratch: Path
) -> tuple[fixtures.Outcome, set[int]]:
    trace = scratch / f"{vector.name}.trace"
    outcome = fixtures.run(
        ["setarch", "-R", str(qemu), "-plugin", f"{plugin},out={trace}", str(binary)],
        vector.data,
    )
    return outcome, executed_pcs(trace)


def validate_vector(
    vector: ContractVector,
    entry: int,
    read_offset_entries: tuple[int, ...],
    reference_python: Path,
    reference_program: Path,
    lean_binary: Path,
    zesu_value_binary: Path,
    qemu: Path,
    plugin: Path,
    rv64_binary: Path,
    scratch: Path,
) -> dict:
    outcomes = {
        "execution_specs": fixtures.run(
            [str(reference_python), str(reference_program)], vector.data
        ),
        "lean": fixtures.run_lean(lean_binary, vector.data),
        "zesu_value": fixtures.run([str(zesu_value_binary)], vector.data),
    }
    production, pcs = run_production(vector, qemu, plugin, rv64_binary, scratch)
    failures = []
    if entry not in pcs:
        failures.append(f"production trace never entered 0x{entry:x}")
    for read_offset_entry in read_offset_entries:
        if read_offset_entry not in pcs:
            failures.append(f"production trace never entered direct readOffset 0x{read_offset_entry:x}")
    if vector.valid:
        for name, outcome in outcomes.items():
            if outcome.returncode != 0:
                error = outcome.stderr.decode(errors="replace").strip()
                failures.append(f"{name} rejected a valid vector: {error}")
            if not fixtures.valid_protocol(outcome.stdout):
                failures.append(f"{name} emitted malformed ssz-value-v1")
        streams = [outcome.stdout for outcome in outcomes.values()]
        if len(set(streams)) != 1:
            failures.append("value oracles disagreed")
        if production.returncode != 0 or not production.stdout.startswith(b"ok "):
            failures.append("production executable rejected a valid vector")
    else:
        for name, outcome in outcomes.items():
            if outcome.returncode == 0:
                failures.append(f"{name} accepted an invalid vector")
        if production.returncode != 1 or production.stdout != b"invalid\n":
            failures.append("production executable accepted an invalid vector")
    return {
        "name": vector.name,
        "qualified": vector.qualified,
        "claim": vector.claim,
        "valid": vector.valid,
        "entryPc": entry,
        "productionEntryReached": entry in pcs,
        "directReadOffsetEntries": list(read_offset_entries),
        "directReadOffsetsReached": all(entry in pcs for entry in read_offset_entries),
        "valueDigest": None
        if not vector.valid
        else fixtures.digest(outcomes["execution_specs"].stdout),
        "passed": not failures,
        "failures": failures,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference-python", type=Path, required=True)
    parser.add_argument("--reference-program", type=Path, required=True)
    parser.add_argument("--lean-binary", type=Path, required=True)
    parser.add_argument("--zesu-value-binary", type=Path, required=True)
    parser.add_argument("--qemu", type=Path, required=True)
    parser.add_argument("--plugin", type=Path, required=True)
    parser.add_argument("--rv64-binary", type=Path, required=True)
    parser.add_argument("--program-json", type=Path, required=True)
    parser.add_argument("--out-json", type=Path, required=True)
    parser.add_argument("--scratch", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    program = json.loads(args.program_json.read_text())
    entries = function_entries(program)
    read_offset_entries = direct_read_offset_entries(program)
    failures = []
    with tempfile.TemporaryDirectory(prefix="level-refinement-") as temporary:
        scratch = args.scratch or Path(temporary)
        scratch.mkdir(parents=True, exist_ok=True)
        records = []
        for vector in vectors():
            record = validate_vector(
                vector,
                entries[vector.qualified],
                read_offset_entries,
                args.reference_python,
                args.reference_program,
                args.lean_binary,
                args.zesu_value_binary,
                args.qemu,
                args.plugin,
                args.rv64_binary,
                scratch,
            )
            records.append(record)
            failures.extend(f"{vector.name}: {failure}" for failure in record["failures"])
        report = {
            "schemaVersion": 1,
            "vectors": records,
            "summary": {
                "contracts": len({record["qualified"] for record in records}),
                "vectors": len(records),
                "passed": sum(record["passed"] for record in records),
                "failed": sum(not record["passed"] for record in records),
            },
        }
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    if failures:
        for failure in failures:
            print(failure)
        return 1
    print(f"deep decoder contract vectors: ok ({len(records)} vectors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
