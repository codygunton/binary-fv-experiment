#!/usr/bin/env python3
"""Deterministically retrieve similar discharged Lean machine-proof corridors.

This is a read-only prototype: it combines named ``...Pcs`` lists in Lean proof modules with the
pinned ``machine-regions.json`` instruction records.  It deliberately does not infer proof
correctness.  Its output is a retrieval index for finding already-dischargeable instruction shapes
and their local proof combinators.
"""
from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

PCS_DEF = re.compile(r"(?:def|abbrev)\s+(\w*Pcs)\s*:\s*(?:List\s+Nat|List\s+UInt64)\s*:=\s*(\[[^\]]*\])", re.S)
HEX = re.compile(r"0x[0-9a-fA-F]+")
COMBINATOR = re.compile(r"\b(decoder\w+Step\w*|Seg\.(?:step|stepJump)|Trace\.(?:append|snoc))\b")
REGISTER = re.compile(r"\b(?:zero|ra|sp|gp|tp|t[0-6]|s(?:[0-9]|1[01])|a[0-7])\b")
MEMORY = re.compile(r"(?P<source>\w+),\s*(?P<offset>-?0x[0-9a-fA-F]+|-?\d+)\((?P<base>\w+)\)")


@dataclass(frozen=True)
class Instruction:
    pc: int
    mnemonic: str
    operands: str
    writes: tuple[str, ...]
    memory: tuple[tuple[str, int], ...]
    successors: tuple[int, ...]
    transfer: str

    def normalized(self) -> str:
        roles: dict[str, str] = {}
        def role(match: re.Match[str]) -> str:
            reg = match.group(0)
            roles.setdefault(reg, f"r{len(roles)}")
            return roles[reg]
        operands = REGISTER.sub(role, self.operands)
        operands = HEX.sub("imm", operands)
        operands = re.sub(r"\b-?\d+\b", "imm", operands)
        effect = "/".join(f"{kind}{width}" for kind, width in self.memory) or "reg"
        return f"{self.mnemonic}({operands})[{effect};{self.transfer}]"


@dataclass(frozen=True)
class Corridor:
    module: str
    name: str
    pcs: tuple[int, ...]
    instructions: tuple[Instruction, ...]
    combinators: tuple[str, ...]

    @property
    def signature(self) -> tuple[str, ...]:
        return tuple(instruction.normalized() for instruction in self.instructions)

    @property
    def mnemonic_signature(self) -> tuple[str, ...]:
        return tuple(instruction.mnemonic for instruction in self.instructions)


def machine_instructions(path: Path) -> dict[int, Instruction]:
    document = json.loads(path.read_text())
    return {
        row["address"]: Instruction(
            pc=row["address"], mnemonic=row["mnemonic"], operands=row["operands"],
            writes=tuple(row["writes"]),
            memory=tuple((effect["kind"], effect["bytes"]) for effect in row["memory"]),
            successors=tuple(row["successors"]), transfer=row["transfer"],
        )
        for row in document["instructions"]
    }


def lean_corridors(root: Path, machine: dict[int, Instruction]) -> list[Corridor]:
    corridors: list[Corridor] = []
    for path in sorted(root.rglob("*.lean")):
        source = path.read_text()
        for match in PCS_DEF.finditer(source):
            pcs = tuple(int(value, 16) for value in HEX.findall(match.group(2)))
            if not pcs or any(pc not in machine for pc in pcs):
                continue
            # Limit combinators to the declaration's local neighborhood, not the whole module.
            neighborhood = source[match.start(): source.find("\ndef ", match.end()) if source.find("\ndef ", match.end()) >= 0 else len(source)]
            corridors.append(Corridor(
                module=str(path), name=match.group(1), pcs=pcs,
                instructions=tuple(machine[pc] for pc in pcs),
                combinators=tuple(sorted(set(COMBINATOR.findall(neighborhood)))),
            ))
    return corridors


def score(query: Corridor, candidate: Corridor) -> tuple[int, int, int]:
    """Lexicographic: exact normalized sequence, mnemonic sequence, then shared effects."""
    exact = int(query.signature == candidate.signature)
    mnemonics = sum(a == b for a, b in zip(query.mnemonic_signature, candidate.mnemonic_signature))
    effects = sum(bool(a.memory) == bool(b.memory) for a, b in zip(query.instructions, candidate.instructions))
    return exact, mnemonics, effects


def retrieve(corridors: Iterable[Corridor], pcs: tuple[int, ...], limit: int) -> list[dict[str, object]]:
    all_corridors = list(corridors)
    by_pc = {instruction.pc: instruction for corridor in all_corridors for instruction in corridor.instructions}
    query = Corridor("<query>", "query", pcs, tuple(by_pc[pc] for pc in pcs), ())
    ranked = [candidate for candidate in all_corridors if candidate.pcs != pcs]
    ranked.sort(key=lambda candidate: (score(query, candidate), candidate.module, candidate.name), reverse=True)
    return [
        {"score": score(query, candidate), "module": candidate.module, "name": candidate.name,
         "pcs": list(candidate.pcs), "mnemonics": list(candidate.mnemonic_signature),
         "combinators": list(candidate.combinators)}
        for candidate in ranked[:limit]
    ]


def report(corridors: list[Corridor], queries: list[tuple[int, ...]]) -> dict[str, object]:
    clusters: dict[tuple[str, ...], list[Corridor]] = {}
    for corridor in corridors:
        clusters.setdefault(corridor.mnemonic_signature, []).append(corridor)
    return {
        "schemaVersion": 1,
        "corridorCount": len(corridors),
        "clusterCount": len(clusters),
        "clusters": [
            {"mnemonics": list(signature), "members": [
                {"module": corridor.module, "name": corridor.name, "pcs": list(corridor.pcs),
                 "combinators": list(corridor.combinators)} for corridor in members]}
            for signature, members in sorted(clusters.items(), key=lambda item: (-len(item[1]), item[0]))
        ],
        "queries": [{"pcs": list(query), "matches": retrieve(corridors, query, 5)} for query in queries],
    }


def parse_pcs(text: str) -> tuple[int, ...]:
    return tuple(int(value, 0) for value in text.split(",") if value)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--machine-regions", type=Path, required=True)
    parser.add_argument("--lean-root", type=Path, default=Path("BinaryFv/Zesu/MachineExecution"))
    parser.add_argument("--query-pcs", action="append", default=[])
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    machine = machine_instructions(args.machine_regions)
    corridors = lean_corridors(args.lean_root, machine)
    queries = [parse_pcs(query) for query in args.query_pcs]
    result = report(corridors, queries)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"machine proof corridors: {len(corridors)}; mnemonic clusters: {result['clusterCount']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
