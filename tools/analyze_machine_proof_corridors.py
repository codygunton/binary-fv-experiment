#!/usr/bin/env python3
"""Deterministically retrieve similar Lean machine-corridor candidates.

This is a read-only prototype: it combines named ``...Pcs`` lists in Lean proof modules with the
pinned ``machine-regions.json`` instruction records. A list is *composition-backed* only when
source text contains a theorem that names that list and an execution composition combinator. This
is a source-level retrieval signal, not evidence that the theorem compiled or discharged every
instruction in the list.
"""
from __future__ import annotations

import argparse
import difflib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

PCS_DEF = re.compile(r"(?:def|abbrev)\s+(\w*Pcs)\s*:\s*(?:List\s+Nat|List\s+UInt64)\s*:=\s*(\[[^\]]*\])", re.S)
HEX = re.compile(r"0x[0-9a-fA-F]+")
COMBINATOR = re.compile(r"\b(decoder\w+Step\w*|Seg\.(?:step|stepJump)|Trace\.(?:append|snoc))\b")
THEOREM = re.compile(r"^\s*(?:private\s+)?theorem\s+(\w+)", re.M)
DECLARATION = re.compile(r"^\s*(?:private\s+)?(?:def|abbrev|theorem)\s+\w+", re.M)
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

@dataclass(frozen=True)
class Corridor:
    module: str
    name: str
    pcs: tuple[int, ...]
    instructions: tuple[Instruction, ...]
    composing_theorems: tuple[str, ...]

    @property
    def composition_backed(self) -> bool:
        return bool(self.composing_theorems)

    @property
    def signature(self) -> tuple[str, ...]:
        roles: dict[str, str] = {}
        def role(match: re.Match[str]) -> str:
            register = match.group(0)
            roles.setdefault(register, f"r{len(roles)}")
            return roles[register]
        result = []
        for instruction in self.instructions:
            operands = REGISTER.sub(role, instruction.operands)
            operands = HEX.sub("imm", operands)
            operands = re.sub(r"\b-?\d+\b", "imm", operands)
            effect = "/".join(f"{kind}{width}" for kind, width in instruction.memory) or "reg"
            result.append(f"{instruction.mnemonic}({operands})[{effect};{instruction.transfer}]")
        return tuple(result)

    @property
    def mnemonic_signature(self) -> tuple[str, ...]:
        return tuple(instruction.mnemonic for instruction in self.instructions)


def machine_instructions_from_document(document: dict) -> dict[int, Instruction]:
    return {
        row["address"]: Instruction(
            pc=row["address"], mnemonic=row["mnemonic"], operands=row["operands"],
            writes=tuple(row["writes"]),
            memory=tuple((effect["kind"], effect["bytes"]) for effect in row["memory"]),
            successors=tuple(row["successors"]), transfer=row["transfer"],
        )
        for row in document["instructions"]
    }


def machine_instructions(path: Path) -> dict[int, Instruction]:
    return machine_instructions_from_document(json.loads(path.read_text()))


def lean_corridors(root: Path, machine: dict[int, Instruction]) -> list[Corridor]:
    corridors: list[Corridor] = []
    for path in sorted(root.rglob("*.lean")):
        source = path.read_text()
        theorem_ranges: list[tuple[str, str]] = []
        for theorem in THEOREM.finditer(source):
            following = DECLARATION.search(source, theorem.end())
            end = following.start() if following else len(source)
            theorem_ranges.append((theorem.group(1), source[theorem.start():end]))
        for match in PCS_DEF.finditer(source):
            pcs = tuple(int(value, 16) for value in HEX.findall(match.group(2)))
            if not pcs or any(pc not in machine for pc in pcs):
                continue
            # An inventory list alone is not a proof. Record source-level composition only where
            # one theorem explicitly names this list and invokes an execution combinator.
            composing = tuple(
                theorem_name for theorem_name, body in theorem_ranges
                if match.group(1) in body and COMBINATOR.search(body)
            )
            corridors.append(Corridor(
                module=str(path), name=match.group(1), pcs=pcs,
                instructions=tuple(machine[pc] for pc in pcs),
                composing_theorems=composing,
            ))
    return corridors


def score(query: Corridor, candidate: Corridor) -> tuple[int, float, int]:
    """Exact sequence, then length-aware normalized subsequence similarity, then mnemonic LCS."""
    normalized = difflib.SequenceMatcher(a=query.signature, b=candidate.signature, autojunk=False)
    mnemonics = difflib.SequenceMatcher(a=query.mnemonic_signature, b=candidate.mnemonic_signature, autojunk=False)
    return int(query.signature == candidate.signature), normalized.ratio(), sum(block.size for block in mnemonics.get_matching_blocks())


def retrieve(corridors: Iterable[Corridor], machine: dict[int, Instruction], pcs: tuple[int, ...], limit: int) -> list[dict[str, object]]:
    all_corridors = list(corridors)
    missing = [pc for pc in pcs if pc not in machine]
    if missing:
        raise ValueError(f"query PCs absent from machine-regions: {missing}")
    query = Corridor("<query>", "query", pcs, tuple(machine[pc] for pc in pcs), ())
    ranked = [candidate for candidate in all_corridors if candidate.composition_backed and candidate.pcs != pcs]
    ranked.sort(key=lambda candidate: (score(query, candidate), candidate.module, candidate.name), reverse=True)
    return [
        {"score": score(query, candidate), "module": candidate.module, "name": candidate.name,
         "pcs": list(candidate.pcs), "mnemonics": list(candidate.mnemonic_signature),
         "compositionBacked": True, "composingTheorems": list(candidate.composing_theorems)}
        for candidate in ranked[:limit]
    ]


def report(corridors: list[Corridor], machine: dict[int, Instruction], queries: list[tuple[int, ...]]) -> dict[str, object]:
    clusters: dict[tuple[str, ...], list[Corridor]] = {}
    for corridor in corridors:
        clusters.setdefault(corridor.mnemonic_signature, []).append(corridor)
    return {
        "schemaVersion": 1,
        "inventoryCorridorCount": len(corridors),
        "compositionBackedCorridorCount": sum(c.composition_backed for c in corridors),
        "clusterCount": len(clusters),
        "clusters": [
            {"mnemonics": list(signature), "members": [
                {"module": corridor.module, "name": corridor.name, "pcs": list(corridor.pcs),
                 "compositionBacked": corridor.composition_backed,
                 "composingTheorems": list(corridor.composing_theorems)} for corridor in members]}
            for signature, members in sorted(clusters.items(), key=lambda item: (-len(item[1]), item[0]))
        ],
        "relevanceCriterion": (
            "A result is manually useful only if it is composition-backed and a reviewer can name "
            "a concrete reusable instruction/proof shape from the source theorem; matching mnemonic "
            "text alone is not useful."
        ),
        "queries": [{"pcs": list(query), "matches": retrieve(corridors, machine, query, 5)} for query in queries],
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
    result = report(corridors, machine, queries)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"composition-backed corridors: {result['compositionBackedCorridorCount']}/{len(corridors)}; mnemonic clusters: {result['clusterCount']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
