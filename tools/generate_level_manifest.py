#!/usr/bin/env python3
"""Generate the reviewed immediate-child manifest for one flamegraph level."""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
import json
import re
from pathlib import Path


INSTANCE = re.compile(r"^(?P<qualified>.+) \[(?P<id>(?:fi|fn):[^]]+)\]$")


def generate(cfg: dict, flame: dict, level: int) -> dict:
    if level < 1:
        raise ValueError("a refinement manifest must select Level 1 or deeper")
    rows = {row["id"]: row for row in cfg["functionInstances"]}
    concrete_entries = {row["entryPc"] for row in rows.values() if row["kind"] == "concrete"}
    for function in cfg["functions"]:
        if function["start"] in concrete_entries:
            continue
        identifier = f"fn:0x{function['start']:x}"
        pcs = [instruction["pc"] for block in function["blocks"]
               for instruction in block["instructions"]]
        rows[identifier] = {
            "id": identifier, "name": function["name"], "kind": "concrete",
            "parent": None, "entryPc": function["start"], "pcs": pcs,
            "instructionCount": len(pcs), "dieOffset": 0,
            "sourceFile": function.get("sourceFile") or "runtime/riscv64/riscv64_baremetal_host.S",
            "declLine": function.get("sourceLine", 0), "callFile": None, "callLine": 0,
        }
    instruction_at_pc = {}
    successors: dict[int, set[int]] = defaultdict(set)
    for function in cfg["functions"]:
        for block in function["blocks"]:
            instructions = block["instructions"]
            for instruction in instructions:
                instruction_at_pc[instruction["pc"]] = instruction
            for before, after in zip(instructions, instructions[1:]):
                successors[before["pc"]].add(after["pc"])
            if instructions:
                successors[instructions[-1]["pc"]].update(int(pc, 16) for pc in block["successors"])
    children: dict[str, list[str]] = {}
    for row in rows.values():
        if row["parent"] is not None:
            children.setdefault(row["parent"], []).append(row["id"])

    def inline_descendant_pcs(identifier: str) -> set[int]:
        result: set[int] = set()
        pending = list(children.get(identifier, []))
        while pending:
            child = pending.pop()
            result.update(rows[child]["pcs"])
            pending.extend(children.get(child, []))
        return result

    def resolve(display_identifier: str) -> str:
        if not display_identifier.startswith("fn:"):
            return display_identifier
        if display_identifier in rows:
            return display_identifier
        entry = int(display_identifier.removeprefix("fn:"), 16)
        candidates = [row["id"] for row in rows.values()
                      if row["kind"] == "concrete" and row["entryPc"] == entry]
        if len(candidates) != 1:
            raise ValueError(f"synthetic identity {display_identifier} has {len(candidates)} CFG matches")
        return candidates[0]

    def local_pcs(identifier: str) -> set[int]:
        return set(rows[identifier]["pcs"]) - inline_descendant_pcs(identifier)

    def source_declaration(identifier: str) -> dict:
        row = rows[identifier]
        return {"file": row["sourceFile"], "qualifiedName": row["name"]}

    def stable_identity(identifier: str) -> dict:
        row = rows[identifier]
        sites = []
        current = row
        while current["parent"] is not None:
            parent = rows[current["parent"]]
            sites.append({
                "caller": source_declaration(parent["id"]),
                "callSite": {
                    "file": current["callFile"],
                    "line": current["callLine"],
                    "column": 0,
                },
            })
            current = parent
        sites.reverse()
        return {
            "function": {
                "declaration": source_declaration(identifier),
                "specialization": [],
            },
            "inlineStack": sites,
        }

    def concrete_ancestor(identifier: str) -> str:
        current = rows[identifier]
        while current["kind"] != "concrete":
            if current["parent"] is None:
                raise ValueError(f"inlined instance {identifier} has no concrete ancestor")
            current = rows[current["parent"]]
        return current["id"]

    concrete_by_entry: dict[int, list[str]] = defaultdict(list)
    for row in rows.values():
        if row["kind"] == "concrete":
            concrete_by_entry[row["entryPc"]].append(row["id"])
    concrete_by_name: dict[str, str] = {}
    for function in cfg["functions"]:
        candidates = concrete_by_entry.get(function["start"], [])
        if len(candidates) == 1:
            concrete_by_name[function["name"]] = candidates[0]
    if "main" not in concrete_by_name:
        raise ValueError("main concrete function instance is absent")

    call_rows = cfg.get("calls", []) + cfg.get("reviewedIndirectCalls", [])
    return_targets: dict[str, set[int]] = defaultdict(set)
    tail_calls: list[tuple[str, str]] = []
    for call in call_rows:
        instruction = instruction_at_pc[call["source"]]
        links = call.get("kind") == "allocator-vtable" or (
            instruction["mnemonic"] in {"jal", "jalr"} and
            instruction["operands"].startswith("ra,"))
        if links:
            return_targets[call["callee"]].add(call["source"] + 4)
        else:
            tail_calls.append((call["caller"], call["callee"]))
    changed = True
    while changed:
        changed = False
        for caller, callee in tail_calls:
            inherited = return_targets[caller] - return_targets[callee]
            if inherited:
                return_targets[callee].update(inherited)
                changed = True

    inline_rows = [row for row in rows.values() if row["kind"] == "inlined"]
    claimed_inline_pcs = set().union(*(set(candidate["pcs"]) for candidate in inline_rows))

    def call_owner(call: dict) -> str:
        containing = [row for row in inline_rows if call["source"] in row["pcs"]]
        if containing:
            return min(containing, key=lambda row: (row["instructionCount"], -row["dieOffset"]))["id"]
        if call["caller"] not in concrete_by_name:
            raise ValueError(f"call source has no concrete or inline owner: {call}")
        return concrete_by_name[call["caller"]]

    edges: dict[str, set[str]] = defaultdict(set)
    for row in rows.values():
        if row["parent"] is not None:
            edges[row["parent"]].add(row["id"])
    for call in call_rows:
        target = concrete_by_name.get(call["callee"])
        if target is None:
            raise ValueError(f"call target has no concrete DWARF instance: {call}")
        edges[call_owner(call)].add(target)

    root_identifier = concrete_by_name["main"]
    depths = {root_identifier: 0}
    pending = deque([root_identifier])
    while pending:
        parent = pending.popleft()
        for child in edges[parent]:
            if child not in depths or depths[child] > depths[parent] + 1:
                depths[child] = depths[parent] + 1
                pending.append(child)

    def execution_pcs(identifier: str) -> set[int]:
        reachable: set[str] = set()
        pending = [identifier]
        while pending:
            current = pending.pop()
            if current in reachable:
                continue
            reachable.add(current)
            pending.extend(edges[current])
        return set().union(*(local_pcs(current) for current in reachable))

    selected = []
    for identifier in sorted((identifier for identifier, depth in depths.items() if depth == level),
                             key=lambda identifier: (rows[identifier]["entryPc"], identifier)):
        row = rows[identifier]
        owned_pcs = sorted(set(row["pcs"]) - inline_descendant_pcs(identifier))
        absorbed_pcs = []
        if row["kind"] == "inlined":
            # Optimized inlined ranges may have short caller-attributed holes. Absorb only holes
            # between this instance's first and last owned PC; never absorb trailing call setup.
            absorbed_pcs = sorted(pc for pc in instruction_at_pc
                                  if row["entryPc"] <= pc <= max(row["pcs"])
                                  and pc not in claimed_inline_pcs)
        subtree = execution_pcs(identifier) | set(absorbed_pcs)
        exit_pcs = {
            target for pc in subtree for target in successors.get(pc, set()) if target not in subtree
        }
        for call in call_rows:
            call_instruction = instruction_at_pc[call["source"]]
            links = call.get("kind") == "allocator-vtable" or (
                call_instruction["mnemonic"] in {"jal", "jalr"} and
                call_instruction["operands"].startswith("ra,"))
            if call["source"] in subtree and links and call["source"] + 4 not in subtree:
                exit_pcs.add(call["source"] + 4)
        if row["kind"] == "concrete" and row["name"] != "zkvm_exit":
            exit_pcs.update(return_targets[row["name"]])
        if row["name"] == "zkvm_exit":
            exit_pcs = {
                pc for pc in subtree if pc in successors.get(pc, set())
            }
        else:
            exit_pcs.update(
                pc for pc in subtree
                if instruction_at_pc[pc]["mnemonic"] == "ecall" and not successors.get(pc)
            )
        if row["kind"] == "inlined" and any(
                instruction_at_pc[pc]["mnemonic"] == "ret" for pc in subtree):
            ancestor = rows[concrete_ancestor(identifier)]
            exit_pcs.update(return_targets[ancestor["name"]])
        subtree_pcs = sorted(subtree)
        selected.append({
            "id": identifier,
            "parentInstanceIds": sorted(
                parent for parent, child_ids in edges.items()
                if depths.get(parent) == level - 1 and identifier in child_ids
            ),
            "qualified": row["name"],
            "kind": row["kind"],
            "functionInstanceIdentity": stable_identity(identifier),
            "sourceFile": row["sourceFile"],
            "declLine": row["declLine"],
            "entryPc": row["entryPc"],
            "instructionPcs": owned_pcs,
            "absorbedInstructionPcs": absorbed_pcs,
            "executionPcs": subtree_pcs,
            "exitPcs": sorted(exit_pcs),
            "ownedInstructionCount": len(owned_pcs),
            "subtreeInstructionCount": len(subtree_pcs),
        })
    return {
        "schemaVersion": 1,
        "artifact": cfg["artifact"],
        "level": level,
        "parent": flame["tree"]["name"],
        "instances": selected,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cfg", required=True, type=Path)
    parser.add_argument("--flame", required=True, type=Path)
    parser.add_argument("--level", required=True, type=int)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = generate(json.loads(args.cfg.read_text()), json.loads(args.flame.read_text()), args.level)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
