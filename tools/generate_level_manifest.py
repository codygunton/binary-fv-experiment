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
    if level != 1:
        raise ValueError("the SSZ spike currently freezes only Level 1")
    rows = {row["id"]: row for row in cfg["functionInstances"]}
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

    inline_rows = [row for row in rows.values() if row["kind"] == "inlined"]

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
    for call in cfg.get("calls", []):
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
        subtree_pcs = sorted(execution_pcs(identifier))
        selected.append({
            "id": identifier,
            "qualified": row["name"],
            "kind": row["kind"],
            "functionInstanceIdentity": stable_identity(identifier),
            "sourceFile": row["sourceFile"],
            "declLine": row["declLine"],
            "entryPc": row["entryPc"],
            "instructionPcs": owned_pcs,
            "executionPcs": subtree_pcs,
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
