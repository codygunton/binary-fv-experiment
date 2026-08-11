#!/usr/bin/env python3
"""Generate the reviewed immediate-child manifest for one flamegraph level."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


INSTANCE = re.compile(r"^(?P<qualified>.+) \[(?P<id>(?:fi|fn):[^]]+)\]$")


def generate(cfg: dict, flame: dict, level: int) -> dict:
    if level != 1:
        raise ValueError("the SSZ spike currently freezes only Level 1")
    root = flame["tree"]
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

    selected = []
    for node in root["children"]:
        match = INSTANCE.fullmatch(node["name"])
        if match is None:
            raise ValueError(f"Level 1 node lacks a generated identity: {node['name']}")
        display_identifier = match.group("id")
        identifier = display_identifier
        if display_identifier.startswith("fn:"):
            entry = int(display_identifier.removeprefix("fn:"), 16)
            candidates = [row["id"] for row in rows.values()
                          if row["kind"] == "concrete" and row["entryPc"] == entry]
            if len(candidates) != 1:
                raise ValueError(f"synthetic identity {display_identifier} has {len(candidates)} CFG matches")
            identifier = candidates[0]
        if identifier not in rows:
            raise ValueError(f"Level 1 identity is absent from CFG: {identifier}")
        row = rows[identifier]
        owned_pcs = sorted(set(row["pcs"]) - inline_descendant_pcs(identifier))
        if len(owned_pcs) != node["self"]:
            raise ValueError(f"owned instruction count drift for {identifier}")
        selected.append({
            "id": identifier,
            "qualified": match.group("qualified"),
            "kind": row["kind"],
            "sourceFile": row["sourceFile"],
            "declLine": row["declLine"],
            "entryPc": row["entryPc"],
            "instructionPcs": owned_pcs,
            "ownedInstructionCount": node["self"],
            "subtreeInstructionCount": node["value"],
        })
    selected.sort(key=lambda row: (row["entryPc"], row["id"]))
    return {
        "schemaVersion": 1,
        "artifact": cfg["artifact"],
        "level": level,
        "parent": root["name"],
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
