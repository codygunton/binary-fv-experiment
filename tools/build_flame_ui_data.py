#!/usr/bin/env python3
"""Split flamegraph data into a compact render payload and lazy detail payload."""

import argparse
import json
from pathlib import Path


CORE_META_FIELDS = (
    "owner",
    "machineOwner",
    "qualified",
    "displayTreeLevel",
    "refinementLevel",
    "machineInstructionCount",
)


def split_flame(data: dict) -> tuple[dict, list[dict]]:
    details: list[dict] = []

    def visit(node: dict) -> dict:
        ui_id = len(details)
        details.append(data["meta"][node["key"]])
        result = {key: value for key, value in node.items() if key not in ("key", "children")}
        result["uiId"] = ui_id
        if node.get("children"):
            result["children"] = [visit(child) for child in node["children"]]
        return result

    tree = visit(data["tree"])
    core = {
        "schemaVersion": data["schemaVersion"],
        "tree": tree,
        "meta": [
            {field: row[field] for field in CORE_META_FIELDS if field in row}
            for row in details
        ],
        "total": data["total"],
        "programTotal": data["programTotal"],
        "machineRegionInputs": data["machineRegionInputs"],
    }
    return core, details


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--core", required=True, type=Path)
    parser.add_argument("--details", required=True, type=Path)
    args = parser.parse_args()
    core, details = split_flame(json.loads(args.input.read_text()))
    args.core.write_text(json.dumps(core, sort_keys=True, separators=(",", ":")) + "\n")
    args.details.write_text(json.dumps(details, sort_keys=True, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
