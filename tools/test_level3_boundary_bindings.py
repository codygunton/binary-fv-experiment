#!/usr/bin/env python3
"""Validate exact Level 3 DWARF boundary-binding coverage."""

import copy
import json
import sys
from pathlib import Path


def validate(report: dict) -> None:
    rows = report["instances"]
    if report["level"] != 3 or len(rows) != 60:
        raise ValueError("boundary report must contain the exact 60 Level 3 instances")
    if len({row["id"] for row in rows}) != len(rows):
        raise ValueError("Level 3 boundary identities must be unique")
    if not all(row["entryPc"] > 0 and row["qualified"] for row in rows):
        raise ValueError("every Level 3 boundary needs a concrete source identity")


def main() -> int:
    report = json.loads(Path(sys.argv[1]).read_text())
    validate(report)
    duplicate = copy.deepcopy(report)
    duplicate["instances"][0]["id"] = duplicate["instances"][1]["id"]
    try:
        validate(duplicate)
    except ValueError:
        pass
    else:
        raise AssertionError("validator accepted a duplicated Level 3 identity")
    missing_entry = copy.deepcopy(report)
    missing_entry["instances"][0]["entryPc"] = 0
    try:
        validate(missing_entry)
    except ValueError:
        pass
    else:
        raise AssertionError("validator accepted a missing Level 3 entry")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
