#!/usr/bin/env python3
"""Validate exact Level 2 DWARF binding coverage and reject forged identity."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def validate(report: dict) -> None:
    rows = report["instances"]
    if report["level"] != 2 or len(rows) != 20:
        raise ValueError("boundary report must contain the exact 20 bare-metal Level 2 instances")
    if len({row["id"] for row in rows}) != len(rows):
        raise ValueError("Level 2 boundary identities must be unique")
    if not all(row["entryPc"] > 0 for row in rows):
        raise ValueError("every Level 2 boundary needs a concrete entry")


def main() -> int:
    report = json.loads(Path(sys.argv[1]).read_text())
    validate(report)
    mutated = json.loads(json.dumps(report))
    mutated["instances"][0]["id"] = mutated["instances"][1]["id"]
    try:
        validate(mutated)
    except ValueError:
        pass
    else:
        raise AssertionError("validator accepted a duplicated Level 2 identity")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
