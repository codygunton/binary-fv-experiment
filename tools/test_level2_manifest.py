#!/usr/bin/env python3
"""Regression checks for the exact immediate children selected at SSZ proof Level 2."""

from __future__ import annotations

import json
import sys
from pathlib import Path


EXPECTED_IDS = {
    "fi:1:31b", "fi:1:3c7", "fi:1:57d", "fi:2:3115", "fi:2:4054", "fi:2:407d",
    "fi:2:40a6", "fi:2:40cf", "fi:2:40f8", "fi:2:4121", "fi:2:414a", "fi:2:4173",
    "fi:2:419c", "fi:2:43b5", "fi:2:43f3", "fi:2:441c", "fi:2:457c", "fi:2:45d2",
    "fi:2:461c", "fi:2:4639", "fi:2:487e", "fi:2:4ca3",
}

LEVEL1_IDS = {"fi:1:510", "fi:1:39b", "fi:2:30e9", "fi:2:3ee7", "fi:2:4028", "fi:2:4c86"}


def main() -> int:
    manifest = json.loads(Path(sys.argv[1]).read_text())
    rows = manifest["instances"]
    assert manifest["schemaVersion"] == 1
    assert manifest["level"] == 2
    assert manifest["artifact"]["sha256"]
    assert {row["id"] for row in rows} == EXPECTED_IDS
    assert len(rows) == len(EXPECTED_IDS)
    for row in rows:
        assert row["parentInstanceIds"]
        assert set(row["parentInstanceIds"]) <= LEVEL1_IDS
        assert row["entryPc"] in row["executionPcs"]
        assert row["ownedInstructionCount"] == len(row["instructionPcs"])
        assert row["subtreeInstructionCount"] == len(row["executionPcs"])
        assert set(row["instructionPcs"]) <= set(row["executionPcs"])
    by_id = {row["id"]: row for row in rows}
    assert by_id["fi:1:31b"]["qualified"] == "memcpy"
    assert by_id["fi:1:3c7"]["exitPcs"] == [66000]
    assert by_id["fi:2:3115"]["qualified"] == "ssz.decode"
    assert by_id["fi:2:3115"]["parentInstanceIds"] == ["fi:2:30e9"]
    assert 85244 in by_id["fi:2:3115"]["exitPcs"]
    assert 88520 in by_id["fi:2:457c"]["exitPcs"]
    assert by_id["fi:2:4ca3"]["parentInstanceIds"] == ["fi:2:4c86"]
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
