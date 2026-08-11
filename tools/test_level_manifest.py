#!/usr/bin/env python3
"""Regression checks for the authoritative SSZ Level 1 manifest."""

from __future__ import annotations

import json
import sys
from pathlib import Path


EXPECTED = {
    "alt_fl_alloc.get",
    "ssz.decode",
    "read_input",
    "zkvm_exit",
    "memcpy",
    "ssz_decode_observation.writeSuccess",
    "ssz_decode_observation.writeFailure",
}


def main() -> int:
    manifest = json.loads(Path(sys.argv[1]).read_text())
    rows = manifest["instances"]
    assert manifest["schemaVersion"] == 1
    assert manifest["level"] == 1
    assert manifest["artifact"]["sha256"]
    assert len(rows) == len(EXPECTED)
    assert {row["qualified"] for row in rows} == EXPECTED
    assert len({row["id"] for row in rows}) == len(rows)
    for row in rows:
        identity = row["functionInstanceIdentity"]
        assert identity["function"]["declaration"]["qualifiedName"] == row["qualified"]
        assert not identity["function"]["declaration"]["file"].startswith("/nix/store/")
        assert row["ownedInstructionCount"] == len(row["instructionPcs"])
        assert row["subtreeInstructionCount"] >= row["ownedInstructionCount"]
        assert row["subtreeInstructionCount"] == len(row["executionPcs"])
        assert set(row["instructionPcs"]) <= set(row["executionPcs"])
        assert row["entryPc"] in row["executionPcs"]
    by_name = {row["qualified"]: row for row in rows}
    allocator = by_name["alt_fl_alloc.get"]
    assert len(allocator["absorbedInstructionPcs"]) == 3
    assert allocator["exitPcs"] == [74208]
    decode = by_name["ssz.decode"]
    assert len(decode["absorbedInstructionPcs"]) == 50
    assert decode["exitPcs"] == [74688, 83360]
    assert by_name["zkvm_exit"]["exitPcs"] == [66000]
    assert by_name["ssz_decode_observation.writeSuccess"]["exitPcs"] == [83720]
    assert by_name["ssz_decode_observation.writeFailure"]["exitPcs"] == [74696]
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
