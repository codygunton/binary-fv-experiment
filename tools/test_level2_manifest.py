#!/usr/bin/env python3
"""Regression checks for the source-identified Level 2 selection."""

from collections import Counter
import json
import sys
from pathlib import Path


EXPECTED = Counter({
    "ssz_decode_observation.Encoder.raw": 10,
    "memcpy": 1,
    "ssz.decode": 1,
    "ssz_decode_observation.Encoder.transactions": 1,
    "ssz_decode_observation.Encoder.withdrawals": 1,
    "ssz_decode_observation.Encoder.hashes": 1,
    "ssz_decode_observation.Encoder.boolean": 1,
    "ssz_decode_observation.Encoder.optionalU64": 1,
    "ssz_decode_observation.Encoder.byteLists": 1,
    "ssz_decode_observation.Encoder.bytes": 1,
    "ssz_decode_observation.Encoder.int__anon_1525": 1,
})


def main() -> int:
    manifest = json.loads(Path(sys.argv[1]).read_text())
    rows = manifest["instances"]
    assert manifest["schemaVersion"] == 1
    assert manifest["level"] == 2
    assert manifest["artifact"]["sha256"]
    assert Counter(row["qualified"] for row in rows) == EXPECTED
    identities = [json.dumps(row["functionInstanceIdentity"], sort_keys=True) for row in rows]
    assert len(identities) == len(set(identities))
    for row in rows:
        assert row["parentInstanceIds"]
        assert row["entryPc"] in row["executionPcs"]
        assert row["ownedInstructionCount"] == len(row["instructionPcs"])
        assert row["subtreeInstructionCount"] == len(row["executionPcs"])
        assert set(row["instructionPcs"]) <= set(row["executionPcs"])
    memcpy = next(row for row in rows if row["qualified"] == "memcpy")
    assert len(memcpy["parentInstanceIds"]) == 2
    decode = next(row for row in rows if row["qualified"] == "ssz.decode")
    assert len(decode["parentInstanceIds"]) == 1
    assert 85244 in decode["exitPcs"]
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
