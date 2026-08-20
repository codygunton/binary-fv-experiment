#!/usr/bin/env python3
"""Validate the Level 3 manifest selected below the unresolved Level 2 contracts."""

import argparse
import json
from pathlib import Path


def validate(manifest: dict, targets: dict) -> None:
    assert manifest["level"] == 3
    rows = manifest["instances"]
    assert len(rows) == 60
    target_ids = {row["instanceId"] for row in targets["targets"]}
    selected = [row for row in rows if set(row["parentInstanceIds"]) & target_ids]
    assert len(selected) == 58
    assert len({row["id"] for row in selected}) == 58
    assert all(set(row["parentInstanceIds"]) & target_ids for row in selected)
    assert any(row["qualified"] == "ssz.decodeByteListList" for row in selected)
    assert any(row["qualified"] == "rlp_decode.decodeSingleTx" for row in selected)
    assert any(row["qualified"] == "extern_io.write_output" for row in selected)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("targets", type=Path)
    args = parser.parse_args()
    validate(json.loads(args.manifest.read_text()), json.loads(args.targets.read_text()))
