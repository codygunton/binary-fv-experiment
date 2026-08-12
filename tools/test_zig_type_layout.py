#!/usr/bin/env python3
"""Validate the top-level StatelessInput layout needed by the machine contract."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def validate(document: dict) -> None:
    root = next(row for row in document["types"] if row["id"] == document["rootType"])
    if root["name"] != "input.StatelessInput" or root["byteSize"] != 848 or root["alignment"] != 8:
        raise ValueError("unexpected input.StatelessInput size or alignment")
    offsets = {member["name"]: member["offset"] for member in root["members"]}
    expected = {"new_payload_request": 0, "witness": 720,
                "chain_config": 768, "public_keys": 832}
    if offsets != expected:
        raise ValueError("unexpected input.StatelessInput member layout")
    ids = {row["id"] for row in document["types"]}
    if any(member["type"] not in ids for row in document["types"] for member in row["members"]):
        raise ValueError("layout graph contains a dangling member type")


def main() -> int:
    document = json.loads(Path(sys.argv[1]).read_text())
    validate(document)
    root = next(row for row in document["types"] if row["id"] == document["rootType"])
    root["members"][1]["offset"] += 8
    try:
        validate(document)
    except ValueError:
        return 0
    raise AssertionError("validator accepted a forged StatelessInput member offset")


if __name__ == "__main__":
    raise SystemExit(main())
