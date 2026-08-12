#!/usr/bin/env python3
"""Validate the Level 1 DWARF boundary bindings used for contract admission."""

from __future__ import annotations

import json
import sys
from pathlib import Path


def register_map(instance: dict) -> dict[str, int | None]:
    return {row["name"]: row["machineRegister"] for row in instance["bindings"]}


def validate(report: dict) -> None:
    rows = {row["qualified"]: row for row in report["instances"]}
    if len(rows) != 6:
        raise ValueError("boundary report must contain the exact six Level 1 instances")
    expected = {
        "read_input": {"buffer": 10, "size": 11},
        "zkvm_exit": {"code": 10},
    }
    for qualified, bindings in expected.items():
        actual = register_map(rows[qualified])
        for name, register in bindings.items():
            if actual.get(name) != register:
                raise ValueError(f"{qualified}.{name} must be live in x{register}")
    decode = {row["name"]: row for row in rows["ssz_decode_root.decodeInput"]["bindings"]}
    if decode["alloc"]["addressRegister"] != 11:
        raise ValueError("decodeInput allocator descriptor must be addressed by x11")
    success = {row["name"]: row
               for row in rows["ssz_decode_observation.writeSuccess"]["bindings"]}
    if success["decoded"]["addressRegister"] != 10:
        raise ValueError("writeSuccess decoded value must be addressed by x10")


def main() -> int:
    report = json.loads(Path(sys.argv[1]).read_text())
    validate(report)
    mutated = json.loads(json.dumps(report))
    decode = next(row for row in mutated["instances"]
                  if row["qualified"] == "ssz_decode_root.decodeInput")
    next(row for row in decode["bindings"] if row["name"] == "alloc")["addressRegister"] = 10
    try:
        validate(mutated)
    except ValueError:
        pass
    else:
        raise AssertionError("validator accepted a forged decode allocator register")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
