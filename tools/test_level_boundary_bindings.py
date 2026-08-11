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
    if len(rows) != 7:
        raise ValueError("boundary report must contain the exact seven Level 1 instances")
    expected = {
        "read_input": {"buffer": 10, "size": 11},
        "zkvm_exit": {"code": 10},
        "memcpy": {"dst": 10, "src": 11, "n": 12},
    }
    for qualified, bindings in expected.items():
        actual = register_map(rows[qualified])
        for name, register in bindings.items():
            if actual.get(name) != register:
                raise ValueError(f"{qualified}.{name} must be live in x{register}")
    decode = register_map(rows["ssz.decode"])
    if decode.get("input_ptr") != 23 or decode.get("input_size") != 18:
        raise ValueError("ssz.decode input_ptr/input_size must be live in x23/x18")
    if decode.get("alloc") is not None:
        raise ValueError("the optimized ssz.decode allocator is not a direct register binding")


def main() -> int:
    report = json.loads(Path(sys.argv[1]).read_text())
    validate(report)
    mutated = json.loads(json.dumps(report))
    decode = next(row for row in mutated["instances"] if row["qualified"] == "ssz.decode")
    next(row for row in decode["bindings"] if row["name"] == "input_ptr")["machineRegister"] = 10
    try:
        validate(mutated)
    except ValueError:
        return 0
    raise AssertionError("validator accepted a forged optimized input register")


if __name__ == "__main__":
    raise SystemExit(main())
