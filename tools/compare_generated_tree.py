#!/usr/bin/env python3
"""Compare a committed generated-source tree with a regenerated tree."""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path


IGNORED_PARTS = frozenset({".git", ".lake", "__pycache__"})


SAIL_EXISTENTIAL = re.compile(rb"\bk_ex[0-9]+_")


def normalize_sail_existentials(content: bytes) -> bytes:
    """Rename unstable Sail-generated existential identifiers by first occurrence."""
    names: dict[bytes, bytes] = {}

    def replace(match: re.Match[bytes]) -> bytes:
        name = match.group(0)
        if name not in names:
            names[name] = f"k_ex{len(names)}_".encode()
        return names[name]

    return SAIL_EXISTENTIAL.sub(replace, content)


def tree_files(root: Path, normalize_existentials: bool = False) -> dict[str, str]:
    """Return the SHA-256 digest for each checked file below ``root``."""
    result: dict[str, str] = {}
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if any(part in IGNORED_PARTS for part in relative.parts):
            continue
        if path.is_file():
            content = path.read_bytes()
            if normalize_existentials and path.suffix == ".lean":
                content = normalize_sail_existentials(content)
            result[relative.as_posix()] = hashlib.sha256(content).hexdigest()
    return result


def differences(expected: Path, actual: Path, normalize_existentials: bool = False) -> list[str]:
    expected_files = tree_files(expected, normalize_existentials)
    actual_files = tree_files(actual, normalize_existentials)
    messages = [f"missing: {name}" for name in sorted(expected_files.keys() - actual_files.keys())]
    messages.extend(f"extra: {name}" for name in sorted(actual_files.keys() - expected_files.keys()))
    messages.extend(
        f"changed: {name}"
        for name in sorted(expected_files.keys() & actual_files.keys())
        if expected_files[name] != actual_files[name]
    )
    return messages


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("expected", type=Path)
    parser.add_argument("actual", type=Path)
    parser.add_argument("--normalize-sail-existentials", action="store_true")
    args = parser.parse_args()
    messages = differences(args.expected, args.actual, args.normalize_sail_existentials)
    if messages:
        print("Generated source differs from the committed snapshot:")
        for message in messages:
            print(message)
        return 1
    print("Generated source matches the committed snapshot.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
