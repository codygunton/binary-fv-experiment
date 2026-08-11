#!/usr/bin/env python3
"""Validate and render the four direct decodeRaw/readOffset occurrence parameters."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Occurrence:
    site: int
    owner: str
    offset: int
    result: str
    final_pair: tuple[str, str]
    fragments: tuple[tuple[int, int, int], ...]


OCCURRENCES = (
    Occurrence(199, "fi:9", 2, "x23/s7", ("x10/a0", "x12/a2"),
               ((0x10534, 0x10540, 0x10544), (0x10554, 0x10564, 0x10568))),
    Occurrence(200, "fi:11", 6, "x25/s9", ("x14/a4", "x15/a5"),
               ((0x10544, 0x10550, 0x10554), (0x10578, 0x10580, 0x10584),
                (0x10590, 0x10594, 0x10598))),
    Occurrence(201, "fi:13", 10, "x24/s8", ("x11/a1", "x13/a3"),
               ((0x10568, 0x10574, 0x10578), (0x10584, 0x1058C, 0x10590),
                (0x10598, 0x1059C, 0x105A0))),
    Occurrence(202, "fi:15", 14, "x19/s3", ("x16/a6", "x17/a7"),
               ((0x105A0, 0x105C0, 0x105C4),)),
)


def instructions_for(occurrence: Occurrence, instructions: list[dict]) -> list[dict]:
    return [instruction for instruction in instructions if instruction["owner"] == occurrence.owner]


def validate(occurrence: Occurrence, owned: list[dict]) -> None:
    addresses = {instruction["address"] for instruction in owned}
    expected = {
        address
        for start, source, _successor in occurrence.fragments
        for address in range(start, source + 1, 4)
    }
    final_pc = 0x105C4 + 4 * (occurrence.site - 199)
    expected.add(final_pc)
    if addresses != expected:
        raise SystemExit(
            f"site {occurrence.site}: schedule/owner mismatch; "
            f"missing={sorted(expected-addresses)}, extra={sorted(addresses-expected)}"
        )
    if len(owned) != 10:
        raise SystemExit(f"site {occurrence.site}: expected 10 owned instructions, got {len(owned)}")
    if owned[-1]["mnemonic"] != "or":
        raise SystemExit(f"site {occurrence.site}: final instruction is not or")


def render_markdown(instructions: list[dict]) -> str:
    lines = [
        "| site | offset | owner | fragments | owned words | final pair | result | final PC |",
        "|---:|---:|---|---:|---:|---|---|---:|",
    ]
    for occurrence in OCCURRENCES:
        owned = instructions_for(occurrence, instructions)
        validate(occurrence, owned)
        lines.append(
            f"| {occurrence.site}:23 | {occurrence.offset} | `{occurrence.owner}` | "
            f"{len(occurrence.fragments)} | {len(owned)} | "
            f"`{occurrence.final_pair[0]}`, `{occurrence.final_pair[1]}` | "
            f"`{occurrence.result}` | `0x{owned[-1]['address']:x}` |"
        )
    return "\n".join(lines)


def render_lean() -> str:
    lines = ["-- Generated skeleton: inputs are source-derived FunctionInstance identifiers."]
    for occurrence in OCCURRENCES:
        lines.extend([
            f"def readOffset{occurrence.site}Interface :=",
            f"  readOffsetInlineInterface "
            f"functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_{occurrence.site}_23",
            f"def readOffset{occurrence.site}Fragments : List (Nat × Nat × Nat) :=",
            "  [" + ", ".join(
                f"(0x{start:x}, 0x{source:x}, 0x{successor:x})"
                for start, source, successor in occurrence.fragments
            ) + "]",
        ])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--machine-regions", type=Path,
                        default=Path("build/machine-regions-lean/machine-regions.json"))
    parser.add_argument("--format", choices=("markdown", "lean"), default="markdown")
    args = parser.parse_args()
    instructions = json.loads(args.machine_regions.read_text())["instructions"]
    print(render_markdown(instructions) if args.format == "markdown" else render_lean())


if __name__ == "__main__":
    main()
