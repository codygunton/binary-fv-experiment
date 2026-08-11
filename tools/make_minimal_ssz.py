#!/usr/bin/env python3
"""Write the minimal Amsterdam StatelessInput shared by Zesu and EVM-Sail smoke tests."""

import argparse
from pathlib import Path


def put_int(data: bytearray, offset: int, width: int, value: int) -> None:
    data[offset:offset + width] = value.to_bytes(width, "little")


def minimal_input() -> bytearray:
    data = bytearray(666)
    data[0:2] = bytes((0x15, 0x01))
    for offset, value in (
        (2, 16), (6, 620), (10, 632), (14, 664), (18, 44), (22, 584), (58, 584),
        (498, 540), (566, 540), (570, 540), (590, 540),
    ):
        put_int(data, offset, 4, value)
    for offset in (602, 606, 610, 614, 618):
        put_int(data, offset, 4, 20)
    for offset in (622, 626, 630):
        put_int(data, offset, 4, 12)
    put_int(data, 634, 8, 1)
    for offset, value in ((642, 12), (646, 4), (650, 8), (654, 16)):
        put_int(data, offset, 4, value)
    return data


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--mutation", choices=("invalid-schema", "block-number"))
    args = parser.parse_args()
    data = minimal_input()
    if args.mutation == "invalid-schema":
        data[1] = 0xFF
    elif args.mutation == "block-number":
        # schema prefix + top-level fixed region + request fixed region + payload field offset
        data[2 + 16 + 44 + 404] = 1
    args.output.write_bytes(data)


if __name__ == "__main__":
    main()
