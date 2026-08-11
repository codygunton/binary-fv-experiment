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
    parser.add_argument(
        "--mutation",
        choices=("invalid-schema", "block-number", "chain-id-zero", "legacy-requests",
                 "legacy-payload", "future-activation", "extra-data-33"),
    )
    args = parser.parse_args()
    data = minimal_input()
    if args.mutation == "invalid-schema":
        data[1] = 0xFF
    elif args.mutation == "block-number":
        # schema prefix + top-level fixed region + request fixed region + payload field offset
        data[2 + 16 + 44 + 404] = 1
    elif args.mutation == "chain-id-zero":
        put_int(data, 634, 8, 0)
    elif args.mutation == "legacy-requests":
        # Remove the two v0.6.2 builder-request offsets, preserving the v0.5.0 three-field table.
        put_int(data, 6, 4, 612)
        put_int(data, 10, 4, 624)
        put_int(data, 14, 4, 656)
        for offset in (602, 606, 610):
            put_int(data, offset, 4, 12)
        del data[614:622]
    elif args.mutation == "legacy-payload":
        # Remove Amsterdam's block-access-list offset and slot number from the payload fixed region.
        put_int(data, 6, 4, 608)
        put_int(data, 10, 4, 620)
        put_int(data, 14, 4, 652)
        put_int(data, 22, 4, 572)
        put_int(data, 58, 4, 572)
        for offset in (498, 566, 570):
            put_int(data, offset, 4, 528)
        del data[590:602]
    elif args.mutation == "future-activation":
        put_int(data, 658, 8, 1)
    elif args.mutation == "extra-data-33":
        put_int(data, 6, 4, 653)
        put_int(data, 10, 4, 665)
        put_int(data, 14, 4, 697)
        put_int(data, 22, 4, 617)
        put_int(data, 58, 4, 617)
        put_int(data, 566, 4, 573)
        put_int(data, 570, 4, 573)
        put_int(data, 590, 4, 573)
        data[602:602] = bytes(range(33))
    args.output.write_bytes(data)


if __name__ == "__main__":
    main()
