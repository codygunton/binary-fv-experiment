#!/usr/bin/env python3
"""Write the minimal Amsterdam StatelessInput shared by Zesu and EVM-Sail smoke tests."""

import argparse
from pathlib import Path


def put_int(data: bytearray, offset: int, width: int, value: int) -> None:
    data[offset:offset + width] = value.to_bytes(width, "little")


def rlp_bytes(value: bytes) -> bytes:
    if len(value) == 1 and value[0] < 0x80:
        return value
    if len(value) <= 55:
        return bytes((0x80 + len(value),)) + value
    raise ValueError("fixture RLP byte string is too large")


def rlp_list(items: list[bytes]) -> bytes:
    payload = b"".join(items)
    if len(payload) <= 55:
        return bytes((0xC0 + len(payload),)) + payload
    raise ValueError("fixture RLP list is too large")


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


def activation_timestamp_input() -> bytearray:
    data = minimal_input()
    put_int(data, 14, 4, 672)
    data.extend((1).to_bytes(8, "little"))
    return data


def blob_transaction_input() -> bytearray:
    data = minimal_input()
    empty = rlp_bytes(b"")
    transaction = bytes((3,)) + rlp_list([
        empty, empty, empty, empty, empty, empty, empty, empty,
        rlp_list([]), empty, rlp_list([rlp_bytes(bytes((1,)) + bytes(31))]),
        empty, empty, empty,
    ])
    encoded = (4).to_bytes(4, "little") + transaction
    added = len(encoded)
    for offset in (6, 10, 14, 22, 58):
        put_int(data, offset, 4, int.from_bytes(data[offset:offset + 4], "little") + added)
    put_int(data, 570, 4, 540 + added)
    put_int(data, 590, 4, 540 + added)
    data[602:602] = encoded
    return data


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--mutation",
        choices=("invalid-schema", "block-number", "chain-id-zero", "legacy-requests",
                 "legacy-payload", "future-activation", "extra-data-33",
                 "public-key-overflow", "versioned-hash-overflow",
                 "one-transaction", "one-withdrawal", "activation-timestamp",
                 "blob-transaction"),
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
    elif args.mutation == "public-key-overflow":
        data.extend((b"\x04" + bytes(64)) * (2 ** 15 + 1))
    elif args.mutation == "versioned-hash-overflow":
        added = 32 * (2 ** 12 + 1)
        put_int(data, 6, 4, 620 + added)
        put_int(data, 10, 4, 632 + added)
        put_int(data, 14, 4, 664 + added)
        put_int(data, 58, 4, 584 + added)
        data[602:602] = bytes(added)
    elif args.mutation == "one-transaction":
        # One SSZ ByteList element containing a minimal nine-field legacy RLP transaction.
        transaction = bytes.fromhex("c9808080808080808080")
        encoded = (4).to_bytes(4, "little") + transaction
        added = len(encoded)
        for offset in (6, 10, 14):
            put_int(data, offset, 4, int.from_bytes(data[offset:offset + 4], "little") + added)
        for offset in (22, 58):
            put_int(data, offset, 4, int.from_bytes(data[offset:offset + 4], "little") + added)
        put_int(data, 570, 4, 540 + added)
        put_int(data, 590, 4, 540 + added)
        data[602:602] = encoded
    elif args.mutation == "one-withdrawal":
        # One packed 44-byte SszWithdrawal with distinct little-endian fields.
        withdrawal = bytearray(44)
        put_int(withdrawal, 0, 8, 1)
        put_int(withdrawal, 8, 8, 2)
        withdrawal[16:36] = bytes(range(1, 21))
        put_int(withdrawal, 36, 8, 3)
        added = len(withdrawal)
        for offset in (6, 10, 14):
            put_int(data, offset, 4, int.from_bytes(data[offset:offset + 4], "little") + added)
        for offset in (22, 58):
            put_int(data, offset, 4, int.from_bytes(data[offset:offset + 4], "little") + added)
        put_int(data, 590, 4, 540 + added)
        data[602:602] = withdrawal
    elif args.mutation == "activation-timestamp":
        # Extend SszForkActivation with one timestamp value at activation offset 16.
        data = activation_timestamp_input()
    elif args.mutation == "blob-transaction":
        # One EIP-4844 transaction with one versioned hash exercises Encoder.raw in its loop.
        data = blob_transaction_input()
    args.output.write_bytes(data)


if __name__ == "__main__":
    main()
