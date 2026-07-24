#!/usr/bin/env python3
"""Row C: the EXPECTED allocation sequence of a production fixture, derived independently of the ELF.

`allocationLedger` used to say only "the cursor moved forward, inside the heap, by a positive amount".
That accepts an extra allocation, a wrong block size, a skipped alignment step, or a reordering — every
defect the ledger exists to catch. This module supplies the other side of the comparison: for the exact
bytes fed to the process, the ordered list of allocations the decoder MUST perform, with each event's
size and alignment, computed without looking at the binary at all.

Two independent inputs, mirroring Row B's `ledger_of`:

  * the **allocation shape** of each routine — which element type it allocates, how many, and in what
    order relative to its siblings — taken from the pinned Zig source's decode order (`ssz_raw.zig`);
  * the **element ABI** — `@sizeOf` / `@alignOf` of each allocated element type — taken from the Row B
    probe's `--dump-abi`, i.e. from the real Zig compiler, not from anything this file believes.

The counts come from parsing the fixture's SSZ layout here, so a fixture change is picked up
automatically and a wrong count is not something the checker can absorb.

The parse mirrors `ssz_raw.zig`'s validation closely enough to stop where the decoder stops: a rejected
payload allocates only what it managed to allocate before the rejection (the `malformed` arm relies on
this). Every allocating call site carries the Zig routine chain that reaches it, so an observed event
can be attributed to the function instances that own it.

Diagnostic-only; never imported by the theorem graph.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

# Element type -> the `--dump-abi` key naming it. `alloc(T, n)` requests `n * @sizeOf(T)` bytes at
# `@alignOf(T)`; a count of 0 allocates nothing (Zig's `alloc(T, 0)` never reaches `rawAlloc`).
ELEM_HASH32 = "hash32"
ELEM_PUBKEY = "pubkey65"
ELEM_WITHDRAWAL = "withdrawal"
ELEM_DEPOSIT = "deposit"
ELEM_WITHDRAWAL_REQ = "withdrawalReq"
ELEM_CONSOLIDATION = "consolidation"
ELEM_SLICE_U8 = "sliceU8"

# Every allocation reaches the bump allocator through the std.mem.Allocator vtable slot and the raw
# runtime entry, so both appear at the tail of each event's routine chain (which is what lets the two
# allocator-leaf function instances claim the same events as the collection that requested them).
ALLOCATOR_CHAIN = ("allocatorAlloc", "zesu_raw_alloc")
DECODE_CHAIN = ("zesu_decode_raw", "decode", "decodeRaw")

CONST_RE = re.compile(r"^\s*(?:pub\s+)?const\s+(\w+)\s*:\s*\w+\s*=\s*"
                      r"(?:(\d+)|1\s*<<\s*(\d+))\s*;", re.M)


class Rejected(Exception):
    """The pinned decoder rejects this payload here; nothing further is allocated."""


def pinned_constants(ssz_raw_zig: str) -> dict[str, int]:
    """The `const NAME: T = <int>|1 << k;` table of the pinned decoder source."""
    out = {}
    for m in CONST_RE.finditer(ssz_raw_zig):
        out[m.group(1)] = int(m.group(2)) if m.group(2) is not None else 1 << int(m.group(3))
    return out


class ShapeWalk:
    """Walks the pinned V4 layout of one payload, recording the allocations it implies."""

    def __init__(self, consts: dict[str, int], abi: dict[str, dict]):
        self.c = consts
        self.abi = abi
        self.events: list[dict] = []

    # ---- primitives, mirroring ssz_raw.zig ------------------------------------------------------
    def _u32(self, data: bytes, offset: int) -> int:
        if offset > len(data) or offset + 4 > len(data):
            raise Rejected("readU32 out of range")
        return int.from_bytes(data[offset:offset + 4], "little")

    def _u64(self, data: bytes, offset: int) -> int:
        if offset > len(data) or offset + 8 > len(data):
            raise Rejected("readU64 out of range")
        return int.from_bytes(data[offset:offset + 8], "little")

    def _canonical(self, data: bytes, fixed_size: int, offsets: list[int]) -> None:
        if len(data) < fixed_size or not offsets or offsets[0] != fixed_size:
            raise Rejected("requireCanonicalOffsets")
        previous = fixed_size
        for off in offsets:
            if off < previous or off > len(data):
                raise Rejected("requireCanonicalOffsets")
            previous = off

    def _alloc(self, path: tuple[str, ...], elem: str, count: int) -> None:
        """One `alloc(T, count)` at the end of the routine chain `path`. Count 0 allocates nothing."""
        if count <= 0:
            return
        spec = self.abi[elem]
        self.events.append({
            "ordinal": len(self.events),
            "routinePath": list(path + ALLOCATOR_CHAIN),
            "routine": path[-1],
            "element": elem,
            "count": count,
            "size": count * spec["size"],
            "alignment": spec["align"],
        })

    # ---- the decode tree ------------------------------------------------------------------------
    def decode_raw(self, data: bytes) -> None:
        p = DECODE_CHAIN
        if len(data) < 2 or data[0:2] != b"\x00\x01":
            raise Rejected("schema id")
        body = data[2:]
        if len(body) < self.c["TOP_FIXED_SIZE"]:
            raise Rejected("top fixed size")
        offsets = [self._u32(body, 0), self._u32(body, 4), self._u32(body, 8), self._u32(body, 12)]
        self._canonical(body, self.c["TOP_FIXED_SIZE"], offsets)
        self.new_payload_request(p + ("decodeNewPayloadRequest",), body[offsets[0]:offsets[1]])
        self.execution_witness(p + ("decodeExecutionWitness",), body[offsets[1]:offsets[2]])
        self.chain_config(body[offsets[2]:offsets[3]])
        self.public_keys(p + ("decodePublicKeys",), body[offsets[3]:])

    def new_payload_request(self, p: tuple[str, ...], data: bytes) -> None:
        if len(data) < self.c["NPR_FIXED_SIZE"]:
            raise Rejected("npr fixed size")
        offsets = [self._u32(data, 0), self._u32(data, 4), self._u32(data, 40)]
        self._canonical(data, self.c["NPR_FIXED_SIZE"], offsets)
        self.execution_payload(p + ("decodeExecutionPayload",), data[offsets[0]:offsets[1]])
        self.versioned_hashes(p + ("decodeVersionedHashes",), data[offsets[1]:offsets[2]])
        self.execution_requests(p + ("decodeExecutionRequests",), data[offsets[2]:])

    def execution_payload(self, p: tuple[str, ...], data: bytes) -> None:
        fixed = self.c["EXECUTION_PAYLOAD_FIXED_SIZE"]
        if len(data) < fixed:
            raise Rejected("payload fixed size")
        offsets = [self._u32(data, 436), self._u32(data, 504), self._u32(data, 508),
                   self._u32(data, 528)]
        self._canonical(data, fixed, offsets)
        extra = data[offsets[0]:offsets[1]]
        bal = data[offsets[3]:]
        if len(extra) > self.c["MAX_EXTRA_DATA_BYTES"] or len(bal) > self.c["MAX_BYTES_PER_TRANSACTION"]:
            raise Rejected("extra data / block access list limit")
        self.byte_list_list(p + ("decodeByteListList",), data[offsets[1]:offsets[2]],
                            self.c["MAX_TRANSACTIONS_PER_PAYLOAD"], self.c["MAX_BYTES_PER_TRANSACTION"])
        self.fixed_stride(p + ("decodeWithdrawals",), data[offsets[2]:offsets[3]],
                          self.c["WITHDRAWAL_SIZE"], self.c["MAX_WITHDRAWALS_PER_PAYLOAD"],
                          ELEM_WITHDRAWAL)

    def versioned_hashes(self, p: tuple[str, ...], data: bytes) -> None:
        self.fixed_stride(p, data, 32, self.c["MAX_BLOB_COMMITMENTS_PER_BLOCK"], ELEM_HASH32)

    def execution_requests(self, p: tuple[str, ...], data: bytes) -> None:
        fixed = self.c["EXECUTION_REQUESTS_FIXED_SIZE"]
        if len(data) < fixed:
            raise Rejected("execution requests fixed size")
        offsets = [self._u32(data, 0), self._u32(data, 4), self._u32(data, 8)]
        self._canonical(data, fixed, offsets)
        self.fixed_stride(p + ("decodeDepositRequests",), data[offsets[0]:offsets[1]],
                          self.c["DEPOSIT_REQUEST_SIZE"],
                          self.c["MAX_DEPOSIT_REQUESTS_PER_PAYLOAD"], ELEM_DEPOSIT)
        self.fixed_stride(p + ("decodeWithdrawalRequests",), data[offsets[1]:offsets[2]],
                          self.c["WITHDRAWAL_REQUEST_SIZE"],
                          self.c["MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD"], ELEM_WITHDRAWAL_REQ)
        self.fixed_stride(p + ("decodeConsolidationRequests",), data[offsets[2]:],
                          self.c["CONSOLIDATION_REQUEST_SIZE"],
                          self.c["MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD"], ELEM_CONSOLIDATION)

    def execution_witness(self, p: tuple[str, ...], data: bytes) -> None:
        fixed = self.c["WITNESS_FIXED_SIZE"]
        if len(data) < fixed:
            raise Rejected("witness fixed size")
        offsets = [self._u32(data, 0), self._u32(data, 4), self._u32(data, 8)]
        self._canonical(data, fixed, offsets)
        q = p + ("decodeByteListList",)
        self.byte_list_list(q, data[offsets[0]:offsets[1]],
                            self.c["MAX_WITNESS_NODES"], self.c["MAX_BYTES_PER_WITNESS_NODE"])
        self.byte_list_list(q, data[offsets[1]:offsets[2]],
                            self.c["MAX_WITNESS_CODES"], self.c["MAX_BYTES_PER_CODE"])
        self.byte_list_list(q, data[offsets[2]:],
                            self.c["MAX_WITNESS_HEADERS"], self.c["MAX_BYTES_PER_HEADER"])

    def chain_config(self, data: bytes) -> None:
        """Non-allocating, but it can REJECT, which ends the sequence (the `malformed` arm)."""
        fixed = self.c["CHAIN_CONFIG_FIXED_SIZE"]
        if len(data) < fixed:
            raise Rejected("chain config fixed size")
        active = self._u32(data, 8)
        self._canonical(data, fixed, [active])
        fork_data = data[active:]
        if len(fork_data) < self.c["FORK_CONFIG_FIXED_SIZE"]:
            raise Rejected("fork config fixed size")
        offsets = [self._u32(fork_data, 8), self._u32(fork_data, 12)]
        self._canonical(fork_data, self.c["FORK_CONFIG_FIXED_SIZE"], offsets)
        if self._u64(fork_data, 0) > self.c["LAST_PROTOCOL_FORK_INDEX"]:
            raise Rejected("unknown fork")
        act = fork_data[offsets[0]:offsets[1]]
        if len(act) < self.c["FORK_ACTIVATION_FIXED_SIZE"]:
            raise Rejected("fork activation fixed size")
        act_offsets = [self._u32(act, 0), self._u32(act, 4)]
        self._canonical(act, self.c["FORK_ACTIVATION_FIXED_SIZE"], act_offsets)
        for opt in (act[act_offsets[0]:act_offsets[1]], act[act_offsets[1]:]):
            if len(opt) not in (0, 8):
                raise Rejected("optional u64 length")
        blob = fork_data[offsets[1]:]
        if len(blob) not in (0, self.c["BLOB_SCHEDULE_SIZE"]):
            raise Rejected("optional blob schedule length")

    def public_keys(self, p: tuple[str, ...], data: bytes) -> None:
        self.fixed_stride(p, data, self.c["PUBLIC_KEY_SIZE"], self.c["MAX_PUBLIC_KEYS"], ELEM_PUBKEY)

    # ---- the two collection shapes --------------------------------------------------------------
    def fixed_stride(self, p: tuple[str, ...], data: bytes, stride: int, max_items: int,
                     elem: str) -> None:
        """`decodeWithdrawals` / `decodeVersionedHashes` / the three request lists / `decodePublicKeys`:
        a stride-divisible byte range allocating exactly one block of `len/stride` elements."""
        if len(data) % stride != 0:
            raise Rejected(f"{p[-1]}: length not a multiple of {stride}")
        count = len(data) // stride
        if count > max_items:
            raise Rejected(f"{p[-1]}: {count} exceeds {max_items}")
        self._alloc(p, elem, count)

    def byte_list_list(self, p: tuple[str, ...], data: bytes, max_items: int,
                       max_item_bytes: int) -> None:
        """`decodeByteListList`: one `[]const u8` block of `first_offset / 4` items. An EMPTY list takes
        the `alloc(T, 0)` path, which allocates nothing."""
        if len(data) == 0:
            return
        if len(data) < 4:
            raise Rejected("byte list list: shorter than one offset")
        first = self._u32(data, 0)
        if first == 0 or first % 4 != 0 or first > len(data):
            raise Rejected("byte list list: bad first offset")
        count = first // 4
        if count > max_items:
            raise Rejected(f"byte list list: {count} exceeds {max_items}")
        self._alloc(p, ELEM_SLICE_U8, count)
        previous = first
        for index in range(count):
            start = self._u32(data, index * 4)
            end = self._u32(data, (index + 1) * 4) if index + 1 < count else len(data)
            if start < previous or end < start or end > len(data) or end - start > max_item_bytes:
                raise Rejected("byte list list: non-canonical item offsets")
            previous = start


def expected_allocations(payload: bytes, consts: dict[str, int], abi: dict[str, dict]) -> dict:
    """The ordered allocation events the pinned decoder performs on `payload`.

    `decode` retries `decodeRaw` on a stripped exact-ERE prefix only when the raw parse fails with
    `InvalidSsz` AND the leading u32 equals `len - 4`; the retry starts a fresh sequence because the
    first attempt's blocks are all freed by its `errdefer` chain (a bump allocator's free is a no-op,
    so the retry's blocks simply follow — which is why the retried events are appended, not replaced)."""
    walk = ShapeWalk(consts, abi)
    try:
        walk.decode_raw(payload)
        return {"events": walk.events, "rejectedAt": None, "retried": False}
    except Rejected as first:
        rejected_at = str(first)
    retried = (len(payload) >= 4
               and int.from_bytes(payload[0:4], "little") == len(payload) - 4)
    if not retried:
        return {"events": walk.events, "rejectedAt": rejected_at, "retried": False}
    try:
        walk.decode_raw(payload[4:])
        return {"events": walk.events, "rejectedAt": None, "retried": True}
    except Rejected as second:
        return {"events": walk.events, "rejectedAt": str(second), "retried": True}


def load_inputs(source_root: str, abi_path: str) -> tuple[dict[str, int], dict[str, dict]]:
    """The pinned decoder constants and the Row B element ABI table."""
    zig = Path(source_root, "src/stateless/stateless/ssz_raw.zig").read_text()
    return pinned_constants(zig), json.loads(Path(abi_path).read_text())


def align_up(value: int, alignment: int) -> int:
    return value if alignment <= 1 else ((value + alignment - 1) // alignment) * alignment
