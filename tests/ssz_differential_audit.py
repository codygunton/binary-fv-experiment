#!/usr/bin/env python3
"""Strict V4 full-value differential for pinned Python, Lean, and Zesu.

Each valid fixture must produce byte-identical ``ssz-value-v1`` output from
all three implementations. Each malformed V4 fixture must be rejected by all
three; error labels are intentionally not compared. V3 is deliberately absent
from the pass/fail gate because no independently pinned V3 oracle exists.
"""

from __future__ import annotations

import argparse
import hashlib
import resource
import subprocess
import sys
import tempfile
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


SCHEMA_ID = b"\x00\x01"


@dataclass(frozen=True)
class Case:
    name: str
    data: bytes
    valid: bool


@dataclass(frozen=True)
class Outcome:
    returncode: int
    stdout: bytes
    stderr: bytes


def u32(value: int) -> bytes:
    return value.to_bytes(4, "little")


def u64(value: int) -> bytes:
    return value.to_bytes(8, "little")


def u256(value: int) -> bytes:
    return value.to_bytes(32, "little")


def bytes_from(start: int, length: int) -> bytes:
    return bytes((start + index) % 256 for index in range(length))


def byte_list_list(items: Iterable[bytes]) -> bytes:
    values = tuple(items)
    if not values:
        return b""
    offset = 4 * len(values)
    offsets: list[bytes] = []
    for item in values:
        offsets.append(u32(offset))
        offset += len(item)
    return b"".join(offsets) + b"".join(values)


def withdrawal(index: int, validator_index: int, address: bytes, amount: int) -> bytes:
    assert len(address) == 20
    return u64(index) + u64(validator_index) + address + u64(amount)


def deposit_request(
    pubkey: bytes,
    withdrawal_credentials: bytes,
    amount: int,
    signature: bytes,
    index: int,
) -> bytes:
    assert len(pubkey) == 48
    assert len(withdrawal_credentials) == 32
    assert len(signature) == 96
    return pubkey + withdrawal_credentials + u64(amount) + signature + u64(index)


def withdrawal_request(source_address: bytes, validator_pubkey: bytes, amount: int) -> bytes:
    assert len(source_address) == 20
    assert len(validator_pubkey) == 48
    return source_address + validator_pubkey + u64(amount)


def consolidation_request(source_address: bytes, source_pubkey: bytes, target_pubkey: bytes) -> bytes:
    assert len(source_address) == 20
    assert len(source_pubkey) == 48
    assert len(target_pubkey) == 48
    return source_address + source_pubkey + target_pubkey


def execution_requests(
    deposits: bytes = b"", withdrawals: bytes = b"", consolidations: bytes = b""
) -> bytes:
    return (
        u32(12)
        + u32(12 + len(deposits))
        + u32(12 + len(deposits) + len(withdrawals))
        + deposits
        + withdrawals
        + consolidations
    )


def execution_payload(
    *,
    parent_hash: bytes = bytes(32),
    fee_recipient: bytes = bytes(20),
    state_root: bytes = bytes(32),
    receipts_root: bytes = bytes(32),
    logs_bloom: bytes = bytes(256),
    prev_randao: bytes = bytes(32),
    block_number: int = 0,
    gas_limit: int = 0,
    gas_used: int = 0,
    timestamp: int = 0,
    extra_data: bytes = b"extra",
    base_fee_per_gas: int = 0,
    block_hash: bytes = bytes(32),
    transactions: Iterable[bytes] = (b"\xc0", b"\x01\x02"),
    withdrawals: Iterable[bytes] = (bytes(range(44)),),
    blob_gas_used: int = 0,
    excess_blob_gas: int = 0,
    block_access_list: bytes = b"access-list",
    slot_number: int = 7,
) -> bytes:
    for value, length in (
        (parent_hash, 32),
        (fee_recipient, 20),
        (state_root, 32),
        (receipts_root, 32),
        (logs_bloom, 256),
        (prev_randao, 32),
        (block_hash, 32),
    ):
        assert len(value) == length
    withdrawals = tuple(withdrawals)
    assert all(len(value) == 44 for value in withdrawals)
    tx_data = byte_list_list(transactions)
    withdrawals_data = b"".join(withdrawals)
    fixed_size = 540
    transactions_offset = fixed_size + len(extra_data)
    withdrawals_offset = transactions_offset + len(tx_data)
    access_list_offset = withdrawals_offset + len(withdrawals_data)
    fixed = bytearray(fixed_size)
    fixed[0:32] = parent_hash
    fixed[32:52] = fee_recipient
    fixed[52:84] = state_root
    fixed[84:116] = receipts_root
    fixed[116:372] = logs_bloom
    fixed[372:404] = prev_randao
    fixed[404:412] = u64(block_number)
    fixed[412:420] = u64(gas_limit)
    fixed[420:428] = u64(gas_used)
    fixed[428:436] = u64(timestamp)
    fixed[436:440] = u32(fixed_size)
    fixed[440:472] = u256(base_fee_per_gas)
    fixed[472:504] = block_hash
    fixed[504:508] = u32(transactions_offset)
    fixed[508:512] = u32(withdrawals_offset)
    fixed[512:520] = u64(blob_gas_used)
    fixed[520:528] = u64(excess_blob_gas)
    fixed[528:532] = u32(access_list_offset)
    fixed[532:540] = u64(slot_number)
    return bytes(fixed) + extra_data + tx_data + withdrawals_data + block_access_list


def fork_activation(block_number: int | None, timestamp: int | None) -> bytes:
    block = b"" if block_number is None else u64(block_number)
    time = b"" if timestamp is None else u64(timestamp)
    return u32(8) + u32(8 + len(block)) + block + time


def chain_config(
    *,
    chain_id: int = 1,
    fork: int = 20,
    activation_block: int | None = None,
    activation_timestamp: int | None = 0,
    blob_schedule: tuple[int, int, int] | None = (1, 2, 3),
) -> bytes:
    activation = fork_activation(activation_block, activation_timestamp)
    blob = b"" if blob_schedule is None else b"".join(u64(value) for value in blob_schedule)
    fork_config = u64(fork) + u32(16) + u32(16 + len(activation)) + activation + blob
    return u64(chain_id) + u32(12) + fork_config


def witness(
    state: Iterable[bytes] = (b"state-a", b"state-b"),
    codes: Iterable[bytes] = (b"code",),
    headers: Iterable[bytes] = (b"header",),
) -> bytes:
    state_data = byte_list_list(state)
    codes_data = byte_list_list(codes)
    headers_data = byte_list_list(headers)
    return (
        u32(12)
        + u32(12 + len(state_data))
        + u32(12 + len(state_data) + len(codes_data))
        + state_data
        + codes_data
        + headers_data
    )


def new_payload_request(
    payload: bytes,
    versioned_hashes: bytes,
    parent_beacon_block_root: bytes,
    requests: bytes,
    padding: int = 0,
) -> bytes:
    assert len(parent_beacon_block_root) == 32
    payload_offset = 44 + padding
    hashes_offset = payload_offset + len(payload)
    requests_offset = hashes_offset + len(versioned_hashes)
    return (
        u32(payload_offset)
        + u32(hashes_offset)
        + parent_beacon_block_root
        + u32(requests_offset)
        + (b"P" * padding)
        + payload
        + versioned_hashes
        + requests
    )


def stateless_input(npr: bytes, witness_bytes: bytes, chain_bytes: bytes, public_keys: bytes) -> bytes:
    witness_offset = 16 + len(npr)
    chain_offset = witness_offset + len(witness_bytes)
    public_keys_offset = chain_offset + len(chain_bytes)
    body = (
        u32(16)
        + u32(witness_offset)
        + u32(chain_offset)
        + u32(public_keys_offset)
        + npr
        + witness_bytes
        + chain_bytes
        + public_keys
    )
    return SCHEMA_ID + body


def make_v4(
    *,
    payload_kwargs: dict[str, object] | None = None,
    versioned_hashes: bytes = b"\x11" * 32,
    parent_beacon_block_root: bytes = bytes(32),
    requests: bytes | None = None,
    npr_padding: int = 0,
    witness_bytes: bytes | None = None,
    chain_bytes: bytes | None = None,
    public_keys: bytes | None = None,
) -> bytes:
    payload = execution_payload(**(payload_kwargs or {}))
    if requests is None:
        requests = execution_requests()
    if witness_bytes is None:
        witness_bytes = witness()
    if chain_bytes is None:
        chain_bytes = chain_config()
    if public_keys is None:
        public_keys = (b"\x04" + bytes(64)) + (b"\x04" + bytes([1]) * 64)
    return stateless_input(
        new_payload_request(payload, versioned_hashes, parent_beacon_block_root, requests, npr_padding),
        witness_bytes,
        chain_bytes,
        public_keys,
    )


def make_rich_v4() -> bytes:
    deposits = deposit_request(bytes_from(1, 48), bytes_from(51, 32), 61, bytes_from(91, 96), 71)
    withdrawal_requests = withdrawal_request(bytes_from(81, 20), bytes_from(101, 48), 151)
    consolidations = consolidation_request(bytes_from(161, 20), bytes_from(181, 48), bytes_from(231, 48))
    return make_v4(
        payload_kwargs={
            "parent_hash": bytes_from(1, 32),
            "fee_recipient": bytes_from(33, 20),
            "state_root": bytes_from(53, 32),
            "receipts_root": bytes_from(85, 32),
            "logs_bloom": bytes_from(117, 256),
            "prev_randao": bytes_from(31, 32),
            "block_number": 1001,
            "gas_limit": 30_000_000,
            "gas_used": 29_999_999,
            "timestamp": 1_700_000_000,
            "extra_data": b"rich-extra-data",
            "base_fee_per_gas": (1 << 240) + (1 << 193) + 123_456_789,
            "block_hash": bytes_from(63, 32),
            "transactions": (b"\x01\x02\x03", b"\xde\xad\xbe\xef"),
            "withdrawals": (
                withdrawal(11, 12, bytes_from(93, 20), 13),
                withdrawal(14, 15, bytes_from(113, 20), 16),
            ),
            "blob_gas_used": 17,
            "excess_blob_gas": 18,
            "block_access_list": b"rich-block-access-list",
            "slot_number": 19,
        },
        versioned_hashes=bytes_from(133, 32) + bytes_from(165, 32),
        parent_beacon_block_root=bytes_from(197, 32),
        requests=execution_requests(deposits, withdrawal_requests, consolidations),
        witness_bytes=witness((b"state-1", b"state-2"), (b"code-1", b"code-2"), (b"header-1", b"header-2")),
        chain_bytes=chain_config(
            chain_id=0,
            activation_block=20,
            activation_timestamp=21,
            blob_schedule=(22, 23, 24),
        ),
        public_keys=(b"\x04" + bytes_from(1, 64)) + (b"\x04" + bytes_from(65, 64)),
    )


def make_v3_structural() -> bytes:
    fixed = bytearray(528)
    fixed[436:440] = u32(528)
    fixed[504:508] = u32(528)
    fixed[508:512] = u32(528)
    payload = bytes(fixed)
    return stateless_input(
        new_payload_request(payload, b"", bytes(32), execution_requests()),
        witness((), (), ()),
        chain_config(fork=17),
        b"",
    )


def set_u32(data: bytes, offset: int, value: int) -> bytes:
    changed = bytearray(data)
    changed[offset : offset + 4] = u32(value)
    return bytes(changed)


def layout(data: bytes) -> dict[str, int]:
    body = 2
    npr = body + int.from_bytes(data[body : body + 4], "little")
    witness_start = body + int.from_bytes(data[body + 4 : body + 8], "little")
    chain_start = body + int.from_bytes(data[body + 8 : body + 12], "little")
    payload = npr + int.from_bytes(data[npr : npr + 4], "little")
    requests = npr + int.from_bytes(data[npr + 40 : npr + 44], "little")
    fork = chain_start + int.from_bytes(data[chain_start + 8 : chain_start + 12], "little")
    activation = fork + int.from_bytes(data[fork + 8 : fork + 12], "little")
    return {
        "top": body,
        "npr": npr,
        "payload": payload,
        "requests": requests,
        "witness": witness_start,
        "chain": chain_start,
        "fork": fork,
        "activation": activation,
        "transactions": payload + int.from_bytes(data[payload + 504 : payload + 508], "little"),
        "witness_state": witness_start + int.from_bytes(data[witness_start : witness_start + 4], "little"),
        "witness_codes": witness_start + int.from_bytes(data[witness_start + 4 : witness_start + 8], "little"),
        "witness_headers": witness_start + int.from_bytes(data[witness_start + 8 : witness_start + 12], "little"),
    }


def cases() -> list[Case]:
    basic = make_v4()
    empty = make_v4(
        payload_kwargs={"extra_data": b"", "transactions": (), "withdrawals": (), "block_access_list": b""},
        versioned_hashes=b"",
        witness_bytes=witness((), (), ()),
        public_keys=b"",
    )
    rich = make_rich_v4()
    base_layout = layout(basic)
    rich_layout = layout(rich)
    one_empty_transaction = make_v4(payload_kwargs={"transactions": (b"",)})
    alias_layout = layout(one_empty_transaction)

    collision_size = 1_048_836
    collision_base = make_v4(payload_kwargs={"block_access_list": b""})
    collision = make_v4(
        payload_kwargs={"block_access_list": b"C" * (collision_size - len(collision_base))}
    )
    assert len(collision) == collision_size
    assert int.from_bytes(collision[:4], "little") == len(collision) - 4

    malformed: list[Case] = [
        Case("bad-schema-id", b"\x00\x02" + basic[2:], False),
        Case("truncated", basic[:-1], False),
        Case("ere-declared-length-mismatch", u32(len(basic) + 1) + basic, False),
        Case("top-first-offset-inside-fixed", set_u32(basic, 2, 1), False),
        Case("top-offset-descending", set_u32(basic, 6, 15), False),
        Case("top-offset-out-of-range", set_u32(basic, 14, len(basic) + 1), False),
        Case("transaction-table-first-offset", set_u32(basic, base_layout["transactions"], 1), False),
        Case(
            "transaction-table-descending-offset",
            set_u32(basic, base_layout["transactions"] + 4, 7),
            False,
        ),
        Case("noncanonical-empty-variable-list", set_u32(one_empty_transaction, alias_layout["transactions"], 0), False),
        Case("versioned-hash-nondivisible", make_v4(versioned_hashes=b"X" * 33), False),
        Case("extra-data-over-bound", make_v4(payload_kwargs={"extra_data": b"X" * 33}), False),
        Case(
            "withdrawals-over-bound",
            make_v4(payload_kwargs={"withdrawals": (bytes(44),) * 17}),
            False,
        ),
        Case("versioned-hashes-over-bound", make_v4(versioned_hashes=b"X" * (32 * 4097)), False),
        Case("deposit-request-nondivisible", make_v4(requests=execution_requests(deposits=b"X")), False),
        Case("withdrawal-request-nondivisible", make_v4(requests=execution_requests(withdrawals=b"X")), False),
        Case("consolidation-request-nondivisible", make_v4(requests=execution_requests(consolidations=b"X")), False),
        Case("unknown-fork-index", make_v4(chain_bytes=chain_config(fork=21)), False),
        Case("noncanonical-npr-first-offset", make_v4(npr_padding=1), False),
    ]
    for name, offset in (
        ("top-witness", rich_layout["top"] + 4),
        ("top-chain", rich_layout["top"] + 8),
        ("npr-payload", rich_layout["npr"]),
        ("npr-hashes", rich_layout["npr"] + 4),
        ("npr-requests", rich_layout["npr"] + 40),
        ("payload-extra", rich_layout["payload"] + 436),
        ("payload-transactions", rich_layout["payload"] + 504),
        ("payload-withdrawals", rich_layout["payload"] + 508),
        ("payload-access-list", rich_layout["payload"] + 528),
        ("requests-deposits", rich_layout["requests"]),
        ("requests-withdrawals", rich_layout["requests"] + 4),
        ("requests-consolidations", rich_layout["requests"] + 8),
        ("witness-state", rich_layout["witness"]),
        ("witness-codes", rich_layout["witness"] + 4),
        ("witness-headers", rich_layout["witness"] + 8),
        ("chain-fork", rich_layout["chain"] + 8),
        ("fork-activation", rich_layout["fork"] + 8),
        ("fork-blob-schedule", rich_layout["fork"] + 12),
        ("activation-block", rich_layout["activation"]),
        ("activation-timestamp", rich_layout["activation"] + 4),
        ("transactions-list", rich_layout["transactions"]),
        ("witness-state-list", rich_layout["witness_state"]),
        ("witness-codes-list", rich_layout["witness_codes"]),
        ("witness-headers-list", rich_layout["witness_headers"]),
    ):
        malformed.append(Case(f"offset-mutation-{name}", set_u32(rich, offset, 0), False))

    return [
        Case("valid-v4-raw", basic, True),
        Case("valid-v4-ere", u32(len(basic)) + basic, True),
        Case("valid-v4-empty-variable-lists", empty, True),
        Case("valid-v4-rich-raw", rich, True),
        Case("valid-v4-rich-ere", u32(len(rich)) + rich, True),
        Case("raw-ere-prefix-collision", collision, True),
        Case("ere-prefixed-collision", u32(len(collision)) + collision, True),
        *malformed,
    ]


def run(
    command: list[str], data: bytes, *, preexec_fn: Callable[[], object] | None = None
) -> Outcome:
    result = subprocess.run(
        command,
        input=data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        preexec_fn=preexec_fn,
    )
    return Outcome(result.returncode, result.stdout, result.stderr)


def run_lean(binary: Path, data: bytes) -> Outcome:
    def unlimited_stack() -> None:
        # SizzLean's executable fixed-element serializer is recursive.  The
        # raw/Ere prefix-collision fixture has a legitimate 1 MiB byte list,
        # so retain the strict serialize-equality check with the host's
        # available unlimited stack rather than weakening canonicality.
        _, hard_limit = resource.getrlimit(resource.RLIMIT_STACK)
        resource.setrlimit(resource.RLIMIT_STACK, (hard_limit, hard_limit))

    with tempfile.NamedTemporaryFile(prefix="ssz-v4-", suffix=".ssz") as fixture:
        fixture.write(data)
        fixture.flush()
        return run([str(binary), fixture.name], b"", preexec_fn=unlimited_stack)


def valid_protocol(stream: bytes) -> bool:
    if not stream.startswith(b"version\tssz-value-v1\n") or not stream.endswith(b"\n"):
        return False
    allowed = {b"scalar", b"bytes", b"count", b"option"}
    for line in stream.splitlines()[1:]:
        fields = line.split(b"\t")
        if len(fields) != 3 or fields[1] not in allowed:
            return False
    return True


def digest(stream: bytes) -> str:
    return hashlib.sha256(stream).hexdigest()[:16]


def show_outcome(name: str, case: Case, outcomes: dict[str, Outcome]) -> None:
    values = " ".join(
        f"{adapter}={outcome.returncode}:{len(outcome.stdout)}B" for adapter, outcome in outcomes.items()
    )
    print(f"{case.name}\t{'valid' if case.valid else 'invalid'}\t{values}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference-python", type=Path, required=True)
    parser.add_argument("--zesu-value-binary", type=Path, required=True)
    parser.add_argument("--lean-binary", type=Path, required=True)
    parser.add_argument(
        "--reference-program",
        type=Path,
        default=Path(__file__).with_name("ssz_value_reference.py"),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    for path in (args.reference_python, args.zesu_value_binary, args.lean_binary, args.reference_program):
        if not path.is_file():
            raise SystemExit(f"required path does not exist or is not a file: {path}")

    failures: list[str] = []
    for case in cases():
        outcomes = {
            "python": run([str(args.reference_python), str(args.reference_program)], case.data),
            "lean": run_lean(args.lean_binary, case.data),
            "zesu": run([str(args.zesu_value_binary)], case.data),
        }
        show_outcome(case.name, case, outcomes)
        if case.valid:
            if any(outcome.returncode != 0 for outcome in outcomes.values()):
                failures.append(f"{case.name}: valid input rejected")
                continue
            if any(not valid_protocol(outcome.stdout) for outcome in outcomes.values()):
                failures.append(f"{case.name}: malformed ssz-value-v1 output")
                continue
            streams = {adapter: outcome.stdout for adapter, outcome in outcomes.items()}
            if len(set(streams.values())) != 1:
                failures.append(
                    f"{case.name}: value mismatch "
                    + " ".join(f"{adapter}={digest(stream)}" for adapter, stream in streams.items())
                )
        elif any(outcome.returncode == 0 for outcome in outcomes.values()):
            accepted = ", ".join(adapter for adapter, outcome in outcomes.items() if outcome.returncode == 0)
            failures.append(f"{case.name}: malformed input accepted by {accepted}")

    if failures:
        print("strict V4 differential failed:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1
    print("strict V4 full-value differential: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
