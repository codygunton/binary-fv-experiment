#!/usr/bin/env python3
"""Render the pinned Amsterdam SSZ schema through ``ssz-value-v1``.

This is intentionally a raw-schema oracle: it decodes ``SszStatelessInput``
directly instead of converting to execution-spec runtime types, so uint256
base fees, chain ID zero, blob schedules, and every request field remain
observable.  The input protocol is raw V4 SSZ first, then an exact ERE length
frame only when raw parsing fails.
"""

from __future__ import annotations

import sys
from typing import Iterable

from ethereum.forks.amsterdam.stateless_ssz import (
    PROTOCOL_FORKS,
    STATELESS_INPUT_SCHEMA_ID_BYTES,
    SszStatelessInput,
)


class DecodeError(ValueError):
    """The input does not satisfy the pinned V4 raw-schema contract."""


def decode_raw_v4(payload: bytes) -> SszStatelessInput:
    if not payload.startswith(STATELESS_INPUT_SCHEMA_ID_BYTES):
        raise DecodeError("bad schema identifier")
    try:
        value = SszStatelessInput.decode_bytes(payload[2:])
    except Exception as error:  # remerkleable exposes several decode exception types
        raise DecodeError(type(error).__name__) from error
    if int(value.chain_config.active_fork.fork) >= len(PROTOCOL_FORKS):
        raise DecodeError("unknown protocol fork")
    return value


def decode_candidate(data: bytes) -> SszStatelessInput:
    try:
        return decode_raw_v4(data)
    except DecodeError as raw_error:
        if len(data) < 4 or int.from_bytes(data[:4], "little") != len(data) - 4:
            raise raw_error
        return decode_raw_v4(data[4:])


def _record(path: str, kind: str, value: str) -> str:
    return f"{path}\t{kind}\t{value}"


def _scalar(path: str, value: object) -> str:
    return _record(path, "scalar", str(int(value)))


def _bytes(path: str, value: object) -> str:
    return _record(path, "bytes", f"0x{bytes(value).hex()}")


def _count(path: str, values: Iterable[object]) -> str:
    return _record(path, "count", str(len(values)))


def _optional_scalar(records: list[str], path: str, values: Iterable[object]) -> None:
    values = list(values)
    if len(values) == 0:
        records.append(_record(path, "option", "none"))
        return
    if len(values) != 1:
        raise DecodeError(f"noncanonical optional at {path}")
    records.append(_record(path, "option", "some"))
    records.append(_scalar(f"{path}.value", values[0]))


def _optional_blob_schedule(records: list[str], path: str, values: Iterable[object]) -> None:
    values = list(values)
    if len(values) == 0:
        records.append(_record(path, "option", "none"))
        return
    if len(values) != 1:
        raise DecodeError(f"noncanonical optional at {path}")
    value = values[0]
    records.append(_record(path, "option", "some"))
    records.append(_scalar(f"{path}.value.target", value.target))
    records.append(_scalar(f"{path}.value.max", value.max))
    records.append(_scalar(f"{path}.value.base_fee_update_fraction", value.base_fee_update_fraction))


def render_value(value: SszStatelessInput) -> bytes:
    records = ["version\tssz-value-v1"]
    request = value.new_payload_request
    payload = request.execution_payload
    payload_path = "new_payload_request.execution_payload"

    for name in (
        "parent_hash",
        "fee_recipient",
        "state_root",
        "receipts_root",
        "logs_bloom",
        "prev_randao",
    ):
        records.append(_bytes(f"{payload_path}.{name}", getattr(payload, name)))
    for name in ("block_number", "gas_limit", "gas_used", "timestamp"):
        records.append(_scalar(f"{payload_path}.{name}", getattr(payload, name)))
    records.append(_bytes(f"{payload_path}.extra_data", payload.extra_data))
    records.append(_scalar(f"{payload_path}.base_fee_per_gas", payload.base_fee_per_gas))
    records.append(_bytes(f"{payload_path}.block_hash", payload.block_hash))

    transactions_path = f"{payload_path}.transactions"
    records.append(_count(transactions_path, payload.transactions))
    for index, transaction in enumerate(payload.transactions):
        records.append(_bytes(f"{transactions_path}[{index}]", transaction))

    withdrawals_path = f"{payload_path}.withdrawals"
    records.append(_count(withdrawals_path, payload.withdrawals))
    for index, withdrawal in enumerate(payload.withdrawals):
        path = f"{withdrawals_path}[{index}]"
        records.append(_scalar(f"{path}.index", withdrawal.index))
        records.append(_scalar(f"{path}.validator_index", withdrawal.validator_index))
        records.append(_bytes(f"{path}.address", withdrawal.address))
        records.append(_scalar(f"{path}.amount", withdrawal.amount))
    for name in ("blob_gas_used", "excess_blob_gas"):
        records.append(_scalar(f"{payload_path}.{name}", getattr(payload, name)))
    records.append(_bytes(f"{payload_path}.block_access_list", payload.block_access_list))
    records.append(_scalar(f"{payload_path}.slot_number", payload.slot_number))

    hashes_path = "new_payload_request.versioned_hashes"
    records.append(_count(hashes_path, request.versioned_hashes))
    for index, hash_ in enumerate(request.versioned_hashes):
        records.append(_bytes(f"{hashes_path}[{index}]", hash_))
    records.append(_bytes("new_payload_request.parent_beacon_block_root", request.parent_beacon_block_root))

    requests = request.execution_requests
    requests_path = "new_payload_request.execution_requests"
    deposits_path = f"{requests_path}.deposits"
    records.append(_count(deposits_path, requests.deposits))
    for index, deposit in enumerate(requests.deposits):
        path = f"{deposits_path}[{index}]"
        records.append(_bytes(f"{path}.pubkey", deposit.pubkey))
        records.append(_bytes(f"{path}.withdrawal_credentials", deposit.withdrawal_credentials))
        records.append(_scalar(f"{path}.amount", deposit.amount))
        records.append(_bytes(f"{path}.signature", deposit.signature))
        records.append(_scalar(f"{path}.index", deposit.index))
    withdrawal_requests_path = f"{requests_path}.withdrawals"
    records.append(_count(withdrawal_requests_path, requests.withdrawals))
    for index, withdrawal in enumerate(requests.withdrawals):
        path = f"{withdrawal_requests_path}[{index}]"
        records.append(_bytes(f"{path}.source_address", withdrawal.source_address))
        records.append(_bytes(f"{path}.validator_pubkey", withdrawal.validator_pubkey))
        records.append(_scalar(f"{path}.amount", withdrawal.amount))
    consolidations_path = f"{requests_path}.consolidations"
    records.append(_count(consolidations_path, requests.consolidations))
    for index, consolidation in enumerate(requests.consolidations):
        path = f"{consolidations_path}[{index}]"
        records.append(_bytes(f"{path}.source_address", consolidation.source_address))
        records.append(_bytes(f"{path}.source_pubkey", consolidation.source_pubkey))
        records.append(_bytes(f"{path}.target_pubkey", consolidation.target_pubkey))

    witness = value.witness
    for name in ("state", "codes", "headers"):
        values = getattr(witness, name)
        path = f"witness.{name}"
        records.append(_count(path, values))
        for index, entry in enumerate(values):
            records.append(_bytes(f"{path}[{index}]", entry))

    config = value.chain_config
    records.append(_scalar("chain_config.chain_id", config.chain_id))
    active_fork = config.active_fork
    records.append(_scalar("chain_config.active_fork.fork", active_fork.fork))
    _optional_scalar(records, "chain_config.active_fork.activation.block_number", active_fork.activation.block_number)
    _optional_scalar(records, "chain_config.active_fork.activation.timestamp", active_fork.activation.timestamp)
    _optional_blob_schedule(records, "chain_config.active_fork.blob_schedule", active_fork.blob_schedule)

    keys_path = "public_keys"
    records.append(_count(keys_path, value.public_keys))
    for index, key in enumerate(value.public_keys):
        records.append(_bytes(f"{keys_path}[{index}]", key))
    return ("\n".join(records) + "\n").encode("utf-8")


def main() -> int:
    try:
        sys.stdout.buffer.write(render_value(decode_candidate(sys.stdin.buffer.read())))
    except DecodeError as error:
        print(f"error\t{error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
