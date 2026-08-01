#!/usr/bin/env python3
"""Anti-DCE regression for the RV64 raw-SSZ result sink.

The checked binary must be the measurement composition: its stdin harness calls
``zesu_decode_raw`` once and prints ``ok <16 lowercase hex digits>`` after
calling the separate sink object. This script uses a canonical rich Amsterdam
V4 fixture and changes one value at a time without changing any offset, list
shape, or fixed-width encoding. Every run must accept and produce a checksum
distinct from every other run.

This is an observability test only. The checksum is intentionally not a value
oracle and is not used by the Python/Lean/Zesu full-value differential.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


# Keep fixture construction centralized with the strict V4 corpus. Importing it
# is side-effect-free because its main function is guarded by __name__.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from ssz_differential_audit import layout, make_rich_v4  # noqa: E402


CHECKSUM = re.compile(rb"ok ([0-9a-f]{16})\n\Z")


def read_u32(data: bytes, offset: int) -> int:
    if offset < 0 or offset + 4 > len(data):
        raise ValueError(f"u32 offset outside fixture: {offset}")
    return int.from_bytes(data[offset : offset + 4], "little")


def flip_byte(data: bytes, offset: int) -> bytes:
    if offset < 0 or offset >= len(data):
        raise ValueError(f"mutation offset outside fixture: {offset}")
    changed = bytearray(data)
    changed[offset] ^= 0x01
    return bytes(changed)


def set_byte(data: bytes, offset: int, value: int) -> bytes:
    if offset < 0 or offset >= len(data) or not 0 <= value <= 0xFF:
        raise ValueError(f"invalid byte mutation at {offset}: {value}")
    changed = bytearray(data)
    changed[offset] = value
    return bytes(changed)


def first_variable_list_item(data: bytes, list_start: int) -> int:
    """Return the first byte of a nonempty canonical List[ByteList]."""
    first_offset = read_u32(data, list_start)
    if first_offset < 4 or first_offset > len(data) - list_start:
        raise ValueError(f"unexpected variable-list layout at {list_start}")
    return list_start + first_offset


def rich_mutations(data: bytes) -> list[tuple[str, bytes]]:
    """Mutate every major raw-schema component while retaining valid V4 SSZ."""
    positions = layout(data)
    payload = positions["payload"]
    npr = positions["npr"]
    requests = positions["requests"]
    chain = positions["chain"]
    fork = positions["fork"]
    activation = positions["activation"]
    top = positions["top"]

    transactions = positions["transactions"]
    withdrawals = payload + read_u32(data, payload + 508)
    block_access_list = payload + read_u32(data, payload + 528)
    hashes = npr + read_u32(data, npr + 4)
    deposits = requests + read_u32(data, requests)
    withdrawal_requests = requests + read_u32(data, requests + 4)
    consolidations = requests + read_u32(data, requests + 8)
    blob_schedule = fork + read_u32(data, fork + 12)
    public_keys = top + read_u32(data, top + 12)

    byte_locations = [
        # Execution payload: fixed vectors, scalar widths, and every variable field.
        ("payload.parent_hash", payload),
        ("payload.fee_recipient", payload + 32),
        ("payload.state_root", payload + 52),
        ("payload.receipts_root", payload + 84),
        ("payload.logs_bloom", payload + 116),
        ("payload.prev_randao", payload + 372),
        ("payload.block_number", payload + 404),
        ("payload.gas_limit", payload + 412),
        ("payload.gas_used", payload + 420),
        ("payload.timestamp", payload + 428),
        ("payload.extra_data", payload + read_u32(data, payload + 436)),
        # Exercise a high byte of uint256 rather than only its u64 low limb.
        ("payload.base_fee_per_gas.high_byte", payload + 440 + 31),
        ("payload.block_hash", payload + 472),
        ("payload.transactions[0]", first_variable_list_item(data, transactions)),
        ("payload.withdrawals[0]", withdrawals + 36),
        ("payload.blob_gas_used", payload + 512),
        ("payload.excess_blob_gas", payload + 520),
        ("payload.block_access_list", block_access_list),
        ("payload.slot_number", payload + 532),
        # NewPayloadRequest and all three typed execution-request lists.
        ("new_payload_request.versioned_hashes[0]", hashes),
        ("new_payload_request.parent_beacon_block_root", npr + 8),
        ("requests.deposits[0]", deposits),
        ("requests.withdrawals[0]", withdrawal_requests),
        ("requests.consolidations[0]", consolidations + 68),
        # Every witness list contains two nonempty entries in make_rich_v4().
        ("witness.state[0]", first_variable_list_item(data, positions["witness_state"])),
        ("witness.codes[0]", first_variable_list_item(data, positions["witness_codes"])),
        ("witness.headers[0]", first_variable_list_item(data, positions["witness_headers"])),
        # Fork configuration preserves exact scalar/optional/blob values.
        ("chain_config.chain_id", chain),
        ("activation.block_number", activation + read_u32(data, activation)),
        ("activation.timestamp", activation + read_u32(data, activation + 4)),
        ("blob_schedule.target", blob_schedule),
        ("public_keys[0]", public_keys + 1),
    ]
    mutations = [(name, flip_byte(data, offset)) for name, offset in byte_locations]

    # Fork 20 is Amsterdam; 20 xor 1 would become the intentionally invalid
    # index 21. Change it to another known enum value instead.
    mutations.append(("chain_config.active_fork.fork", set_byte(data, fork, 19)))
    return mutations


def run_harness(qemu: Path, binary: Path, data: bytes, timeout: float) -> str:
    try:
        result = subprocess.run(
            [str(qemu), str(binary)],
            input=data,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f"timed out after {timeout:g}s") from error

    if result.returncode != 0:
        stderr = result.stderr.decode("utf-8", "replace").strip()
        stdout = result.stdout.decode("utf-8", "replace").strip()
        raise RuntimeError(f"rejected (exit {result.returncode}, stdout={stdout!r}, stderr={stderr!r})")
    match = CHECKSUM.fullmatch(result.stdout)
    if match is None:
        rendered = result.stdout.decode("utf-8", "replace").strip()
        raise RuntimeError(f"expected 'ok <checksum>', got {rendered!r}")
    return match.group(1).decode("ascii")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qemu", type=Path, required=True, help="riscv64 user-mode QEMU executable")
    parser.add_argument("--binary", type=Path, required=True, help="RV64 Zesu raw-decoder/sink harness")
    parser.add_argument("--timeout", type=float, default=30.0, help="per-fixture timeout in seconds")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    for path in (args.qemu, args.binary):
        if not path.is_file():
            print(f"required file does not exist: {path}", file=sys.stderr)
            return 2
    if args.timeout <= 0:
        print("--timeout must be positive", file=sys.stderr)
        return 2

    baseline = make_rich_v4()
    observations: dict[str, str] = {}
    owners: dict[str, str] = {}
    cases = [("baseline", baseline), *rich_mutations(baseline)]
    for name, fixture in cases:
        try:
            checksum = run_harness(args.qemu, args.binary, fixture, args.timeout)
        except RuntimeError as error:
            print(f"{name}\tfailed\t{error}", file=sys.stderr)
            return 1
        if checksum in owners:
            print(
                f"checksum collision: {name} and {owners[checksum]} both produced {checksum}",
                file=sys.stderr,
            )
            return 1
        owners[checksum] = name
        observations[name] = checksum
        print(f"{name}\t{checksum}")

    print(f"sink observability: ok ({len(observations) - 1} valid mutations)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
