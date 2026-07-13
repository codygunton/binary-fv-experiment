#!/usr/bin/env python3
"""Exercise a deterministic raw-SSZ corpus against Python and RV64 Zesu.

The Python oracle must be the virtual environment built for the pinned
execution-specs revision.  The RV64 program must be the ``.#zesu-ssz`` ELF
run through a RISC-V user-mode emulator.  For example:

  python3 tests/ssz_differential_audit.py \
    --reference-python /path/to/execution-specs/.venv/bin/python \
    --qemu /path/to/qemu-riscv64 \
    --binary build/zesu-ssz/bin/zesu-ssz \
    --lean-binary specs/ssz-bridge/.lake/build/bin/ssz_bridge

The expected-results file deliberately records known divergences.  Add
``--fail-on-divergence`` when using this as a specification gate.

Pass the executable built by ``specs/ssz-bridge`` with ``--lean-binary`` to
check the same corpus against the executable Lean normalization bridge.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


REFERENCE_PROGRAM = r"""
import json
import sys

from ethereum.forks.amsterdam.stateless_guest import deserialize_stateless_input
from ethereum_types.bytes import Bytes

try:
    deserialize_stateless_input(Bytes(sys.stdin.buffer.read()))
except Exception as error:
    print(json.dumps({"ok": False, "detail": type(error).__name__}))
else:
    print(json.dumps({"ok": True, "detail": "ok"}))
"""


def u32(value: int) -> bytes:
    return value.to_bytes(4, "little")


def u64(value: int) -> bytes:
    return value.to_bytes(8, "little")


def byte_list_list(items: tuple[bytes, ...]) -> bytes:
    if not items:
        return b""
    offset = 4 * len(items)
    offsets: list[bytes] = []
    for item in items:
        offsets.append(u32(offset))
        offset += len(item)
    return b"".join(offsets) + b"".join(items)


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
    version: int,
    *,
    extra_data: bytes,
    transactions: tuple[bytes, ...],
    withdrawals: tuple[bytes, ...],
    block_access_list: bytes,
) -> bytes:
    fixed_size = 540 if version == 4 else 528
    assert version in (3, 4)
    assert all(len(withdrawal) == 44 for withdrawal in withdrawals)
    tx_data = byte_list_list(transactions)
    withdrawals_data = b"".join(withdrawals)
    transactions_offset = fixed_size + len(extra_data)
    withdrawals_offset = transactions_offset + len(tx_data)
    access_list_offset = withdrawals_offset + len(withdrawals_data)
    fixed = bytearray(fixed_size)
    fixed[436:440] = u32(fixed_size)
    fixed[504:508] = u32(transactions_offset)
    fixed[508:512] = u32(withdrawals_offset)
    if version == 4:
        fixed[528:532] = u32(access_list_offset)
        fixed[532:540] = u64(7)
        return bytes(fixed) + extra_data + tx_data + withdrawals_data + block_access_list
    return bytes(fixed) + extra_data + tx_data + withdrawals_data


def chain_config(fork: int) -> bytes:
    """Encode nested variable containers for ForkConfig and ForkActivation."""
    activation = u32(8) + u32(8) + u64(0)
    blob_schedule = u64(1) + u64(2) + u64(3)
    fork_config = u64(fork) + u32(16) + u32(16 + len(activation))
    fork_config += activation + blob_schedule
    return u64(1) + u32(12) + fork_config


def witness() -> bytes:
    state = byte_list_list((b"state-a", b"state-b"))
    codes = byte_list_list((b"code",))
    headers = byte_list_list((b"header",))
    return (
        u32(12)
        + u32(12 + len(state))
        + u32(12 + len(state) + len(codes))
        + state
        + codes
        + headers
    )


def empty_witness() -> bytes:
    return u32(12) + u32(12) + u32(12)


def new_payload_request(
    payload: bytes, versioned_hashes: bytes, requests: bytes, padding: int
) -> bytes:
    ep_offset = 44 + padding
    hashes_offset = ep_offset + len(payload)
    requests_offset = hashes_offset + len(versioned_hashes)
    return (
        u32(ep_offset)
        + u32(hashes_offset)
        + bytes(32)
        + u32(requests_offset)
        + (b"P" * padding)
        + payload
        + versioned_hashes
        + requests
    )


def stateless_input(
    npr: bytes, witness_bytes: bytes, chain_bytes: bytes, public_keys: bytes
) -> bytes:
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
    return b"\x00\x01" + body


def make_input(
    version: int,
    *,
    extra_data: bytes = b"extra",
    transactions: tuple[bytes, ...] = (b"\xc0", b"\x01\x02"),
    withdrawals: tuple[bytes, ...] = (bytes(range(44)),),
    block_access_list: bytes = b"access-list",
    fork: int | None = None,
    versioned_hashes: bytes = b"\x11" * 32,
    requests: bytes | None = None,
    npr_padding: int = 0,
    witness_bytes: bytes | None = None,
    public_keys: bytes | None = None,
) -> bytes:
    if fork is None:
        fork = 20 if version == 4 else 17
    if requests is None:
        requests = execution_requests()
    payload = execution_payload(
        version,
        extra_data=extra_data,
        transactions=transactions,
        withdrawals=withdrawals,
        block_access_list=block_access_list,
    )
    npr = new_payload_request(payload, versioned_hashes, requests, npr_padding)
    if witness_bytes is None:
        witness_bytes = witness()
    if public_keys is None:
        public_keys = (b"\x04" + bytes(64)) + (b"\x04" + bytes([1]) * 64)
    return stateless_input(npr, witness_bytes, chain_config(fork), public_keys)


def set_u32(data: bytes, offset: int, value: int) -> bytes:
    changed = bytearray(data)
    changed[offset : offset + 4] = u32(value)
    return bytes(changed)


def transaction_table_start(data: bytes) -> int:
    npr_start = 2 + 16
    ep_start = npr_start + int.from_bytes(data[npr_start : npr_start + 4], "little")
    tx_offset = int.from_bytes(data[ep_start + 504 : ep_start + 508], "little")
    return ep_start + tx_offset


def corpus() -> list[tuple[str, bytes, bool]]:
    """Return ``(name, input, has_v4_python_oracle)`` corpus entries."""
    v4 = make_input(4)
    empty_v4 = make_input(
        4,
        extra_data=b"",
        transactions=(),
        withdrawals=(),
        block_access_list=b"",
        versioned_hashes=b"",
        requests=execution_requests(),
        witness_bytes=empty_witness(),
        public_keys=b"",
    )
    tx_table = transaction_table_start(v4)
    v3 = make_input(3, block_access_list=b"")

    collision_size = 1_048_836
    base = make_input(4, block_access_list=b"")
    collision = make_input(4, block_access_list=b"C" * (collision_size - len(base)))
    assert len(collision) == collision_size
    assert int.from_bytes(collision[:4], "little") == len(collision) - 4

    return [
        ("valid-v4-raw", v4, True),
        ("valid-v4-empty-variable-lists", empty_v4, True),
        ("valid-v4-ere", u32(len(v4)) + v4, False),
        ("valid-v3-raw-structural-only", v3, False),
        ("valid-v3-ere-structural-only", u32(len(v3)) + v3, False),
        ("bad-schema-id", b"\x00\x02" + v4[2:], True),
        ("truncated", v4[:-1], True),
        ("ere-declared-length-mismatch", u32(len(v4) + 1) + v4, False),
        ("top-first-offset-inside-fixed", set_u32(v4, 2, 1), True),
        ("top-offset-descending", set_u32(v4, 6, 15), True),
        ("top-offset-out-of-range", set_u32(v4, 14, len(v4) + 1), True),
        ("transaction-table-first-offset", set_u32(v4, tx_table, 1), True),
        ("transaction-table-overlap-descending", set_u32(v4, tx_table + 4, 7), True),
        (
            "fixed-element-divisibility-versioned-hashes",
            make_input(4, versioned_hashes=bytes(33)),
            True,
        ),
        ("oversized-extra-data-33", make_input(4, extra_data=b"X" * 33), True),
        ("too-many-withdrawals-17", make_input(4, withdrawals=(bytes(44),) * 17), True),
        ("too-many-versioned-hashes-4097", make_input(4, versioned_hashes=bytes(32 * 4097)), True),
        ("malformed-deposit-fixed-size", make_input(4, requests=execution_requests(deposits=b"X")), True),
        ("unknown-fork-index", make_input(4, fork=999), True),
        ("noncanonical-npr-first-offset", make_input(4, npr_padding=1), True),
        ("ere-heuristic-collision-raw", collision, True),
        ("ere-heuristic-collision-prefixed", u32(len(collision)) + collision, False),
    ]


def reference_accepts(reference_python: Path, data: bytes) -> tuple[bool, str]:
    result = subprocess.run(
        [str(reference_python), "-c", REFERENCE_PROGRAM],
        input=data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.decode("utf-8", "replace").strip())
    decoded = json.loads(result.stdout)
    return bool(decoded["ok"]), str(decoded["detail"])


def zesu_accepts(qemu: Path, binary: Path, data: bytes) -> tuple[bool, str]:
    result = subprocess.run(
        [str(qemu), str(binary)],
        input=data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    message = result.stdout.decode("ascii", "replace").strip()
    if result.stderr:
        message += f" stderr={result.stderr.decode('ascii', 'replace').strip()}"
    return result.returncode == 0 and message == "ok", f"{result.returncode}:{message}"


def lean_accepts(binary: Path, data: bytes) -> tuple[bool, str]:
    with tempfile.NamedTemporaryFile(prefix="ssz-bridge-", suffix=".ssz") as fixture:
        fixture.write(data)
        fixture.flush()
        result = subprocess.run(
            [str(binary), fixture.name],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    message = result.stdout.decode("utf-8", "replace").strip()
    if result.stderr:
        message += f" stderr={result.stderr.decode('utf-8', 'replace').strip()}"
    return result.returncode == 0 and message.startswith("ok\t"), f"{result.returncode}:{message}"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference-python", type=Path, required=True)
    parser.add_argument("--qemu", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--lean-binary", type=Path, required=True)
    parser.add_argument(
        "--expected",
        type=Path,
        default=Path(__file__).with_name("ssz-differential-expected.json"),
    )
    parser.add_argument("--fail-on-divergence", action="store_true")
    parser.add_argument("--json", action="store_true", help="emit JSON Lines")
    return parser.parse_args()


def render(record: dict[str, Any], as_json: bool) -> str:
    if as_json:
        return json.dumps(record, sort_keys=True)
    return (
        f"{record['case']}\tbytes={record['bytes']}"
        f"\tpython={record['python']}:{record['python_detail']}"
        f"\tlean={record['lean']}:{record['lean_detail']}"
        f"\tzesu={record['zesu']}:{record['zesu_detail']}"
    )


def main() -> int:
    args = parse_args()
    for path in (args.reference_python, args.qemu, args.binary, args.lean_binary, args.expected):
        if not path.is_file():
            raise SystemExit(f"required path does not exist or is not a file: {path}")

    expected = json.loads(args.expected.read_text())
    expected_cases: dict[str, dict[str, bool | None]] = expected["cases"]
    mismatched_expectations: list[str] = []
    divergences: list[str] = []
    seen: set[str] = set()

    for name, data, has_python_oracle in corpus():
        python_ok: bool | None = None
        python_detail = "n/a"
        if has_python_oracle:
            python_ok, python_detail = reference_accepts(args.reference_python, data)
        zesu_ok, zesu_detail = zesu_accepts(args.qemu, args.binary, data)
        lean_ok, lean_detail = lean_accepts(args.lean_binary, data)
        record: dict[str, Any] = {
            "case": name,
            "bytes": len(data),
            "python": python_ok,
            "python_detail": python_detail,
            "lean": lean_ok,
            "lean_detail": lean_detail,
            "zesu": zesu_ok,
            "zesu_detail": zesu_detail,
        }
        print(render(record, args.json))
        seen.add(name)

        if name not in expected_cases:
            mismatched_expectations.append(f"missing expected case: {name}")
            continue
        expected_case = expected_cases[name]
        if (
            expected_case["python"] != python_ok
            or expected_case["lean"] != lean_ok
            or expected_case["zesu"] != zesu_ok
        ):
            mismatched_expectations.append(
                f"{name}: expected python={expected_case['python']} "
                f"lean={expected_case['lean']} zesu={expected_case['zesu']}"
            )
        outcomes = {outcome for outcome in (python_ok, lean_ok, zesu_ok) if outcome is not None}
        if len(outcomes) > 1:
            divergences.append(name)

    unexpected = set(expected_cases) - seen
    mismatched_expectations.extend(f"unexpected expected case: {name}" for name in sorted(unexpected))
    if mismatched_expectations:
        print("expected-result mismatch: " + "; ".join(mismatched_expectations), file=sys.stderr)
        return 1
    if divergences:
        print("Reference/Lean/Zesu divergences: " + ", ".join(divergences), file=sys.stderr)
        if args.fail_on_divergence:
            return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
