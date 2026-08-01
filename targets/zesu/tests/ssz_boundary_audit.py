#!/usr/bin/env python3
"""Strict three-way V4 boundary differential.

The default corpus instantiates every V4 capacity that remains practical for
the complete ``ssz-value-v1`` renderer.  A valid boundary must yield
byte-identical values from the pinned Python reference, the Lean/SizzLean
oracle, and the host-only Zesu value formatter.  Its paired over-bound input
must be rejected by all three.

``--extended`` additionally instantiates the 2**18-item ``witness.codes``
limit with empty byte lists.  It is valid SSZ and has a modest wire size
(about 1 MiB), but its complete value stream has 262,144 indexed records.

Intentionally uninstantiated limits:

* An individual transaction and the block-access list each permit 2**30
  bytes.  A boundary fixture would require at least 1 GiB of input and the
  lossless hexadecimal value protocol would make each adapter emit more than
  2 GiB.  The existing raw/Ere collision case still covers a legitimate
  approximately-1 MiB byte list and the decoder retains the actual bounds.
* The 2**20 transaction-count and 2**22 witness-state-count boundaries would
  respectively require one and four million indexed full-value records.  The
  latter alone produces roughly 150 MiB per adapter and drives SizzLean's
  recursive variable-list decode/serialize/render paths far beyond a useful
  function gate.  They are deliberately not treated as evidence that the
  limits are unchecked.
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path

from ssz_differential_audit import (
    Case,
    Outcome,
    bytes_from,
    consolidation_request,
    deposit_request,
    execution_requests,
    make_v4,
    run,
    run_lean,
    u32,
    u64,
    valid_protocol,
    withdrawal,
    withdrawal_request,
    witness,
)


@dataclass(frozen=True)
class BoundaryCase:
    case: Case
    tier: str = "default"


def empty_byte_list_list(count: int) -> bytes:
    """Canonical variable-list encoding of ``count`` empty byte lists."""
    assert count >= 0
    if count == 0:
        return b""
    table_size = 4 * count
    assert table_size <= 0xFFFF_FFFF
    return u32(table_size) * count


def raw_witness(*, state: bytes = b"", codes: bytes = b"", headers: bytes = b"") -> bytes:
    """Build the variable-field witness container from pre-encoded lists."""
    return (
        u32(12)
        + u32(12 + len(state))
        + u32(12 + len(state) + len(codes))
        + state
        + codes
        + headers
    )


def raw_chain_config(
    *,
    activation_blocks: tuple[int, ...] = (),
    activation_timestamps: tuple[int, ...] = (),
    blob_schedules: tuple[tuple[int, int, int], ...] = (),
    chain_id: int = 1,
    fork: int = 20,
) -> bytes:
    """Build ChainConfig while allowing deliberately over-bound option lists."""
    block_values = b"".join(u64(value) for value in activation_blocks)
    timestamp_values = b"".join(u64(value) for value in activation_timestamps)
    activation = u32(8) + u32(8 + len(block_values)) + block_values + timestamp_values
    blob_values = b"".join(
        u64(target) + u64(maximum) + u64(base_fee_update_fraction)
        for target, maximum, base_fee_update_fraction in blob_schedules
    )
    fork_config = u64(fork) + u32(16) + u32(16 + len(activation)) + activation + blob_values
    return u64(chain_id) + u32(12) + fork_config


def paired(name: str, boundary: bytes, over_bound: bytes, *, tier: str = "default") -> list[BoundaryCase]:
    return [
        BoundaryCase(Case(f"boundary-{name}-max", boundary, True), tier),
        BoundaryCase(Case(f"boundary-{name}-over", over_bound, False), tier),
    ]


def cases() -> list[BoundaryCase]:
    result: list[BoundaryCase] = []

    result += paired(
        "extra-data-32",
        make_v4(payload_kwargs={"extra_data": b"E" * 32}),
        make_v4(payload_kwargs={"extra_data": b"E" * 33}),
    )

    withdrawal_records = tuple(
        withdrawal(index, index + 100, bytes_from(index, 20), index + 1_000)
        for index in range(17)
    )
    result += paired(
        "withdrawals-16",
        make_v4(payload_kwargs={"withdrawals": withdrawal_records[:16]}),
        make_v4(payload_kwargs={"withdrawals": withdrawal_records}),
    )

    hash = bytes_from(17, 32)
    result += paired(
        "versioned-hashes-4096",
        make_v4(versioned_hashes=hash * 4096),
        make_v4(versioned_hashes=hash * 4097),
    )

    deposit = deposit_request(
        bytes_from(1, 48), bytes_from(49, 32), 0x0102_0304_0506_0708, bytes_from(81, 96), 9
    )
    result += paired(
        "deposit-requests-8192",
        make_v4(requests=execution_requests(deposits=deposit * 8192)),
        make_v4(requests=execution_requests(deposits=deposit * 8193)),
    )

    withdrawal_request_record = withdrawal_request(
        bytes_from(3, 20), bytes_from(23, 48), 0x1112_1314_1516_1718
    )
    result += paired(
        "withdrawal-requests-16",
        make_v4(requests=execution_requests(withdrawals=withdrawal_request_record * 16)),
        make_v4(requests=execution_requests(withdrawals=withdrawal_request_record * 17)),
    )

    consolidation = consolidation_request(bytes_from(4, 20), bytes_from(24, 48), bytes_from(72, 48))
    result += paired(
        "consolidation-requests-2",
        make_v4(requests=execution_requests(consolidations=consolidation * 2)),
        make_v4(requests=execution_requests(consolidations=consolidation * 3)),
    )

    result += paired(
        "witness-state-item-bytes-1024",
        make_v4(witness_bytes=witness((b"S" * 1024,), (), ())),
        make_v4(witness_bytes=witness((b"S" * 1025,), (), ())),
    )

    result += paired(
        "witness-code-item-bytes-65536",
        make_v4(witness_bytes=witness((), (b"C" * 65536,), ())),
        make_v4(witness_bytes=witness((), (b"C" * 65537,), ())),
    )

    header_items = tuple(bytes((index % 256,)) for index in range(257))
    result += paired(
        "witness-headers-count-256",
        make_v4(witness_bytes=witness((), (), header_items[:256])),
        make_v4(witness_bytes=witness((), (), header_items)),
    )

    result += paired(
        "witness-header-item-bytes-1024",
        make_v4(witness_bytes=witness((), (), (b"H" * 1024,))),
        make_v4(witness_bytes=witness((), (), (b"H" * 1025,))),
    )

    result += paired(
        "activation-block-number-1",
        make_v4(chain_bytes=raw_chain_config(activation_blocks=(0x0102_0304_0506_0708,))),
        make_v4(
            chain_bytes=raw_chain_config(
                activation_blocks=(0x0102_0304_0506_0708, 0x1112_1314_1516_1718)
            )
        ),
    )

    result += paired(
        "activation-timestamp-1",
        make_v4(chain_bytes=raw_chain_config(activation_timestamps=(0x2122_2324_2526_2728,))),
        make_v4(
            chain_bytes=raw_chain_config(
                activation_timestamps=(0x2122_2324_2526_2728, 0x3132_3334_3536_3738)
            )
        ),
    )

    result += paired(
        "blob-schedule-1",
        make_v4(chain_bytes=raw_chain_config(blob_schedules=((1, 2, 3),))),
        make_v4(chain_bytes=raw_chain_config(blob_schedules=((1, 2, 3), (4, 5, 6)))),
    )

    public_key = bytes([4]) + bytes_from(1, 64)
    result += paired(
        "public-keys-32768",
        make_v4(public_keys=public_key * 32768),
        make_v4(public_keys=public_key * 32769),
    )

    result += paired(
        "witness-codes-count-262144",
        make_v4(witness_bytes=raw_witness(codes=empty_byte_list_list(1 << 18))),
        make_v4(witness_bytes=raw_witness(codes=empty_byte_list_list((1 << 18) + 1))),
        tier="extended",
    )

    return result


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
    parser.add_argument(
        "--extended",
        action="store_true",
        help="also run the 2**18-item witness.codes boundary pair",
    )
    return parser.parse_args()


def show_outcome(boundary: BoundaryCase, outcomes: dict[str, Outcome]) -> None:
    values = " ".join(
        f"{adapter}={outcome.returncode}:{len(outcome.stdout)}B" for adapter, outcome in outcomes.items()
    )
    print(f"{boundary.case.name}\t{'valid' if boundary.case.valid else 'invalid'}\t{values}")


def main() -> int:
    args = parse_args()
    for path in (args.reference_python, args.zesu_value_binary, args.lean_binary, args.reference_program):
        if not path.is_file():
            raise SystemExit(f"required path does not exist or is not a file: {path}")

    failures: list[str] = []
    selected = [case for case in cases() if args.extended or case.tier == "default"]
    for boundary in selected:
        case = boundary.case
        outcomes = {
            "python": run([str(args.reference_python), str(args.reference_program)], case.data),
            "lean": run_lean(args.lean_binary, case.data),
            "zesu": run([str(args.zesu_value_binary)], case.data),
        }
        show_outcome(boundary, outcomes)
        if case.valid:
            if any(outcome.returncode != 0 for outcome in outcomes.values()):
                failures.append(f"{case.name}: valid input rejected")
                continue
            if any(not valid_protocol(outcome.stdout) for outcome in outcomes.values()):
                failures.append(f"{case.name}: malformed ssz-value-v1 output")
                continue
            streams = {adapter: outcome.stdout for adapter, outcome in outcomes.items()}
            if len(set(streams.values())) != 1:
                failures.append(f"{case.name}: value mismatch")
        elif any(outcome.returncode == 0 for outcome in outcomes.values()):
            accepted = ", ".join(adapter for adapter, outcome in outcomes.items() if outcome.returncode == 0)
            failures.append(f"{case.name}: malformed input accepted by {accepted}")

    if failures:
        print("strict V4 boundary differential failed:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1
    tier = "extended" if args.extended else "default"
    print(f"strict V4 boundary differential ({tier}): ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
