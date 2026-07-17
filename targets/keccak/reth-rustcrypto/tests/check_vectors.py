#!/usr/bin/env python3
"""Run the RV64 Reth/RustCrypto wrapper against independently recorded Keccak vectors."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--qemu", required=True)
    parser.add_argument("--binary", required=True)
    parser.add_argument("--vectors", required=True)
    args = parser.parse_args()

    vectors = json.load(open(args.vectors, encoding="utf-8"))
    for vector in vectors:
        message = bytes(range(vector["length"])).hex()
        completed = subprocess.run(
            [args.qemu, args.binary, message],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        actual = completed.stdout.strip()
        if completed.returncode != 0 or actual != vector["digest"]:
            sys.stderr.write(
                f"Keccak vector length {vector['length']} failed: "
                f"exit={completed.returncode} expected={vector['digest']} actual={actual} "
                f"stderr={completed.stderr.strip()}\n"
            )
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
