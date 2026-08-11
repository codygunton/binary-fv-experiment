#!/usr/bin/env python3
"""Run and summarize the Level 4 deinit Lean profiler used by the reuse study."""

from __future__ import annotations

import re
import subprocess
import time


COMMAND = [
    "lake", "env", "lean", "--tstack=65536", "-Dtrace.profiler=true",
    "-Dtrace.profiler.threshold=400",
    "BinaryFv/Zesu/MachineExecution/Level4RawNewPayloadRequestDeinitSteps.lean",
]
TOP_LEVEL = re.compile(
    r"^\[Elab\.async\] \[([0-9.]+)\] elaborating proof of (\S+)", re.MULTILINE
)


def main() -> int:
    started = time.monotonic()
    result = subprocess.run(COMMAND, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - started
    reports = sorted(
        ((float(seconds), name.rsplit(".", 1)[-1]) for seconds, name in TOP_LEVEL.findall(result.stdout)),
        reverse=True,
    )
    print(f"wall_seconds={elapsed:.2f} exit={result.returncode}")
    print("largest_async_proofs_seconds_overlapping=true")
    for seconds, name in reports[:10]:
        print(f"{seconds:.2f} {name}")
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
