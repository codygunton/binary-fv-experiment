#!/usr/bin/env python3
"""Capture a deterministic execution trace of the unchanged production RV64 `zesu-ssz` ELF.

Runs the pinned `qemu-riscv64` (user mode) with the pinned `qemu_trace_plugin.so` over an SSZ input fed
on stdin, and writes the plugin's `(pc | pc,addr,width,value)` trace to `--out`. `setarch -R`
stabilizes repeated captures on one host; the reducer normalizes stack addresses relative to entry SP
because absolute guest-stack placement can still differ across hosts. Code/input/heap addresses are
static (`-no-pie`, static globals) and remain exact. The ELF is never rebuilt, relinked, patched, or
instrumented: the plugin only observes.

An optional `[--lo, --hi)` PC window keeps a vertical-slice trace small. The ELF's own stdout
(`ok <checksum>` / `invalid`) is written to `--elf-stdout` if given, else discarded; the process exit
status is returned. Diagnostic-only evidence; never imported by the proof.
"""
from __future__ import annotations

import argparse
import subprocess
import sys


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qemu", required=True, help="pinned qemu-riscv64 (user mode)")
    ap.add_argument("--plugin", required=True, help="pinned qemu_trace_plugin.so")
    ap.add_argument("--elf", required=True, help="the unchanged production zesu-ssz ELF")
    ap.add_argument("--input", required=True, help="SSZ input bytes fed on stdin")
    ap.add_argument("--out", required=True, help="trace log output path")
    ap.add_argument("--lo", type=lambda s: int(s, 0), default=None, help="window PC start (inclusive)")
    ap.add_argument("--hi", type=lambda s: int(s, 0), default=None, help="window PC end (exclusive)")
    ap.add_argument("--elf-stdout", default=None, help="capture the ELF's stdout here")
    a = ap.parse_args()

    plugin_arg = f"{a.plugin},out={a.out}"
    if a.lo is not None:
        plugin_arg += f",lo={a.lo}"
    if a.hi is not None:
        plugin_arg += f",hi={a.hi}"

    with open(a.input, "rb") as stdin:
        result = subprocess.run(
            ["setarch", "-R", a.qemu, "-plugin", plugin_arg, a.elf],
            stdin=stdin, capture_output=True,
        )
    if a.elf_stdout is not None:
        with open(a.elf_stdout, "wb") as fh:
            fh.write(result.stdout)
    if result.returncode not in (0, 1):  # 0 = accept, 1 = reject; anything else is a harness failure
        sys.stderr.write(result.stderr.decode(errors="replace"))
        sys.stderr.write(f"\ncapture_trace: unexpected qemu exit {result.returncode}\n")
        return 2
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
