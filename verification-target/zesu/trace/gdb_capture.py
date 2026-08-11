#!/usr/bin/env python3
"""Batch-GDB capture of RV64 registers and selected memory at binding-defined boundary PCs.

Independent of the trace plugin (a second, separate evidence channel): drive the pinned `qemu-riscv64`
gdbstub with a RISC-V GDB, break at each boundary PC, and record all 32 integer registers + `pc` at
every stop, plus selected memory windows (each read as bytes). `setarch -R` stabilizes repeated runs
on one host; the evidence reducer separately normalizes stack addresses relative to entry SP because
absolute guest-stack placement can differ across hosts. The production ELF is only OBSERVED — never
rebuilt, relinked, patched, or instrumented.

Inline exits are captured AFTER the outgoing edge (stops at the continuation target PC). Output is
deterministic JSON. Diagnostic-only; never imported by the proof.

Memory windows (`--mem`): `<addr-or-$reg[+off]>:<len>`, read at every stop.
"""
from __future__ import annotations

import argparse
import json
import os
import socket
import subprocess
import sys
import tempfile
import time


GDB_DRIVER = r'''
python
import json, gdb
regs = ["x%d" % i for i in range(32)]
mem_specs = __MEM_SPECS__
max_stops = __MAX_STOPS__
out_path = __OUT_PATH__

def read_windows():
    windows = []
    for spec in mem_specs:
        loc, length = spec.rsplit(":", 1)
        length = int(length, 0)
        if loc.startswith("0x") or loc.lstrip("-").isdigit():
            addr = int(loc, 0)
        else:
            addr = int(gdb.parse_and_eval(loc)) & (2**64 - 1)
        # A boundary register may not hold a pointer at every stop; record null rather than aborting.
        try:
            data = bytes(gdb.selected_inferior().read_memory(addr, length))
            windows.append({"spec": spec, "addr": addr, "bytes": data.hex()})
        except (gdb.MemoryError, gdb.error):
            windows.append({"spec": spec, "addr": addr, "bytes": None})
    return windows

stops = []
gdb.execute("continue")
while len(stops) < max_stops:
    try:
        pc = int(gdb.selected_frame().pc()) & (2**64 - 1)
    except gdb.error:
        break
    rv = {r: int(gdb.parse_and_eval("$" + r)) & (2**64 - 1) for r in regs}
    rv["pc"] = pc
    stops.append({"pc": pc, "index": len(stops), "registers": rv, "memory": read_windows()})
    try:
        gdb.execute("continue")
    except gdb.error:
        break

with open(out_path, "w") as fh:
    fh.write(json.dumps({"stops": stops}, indent=1, sort_keys=True) + "\n")
end
kill
quit
'''


def _free_port() -> int:
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    port = s.getsockname()[1]
    s.close()
    return port


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qemu", required=True)
    ap.add_argument("--gdb", required=True)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--input", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--pc", type=lambda s: int(s, 0), action="append", default=[],
                    help="a boundary PC to break at (repeatable)")
    ap.add_argument("--mem", action="append", default=[], help="a memory window '<addr|$reg[+off]>:len'")
    ap.add_argument("--max-stops", type=int, default=256)
    a = ap.parse_args()

    port = _free_port()
    with open(a.input, "rb") as stdin:
        qemu = subprocess.Popen(
            ["setarch", "-R", a.qemu, "-g", str(port), a.elf],
            stdin=stdin, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
    # qemu -g starts SUSPENDED, listening for the single gdb connection; do NOT probe the port (that
    # would consume the connection). A short settle is enough for the TCP listen to be up; gdb also
    # retries the connect below.
    time.sleep(0.4)

    prelude = [
        "set pagination off", "set confirm off", "set debuginfod enabled off",
        "set tcp connect-timeout 30",
        "set architecture riscv:rv64",
    ] + [f"target remote :{port}"] + [f"break *{pc}" for pc in a.pc]
    driver = (GDB_DRIVER
              .replace("__MEM_SPECS__", repr(a.mem))
              .replace("__MAX_STOPS__", str(a.max_stops))
              .replace("__OUT_PATH__", repr(a.out)))
    with tempfile.NamedTemporaryFile("w", suffix=".gdb", delete=False) as fh:
        fh.write("\n".join(prelude) + "\n" + driver)
        cmd_file = fh.name

    try:
        gdb_proc = subprocess.run([a.gdb, "-q", "-nx", "-batch", "-x", cmd_file],
                                  capture_output=True, text=True, timeout=60)
    finally:
        os.unlink(cmd_file)
        try:
            qemu.wait(timeout=10)
        except subprocess.TimeoutExpired:
            qemu.kill()

    if not os.path.exists(a.out):
        sys.stderr.write(gdb_proc.stdout[-3000:])
        sys.stderr.write(gdb_proc.stderr[-2000:])
        sys.stderr.write("\ngdb_capture: no output produced\n")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
