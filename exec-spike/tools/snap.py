#!/usr/bin/env python3
"""Entry/return snapshots of F1 and F2 under Unicorn, for `zesu-difftest` (plan S2 step 4).

    snap.py --runner <zesislar>/tools/oblig/exec/run.py --fn F1|F2 [--elf ELF] [--inputs FILE ...]
            [--input ID ...] --out DIR

Imports zesislar's Unicorn runner `run.py` as a module and runs its profile (`keysEnsureCapacity`
for F1, `decodeItem` for F2) on each input of the given input sets (runner schema
`oblig-exec-inputs/1`; default: `inputs/<profile>.json` beside `run.py`; `tools/snap_inputs/`
adds F1 paths the runner's set lacks). Unlike `run.py`, the allocator entries are not hooked:
Unicorn executes the real `alt_fl_alloc.{alloc,remap,free}` reached through the vtable; only the
`memcpy` stub is replaced, by the runner's ZisK service hook.

Writes `DIR/<Fn>/<input id>.json`, schema `zesu-snap/1`:

    {"schema", "fn", "symbol", "elf_sha256", "input", "stop", "unicorn_insns",
     "entry": {"pc", "regs": [x1..x31], "mem": [{"base", "hex"}]},
     "exit":  {"pc", "regs": [x1..x31], "changed": [{"base", "hex"}]}}

`entry.mem`: every byte (zero or not) of every 4 KiB page, clipped to rodata, input and RAM, that the
run reads or writes (including `memcpy` source, destination and the ZisK scratch word) or that holds
an argument range or initialised ELF data. The machine's memory is partial, so this lists every
byte the run needs present. `exit.changed`: the bytes of those pages that differ at the return.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

FNS = {'F1': 'keysEnsureCapacity', 'F2': 'decodeItem'}
PAGE = 0x1000
# Readable regions of `ZesuExec.Layout` (half-open): rodata, input, RAM.
REGIONS = [(0x8010fd80, 0x80118678), (0x40000000, 0x80000000), (0xa0000000, 0xc0000000)]


def load_runner(path: Path):
    spec = importlib.util.spec_from_file_location('zesislar_exec_run', path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def runs(a: int, data: bytes) -> list[dict]:
    """Maximal runs of the given bytes starting at `a` as `{"base", "hex"}` rows."""
    return [{'base': a, 'hex': data.hex()}] if data else []


def changed_runs(base: int, before: bytes, after: bytes) -> list[dict]:
    out, i, n = [], 0, len(before)
    while i < n:
        if before[i] == after[i]:
            i += 1
            continue
        j = i
        while j < n and before[j] != after[j]:
            j += 1
        out.append({'base': base + i, 'hex': after[i:j].hex()})
        i = j
    return out


def page_spans(pages: set[int]) -> list[tuple[int, int]]:
    """Merge pages into spans and clip them to the readable regions."""
    spans: list[list[int]] = []
    for p in sorted(pages):
        lo = p * PAGE
        if spans and spans[-1][1] == lo:
            spans[-1][1] = lo + PAGE
        else:
            spans.append([lo, lo + PAGE])
    out = []
    for lo, hi in spans:
        for rlo, rhi in REGIONS:
            a, b = max(lo, rlo), min(hi, rhi)
            if a < b:
                out.append((a, b))
    return out


def add_range(pages: set[int], a: int, n: int):
    if n > 0:
        pages.update(range(a // PAGE, (a + n - 1) // PAGE + 1))


def regs(r, m) -> list[int]:
    return [m.reg(r.XREG[i]) for i in range(1, 32)]


def snapshot(r, elf, fn: str, row: dict, max_insns: int) -> dict:
    profile = r.PROFILES[FNS[fn]]

    def machine():
        m = r.Machine(elf, profile, row, [], None, 'top', max_insns)
        m.stubs = {elf.sym('memcpy'): m._memcpy}   # real alloc, remap, free
        return m

    m0, m = machine(), machine()
    pages: set[int] = set()

    def on_access(uc, access, addr, size, value, _):
        add_range(pages, addr, size)

    m.uc.hook_add(r.UC_HOOK_MEM_READ | r.UC_HOOK_MEM_WRITE, on_access)
    entry = {'pc': m.reg(r.R.UC_RISCV_REG_PC), 'regs': regs(r, m)}
    m.run()
    for c in m.memcpy:
        add_range(pages, c['src'], c['len'])
        add_range(pages, c['dst'], c['len'])
    add_range(pages, r.ZISK_SCRATCH, 8)
    for _, base, size, _ in m.ranges:
        add_range(pages, base, size)
    for vaddr, memsz, data in elf.segments:
        if r.RAM[0] <= vaddr < r.RAM[1] and any(data):
            add_range(pages, vaddr, len(data))
    spans = page_spans(pages)
    entry['mem'] = [row_ for lo, hi in spans for row_ in runs(lo, m0.read(lo, hi - lo))]
    changed = [c for lo, hi in spans for c in changed_runs(lo, m0.read(lo, hi - lo), m.read(lo, hi - lo))]
    return {'schema': 'zesu-snap/1', 'fn': fn, 'symbol': profile.symbol, 'elf_sha256': elf.sha256,
            'input': row['id'], 'stop': m.stop, 'unicorn_insns': m.insns,
            'outcome': profile.outcome(m, row), 'unmapped': len(m.unmapped),
            'entry': entry,
            'exit': {'pc': m.reg(r.R.UC_RISCV_REG_PC), 'regs': regs(r, m), 'changed': changed}}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--runner', type=Path, required=True, help="zesislar's tools/oblig/exec/run.py")
    ap.add_argument('--fn', required=True, choices=sorted(FNS))
    ap.add_argument('--elf', type=Path, help="default: the runner's DEFAULT_ELF")
    ap.add_argument('--inputs', type=Path, action='append',
                    help="input sets (repeatable; default: inputs/<profile>.json beside the runner)")
    ap.add_argument('--input', action='append', help='only these input ids')
    ap.add_argument('--max-insns', type=int, default=1_000_000)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args(argv)
    r = load_runner(args.runner.resolve())
    elf = r.Elf(args.elf or r.DEFAULT_ELF)
    rows = []
    for f in args.inputs or [args.runner.parent / 'inputs' / f'{FNS[args.fn]}.json']:
        spec = json.loads(f.read_text())
        if spec.get('function') != FNS[args.fn]:
            raise SystemExit(f'{f}: inputs are for {spec.get("function")!r}, not {FNS[args.fn]!r}')
        rows += [row for row in spec['inputs'] if not args.input or row['id'] in args.input]
    out = args.out / args.fn
    out.mkdir(parents=True, exist_ok=True)
    bad = 0
    for row in rows:
        s = snapshot(r, elf, args.fn, row, args.max_insns)
        (out / f"{row['id']}.json").write_text(json.dumps(s) + '\n')
        nbytes = sum(len(x['hex']) // 2 for x in s['entry']['mem'])
        nchg = sum(len(x['hex']) // 2 for x in s['exit']['changed'])
        print(f"{args.fn}\t{row['id']}\t{s['stop']}\t{s['outcome'].get('kind')}\tinsns={s['unicorn_insns']}\t"
              f"entry_bytes={nbytes}\tchanged={nchg}\tunmapped={s['unmapped']}")
        bad += s['stop'] != 'returned'
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
