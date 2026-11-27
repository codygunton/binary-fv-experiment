#!/usr/bin/env python3
"""Entry/return snapshots of F1, F2, TX and DTF under Unicorn, for `zesu-difftest` (plan S2 step 4).

    snap.py --runner <zesislar>/tools/oblig/exec/run.py --fn F1|F2|TX|DTF [--elf ELF] [--inputs FILE ...]
            [--input ID ...] --out DIR

Imports zesislar's Unicorn runner `run.py` as a module and runs its profile (`keysEnsureCapacity`
for F1, `decodeItem` for F2, `txAccessList` for TX; DTF uses `dtf_profile` below, the runner has
none) on each input of the given input sets (runner schema `oblig-exec-inputs/1`; default:
`inputs/<profile>.json` beside `run.py`, for DTF `tools/snap_inputs/decodeTxFields.json`;
`tools/snap_inputs/` adds F1 paths the runner's set lacks). Unlike `run.py`, the allocator entries are not hooked:
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

FNS = {'F1': 'keysEnsureCapacity', 'F2': 'decodeItem', 'TX': 'txAccessList', 'DTF': 'decodeTxFields'}
PAGE = 0x1000
# Readable regions of `ZesuExec.Layout` (half-open): rodata, input, RAM.
REGIONS = [(0x8010fd80, 0x80118678), (0x40000000, 0x80000000), (0xa0000000, 0xc0000000)]


def load_runner(path: Path):
    spec = importlib.util.spec_from_file_location('zesislar_exec_run', path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def dtf_profile(r):
    """`rlp_decode.decodeTxFields` (zesislar's runner has no profile for it).

    a0 = result `anyerror!input.Transaction` (0x128 bytes; u16 error code at +0x120), a1 = allocator
    object `{ctx, vtable}`, a2 = `tx_type` (input field `tx_type`, 0-4), a3/a4 = the payload slice
    (input field `hex`: the content of the transaction's RLP list). Layout of `input.Transaction`
    from the debug object (`OPEN/DTF/BLOCKERS.md`, `ZesuExec/Fn/DTF/Spec.lean`).
    """
    import struct

    class DecodeTxFields(r.Profile):
        name, symbol = 'decodeTxFields', 'rlp_decode.decodeTxFields'
        oom_expect = {'kind': 'Error'}

        def setup(self, m, row):
            data = bytes.fromhex(row['hex'])
            m.own('input', r.DATA_PTR, len(data), False, data)
            allocator = r.allocator_cells(m, r.CELLS + 0x20)
            m.own('result', r.RESULT_PTR, 0x128, True, b'\xaa' * 0x128)
            return [r.RESULT_PTR, allocator, row['tx_type'], r.DATA_PTR, len(data)]

        def outcome(self, m, row):
            res = m.read(r.RESULT_PTR, 0x128)
            err = struct.unpack_from('<H', res, 0x120)[0]
            if err != 0:
                return {'kind': 'Error' if err == 3 else f'Other(err={err})', 'err': err}
            le = lambda o, n: int.from_bytes(res[o:o + n], 'little')  # noqa: E731
            opt = lambda o, n, t: le(o, n) if res[t] == 1 else None  # noqa: E731
            sl = lambda o: (le(o, 8), le(o + 8, 8))  # noqa: E731
            (dp, dn), (ap, an), (bp, bn), (up, un) = sl(0xc0), sl(0xd0), sl(0xe0), sl(0xf0)
            return {'kind': 'Success', 'err': 0, 'tx_type': res[0x108], 'chain_id': opt(0xa0, 8, 0xa8),
                    'nonce': le(0xb0, 8), 'gas_price': le(0, 16),
                    'gas_priority_fee': opt(0x10, 16, 0x20), 'gas_limit': le(0xb8, 8),
                    'to': res[0x109:0x11d].hex() if res[0x11d] == 1 else None, 'value': le(0x30, 32),
                    'data': m.read(dp, dn).hex() if dn else '', 'access_list_len': an,
                    'blob_hashes': [m.read(bp + 32 * k, 32).hex() for k in range(bn)],
                    'max_fee_per_blob_gas': le(0x50, 16), 'authorizations': un, 'v': le(0x100, 8),
                    'r': le(0x60, 32), 's': le(0x80, 32)}

    return DecodeTxFields()


def profile_for(r, fn: str):
    return dtf_profile(r) if fn == 'DTF' else r.PROFILES[FNS[fn]]


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
    profile = profile_for(r, fn)

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
    default = (Path(__file__).parent / 'snap_inputs' / 'decodeTxFields.json' if args.fn == 'DTF'
               else args.runner.parent / 'inputs' / f'{FNS[args.fn]}.json')
    for f in args.inputs or [default]:
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
