#!/usr/bin/env python3
"""Each ZisK service definition of `ZesuExec/Service/` against `ziskemu` (plan S14).

    svc_test.py [--n 100] [--seed 14] [--check NAME ...] [--ziskemu PATH] [--json OUT]

For every check, `n` random cases. A case is an initial machine (register values, byte regions)
and an instruction pattern. The pattern runs twice:

* in `ziskemu`: a generated RISC-V program (`riscv64-elf-gcc`) copies the regions into RAM, sets
  the registers, executes the pattern, copies the observed regions and registers to `OUTPUT_ADDR`
  and exits; `ziskemu -c` prints the 256 output bytes;
* in Lean: `lake env lean` evaluates the registry (`ZesuExec.svc`, `ZesuExec.ziskExit`) on the same
  machine and prints the same bytes.

A check passes when the bytes agree on every case. Parts of a dump are compared separately
(`parts`), so a divergence in one part (e.g. the `memcpy` staging word,
`OPEN/services/extra_params.md`) is reported without hiding the rest.

`ziskemu` is built from `/home/cody/zisk` (`eed62f4d9`) as recorded in `LOG.md` (S14); it needs
`LD_LIBRARY_PATH` to find `libiomp5.so`.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
# `ziskemu` of ZisK eed62f4d9 (LOG.md S14 records the build); `--ziskemu` selects another build,
# e.g. `ziskemu-relaxed12` (the same with the `inst_size` assertion of
# `riscv2zisk_context.rs:695` admitting 12, which the immediate-count `memset` form needs).
ZISKEMU = '/home/cody/.cache/zesu-tmp/ziskemu-eed62f4d9'
LIBDIR = '/home/cody/.local/lib'
OUTPUT_ADDR = 0xa0010000
PAT_PC = 0x80001000          # where the Lean image holds the pattern
WIN = 0xa0100000             # data window
EXTRA_ZISK = 0xa0000f00      # EXTRA_PARAMS_ADDR, core/src/mem.rs:147 = Layout.extraParams
EXTRA_OLD = 0xa0400f00       # Layout.extraParams before the correction; must stay untouched
MARCHID_ADDR = 0xa0008000 + 8 * 0xf12
ARCH_ID = 0xFFFEEEE
POOL = [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17]   # registers a pattern may use; all dumped
REGNAME = {5: 't0', 6: 't1', 7: 't2', 10: 'a0', 11: 'a1', 12: 'a2', 13: 'a3', 14: 'a4',
           15: 'a5', 16: 'a6', 17: 'a7'}


# -- encodings ------------------------------------------------------------------------------------
def csrrs(rd, csr, rs1):
    return (csr << 20) | (rs1 << 15) | (2 << 12) | (rd << 7) | 0x73


def csrrsi(rd, csr, uimm):
    return (csr << 20) | (uimm << 15) | (6 << 12) | (rd << 7) | 0x73


def add(rd, rs1, rs2):
    return (rs2 << 20) | (rs1 << 15) | (rd << 7) | 0x33


def addi(rd, rs1, imm):
    return ((imm & 0xfff) << 20) | (rs1 << 15) | (rd << 7) | 0x13


# -- cases ----------------------------------------------------------------------------------------
class Case:
    """regs: {x: value}; regions: [(addr, bytes)]; words: pattern; plen: bytes the pattern spans;
    dump: [(name, addr, len)] regions observed after the pattern (regs are always dumped)."""

    def __init__(self, regs, regions, words, plen, dump, exit_only=False, fn=None, mask=(),
                 extra=None, pool=POOL, ret_bit=None, unchanged=(), expect=None, alt=()):
        self.regs, self.regions, self.words, self.plen = regs, regions, words, plen
        self.dump, self.exit_only = dump, exit_only
        # fn: call the binary's own function (its words at their addresses) instead of a pattern;
        # mask: registers the contract leaves unconstrained (not compared); pool: registers dumped
        self.fn, self.mask, self.pool = fn, mask, pool
        # extra: {abi name: value} set before the call and dumped after the pool registers
        self.extra = extra or {}
        # ret_bit: call with `ra = ret_ok + ret_bit` and dump 1 when the callee lands on `ret_ok`
        # (the return clause, pc = ra & ~1)
        self.ret_bit = ret_bit
        # unchanged: [(name, region index, [(lo, hi)] offsets the contract may write)]; after the
        # call the program counts the bytes of the region that differ from their initial value
        # outside those ranges (8 bytes, little-endian)
        self.unchanged = unchanged
        # expect: {part: bytes} parts compared against a Python expectation instead of Lean;
        # alt: [(name, part, bytes, must_differ)] further comparisons of a dumped part
        self.expect, self.alt = expect or {}, alt


def rbytes(rng, n):
    return bytes(rng.randrange(256) for _ in range(n))


def pick(rng, k):
    return rng.sample(POOL, k)


def base_regs(rng):
    return {r: rng.getrandbits(64) for r in POOL}


def case_813_reg(rng):
    rs, rd, rn = pick(rng, 3)
    od, os_ = rng.randrange(64), rng.randrange(64)
    if rng.random() < 0.1:
        os_ = od
    n = rng.randrange(0, 64 - max(od, os_) + 1)
    regs = base_regs(rng)
    regs.update({rs: WIN + os_, rd: WIN + od, rn: n})
    regions = [(WIN, rbytes(rng, 64)), (EXTRA_ZISK, rbytes(rng, 8)), (EXTRA_OLD, rbytes(rng, 8))]
    return Case(regs, regions, [csrrs(0, 0x813, rs), add(0, rd, rn)], 8,
                [('window', WIN, 64), ('staging@0xa0000f00', EXTRA_ZISK, 8),
                 ('old@0xa0400f00', EXTRA_OLD, 8)])


def case_813_imm(rng):
    rs, rd = pick(rng, 2)
    od, os_ = rng.randrange(64), rng.randrange(64)
    n = rng.randrange(0, 64 - max(od, os_) + 1)
    regs = base_regs(rng)
    regs.update({rs: WIN + os_, rd: WIN + od})
    return Case(regs, [(WIN, rbytes(rng, 64))], [csrrs(0, 0x813, rs), addi(0, rd, n)], 8,
                [('window', WIN, 64)])


def case_816_reg(rng):
    rd, rn = pick(rng, 2)
    od = rng.randrange(64)
    n = rng.randrange(0, 64 - od + 1)
    regs = base_regs(rng)
    regs.update({rd: WIN + od, rn: n})
    return Case(regs, [(WIN, rbytes(rng, 64))],
                [csrrs(0, 0x816, rd), addi(0, rn, rng.randrange(256))], 8, [('window', WIN, 64)])


def case_816_imm(rng):
    (rd,) = pick(rng, 1)
    od = rng.randrange(64)
    n = rng.randrange(0, 64 - od + 1)
    regs = base_regs(rng)
    regs[rd] = WIN + od
    return Case(regs, [(WIN, rbytes(rng, 64))],
                [csrrsi(0, 0x816, 2), addi(0, rd, n), addi(0, rd, rng.randrange(256))], 12,
                [('window', WIN, 64)])


def case_805(rng):
    (rp,) = pick(rng, 1)
    p, st, inp = WIN, WIN + 0x40, WIN + 0x80
    if rng.random() < 0.5:
        st, inp = inp, st
    regs = base_regs(rng)
    regs[rp] = p
    params = st.to_bytes(8, 'little') + inp.to_bytes(8, 'little')
    regions = [(p, params), (WIN + 0x40, rbytes(rng, 64)), (WIN + 0x80, rbytes(rng, 64))]
    return Case(regs, regions, [csrrs(0, 0x805, rp)], 4, [('state', st, 32), ('block', inp, 64)])


def case_f12(rng):
    (rd,) = pick(rng, 1)
    regs = base_regs(rng)
    marchid = (MARCHID_ADDR, ARCH_ID.to_bytes(8, 'little'))   # ZiskBoot (Lean side only)
    return Case(regs, [marchid], [csrrs(rd, 0xf12, 0)], 4, [])


def case_exit(rng):
    regs = base_regs(rng)
    regs[17] = 93
    return Case(regs, [(OUTPUT_ADDR, rbytes(rng, 256))], [0x73], 0, [], exit_only=True)


ELF = '/home/cody/zesislar/build/stock-zisk/zesu-zisk.elf'
FN_LO, FN_HI = 0x800e06d0, 0x800e06f0 + 4 * 1036      # memmove, memset
FN = {'memmove': 0x800e06d0, 'memset': 0x800e06f0, 'sha256': 0x800ea180}
_FN_WORDS = None


def fn_words():
    """The words of `memmove` and `memset` from the ELF."""
    global _FN_WORDS
    if _FN_WORDS is None:
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / 'text.bin'
            subprocess.run(['riscv64-elf-objcopy', '-O', 'binary', '--only-section=.text', ELF,
                            str(out)], check=True)
            data = out.read_bytes()
        base = 0x80000000
        _FN_WORDS = [int.from_bytes(data[a - base:a - base + 4], 'little')
                     for a in range(FN_LO, FN_HI, 4)]
    return _FN_WORDS


def case_fn_memmove(rng):
    regs = base_regs(rng)
    od, os_ = rng.randrange(64), rng.randrange(64)
    n = rng.randrange(0, 64 - max(od, os_) + 1)
    regs.update({10: WIN + od, 11: WIN + os_, 12: n})
    regions = [(WIN, rbytes(rng, 64)), (EXTRA_ZISK, rbytes(rng, 8)), (EXTRA_OLD, rbytes(rng, 8))]
    return Case(regs, regions, [], 0, [('window', WIN, 64), ('staging@0xa0000f00', EXTRA_ZISK, 8),
                                       ('old@0xa0400f00', EXTRA_OLD, 8)], fn='memmove')


def case_fn_memset(rng):
    regs = base_regs(rng)
    od = rng.randrange(64)
    n = rng.randrange(0, 64 - od + 1)
    if rng.random() < 0.15:
        regs[11] = 0
    elif rng.random() < 0.15:
        regs[11] = rng.randrange(256) << 8      # nonzero, low byte 0
    regs.update({10: WIN + od, 12: n})
    return Case(regs, [(WIN, rbytes(rng, 64))], [], 0, [('window', WIN, 64)], fn='memset',
                mask=(5, 11))


SHA_OUT = 0xa0200000
SHA_GLOBALS = 0xa05340b8     # Sha256.bump
SHA_FRAME = 0xe0             # Sha256.frameSize
SHA_IN = 512                 # input window: lengths 0..300 at offsets 0..7
SHA_LENS = [0, 55, 56, 63, 64, 119, 120, 128]     # padding and block boundaries
SHA_STACK_BELOW, SHA_STACK_ABOVE = 0x200, 0x100
SCRATCH = 0xa0600000         # `gp`: where the rev8 stubs spill (outside every window)
CALLEE_SAVED = ['sp', 's0', 's1', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11']


def case_fn_sha256(rng, i):
    """Every clause of `Sha256.Post` the emulator can observe. Cases 0..15: the lengths of
    `SHA_LENS`, each with an 8-aligned and an unaligned input; then random lengths 0..300."""
    regs = base_regs(rng)
    if i < 2 * len(SHA_LENS):
        n, off = SHA_LENS[i // 2], (0 if i % 2 == 0 else rng.randrange(1, 8))
    else:
        n, off = rng.randrange(0, 301), rng.choice([0, rng.randrange(1, 8)])
    oo = rng.randrange(8)
    regs.update({10: WIN + off, 11: n, 12: SHA_OUT + oo})
    extra = {name: rng.getrandbits(64) for name in CALLEE_SAVED}
    sp = 0xa0300000 + 16 * rng.randrange(256)
    extra['sp'] = sp
    inp = rbytes(rng, SHA_IN)
    regions = [(WIN, inp), (SHA_OUT - 64, rbytes(rng, 160)),
               (sp - SHA_STACK_BELOW, rbytes(rng, SHA_STACK_BELOW + SHA_STACK_ABOVE)),
               (SHA_GLOBALS - 64, rbytes(rng, 144)), (EXTRA_ZISK, rbytes(rng, 256))]
    unchanged = [('unchanged input [a0-off, +512)', 0, []),
                 ('unchanged out-64..out+96 except out', 1, [(64 + oo, 96 + oo)]),
                 ('unchanged sp-0x200..sp+0x100 except frame', 2,
                  [(SHA_STACK_BELOW - SHA_FRAME, SHA_STACK_BELOW)]),
                 ('unchanged bump-64..bump+80 except bump', 3, [(64, 80)]),
                 ('unchanged extra params 0xa0000f00+256 except staging', 4, [(0, 8)])]
    h = hashlib.sha256(inp[off:off + n]).digest()
    k = rng.randrange(32)
    flipped = h[:k] + bytes([h[k] ^ rng.randrange(1, 256)]) + h[k + 1:]
    expect = {'returned to ra': (1).to_bytes(8, 'little')}
    expect.update({name: bytes(8) for name, _, _ in unchanged})
    return Case(regs, regions, [], 0, [('digest', SHA_OUT + oo, 32), ('bump words', SHA_GLOBALS, 16)],
                fn='sha256', pool=[10], extra=extra, ret_bit=rng.randrange(2), unchanged=unchanged,
                expect=expect, alt=[('digest = hashlib', 'digest', h, False),
                                    ('flipped hashlib digest rejected', 'digest', flipped, True)])


case_fn_sha256.indexed = True


CHECKS = {
    '0x813-reg': (case_813_reg, 'csr813, register count (memcpy, memmove, inline sites)'),
    '0x813-imm': (case_813_imm, 'csr813, immediate count'),
    '0x816-reg': (case_816_reg, 'csr816, register count (memset)'),
    '0x816-imm': (case_816_imm, 'csr816, immediate count'),
    '0x805': (case_805, 'csr805, SHA-256 compression'),
    '0xf12': (case_f12, 'csrF12, marchid read after ZiskBoot'),
    'exit': (case_exit, 'ziskExit, public output of the exit ecall'),
    'fn-memmove': (case_fn_memmove, 'memmove (0x800e06d0) run by ziskemu vs MemcpyPost (ziskMemcpy)'),
    'fn-memset': (case_fn_memset, 'memset (0x800e06f0) run by ziskemu vs Memset.Post'),
    'fn-sha256': (case_fn_sha256, 'zkvm_sha256 (0x800ea180) run by ziskemu (rev8 sites through '
                  'harness stubs) vs Sha256.Post: digest (Lean Sha256.hash and hashlib), a0, '
                  'callee-saved, return to ra, bump words, memory outside Written (needs a ziskemu '
                  'that loads csrsi 0x816,2)'),
}


# -- the ziskemu side -----------------------------------------------------------------------------
LINK_MEM = """ENTRY(_start)
PHDRS { text PT_LOAD FLAGS(5); fn PT_LOAD FLAGS(5); rodata PT_LOAD FLAGS(4); }
SECTIONS { . = 0x80120000; .text : { *(.text) } :text
           . = 0x800e06d0; .fntext : { *(.fntext) } :fn
           . = 0x80200000; .rodata : { *(.rodata*) } :rodata }
"""
# `zkvm_sha256` with the whole of the binary's `.text` (its `rev8` sites patched, `sha_text`) and
# `.rodata` at their addresses; the `rev8` stubs at `STUBS`
STUBS = 0x80130000
LINK_SHA = f"""ENTRY(_start)
PHDRS {{ text PT_LOAD FLAGS(5); fn PT_LOAD FLAGS(5); zro PT_LOAD FLAGS(4); stub PT_LOAD FLAGS(5);
        rodata PT_LOAD FLAGS(4); }}
SECTIONS {{ . = 0x80120000; .text : {{ *(.text) }} :text
           . = 0x80000000; .fntext : {{ *(.fntext) }} :fn
           . = 0x8010fd80; .zrodata : {{ *(.zrodata) }} :zro
           . = {STUBS:#x}; .stubs : {{ *(.stubs) }} :stub
           . = 0x80200000; .rodata : {{ *(.rodata*) }} :rodata }}
"""
_ZBIN: dict[str, str] = {}
_ZLOCK = threading.Lock()


def zesu_bin(section: str) -> str:
    """The bytes of one section of the binary, in a file (cached for the run)."""
    with _ZLOCK:
        return zesu_bin_unlocked(section)


# ZisK eed62f4d9 has no Zbb: its decoder (`riscv/src/riscv_rvd.rs`, opcode 19 funct3 5) maps
# `rev8` to "reserved", which transpiles to `halt_with_error` (`riscv2zisk_context.rs:442`), so
# ziskemu stops at the first `rev8` of `zkvm_sha256` (0x800ea2d0 or 0x800ea33c) with the output
# never written. Each `rev8 rd, rs` of the function is replaced by `jal x0, stub` to a stub that
# computes the byte reversal into `tp` (with one more temporary, both spilled at `gp` = `SCRATCH`),
# moves it to `rd` and jumps back: every register but `rd` and all memory the test observes keep
# their values, so the patched function has the state transitions of the original. Later ZisK
# (`op_rev8`, `core/src/ops_core.rs` of fe919f2) defines the instruction the same way.
SHA_WORDS = 242
_SHA_TEXT: list = []


def sha_text():
    """(path of the patched `.text`, [(site, rd, rs)]), cached for the run."""
    with _ZLOCK:
        if not _SHA_TEXT:
            src = Path(zesu_bin_unlocked('.text')).read_bytes()
            data, sites = bytearray(src), []
            for a in range(FN['sha256'], FN['sha256'] + 4 * SHA_WORDS, 4):
                w = int.from_bytes(data[a - 0x80000000:a - 0x80000000 + 4], 'little')
                if w & 0xfff0707f == 0x6b805013:            # rev8 rd, rs
                    stub = STUBS + 256 * len(sites)
                    sites.append((a, (w >> 7) & 31, (w >> 15) & 31))
                    data[a - 0x80000000:a - 0x80000000 + 4] = jal0(stub - a).to_bytes(4, 'little')
            assert len(sites) == 10, sites
            out = Path(tempfile.mkdtemp(prefix='svc-zesu-')) / 'text-rev8.bin'
            out.write_bytes(data)
            _SHA_TEXT[:] = [str(out), sites]
        return _SHA_TEXT[0], _SHA_TEXT[1]


def zesu_bin_unlocked(section: str) -> str:
    """`zesu_bin` with `_ZLOCK` held by the caller."""
    if section not in _ZBIN:
        out = Path(tempfile.mkdtemp(prefix='svc-zesu-')) / (section.strip('.') + '.bin')
        subprocess.run(['riscv64-elf-objcopy', '-O', 'binary', f'--only-section={section}',
                        ELF, str(out)], check=True)
        _ZBIN[section] = str(out)
    return _ZBIN[section]


def jal0(off):
    """`jal x0, off`."""
    assert -(1 << 20) <= off < (1 << 20) and off % 2 == 0
    o = off & 0x1fffff
    return ((o >> 20) << 31) | (((o >> 1) & 0x3ff) << 21) | (((o >> 11) & 1) << 20) | \
        (((o >> 12) & 0xff) << 12) | 0x6f


def rev8_stub(site, rd, rs):
    x = lambda r: f'x{r}'
    t = next(r for r in (5, 6, 7, 28, 29, 30, 31) if r not in (rd, rs))
    out = ['  .balign 256', '  sd tp, 0(gp)', f'  sd {x(t)}, 8(gp)', '  li tp, 0']
    for k in range(8):
        out += [f'  srli {x(t)}, {x(rs)}, {8 * k}', f'  andi {x(t)}, {x(t)}, 255',
                f'  slli {x(t)}, {x(t)}, {56 - 8 * k}', f'  or tp, tp, {x(t)}']
    return out + [f'  mv {x(rd)}, tp', f'  ld {x(t)}, 8(gp)', '  ld tp, 0(gp)',
                  f'  jal x0, {site + 4:#x}']


def dump_layout(c: Case):
    """(name, offset, len) of each dumped part in the 256 output bytes."""
    if c.exit_only:
        return [('output', 0, 256)]
    parts, off = [], 0
    for name, _, n in c.dump:
        parts.append((name, off, n))
        off += n
    parts.append(('regs', off, 8 * len(c.pool)))
    off += 8 * len(c.pool)
    if c.extra:
        parts.append(('callee-saved', off, 8 * len(c.extra)))
        off += 8 * len(c.extra)
    if c.ret_bit is not None:
        parts.append(('returned to ra', off, 8))
        off += 8
    for name, _, _ in c.unchanged:
        parts.append((name, off, 8))
        off += 8
    assert off <= 256
    return parts


def program(c: Case) -> str:
    out = ['.section .text', '.globl _start', '_start:']
    data = ['.section .rodata']
    for k, (addr, bs) in enumerate(c.regions):
        if addr == MARCHID_ADDR:
            continue                      # ZisK's start-up code writes it
        data.append(f'blob{k}: .byte ' + ','.join(str(b) for b in bs))
        out += [f'  la t3, blob{k}', f'  li t4, {addr:#x}', f'  li t5, {len(bs)}', '  jal copy']
    for r in POOL:
        out.append(f'  li {REGNAME[r]}, {c.regs[r]:#x}')
    if c.fn == 'sha256':
        out.append(f'  li gp, {SCRATCH:#x}')
    for name, v in c.extra.items():
        out.append(f'  li {name}, {v:#x}')
    if c.exit_only:
        out += ['  .word 0x00000073']
    else:
        if c.fn and c.ret_bit is not None:
            # t3 = 1 only when the callee returns to `ra & ~1`
            out += [f'  li t6, {FN[c.fn]:#x}', '  la ra, ret_ok', f'  addi ra, ra, {c.ret_bit}',
                    '  jr t6', '  li t3, 0', '  j ret_done', 'ret_ok:', '  li t3, 1', 'ret_done:']
        elif c.fn:
            out += [f'  li t6, {FN[c.fn]:#x}', '  jalr ra, 0(t6)']
        else:
            out += [f'  .word {w:#010x}' for w in c.words]
        out.append(f'  li t6, {OUTPUT_ADDR:#x}')
        parts = dump_layout(c)
        poff = {p: o for p, o, _ in parts}
        regoff = poff['regs']
        for i, r in enumerate(c.pool):
            out.append(f'  sd {REGNAME[r]}, {regoff + 8 * i}(t6)')
        for i, name in enumerate(c.extra):
            out.append(f'  sd {name}, {regoff + 8 * len(c.pool) + 8 * i}(t6)')
        if c.ret_bit is not None:
            out.append(f"  sd t3, {poff['returned to ra']}(t6)")
        for (name, addr, n), (_, off, _) in zip(c.dump, parts):
            out += [f'  li t3, {addr:#x}', f'  li t4, {OUTPUT_ADDR + off:#x}', f'  li t5, {n}',
                    '  jal copy']
        for j, (name, k, keep) in enumerate(c.unchanged):
            addr, bs = c.regions[k]
            mask = [0 if any(lo <= o < hi for lo, hi in keep) else 1 for o in range(len(bs))]
            data.append(f'mask{j}: .byte ' + ','.join(map(str, mask)))
            out += [f'  li t3, {addr:#x}', f'  la t4, blob{k}', f'  li t5, {len(bs)}',
                    f'  la a1, mask{j}', f'  li a2, {OUTPUT_ADDR + poff[name]:#x}', '  jal cmp']
        out += ['  li a7, 93', '  ecall']
    out += ['copy:', '  beqz t5, 2f', '1: lbu t0, 0(t3)', '  sb t0, 0(t4)', '  addi t3, t3, 1',
            '  addi t4, t4, 1', '  addi t5, t5, -1', '  bnez t5, 1b', '2: ret']
    # cmp: a3 = #{i < t5 | a1[i] ≠ 0 ∧ t3[i] ≠ t4[i]}, stored at a2
    out += ['cmp:', '  li a3, 0', '  beqz t5, 2f', '1: lbu t0, 0(t3)', '  lbu t1, 0(t4)',
            '  lbu t2, 0(a1)', '  beqz t2, 3f', '  beq t0, t1, 3f', '  addi a3, a3, 1',
            '3: addi t3, t3, 1', '  addi t4, t4, 1', '  addi a1, a1, 1', '  addi t5, t5, -1',
            '  bnez t5, 1b', '2: sd a3, 0(a2)', '  ret']
    if c.fn == 'sha256':
        text, sites = sha_text()
        data += ['.section .fntext,"ax"', f'  .incbin "{text}"',
                 '.section .zrodata,"a"', f'  .incbin "{zesu_bin(".rodata")}"',
                 '.section .stubs,"ax"']
        for site in sites:
            data += rev8_stub(*site)
    elif c.fn:
        data += ['.section .fntext,"ax"'] + [f'  .word {w:#010x}' for w in fn_words()]
    return '\n'.join(out + data) + '\n'


def run_emu(c: Case, work: Path, idx: int, ziskemu: str) -> bytes | str:
    """The 256 output bytes, or ziskemu's panic message when it rejects the program."""
    s, elf = work / f'c{idx}.s', work / f'c{idx}.elf'
    s.write_text(program(c))
    subprocess.run(['riscv64-elf-gcc', '-march=rv64ima_zicsr', '-mabi=lp64', '-nostdlib', '-static',
                    '-T', str(work / ('link_sha.ld' if c.fn == 'sha256' else 'link.ld')), str(s),
                    '-o', str(elf)], check=True)
    env = dict(os.environ, LD_LIBRARY_PATH=LIBDIR)
    r = subprocess.run([ziskemu, '-e', str(elf), '-c'], capture_output=True, text=True, env=env,
                       timeout=120)
    words = [int(x, 16) for x in r.stdout.split() if len(x) == 8]
    if len(words) < 64:
        panic = [ln for ln in r.stderr.splitlines() if 'panicked' in ln or 'assertion' in ln]
        return re.sub(r"thread 'main' \(\d+\) ", '', ' | '.join(panic)) or f'no output: {r.stderr[-300:]}'
    return b''.join(w.to_bytes(4, 'little') for w in words[:64])


# -- the Lean side --------------------------------------------------------------------------------
LEAN_HEAD = """import ZesuExec.Service
open ZesuExec

def tMem (rs : List (Nat × List Nat)) : Word → Option Byte := fun x =>
  rs.findSome? fun (a, bs) =>
    if a ≤ x.toNat ∧ x.toNat < a + bs.length then some (BitVec.ofNat 8 (bs.getD (x.toNat - a) 0))
    else none

def tM (regs : List (Nat × Nat)) (pc : Nat) (rs : List (Nat × List Nat)) : Machine where
  regs := fun i => BitVec.ofNat 64 ((regs.lookup i.val).getD 0)
  pc := BitVec.ofNat 64 pc
  mem := tMem rs

def tImg (pc : Nat) (ws : List Nat) : Image := { text := [{ base := pc, words := ws }], rodata := [] }

def hex2 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.mk (List.replicate (2 - d.length) '0' ++ d)

def tBytes (mem : Word → Option Byte) (a n : Nat) : String :=
  String.join ((List.range n).map fun i => match mem (BitVec.ofNat 64 (a + i)) with
    | some b => hex2 b.toNat | none => "??")

def tRegs (m : Machine) (rs : List Nat) : String :=
  String.join (rs.map fun r => String.join ((List.range 8).map fun i =>
    hex2 ((m.reg ⟨r % 32, Nat.mod_lt _ (by decide)⟩).toNat / 256 ^ i % 256)))

def tRun (regs : List (Nat × Nat)) (rs : List (Nat × List Nat)) (ws : List Nat) (plen : Nat)
    (dump : List (Nat × Nat)) (pool : List Nat) : String :=
  let m := tM regs {pc} rs
  match svc (tImg {pc} ws) m with
  | some e =>
    let m' := e.apply m
    if m'.pc.toNat = {pc} + plen then
      String.join (dump.map fun (a, n) => tBytes m'.mem a n) ++ tRegs m' pool
    else "BADPC " ++ toString m'.pc.toNat
  | none => "NONE"

def tPost (m' : Machine) (dump : List (Nat × Nat)) (pool : List Nat) : String :=
  String.join (dump.map fun (a, n) => tBytes m'.mem a n) ++ tRegs m' pool

/-- `memmove` called at its entry: the state `MemcpyPost` fixes (`ziskMemcpy`). -/
def tMemmove (regs : List (Nat × Nat)) (rs : List (Nat × List Nat)) (dump : List (Nat × Nat))
    (pool : List Nat) : String :=
  match ziskMemcpy (tM ((1, 0x80000100) :: regs) 0x800e06d0 rs) with
  | some m' => tPost m' dump pool
  | none => "NONE"

/-- `memset` called at its entry: memory and registers as `Memset.Post` fixes them (`t0`, `a1`
are left as on entry and masked by the driver). -/
def tMemset (regs : List (Nat × Nat)) (rs : List (Nat × List Nat)) (dump : List (Nat × Nat))
    (pool : List Nat) : String :=
  let m := tM regs 0x800e06f0 rs
  let mem := Machine.fillMem m.mem (m.reg 10).toNat (m.reg 12).toNat ((m.reg 11).setWidth 8)
  tPost { m with mem := mem } dump pool

/-- `zkvm_sha256` called at its entry: the outputs `Sha256.Post` fixes (digest at `a2`, the
allocator words, `a0 = 0`). -/
def tSha256 (regs : List (Nat × Nat)) (rs : List (Nat × List Nat)) (dump : List (Nat × Nat))
    (pool : List Nat) : String :=
  let m := tM regs 0x800ea180 rs
  let msg := (List.range (m.reg 11).toNat).map fun i =>
    (m.mem (BitVec.ofNat 64 ((m.reg 10).toNat + i))).getD 0
  let g : List Byte := (List.range 8).map (fun i => BitVec.ofNat 8 (0xa05340c8 / 256 ^ i)) ++
    (List.range 8).map (fun i => BitVec.ofNat 8 (0xa0d340c8 / 256 ^ i))
  let mem := Machine.putBytes (Machine.putBytes m.mem (m.reg 12).toNat 32 (Sha256.hash msg))
    0xa05340b8 16 g
  tPost ({ m with mem := mem }.setReg 10 0) dump pool

def tExit (regs : List (Nat × Nat)) (rs : List (Nat × List Nat)) : String :=
  match ziskExit (tImg {pc} [0x73]) (tM regs {pc} rs) with
  | some bs => String.join (bs.map fun b => hex2 b.toNat)
  | none => "NONE"
"""


def extra_hex(c: Case) -> str:
    """The extra registers as dumped, which the contract keeps (entry values)."""
    return ''.join(v.to_bytes(8, 'little').hex() for v in c.extra.values())


def lean_list(xs):
    return '[' + ', '.join(xs) + ']'


def lean_case(c: Case) -> str:
    regs = lean_list(f'({r}, {v})' for r, v in sorted(c.regs.items()))
    rs = lean_list(f'({a}, {lean_list(str(b) for b in bs)})' for a, bs in c.regions)
    if c.exit_only:
        return f'tExit {regs} {rs}'
    dump = lean_list(f'({a}, {n})' for _, a, n in c.dump)
    if c.fn:
        f = {'memmove': 'tMemmove', 'memset': 'tMemset', 'sha256': 'tSha256'}[c.fn]
        return (f'({f} {regs} {rs} {dump} {lean_list(str(r) for r in c.pool)} ++ '
                f'"{extra_hex(c)}")')

    return (f'tRun {regs} {rs} {lean_list(str(w) for w in c.words)} {c.plen} {dump} '
            f'{lean_list(str(r) for r in POOL)}')


def run_lean(cases, work: Path) -> list[bytes | str]:
    src = LEAN_HEAD.replace('{pc}', str(PAT_PC))
    src += '\n'.join(f'#eval IO.println ("CASE{i} " ++ {lean_case(c)})' for i, c in enumerate(cases))
    f = work / 'SvcEval.lean'
    f.write_text(src + '\n')
    r = subprocess.run(['lake', 'env', 'lean', str(f)], cwd=PKG, capture_output=True, text=True,
                       timeout=3600)
    res: dict[int, bytes | str] = {}
    for line in r.stdout.splitlines():
        if line.startswith('CASE'):
            k, v = line[4:].split(' ', 1)
            try:
                res[int(k)] = bytes.fromhex(v)
            except ValueError:
                res[int(k)] = v
    if len(res) != len(cases):
        raise RuntimeError(f'lean: {r.stdout[-800:]} {r.stderr[-800:]}')
    return [res[i] for i in range(len(cases))]


# -- driver ---------------------------------------------------------------------------------------
def run_check(name, n, seed, ziskemu, jobs):
    gen, what = CHECKS[name]
    rng = random.Random(f'{seed}:{name}')
    cases = [gen(rng, i) if getattr(gen, 'indexed', False) else gen(rng) for i in range(n)]
    with tempfile.TemporaryDirectory(prefix=f'svc-{name}-') as d:
        work = Path(d)
        (work / 'link.ld').write_text(LINK_MEM)
        (work / 'link_sha.ld').write_text(LINK_SHA)
        with ThreadPoolExecutor(jobs) as ex:
            emu = list(ex.map(lambda ic: run_emu(ic[1], work, ic[0], ziskemu), enumerate(cases)))
        lean = run_lean(cases, work)
    names = [p for p, _, _ in dump_layout(cases[0])] + [a for a, _, _, _ in cases[0].alt]
    parts = {p: {'agree': 0, 'disagree': 0, 'first': None} for p in names}
    lean_none, emu_errors = 0, {}
    for i, (c, e, l) in enumerate(zip(cases, emu, lean)):
        if isinstance(e, str):
            emu_errors[e] = emu_errors.get(e, 0) + 1
            continue
        if isinstance(l, str):
            lean_none += 1
            for p in parts.values():
                p['disagree'] += 1
                p['first'] = p['first'] or {'case': i, 'lean': l}
            continue
        layout = {p: (off, ln) for p, off, ln in dump_layout(c)}
        if c.mask:
            regoff = layout['regs'][0]
            e, l = bytearray(e), bytearray(l)
            for r in c.mask:
                k = regoff + 8 * c.pool.index(r)
                e[k:k + 8] = l[k:k + 8] = bytes(8)
        # (part name, emulator bytes, expected bytes, must differ, what the expectation is)
        cmps = []
        for p, (off, ln) in layout.items():
            if p in c.expect:
                cmps.append((p, e[off:off + ln], c.expect[p], False, 'python'))
            else:
                cmps.append((p, e[off:off + ln], l[off:off + ln], False, 'lean'))
        for a, p, want, differ in c.alt:
            off, ln = layout[p]
            cmps.append((a, e[off:off + ln], want, differ, 'python'))
        for p, got, want, differ, src in cmps:
            ok = (got == want) != differ
            parts[p]['agree' if ok else 'disagree'] += 1
            if not ok and parts[p]['first'] is None:
                parts[p]['first'] = {'case': i, 'emu': bytes(got).hex(), src: bytes(want).hex()}
    return {'check': name, 'definition': what, 'cases': n, 'lean_none': lean_none, 'parts': parts,
            'emulator_errors': emu_errors,
            'pass': not emu_errors and all(p['disagree'] == 0 for p in parts.values())}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--n', type=int, default=100)
    ap.add_argument('--seed', default='14')
    ap.add_argument('--check', nargs='*', default=list(CHECKS))
    ap.add_argument('--ziskemu', default=ZISKEMU)
    ap.add_argument('--jobs', type=int, default=16)
    ap.add_argument('--json')
    a = ap.parse_args(argv)
    results = [run_check(c, a.n, a.seed, a.ziskemu, a.jobs) for c in a.check]
    for r in results:
        print(f"{r['check']:10} {'PASS' if r['pass'] else 'FAIL'}  {r['cases']} cases  "
              f"lean-none {r['lean_none']}  " +
              '  '.join(f"{p}: {v['agree']}/{v['agree'] + v['disagree']}" for p, v in r['parts'].items()))
        for msg, k in r['emulator_errors'].items():
            print(f'    ziskemu rejected {k} cases: {msg}')
        for p, v in r['parts'].items():
            if v['first']:
                print(f"    first disagreement in {p}: {v['first']}")
    if a.json:
        # results of other checks already in the file are kept
        old = json.loads(Path(a.json).read_text()) if Path(a.json).exists() else []
        new = {r['check']: r for r in results}
        merged = [new.pop(r['check'], r) for r in old] + list(new.values())
        Path(a.json).write_text(json.dumps(merged, indent=1) + '\n')
    return 0 if all(r['pass'] for r in results) else 1


if __name__ == '__main__':
    sys.exit(main())
