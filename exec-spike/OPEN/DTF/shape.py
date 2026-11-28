"""Register and frame-slot shapes of `decodeTxFields` at its cut points (design aid, S7).

A forward abstract interpretation over the function's instructions. Abstract values:
`('sp', k)` = entry `sp` + k, `('res', k)` = result + k, `('ao', k)` = allocator object + k,
`('lit', n)`, `('inp',)` = a pointer into the payload (any offset), `None` = unknown. Frame slots
are tracked at 8-byte granularity by their offset from the entry `sp`. Calls clobber the ABI's
caller-saved registers; `decodeItem` writes its 40-byte outcome at `a0` (payload pointer at `+0`),
`txAccessList` its 24-byte result at `a0` and `rest` `{ptr, len}` at `a2`, F1/F4 their headers.

Output (JSON on stdout): for every cut pc, the registers and the frame slots whose value is a
pointer the executor follows (`sp`, `res`, `ao`, the vtable literal, `inp`). `Regions.lean` states
exactly these as the cut's register overrides / known facts, and `Cuts.lean` the matching facts.

Usage: python3 OPEN/DTF/shape.py <elf> <cuts as hex,...>
"""
import json
import re
import subprocess
import sys

ENTRY, END = 0x8000050c, 0x8000050c + 11300
VTABLE = 0x801136d8
DECODE_ITEM, MEMCPY, TXAL, F1, F4 = 0x800d6960, 0x800e06c0, 0x80000000, 0x800cb40c, 0x800d677c
TABLE = [0x80000588, 0x8000081c, 0x8000069c, 0x8000075c, 0x800005dc]
ABI = [1, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]
NAMES = {'zero': 0, 'ra': 1, 'sp': 2, 'gp': 3, 'tp': 4, 't0': 5, 't1': 6, 't2': 7, 's0': 8,
         's1': 9, 'a0': 10, 'a1': 11, 'a2': 12, 'a3': 13, 'a4': 14, 'a5': 15, 'a6': 16, 'a7': 17,
         's2': 18, 's3': 19, 's4': 20, 's5': 21, 's6': 22, 's7': 23, 's8': 24, 's9': 25,
         's10': 26, 's11': 27, 't3': 28, 't4': 29, 't5': 30, 't6': 31}
INSN = re.compile(r'^\s*([0-9a-f]+):\s+[0-9a-f]+\s+(\S+)(?:\s+(.*?))?\s*$')


def disasm(elf):
    out = subprocess.run(['llvm-objdump', '-d', '-M', 'no-aliases', f'--start-address={ENTRY}',
                          f'--stop-address={END}', elf], check=True, capture_output=True,
                         text=True).stdout
    ins = {}
    for line in out.splitlines():
        m = INSN.match(line)
        if not m:
            continue
        ops = re.sub(r'\s*<[^>]*>\s*$', '', m.group(3) or '')
        ins[int(m.group(1), 16)] = (m.group(2), [o.strip() for o in ops.split(',')] if ops else [])
    return ins


def num(s):
    return int(s, 0)

def hi20(s):
    """A 20-bit upper immediate, sign-extended."""
    v = num(s) & 0xfffff
    return v - (1 << 20) if v >= 1 << 19 else v



def mem(op):
    m = re.match(r'(-?0x[0-9a-f]+|-?\d+)\((\w+)\)', op)
    return num(m.group(1)), NAMES[m.group(2)]


def add(v, k):
    if v is None:
        return None
    if v[0] in ('sp', 'res', 'ao'):
        return (v[0], v[1] + k)
    if v[0] == 'lit':
        return ('lit', (v[1] + k) % 2 ** 64)
    if v[0] == 'inp':
        return v if k == 0 else ('inp', None)
    return v if k == 0 else None


def jv(a, b):
    """Join of two abstract values: payload pointers stay payload pointers."""
    if a == b:
        return a
    if a and b and a[0] == 'inp' and b[0] == 'inp':
        return ('inp', None)
    return None


class St:
    def __init__(self, regs, slots, arms=frozenset()):
        self.regs, self.slots, self.arms = regs, slots, arms

    def copy(self):
        return St(list(self.regs), dict(self.slots), self.arms)

    def get(self, r):
        return ('lit', 0) if r == 0 else self.regs[r]

    def set(self, r, v):
        if r:
            self.regs[r] = v

    def kill(self, off, n):
        for k in list(self.slots):
            if k < off + n and off < k + 8:
                del self.slots[k]

    def join(self, o):
        regs = [jv(a, b) for a, b in zip(self.regs, o.regs)]
        slots = {k: jv(v, o.slots.get(k)) for k, v in self.slots.items()}
        return St(regs, {k: v for k, v in slots.items() if v is not None}, self.arms | o.arms)

    def __eq__(self, o):
        return self.regs == o.regs and self.slots == o.slots and self.arms == o.arms


def entry_state():
    regs = [None] * 32
    regs[2] = ('sp', 0)
    regs[10], regs[11] = ('res', 0), ('ao', 0)
    regs[13], regs[14] = ('inp', 0), ('rl', 0)
    return St(regs, {})


def call_effect(s, target):
    a0, a1, a2 = s.get(10), s.get(11), s.get(12)
    if target == DECODE_ITEM and a0 and a0[0] == 'sp':
        s.kill(a0[1], 40)
        s.slots[a0[1]] = ('inp', None)
        if a1 and a1[0] == 'inp' and a1[1] is not None and a2 == ('rl', a1[1]):
            s.slots[a0[1] + 0x18] = ('cons', a1[1])
    elif target == TXAL:
        if a0 and a0[0] == 'sp':
            s.kill(a0[1], 24)
        if a2 and a2[0] == 'sp':
            p, n = s.slots.get(a2[1]), s.slots.get(a2[1] + 8)
            s.kill(a2[1], 16)
            ok = p and p[0] == 'inp' and p[1] is not None and n == ('rl', p[1])
            s.slots[a2[1]] = ('inp', p[1] + 1 if ok else None)
            if ok:
                s.slots[a2[1] + 8] = ('rl', p[1] + 1)
    elif target in (F1, F4):
        for r in (10, 11):
            v = s.get(r)
            if v and v[0] == 'sp':
                s.kill(v[1], 24)
    elif target == MEMCPY:
        if a0 and a0[0] == 'sp':
            s.kill(a0[1], 1 << 20)
    for r in ABI:
        s.regs[r] = None


def step(ins, pc, s):
    """Successors [(pc, state)] of the instruction at `pc`."""
    op, a = ins[pc]
    s = s.copy()
    nxt = pc + 4
    R = lambda x: NAMES[x]
    if op in ('beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu'):
        return [(nxt, s), (num(a[2]), s)]
    if op == 'jal':
        t = num(a[1])
        if R(a[0]) == 1:
            call_effect(s, t)
            return [(nxt, s)]
        return [(t, s)] if ENTRY <= t < END else []
    if op == 'jalr':
        rd, (imm, rs) = R(a[0]), mem(a[1])
        if rd == 1:
            prev = ins.get(pc - 4)
            tgt = None
            if prev and prev[0] == 'auipc':
                tgt = (pc - 4 + (hi20(prev[1][1]) << 12) + imm) % 2 ** 64
            call_effect(s, tgt)
            return [(nxt, s)]
        if rs == 1:
            return []
        out = []
        for i, t in enumerate(TABLE):
            s2 = s.copy()
            s2.arms = frozenset([i])
            out.append((t, s2))
        return out
    if op == 'auipc':
        s.set(R(a[0]), ('lit', (pc + (hi20(a[1]) << 12)) % 2 ** 64))
        return [(nxt, s)]
    if op == 'lui':
        s.set(R(a[0]), ('lit', (hi20(a[1]) << 12) % 2 ** 64))
        return [(nxt, s)]
    if op == 'addi':
        s.set(R(a[0]), add(s.get(R(a[1])), num(a[2])))
        return [(nxt, s)]
    if op == 'add':
        x, y = s.get(R(a[1])), s.get(R(a[2]))
        v = None
        if x and y and x[0] == 'lit' and y[0] == 'lit':
            v = ('lit', (x[1] + y[1]) % 2 ** 64)
        elif x and y and {x[0], y[0]} == {'inp', 'cons'}:
            p, c = (x, y) if x[0] == 'inp' else (y, x)
            v = ('inp', p[1] + 1 if p[1] is not None and p[1] == c[1] else None)
        elif x and x[0] == 'inp' or y and y[0] == 'inp':
            v = ('inp', None)
        elif y and y[0] == 'lit':
            v = add(x, y[1])
        elif x and x[0] == 'lit':
            v = add(y, x[1])
        s.set(R(a[0]), v)
        return [(nxt, s)]
    if op == 'sub':
        x, y = s.get(R(a[1])), s.get(R(a[2]))
        v = None
        if x and y and x[0] == 'rl' and y == ('cons', x[1]):
            v = ('rl', x[1] + 1)
        s.set(R(a[0]), v)
        return [(nxt, s)]
    if op in ('ld', 'lw', 'lwu', 'lh', 'lhu', 'lb', 'lbu'):
        off, rs = mem(a[1])
        b = add(s.get(rs), off)
        v = None
        if op == 'ld' and b:
            if b[0] == 'sp':
                v = s.slots.get(b[1])
            elif b == ('ao', 8):
                v = ('lit', VTABLE)
        s.set(R(a[0]), v)
        return [(nxt, s)]
    if op in ('sd', 'sw', 'sh', 'sb'):
        off, rs = mem(a[1])
        b = add(s.get(rs), off)
        n = {'sd': 8, 'sw': 4, 'sh': 2, 'sb': 1}[op]
        if b and b[0] == 'sp':
            s.kill(b[1], n)
            if n == 8 and s.get(R(a[0])) is not None:
                s.slots[b[1]] = s.get(R(a[0]))
        return [(nxt, s)]
    # every other form writes rd with an unknown value
    if a:
        s.set(R(a[0]), None)
    return [(nxt, s)]


def analyse(ins):
    states = {ENTRY: entry_state()}
    work = [ENTRY]
    while work:
        pc = work.pop()
        for t, s in step(ins, pc, states[pc]):
            if t not in ins:
                continue
            old = states.get(t)
            new = s if old is None else old.join(s)
            if old is None or not (new == old):
                states[t] = new
                work.append(t)
    return states

KEEP = ('sp', 'res', 'ao', 'inp')

# Hand-placed cuts whose `a0` is the base of region 4: the jump-table word (8 rodata bytes), a
# `txHashList` slot (32 bytes), a `txAuthList` slot (0x90 bytes).
SLOT_CUTS = {0x80000574: '⟨some 8, 1, false⟩', 0x80002138: '⟨some 32, 1, true⟩',
             0x80002434: '⟨some 0x90, 1, true⟩'}


def keep(v):
    return v is not None and (v[0] in KEEP or v == ('lit', VTABLE))


def lean_val(v):
    return {'sp': lambda: f'.fr 0x{0x370 + v[1]:x}', 'res': lambda: f'.res {v[1]}',
            'ao': lambda: f'.ao {v[1]}', 'lit': lambda: '.vt', 'inp': lambda: '.inp'}[v[0]]()


KINDS = {DECODE_ITEM: '.f2', MEMCPY: '.memcpy', TXAL: '.tx', F1: '.f1', F4: '.f4'}
VSLOTS = {0: '.alloc', 2: '.remap', 3: '.free'}


def call_kind(ins, call):
    """The callee of the call instruction at `call`: a direct target, or an allocator vtable
    slot (`ld t, 8k(vtable)` shortly before an indirect `jalr ra, 0(t)`)."""
    op, a = ins[call]
    if op == 'jal':
        return KINDS[num(a[1])]
    imm, rs = mem(a[1])
    prev = ins.get(call - 4)
    if prev and prev[0] == 'auipc' and rs == 1:
        return KINDS[(call - 4 + (hi20(prev[1][1]) << 12) + imm) % 2 ** 64]
    for back in range(4, 64, 4):
        p = ins.get(call - back)
        if p and p[0] == 'ld' and NAMES[p[1][0]] == rs:
            return VSLOTS[mem(p[1][1])[0] // 8]
    raise ValueError(hex(call))


def jump_targets(ins):
    out = set()
    for pc, (op, a) in ins.items():
        if op in ('beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu'):
            out.add(num(a[2]))
        elif op == 'jal' and NAMES[a[0]] == 0:
            out.add(num(a[1]))
    return out | set(TABLE)


def lean_shape(s, slot=None):
    regs = [(i, lean_val(v)) for i, v in enumerate(s.regs) if i and keep(v)]
    extra = '[]'
    if slot:
        regs = sorted([x for x in regs if x[0] != 10] + [(10, '.slot')])
        extra = f'[{slot}]'
    slots = [(0x370 + k, lean_val(v)) for k, v in sorted(s.slots.items()) if keep(v)]
    r = ', '.join(f'({i}, {x})' for i, x in regs)
    sl = ', '.join(f'(0x{o:x}, {x})' for o, x in slots)
    return f'⟨[{r}], [{sl}], {extra}⟩'


def lean_rest(s):
    """Where the rest slice `{ptr, len}` after the latest `k` items is (older copies dropped)."""
    locs = [(f'.reg {i}', v) for i, v in enumerate(s.regs)
            if v and v[1] is not None and v[0] in ('rl', 'inp')]
    locs += [(f'.slot 0x{0x370 + k:x}', v) for k, v in sorted(s.slots.items())
             if v[1] is not None and v[0] in ('rl', 'inp')]
    top = {kind: max((v[1] for _, v in locs if v[0] == kind), default=None)
           for kind in ('rl', 'inp')}
    out = [f'⟨{loc}, {str(v[0] == "rl").lower()}, {v[1]}⟩' for loc, v in locs if v[1] == top[v[0]]]
    return '[' + ', '.join(out) + ']'


def site_state(ins, st, call):
    """The abstract state at the call instruction (before the call's effect)."""
    return st[call]


def lean_table(ins, st, cuts):
    rows = []
    jt = jump_targets(ins)
    for c in sorted(cuts):
        s = st[c]
        call = c - 4
        is_ret = call in ins and (ins[call][0] == 'jal' and NAMES[ins[call][1][0]] == 1 or
                                  ins[call][0] == 'jalr' and NAMES[ins[call][1][0]] == 1)
        plain = 'true' if (not is_ret or c in jt) else 'false'
        site = 'none'
        if is_ret:
            cs = site_state(ins, st, call)
            site = (f'some ⟨{call_kind(ins, call)}, {lean_shape(cs)}, '
                    f'[{", ".join(str(x) for x in sorted(cs.arms))}], {lean_rest(cs)}⟩')
        arms = ', '.join(str(x) for x in sorted(s.arms))
        rows.append(f'  ⟨0x{c:x}, {lean_shape(s, SLOT_CUTS.get(c))}, [{arms}], {lean_rest(s)}, '
                    f'{plain}, {site}⟩')
    return ',\n'.join(rows)


ROOT = __import__('pathlib').Path(__file__).resolve().parents[2]
ROWS = ROOT / 'ZesuExec/Fn/DTF/Rows.lean'
ROWS_HEAD = '''import ZesuExec.Fn.DTF.Field

/-!
# DTF item-value rows (generated by `OPEN/DTF/shape.py --fields {arms}`)

Per call site (by return address) and per cut reached by jumps and branches, the item values its
registers and frame words hold (`FieldsOk`), with the arms each holds for (`[]`: every arm reaching
it). `OPEN/DTF/fields_infer.lean` infers them over the leaves with the carry rules of `Gen.lean`
(arms {arms}; the other arms' call sites keep their earlier rows) and keeps the entries a value
at the success write `0x80002dc4` or an allocator call's copy arguments rests on.
-/

namespace ZesuExec.Fn.DTF

'''


def fields(arms):
    """Run the field-row inference for `arms` and write `Rows.lean`."""
    import os
    import tempfile
    probe = (ROOT / 'OPEN/DTF/fields_infer.lean').read_text()
    probe = probe.replace('ACTIVE_ARMS', '[' + ', '.join(map(str, arms)) + ']')
    probe = probe.replace('PRUNE', 'true')
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as f:
        f.write(probe)
        path = f.name
    res = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT, capture_output=True, text=True)
    os.unlink(path)
    if res.returncode != 0:
        sys.exit(res.stdout + res.stderr)
    fails = [l for l in res.stdout.splitlines() if l.startswith('FAIL ')]
    if fails:
        sys.exit('\n'.join(fails))
    rows = {'site': {}, 'cut': {}}
    for line in res.stdout.splitlines():
        m = re.match(r'ROW (site|cut) (\d+) (\.\w+ \w+) (\[[^\]]*\]) (.*)$', line)
        if m:
            rows[m.group(1)].setdefault(int(m.group(2)), []).append(
                f'⟨{m.group(3)}, {m.group(4)}, {m.group(5)}⟩')
    out = [ROWS_HEAD.format(arms=','.join(map(str, arms)))]
    for kind, name in (('site', 'siteFieldsTable'), ('cut', 'cutFieldsTable')):
        body = [f'  (0x{k:x}, [{", ".join(v)}])' for k, v in sorted(rows[kind].items()) if v]
        out.append(f'def {name} : List (Nat × List Field) := [\n' + ',\n'.join(body) + ']\n\n')
    out.append('end ZesuExec.Fn.DTF\n')
    ROWS.write_text(''.join(out))
    n = sum(len(v) for r in rows.values() for v in r.values())
    print(f'{n} entries -> {ROWS.relative_to(ROOT)}')


def main():
    if sys.argv[1] == '--fields':
        fields([int(x) for x in sys.argv[2].split(',')])
        return
    elf, cuts = sys.argv[1], [int(x, 16) for x in sys.argv[2].split(',')]
    ins = disasm(elf)
    st = analyse(ins)
    if len(sys.argv) > 3 and sys.argv[3] == '--lean':
        print(lean_table(ins, st, cuts))
        return
    out = {}
    for c in cuts:
        s = st[c]
        rest = [(f'r{i}', v[0], v[1]) for i, v in enumerate(s.regs)
                if v and (v[0] == 'rl' or v[0] == 'inp' and v[1] is not None)]
        rest += [(f's{0x370 + k:x}', v[0], v[1]) for k, v in sorted(s.slots.items())
                 if v[0] in ('rl', 'cons') or v[0] == 'inp' and v[1] is not None]
        out[hex(c)] = {
            'arms': sorted(s.arms),
            'regs': {i: list(v) for i, v in enumerate(s.regs) if i and keep(v)},
            'slots': {k: list(v) for k, v in sorted(s.slots.items()) if keep(v)},
            'rest': rest,
        }
    json.dump(out, sys.stdout, indent=0)



if __name__ == '__main__':
    main()
