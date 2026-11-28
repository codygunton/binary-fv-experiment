"""Map precision (plan stage S17): exact resolution of indirect calls and jumps, precondition
targets from the callers, and cycle cuts for irreducible control flow.

One forward abstract interpretation per function computes, at every indirect call or jump, a
symbolic term for the target address: the backward slice of the pointer source, written
forwards. Resolution kinds of an indirect call (`calls[].resolution`):

- `exact`: every value of the term is known: a constant, or slots of a constant read-only
  table, indexed by a bounded value (a byte load, a mask, a bound checked by `bltu`/`bgeu`).
- `precondition`: the term is an argument register or a chain of loads rooted at one (or at a
  stack-passed argument). `targets` are the functions the callers pass, found by substituting
  each caller's state at its call into the term; `targets_complete` is false when a caller does
  not resolve or the function's address is taken (it may be called from a site not seen).
- `unknown`: anything else (a call result, a mutable global, values merged from two paths).
  `reason` says which.

Indirect jumps: `exact` when every value is code of the function; when the index reaches past
the table, the leading run of code slots, as `precondition` if the index comes from an argument
(its bound is the caller's), else `table-heuristic`; else the block-local `table-heuristic`;
else `unresolved`.

This is a map, not a proof; the analysis assumes: callees keep the RISC-V calling convention
(`sp`, `s0`-`s11` preserved; `ra`, `t*`, `a*` clobbered); a callee writes into its caller's frame
only through pointer arguments, inside the offset window of its write summary
(`write_summaries`; frame addresses stored to memory are not followed); an indirect call writes as
its known targets do; a frame slot not written on some path into a join is undefined there;
a pointer walking a frame buffer at an unknown offset stays at or above its lowest known offset;
`.rodata` and `.text` are never written; a load reads memory as it is at the load.
"""
import heapq
from collections import Counter, defaultdict

from . import elfread

M64 = (1 << 64) - 1
TOP = ('u',)
SP = ('sp',)
# ('spbase', lo): a frame address at an unknown offset at or above sp + lo (a pointer walking a
# frame buffer upwards).
ARGS = tuple(f'a{i}' for i in range(8))
CLOBBER = ('ra',) + tuple(f't{i}' for i in range(7)) + ARGS
MAX_VALUES = 4096   # largest enumerated value set
MAX_DEPTH = 8       # deeper terms become TOP (keeps the lattice finite)
MAX_TERMS = 4
MAX_SET = 16        # largest set of constants a join keeps (('set', values))
MAX_WINDOW = 1 << 16  # widest offset window of a write summary
ANY = 'any'         # a write at an unknown offset
UNKNOWN = object()  # the write summary of an unknown callee
# Library copies by symbol name: (dst a0, src a1 or byte a1, length a2). Their bodies are CSR
# accelerator writes (ZisK services), invisible to the analysis.
MEMOPS = {'memcpy': 'copy', 'memmove': 'copy', 'memset': 'set'}
LOADS = {'ld': (8, True), 'lw': (4, True), 'lwu': (4, False), 'lh': (2, True), 'lhu': (2, False),
         'lb': (1, True), 'lbu': (1, False)}
STORES = {'sd': 8, 'sw': 4, 'sh': 2, 'sb': 1}
READ_ONLY = ('.rodata', '.text')


def imm(text):
    return int(text, 0)


def sext(value, bits):
    value &= (1 << bits) - 1
    return value - (1 << bits) if value >> (bits - 1) else value


def mem_operand(text):
    off, reg = text[:-1].split('(')
    return imm(off), reg


# ---------------------------------------------------------------- terms

def depth(v):
    k = v[0]
    if k == 'ld':
        return 1 + depth(v[3])
    if k == 'sum':
        return 1 + max(depth(t) for t in v[2])
    if k == 'shl':
        return 1 + depth(v[1])
    return 0


def const(n):
    return ('c', n & M64)


def add(a, b):
    if a == TOP or b == TOP:
        return TOP
    if a[0] == 'spbase' or b[0] == 'spbase':  # the bound stays (finite lattice)
        return a if a[0] == 'spbase' else b
    if a[0] == 'base' or b[0] == 'base':
        return ('base', tuple(sorted(direct_args(a) | direct_args(b))))
    c, terms = 0, []
    for v in (a, b):
        if v[0] == 'c':
            c += v[1]
        elif v[0] == 'sum':
            c += v[1]
            terms.extend(v[2])
        else:
            terms.append(v)
    c &= M64
    if not terms:
        return ('c', c)
    if len(terms) == 1 and c == 0:
        return terms[0]
    if len(terms) > MAX_TERMS:
        return TOP
    v = ('sum', c, tuple(sorted(terms)))
    return v if depth(v) <= MAX_DEPTH else TOP


def shl(a, k):
    if a[0] == 'c':
        return const(a[1] << k)
    if a[0] == 'rng':
        return ('rng', (a[1] << k) & M64, a[2] << k, a[3]) + a[4:]
    if a[0] == 'set':
        return ('set', tuple(sorted({(x << k) & M64 for x in a[1]})))
    if a[0] == 'sum':
        out = const(a[1] << k)
        for t in a[2]:
            out = add(out, shl(t, k))
        return out
    if a == TOP:
        return TOP
    v = ('shl', a, k)
    return v if depth(v) <= MAX_DEPTH else TOP


def srl(a, k):
    if a[0] == 'c':
        return ('c', a[1] >> k)
    if a[0] == 'rng' and a[1] % (1 << k) == 0 and a[2] % (1 << k) == 0:
        return ('rng', a[1] >> k, a[2] >> k, a[3]) + a[4:]
    if a[0] == 'set':
        return ('set', tuple(sorted({x >> k for x in a[1]})))
    return TOP


def mask(a, m):
    """a & m for a non-negative immediate m."""
    if a[0] == 'c':
        return ('c', a[1] & m)
    if a[0] == 'set':
        vals = sorted({x & m for x in a[1]})
        return ('set', tuple(vals)) if len(vals) > 1 else ('c', vals[0])
    if m >= 0 and m & (m + 1) == 0:  # low-bit mask
        if a[0] == 'rng' and a[1] + a[2] * (a[3] - 1) <= m:
            return a
        return ('rng', 0, 1, m + 1) + origin(a)
    return TOP


def origin(a):
    """The origin suffix of a range derived from value a: what the range bounds (kept for the
    classification of the index; enumeration ignores it)."""
    if a[0] == 'rng':
        return a[4:]
    return () if a == TOP else (a,)


def sp_offset(v):
    """k when v is sp + k (sp at function entry), else None."""
    if v == SP:
        return 0
    if v[0] == 'sum' and v[2] == (SP,):
        return sext(v[1], 64)
    return None


def fmt(v):
    k = v[0]
    if k == 'c':
        return f'{v[1]:#x}'
    if k == 'arg':
        return v[1]
    if k == 'sp':
        return 'sp'
    if k == 'sum':
        parts = [fmt(t) for t in v[2]]
        if v[1]:
            parts.append(f'{sext(v[1], 64):#x}')
        return '(' + '+'.join(parts) + ')'
    if k == 'ld':
        return f'ld{v[1]}{"" if v[2] else "u"}[{fmt(v[3])}]'
    if k == 'shl':
        return f'({fmt(v[1])}<<{v[2]})'
    if k == 'rng':
        return f'{{{v[1]:#x}+{v[2]}i, i<{v[3]}}}'
    if k == 'set':
        return '{' + ','.join(f'{x:#x}' for x in v[1]) + '}'
    if k == 'ret':
        return f'ret@{v[1]:#x}'
    if k == 'base':
        return '(' + '|'.join(v[1]) + ')+?'
    return '?'


def enumerate_values(v, binary):
    """Every value of term v, or None when not all are known (or more than MAX_VALUES)."""
    k = v[0]
    if k == 'c':
        return {v[1]}
    if k == 'set':
        return set(v[1])
    if k == 'rng':
        if v[3] > MAX_VALUES:
            return None
        return {(v[1] + v[2] * i) & M64 for i in range(v[3])}
    if k == 'sum':
        out = {v[1]}
        for t in v[2]:
            vals = enumerate_values(t, binary)
            if vals is None or len(out) * len(vals) > MAX_VALUES:
                return None
            out = {(a + b) & M64 for a in out for b in vals}
        return out
    if k == 'shl':
        vals = enumerate_values(v[1], binary)
        return None if vals is None else {(x << v[2]) & M64 for x in vals}
    if k == 'ld':
        w, signed, addr = v[1], v[2], v[3]
        addrs = enumerate_values(addr, binary)
        if addrs is not None and all(binary.in_section(a, READ_ONLY) for a in addrs):
            out = set()
            for a in addrs:
                word = binary.read(a, w)
                if word is None:
                    return None
                out.add(sext(word, 8 * w) & M64 if signed else word)
            return out
        if not signed and (1 << (8 * w)) <= MAX_VALUES:
            return set(range(1 << (8 * w)))  # any byte (or halfword) value
        return None
    return None


def table_addresses(v, binary):
    """The read-only slots a load term reads, when the term is a load."""
    if v[0] == 'ld':
        addrs = enumerate_values(v[3], binary)
        if addrs:
            return v[1], sorted(addrs)
    return None


def roots(v, out):
    """Atoms a term is built from (constants excluded; a range contributes its origin)."""
    k = v[0]
    if k in ('c', 'set'):
        return out
    if k == 'rng':
        return roots(v[4], out) if len(v) > 4 else out
    if k == 'sum':
        for t in v[2]:
            roots(t, out)
    elif k == 'shl':
        roots(v[1], out)
    elif k == 'ld':
        a = v[3]
        if sp_offset(a) is not None:
            out.add(('stack-arg',) if sp_offset(a) >= 0 else TOP)
        elif a[0] == 'c':
            out.add(('global', a[1]))
        else:
            roots(a, out)
    else:
        out.add(v)
    return out


def classify(v, binary, kind):
    """(resolution, values or None, reason) of a target term. kind: 'call' or 'jump'."""
    vals = enumerate_values(v, binary)
    if vals is not None:
        if kind == 'call' and all(x in binary.by_entry for x in vals):
            return 'exact', vals, None
        if kind == 'jump':
            return 'exact', vals, None  # the caller checks the values are in the function
    rs = roots(v, set())
    if rs and all(r == ('stack-arg',) or r[0] == 'base' or (r[0] == 'arg' and r[1] in ARGS)
                  for r in rs):
        return 'precondition', None, None
    if any(r[0] == 'ret' for r in rs):
        reason = 'call-result'
    elif any(r[0] == 'global' for r in rs):
        reason = 'global'
    elif any(r[0] == 'arg' for r in rs):
        reason = 'callee-saved-at-entry'
    elif v[0] == 'ld' or vals is None:
        reason = 'merged-or-computed'
    else:
        reason = 'not-a-code-address'
    return 'unknown', None, reason


# ---------------------------------------------------------------- abstract state

def init_reg(r):
    return SP if r == 'sp' else ('arg', r)


class State:
    __slots__ = ('regs', 'slots')

    def __init__(self, regs=None, slots=None):
        self.regs = regs if regs is not None else {}
        self.slots = slots if slots is not None else {}  # sp offset -> (width, value)

    def copy(self):
        return State(dict(self.regs), dict(self.slots))

    def get(self, r):
        if r == 'zero':
            return ('c', 0)
        v = self.regs.get(r)
        return init_reg(r) if v is None else v

    def set(self, r, v):
        if r != 'zero':
            self.regs[r] = v

    def __eq__(self, o):
        return self.regs == o.regs and self.slots == o.slots

    def overlapping(self, k, w):
        return [j for j in range(k - 7, k + w) if j in self.slots
                and j + self.slots[j][0] > k and j < k + w]

    def store(self, k, w, v):
        for j in self.overlapping(k, w):
            wj = self.slots[j][0]
            if k <= j and j + wj <= k + w:
                del self.slots[j]
            else:  # partly overwritten
                self.slots[j] = (wj, TOP)
        self.slots[k] = (w, v)

    def load(self, k, w, signed):
        ent = self.slots.get(k)
        if ent is not None and ent[0] == w:
            v = ent[1]
            if w == 8 or v == TOP:
                return v
            if v[0] == 'c':
                word = v[1] & ((1 << (8 * w)) - 1)
                return const(sext(word, 8 * w)) if signed else ('c', word)
            if v[0] == 'ld' and v[1] == w and v[2] == signed:
                return v
            return TOP
        if self.overlapping(k, w) or k < 0:
            return TOP
        return ('ld', w, signed, add(SP, const(k)))

    def kill_range(self, lo, hi):
        for j in [j for j in self.slots if j < hi and j + self.slots[j][0] > lo]:
            self.slots[j] = (self.slots[j][0], TOP)

    def kill_from(self, lo):
        self.kill_range(lo, 1 << 62)


def join_value(va, vb):
    """Equal values stay; two frame addresses become ('spbase', lowest offset); two pointers
    based on the same arguments become ('base', args); anything else TOP."""
    if va == vb:
        return va
    if va == TOP or vb == TOP:
        return TOP
    if va[0] == 'rng' and vb[0] == 'rng' and va[2] == vb[2] and (va[1] - vb[1]) % va[2] == 0:
        lo = min(va[1], vb[1])
        hi = max(va[1] + va[2] * va[3], vb[1] + vb[2] * vb[3])
        hull = ('rng', lo, va[2], (hi - lo) // va[2])
        if hull in (va[:4], vb[:4]):  # one contains the other (no widening sequence)
            return hull + (va[4:] if va[4:] == vb[4:] else ())
    if va[0] in ('c', 'set') and vb[0] in ('c', 'set'):
        vals = set(va[1:2] if va[0] == 'c' else va[1]) | set(vb[1:2] if vb[0] == 'c' else vb[1])
        return ('set', tuple(sorted(vals))) if len(vals) <= MAX_SET else TOP
    la, lb = frame_lo(va), frame_lo(vb)
    if la is not None and lb is not None:
        return ('spbase', min(la, lb))
    da = direct_args(va)
    if da and da == direct_args(vb):
        return ('base', tuple(sorted(da)))
    return TOP


def join(a, b):
    regs = {}
    for r in a.regs.keys() | b.regs.keys():
        va, vb = a.get(r), b.get(r)
        v = join_value(va, vb)
        if v != init_reg(r):
            regs[r] = v
    slots = {}
    for k in a.slots.keys() | b.slots.keys():
        ea, eb = a.slots.get(k), b.slots.get(k)
        if ea == eb:
            slots[k] = ea
        elif ea is not None and eb is not None:
            slots[k] = (ea[0], join_value(ea[1], eb[1]) if ea[0] == eb[0] else TOP)
        elif k >= 0:  # one side has the caller's value from entry
            slots[k] = ((ea or eb)[0], TOP)
        else:  # not written on one side: undefined there
            slots[k] = ea or eb
    return State(regs, slots)


# ---------------------------------------------------------------- transfer

def load_value(st, binary, addr, w, signed):
    if addr == TOP or addr[0] == 'spbase' or depth(addr) >= MAX_DEPTH:  # bytes are bounded
        return ('rng', 0, 1, 1 << (8 * w)) if not signed and w <= 2 else TOP
    k = sp_offset(addr)
    if k is not None:
        return st.load(k, w, signed)
    if addr[0] == 'c' and binary.in_section(addr[1], READ_ONLY):
        word = binary.read(addr[1], w)
        if word is not None:
            return const(sext(word, 8 * w)) if signed else ('c', word)
    return ('ld', w, signed, addr)


def frame_lo(v):
    """Lowest frame offset (from sp at entry) a frame address may have, else None."""
    return v[1] if v[0] == 'spbase' else sp_offset(v)


def arg_offsets(v):
    """{argument register: offset or None (unknown)} a pointer term is directly based on:
    a + offset, a + index; not a pointer loaded through a."""
    if v == TOP:
        return {}
    if v[0] == 'arg':
        return {v[1]: 0} if v[1] in ARGS else {}
    if v[0] == 'base':
        return {r: None for r in v[1]}
    if v[0] == 'sum':
        args = [t[1] for t in v[2] if t[0] == 'arg' and t[1] in ARGS]
        if len(v[2]) == 1 and args:
            return {args[0]: sext(v[1], 64)}
        return {r: None for r in args}
    return {}


def merge_window(old, new):
    if old is None:
        return new
    if old == ANY or new == ANY:
        return ANY
    lo, hi = min(old[0], new[0]), max(old[1], new[1])
    return ANY if hi - lo > MAX_WINDOW else (lo, hi)


def direct_args(v):
    """Argument registers (entry values) a pointer term is directly based on: a + offset or
    a + index, not a pointer loaded through a."""
    if v == TOP:
        return set()
    if v[0] == 'base':
        return set(v[1])
    if v[0] == 'arg':
        return {v[1]} if v[1] in ARGS else set()
    if v[0] == 'sum':
        return {t[1] for t in v[2] if t[0] == 'arg' and t[1] in ARGS}
    return set()


def step(st, insn, binary, acc):
    """Execute one non-control instruction on the state. Records in `acc` the function-entry
    constants (`taken`) and the arguments written through (`writes`)."""
    mn, ops = insn.mn, insn.ops
    if mn in STORES:
        off, base = mem_operand(ops[1])
        addr = add(st.get(base), const(off))
        v = st.get(ops[0])
        k = sp_offset(addr)
        if k is not None:
            st.store(k, STORES[mn], v if STORES[mn] == 8 or v[0] == 'c' else TOP)
        elif addr[0] == 'spbase':  # somewhere in this frame at or above lo
            st.kill_from(addr[1])
        else:
            for r, off in arg_offsets(addr).items():
                acc['writes'][r] = merge_window(acc['writes'].get(r),
                                                ANY if off is None else (off, off + STORES[mn]))
        return
    if mn == 'ecall':  # an environment call may write through any argument
        for r in ARGS:
            acc['writes'][r] = ANY
    elif mn in ('csrrw', 'csrrs', 'csrrc'):  # a service writes through its operand's memory
        for r in arg_offsets(st.get(ops[2])):
            acc['writes'][r] = ANY
    if mn in elfread.BRANCHES or not ops or mn in ('fence', 'ecall', 'ebreak', 'unimp'):
        return
    rd = ops[0]
    if rd == 'zero' or '(' in rd:
        return
    if mn == 'lui':
        v = const(sext(imm(ops[1]), 20) << 12)
    elif mn == 'auipc':
        st.set(rd, const(insn.pc + (sext(imm(ops[1]), 20) << 12)))
        return
    elif mn == 'addi':
        v = add(st.get(ops[1]), const(imm(ops[2])))
    elif mn == 'add':
        v = add(st.get(ops[1]), st.get(ops[2]))
    elif mn == 'sub':
        a, b = st.get(ops[1]), st.get(ops[2])
        v = add(a, const(-b[1])) if b[0] == 'c' else ('c', 0) if a == b and a != TOP else TOP
    elif mn == 'andi':
        v = mask(st.get(ops[1]), imm(ops[2]))
    elif mn == 'and':
        a, b = st.get(ops[1]), st.get(ops[2])
        v = mask(a, b[1]) if b[0] == 'c' else mask(b, a[1]) if a[0] == 'c' else TOP
    elif mn == 'slli':
        v = shl(st.get(ops[1]), imm(ops[2]))
    elif mn == 'srli':
        v = srl(st.get(ops[1]), imm(ops[2]))
    elif mn in ('ori', 'xori'):
        a, n = st.get(ops[1]), imm(ops[2]) & M64
        v = ('c', a[1] | n if mn == 'ori' else a[1] ^ n) if a[0] == 'c' else TOP
    elif mn in ('or', 'xor', 'mul'):
        a, b = st.get(ops[1]), st.get(ops[2])
        if a[0] == 'c' and b[0] == 'c':
            v = ('c', (a[1] | b[1]) if mn == 'or' else (a[1] ^ b[1]) if mn == 'xor'
                 else (a[1] * b[1]) & M64)
        else:
            v = TOP
    elif mn == 'addiw':
        a = st.get(ops[1])
        v = const(sext(a[1] + imm(ops[2]), 32)) if a[0] == 'c' else TOP
    elif mn in LOADS:
        w, signed = LOADS[mn]
        off, base = mem_operand(ops[1])
        v = load_value(st, binary, add(st.get(base), const(off)), w, signed)
    else:
        v = TOP
    for n in (v[1],) if v[0] == 'c' else v[1] if v[0] == 'set' else ():
        if n in binary.by_entry:
            acc['taken'].add(n)
        elif binary.in_section(n, ('.rodata',)):
            acc['refs'].add(n)
    st.set(rd, v)


def refine(st, insn, edge):
    """State on one edge of an unsigned branch against a constant bound (bound <= MAX_VALUES)."""
    mn = insn.mn
    if mn not in ('bltu', 'bgeu'):
        return st
    x, y = insn.ops[0], insn.ops[1]
    vx, vy = st.get(x), st.get(y)
    less = (mn == 'bltu') == (edge == 'taken')  # x <u y holds on this edge, else x >=u y
    if less and vy[0] == 'c' and vx[0] != 'c' and 0 < vy[1] <= MAX_VALUES:
        reg, old, rng = x, vx, ('rng', 0, 1, vy[1]) + origin(vx)
    elif not less and vx[0] == 'c' and vy[0] != 'c' and vx[1] < MAX_VALUES:
        reg, old, rng = y, vy, ('rng', 0, 1, vx[1] + 1) + origin(vy)  # y <=u x
    else:
        return st
    st = st.copy()
    if old == TOP:
        st.set(reg, rng)
    else:  # every register holding the same value
        for r in list(st.regs) + [reg]:
            if st.get(r) == old:
                st.set(r, rng)
    return st


def block_succ(block, ctrl, start_set):
    """[(successor, edge kind)] of a block: 'taken', 'fall' or 'jump'."""
    last = block[-1]
    c = ctrl.get(last.pc)
    kind = c['kind'] if c else None
    if kind == 'branch':
        out = [(c['target'], 'taken'), (last.next, 'fall')]
    elif kind == 'jump':
        out = [(c['target'], 'jump')]
    elif kind == 'ijump':
        out = [(t, 'jump') for t in c.get('targets', ())]
    elif kind in ('ret', 'tail', 'trap'):
        out = []
    else:
        out = [(last.next, 'fall')]
    return [(s, k) for s, k in out if s in start_set]


def flow(binary, f, blocks, ctrl, summaries=None):
    """Fixpoint of the abstract interpretation over the blocks of one function.

    `summaries` (`write_summaries`): function entry, or ('icall', pc) for an indirect call site,
    -> {argument register: offset window it may write through}; a call marks the frame slots
    in those windows unknown. None: callees write through no argument.

    Returns {'sites': pc -> target term of an indirect call/jump, 'snaps': pc -> State at a
    call or tail call (before it), 'taken': function entries materialised as constants,
    'refs': `.rodata` addresses materialised as constants, 'writes': {argument: offset window
    written through}, 'passes': [(callee entry or ('icall', pc), {callee argument: {own
    argument: offset or None}})]}."""
    by_start = {b[0].pc: b for b in blocks}
    succ = {s: block_succ(b, ctrl, by_start) for s, b in by_start.items()}
    order, seen, stack = [], {f.entry}, [(f.entry, iter(succ[f.entry]))]
    while stack:  # reverse postorder
        n, it = stack[-1]
        for s, _ in it:
            if s not in seen:
                seen.add(s)
                stack.append((s, iter(succ[s])))
                break
        else:
            order.append(n)
            stack.pop()
    rank = {n: i for i, n in enumerate(reversed(order))}
    ins = {f.entry: State()}
    work, queued = [rank[f.entry]], {f.entry}
    sites, snaps = {}, {}
    acc = {'taken': set(), 'refs': set(), 'writes': {}}
    passes = []
    by_rank = {i: n for n, i in rank.items()}
    while work:
        s = by_rank[heapq.heappop(work)]
        queued.discard(s)
        st = ins[s].copy()
        for insn in by_start[s]:
            c = ctrl.get(insn.pc)
            kind = c['kind'] if c else None
            if kind in ('icall', 'ijump'):
                sites[insn.pc] = add(st.get(c['rs']), const(c['off']))
            if kind in ('call', 'icall', 'tail'):
                snaps[insn.pc] = st.copy()
                callee = c['targets'][0] if kind != 'icall' else ('icall', insn.pc)
                based = {p: arg_offsets(st.get(p)) for p in ARGS}
                based = {p: offs for p, offs in based.items() if offs}
                if based:
                    passes.append((callee, based))
            if kind in ('call', 'icall'):
                op = (MEMOPS.get(binary.by_entry[callee].name)
                      if kind == 'call' and callee in binary.by_entry else None)
                if op:
                    mem_op(st, binary, op)
                elif summaries is not None:
                    kill_written(st, summaries.get(callee, UNKNOWN))
                for r in CLOBBER:
                    st.set(r, TOP)
                st.set('a0', ('ret', insn.pc))
            elif kind is None:
                step(st, insn, binary, acc)
        last = by_start[s][-1]
        for t, ek in succ[s]:
            out = refine(st, last, ek) if ek in ('taken', 'fall') else st
            old = ins.get(t)
            new = out.copy() if old is None else join(old, out)
            if old is None or not (new == old):
                ins[t] = new
                if t not in queued:
                    queued.add(t)
                    heapq.heappush(work, rank[t])
    return {'sites': sites, 'snaps': snaps, 'taken': acc['taken'], 'refs': acc['refs'],
            'writes': acc['writes'], 'passes': passes}


def write_summaries(cfgs):
    """Least fixpoint: for each function, the argument registers it may write through and the
    offset window written (`(lo, hi)` or ANY), directly or by passing a pointer based on the
    argument to a callee that writes through that parameter. An indirect call site writes as
    the union of its known targets; with no known target it is unknown, and an unknown callee
    writes anywhere through every pointer it gets. Keys: function entries and ('icall', pc)."""
    w = {cfg['f'].entry: ({'a0': ANY} if cfg['f'].name in MEMOPS else dict(cfg['flow']['writes']))
         for cfg in cfgs}
    icall_targets = {('icall', pc): c['targets'] for cfg in cfgs
                     for pc, c in cfg['ctrl'].items() if c['kind'] == 'icall' and c['targets']}

    def summary(callee):
        if callee in icall_targets:
            out = {}
            for t in icall_targets[callee]:
                tw = w.get(t, UNKNOWN)
                if tw is UNKNOWN:
                    return UNKNOWN
                for r, iv in tw.items():
                    out[r] = merge_window(out.get(r), iv)
            return out
        return w.get(callee, UNKNOWN)

    changed = True
    while changed:
        changed = False
        for cfg in cfgs:
            own = w[cfg['f'].entry]
            for callee, based in cfg['flow']['passes']:
                cw = summary(callee)
                for p, offs in based.items():
                    civ = ANY if cw is UNKNOWN else cw.get(p)
                    if civ is None:
                        continue
                    for r, off in offs.items():
                        iv = ANY if civ == ANY or off is None else (civ[0] + off, civ[1] + off)
                        new = merge_window(own.get(r), iv)
                        if new != own.get(r):
                            own[r] = new
                            changed = True
    for key in icall_targets:
        w[key] = summary(key)
    return w


def mem_op(st, binary, op):
    """memcpy/memmove (op 'copy') or memset ('set') into this frame: the destination window
    gets the source's 8-byte words (loads at the time of the copy) or the fill byte."""
    dst, src, n = st.get('a0'), st.get('a1'), st.get('a2')
    kd = frame_lo(dst)
    if kd is None:
        return
    if n[0] != 'c' or n[1] > MAX_VALUES or dst[0] == 'spbase':
        st.kill_from(kd)
        return
    n = n[1]
    if op == 'copy':
        vals = [] if src == TOP else [(i, load_value(st, binary, add(src, const(i)), 8, True))
                                      for i in range(0, n - 7, 8)]
    else:
        word = const(int.from_bytes(bytes([src[1] & 0xff]) * 8, 'little')) if src[0] == 'c' \
            else TOP
        vals = [(i, word) for i in range(0, n - 7, 8)]
    st.kill_range(kd, kd + n)
    for i, v in vals:
        st.store(kd + i, 8, v)


def kill_written(st, cw):
    """At a call: mark unknown the frame slots the callee may write through its pointer
    arguments (`cw`: its write summary, or UNKNOWN)."""
    for r in ARGS:
        v = st.get(r)
        k = frame_lo(v)
        if k is None:
            continue
        iv = ANY if cw is UNKNOWN else cw.get(r)
        if iv is None:
            continue
        if iv == ANY or v[0] == 'spbase':
            st.kill_from(k)
        else:
            st.kill_range(k + iv[0], k + iv[1])


# ---------------------------------------------------------------- intraprocedural resolution

def resolve_function(binary, f, insns, ctrl, split_blocks, heuristic_ijump, summaries=None):
    """Resolve the indirect calls and jumps of one function; re-split blocks at new jump
    targets until stable. Sets ctrl[pc]['targets'], ['resolution'] and slice fields; returns
    (blocks, tables, flow)."""
    pcs = {i.pc for i in insns}
    extra, tables = set(), {}
    blocks1 = None
    while True:
        blocks = split_blocks(f, insns, ctrl, extra)
        if blocks1 is None:
            blocks1 = {b[-1].pc: b for b in blocks}
        fl = flow(binary, f, blocks, ctrl, summaries)
        new = set()
        bases = set()  # first slot of every table this function jumps through
        for pc, c in ctrl.items():
            term = fl['sites'].get(pc)
            tab = table_addresses(term, binary) if c['kind'] == 'ijump' and term else None
            if tab:
                bases.add(tab[1][0])
        for pc, c in ctrl.items():
            if c['kind'] not in ('icall', 'ijump'):
                continue
            term = fl['sites'].get(pc)
            res, vals, reason = classify(term, binary, 'call' if c['kind'] == 'icall' else 'jump') \
                if term is not None else ('unknown', None, 'unreachable')
            c['slice'] = fmt(term) if term is not None else None
            c['reason'] = reason
            if c['kind'] == 'icall':
                c['resolution'] = res
                c['targets'] = sorted(vals) if vals else []
                continue
            if res == 'exact' and all(v in pcs and f.entry <= v < f.end for v in vals):
                c['resolution'], c['targets'] = 'exact', sorted(vals)
                c['reason'] = None
                tab = table_addresses(term, binary) if term[0] == 'ld' else None
                if tab:
                    tables[pc] = {'table': tab[1][0], 'entry_size': tab[0],
                                  'entries': len(tab[1]), 'relative_to': None,
                                  'targets': c['targets']}
                else:
                    tables.pop(pc, None)
            else:
                prefix = table_prefix(term, binary, f, pcs, bases) if term is not None else None
                jt = None
                if prefix:
                    # The index reaches past the table: its bound is not in this function.
                    w, addrs, targets = prefix
                    rs = roots(term[3], set())
                    by_arg = all(r == ('stack-arg',) or r[0] == 'base'
                                 or (r[0] == 'arg' and r[1] in ARGS) for r in rs)
                    c['resolution'] = 'precondition' if by_arg else 'table-heuristic'
                    jt = {'table': addrs[0], 'entry_size': w, 'entries': len(addrs),
                          'relative_to': None, 'targets': targets}
                elif pc in blocks1:
                    jt = heuristic_ijump(binary, f, blocks1[pc], insns_at(blocks1[pc], pc), c,
                                         pcs)
                    c['resolution'] = 'table-heuristic'
                if jt:
                    c['targets'] = jt['targets']
                    tables[pc] = jt
                else:
                    c['resolution'], c['targets'] = 'unresolved', []
                    tables.pop(pc, None)
            new |= set(c['targets'])
        if new <= extra:
            return blocks, tables, fl
        extra |= new


def table_prefix(term, binary, f, pcs, bases):
    """For a jump through a load from enumerated read-only slots where some slots are not code
    of the function: the leading run of slots (in address order) that are code of the function
    or its end (an unreachable default). (width, slot addresses, in-function targets) or None."""
    tab = table_addresses(term, binary)
    if tab is None or not all(binary.in_section(a, READ_ONLY) for a in tab[1]):
        return None
    w, addrs = tab
    run, targets = [], set()
    for a in addrs:
        if run and a in bases:  # the next table
            break
        word = binary.read(a, w)
        if word is None:
            break
        if term[2]:
            word = sext(word, 8 * w) & M64
        if word in pcs and f.entry <= word < f.end:
            targets.add(word)
        elif word != f.end:
            break
        run.append(a)
    if not targets or len(run) == len(addrs) or any(b - a != w for a, b in zip(run, run[1:])):
        return None
    return w, run, sorted(targets)


def insns_at(block, pc):
    return next(i for i in block if i.pc == pc)


# ---------------------------------------------------------------- interprocedural targets

def subst(v, snap, binary):
    """The callee's entry term v in the caller's state at the call."""
    k = v[0]
    if k == 'arg':
        return snap.get(v[1]) if v[1] in ARGS else TOP
    if k == 'sp':
        return snap.get('sp')
    if k == 'sum':
        out = ('c', v[1])
        for t in v[2]:
            out = add(out, subst(t, snap, binary))
        return out
    if k == 'shl':
        return shl(subst(v[1], snap, binary), v[2])
    if k == 'ld':
        return load_value(snap, binary, subst(v[3], snap, binary), v[1], v[2])
    if k in ('c', 'rng', 'set'):
        return v
    return TOP


class Interproc:
    """Targets of precondition sites, by substitution into every known caller."""

    def __init__(self, binary, cfgs):
        self.binary = binary
        self.cfgs = {cfg['f'].entry: cfg for cfg in cfgs}
        taken = set()
        for cfg in cfgs:
            taken |= cfg['flow']['taken']
        jump_slots = {jt['table'] + i * jt['entry_size'] for cfg in cfgs
                      for jt in cfg['tables'].values() for i in range(jt['entries'])}
        addr0, _ = binary.sections['.rodata']
        data = binary.section_data['.rodata']
        for off in range((-addr0) % 8, len(data) - 7, 8):
            word = int.from_bytes(data[off:off + 8], 'little')
            if word in binary.by_entry and addr0 + off not in jump_slots:
                taken.add(word)
        self.taken = taken
        self.callers = defaultdict(list)  # callee entry -> [(caller entry, site pc)]
        for cfg in cfgs:
            for pc, c in cfg['ctrl'].items():
                if c['kind'] in ('call', 'tail') or (c['kind'] == 'icall'
                                                    and c['resolution'] == 'exact'):
                    for t in c['targets']:
                        self.callers[t].append((cfg['f'].entry, pc))
        self.memo = {}

    def resolve(self, entry, term, stack=()):
        """(target entries, complete) of a precondition term of the function at `entry`."""
        key = (entry, term)
        if key in self.memo:
            return self.memo[key]
        if key in stack or len(stack) > 8:
            return set(), False
        out, complete = set(), entry not in self.taken
        for caller, pc in self.callers.get(entry, ()):
            snap = self.cfgs[caller]['flow']['snaps'].get(pc)
            if snap is None:
                complete = False
                continue
            v = subst(term, snap, self.binary)
            res, vals, _ = classify(v, self.binary, 'call')
            if res == 'exact':
                out |= vals
            elif res == 'precondition':
                sub, ok = self.resolve(caller, v, stack + (key,))
                out |= sub
                complete &= ok
            else:
                complete = False
        self.memo[key] = (out, complete)
        return out, complete

    def run(self):
        """Resolve every precondition site; callers through resolved sites join until stable."""
        for _ in range(6):
            changed = False
            self.memo = {}
            for entry, cfg in self.cfgs.items():
                for pc, c in cfg['ctrl'].items():
                    if c['kind'] != 'icall' or c['resolution'] != 'precondition':
                        continue
                    term = cfg['flow']['sites'][pc]
                    vals, ok = self.resolve(entry, term)
                    vals = sorted(v for v in vals if v in self.binary.by_entry)
                    if vals != c['targets'] or ok != c.get('targets_complete'):
                        added = set(vals) - set(c['targets'])
                        for t in added:
                            self.callers[t].append((entry, pc))
                        c['targets'], c['targets_complete'] = vals, ok
                        changed = True
            if not changed:
                break


# ---------------------------------------------------------------- irreducible regions, cycle cuts

def _sccs(nodes, succ):
    from .analyze import tarjan
    return [c for c in tarjan(sorted(nodes), succ) if len(c) > 1 or c[0] in succ[c[0]]]


def multi_entry_regions(entry, nodes, succ):
    """Strongly connected regions with more than one entry, nested ones included: each
    region's entries are removed and the rest is decomposed again (single-entry loops are
    decomposed the same way, through their head)."""
    preds = defaultdict(set)
    for n in nodes:
        for s in succ[n]:
            preds[s].add(n)
    out, work = [], [set(nodes)]
    while work:
        sub = work.pop()
        local = {n: [s for s in succ[n] if s in sub] for n in sub}
        for comp in _sccs(sub, local):
            cs = set(comp)
            entries = sorted(n for n in comp if n == entry or any(p not in cs for p in preds[n]))
            if not entries:
                entries = [comp[0]]
            if len(entries) > 1:
                out.append({'entries': entries, 'nodes': comp})
            work.append(cs - set(entries))
    out.sort(key=lambda r: (r['entries'][0], len(r['nodes'])))
    return out


def cycle_cuts(nodes, succ, cuts):
    """Nodes to add to `cuts` so that every cycle passes a cut: repeatedly, in each strongly
    connected region left after removing the cuts, cut the entry with most predecessors inside
    the region."""
    alive = set(nodes) - set(cuts)
    preds = defaultdict(set)
    for n in nodes:
        for s in succ[n]:
            preds[s].add(n)
    added = []
    while True:
        local = {n: [s for s in succ[n] if s in alive] for n in alive}
        comps = _sccs(alive, local)
        if not comps:
            return sorted(added)
        for comp in comps:
            cs = set(comp)
            entries = [n for n in comp if any(p not in cs for p in preds[n])] or comp
            best = max(entries, key=lambda n: (sum(p in cs for p in preds[n]), -n))
            added.append(best)
            alive.discard(best)


def uncut_regions(nodes, succ, cuts):
    """Strongly connected regions left after removing the cut nodes (cycles passing no cut)."""
    alive = set(nodes) - set(cuts)
    return _sccs(alive, {n: [s for s in succ[n] if s in alive] for n in alive})


# ---------------------------------------------------------------- measures

def measures(functions):
    """Sites by resolution kind (target set and all), jump resolution, cut counts of the
    irreducible functions."""
    def calls(fs):
        return Counter(c['resolution'] for f in fs for c in f['calls'] if c['kind'] == 'indirect')
    target = [f for f in functions if f['set'] == 'target']
    pre = [c for f in target for c in f['calls'] if c['resolution'] == 'precondition']
    jumps = Counter(j['resolution'] for f in target for j in f['jump_tables'])
    return {
        'indirect_calls_target': dict(calls(target)),
        'indirect_calls_all': dict(calls(functions)),
        'precondition_complete': sum(1 for c in pre if c.get('targets_complete')),
        'unknown_reasons': dict(Counter(c.get('reason') for f in target for c in f['calls']
                                        if c['resolution'] == 'unknown')),
        'indirect_jumps_target': dict(jumps),
        'irreducible': [{'name': f['name'], 'cuts_before': f['cycle']['cuts_before'],
                         'uncut_regions_before': f['cycle']['uncut_regions_before'],
                         'cycle_cuts': len(f['cycle']['added']),
                         'cuts_after': len(f['cuts']),
                         'multi_entry_regions': len(f['irreducible_regions'])}
                        for f in functions if f['irreducible']],
    }
