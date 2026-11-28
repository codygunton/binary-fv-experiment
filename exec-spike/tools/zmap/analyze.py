"""Static analysis of one RV64 ELF: functions, CFGs, calls, tables, loops, cuts, reachability.

Addresses in the output are integers. Heuristic results (indirect call candidates, jump
tables, source hints) are labelled as such and are never used in proofs.
"""
import bisect
from collections import Counter, defaultdict

from . import elfread

M64 = (1 << 64) - 1

# The instruction forms of the executor (`ZesuExec/Decode.lean`, `inductive Instr`).
FORMS = frozenset('''lui auipc jal jalr beq bne blt bltu bgeu lb lbu lhu lw ld sb sh sw sd
addi andi xori sltiu slli srli add sub and or sll sltu mul mulhu xor addiw bge lwu srliw
subw'''.split())
CSR = frozenset({'csrrw', 'csrrs', 'csrrc', 'csrrwi', 'csrrsi', 'csrrci'})
STORES = frozenset({'sb', 'sh', 'sw', 'sd', 'c.sd', 'c.sw', 'c.sdsp', 'c.swsp', 'c.fsd', 'c.fsdsp'})
LOADS = {'ld': (8, True), 'c.ld': (8, True), 'c.ldsp': (8, True), 'lw': (4, True),
         'c.lw': (4, True), 'c.lwsp': (4, True), 'lwu': (4, False)}
SHIFT_FOR_WIDTH = {8: 3, 4: 2}
TABLE_CAP = 4096


def imm(text):
    return int(text, 0)


def mem_operand(text):
    """'-0x10(sp)' -> (-16, 'sp')."""
    off, reg = text[:-1].split('(')
    return imm(off), reg


def sext(value, bits):
    value &= (1 << bits) - 1
    return value - (1 << bits) if value >> (bits - 1) else value


def jalr_parts(insn):
    """(rd, rs, imm) of an indirect jump or call, compressed forms included."""
    if insn.mn == 'jalr':
        off, rs = mem_operand(insn.ops[1])
        return insn.ops[0], rs, off
    if insn.mn == 'c.jr':
        return 'zero', insn.ops[0], 0
    if insn.mn == 'c.jalr':
        return 'ra', insn.ops[0], 0
    return None


def dest(insn):
    """Register written by an instruction, or None."""
    if insn.mn in STORES or insn.mn in elfread.BRANCHES or insn.mn in ('c.j', 'c.jr', 'ecall',
                                                                      'ebreak', 'unimp', 'fence'):
        return None
    if insn.mn in ('c.jalr', 'c.jal'):
        return 'ra'
    if not insn.ops:
        return None
    rd = insn.ops[0]
    return None if rd == 'zero' or '(' in rd else rd


# ---------------------------------------------------------------- block-local values

def evaluate(block_insns, upto_pc):
    """Symbolic register values after the instructions of a block before `upto_pc`.

    Values: ('c', n) constant; ('r', reg) value at block start; ('u', pc) unknown;
    ('add', a, b); ('shl', a, k); ('ld', width, signed, addr, k, pc).
    """
    regs = {}

    def get(r):
        if r == 'zero':
            return ('c', 0)
        return regs.get(r, ('r', r))

    def add(a, b):
        if a[0] == 'c' and b[0] == 'c':
            return ('c', (a[1] + b[1]) & M64)
        if b == ('c', 0):
            return a
        if a == ('c', 0):
            return b
        return ('add', a, b)

    for insn in block_insns:
        if insn.pc >= upto_pc:
            break
        mn, ops = insn.mn, insn.ops
        rd = dest(insn)
        if rd is None:
            continue
        if mn == 'auipc':
            val = ('c', (insn.pc + (sext(imm(ops[1]), 20) << 12)) & M64)
        elif mn in ('lui', 'c.lui'):
            val = ('c', (sext(imm(ops[1]), 20) << 12) & M64)
        elif mn in ('addi', 'c.addi'):
            src = ops[1] if mn == 'addi' else ops[0]
            val = add(get(src), ('c', imm(ops[-1]) & M64))
        elif mn in ('c.li',):
            val = ('c', imm(ops[1]) & M64)
        elif mn in ('add',):
            val = add(get(ops[1]), get(ops[2]))
        elif mn == 'c.add':
            val = add(get(ops[0]), get(ops[1]))
        elif mn == 'c.mv':
            val = get(ops[1])
        elif mn in ('slli', 'c.slli'):
            src, k = (ops[1], imm(ops[2])) if mn == 'slli' else (ops[0], imm(ops[1]))
            v = get(src)
            val = ('c', (v[1] << k) & M64) if v[0] == 'c' else ('shl', v, k)
        elif mn in LOADS:
            width, signed = LOADS[mn]
            off, base = mem_operand(ops[1])
            val = ('ld', width, signed, add(get(base), ('c', off & M64)), off, insn.pc)
        else:
            val = ('u', insn.pc)
        regs[rd] = val
    return get


def linear(v):
    """Flatten nested adds: (constant, [non-constant terms])."""
    if v[0] == 'c':
        return v[1], []
    if v[0] == 'add':
        c1, t1 = linear(v[1])
        c2, t2 = linear(v[2])
        return (c1 + c2) & M64, t1 + t2
    return 0, [v]


# ---------------------------------------------------------------- dominators, loops

def dominators(entry, succ):
    """Immediate dominators (Cooper, Harvey, Kennedy) of the nodes reachable from entry."""
    order, seen, stack = [], {entry}, [(entry, iter(succ[entry]))]
    while stack:
        node, it = stack[-1]
        for s in it:
            if s not in seen:
                seen.add(s)
                stack.append((s, iter(succ[s])))
                break
        else:
            order.append(node)
            stack.pop()
    rpo = order[::-1]
    index = {n: i for i, n in enumerate(rpo)}
    preds = defaultdict(list)
    for n in rpo:
        for s in succ[n]:
            preds[s].append(n)
    idom = {entry: entry}

    def intersect(a, b):
        while a != b:
            while index[a] > index[b]:
                a = idom[a]
            while index[b] > index[a]:
                b = idom[b]
        return a

    changed = True
    while changed:
        changed = False
        for n in rpo[1:]:
            done = [p for p in preds[n] if p in idom]
            new = done[0]
            for p in done[1:]:
                new = intersect(p, new)
            if idom.get(n) != new:
                idom[n] = new
                changed = True
    return idom


def dominates(idom, a, b):
    """a dominates b (both reachable)."""
    while True:
        if a == b:
            return True
        parent = idom[b]
        if parent == b:
            return False
        b = parent


def natural_loop(head, tail, preds):
    body, stack = {head, tail}, [tail]
    while stack:
        n = stack.pop()
        if n == head:
            continue
        for p in preds[n]:
            if p not in body:
                body.add(p)
                stack.append(p)
    return body


# ---------------------------------------------------------------- path counting

def segment_counts(start, succ, sink):
    """Acyclic paths from `start` with `sink(node)` nodes ending paths.

    Returns (paths, into): paths = number of paths from start to a path end; into[b] = number
    of paths from start that arrive at b. An edge that closes a cycle in the depth-first search
    (possible only in irreducible regions) ends its path.
    """
    order, state, stack = [], {start: 1}, [(start, iter(succ[start]))]
    retreat = set()
    while stack:
        node, it = stack[-1]
        for s in it:
            if sink(s) and s != node:
                continue
            st = state.get(s)
            if st is None:
                state[s] = 1
                stack.append((s, iter(succ[s]) if not sink(s) or s == start else iter(())))
                break
            if st == 1:
                retreat.add((node, s))
        else:
            state[node] = 2
            order.append(node)
            stack.pop()
    out = {}
    for n in order:  # postorder: successors first
        if n != start and sink(n):
            out[n] = 1
            continue
        succs = succ[n]
        if not succs:
            out[n] = 1
            continue
        total = 0
        for s in succs:
            if (n, s) in retreat or (sink(s) and s != n) or s == start:
                total += 1
            else:
                total += out[s]
        out[n] = total
    into = defaultdict(int)
    into[start] = 1
    for n in reversed(order):
        if n != start and sink(n):
            continue
        for s in succ[n]:
            if (n, s) in retreat or s == start:
                continue
            into[s] += into[n]
    return out[start], into


# ---------------------------------------------------------------- function analysis

class Function:
    def __init__(self, entry, size, name, aliases):
        self.entry, self.size, self.name, self.aliases = entry, size, name, aliases
        self.end = entry + size
        self.id = f'f_{entry:x}'


class Binary:
    """Shared context: instructions, function index, section bytes, function-pointer tables."""

    def __init__(self, insns, functions, sections, section_data):
        self.insns = insns
        self.pcs = sorted(insns)
        self.functions = functions
        self.by_entry = {f.entry: f for f in functions}
        self.starts = sorted(self.by_entry)
        self.sections = sections
        self.section_data = section_data
        self.fn_tables = []

    def function_at(self, addr):
        i = bisect.bisect_right(self.starts, addr) - 1
        if i >= 0:
            f = self.by_entry[self.starts[i]]
            if addr < f.end:
                return f
        return None

    def read(self, addr, width):
        for name, data in self.section_data.items():
            base = self.sections[name][0]
            if base <= addr and addr + width <= base + len(data):
                return int.from_bytes(data[addr - base:addr - base + width], 'little')
        return None

    def in_section(self, addr, names):
        return any(self.sections[n][0] <= addr < self.sections[n][0] + self.sections[n][1]
                   for n in names if n in self.sections)

    def function_insns(self, f):
        lo = bisect.bisect_left(self.pcs, f.entry)
        hi = bisect.bisect_left(self.pcs, f.end)
        return [self.insns[pc] for pc in self.pcs[lo:hi]]

    def scan_fn_tables(self):
        """Runs of >= 2 consecutive 8-byte words in .rodata that are function entries."""
        addr0, _ = self.sections['.rodata']
        data = self.section_data['.rodata']
        run = []
        tables = []
        start = (-addr0) % 8
        for off in range(start, len(data) - 7, 8):
            word = int.from_bytes(data[off:off + 8], 'little')
            if word in self.by_entry:
                run.append(word)
                continue
            if len(run) >= 2:
                tables.append({'addr': addr0 + off - 8 * len(run), 'slots': run})
            run = []
        if len(run) >= 2:
            tables.append({'addr': addr0 + len(data) - len(data) % 8 - 8 * len(run), 'slots': run})
        self.fn_tables = tables


def classify(binary, f, insns):
    """Control effect of each control instruction: pc -> dict."""
    ctrl = {}
    prev = None
    for insn in insns:
        mn = insn.mn
        if mn in elfread.BRANCHES:
            ctrl[insn.pc] = {'kind': 'branch', 'target': insn.target}
        elif mn in ('jal', 'c.j', 'c.jal'):
            rd = 'zero' if mn == 'c.j' else ('ra' if mn == 'c.jal' else insn.ops[0])
            t = insn.target
            if rd != 'zero':
                ctrl[insn.pc] = {'kind': 'call', 'targets': [t], 'resolution': 'direct'}
            elif f.entry <= t < f.end and t != f.entry:
                ctrl[insn.pc] = {'kind': 'jump', 'target': t}
            else:
                ctrl[insn.pc] = {'kind': 'tail', 'targets': [t], 'resolution': 'direct'}
        elif mn in ('jalr', 'c.jr', 'c.jalr'):
            rd, rs, off = jalr_parts(insn)
            far = (prev is not None and prev.mn == 'auipc' and prev.ops[0] == rs
                   and prev.next == insn.pc)
            if far:
                t = (prev.pc + (sext(imm(prev.ops[1]), 20) << 12) + off) & M64
                if rd != 'zero':
                    ctrl[insn.pc] = {'kind': 'call', 'targets': [t], 'resolution': 'direct'}
                elif f.entry <= t < f.end and t != f.entry:
                    ctrl[insn.pc] = {'kind': 'jump', 'target': t}
                else:
                    ctrl[insn.pc] = {'kind': 'tail', 'targets': [t], 'resolution': 'direct'}
            elif rd == 'zero' and rs == 'ra' and off == 0:
                ctrl[insn.pc] = {'kind': 'ret'}
            elif rd != 'zero':
                ctrl[insn.pc] = {'kind': 'icall', 'rs': rs, 'off': off}
            else:
                ctrl[insn.pc] = {'kind': 'ijump', 'rs': rs, 'off': off}
        elif mn == 'unimp':
            ctrl[insn.pc] = {'kind': 'trap'}
        prev = insn
    return ctrl


def split_blocks(f, insns, ctrl, extra_leaders):
    pcs = {i.pc for i in insns}
    leaders = {f.entry} | {t for t in extra_leaders if t in pcs}
    for insn in insns:
        c = ctrl.get(insn.pc)
        if c is None:
            continue
        if c['kind'] in ('branch', 'jump') and c['target'] in pcs:
            leaders.add(c['target'])
        if insn.next in pcs:
            leaders.add(insn.next)
    blocks, cur = [], []
    for insn in insns:
        if insn.pc in leaders and cur:
            blocks.append(cur)
            cur = []
        cur.append(insn)
    if cur:
        blocks.append(cur)
    return blocks


def resolve_icall(binary, block, insn, c):
    """Indirect call: candidates from function-pointer tables when the target came from `ld t, k(b)`."""
    if c['off'] != 0:
        return [], 'unresolved'
    v = evaluate(block, insn.pc)(c['rs'])
    if v[0] == 'ld' and v[1] == 8 and v[4] >= 0 and v[4] % 8 == 0:
        slot = v[4] // 8
        cands = sorted({t['slots'][slot] for t in binary.fn_tables if len(t['slots']) > slot})
        if cands:
            return cands, 'table-heuristic'
    return [], 'unresolved'


def resolve_ijump(binary, f, block, insn, c, pcs):
    """Jump table: target loaded from base + (idx << 2|3), base a constant in .rodata/.text."""
    v = evaluate(block, insn.pc)(c['rs'])
    rel = None
    if v[0] == 'add':
        k, terms = linear(v)
        if len(terms) == 1 and terms[0][0] == 'ld':
            rel, v = k, terms[0]
    if v[0] != 'ld' or c['off'] != 0 and rel is None:
        return None
    if rel is None:
        rel_base = 0
    else:
        rel_base = (rel + c['off']) & M64
    width, signed = v[1], v[2]
    base, terms = linear(v[3])
    shift = SHIFT_FOR_WIDTH.get(width)
    if shift is None or len(terms) != 1 or terms[0][0] != 'shl' or terms[0][2] != shift:
        return None
    if not binary.in_section(base, ('.rodata', '.text')):
        return None
    targets, n = [], 0
    while n < TABLE_CAP:
        word = binary.read(base + n * width, width)
        if word is None:
            break
        if signed:
            word = sext(word, width * 8) & M64
        t = (word + (rel_base if rel is not None else (c['off'] & M64))) & M64
        if not (f.entry <= t < f.end and t in pcs):
            break
        targets.append(t)
        n += 1
    if not targets:
        return None
    return {'table': base, 'entry_size': width, 'entries': n,
            'relative_to': rel_base if rel is not None else None,
            'targets': sorted(set(targets))}


def function_cfg(binary, f):
    """Blocks, edges, calls and exits of one function (call blocks still fall through)."""
    insns = binary.function_insns(f)
    pcs = {i.pc for i in insns}
    ctrl = classify(binary, f, insns)

    # Pass 1: blocks without table targets; resolve indirect transfers block-locally.
    blocks1 = split_blocks(f, insns, ctrl, ())
    tables = {}
    for block in blocks1:
        last = block[-1]
        c = ctrl.get(last.pc)
        if c is None:
            continue
        if c['kind'] == 'icall':
            c['targets'], c['resolution'] = resolve_icall(binary, block, last, c)
        elif c['kind'] == 'ijump':
            jt = resolve_ijump(binary, f, block, last, c, pcs)
            if jt:
                tables[last.pc] = jt
                c['targets'], c['resolution'] = jt['targets'], 'table-heuristic'
            else:
                c['targets'], c['resolution'] = [], 'unresolved'
    extra = {t for jt in tables.values() for t in jt['targets']}
    blocks = split_blocks(f, insns, ctrl, extra) if extra else blocks1
    starts = [b[0].pc for b in blocks]
    start_set = set(starts)

    # Edges and exits.
    succ = {s: [] for s in starts}
    edges = []
    calls = []
    call_at = {}  # block start -> call record of its last instruction
    exits = {}  # block start -> exit kind of its last instruction

    def edge(a, b, kind):
        if b in start_set and b not in succ[a]:
            succ[a].append(b)
            edges.append({'from': a, 'to': b, 'kind': kind})

    for block in blocks:
        s, last = block[0].pc, block[-1]
        c = ctrl.get(last.pc)
        kind = c['kind'] if c else None
        if kind == 'branch':
            t = c['target']
            if t in start_set:
                edge(s, t, 'taken')
            else:
                tf = binary.function_at(t)
                calls.append({'site': last.pc, 'ret': None, 'kind': 'tail',
                              'targets': [tf.id] if tf else [], 'resolution': 'direct'})
            edge(s, last.next, 'fall')
        elif kind == 'jump':
            edge(s, c['target'], 'jump')
        elif kind in ('call', 'icall'):
            targets = c['targets']
            ids = sorted({binary.function_at(t).id for t in targets if binary.function_at(t)})
            call = {'site': last.pc, 'ret': last.next,
                    'kind': 'direct' if kind == 'call' else 'indirect',
                    'targets': ids, 'resolution': c['resolution']}
            calls.append(call)
            call_at[s] = call
            exits[s] = 'call'
            edge(s, last.next, 'fall')
        elif kind == 'tail':
            tf = binary.function_at(c['targets'][0])
            call = {'site': last.pc, 'ret': None, 'kind': 'tail',
                    'targets': [tf.id] if tf else [], 'resolution': 'direct'}
            calls.append(call)
            call_at[s] = call
            exits[s] = 'tail'
        elif kind == 'ret':
            exits[s] = 'ret'
        elif kind == 'trap':
            exits[s] = 'trap'
        elif kind == 'ijump':
            for t in c['targets']:
                edge(s, t, 'table')
            exits[s] = 'jumpInd' if c['resolution'] == 'unresolved' else 'table'
        else:
            edge(s, last.next, 'fall')
    return {'f': f, 'insns': insns, 'ctrl': ctrl, 'tables': tables, 'blocks': blocks,
            'starts': starts, 'succ': succ, 'edges': edges, 'calls': calls, 'exits': exits,
            'call_at': call_at}


def no_return_call(call, noreturn):
    """A direct call whose callee never returns (by the fixpoint in `build`)."""
    return call['kind'] == 'direct' and bool(call['targets']) and all(
        t in noreturn for t in call['targets'])


def may_return(cfg, noreturn):
    """Some path from the entry reaches a return, a returning tail call, an unresolved
    indirect jump, or the end of the function."""
    f, succ, exits, call_at = cfg['f'], cfg['succ'], cfg['exits'], cfg['call_at']
    seen, stack = {f.entry}, [f.entry]
    while stack:
        s = stack.pop()
        ex = exits.get(s)
        if ex in ('ret', 'jumpInd'):
            return True
        if ex == 'tail' and not all(t in noreturn for t in call_at[s]['targets'] or [None]):
            return True
        if ex == 'call' and no_return_call(call_at[s], noreturn):
            continue
        if ex in (None, 'call') and not succ[s]:
            return True  # falls off the end of the function
        for t in succ[s]:
            if t not in seen:
                seen.add(t)
                stack.append(t)
    return False


def analyze_function(binary, cfg, noreturn, join_cuts=False):
    f, insns, ctrl, tables = cfg['f'], cfg['insns'], cfg['ctrl'], cfg['tables']
    blocks, starts, exits, calls = cfg['blocks'], cfg['starts'], cfg['exits'], cfg['calls']
    start_set = set(starts)
    # A call to a function that never returns has no fall-through edge.
    dead_fall = set()
    for s, call in cfg['call_at'].items():
        if exits[s] == 'call' and no_return_call(call, noreturn):
            call['noreturn'] = True
            dead_fall.add(s)
    edges = [e for e in cfg['edges'] if not (e['from'] in dead_fall and e['kind'] == 'fall')]
    succ = {s: [t for t in cfg['succ'][s] if s not in dead_fall] for s in starts}

    # Dominators, back edges, loops.
    idom = dominators(f.entry, succ)
    preds = defaultdict(list)
    for e in edges:
        preds[e['to']].append(e['from'])
    back = set()
    for e in edges:
        a, b = e['from'], e['to']
        if a in idom and b in idom and dominates(idom, b, a):
            e['kind'] = 'back'
            back.add((a, b))
    # An edge to an earlier address that is not a back edge is irreducible only when it lies
    # on a cycle of the graph without back edges (a layout jump to a lower address is not).
    fwd_succ = {s: [] for s in starts}
    for e in edges:
        if e['kind'] != 'back':
            fwd_succ[e['from']].append(e['to'])
    component = {n: i for i, comp in enumerate(tarjan(starts, fwd_succ)) for n in comp}
    irreducible = [(e['from'], e['to']) for e in edges
                   if e['kind'] != 'back' and e['to'] <= e['from']
                   and component[e['from']] == component[e['to']]]
    loop_bodies = defaultdict(set)
    for a, b in back:
        loop_bodies[b] |= natural_loop(b, a, preds)
    heads = set(loop_bodies)

    # Joins: two or more forward predecessors, not a loop head.
    fwd_preds = Counter(e['to'] for e in edges if e['kind'] != 'back')
    joins = sorted(s for s in starts if fwd_preds[s] >= 2 and s not in heads)

    # Cut points: entry, loop heads, call return sites.
    cuts = {f.entry: 'entry'}
    for h in sorted(heads):
        cuts.setdefault(h, 'loop')
    for c in calls:
        if c['ret'] in start_set and c['kind'] != 'tail' and not c.get('noreturn'):
            cuts.setdefault(c['ret'], 'ret')

    # Paths per segment; a call block ends its leaf at the call.
    seg_succ = {s: ([] if exits.get(s) in ('call', 'table') else succ[s]) for s in starts}
    join_set = set(joins)

    def segments(cuts):
        leaves, fanin = 0, Counter()
        for cp in sorted(cuts):
            paths, into = segment_counts(cp, seg_succ, lambda n: n in cuts)
            leaves += paths
            for j, k in into.items():
                if j in join_set and j != cp:
                    fanin[j] += k
        return leaves, fanin

    leaves, fanin = segments(cuts)
    candidates = [j for j in joins if fanin[j] >= 4]
    # Join cuts (default; `--no-join-cuts` turns them off): the join cut candidates of the fixed
    # rule become cut points too (S5 probe 1 passed); paths and fan-in are recounted with them.
    if join_cuts and candidates:
        for j in candidates:
            cuts.setdefault(j, 'join')
        leaves, fanin = segments(cuts)

    # Layout: longest path layer over the forward graph, order by address.
    layer = {}
    fwd = defaultdict(list)
    indeg = Counter()
    irr = set(irreducible)
    for e in edges:
        if e['kind'] != 'back' and (e['from'], e['to']) not in irr:
            fwd[e['from']].append(e['to'])
            indeg[e['to']] += 1
    ready = [s for s in starts if indeg[s] == 0]
    for s in ready:
        layer[s] = 0
    while ready:
        n = ready.pop()
        for s in fwd[n]:
            layer[s] = max(layer.get(s, 0), layer[n] + 1)
            indeg[s] -= 1
            if indeg[s] == 0:
                ready.append(s)
    for s in starts:  # nodes left on a cycle of the forward graph (should not happen)
        layer.setdefault(s, 0)
    by_layer = defaultdict(list)
    for s in starts:
        by_layer[layer[s]].append(s)
    xy = {}
    for y, row in by_layer.items():
        for x, s in enumerate(sorted(row)):
            xy[s] = (x, y)

    # Forms and blockers.
    forms = Counter(i.mn for i in insns)
    unsupported = Counter()
    compressed = 0
    ecalls = []
    for i in insns:
        if i.size == 2:
            compressed += 1
        elif i.mn == 'ecall':
            ecalls.append(i.pc)
        elif i.mn in CSR:
            unsupported[f'{i.mn}:{csr_number(i)}'] += 1
        elif i.mn not in FORMS:
            unsupported[i.mn] += 1
    blockers = []
    if unsupported:
        blockers.append({'kind': 'unsupported-form', 'detail': dict(sorted(unsupported.items()))})
    if compressed:
        blockers.append({'kind': 'compressed', 'detail': compressed})
    ic = [c['site'] for c in calls if c['kind'] == 'indirect' and c['resolution'] == 'unresolved']
    if ic:
        blockers.append({'kind': 'indirect-call-unresolved', 'detail': ic})
    ij = [pc for pc, c in sorted(ctrl.items()) if c['kind'] == 'ijump' and c['resolution'] == 'unresolved']
    if ij:
        blockers.append({'kind': 'indirect-jump-unresolved', 'detail': ij})
    if irreducible:
        blockers.append({'kind': 'irreducible', 'detail': [list(e) for e in sorted(irreducible)]})
    if ecalls:
        blockers.append({'kind': 'ecall', 'detail': ecalls})

    jump_tables = []
    for pc, c in sorted(ctrl.items()):
        if c['kind'] == 'ijump':
            jt = tables.get(pc)
            row = {'site': pc, 'resolution': c['resolution'], 'targets': c['targets']}
            if jt:
                row.update(table=jt['table'], entry_size=jt['entry_size'], entries=jt['entries'],
                           relative_to=jt['relative_to'])
            jump_tables.append(row)

    out_blocks = []
    for block in blocks:
        s = block[0].pc
        out_blocks.append({'start': s, 'end': block[-1].next, 'n': len(block), 'succ': succ[s],
                           'kind': 'loop_head' if s in heads else 'join' if s in join_set else 'plain',
                           'x': xy[s][0], 'y': xy[s][1], 'src': None})
    return {
        'id': f.id, 'name': f.name, 'aliases': f.aliases, 'entry': f.entry, 'size': f.size,
        'n_instr': len(insns), 'set': 'other', 'recursive': False,
        'irreducible': bool(irreducible),
        'blocks': out_blocks, 'edges': edges, 'calls': calls,
        'jump_tables': jump_tables,
        'loops': [{'head': h, 'body': sorted(loop_bodies[h])} for h in sorted(heads)],
        'joins': [{'at': j, 'fanin_paths': fanin[j]} for j in joins],
        'cuts': [{'pc': pc, 'why': why} for pc, why in sorted(cuts.items())],
        'join_cut_candidates': candidates,
        'leaves_estimate': leaves,
        'forms': dict(sorted(forms.items())),
        'blockers': blockers,
        'callees': [], 'callers': [], 'order': None,
    }


def csr_number(insn):
    """CSR operand of a Zicsr instruction as a hex string (named CSRs keep their name)."""
    try:
        return f'{imm(insn.ops[1]):#x}'
    except ValueError:
        return insn.ops[1]


# ---------------------------------------------------------------- whole binary

def tarjan(nodes, succ):
    """Strongly connected components in reverse topological order (callees first)."""
    index, low, on, stack, comps = {}, {}, set(), [], []
    counter = 0
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(succ[root]))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on.add(root)
        while work:
            node, it = work[-1]
            for s in it:
                if s not in index:
                    index[s] = low[s] = counter
                    counter += 1
                    stack.append(s)
                    on.add(s)
                    work.append((s, iter(succ[s])))
                    break
                if s in on:
                    low[node] = min(low[node], index[s])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[node])
                if low[node] == index[node]:
                    comp = []
                    while True:
                        w = stack.pop()
                        on.discard(w)
                        comp.append(w)
                        if w == node:
                            break
                    comps.append(sorted(comp))
    return comps


def load_functions(symbols):
    """Group FUNC symbols by entry; the longest size wins, the others are aliases."""
    by_entry = defaultdict(list)
    for entry, size, name in symbols:
        by_entry[entry].append((size, name))
    out = []
    for entry, syms in sorted(by_entry.items()):
        syms.sort(key=lambda t: (-t[0], t[1]))
        size, name = syms[0]
        out.append(Function(entry, size, name, [n for _, n in syms[1:]]))
    return out


def build(elf, start_symbol='_start', join_cuts=True):
    """Analyse the ELF; return the static map dict (without hints)."""
    sections = elfread.sections(elf)
    functions = load_functions(elfread.func_symbols(elf))
    insns = elfread.disassemble(elf)
    data = {name: elfread.section_bytes(elf, name) for name in ('.rodata', '.text')}
    binary = Binary(insns, functions, sections, data)
    binary.scan_fn_tables()

    cfgs = [function_cfg(binary, f) for f in functions]
    # Functions that never return: greatest fixpoint, starting from "none returns".
    noreturn = {f.id for f in functions}
    changed = True
    while changed:
        changed = False
        for cfg in cfgs:
            if cfg['f'].id in noreturn and may_return(cfg, noreturn):
                noreturn.discard(cfg['f'].id)
                changed = True
    fns = [analyze_function(binary, cfg, noreturn, join_cuts) for cfg in cfgs]
    for fn in fns:
        fn['noreturn'] = fn['id'] in noreturn
    by_id = {fn['id']: fn for fn in fns}

    # Call graph.
    callees = {fn['id']: sorted({t for c in fn['calls'] for t in c['targets']}) for fn in fns}
    callers = defaultdict(set)
    for a, bs in callees.items():
        for b in bs:
            callers[b].add(a)

    # Reachability.
    start = binary.function_at(elfread.symbol_value(elf, start_symbol))
    target, stack = {start.id}, [start.id]
    while stack:
        for b in callees[stack.pop()]:
            if b not in target:
                target.add(b)
                stack.append(b)
    in_tables = {f'f_{e:x}' for t in binary.fn_tables for e in t['slots']}

    # SCCs and bottom-up order of the target set.
    ids = [fn['id'] for fn in fns]
    comps = tarjan(ids, callees)
    recursive = set()
    for comp in comps:
        if len(comp) > 1 or comp[0] in callees[comp[0]]:
            recursive.update(comp)
    order = 0
    for comp in tarjan(sorted(target), {a: [b for b in callees[a] if b in target] for a in target}):
        for n in comp:
            by_id[n]['order'] = order
            order += 1

    for fn in fns:
        fid = fn['id']
        fn['set'] = 'target' if fid in target else 'maybe' if fid in in_tables else 'other'
        fn['recursive'] = fid in recursive
        fn['callees'] = callees[fid]
        fn['callers'] = sorted(callers[fid])

    csr = Counter()
    for i in insns.values():
        if i.mn in CSR and binary.function_at(i.pc):
            csr[csr_number(i)] += 1

    tables = [{'kind': 'fnptr', 'addr': t['addr'], 'slots': [f'f_{e:x}' for e in t['slots']]}
              for t in binary.fn_tables]
    for fn in fns:
        for jt in fn['jump_tables']:
            if 'table' in jt:
                tables.append({'kind': 'jump', 'addr': jt['table'], 'function': fn['id'],
                               'site': jt['site'], 'entry_size': jt['entry_size'],
                               'entries': jt['entries'], 'targets': jt['targets']})
    return {
        'schema': 'zmap.static.v1',
        'elf_sha256': None,
        'functions': fns,
        'tables': tables,
        'csr_numbers': dict(sorted(csr.items())),
    }
