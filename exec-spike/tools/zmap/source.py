"""Source functions and source edges of the target set (plan S9.4).

The unit a person reads is the source function, not the binary symbol. From the debug object's
full inline chains (`vendor/dwarf.py` `inline_frames`) and line table, every target instruction
is assigned to its innermost source function, or to a `compiler` bucket of its binary function
when it has no source line, or to a `runtime` bucket when the debug object has no code for it.

A source function is keyed by its declaration (file, line), so a generic's compiled copies are
one record with all their instances. Each record lists its locations: the binary functions it
is compiled out of line as, and the ones it is inlined into, with exclusive instruction counts
and the blocks it appears in (anywhere in the inline chain). Source edges join source functions
through sites: an inlined subroutine (kind `inlined`, at its DW_AT_call_file:line), a call
instruction (`call`, `tail`, `indirect` with its resolution), or a CSR access (`accelerator`
with the CSR number). Everything here is heuristic display data; proofs never read it.
"""
import bisect
import os
import re
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'vendor'))

from .analyze import CSR, csr_number  # noqa: E402

GROUPS = ('zesu', 'std', 'runtime', 'compiler', 'accelerator')
SRC_MARK = '/p0c-zesu-source/src/'
STD_MARK = '/lib/zig/std/'
# Worst-first orders of the colour layers; a source function takes the worst over its locations.
PROOF_ORDER = ('blocked', 'waiting', 'ready', 'contract-draft', 'in-proof', 'conditional', 'assumed',
               'closed-on-assumptions', 'closed', 'closed+sail', 'closed+compliance', 'out')
MEANING_ORDER = ('none', 'machine-only', 'model', 'spec-sail')
CONTRACT_ORDER = ('none', 'draft', 'transcribed', 'reviewed')
TRUST_ORDER = ('assumed', 'service', 'rests on trusted', 'rests on nothing trusted')
ANON = re.compile(r'__anon_\d+$')


def group_of(path):
    if not path:
        return 'runtime'
    if SRC_MARK in path:
        return 'zesu'
    if STD_MARK in path:
        return 'std'
    return 'runtime'


def short_path(path):
    if path and SRC_MARK in path:
        return path.split(SRC_MARK, 1)[1]
    if path and STD_MARK in path:
        return 'std/' + path.split(STD_MARK, 1)[1]
    return path


def qualname(name):
    """Linkage name without `__anon_N` and with generic arguments folded to `(…)`."""
    name = ANON.sub('', name or '?')
    out, depth = [], 0
    for ch in name:
        if ch == '(':
            if depth == 0:
                out.append('(…)')
            depth += 1
        elif ch == ')':
            depth = max(depth - 1, 0)
        elif depth == 0:
            out.append(ch)
    return ''.join(out)


def worst(values, order):
    present = [v for v in values if v in order]
    return min(present, key=order.index) if present else None


def trust_value(f):
    if f.get('assumed'):
        return 'assumed'
    if f.get('service'):
        return 'service'
    return 'rests on trusted' if f.get('rests_on') else 'rests on nothing trusted'


def contract_value(f):
    c = f.get('contract')
    if not c:
        return 'none'
    return 'reviewed' if c.get('review') == 'reviewed' else (c.get('contract') or 'draft')


def build(m, insns, frames, rows):
    """Source data of the target set.

    m: map.json; insns: pc -> Insn (elfread.disassemble); frames: dwarf.inline_frames;
    rows: dwarf.line_rows. Returns {'functions', 'edges', 'files', 'stats', 'pc_owner'}; pc_owner
    maps every target instruction to the index of its source function (for tests).
    """
    fns = [f for f in m['functions'] if f['set'] == 'target']
    by_id = {f['id']: f for f in m['functions']}

    # Target instructions: pc -> (function id, block index).
    pcs, where = [], {}
    for f in fns:
        for bi, b in enumerate(f['blocks']):
            pc = b['start']
            while pc < b['end']:
                i = insns.get(pc)
                pcs.append(pc)
                where[pc] = (f['id'], bi)
                pc = i.next if i is not None else pc + 2
    pcs.sort()

    # Innermost frame per pc: the deepest frame whose ranges hold it.
    inner = {}
    for k, fr in enumerate(frames):
        for lo, hi in fr['ranges']:
            for j in range(bisect.bisect_left(pcs, lo), bisect.bisect_left(pcs, hi)):
                pc = pcs[j]
                cur = inner.get(pc)
                if cur is None or frames[cur]['depth'] < fr['depth']:
                    inner[pc] = k

    row_lo = [r[0] for r in rows]

    def line_at(pc):
        i = bisect.bisect_right(row_lo, pc) - 1
        if i >= 0 and rows[i][0] <= pc < rows[i][1]:
            return rows[i][2], rows[i][3]
        return None

    # Source functions.
    sfs, key_index = [], {}

    def sf_for(key, **fields):
        if key not in key_index:
            key_index[key] = len(sfs)
            sfs.append(dict(fields, id=len(sfs), instances=set(), loc={}, lines=[], ))
        return key_index[key]

    frame_sf = {}

    def sf_of_frame(k):
        if k not in frame_sf:
            fr = frames[k]
            key = (fr['decl_file'], fr['decl_line']) if fr['decl_file'] else ('?', fr['name'])
            s = sf_for(key, kind='source', name=qualname(fr['name']), short=fr['short'],
                       file=fr['decl_file'], decl_line=fr['decl_line'], group=group_of(fr['decl_file']))
            sfs[s]['instances'].add(ANON.sub('', fr['name'] or '?'))
            frame_sf[k] = s
        return frame_sf[k]

    def bucket(kind, f):
        return sf_for((kind, f['id']), kind=kind, name=f'{f["name"]} ({kind})', short=f['name'],
                      file=None, decl_line=None, group=kind)

    def loc(s, fid):
        L = sfs[s]['loc'].get(fid)
        if L is None:
            L = sfs[s]['loc'][fid] = {'fn': fid, 'instr': 0, 'blocks': set(), 'out_of_line': False}
        return L

    # Assign instructions; record chains, lines and out-of-line placements.
    owner = {}
    no_line_with_frame = 0
    for f in fns:
        k0 = inner.get(f['entry'])
        while k0 is not None and frames[k0]['parent'] is not None:
            k0 = frames[k0]['parent']
        if k0 is not None:
            loc(sf_of_frame(k0), f['id'])['out_of_line'] = True
    for pc in pcs:
        fid, bi = where[pc]
        f = by_id[fid]
        k = inner.get(pc)
        ln = line_at(pc)
        if k is None:
            s = bucket('runtime', f)
            loc(s, fid)['out_of_line'] = True
        elif ln is None:
            no_line_with_frame += 1
            s = bucket('compiler', f)
        else:
            s = sf_of_frame(k)
            if ln[0] == sfs[s]['file']:
                sfs[s]['lines'].append(ln[1])
        owner[pc] = s
        L = loc(s, fid)
        L['instr'] += 1
        L['blocks'].add(bi)
        while k is not None:        # every source function of the inline chain appears in the block
            loc(sf_of_frame(k), fid)['blocks'].add(bi)
            k = frames[k]['parent']

    # Edges: {(from, to): [site, ...]}, a site = (file, line, kind, addr, extra).
    edges = defaultdict(set)
    covered = {}
    for pc in pcs:
        k = inner.get(pc)
        while k is not None and k not in covered:
            covered[k] = pc
            k = frames[k]['parent']
    for k, pc in covered.items():
        fr = frames[k]
        if fr['parent'] is None:
            continue
        first = min(lo for lo, hi in fr['ranges'])
        edges[(sf_of_frame(fr['parent']), sf_of_frame(k))].add(
            (fr['call_file'], fr['call_line'], 'inlined', first, None))
    # Code without a source line: one site per (frame, bucket) carrying the instruction count.
    no_line = Counter()
    first_pc = {}
    for pc in pcs:
        s = owner[pc]
        if sfs[s]['kind'] == 'compiler' and inner.get(pc) is not None:
            key = (sf_of_frame(inner[pc]), s)
            no_line[key] += 1
            first_pc.setdefault(key, pc)
    for key, n in no_line.items():
        edges[key].add((None, None, 'inlined', first_pc[key], f'no line: {n} instructions'))

    def attrib(pc):
        """(source function, file, line) a call or CSR site at `pc` is drawn from: the innermost
        Zesu frame of the chain (std helpers inlined into Zesu code fold into the line of Zesu
        source that reached them), else the innermost frame; buckets when there is no frame."""
        k = inner.get(pc)
        if k is None:
            return owner[pc], None, None
        child = None
        while k is not None and sfs[sf_of_frame(k)]['group'] != 'zesu':
            child, k = k, frames[k]['parent']
        if k is None:                       # no Zesu frame: the innermost one
            k, child = inner[pc], None
        if child is None:
            ln = line_at(pc)
            return sf_of_frame(k), ln[0] if ln else None, ln[1] if ln else None
        return sf_of_frame(k), frames[child]['call_file'], frames[child]['call_line']

    accel = {}
    for f in fns:
        for c in f['calls']:
            pc = c['site']
            if pc not in owner:
                continue
            s, file, line = attrib(pc)
            kind = {'direct': 'call', 'tail': 'tail', 'indirect': 'indirect'}[c['kind']]
            for t in c['targets']:
                g = by_id.get(t)
                if g is None:
                    continue
                k0 = inner.get(g['entry'])
                while k0 is not None and frames[k0]['parent'] is not None:
                    k0 = frames[k0]['parent']
                callee = sf_of_frame(k0) if k0 is not None else bucket('runtime', g)
                edges[(s, callee)].add((file, line, kind, pc,
                                        c['resolution'] if kind == 'indirect' else None))
    for pc in pcs:
        i = insns.get(pc)
        if i is None or i.mn not in CSR:
            continue
        num = csr_number(i)
        if num not in accel:
            accel[num] = sf_for(('accelerator', num), kind='accelerator', name=f'csr {num}',
                                short=f'csr {num}', file=None, decl_line=None, group='accelerator')
        s, file, line = attrib(pc)
        edges[(s, accel[num])].add((file, line, 'accelerator', pc, num))
        loc(accel[num], where[pc][0])['blocks'].add(where[pc][1])

    # Line ranges: declaration line to the last line of its own code or of its call sites.
    for (a, b), sites in edges.items():
        for file, line, kind, addr, extra in sites:
            if line is not None and file == sfs[a]['file']:
                sfs[a]['lines'].append(line)
    for s in sfs:
        ls = s.pop('lines') + ([s['decl_line']] if s['decl_line'] else [])
        s['lo'], s['hi'] = (min(ls), max(ls)) if ls else (None, None)

    # Derived state: the worst over the binary functions it lives in.
    for s in sfs:
        locs = [by_id[fid] for fid in s['loc']]
        s['derived'] = {
            'proof': worst([f['state'] for f in locs], PROOF_ORDER),
            'meaning': worst([f.get('meaning', 'none') for f in locs], MEANING_ORDER),
            'contract': worst([contract_value(f) for f in locs], CONTRACT_ORDER),
            'trust': worst([trust_value(f) for f in locs], TRUST_ORDER),
        }

    # Files: every file the debug information names for a source function or a code line.
    code_lines = defaultdict(set)
    for pc in pcs:
        ln = line_at(pc)
        if ln:
            code_lines[ln[0]].add(ln[1])
    paths = sorted({s['file'] for s in sfs if s['file']} | set(code_lines))
    file_index = {p: i for i, p in enumerate(paths)}
    files = [{'n': i, 'path': p, 'short': short_path(p), 'group': group_of(p),
              'code_lines': sorted(code_lines.get(p, ())),
              'functions': sorted([s['id'], s['lo'], s['hi']] for s in sfs if s['file'] == p and s['lo'])}
             for i, p in enumerate(paths)]

    out_fns = []
    for s in sfs:
        out_fns.append({
            'id': s['id'], 'kind': s['kind'], 'name': s['name'], 'short': s['short'],
            'group': s['group'], 'file': file_index.get(s['file']), 'decl_line': s['decl_line'],
            'lo': s['lo'], 'hi': s['hi'], 'instances': sorted(s['instances']),
            'locations': sorted(({'fn': L['fn'], 'instr': L['instr'], 'out_of_line': L['out_of_line'],
                                  'blocks': sorted(L['blocks'])} for L in s['loc'].values()),
                                key=lambda L: (not L['out_of_line'], -L['instr'], L['fn'])),
            'derived': s['derived'],
        })
    out_edges = []
    for (a, b), sites in sorted(edges.items()):
        out_edges.append({'from': a, 'to': b,
                          'sites': sorted(([file_index.get(f) if f else None, line, kind, addr, extra]
                                           for f, line, kind, addr, extra in sites),
                                          key=lambda s: (s[1] is None, s[1] or 0, s[3]))})
    inlined = [s for e in out_edges for s in e['sites']
               if s[2] == 'inlined' and not (s[4] or '').startswith('no line')]
    stats = {
        'instructions': len(pcs), 'source_functions': sum(s['kind'] == 'source' for s in sfs),
        'by_group': dict(Counter(s['group'] for s in sfs)), 'edges': len(out_edges),
        'sites': sum(len(e['sites']) for e in out_edges),
        'inlined_sites': len(inlined),
        'inlined_sites_without_line': sum(1 for s in inlined if s[1] is None),
        'no_line_edges': len(no_line), 'instructions_without_line': no_line_with_frame,
    }
    return {'functions': out_fns, 'edges': out_edges, 'files': files, 'stats': stats,
            'pc_owner': owner}


def load(elf, debug_object, m, insns):
    """Read the debug object (relocated to the ELF, as hints.py does) and build the source data."""
    from elftools.elf.elffile import ELFFile
    from dwarf import code_dwarf, inline_frames, line_rows  # vendor/dwarf.py
    with open(debug_object, 'rb') as fo, open(elf, 'rb') as fe:
        dwarf, _ = code_dwarf(ELFFile(fo), ELFFile(fe))
        frames = inline_frames(dwarf)
        rows = line_rows(dwarf)
    return build(m, insns, frames, rows)
