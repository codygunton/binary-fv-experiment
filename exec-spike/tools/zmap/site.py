"""`zmap site`: the graph viewer (plan S9) and its data.

Writes, under --out (P/map/site):
  index.html        the viewer (W/tools/binary-regions-ui/graph.html)
  vendor/d3.min.js
  data/index.js     window.ZMAP_INDEX: function summaries, call graph, program layout, queue,
                    metrics and history when present. Under 1 MB.
  data/fn/<id>.js   ZMAP_FN(<id>, {...}): blocks with disassembly and source lines, edges, cuts,
                    loops, joins, calls, leaves, the function layout and the function card.
Fields that S10 adds to map.json (rests_on, meaning, classes, cost, forecast, census,
meaning_link) are copied when present. Before S10, `meaning` comes from reviews.json (`meaning`,
else 'none'), and `rests_on` and `classes` are derived here by the S10.5/S10.6 rules; the index
lists such fields under `derived`.
"""
import json
import os
import shutil
from collections import Counter, defaultdict

from . import elfread, layout, workqueue
from .analyze import CSR, FORMS, csr_number

ZIG_SRC = '/home/cody/zesislar/_build/p0c-zesu-source/src/'
SRC_MARK = '/p0c-zesu-source/src/'
STD_MARK = '/lib/zig/std/'
SRC_LINES_CAP = 40
CLOSED = ('closed+compliance', 'closed+sail', 'closed')


def short_file(path):
    if not path:
        return None
    if SRC_MARK in path:
        return path.split(SRC_MARK, 1)[1]
    if STD_MARK in path:
        return 'std/' + path.split(STD_MARK, 1)[1]
    return path


def local_file(path):
    if SRC_MARK in path:
        return ZIG_SRC + path.split(SRC_MARK, 1)[1]
    return path


class Sources:
    def __init__(self):
        self.cache = {}

    def lines(self, path):
        if path not in self.cache:
            try:
                with open(local_file(path), errors='replace') as f:
                    self.cache[path] = f.read().split('\n')
            except OSError:
                self.cache[path] = None
        return self.cache[path]


def size_band(n):
    return 'size:<=150' if n <= 150 else 'size:151-600' if n <= 600 else 'size:601-3000' \
        if n <= 3000 else 'size:>3000'


def loop_band(n):
    return 'loops:0' if n == 0 else 'loops:1-3' if n <= 3 else 'loops:>3'


def unsupported(f):
    forms, csr = {}, {}
    for b in f['blockers']:
        if b['kind'] == 'unsupported-form':
            for k, v in b['detail'].items():
                if ':' in k:
                    num = k.split(':', 1)[1]
                    csr[num] = csr.get(num, 0) + v
                else:
                    forms[k] = v
    ecall = sum(len(b['detail']) for b in f['blockers'] if b['kind'] == 'ecall')
    return forms, csr, ecall


def loop_depths(f):
    bodies = {l['head']: set(l['body']) for l in f['loops']}
    return {h: 1 + sum(1 for g in bodies if g != h and h in bodies[g] and bodies[h] <= bodies[g])
            for h in bodies}


def summaries(m, reviews):
    """Per-function summary rows of index.js for the target set, plus the list of derived fields."""
    fns = m['functions']
    by_id = {f['id']: f for f in fns}
    target = [f for f in fns if f['set'] == 'target']
    meaning_rev = reviews.get('meaning', {})
    trust_ids = {f['id'] for f in fns if f.get('assumed') or f.get('service')}
    stems = Counter(layout.stem(f['name']) for f in target)
    derived = set()

    memo = {}

    def closure(fid):
        if fid in memo:
            return memo[fid]
        seen, stack = set(), [fid]
        while stack:
            for c in by_id[stack.pop()]['callees']:
                if c not in seen and c in by_id:
                    seen.add(c)
                    stack.append(c)
        memo[fid] = seen
        return seen

    rows = []
    for f in target:
        forms, csr, ecall = unsupported(f)
        ind = [c for c in f['calls'] if c['kind'] == 'indirect']
        depths = loop_depths(f)
        entry_block = next((b for b in f['blocks'] if b['start'] == f['entry']), None)
        src = (entry_block or {}).get('src') or {}
        st = layout.stem(f['name'])
        if 'meaning' in f:
            meaning = f['meaning']
        else:
            meaning = meaning_rev.get(f['id'], 'none')
            derived.add('meaning')
        if 'rests_on' in f:
            rests_on = f['rests_on']
        else:
            rests_on = sorted(c for c in closure(f['id']) if c in trust_ids and c != f['id'])
            derived.add('rests_on')
        if 'classes' in f:
            classes = f['classes']
        else:
            classes = [size_band(f['n_instr']), loop_band(len(f['loops']))]
            classes += [k for k, on in (('recursive', f['recursive']),
                                        ('irreducible', f['irreducible']),
                                        ('jump-table', bool(f['jump_tables'])),
                                        ('indirect-call', bool(ind)),
                                        ('accelerator', bool(csr)),
                                        ('ecall', bool(ecall)),
                                        ('generic-copy', stems[st] > 1)) if on]
            derived.add('classes')
        lv = f['leaves']
        n_leaves = sum(lv.values())
        led = (f.get('ledger') or {}).get('all') or {}     # schema-1 ledger: hand-typed minutes
        rows.append({
            'id': f['id'], 'name': f['name'], 'entry': f['entry'], 'n_instr': f['n_instr'],
            'n_cuts': len(f['cuts']), 'n_loops': len(f['loops']),
            'max_loop_depth': max(depths.values(), default=0),
            'n_joins': len(f['joins']),
            'max_fanin': max((j['fanin_paths'] for j in f['joins']), default=0),
            'n_tables': len(f['jump_tables']), 'n_indirect': len(ind),
            'indirect_resolution': dict(Counter(c['resolution'] for c in ind)),
            'n_calls': len(f['calls']),
            'recursive': f['recursive'], 'irreducible': f['irreducible'],
            'noreturn': f.get('noreturn', False),
            'forms_unsupported': forms, 'csr': csr, 'ecall': ecall,
            'blockers': sorted(set(workqueue.blocker_keys(f))),
            'src_file': short_file(src.get('file')), 'stem': st,
            'state': f['state'], 'leaves': lv, 'cut_lemmas': f.get('cut_lemmas'),
            'open_items': f['open_items'], 'contract': f.get('contract'),
            'assumed': f.get('assumed', False), 'service': f.get('service', False),
            'status_id': f.get('status_id'), 'theorems': f.get('theorems'),
            'theorem_names': f.get('theorem_names'),
            'rests_on': rests_on, 'meaning': meaning, 'classes': classes,
            'cost': (f.get('cost') or {}).get('all'), 'forecast': f.get('forecast'),
            'auto_share': f.get('auto_share', round(lv['auto'] / n_leaves, 3) if n_leaves else None),
            'census': f.get('census'),
            'minutes_typed': led.get('minutes') or 0, 'ledger_items': led.get('items') or 0,
            'waiting_on': f.get('waiting_on', []),
        })
    return rows, sorted(derived)


def call_edges(m):
    """Program-level edges between target functions, merged per (caller, callee)."""
    fns = m['functions']
    by_id = {f['id']: f for f in fns}
    agg = {}
    for f in fns:
        if f['set'] != 'target':
            continue
        for c in f['calls']:
            for t in c['targets']:
                if t not in by_id or by_id[t]['set'] != 'target':
                    continue
                e = agg.setdefault((f['id'], t), {'from': f['id'], 'to': t, 'sites': 0,
                                                  'kinds': {'direct': 0, 'tail': 0, 'indirect': 0},
                                                  'res': Counter()})
                e['sites'] += 1
                e['kinds'][c['kind']] = e['kinds'].get(c['kind'], 0) + 1
                if c['kind'] == 'indirect':
                    e['res'][c['resolution']] += 1
    out = []
    for (a, b), e in sorted(agg.items()):
        res = e.pop('res')
        e['resolution'] = res.most_common(1)[0][0] if res else 'direct'
        e['noreturn'] = bool(by_id[b].get('noreturn'))
        # S10.2: map.json functions may carry meaning_links {callee id: bool}.
        e['meaning_link'] = (by_id[a].get('meaning_links') or {}).get(b)
        out.append(e)
    return out


def fn_data(m, f, by_id, insns, sources):
    names = {g['id']: g['name'] for g in m['functions']}
    lay = layout.function(f, names)
    blocks = []
    src_out = defaultdict(dict)
    for b in f['blocks']:
        dis, glyphs = [], []
        if insns is not None:
            pc = b['start']
            while pc < b['end']:
                i = insns.get(pc)
                if i is None:
                    dis.append([pc, '?'])
                    pc += 2
                    continue
                dis.append([pc, f'{i.mn} {", ".join(i.ops)}'.strip()])
                if i.mn == 'ecall':
                    glyphs.append('ecall')
                elif i.mn in CSR:
                    glyphs.append('csr ' + csr_number(i))
                elif i.size == 4 and i.mn not in FORMS:
                    glyphs.append(i.mn)
                pc = i.next
        src = b.get('src') or {}
        if src.get('file') and src.get('lines'):
            text = sources.lines(src['file'])
            lo, hi = src['lines']
            if text is not None:
                key = short_file(src['file'])
                for ln in range(lo, min(hi, lo + SRC_LINES_CAP - 1) + 1):
                    if 1 <= ln <= len(text):
                        src_out[key][ln] = text[ln - 1]
        blocks.append({'start': b['start'], 'end': b['end'], 'n': b['n'], 'kind': b['kind'],
                       'succ': b['succ'], 'gx': b['x'], 'gy': b['y'],
                       'src': {'file': short_file(src.get('file')), 'lines': src.get('lines'),
                               'inline': src.get('inline')} if src else None,
                       'dis': dis, 'glyphs': dict(Counter(glyphs))})
    return {
        'id': f['id'], 'name': f['name'], 'entry': f['entry'], 'n_instr': f['n_instr'],
        'blocks': blocks, 'edges': f['edges'], 'cuts': f['cuts'], 'loops': f['loops'],
        'joins': f['joins'], 'calls': f['calls'], 'jump_tables': f['jump_tables'],
        'callers': f['callers'], 'callees': f['callees'],
        'vc_cuts': [{'pc': c['pc'], 'cut_lemma': c.get('cut_lemma', 'open'),
                     'residual': c.get('residual'), 'n_leaves': len(c['leaves']),
                     'thm': c.get('thm')}
                    for c in f.get('vc_cuts') or []],
        'source': {k: v for k, v in src_out.items()},
        'card': workqueue.card(m, f),
        'layout': lay,
        'disassembly': insns is not None,
    }


def read_jsonl(path):
    if not path or not os.path.exists(path):
        return None
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


def write_js(path, prefix, obj, suffix=';\n'):
    with open(path, 'w') as f:
        f.write(prefix)
        json.dump(obj, f, separators=(',', ':'))
        f.write(suffix)


def build(m, queue, reviews, out, ui, insns=None, metrics=None, history=None):
    """Write the site. Returns {'index_bytes', 'functions'}."""
    fns = m['functions']
    by_id = {f['id']: f for f in fns}
    rows, derived = summaries(m, reviews)
    edges = call_edges(m)
    root = next((f['id'] for f in fns if f['name'] == '_start'), rows[0]['id'] if rows else None)
    prog = layout.program(
        [{'id': r['id'], 'name': r['name'], 'src_file': r['src_file'],
          'size': {'cuts': r['n_cuts'], 'instr': r['n_instr'],
                   'forecast': (r['forecast'] or {}).get('p50') if isinstance(r['forecast'], dict)
                   else r['forecast']}} for r in rows],
        [(e['from'], e['to']) for e in edges], root)
    index = {
        'schema': 'zmap.site.v1', 'elf_sha256': m.get('elf_sha256'),
        'status_source': m.get('status_source'), 'root': root,
        'functions': rows, 'edges': edges, 'layout': prog,
        'queue': queue, 'trust': m.get('trust', []), 'state_counts': m.get('state_counts'),
        'ledger_totals': m.get('ledger_totals'), 'cost_totals': m.get('cost_totals'),
        'metrics': metrics, 'history': history,
        'derived': derived, 'disassembly': insns is not None,
    }
    data = os.path.join(out, 'data')
    fn_dir = os.path.join(data, 'fn')
    if os.path.isdir(fn_dir):
        shutil.rmtree(fn_dir)
    os.makedirs(fn_dir)
    os.makedirs(os.path.join(out, 'vendor'), exist_ok=True)
    for stale in ('map.html', 'map-data.js'):
        p = os.path.join(out, stale)
        if os.path.exists(p):
            os.remove(p)
    shutil.copy(os.path.join(ui, 'graph.html'), os.path.join(out, 'index.html'))
    shutil.copy(os.path.join(ui, 'vendor', 'd3.min.js'), os.path.join(out, 'vendor', 'd3.min.js'))
    write_js(os.path.join(data, 'index.js'), 'window.ZMAP_INDEX = ', index)
    sources = Sources()
    for r in rows:
        f = by_id[r['id']]
        write_js(os.path.join(fn_dir, f'{f["id"]}.js'), f'ZMAP_FN({json.dumps(f["id"])}, ',
                 fn_data(m, f, by_id, insns, sources), ');\n')
    return {'index_bytes': os.path.getsize(os.path.join(data, 'index.js')), 'functions': len(rows)}


def cmd(args):
    with open(args.map) as f:
        m = json.load(f)
    queue = []
    if os.path.exists(args.queue):
        with open(args.queue) as f:
            queue = json.load(f)
    reviews = {}
    if args.reviews and os.path.exists(args.reviews):
        with open(args.reviews) as f:
            reviews = json.load(f)
    metrics = None
    if args.metrics and os.path.exists(args.metrics):
        with open(args.metrics) as f:
            metrics = json.load(f)
    insns = elfread.disassemble(args.elf) if args.elf and os.path.exists(args.elf) else None
    r = build(m, queue, reviews, args.out, args.ui, insns=insns, metrics=metrics,
              history=read_jsonl(args.history))
    print(f'zmap: site -> {os.path.join(args.out, "index.html")} ({r["functions"]} functions, '
          f'index.js {r["index_bytes"]} bytes, disassembly {"yes" if insns else "no"})')


def register(sub, package, ui):
    mp = os.path.join(package, 'map')
    st = sub.add_parser('site', help='write the graph viewer (index.html, data/index.js, data/fn/)')
    st.add_argument('--map', default=os.path.join(mp, 'map.json'))
    st.add_argument('--queue', default=os.path.join(mp, 'queue.json'))
    st.add_argument('--reviews', default=os.path.join(mp, 'reviews.json'))
    st.add_argument('--metrics', default=os.path.join(mp, 'metrics.json'))
    st.add_argument('--history', default=os.path.join(mp, 'history.jsonl'))
    st.add_argument('--elf', help='ELF for the block disassembly (omitted: no disassembly)')
    st.add_argument('--ui', default=ui, help='directory with graph.html and vendor/d3.min.js')
    st.add_argument('--out', required=True)
    st.set_defaults(func=cmd)
