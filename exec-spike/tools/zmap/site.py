"""`zmap site`: the graph viewer (plan S9) and its data.

Writes, under --out (P/map/site):
  index.html        the viewer (W/tools/binary-regions-ui/graph.html)
  vendor/           d3.min.js, pixi.min.js (WebGL renderer, S9.3), README.md
  data/index.js     window.ZMAP_INDEX: function summaries, call graph, program layout, queue,
                    metrics and history when present. Under 1 MB.
  data/fn/<id>.js   ZMAP_FN(<id>, {...}): what the renderer draws, numbers in flat arrays: blocks,
                    edges, cuts, loops, joins, calls, leaves, the function layout. Under 1 MB.
  data/fn/<id>.detail.js  ZMAP_FN_DETAIL(<id>, {...}): disassembly, source lines, the card, and
                    `vars` (S23: variables in scope at each block's start, from map/varloc);
                    loaded when a block or the card is first opened.
Fields that S10 adds to map.json (rests_on, meaning, classes, cost, forecast, census,
meaning_link) are copied when present. Before S10, `meaning` comes from reviews.json (`meaning`,
else 'none'), and `rests_on` and `classes` are derived here by the S10.5/S10.6 rules; the index
lists such fields under `derived`.
"""
import json
import os
import shutil
from collections import Counter, defaultdict

from . import elfread, layout, source, varloc, workqueue
from .analyze import CSR, FORMS, csr_number

ZIG_SRC = '/home/cody/zesislar/_build/p0c-zesu-source/src/'
SRC_MARK = '/p0c-zesu-source/src/'
STD_MARK = '/lib/zig/std/'
SRC_LINES_CAP = 40
VENDOR = ('d3.min.js', 'pixi.min.js', 'README.md')


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


BLOCK_KINDS = ('plain', 'join', 'loop_head')
EXITS = (None, 'call', 'tail', 'table', 'ret')
EDGE_KINDS = ('fall', 'taken', 'jump', 'back', 'table')
CUT_WHY = ('entry', 'loop', 'ret', 'join', 'cycle')
CALL_KINDS = ('direct', 'indirect', 'tail')


def flat(pts):
    """[[x, y], ...] -> [x, y, ...] in whole pixels."""
    return [round(v) for p in pts for v in p]


def fn_data(m, f, insns, sources, names):
    """(main, detail) of one function: data/fn/<id>.js and data/fn/<id>.detail.js.

    main holds what the renderer draws, with numbers in flat arrays (blocks and cuts as columns,
    routes as [x, y, x, y, ...]); detail holds disassembly, source lines and the card.
    """
    lay = layout.function(f, names)
    index = {b['start']: i for i, b in enumerate(f['blocks'])}
    files, inlines = [], []

    def intern(table, s):
        if s is None:
            return -1
        if s not in table:
            table.append(s)
        return table.index(s)

    cols = {k: [] for k in ('start', 'end', 'n', 'kind', 'x', 'y', 'exit', 'file', 'lo', 'hi', 'inl')}
    glyph_rows, dis_rows = {}, []
    src_out = defaultdict(dict)
    for i, (b, lb) in enumerate(zip(f['blocks'], lay['blocks'])):
        dis, glyphs = [], []
        if insns is not None:
            pc = b['start']
            while pc < b['end']:
                ins = insns.get(pc)
                if ins is None:
                    dis.append([pc, '?'])
                    pc += 2
                    continue
                dis.append([pc, f'{ins.mn} {", ".join(ins.ops)}'.strip()])
                if ins.mn == 'ecall':
                    glyphs.append('ecall')
                elif ins.mn in CSR:
                    glyphs.append('csr ' + csr_number(ins))
                elif ins.size == 4 and ins.mn not in FORMS:
                    glyphs.append(ins.mn)
                pc = ins.next
        dis_rows.append(dis)
        if glyphs:
            glyph_rows[i] = dict(Counter(glyphs))
        src = b.get('src') or {}
        lines = src.get('lines') or [0, 0]
        if src.get('file') and src.get('lines'):
            text = sources.lines(src['file'])
            if text is not None:
                key = short_file(src['file'])
                for ln in range(lines[0], min(lines[1], lines[0] + SRC_LINES_CAP - 1) + 1):
                    if 1 <= ln <= len(text):
                        src_out[key][ln] = text[ln - 1]
        for k, v in (('start', b['start']), ('end', b['end']), ('n', b['n']),
                     ('kind', BLOCK_KINDS.index(b['kind'])), ('x', round(lb['x'])),
                     ('y', round(lb['y'])), ('exit', EXITS.index(lb['exit'])),
                     ('file', intern(files, short_file(src.get('file')))), ('lo', lines[0]),
                     ('hi', lines[1]), ('inl', intern(inlines, src.get('inline')))):
            cols[k].append(v)
    stubs = {s['key']: i for i, s in enumerate(lay['callee_stubs'])}
    main = {
        'id': f['id'], 'name': f['name'], 'entry': f['entry'], 'n_instr': f['n_instr'],
        'disassembly': insns is not None, 'files': files, 'inlines': inlines,
        'block_w': lay['blocks'][0]['w'] if lay['blocks'] else 0,
        'block_h': lay['blocks'][0]['h'] if lay['blocks'] else 0,
        'blocks': cols, 'glyphs': glyph_rows,
        'edges': {'from': [index[e['from']] for e in lay['edges']],
                  'to': [index[e['to']] for e in lay['edges']],
                  'kind': [EDGE_KINDS.index(e['kind']) for e in lay['edges']],
                  'pts': [flat(e['pts']) for e in lay['edges']]},
        'cuts': {'pc': [c['pc'] for c in f['cuts']], 'why': [CUT_WHY.index(c['why']) for c in f['cuts']]},
        'loops': {'head': [l['head'] for l in f['loops']], 'n': [len(l['body']) for l in f['loops']]},
        'joins': {'at': [j['at'] for j in f['joins']], 'fanin': [j['fanin_paths'] for j in f['joins']]},
        'tables': {'site': [t['site'] for t in f['jump_tables']],
                   'entries': [t.get('entries') or len(t['targets']) for t in f['jump_tables']]},
        'calls': {'n': [c['n'] for c in lay['calls']], 'site': [c['site'] for c in lay['calls']],
                  'ret': [c['ret'] for c in lay['calls']],
                  'block': [index[c['block']] for c in lay['calls']],
                  'kind': [CALL_KINDS.index(c['kind']) for c in lay['calls']],
                  'resolution': [c['resolution'] for c in lay['calls']],
                  'stub': [stubs[c['stub']] for c in lay['calls']],
                  'noreturn': [int(c['noreturn']) for c in lay['calls']],
                  'no_return_site': [int(c['no_return_site']) for c in lay['calls']],
                  'call': [flat(c['call']) for c in lay['calls']],
                  'return': [flat(c['return']) if c['return'] else None for c in lay['calls']]},
        'callee_stubs': [{'key': s['key'], 'label': s['label'], 'targets': s['targets'],
                          'x': round(s['x']), 'y': round(s['y'])} for s in lay['callee_stubs']],
        'caller_stubs': [{'key': s['key'], 'label': s['label'], 'x': round(s['x']), 'y': round(s['y'])}
                         for s in lay['caller_stubs']],
        'stub_w': layout.STUB_W, 'stub_h': layout.STUB_H,
        'hulls': {'depth': [h['depth'] for h in lay['hulls']], 'pts': [flat(h['pts']) for h in lay['hulls']]},
        'irr': {'pts': [flat(r['pts']) for r in lay['irr']],
                'entries': [[index[s] for s in r['entries']] for r in lay['irr']]},
        'drains': [flat(d['pts']) for d in lay['drains']],
        'exit_bar': {'x0': round(lay['exit_bar']['x0']), 'x1': round(lay['exit_bar']['x1']),
                     'y': round(lay['exit_bar']['y']),
                     'link': flat(lay['exit_bar']['link']) if lay['exit_bar']['link'] else None},
        'vc_cuts': [{'pc': c['pc'], 'cut_lemma': c.get('cut_lemma', 'open'),
                     'residual': c.get('residual'), 'n_leaves': len(c['leaves']),
                     'thm': c.get('thm')}
                    for c in f.get('vc_cuts') or []],
        'leaf_paths': {str(pc): dict(lp, leaves=[dict(l, blocks=[index[s] for s in l['blocks']])
                                                 for l in lp['leaves']])
                       for pc, lp in lay['leaf_paths'].items()},
        'bounds': [round(v) for v in lay['bounds']],
    }
    detail = {'dis': dis_rows, 'source': dict(src_out), 'card': workqueue.card(m, f)}
    return main, detail


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


SITE_KINDS = ('inlined', 'call', 'tail', 'indirect', 'accelerator')


def write_src(data, src, m):
    """data/src/index.js (source functions, edges, groups, files) and data/src/file/<n>.js.

    Locations are [binary function id, exclusive instructions, out of line 0/1, block indices];
    sites are [file index, line, kind index in SITE_KINDS, address, extra]; `in`/`out` are the
    offline display order of the depth-one neighbourhood (layout.neighbourhood).
    """
    src_dir = os.path.join(data, 'src')
    if os.path.isdir(src_dir):
        shutil.rmtree(src_dir)
    os.makedirs(os.path.join(src_dir, 'file'))
    order = layout.neighbourhood(src['functions'], src['edges'])
    fns = []
    for f, nb in zip(src['functions'], order):
        fns.append({k: f[k] for k in ('id', 'kind', 'name', 'short', 'group', 'file', 'decl_line',
                                      'lo', 'hi', 'instances', 'derived')}
                   | {'loc': [[L['fn'], L['instr'], int(L['out_of_line']), L['blocks']]
                              for L in f['locations']], 'in': nb['in'], 'out': nb['out']})
    # Landing function: the Zesu program's entry, the first function reached from `_start`
    # (breadth first over binary callees: _start -> _zisk_main -> main) whose out-of-line source
    # function is in the Zesu tree.
    by_id = {f['id']: f for f in m['functions']}
    out_of_line = {L['fn']: f for f in src['functions'] for L in f['locations']
                   if L['out_of_line'] and f['kind'] == 'source'}
    start = next((f['id'] for f in m['functions'] if f['name'] == '_start'), None)
    default, seen, queue = None, {start}, [start] if start else []
    while queue and default is None:
        fid = queue.pop(0)
        sf = out_of_line.get(fid)
        if sf is not None and sf['group'] == 'zesu':
            default = sf
            break
        for c in by_id[fid]['callees']:
            if c not in seen:
                seen.add(c)
                queue.append(c)
    if default is None:
        zesu = [f for f in src['functions'] if f['group'] == 'zesu' and f['kind'] == 'source']
        default = max(zesu, key=lambda f: sum(L['instr'] for L in f['locations']), default=None)
    files = []
    missing = []
    for fl in src['files']:
        path = local_file(fl['path'])
        try:
            with open(path, errors='replace') as fh:
                text = fh.read()
        except OSError:
            text = None
            missing.append(fl['short'])
        files.append({k: fl[k] for k in ('n', 'short', 'group')} | {'missing': text is None,
                                                                     'n_functions': len(fl['functions'])})
        write_js(os.path.join(src_dir, 'file', f'{fl["n"]}.js'), f'ZMAP_SRC_FILE({fl["n"]}, ',
                 {'n': fl['n'], 'short': fl['short'], 'path': fl['path'], 'text': text,
                  'functions': fl['functions'], 'code_lines': fl['code_lines']}, ');\n')
    index = {'schema': 'zmap.src.v1', 'functions': fns,
             'edges': [{'from': e['from'], 'to': e['to'],
                        'sites': [[s[0], s[1], SITE_KINDS.index(s[2]), s[3], s[4]] for s in e['sites']]}
                       for e in src['edges']],
             'site_kinds': SITE_KINDS, 'groups': list(source.GROUPS), 'files': files,
             'default': default['id'] if default else None, 'stats': src['stats'] | {'missing_files': missing}}
    write_js(os.path.join(src_dir, 'index.js'), 'window.ZMAP_SRC = ', index)
    return {'src_bytes': os.path.getsize(os.path.join(src_dir, 'index.js')), 'missing': missing,
            'stats': src['stats']}


def build(m, queue, reviews, out, ui, insns=None, metrics=None, history=None, src=None,
          varloc_dir=None):
    """Write the site. Returns {'index_bytes', 'functions', 'src'}."""
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
    for v in VENDOR:
        shutil.copy(os.path.join(ui, 'vendor', v), os.path.join(out, 'vendor', v))
    write_js(os.path.join(data, 'index.js'), 'window.ZMAP_INDEX = ', index)
    sources = Sources()
    names = {g['id']: g['name'] for g in fns}
    for r in rows:
        f = by_id[r['id']]
        main, detail = fn_data(m, f, insns, sources, names)
        vt = varloc.load_file(varloc_dir, f['id']) if varloc_dir else None
        detail['vars'] = varloc.block_rows(vt, [b['start'] for b in f['blocks']]) if vt else None
        write_js(os.path.join(fn_dir, f'{f["id"]}.js'), f'ZMAP_FN({json.dumps(f["id"])}, ', main, ');\n')
        write_js(os.path.join(fn_dir, f'{f["id"]}.detail.js'), f'ZMAP_FN_DETAIL({json.dumps(f["id"])}, ',
                 detail, ');\n')
    if src is not None:
        src_info = write_src(data, src, m)
    else:
        src_info = None
        shutil.rmtree(os.path.join(data, 'src'), ignore_errors=True)
    return {'index_bytes': os.path.getsize(os.path.join(data, 'index.js')), 'functions': len(rows),
            'src': src_info}


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
    src = None
    if insns is not None and args.debug_object and os.path.exists(args.debug_object):
        src = source.load(args.elf, args.debug_object, m, insns)
    r = build(m, queue, reviews, args.out, args.ui, insns=insns, metrics=metrics,
              history=read_jsonl(args.history), src=src, varloc_dir=args.varloc)
    s = r['src']
    print(f'zmap: site -> {os.path.join(args.out, "index.html")} ({r["functions"]} functions, '
          f'index.js {r["index_bytes"]} bytes, disassembly {"yes" if insns else "no"}, source view '
          + (f'{s["stats"]["source_functions"]} source functions, src/index.js {s["src_bytes"]} bytes, '
             f'inlined sites without line {s["stats"]["inlined_sites_without_line"]}/'
             f'{s["stats"]["inlined_sites"]}, missing files {s["missing"] or "none"})' if s else 'no)'))


def register(sub, package, ui):
    mp = os.path.join(package, 'map')
    st = sub.add_parser('site', help='write the graph viewer (index.html, data/index.js, data/fn/)')
    st.add_argument('--map', default=os.path.join(mp, 'map.json'))
    st.add_argument('--queue', default=os.path.join(mp, 'queue.json'))
    st.add_argument('--reviews', default=os.path.join(mp, 'reviews.json'))
    st.add_argument('--metrics', default=os.path.join(mp, 'metrics.json'))
    st.add_argument('--history', default=os.path.join(mp, 'history.jsonl'))
    st.add_argument('--elf', help='ELF for the block disassembly (omitted: no disassembly)')
    st.add_argument('--debug-object', help='pre-link debug object for the source view (needs --elf)')
    st.add_argument('--varloc', default=os.path.join(mp, 'varloc'),
                    help='directory of map/varloc/<id>.json (S23); missing tables: no variable list')
    st.add_argument('--ui', default=ui, help='directory with graph.html and vendor/d3.min.js')
    st.add_argument('--out', required=True)
    st.set_defaults(func=cmd)
