"""Metrics, history, forecast, agent brief and the check (programme plan S10.4, S10.7).

`compute(map, items, per_agent, build)` returns `metrics.json`: one object per group of plan
S10.4 (`coverage`, `trust`, `contracts`, `meaning`, `automation`, `effort`, `build`,
`map_precision`, `census`, `fragility`, `forecast`), each a dict of named values and tables
(`{"columns": [...], "rows": [[...]]}`). It also sets each function's `forecast` in the map.
Groups without data say so in `note`.

`append_history` adds one line per commit to `history.jsonl` (the line of the same commit is
replaced): the coverage headline and every target function's state and meaning level.
"""
import datetime
import glob
import json
import os
import re
import statistics
import subprocess
from collections import Counter, defaultdict

from .merge import CLASSES, CLOSED, MEANING, PROVED, STATES

UNITS = ('functions', 'instructions', 'cut_points', 'loops', 'call_sites')
BUCKETS = ('closed', 'closed-on-assumptions', 'conditional', 'open')
GROUPS = ('coverage', 'trust', 'contracts', 'meaning', 'automation', 'effort', 'build',
          'map_precision', 'census', 'fragility', 'forecast')
ADDR = re.compile(r'0x800[0-9a-fA-F]{2,}')
PCTS = (25, 50, 75)


def table(columns, rows):
    return {'columns': list(columns), 'rows': [list(r) for r in rows]}


def bucket(f):
    s = f['state']
    if s in CLOSED:
        return 'closed'
    if s in ('closed-on-assumptions', 'conditional'):
        return s
    return 'open'


def units(f):
    return {'functions': 1, 'instructions': f['n_instr'], 'cut_points': len(f['cuts']),
            'loops': len(f['loops']), 'call_sites': len(f['calls'])}


def pct(vals, p):
    """Linear-interpolated percentile of a non-empty list."""
    v = sorted(vals)
    if len(v) == 1:
        return v[0]
    k = (len(v) - 1) * p / 100
    lo = int(k)
    hi = min(lo + 1, len(v) - 1)
    return v[lo] + (v[hi] - v[lo]) * (k - lo)


def _lines(path):
    try:
        with open(path) as f:
            return sum(1 for _ in f)
    except OSError:
        return 0


def _r(x, n=4):
    return round(x, n) if isinstance(x, float) else x


# ---------------------------------------------------------------------------------- groups

def coverage(target):
    tot = {u: Counter() for u in UNITS}
    for f in target:
        for u, n in units(f).items():
            tot[u][bucket(f)] += n
    rows = [[u] + [tot[u][b] for b in BUCKETS] + [sum(tot[u].values())] for u in UNITS]
    per_class = []
    for c in CLASSES:
        cnt = Counter()
        for f in target:
            if c in f['classes']:
                cnt[bucket(f)] += len(f['cuts'])
        per_class.append([c] + [cnt[b] for b in BUCKETS] + [sum(cnt.values())])
    cp = tot['cut_points']
    return {'headline': {'cut_points_closed': cp['closed'],
                         'cut_points_closed_on_assumptions': cp['closed-on-assumptions'],
                         'cut_points_total': sum(cp.values())},
            'by_unit': table(('unit',) + BUCKETS + ('total',), rows),
            'cut_points_by_class': table(('class',) + BUCKETS + ('total',), per_class),
            'states': dict(Counter(f['state'] for f in target))}


def trust(m, target, reviews_csr, package_dir):
    by_id = {f['id']: f for f in m['functions']}
    assumed = [f for f in m['functions'] if f['assumed'] and not f['service']]
    csr_total = sorted({k.split(':', 1)[1] for f in target for b in f['blockers']
                        if b['kind'] == 'unsupported-form' for k in b['detail'] if ':' in k})
    defined = sorted(k for k in reviews_csr if reviews_csr[k].get('defined'))
    tested = sorted(k for k in reviews_csr if reviews_csr[k].get('emulator_tested'))
    zx = os.path.join(package_dir, 'ZesuExec')
    contracts = sum(_lines(p) for p in glob.glob(os.path.join(zx, 'Fn', '*', 'Spec.lean')))
    services = _lines(os.path.join(zx, 'Service.lean')) + sum(
        _lines(p) for p in glob.glob(os.path.join(zx, 'Service', '*.lean')))
    hunks = 0
    for p in glob.glob(os.path.join(package_dir, 'sail', '*.patch')):
        with open(p) as f:
            hunks += sum(1 for line in f if line.startswith('@@'))
    configured = 0
    rel = os.path.join(zx, 'Sail', 'Rel.lean')
    if os.path.exists(rel):
        with open(rel) as f:
            src = f.read().split('\n')
        for i, line in enumerate(src):
            if line.startswith('structure Configured'):
                j = i
                while j < len(src) and src[j].strip():
                    j += 1
                configured = j - i
    rev = Counter((f['contract'] or {}).get('review') for f in m['functions'] if f['contract'])
    rests = [[f['id'], f['name'], f['state'],
              ', '.join(by_id[r]['name'] for r in f['rests_on']) or '-']
             for f in m['functions'] if f['state'] in PROVED]
    return {'assumed_non_service': len(assumed),
            'assumed_non_service_fns': [f['id'] for f in assumed],
            'csr': {'defined': len(defined), 'emulator_tested': len(tested),
                    'total': len(csr_total), 'numbers': csr_total},
            'trusted_lines': {'contracts': contracts, 'service_definitions': services,
                              'sail_patch_hunks': hunks, 'configured': configured},
            'contracts_reviewed': rev.get('reviewed', 0),
            'contracts_unreviewed': rev.get('unreviewed', 0),
            'rests_on': table(('fn', 'name', 'state', 'rests on'), rests)}


def rework(fid, history):
    """Changes of a function's contract hashes after its first dependent proof (history)."""
    seen = None
    n = 0
    for h in history:
        e = (h.get('hashes') or {}).get(fid)
        if not e:
            continue
        key = (e.get('pre'), e.get('post'), e.get('cuts'), e.get('callees'))
        if seen is not None and key != seen:
            n += 1
        if seen is not None or e.get('dep'):
            seen = key
    return n


def contracts(m, history):
    rows = []
    for f in m['functions']:
        c = f['contract']
        if not c and not f['hashes']:
            continue
        rows.append([f['id'], f['name'], (c or {}).get('contract', '-'),
                     (c or {}).get('review', '-'), f['nonvacuity'] or '-', f['snapshot'] or '-',
                     rework(f['id'], history)])
    return {'contracts': table(('fn', 'name', 'contract', 'review', 'non-vacuity', 'snapshot',
                                'rework'), rows),
            'missing_nonvacuity': sum(1 for r in rows if r[4] == '-'),
            'missing_snapshot': sum(1 for r in rows if r[5] == '-')}


def meaning(m, target, package_dir):
    by_id = {f['id']: f for f in m['functions']}
    good = ('spec-sail', 'model')
    memo = {}

    def complete(fid, stack=()):
        if fid in memo:
            return memo[fid]
        f = by_id[fid]
        ok = f['meaning'] in good and all(
            complete(c, stack + (fid,)) for c in f['callees'] if c != fid and c not in stack)
        memo[fid] = ok
        return ok

    fn_cnt = Counter(f['meaning'] for f in target)
    cp_cnt = Counter()
    for f in target:
        cp_cnt[f['meaning']] += len(f['cuts'])
    comp = sum(len(f['cuts']) for f in target if complete(f['id']))
    rows = []
    cdir = os.path.join(package_dir, 'ZesuExec', 'Compliance')
    for f in m['functions']:
        if not f['status_id']:
            continue
        key = f['status_id'].split('.')[-1]
        files = [p for p in glob.glob(os.path.join(cdir, '*.lean'))
                 if os.path.basename(p).startswith(key)]
        rows.append([f['id'], f['name'], f['meaning'], sum(_lines(p) for p in files)])
    return {'functions': {k: fn_cnt.get(k, 0) for k in MEANING},
            'cut_points': {k: cp_cnt.get(k, 0) for k in MEANING},
            'meaning_complete_cut_points': comp,
            'compliance_lines': table(('fn', 'name', 'meaning', 'compliance lines'), rows)}


def residual_class(residual):
    from .costmodel import residual_class as rc
    return rc(residual)


def automation(m, pre_revision):
    st = Counter()
    by_class = defaultdict(Counter)
    rules = Counter()
    hand = []
    per_fn = []
    new_st = Counter()
    for f in m['functions']:
        if not f['vc_cuts']:
            continue
        for c in f['vc_cuts']:
            if (c.get('thm') or {}).get('rule', '').startswith('auto'):
                rules[c['thm']['rule']] += 1
            for lf in c['leaves']:
                s = lf.get('state', 'open')
                st[s] += 1
                if f['id'] not in pre_revision:
                    new_st[s] += 1
                k = 'auto' if s == 'auto' else residual_class(lf.get('residual'))
                by_class[k][s] += 1
                th = lf.get('thm') or {}
                if th.get('rule', '').startswith('auto'):
                    rules[th['rule']] += 1
                if s == 'manual' and th.get('lines'):
                    hand.append(th['lines'][1] - th['lines'][0] + 1)
        lv = f['leaves']
        per_fn.append([f['id'], f['name'], lv['auto'], lv['manual'], lv['open'], f['auto_share']])
    n = sum(st.values())
    nn = sum(new_st.values())
    return {'auto_share': _r(st['auto'] / n) if n else None,
            'leaves': dict(st),
            'auto_share_after_revision': _r(new_st['auto'] / nn) if nn else None,
            'leaves_after_revision': dict(new_st),
            'by_residual_class': table(('class', 'auto', 'manual', 'open'),
                                       [[k, v['auto'], v['manual'], v['open']]
                                        for k, v in sorted(by_class.items())]),
            'per_function': table(('fn', 'name', 'auto', 'manual', 'open', 'auto share'), per_fn),
            'rule_hits': dict(rules),
            'hand_lines_per_manual_leaf': _r(statistics.mean(hand), 2) if hand else None}


EFFORT_KEYS = ('usd', 'totalTokens', 'requests', 'minutes', 'builds')


def _sum(items):
    t = {k: 0.0 for k in EFFORT_KEYS}
    for i in items:
        c = i.get('cost') or {}
        for k in EFFORT_KEYS:
            t[k] += (i.get('minutes') or 0) if k == 'minutes' else (c.get(k) or 0)
    return {k: round(v, 2) for k, v in t.items()}


def effort(m, items, per_agent):
    by_kind = defaultdict(list)
    for i in items:
        by_kind[i.get('kind') or '-'].append(i)
    kinds = [[k, len(v)] + [_sum(v)[x] for x in EFFORT_KEYS] for k, v in sorted(by_kind.items())]
    fns = []
    for f in m['functions']:
        c = f['cost']['all']
        if not c['items']:
            continue
        cuts = len(f['cuts']) or 1
        fns.append([f['id'], f['name'], f['state'], c['items'], round(c['usd'], 2),
                    c['totalTokens'], c['requests'], c['minutes'], c['builds'],
                    round(c['usd'] / cuts, 2), round(c['usd'] / max(f['n_instr'], 1), 4)])
    total = _sum(items)
    infra = _sum(by_kind.get('infra', []))
    sess = sum(a['session']['usd'] for a in per_agent.values())
    un = sum(a['unattributed']['usd'] for a in per_agent.values())
    agents = [[a, round(v['session']['usd'], 2), round(v['items']['usd'], 2),
               round(v['unattributed']['usd'], 2), v['unattributed_share'], v['session']['unknown']]
              for a, v in sorted(per_agent.items(), key=lambda kv: -kv[1]['session']['usd'])]
    unknown = sum(a['session']['unknown'] for a in per_agent.values())
    reqs = sum(a['session']['requests'] for a in per_agent.values())
    return {'total': total, 'session_usd': round(sess, 2), 'unattributed_usd': round(un, 2),
            'unattributed_share': _r(un / sess) if sess else None,
            'unknown_cost_requests': unknown,
            'unknown_cost_share': _r(unknown / reqs) if reqs else None,
            'infrastructure_share': _r(infra['usd'] / total['usd']) if total['usd'] else None,
            'abandoned': _sum([i for i in items if i.get('outcome') == 'abandoned']),
            'by_kind': table(('kind', 'items') + EFFORT_KEYS, kinds),
            'by_function': table(('fn', 'name', 'state', 'items', 'usd', 'tokens', 'requests',
                                  'minutes', 'builds', 'usd/cut', 'usd/instr'), fns),
            'by_agent': table(('agent', 'session usd', 'in items usd', 'unattributed usd',
                               'unattributed share', 'unknown-cost requests'), agents)}


def build(m, b):
    if not b:
        return {'note': 'no data: run tools/buildstat.py after a full lake build'}
    mods = b.get('modules', [])
    cpu = sum(x.get('user_s') or 0 for x in mods)
    instr = sum(f['n_instr'] for f in m['functions'] if f['state'] in PROVED)
    return {'commit': b.get('commit'),
            'total': {'wall_s': round(sum(x.get('wall_s') or 0 for x in mods), 1),
                      'cpu_s': round(cpu, 1),
                      'peak_rss_mb_max': max((x.get('peak_rss_mb') or 0 for x in mods), default=0)},
            'cpu_s_per_proved_instruction': _r(cpu / instr) if instr else None,
            'modules': table(('module', 'wall s', 'cpu s', 'peak MB', 'ok'),
                             [[x['module'], x.get('wall_s'), x.get('user_s'), x.get('peak_rss_mb'),
                               x.get('ok')] for x in mods])}


def map_precision(m, target):
    by_id = {f['id']: f for f in m['functions']}
    res = Counter(c['resolution'] for f in target for c in f['calls'] if c['kind'] == 'indirect')
    unres = sum(len(b['detail']) if isinstance(b['detail'], list) else 1
                for f in target for b in f['blockers'] if b['kind'] == 'indirect-jump-unresolved')
    tables = sum(len(f['jump_tables']) for f in target)
    # recursion through direct calls only (what survives once heuristic edges go)
    direct = {f['id']: {t for c in f['calls'] if c['resolution'] == 'direct' for t in c['targets']}
              for f in target}
    surviving = []
    for f in target:
        if not f['recursive']:
            continue
        seen, todo = set(), list(direct.get(f['id'], ()))
        while todo:
            x = todo.pop()
            if x == f['id']:
                surviving.append(f['id'])
                break
            if x in seen or x not in direct:
                continue
            seen.add(x)
            todo.extend(direct[x])
    return {'indirect_calls_by_resolution': dict(res),
            'indirect_jumps': {'resolved_tables': tables, 'unresolved': unres},
            'recursive': sum(1 for f in target if f['recursive']),
            'recursive_through_direct_calls': len(surviving),
            'recursive_through_direct_calls_fns': [by_id[x]['name'] for x in surviving]}


def census(package_dir):
    p = os.path.join(package_dir, 'map', 'census.json')
    if not os.path.exists(p):
        return {'note': 'no data: census.json is written by S18'}
    with open(p) as f:
        c = json.load(f)
    rows = c.get('functions', c) if isinstance(c, dict) else c
    return {'functions': len(rows),
            'finished': sum(1 for r in rows if r.get('finished'))}


def fragility(m, package_dir):
    rows = []
    for f in m['functions']:
        sid = f['status_id'] or ''
        if not sid:
            continue
        ns = sid.split('.')[2] if sid.startswith('ZesuExec.Fn.') else sid
        d = os.path.join(package_dir, 'ZesuExec', 'Fn', ns)
        n = 0
        for p in glob.glob(os.path.join(d, '*.lean')):
            if os.path.basename(p) in ('Gen.lean',):  # generated
                continue
            with open(p) as fh:
                n += len(ADDR.findall(fh.read()))
        rows.append([f['id'], f['name'], n])
    return {'address_literals': table(('fn', 'name', 'literals'), rows)}


def forecast(m, target, items):
    """Open cut points per size band x items per cut point x dollars per item (plan S10.4).

    Samples: proved functions with costed items (excluding `infra`). For each size band the
    25th/50th/75th percentiles of the sample's items per cut point and dollars per item; a band
    without a sample takes the pooled sample. A function's open cut points are all its cuts when
    unproved, the cuts with an open item when it has a plan."""
    led = defaultdict(list)
    by_fn = {f['id']: f for f in m['functions']}
    alias = {f['status_id']: f['id'] for f in m['functions'] if f['status_id']}
    for i in items:
        fid = alias.get(i.get('fn'), i.get('fn'))
        if fid in by_fn and i.get('kind') != 'infra':
            led[fid].append(i)
    sample = [f for f in m['functions'] if f['state'] in PROVED and led.get(f['id'])]
    band = {f['id']: f['classes'][0] for f in m['functions']}
    sampled_classes = {c for f in sample for c in f['classes']}

    def rates(fs):
        ipc = [len(led[f['id']]) / max(len(f['cuts']), 1) for f in fs]
        dpi = [(i.get('cost') or {}).get('usd') or 0 for f in fs for i in led[f['id']]]
        return ipc, dpi

    pooled = rates(sample)
    per_band = {}
    for b in sorted({band[f['id']] for f in target}):
        fs = [f for f in sample if band[f['id']] == b]
        per_band[b] = (rates(fs), bool(fs))

    def open_cuts(f):
        if f['state'] in PROVED or f['service']:
            return 0
        return f['open_cuts'] if f['vc_cuts'] else len(f['cuts'])

    totals = {p: 0.0 for p in PCTS}
    rows = []
    unsampled = 0
    open_total = 0
    for b, ((ipc, dpi), has) in per_band.items():
        if not has:
            ipc, dpi = pooled
        oc = sum(open_cuts(f) for f in target if band[f['id']] == b)
        q = {p: (pct(ipc, p) * pct(dpi, p) if ipc and dpi else None) for p in PCTS}
        for p in PCTS:
            if q[p] is not None:
                totals[p] += oc * q[p]
        rows.append([b, oc, 'yes' if has else 'pooled'] +
                    [_r(pct(ipc, 50), 2) if ipc else None, _r(pct(dpi, 50), 2) if dpi else None] +
                    [round(oc * q[p], 0) if q[p] is not None else None for p in PCTS])
    for f in target:
        oc = open_cuts(f)
        open_total += oc
        if any(c not in sampled_classes for c in f['classes']):
            unsampled += oc
        (ipc, dpi), has = per_band.get(band[f['id']], (pooled, False))
        if not has:
            ipc, dpi = pooled
        f['forecast'] = ({f'p{p}': round(oc * pct(ipc, p) * pct(dpi, p), 2) for p in PCTS}
                         if oc and ipc and dpi else None)
    by_class = []
    for c in CLASSES:
        oc = sum(open_cuts(f) for f in target if c in f['classes'])
        by_class.append([c, oc, sum(1 for f in sample if c in f['classes'])])
    return {'sample_functions': [f['id'] for f in sample],
            'totals_usd': {f'p{p}': round(totals[p], 0) for p in PCTS},
            'open_cut_points': open_total,
            'unsampled_share': _r(unsampled / open_total) if open_total else None,
            'by_band': table(('size band', 'open cut points', 'sample', 'items/cut p50',
                              '$/item p50', '$ p25', '$ p50', '$ p75'), rows),
            'by_class': table(('class', 'open cut points', 'closed sample functions'), by_class)}


# ---------------------------------------------------------------------------------- compute

def read_history(path):
    try:
        with open(path) as f:
            return [json.loads(line) for line in f if line.strip()]
    except FileNotFoundError:
        return []


def load_waivers(package_dir):
    p = os.path.join(package_dir, 'map', 'waivers.json')
    try:
        with open(p) as f:
            return json.load(f)
    except FileNotFoundError:
        return {'pre_revision': [], 'waivers': {}}


def compute(m, items, per_agent, build_json=None, package_dir='.', reviews_csr=None,
            history=None):
    target = [f for f in m['functions'] if f['set'] == 'target']
    if history is None:
        history = read_history(os.path.join(package_dir, 'map', 'history.jsonl'))
    pre = set(load_waivers(package_dir).get('pre_revision', []))
    if reviews_csr is None:
        rp = os.path.join(package_dir, 'map', 'reviews.json')
        reviews_csr = {}
        if os.path.exists(rp):
            with open(rp) as f:
                reviews_csr = json.load(f).get('csr', {})
    return {'schema': 'zmap.metrics.v1',
            'generated': datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
            'coverage': coverage(target),
            'trust': trust(m, target, reviews_csr, package_dir),
            'contracts': contracts(m, history),
            'meaning': meaning(m, target, package_dir),
            'automation': automation(m, pre),
            'effort': effort(m, items, per_agent),
            'build': build(m, build_json),
            'map_precision': map_precision(m, target),
            'census': census(package_dir),
            'fragility': fragility(m, package_dir),
            'forecast': forecast(m, target, items)}


def _git(package_dir, *args):
    try:
        return subprocess.run(['git', '-C', package_dir, *args], capture_output=True, text=True,
                              check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def append_history(path, m, met, package_dir):
    commit = _git(package_dir, 'rev-parse', 'HEAD')
    code = {s: i for i, s in enumerate(STATES)}
    mcode = {s: i for i, s in enumerate(MEANING)}
    callers = defaultdict(bool)
    for f in m['functions']:
        if f['registered'] or f['state'] in PROVED:
            for c in f['proof_callees']:
                callers[c] = True
    line = {'commit': commit, 'ts': met['generated'],
            'state_codes': list(STATES), 'meaning_codes': list(MEANING),
            'coverage': met['coverage']['headline'],
            'auto_share': met['automation']['auto_share'],
            'usd': met['effort']['total']['usd'],
            'fns': {f['id']: [code[f['state']], mcode[f['meaning']]]
                    for f in m['functions'] if f['set'] == 'target'},
            'hashes': {f['id']: dict(f['hashes'], dep=bool(f['state'] in PROVED or callers[f['id']]))
                       for f in m['functions'] if f['hashes']}}
    old = [h for h in read_history(path) if h.get('commit') != commit]
    with open(path, 'w') as f:
        for h in old + [line]:
            f.write(json.dumps(h, separators=(',', ':')) + '\n')


# ---------------------------------------------------------------------------------- printing

def _cell(x):
    if x is None:
        return '-'
    if isinstance(x, float):
        return f'{x:.4g}' if abs(x) < 1 else f'{x:,.2f}'.rstrip('0').rstrip('.')
    return str(x)


def render_group(name, g):
    """Markdown of one metrics group: scalars, then tables."""
    out = [f'## {name}', '']
    for k, v in g.items():
        if isinstance(v, dict) and 'columns' in v:
            continue
        if isinstance(v, list) and len(v) > 12:
            v = v[:12] + ['…']
        out.append(f'- {k}: {json.dumps(v) if isinstance(v, (dict, list)) else _cell(v)}')
    for k, v in g.items():
        if isinstance(v, dict) and 'columns' in v:
            out += ['', f'{k}:', '', '| ' + ' | '.join(v['columns']) + ' |',
                    '|' + '---|' * len(v['columns'])]
            out += ['| ' + ' | '.join(_cell(x) for x in r) + ' |' for r in v['rows']]
    return '\n'.join(out) + '\n'


# ---------------------------------------------------------------------------------- brief

def brief(m, fid_or_name, items):
    """At most 60 lines for a subagent (plan S10.7)."""
    from . import workqueue
    from .costmodel import residual_class as rc
    by_id = {f['id']: f for f in m['functions']}
    f = workqueue.find(m, fid_or_name)
    L = [f'{f["id"]} {f["name"]}  state {f["state"]}  meaning {f["meaning"]}  '
         f'classes {",".join(f["classes"])}']
    def spec(g):
        return (g['theorem_names'] or {}).get('spec') if g['theorems']['spec'] else None
    c = f['contract'] or {}
    hyps = ', '.join(h['name'] + ': ' + h['type'] for h in f['hyps'] or [])
    L.append(f'contract: {c.get("contract", "none")}/{c.get("review", "-")}; end theorem '
             f'{spec(f) or "-"}; hyps {hyps or "-"}')
    if f['rests_on']:
        L.append('rests on: ' + ', '.join(f'{r} {by_id[r]["name"]}' for r in f['rests_on']))
    L.append('callee contracts:')
    for cid in (f['proof_callees'] or f['callees'])[:12]:
        g = by_id[cid]
        L.append(f'  {cid} {g["name"]} [{g["state"]}] {spec(g) or "-"}')
    L.append(f'cuts ({len(f["cuts"])}): ' + ' '.join(f'{x["pc"]:#x}:{x["why"]}' for x in f['cuts'][:16])
             + (' …' if len(f['cuts']) > 16 else ''))
    opens = []
    for cu in f['vc_cuts']:
        if cu.get('cut_lemma') == 'open':
            opens.append(f'  cut {cu["pc"]:#x}: {rc(cu.get("residual"))}')
        for lf in cu['leaves']:
            if lf.get('state') == 'open':
                opens.append(f'  leaf {cu["pc"]:#x}_{lf["i"]} -> {lf.get("exit")} '
                             f'{hex(lf["target"]) if lf.get("target") is not None else lf.get("target_sym")}: '
                             f'{rc(lf.get("residual"))}')
    L.append(f'open items ({len(opens)}):')
    L += opens[:20] + ([f'  … {len(opens) - 20} more (zmap show)'] if len(opens) > 20 else [])
    # cheapest comparable closed items: same kind as the open work, in functions sharing a class
    kinds = ('leaf', 'cut_lemma') if opens else ('contract', 'assertion', 'leaf')
    cls = set(f['classes'])
    alias = {g['status_id']: g['id'] for g in m['functions'] if g['status_id']}
    cand = []
    for it in items:
        g = by_id.get(alias.get(it.get('fn'), it.get('fn')))
        if (g and g['id'] != f['id'] and it.get('outcome') == 'closed' and it.get('kind') in kinds
                and cls & set(g['classes']) and (it.get('cost') or {}).get('usd')):
            cand.append((it['cost']['usd'], it, g))
    cand.sort(key=lambda x: x[0])
    L.append('cheapest comparable closed items:')
    for usd, it, g in cand[:3]:
        L.append(f'  ${usd:.2f} {it.get("minutes") or 0:.0f} min  {it["kind"]} {it["item"]} ({g["name"]})')
    if not cand:
        L.append('  none')
    return '\n'.join(L[:60])


# ---------------------------------------------------------------------------------- check

def check(package_dir, now=None):
    """Failures of plan S10.7's `zmap check`; [] when it passes."""
    from . import ledger
    from .cost import parse_ts
    mp = os.path.join(package_dir, 'map')
    now = now if now is not None else datetime.datetime.now(datetime.timezone.utc).timestamp()
    fails = []
    rows = ledger.read(os.path.join(mp, 'ledger.jsonl'))
    for it in ledger.pair(rows):
        if it['stop'] is None and now - parse_ts(it['ts']) > 24 * 3600:
            fails.append(f'ledger item {it["id"]} ({it["agent"]}: {it["item"]}) started {it["ts"]} '
                         f'has no stop after 24 hours')
    for i, r in enumerate(rows):
        if ledger.is_v2(r):
            typed = [k for k in ledger.TYPED if k in r]
            if typed:
                fails.append(f'ledger line {i + 1}: schema-2 record carries typed {", ".join(typed)}')
    try:
        with open(os.path.join(mp, 'map.json')) as f:
            m = json.load(f)
    except FileNotFoundError:
        return fails + ['map/map.json missing']
    waivers = load_waivers(package_dir).get('waivers', {})
    for f in m['functions']:
        if f['state'] not in CLOSED:
            continue
        if f.get('hyps'):
            fails.append(f'{f["id"]} {f["name"]} is {f["state"]} with non-Pre hypotheses: '
                         + ', '.join(h['name'] for h in f['hyps']))
        w = set(waivers.get(f['id'], []))
        if not f.get('nonvacuity') and 'nonvacuity' not in w:
            fails.append(f'{f["id"]} {f["name"]} is {f["state"]} without a non-vacuity theorem')
        if not f.get('snapshot') and 'snapshot' not in w:
            fails.append(f'{f["id"]} {f["name"]} is {f["state"]} without a snapshot test')
    met = os.path.join(mp, 'metrics.json')
    if not os.path.exists(met):
        fails.append('map/metrics.json missing')
    elif os.path.getmtime(met) < os.path.getmtime(os.path.join(mp, 'map.json')):
        fails.append('map/metrics.json is older than map/map.json')
    return fails


def register(sub, package, load):
    import sys
    mp = os.path.join(package, 'map')
    me = sub.add_parser('metrics', help='write metrics.json, or print one group')
    me.add_argument('--group', choices=GROUPS)
    me.add_argument('--map', default=os.path.join(mp, 'map.json'))
    me.add_argument('--out', default=os.path.join(mp, 'metrics.json'))

    def go_metrics(a):
        if a.group:
            met = load(a.out)
            print(render_group(a.group, met[a.group]), end='')
            return
        from . import cost, ledger
        m = load(a.map)
        agents = cost.Agents(cost.read_rows(cost.load_sessions(os.path.join(mp, 'sessions.json'))))
        items, per_agent = cost.attribute(ledger.read(os.path.join(mp, 'ledger.jsonl')),
                                          cost.read_backfill(os.path.join(mp, 'backfill.jsonl')),
                                          agents)
        bp = os.path.join(mp, 'build.json')
        met = compute(m, items, per_agent, load(bp) if os.path.exists(bp) else None, package)
        with open(a.out, 'w') as f:
            json.dump(met, f, indent=1)
            f.write('\n')
        print(f'zmap: metrics -> {a.out}')
    me.set_defaults(func=go_metrics)

    br = sub.add_parser('brief', help='at most 60 lines about one function, for a subagent')
    br.add_argument('fn')
    br.add_argument('--map', default=os.path.join(mp, 'map.json'))

    def go_brief(a):
        from . import cost, ledger
        m = load(a.map)
        agents = cost.Agents(cost.read_rows(cost.load_sessions(os.path.join(mp, 'sessions.json'))))
        items, _ = cost.attribute(ledger.read(os.path.join(mp, 'ledger.jsonl')),
                                  cost.read_backfill(os.path.join(mp, 'backfill.jsonl')), agents)
        try:
            print(brief(m, a.fn, items))
        except KeyError as e:
            sys.exit(f'zmap: no function {e}')
    br.set_defaults(func=go_brief)

    ck = sub.add_parser('check', help='tracking check (plan S10.7); exit 1 on a failure')

    def go_check(a):
        fails = check(package)
        for x in fails:
            print('FAIL ' + x)
        if fails:
            sys.exit(1)
        print('zmap check: pass')
    ck.set_defaults(func=go_check)
