"""Metrics, history, forecast, agent brief and the check (programme plan S10.4, S10.7).

`compute(map, items, per_agent, build)` returns `metrics.json`: one object per group of plan
S10.4 (`coverage`, `trust`, `contracts`, `meaning`, `automation`, `effort`, `build`,
`map_precision`, `census`, `fragility`, `forecast`) and of S29 (`tiers`, `replay`, `reuse`,
`varloc`, `fit`), each a dict of named values and tables (`{"columns": [...], "rows": [[...]]}`).
It also sets each function's `forecast` in the map. Groups without data say so in `note`.

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
          'map_precision', 'census', 'fragility', 'forecast', 'tiers', 'replay', 'reuse',
          'varloc', 'fit')
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


def ledger_by_fn(m, items):
    """Costed items per map function id (status aliases resolved)."""
    by_fn = {f['id'] for f in m['functions']}
    alias = {f['status_id']: f['id'] for f in m['functions'] if f.get('status_id')}
    led = defaultdict(list)
    for i in items:
        fid = alias.get(i.get('fn'), i.get('fn'))
        if fid in by_fn:
            led[fid].append(i)
    return led


def fully_ledgered(m, led, excluded=()):
    """Functions whose whole proof is in the ledger (plan S29): proved or conditional, with a
    `contract` item (the proof was ledgered from its contract on), and not listed in
    `waivers.json` `not_fully_ledgered` (proved before the ledger, later items cover only
    refinements)."""
    return [f for f in m['functions']
            if (f['state'] in PROVED or f['state'] == 'conditional') and f['id'] not in excluded
            and any(i.get('kind') == 'contract' for i in led.get(f['id'], ()))]


def forecast(m, target, items, excluded=()):
    """Open cut points x measured dollars and tokens per cut point (plan S10.4, S29).

    Sample: the fully ledgered functions; each gives one rate, all its items' dollars (tokens)
    over its cut points. Totals sum over size bands (a function is in exactly one) the band's
    open cut points times the 25th/50th/75th percentile of the band's sample rates; a band
    without a sample takes the pooled sample. A function's open cut points are all its cuts
    when unproved, the cuts with an open item when it has a plan."""
    led = ledger_by_fn(m, items)
    sample = fully_ledgered(m, led, excluded)
    band = {f['id']: f['classes'][0] for f in m['functions']}
    sampled_classes = {c for f in sample for c in f['classes']}

    def rate(f, key):
        return sum((i.get('cost') or {}).get(key) or 0 for i in led[f['id']]) / max(len(f['cuts']), 1)

    def rates(fs):
        return [rate(f, 'usd') for f in fs], [rate(f, 'totalTokens') for f in fs]

    pooled = rates(sample)

    def rates_for(fs):
        return (rates(fs), True) if fs else (pooled, False)

    def open_cuts(f):
        if f['state'] in PROVED or f['service']:
            return 0
        return f['open_cuts'] if f['vc_cuts'] else len(f['cuts'])

    def q(vals, p):
        return pct(vals, p) if vals else None

    def row(label, oc, fs):
        (usd, tok), has = rates_for(fs)
        u = {p: q(usd, p) for p in PCTS}
        t = {p: q(tok, p) for p in PCTS}
        return ([label, oc, len(fs) if has else 'pooled']
                + [_r(u[50], 2), None if t[50] is None else round(t[50])]
                + [None if u[p] is None else round(oc * u[p]) for p in PCTS]
                + [None if t[p] is None else round(oc * t[p]) for p in PCTS]), u, t

    tot_usd = {p: 0.0 for p in PCTS}
    tot_tok = {p: 0.0 for p in PCTS}
    by_band = []
    band_rates = {}
    for b in sorted({band[f['id']] for f in target}):
        oc = sum(open_cuts(f) for f in target if band[f['id']] == b)
        r, u, t = row(b, oc, [f for f in sample if band[f['id']] == b])
        band_rates[b] = (u, t)
        by_band.append(r)
        for p in PCTS:
            tot_usd[p] += oc * (u[p] or 0)
            tot_tok[p] += oc * (t[p] or 0)
    open_total = unsampled = 0
    for f in target:
        oc = open_cuts(f)
        open_total += oc
        if any(c not in sampled_classes for c in f['classes']):
            unsampled += oc
        u, t = band_rates[band[f['id']]]
        f['forecast'] = (dict({f'p{p}': round(oc * u[p], 2) for p in PCTS},
                              **{f'tokens_p{p}': round(oc * t[p]) for p in PCTS})
                         if oc and u[50] is not None else None)
    by_class = [row(c, sum(open_cuts(f) for f in target if c in f['classes']),
                    [f for f in sample if c in f['classes']])[0] for c in CLASSES]
    rate_rows = [[f['id'], f['name'], f['state'], len(f['cuts']), len(led[f['id']]),
                  round(sum((i.get('cost') or {}).get('usd') or 0 for i in led[f['id']]), 2),
                  _r(rate(f, 'usd'), 2), round(rate(f, 'totalTokens'))] for f in sample]
    cols = ('open cut points', 'sample functions', '$/cut p50', 'tokens/cut p50',
            '$ p25', '$ p50', '$ p75', 'tokens p25', 'tokens p50', 'tokens p75')
    return {'sample_functions': [f['id'] for f in sample],
            'excluded': sorted(excluded),
            'totals_usd': {f'p{p}': round(tot_usd[p]) for p in PCTS},
            'totals_tokens': {f'p{p}': round(tot_tok[p]) for p in PCTS},
            'open_cut_points': open_total,
            'unsampled_share': _r(unsampled / open_total) if open_total else None,
            'sample': table(('fn', 'name', 'state', 'cut points', 'items', 'usd', 'usd/cut',
                             'tokens/cut'), rate_rows),
            'by_band': table(('size band',) + cols, by_band),
            'by_class': table(('class',) + cols, by_class)}


# ---------------------------------------------------------------------------------- S29 groups

def tier_of(i):
    """An item's model tier; ledger records without one predate S29 and ran at tier 2 (plan rule
    14: every kind started at tier 2 until S26)."""
    return i.get('tier') or 2


def tiers(m, items):
    """Cost per item and per cut point by tier, share of items closed at tier 1, escalations."""
    v2 = [i for i in items if not i.get('backfill')]
    by_fn = {f['id']: f for f in m['functions']}
    led = ledger_by_fn(m, v2)
    rows = []
    for t in (1, 2):
        its = [i for i in v2 if tier_of(i) == t]
        s = _sum(its)
        fns = {fid for fid, its_f in led.items() if any(tier_of(i) == t for i in its_f)
               and by_fn[fid]['state'] in PROVED}
        cuts = sum(len(by_fn[fid]['cuts']) for fid in fns)
        fusd = sum((i.get('cost') or {}).get('usd') or 0 for fid in fns for i in led[fid]
                   if tier_of(i) == t)
        ftok = sum((i.get('cost') or {}).get('totalTokens') or 0 for fid in fns for i in led[fid]
                   if tier_of(i) == t)
        rows.append([t, len(its), sum(i.get('outcome') == 'closed' for i in its),
                     sum(1 for i in its if i.get('tier') is None), s['usd'], s['totalTokens'],
                     _r(s['usd'] / len(its), 2) if its else None,
                     round(s['totalTokens'] / len(its)) if its else None,
                     len(fns), cuts, _r(fusd / cuts, 2) if cuts else None,
                     round(ftok / cuts) if cuts else None])
    closed = [i for i in v2 if i.get('outcome') == 'closed']
    esc = [[i.get('id'), i.get('agent'), i.get('fn'), i.get('item'), i.get('escalates'),
            i.get('outcome')] for i in v2 if i.get('escalates') is not None]
    return {'tier1_closed_share': _r(sum(tier_of(i) == 1 for i in closed) / len(closed))
            if closed else None,
            'closed_items': len(closed), 'escalations': len(esc),
            'by_tier': table(('tier', 'items', 'closed', 'without tier (pre-S29)', 'usd', 'tokens',
                              'usd/item', 'tokens/item', 'proved functions', 'their cut points',
                              'usd/cut', 'tokens/cut'), rows),
            'escalated_items': table(('id', 'agent', 'fn', 'item', 'escalates', 'outcome'), esc)}


def _read_json(path):
    try:
        with open(path) as f:
            return json.load(f)
    except (FileNotFoundError, ValueError):
        return None


def replay(package_dir, items):
    """S26 replay results (`map/replay.jsonl`): per kind and residual class, hit rate, attempts,
    tier-1 cost per item, beside the ledger's tier-2 dollars per closed item of that kind."""
    p = os.path.join(package_dir, 'map', 'replay.jsonl')
    try:
        with open(p) as f:
            rs = [json.loads(line) for line in f if line.strip()]
    except FileNotFoundError:
        rs = []
    routing = os.path.exists(os.path.join(package_dir, 'map', 'routing.json'))
    if not rs:
        return {'note': 'no data (map/replay.jsonl missing)', 'routing_json': routing}
    t2 = defaultdict(list)
    for i in items:
        if tier_of(i) == 2 and i.get('outcome') == 'closed':
            t2[i.get('kind')].append((i.get('cost') or {}).get('usd') or 0)
    groups = defaultdict(list)
    for r in rs:
        groups[(r.get('kind') or '-', r.get('class') or '-')].append(r)
    rows = []
    for (k, c), g in sorted(groups.items()):
        hits = sum(bool(r.get('hit')) for r in g)
        rows.append([k, c, len(g), hits, _r(hits / len(g), 2),
                     _r(statistics.mean(r.get('attempts') or 0 for r in g), 2),
                     _r(sum(r.get('usd') or 0 for r in g) / len(g), 3),
                     round(sum(r.get('tokens') or 0 for r in g) / len(g)),
                     _r(statistics.mean(t2[k]), 2) if t2.get(k) else None])
    hits = sum(bool(r.get('hit')) for r in rs)
    return {'items': len(rs), 'hits': hits, 'hit_rate': _r(hits / len(rs)),
            'usd': round(sum(r.get('usd') or 0 for r in rs), 2), 'routing_json': routing,
            'by_class': table(('kind', 'class', 'items', 'hits', 'hit rate', 'attempts mean',
                               'tier-1 usd/item', 'tier-1 tokens/item',
                               'ledger tier-2 usd/closed item'), rows)}


def reuse(m, items):
    """Family reuse ratios: per stem with two or more ledgered copies, each later copy's dollars
    and tokens over the first copy's (the copy whose first item is earliest)."""
    led = ledger_by_fn(m, items)
    fams = defaultdict(list)
    for f in m['functions']:
        if f['set'] == 'target' and 'generic-copy' in f['classes'] and led.get(f['id']):
            fams[f['stem']].append(f)

    def tot(f, k):
        return sum((i.get('cost') or {}).get(k) or 0 for i in led[f['id']])
    rows = []
    for s, fs in sorted(fams.items()):
        if len(fs) < 2:
            continue
        fs.sort(key=lambda f: min(i.get('ts') or '' for i in led[f['id']]))
        first = fs[0]
        u0, t0 = tot(first, 'usd'), tot(first, 'totalTokens')
        for f in fs[1:]:
            rows.append([s, first['id'], f['id'], f['state'], round(u0, 2), round(tot(f, 'usd'), 2),
                         _r(tot(f, 'usd') / u0, 2) if u0 else None,
                         _r(tot(f, 'totalTokens') / t0, 2) if t0 else None])
    if not rows:
        return {'note': 'no data (no family with two ledgered copies)'}
    return {'ratios': table(('stem', 'first copy', 'copy', 'state', 'first usd', 'copy usd',
                             'usd ratio', 'tokens ratio'), rows)}


def varloc(m, target, package_dir):
    """S23 coverage: variables in scope at cut points with a machine location, from
    `map/varloc/index.json` (else the per-function files' `coverage`)."""
    d = os.path.join(package_dir, 'map', 'varloc')
    idx = _read_json(os.path.join(d, 'index.json'))
    per = {}
    if isinstance(idx, dict):
        fns = idx.get('functions') if isinstance(idx.get('functions'), dict) else idx
        per = {k: v for k, v in fns.items() if k.startswith('f_') and isinstance(v, dict)}
    for f in target:
        if f['id'] not in per:
            cov = (_read_json(os.path.join(d, f['id'] + '.json')) or {}).get('coverage')
            if cov:
                per[f['id']] = cov
    if not per:
        return {'note': 'no data (map/varloc/ missing)'}
    tids = {f['id'] for f in target}
    have = [k for k in per if k in tids]
    ins = sum(per[k].get('in_scope') or 0 for k in have)
    loc = sum(per[k].get('located') or 0 for k in have)
    by_id = {f['id']: f for f in target}
    rows = [[k, by_id[k]['name'], per[k].get('in_scope'), per[k].get('located'),
             _r(per[k]['located'] / per[k]['in_scope'], 3) if per[k].get('in_scope') else None]
            for k in sorted(have)]
    return {'target_functions': len(target), 'functions_with_table': len(have),
            'in_scope': ins, 'located': loc, 'located_share': _r(loc / ins) if ins else None,
            'by_function': table(('fn', 'name', 'in scope', 'located', 'share'), rows)}


FIT_RE = re.compile(r'\b(assertions|leaves)\b\W*(\d+)\s+of\s+(\d+)', re.I)


def fit(package_dir):
    """S24 fit counts (`OPEN/checkable/fit.json`, else `FIT.md` lines `assertions: n of m`,
    `leaves: n of m`) and snapshot-screen results (`map/screen.json`)."""
    out = {}
    d = os.path.join(package_dir, 'OPEN', 'checkable')
    fj = _read_json(os.path.join(d, 'fit.json'))
    counts = {}
    if isinstance(fj, dict):
        counts = {k: fj[k] for k in ('assertions', 'leaves') if isinstance(fj.get(k), dict)}
    else:
        try:
            with open(os.path.join(d, 'FIT.md')) as f:
                for k, n, t in FIT_RE.findall(f.read()):
                    counts.setdefault(k.lower(), {'fit': int(n), 'total': int(t)})
        except FileNotFoundError:
            pass
    for k in ('assertions', 'leaves'):
        c = counts.get(k)
        out[f'{k}_fit'] = c.get('fit') if c else None
        out[f'{k}_total'] = c.get('total') if c else None
        out[f'{k}_share'] = _r(c['fit'] / c['total']) if c and c.get('total') else None
    sc = _read_json(os.path.join(package_dir, 'map', 'screen.json'))
    if isinstance(sc, list) and sc:
        res = Counter(r.get('result') or '-' for r in sc)
        out['screen'] = table(('result', 'assertions'), sorted(res.items()))
    if not counts and 'screen' not in out:
        return {'note': 'no data (OPEN/checkable/FIT.md, map/screen.json missing)'}
    return out


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
    waivers = load_waivers(package_dir)
    pre = set(waivers.get('pre_revision', []))
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
            'forecast': forecast(m, target, items, set(waivers.get('not_fully_ledgered', {}))),
            'tiers': tiers(m, items),
            'replay': replay(package_dir, items),
            'reuse': reuse(m, items),
            'varloc': varloc(m, target, package_dir),
            'fit': fit(package_dir)}


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

def family_dir(f):
    """`<Family>` when the function's proof module is under `ZesuExec/Fn/<Family>/`, else None."""
    p = (f.get('status_id') or '').split('.')
    return p[2] if len(p) >= 4 and p[:2] == ['ZesuExec', 'Fn'] else None


def family_failures(m):
    """Plan rule 16, S29: every copy with proof material of a stem that has several target
    copies, one of them proved, is in `ZesuExec/Fn/<Family>/`; all such copies use one family
    directory, and that directory serves no other stem."""
    stems = defaultdict(list)
    dir_stems = defaultdict(set)
    for f in m['functions']:
        if f.get('set') == 'target':
            stems[f.get('stem')].append(f)
        if family_dir(f):
            dir_stems[family_dir(f)].add(f.get('stem'))
    fails = []
    for s, fs in sorted(stems.items(), key=lambda kv: str(kv[0])):
        if len(fs) < 2 or not any(f['state'] in PROVED for f in fs):
            continue
        proofs = [f for f in fs if f.get('status_id')]
        for f in proofs:
            if family_dir(f) is None:
                fails.append(f'{f["id"]} {f["name"]} shares stem {s} with a proved copy but is '
                             f'proved outside ZesuExec/Fn/<Family>/ ({f["status_id"]})')
        dirs = sorted({family_dir(f) for f in proofs} - {None})
        if len(dirs) > 1:
            fails.append(f'copies of {s} are proved in several directories: '
                         + ', '.join(f'Fn/{d}' for d in dirs))
        for d in dirs:
            other = sorted(str(x) for x in dir_stems[d] - {s})
            if other:
                fails.append(f'family directory Fn/{d} of {s} also serves {", ".join(other)}')
    return fails


def check(package_dir, now=None):
    """Failures of plan S10.7's and S29's `zmap check`; [] when it passes."""
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
    w_all = load_waivers(package_dir)
    since = w_all.get('tier_required_from')
    for it in ledger.pair(rows):
        if it.get('tier') not in ledger.TIERS and (since is None or it['ts'] >= since):
            fails.append(f'ledger item {it["id"]} ({it["agent"]}: {it["item"]}) started '
                         f'{it["ts"]} has no tier')
    try:
        with open(os.path.join(mp, 'map.json')) as f:
            m = json.load(f)
    except FileNotFoundError:
        return fails + ['map/map.json missing']
    waivers = w_all.get('waivers', {})
    fails += family_failures(m)
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

    br = sub.add_parser('brief', help='at most 60 lines about one function, for a subagent, then '
                                      'the variable table of each cut point (S23)')
    br.add_argument('fn')
    br.add_argument('--map', default=os.path.join(mp, 'map.json'))
    br.add_argument('--no-vars', dest='vars', action='store_false',
                    help='omit the variable table (map/varloc/<id>.json)')

    def go_brief(a):
        from . import cost, ledger, varloc, workqueue
        m = load(a.map)
        agents = cost.Agents(cost.read_rows(cost.load_sessions(os.path.join(mp, 'sessions.json'))))
        items, _ = cost.attribute(ledger.read(os.path.join(mp, 'ledger.jsonl')),
                                  cost.read_backfill(os.path.join(mp, 'backfill.jsonl')), agents)
        try:
            print(brief(m, a.fn, items))
        except KeyError as e:
            sys.exit(f'zmap: no function {e}')
        if a.vars:
            t = varloc.load(package, workqueue.find(m, a.fn)['id'])
            print(varloc.render(t) if t else 'variables at cut points: no map/varloc table '
                                                  '(zmap varloc build)')
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
