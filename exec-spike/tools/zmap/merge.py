"""Merge the static map, the proof status (`zesu-status`), reviews and the ledger into map.json."""
import bisect
import json
from collections import Counter, defaultdict

CLOSED = ('closed+compliance', 'closed+sail', 'closed')
STATES = ('closed+compliance', 'closed+sail', 'closed', 'conditional', 'in-proof',
          'contract-draft', 'assumed', 'blocked', 'ready', 'waiting', 'out')
ITEM_STATES = ('auto', 'manual', 'open')


def read_ledger(path):
    rows = []
    if path:
        try:
            with open(path) as f:
                rows = [json.loads(line) for line in f if line.strip()]
        except FileNotFoundError:
            pass
    return rows


def _totals(rows):
    t = {'items': len(rows), 'minutes': 0.0, 'usd': 0.0, 'requests': 0,
         'closed': sum(r.get('outcome') == 'closed' for r in rows)}
    for r in rows:
        t['minutes'] += r.get('minutes') or 0
        t['usd'] += r.get('usd') or 0
        t['requests'] += r.get('requests') or 0
    t['minutes'] = round(t['minutes'], 2)
    t['usd'] = round(t['usd'], 4)
    return t


def ledger_totals(rows):
    by_kind = defaultdict(list)
    for r in rows:
        by_kind[r['kind']].append(r)
    return {'all': _totals(rows), 'by_kind': {k: _totals(v) for k, v in sorted(by_kind.items())}}


def _leaf_join(fn, cut_pc, leaf, entries):
    """Place a status leaf on the CFG: its cut's block and the block of its exit target."""
    starts = [b['start'] for b in fn['blocks']]
    cuts = {c['pc'] for c in fn['cuts']}

    def block_of(pc):
        i = bisect.bisect_right(starts, pc) - 1
        if i >= 0 and pc < fn['blocks'][i]['end']:
            return starts[i]
        return None

    t = leaf.get('target')
    if t is None:
        kind = None
    elif t in cuts:
        kind = 'cut'
    elif t in entries:
        kind = 'callee'
    elif block_of(t) is not None:
        kind = 'block'
    else:
        kind = 'outside'
    return {'cut_block': block_of(cut_pc), 'target_block': block_of(t) if t is not None else None,
            'target_kind': kind}


def merge(static, status, reviews, ledger_rows, status_source=''):
    fns = static['functions']
    by_id = {f['id']: f for f in fns}
    by_entry = {f['entry']: f for f in fns}
    contracts = reviews.get('contracts', {})
    assumed = set(reviews.get('assumed', []))
    services = set(reviews.get('services', []))

    # Status rows by entry; status ids (e.g. "F1", "TX") map to static ids.
    alias = {}
    for st in status.get('functions', []):
        f = by_entry.get(st['entry'])
        if f is None:
            raise ValueError(f'status function {st.get("id")} at {st["entry"]:#x} is not a function entry')
        f['_status'] = st
        for key in (st.get('id'), st.get('fn')):
            if key:
                alias[key] = f['id']

    # Ledger rows per static id.
    led = defaultdict(list)
    for r in ledger_rows:
        fid = r.get('fn')
        if fid:
            led[alias.get(fid, fid)].append(r)

    # Per-function proof fields.
    for f in fns:
        st = f.pop('_status', None)
        th = (st or {}).get('theorems', {})
        f['status_id'] = (st.get('fn') or st.get('id')) if st else None
        f['legacy'] = bool(st and st.get('legacy'))
        f['theorems'] = {k: bool(th.get(k)) for k in ('reach', 'spec', 'sail', 'compliance')}
        f['theorem_names'] = (st or {}).get('names')
        f['registered'] = bool(st) and not f['legacy']
        f['assembled'] = bool(st and st.get('assembled'))
        counts = Counter()
        cut_counts = Counter()
        vc_cuts = []
        for c in (st or {}).get('cuts', []):
            cut_counts[c.get('cut_lemma', 'open')] += 1
            leaves = []
            for leaf in c.get('leaves', []):
                counts[leaf.get('state', 'open')] += 1
                leaves.append(dict(leaf, cfg=_leaf_join(f, c['pc'], leaf, by_entry)))
            vc_cuts.append(dict(c, leaves=leaves))
        f['vc_cuts'] = vc_cuts
        f['leaves'] = {k: counts[k] for k in ITEM_STATES}
        f['cut_lemmas'] = {k: cut_counts[k] for k in ITEM_STATES}
        f['open_items'] = counts['open'] + cut_counts['open']
        f['contract'] = contracts.get(f['id'])
        f['assumed'] = f['id'] in assumed
        f['service'] = f['id'] in services
        f['ledger'] = ledger_totals(led[f['id']])

    # States: the first rule that applies. Callee states for ready/waiting need closed first.
    def base_state(f):
        th = f['theorems']
        if th['reach'] or th['spec']:
            if th['compliance']:
                return 'closed+compliance'
            return 'closed+sail' if th['sail'] else 'closed'
        if f['registered'] and f['assembled'] and f['open_items']:
            return 'conditional'
        if f['registered']:
            return 'in-proof'
        if (f['contract'] or {}).get('contract') == 'draft':
            return 'contract-draft'
        if f['assumed'] or f['service']:
            return 'assumed'
        if f['blockers']:
            return 'blocked'
        return None

    for f in fns:
        f['state'] = base_state(f)
    for f in fns:
        if f['state'] is not None:
            continue
        if f['set'] != 'target':
            f['state'] = 'out'
            continue
        pending = [c for c in f['callees'] if c != f['id']
                   and by_id[c]['state'] not in CLOSED + ('assumed',)]
        f['state'] = 'waiting' if pending else 'ready'
        f['waiting_on'] = pending

    trust = []
    for fid in sorted(assumed):
        trust.append({'kind': 'assumed', 'fn': fid, 'name': by_id[fid]['name']})
    for fid in sorted(services):
        trust.append({'kind': 'service', 'fn': fid, 'name': by_id[fid]['name']})
    for fid, c in sorted(contracts.items()):
        if c.get('review') == 'unreviewed':
            trust.append({'kind': 'contract-unreviewed', 'fn': fid, 'name': by_id[fid]['name'],
                          'contract': c.get('contract'), 'source': c.get('source')})

    out = dict(static)
    out['schema'] = 'zmap.map.v1'
    out['status_source'] = status_source
    out['trust'] = trust
    out['ledger_totals'] = ledger_totals(ledger_rows)
    out['state_counts'] = {s: sum(f['state'] == s for f in fns) for s in STATES}
    return out
