"""Merge the static map, the proof status (`zesu-status`), reviews and the costed ledger into
map.json (programme plan S3, S10).

Per function, besides the static fields: proof fields from the status, `state` (S10.6), `rests_on`,
`classes` (S10.5), `stem`, `meaning` (S10.4), `meaning_links` and `post_mentions_model` (S10.2),
`proof_callees`, `cost` (S10.1), `auto_share`. `forecast` is added by `metrics`.
"""
import bisect
import os
import re
from collections import Counter, defaultdict

CLOSED = ('closed+compliance', 'closed+sail', 'closed')
PROVED = CLOSED + ('closed-on-assumptions',)
STATES = ('closed+compliance', 'closed+sail', 'closed', 'closed-on-assumptions', 'conditional',
          'in-proof', 'contract-draft', 'assumed', 'blocked', 'ready', 'waiting', 'out')
ITEM_STATES = ('auto', 'manual', 'open')
MEANING = ('spec-sail', 'model', 'machine-only', 'none')
SIZE_BANDS = ((150, 'size:<=150'), (600, 'size:151-600'), (3000, 'size:601-3000'),
              (None, 'size:>3000'))
LOOP_BANDS = ((0, 'loops:0'), (3, 'loops:1-3'), (None, 'loops:>3'))
CLASSES = tuple(b for _, b in SIZE_BANDS) + tuple(b for _, b in LOOP_BANDS) + (
    'recursive', 'irreducible', 'jump-table', 'indirect-call', 'accelerator', 'ecall',
    'generic-copy')
COST_KEYS = ('usd', 'unknown', 'requests', 'builds', 'totalTokens', 'input', 'output',
             'cacheRead', 'cacheWrite')
ANON = re.compile(r'__anon_\d+$')


def stem(name):
    return ANON.sub('', name)


def _band(n, bands):
    for hi, label in bands:
        if hi is None or n <= hi:
            return label


def classes(f, stem_counts):
    """Structural classes of a static function (S10.5)."""
    out = [_band(f['n_instr'], SIZE_BANDS), _band(len(f['loops']), LOOP_BANDS)]
    forms = f.get('forms') or {}
    if f.get('recursive'):
        out.append('recursive')
    if f.get('irreducible'):
        out.append('irreducible')
    if f.get('jump_tables'):
        out.append('jump-table')
    if any(c['kind'] == 'indirect' for c in f['calls']):
        out.append('indirect-call')
    if any(k.startswith('csr') for k in forms):
        out.append('accelerator')
    if 'ecall' in forms or any(b['kind'] == 'ecall' for b in f['blockers']):
        out.append('ecall')
    if stem_counts[stem(f['name'])] > 1:
        out.append('generic-copy')
    return out


def cost_totals(items):
    """Sums of costed ledger items (cost.attribute): count, closed, minutes, cost keys, by kind."""
    def tot(its):
        t = {'items': len(its), 'closed': sum(i.get('outcome') == 'closed' for i in its),
             'abandoned': sum(i.get('outcome') == 'abandoned' for i in its),
             'minutes': round(sum(i.get('minutes') or 0 for i in its), 2)}
        for k in COST_KEYS:
            v = sum((i.get('cost') or {}).get(k) or 0 for i in its)
            t[k] = round(v, 4) if k == 'usd' else round(v, 2)
        return t
    by_kind = defaultdict(list)
    for i in items:
        by_kind[i.get('kind')].append(i)
    return {'all': tot(items), 'by_kind': {k: tot(v) for k, v in sorted(by_kind.items(),
                                                                         key=lambda kv: str(kv[0]))}}


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


def merge(static, status, reviews, items, status_source=''):
    """`items`: costed ledger items (`cost.attribute`); `fn` may be a status alias."""
    fns = static['functions']
    by_id = {f['id']: f for f in fns}
    by_entry = {f['entry']: f for f in fns}
    contracts = reviews.get('contracts', {})
    assumed = set(reviews.get('assumed', []))
    assumed_notes = reviews.get('assumed_notes', {})
    services = set(reviews.get('services', []))
    models = {fid: c['model'] for fid, c in contracts.items() if c.get('model')}

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

    led = defaultdict(list)
    for it in items:
        fid = it.get('fn')
        if fid:
            led[alias.get(fid, fid)].append(it)

    target = [f for f in fns if f['set'] == 'target']
    stem_counts = Counter(stem(f['name']) for f in target)

    # Per-function proof fields.
    for f in fns:
        st = f.pop('_status', None)
        th = (st or {}).get('theorems', {})
        f['stem'] = stem(f['name'])
        f['classes'] = classes(f, stem_counts)
        f['status_id'] = (st.get('fn') or st.get('id')) if st else None
        f['legacy'] = bool(st and st.get('legacy'))
        f['theorems'] = {k: bool(th.get(k)) for k in ('reach', 'spec', 'sail', 'compliance')}
        f['theorem_names'] = (st or {}).get('names')
        f['registered'] = bool(st) and not f['legacy']
        f['assembled'] = bool(st and st.get('assembled'))
        for k in ('hashes', 'hyps', 'nonvacuity', 'snapshot', 'post_consts'):
            f[k] = (st or {}).get(k)
        counts = Counter()
        cut_counts = Counter()
        vc_cuts = []
        proof_callees = set()
        for c in (st or {}).get('cuts', []):
            cut_counts[c.get('cut_lemma', 'open')] += 1
            leaves = []
            for leaf in c.get('leaves', []):
                counts[leaf.get('state', 'open')] += 1
                lf = dict(leaf, cfg=_leaf_join(f, c['pc'], leaf, by_entry))
                if leaf.get('target') in by_entry and (leaf.get('exit') == 'call'
                                                        or lf['cfg']['target_kind'] == 'callee'):
                    proof_callees.add(by_entry[leaf['target']]['id'])
                leaves.append(lf)
            vc_cuts.append(dict(c, leaves=leaves))
        f['vc_cuts'] = vc_cuts
        f['leaves'] = {k: counts[k] for k in ITEM_STATES}
        f['cut_lemmas'] = {k: cut_counts[k] for k in ITEM_STATES}
        n_leaves = sum(counts.values())
        f['auto_share'] = round(counts['auto'] / n_leaves, 4) if n_leaves else None
        f['open_items'] = counts['open'] + cut_counts['open']
        f['open_cuts'] = sum(1 for c in vc_cuts if c.get('cut_lemma') == 'open'
                             or any(lf.get('state') == 'open' for lf in c['leaves']))
        # plans: the callees their leaves call; spike proofs without a plan: the functions whose
        # end theorems the proof uses (`spec_callees`, measured by `zesu-status`), else (a status
        # without them, such as the legacy fixture) the direct callees (a proof states no
        # heuristic indirect-call edge); both: the functions whose `Spec` a hypothesis of the end
        # theorem assumes
        if not vc_cuts:
            sc = (st or {}).get('spec_callees')
            if sc is not None:
                proof_callees = {by_entry[e]['id'] for e in sc if e in by_entry}
            else:
                proof_callees = {t for c in f['calls'] if c['resolution'] == 'direct'
                                 for t in c['targets']}
        for h in f['hyps'] or ():
            proof_callees |= {by_entry[e]['id'] for e in h.get('spec_entries', ()) if e in by_entry}
        f['proof_callees'] = sorted(proof_callees - {f['id']})
        f['contract'] = contracts.get(f['id'])
        f['assumed'] = f['id'] in assumed
        f['service'] = f['id'] in services
        f['cost'] = cost_totals(led[f['id']])

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
        f['proved'] = f['state'] if f['state'] in CLOSED else None

    # S10.6: closed only when every transitive proof callee is closed or a service.
    memo = {}

    def rests_on(fid, stack=()):
        if fid in memo:
            return memo[fid]
        out = set()
        for c in by_id[fid]['proof_callees']:
            g = by_id[c]
            if g['service'] or c in stack:
                continue
            if g['state'] in CLOSED:
                out |= rests_on(c, stack + (fid,))
            else:
                out.add(c)
        memo[fid] = out
        return out

    for f in fns:
        f['rests_on'] = []
        if f['state'] in CLOSED:
            r = sorted(rests_on(f['id']) - {f['id']})
            if r:
                f['state'] = 'closed-on-assumptions'
                f['rests_on'] = r

    for f in fns:
        if f['state'] is not None:
            continue
        if f['set'] != 'target':
            f['state'] = 'out'
            continue
        pending = [c for c in f['callees'] if c != f['id']
                   and by_id[c]['state'] not in PROVED + ('assumed',)]
        f['state'] = 'waiting' if pending else 'ready'
        f['waiting_on'] = pending

    # Meaning (plan Terms) and meaning links (S10.2).
    for f in fns:
        consts = set(f['post_consts'] or ())
        own = models.get(f['id'])
        f['post_mentions_model'] = (own in consts) if own else None
        if f['theorems']['compliance']:
            f['meaning'] = 'spec-sail'
        elif own and own in consts:
            f['meaning'] = 'model'
        elif f['contract'] or f['theorems']['spec'] or f['theorems']['reach']:
            f['meaning'] = 'machine-only'
        else:
            f['meaning'] = 'none'
        f['meaning_links'] = {c: bool(models.get(c) and models[c] in consts)
                              for c in sorted(set(f['callees']) | set(f['proof_callees']))
                              if c != f['id']}

    trust = []
    for fid in sorted(assumed):
        trust.append({'kind': 'assumed', 'fn': fid, 'name': by_id[fid]['name'],
                      'source': assumed_notes.get(fid)})
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
    out['cost_totals'] = cost_totals(items)
    out['state_counts'] = {s: sum(f['state'] == s for f in fns) for s in STATES}
    return out


def register(sub, package, load, dump):
    """`zmap merge`: map.json, then metrics.json and one line of history.jsonl."""
    import sys
    from . import cost, ledger, metrics
    mp = os.path.join(package, 'map')
    mg = sub.add_parser('merge', help='merge static map, status, reviews, costed ledger; metrics')
    mg.add_argument('--static', required=True)
    mg.add_argument('--status', required=True)
    mg.add_argument('--reviews')
    mg.add_argument('--ledger', default=os.path.join(mp, 'ledger.jsonl'))
    mg.add_argument('--backfill', default=os.path.join(mp, 'backfill.jsonl'))
    mg.add_argument('--sessions', default=os.path.join(mp, 'sessions.json'))
    mg.add_argument('--build', default=os.path.join(mp, 'build.json'))
    mg.add_argument('--out', required=True)
    mg.add_argument('--metrics', help='default: metrics.json beside --out')
    mg.add_argument('--history', help='default: history.jsonl beside --out')

    def go(args):
        static = load(args.static)
        status = load(args.status)
        if status.get('schema') != 'zmap.status.v1':
            sys.exit(f'zmap: {args.status} is not zmap.status.v1')
        reviews = load(args.reviews) if args.reviews else {}
        rows = ledger.read(args.ledger)
        agents = cost.Agents(cost.read_rows(cost.load_sessions(args.sessions)))
        items, per_agent = cost.attribute(rows, cost.read_backfill(args.backfill), agents)
        out = merge(static, status, reviews, items, status_source=status.get('source', args.status))
        build = load(args.build) if os.path.exists(args.build) else None
        met = metrics.compute(out, items, per_agent, build, package_dir=package)
        dump(out, args.out)
        d = os.path.dirname(os.path.abspath(args.out))
        mpath = args.metrics or os.path.join(d, 'metrics.json')
        dump(met, mpath, compact=False)
        hpath = args.history or os.path.join(d, 'history.jsonl')
        metrics.append_history(hpath, out, met, package)
        print('zmap: ' + ', '.join(f'{k} {v}' for k, v in out['state_counts'].items() if v)
              + f' -> {args.out}, {mpath}, {hpath}')
    mg.set_defaults(func=go)
