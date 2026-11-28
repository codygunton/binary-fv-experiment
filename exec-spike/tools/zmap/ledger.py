"""Effort ledger `map/ledger.jsonl` (programme plan S10.1).

Schema 1 (S1 to S9, `zmap ledger log`, retired): one row per finished item with typed `minutes`,
`usd` and `requests`. Its rows are costed once by `zmap cost backfill`.

Schema 2: an item is a `start` record and a `stop` record with the same `id`.

    {"schema": 2, "rec": "start", "id": N, "ts": ..., "fn": ..., "item": ..., "kind": ..., "agent": ...}
    {"schema": 2, "rec": "stop", "id": N, "agent": ..., "ts": ..., "outcome": ..., "note": ...}

Ids are `max + 1` in the file; branches merged later may repeat an id, so an item is keyed by
(`agent`, `id`) and `stop --id N` picks the open item with that id.

No minutes, dollars or tokens are typed: `merge` computes them from the two timestamps and the
agent's session-log messages between them (`cost.py`). An agent has at most one item open.
"""
import datetime
import fcntl
import json
import os

KINDS = ('contract', 'assertion', 'cut', 'cut_lemma', 'leaf', 'run', 'rule', 'review',
         'compliance', 'form', 'service', 'infra')
OUTCOMES = ('closed', 'open', 'abandoned')
TYPED = ('minutes', 'usd', 'dollars', 'requests', 'tokens', 'builds')


def now_ts(now=None):
    now = now or datetime.datetime.now(datetime.timezone.utc)
    return now.strftime('%Y-%m-%dT%H:%M:%SZ')


def read(path):
    try:
        with open(path) as f:
            return [json.loads(line) for line in f if line.strip()]
    except FileNotFoundError:
        return []


def is_v2(r):
    return r.get('schema') == 2


def pair(rows):
    """Schema-2 items: [{start record fields..., stop: stop record or None}] in file order,
    keyed by (agent, id)."""
    items = {}
    for r in rows:
        if not is_v2(r):
            continue
        key = (r.get('agent'), r.get('id'))
        if r.get('rec') == 'start':
            items[key] = dict(r, stop=None)
        elif r.get('rec') == 'stop' and key in items:
            items[key]['stop'] = r
    return list(items.values())


def open_items(rows, agent=None):
    return [it for it in pair(rows) if it['stop'] is None
            and (agent is None or it['agent'] == agent)]


def _append_locked(path, build):
    """Read the ledger and append `build(rows)` under an exclusive lock (agents share the file)."""
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    with open(path, 'a+') as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            f.seek(0)
            rows = [json.loads(line) for line in f if line.strip()]
            row = build(rows)
            f.seek(0, os.SEEK_END)
            f.write(json.dumps(row) + '\n')
            f.flush()
            return row
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def start(path, fn, item, kind, agent, now=None):
    if kind not in KINDS:
        raise ValueError(f'kind must be one of {KINDS}')

    def build(rows):
        held = open_items(rows, agent)
        if held:
            h = held[0]
            raise ValueError(f'agent {agent} has item {h["id"]} ({h["item"]}) open since '
                             f'{h["ts"]}; stop it first')
        ids = [r['id'] for r in rows if is_v2(r) and r.get('rec') == 'start']
        return {'schema': 2, 'rec': 'start', 'id': max(ids, default=0) + 1, 'ts': now_ts(now),
                'fn': None if fn in (None, '-') else fn, 'item': item, 'kind': kind,
                'agent': agent}
    return _append_locked(path, build)


def stop(path, item_id, outcome, note=None, now=None):
    if outcome not in OUTCOMES:
        raise ValueError(f'outcome must be one of {OUTCOMES}')

    def build(rows):
        its = [it for it in pair(rows) if it['id'] == item_id]
        if not its:
            raise ValueError(f'no started item {item_id}')
        held = [it for it in its if it['stop'] is None]
        if not held:
            raise ValueError(f'item {item_id} is already stopped')
        if len(held) > 1:
            raise ValueError(f'item id {item_id} is open for several agents: '
                             + ', '.join(it['agent'] for it in held))
        return {'schema': 2, 'rec': 'stop', 'id': item_id, 'agent': held[0]['agent'],
                'ts': now_ts(now), 'outcome': outcome, 'note': note}
    return _append_locked(path, build)


def register(sub, default_ledger):
    """`zmap ledger start|stop|open`."""
    import sys
    lg = sub.add_parser('ledger', help='effort ledger (schema 2: start/stop)')
    lsub = lg.add_subparsers(dest='ledger_cmd', required=True)

    def run(fn):
        def go(args):
            try:
                print(json.dumps(fn(args)))
            except ValueError as e:
                sys.exit(f'zmap ledger: {e}')
        return go

    s = lsub.add_parser('start', help='open an item; prints its record (with id)')
    s.add_argument('--fn', required=True, help='function id, or - for none')
    s.add_argument('--item', required=True)
    s.add_argument('--kind', required=True, choices=KINDS)
    s.add_argument('--agent', required=True, help='session-log file stem; coordinator for the top level')
    s.add_argument('--ledger', default=default_ledger)
    s.set_defaults(func=run(lambda a: start(a.ledger, a.fn, a.item, a.kind, a.agent)))

    t = lsub.add_parser('stop', help='close an item')
    t.add_argument('--id', required=True, type=int)
    t.add_argument('--outcome', required=True, choices=OUTCOMES)
    t.add_argument('--note')
    t.add_argument('--ledger', default=default_ledger)
    t.set_defaults(func=run(lambda a: stop(a.ledger, a.id, a.outcome, a.note)))

    o = lsub.add_parser('open', help='list open items')
    o.add_argument('--agent')
    o.add_argument('--ledger', default=default_ledger)

    def show_open(a):
        for it in open_items(read(a.ledger), a.agent):
            print(json.dumps({k: v for k, v in it.items() if k != 'stop'}))
    o.set_defaults(func=show_open)
