"""Effort ledger: one JSON line per work item in `map/ledger.jsonl`."""
import datetime
import json
import os

KINDS = ('contract', 'assertion', 'cut_lemma', 'leaf', 'run', 'rule', 'review', 'compliance',
         'infra')
OUTCOMES = ('closed', 'open', 'failed')


def log(path, fn, item, kind, agent, minutes, outcome, usd=None, requests=None, note=None,
        now=None):
    if kind not in KINDS:
        raise ValueError(f'kind must be one of {KINDS}')
    if outcome not in OUTCOMES:
        raise ValueError(f'outcome must be one of {OUTCOMES}')
    now = now or datetime.datetime.now(datetime.timezone.utc)
    row = {'ts': now.strftime('%Y-%m-%dT%H:%M:%SZ'), 'fn': None if fn == '-' else fn,
           'item': item, 'kind': kind, 'agent': agent, 'minutes': minutes, 'usd': usd,
           'requests': requests, 'outcome': outcome, 'note': note}
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    with open(path, 'a') as f:
        f.write(json.dumps(row, sort_keys=False) + '\n')
    return row
