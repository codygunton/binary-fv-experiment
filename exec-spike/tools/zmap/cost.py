"""Cost from the agents' session logs (programme plan S10.1).

`map/sessions.json` lists session directories:

    {"root": "~/.omp/agent/sessions/-zesislar", "sessions": ["<session>", ...]}

Each session is a top-level `<session>.jsonl` (agent `coordinator`) and a directory of
`<Agent>.jsonl` files, nested agents under `<Agent>/<Agent>.<Sub>.jsonl` (agent = file stem).
`changes.jsonl`, `local/` and `blobs/` are not agents.

One row per model request: an assistant `message` line (its `message.usage`), or a
`model_usage` line (side requests the harness makes for the agent: captions, completion probes,
compaction). Fields: agent, session, `t` (epoch seconds), tokens by kind, `usd`
(`usage.cost.total`; `None` when the line has no usage: unknown cost, counted as a request),
`builds` (`bash` tool calls whose command contains `lake build` or `lake env lean`), `aux` (the
`model_usage` purpose, else `None`).

Attribution: every request is owned by at most one ledger item of its agent. Backfilled
schema-1 rows (`map/backfill.jsonl`, written once by `zmap cost backfill`) own the requests in
their interval; schema-2 items own the requests of their agent between `start` and `stop` not
already owned. Unattributed cost of an agent = its session dollars minus the dollars its items
own.
"""
import bisect
import datetime
import json
import os
from collections import defaultdict

TOKENS = ('input', 'output', 'cacheRead', 'cacheWrite', 'totalTokens')
NOT_AGENTS = ('changes',)
NOT_DIRS = ('local', 'blobs')
COORDINATOR = 'coordinator'


def parse_ts(s):
    """ISO-8601 (`...Z`, optional fraction) to epoch seconds."""
    if s.endswith('Z'):
        s = s[:-1] + '+00:00'
    return datetime.datetime.fromisoformat(s).timestamp()


def fmt_ts(t):
    return datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def load_sessions(path):
    """Session directories (absolute) from `sessions.json`; [] when the file is missing."""
    try:
        with open(path) as f:
            cfg = json.load(f)
    except FileNotFoundError:
        return []
    root = os.path.expanduser(cfg.get('root', ''))
    return [os.path.join(root, s) for s in cfg.get('sessions', [])]


def agent_files(session_dir):
    """[(agent, path)] of one session: the top-level log, then every agent log below the dir."""
    out = []
    top = session_dir.rstrip('/') + '.jsonl'
    if os.path.exists(top):
        out.append((COORDINATOR, top))
    for dirpath, dirnames, filenames in os.walk(session_dir):
        if dirpath == session_dir:
            dirnames[:] = [d for d in dirnames if d not in NOT_DIRS]
        dirnames.sort()
        for fn in sorted(filenames):
            stem, ext = os.path.splitext(fn)
            if ext == '.jsonl' and stem not in NOT_AGENTS:
                out.append((stem, os.path.join(dirpath, fn)))
    return out


def _builds(content):
    n = 0
    for c in content or ():
        if c.get('type') == 'toolCall' and c.get('name') == 'bash':
            cmd = (c.get('arguments') or {}).get('command') or ''
            if 'lake build' in cmd or 'lake env lean' in cmd:
                n += 1
    return n


def _row(usage, t, builds, aux):
    usage = usage or {}
    cost = usage.get('cost') or {}
    r = {k: usage.get(k) or 0 for k in TOKENS}
    r['t'] = t
    r['usd'] = cost.get('total') if 'total' in cost else None
    r['builds'] = builds
    r['aux'] = aux
    return r


def parse_file(path):
    """Request rows of one log file (without agent/session)."""
    rows = []
    with open(path, 'rb') as f:
        for raw in f:
            # cheap filter: tool results and user lines are most of the bytes
            if b'"model_usage"' not in raw[:64] and b'"role":"assistant"' not in raw:
                continue
            try:
                d = json.loads(raw)
            except ValueError:
                continue
            ty = d.get('type')
            if ty == 'model_usage':
                rows.append(_row(d.get('usage'), parse_ts(d['timestamp']), 0,
                                 d.get('purpose') or 'aux'))
            elif ty == 'message':
                m = d.get('message') or {}
                if m.get('role') != 'assistant':
                    continue
                rows.append(_row(m.get('usage'), parse_ts(d['timestamp']),
                                 _builds(m.get('content')), None))
    return rows


def read_rows(session_dirs):
    """Request rows of every agent of every session, sorted by time."""
    rows = []
    for sd in session_dirs:
        sess = os.path.basename(sd.rstrip('/'))
        for agent, path in agent_files(sd):
            for r in parse_file(path):
                rows.append(dict(r, agent=agent, session=sess))
    rows.sort(key=lambda r: r['t'])
    return rows


def _zero():
    return {'usd': 0.0, 'unknown': 0, 'requests': 0, 'builds': 0,
            **{k: 0 for k in TOKENS}}


def add(acc, r, share=1.0):
    acc['requests'] += share
    acc['builds'] += r['builds'] * share
    for k in TOKENS:
        acc[k] += r[k] * share
    if r['usd'] is None:
        acc['unknown'] += share
    else:
        acc['usd'] += r['usd'] * share
    return acc


def rounded(acc):
    out = {}
    for k, v in acc.items():
        out[k] = round(v, 4) if k == 'usd' else (round(v, 2) if isinstance(v, float) else v)
    return out


class Agents:
    """Request rows indexed per agent (sorted by time) and per (session, agent) stream."""

    def __init__(self, rows):
        self.rows = defaultdict(list)
        for r in rows:
            self.rows[r['agent']].append(r)
        self.t = {a: [r['t'] for r in rs] for a, rs in self.rows.items()}
        self.spans = {}
        for a, rs in self.rows.items():
            sp = {}
            for r in rs:
                lo, hi = sp.get(r['session'], (r['t'], r['t']))
                sp[r['session']] = (min(lo, r['t']), max(hi, r['t']))
            self.spans[a] = sp

    def stream_of(self, agent, t):
        """The session of `agent` whose span holds `t`, else the latest one starting before it."""
        sp = self.spans.get(agent, {})
        inside = [s for s, (lo, hi) in sp.items() if lo <= t <= hi]
        if inside:
            return max(inside, key=lambda s: sp[s][0])
        before = [s for s, (lo, _) in sp.items() if lo <= t]
        return max(before, key=lambda s: sp[s][0]) if before else None

    def index_range(self, agent, t0, t1):
        """Indices of `agent`'s rows with t0 < t <= t1."""
        ts = self.t.get(agent, [])
        return range(bisect.bisect_right(ts, t0), bisect.bisect_right(ts, t1))


def backfill_rows(ledger_rows, agents, done_lines=()):
    """Cost the schema-1 ledger rows not in `done_lines` (line numbers, 0-based).

    An entry's interval runs from the previous entry of the same agent (in the same session
    stream) to its own timestamp; the first entry of a stream starts just before the stream's
    first request. Entries of one agent with the same timestamp share one interval equally.
    """
    by_agent = defaultdict(list)
    for i, r in enumerate(ledger_rows):
        if r.get('schema') == 2:
            continue
        by_agent[r.get('agent')].append((parse_ts(r['ts']), i, r))
    out = []
    for agent, ents in by_agent.items():
        ents.sort(key=lambda e: (e[0], e[1]))
        groups = []
        for t, i, r in ents:
            if groups and groups[-1][0] == t:
                groups[-1][1].append((i, r))
            else:
                groups.append((t, [(i, r)]))
        prev = {}
        for t, members in groups:
            sess = agents.stream_of(agent, t)
            if sess is None:
                t0 = None
            else:
                lo = agents.spans[agent][sess][0]
                t0 = prev.get(sess, lo - 1)
                prev[sess] = t
            todo = [(i, r) for i, r in members if i not in done_lines]
            if not todo:
                continue
            acc = _zero()
            if t0 is not None:
                for k in agents.index_range(agent, t0, t):
                    if agents.rows[agent][k]['session'] == sess:
                        add(acc, agents.rows[agent][k])
            n = len(members)
            for i, r in todo:
                share = {k: v / n for k, v in acc.items()}
                out.append({'line': i, 'ts': r['ts'], 'agent': agent, 'item': r.get('item'),
                            'fn': r.get('fn'), 'kind': r.get('kind'),
                            'outcome': r.get('outcome'), 'session': sess,
                            'from': fmt_ts(t0) if t0 is not None else None, 'to': r['ts'],
                            'from_t': t0, 'to_t': t, 'shared_by': n,
                            'minutes': round((t - t0) / 60 / n, 2) if t0 is not None else None,
                            'cost': rounded(share), 'backfill': True})
    out.sort(key=lambda b: b['line'])
    return out


def attribute(ledger_rows, backfill, agents, now=None):
    """Costed items and per-agent totals.

    Returns (items, per_agent): items are dicts with `fn`, `item`, `kind`, `agent`, `outcome`,
    `minutes`, `cost` (usd, tokens, requests, builds, unknown), `backfill`, `open`; per_agent maps
    an agent to {session, items, unattributed} cost totals.
    """
    from . import ledger as led
    now = now if now is not None else datetime.datetime.now(datetime.timezone.utc).timestamp()
    owned = {a: [None] * len(rs) for a, rs in agents.rows.items()}
    items = []
    for b in backfill:
        it = {k: b.get(k) for k in ('fn', 'item', 'kind', 'agent', 'outcome', 'minutes')}
        it.update(backfill=True, open=False, cost=b['cost'], ts=b['ts'])
        items.append(it)
        a = b['agent']
        if b.get('from_t') is None or a not in owned:
            continue
        for k in agents.index_range(a, b['from_t'], b['to_t']):
            if agents.rows[a][k]['session'] == b.get('session'):
                owned[a][k] = 'backfill'
    for it in led.pair(ledger_rows):
        a = it['agent']
        t0 = parse_ts(it['ts'])
        stop = it['stop']
        t1 = parse_ts(stop['ts']) if stop else now
        acc = _zero()
        for k in agents.index_range(a, t0, t1):
            if owned[a][k] is None:
                owned[a][k] = it['id']
                add(acc, agents.rows[a][k])
        items.append({'fn': it.get('fn'), 'item': it.get('item'), 'kind': it.get('kind'),
                      'agent': a, 'outcome': stop.get('outcome') if stop else None,
                      'minutes': round((t1 - t0) / 60, 2), 'backfill': False,
                      'open': stop is None, 'cost': rounded(acc), 'ts': it['ts'],
                      'id': it['id']})
    per_agent = {}
    for a, rs in agents.rows.items():
        sess, inside = _zero(), _zero()
        for r, o in zip(rs, owned[a]):
            add(sess, r)
            if o is not None:
                add(inside, r)
        un = {k: sess[k] - inside[k] for k in sess}
        per_agent[a] = {'session': rounded(sess), 'items': rounded(inside),
                        'unattributed': rounded(un),
                        'unattributed_share': round(un['usd'] / sess['usd'], 4) if sess['usd'] else None}
    # backfill rows for agents with no log still count inside items
    for b in backfill:
        if b['agent'] not in per_agent:
            per_agent[b['agent']] = {'session': rounded(_zero()), 'items': rounded(_zero()),
                                     'unattributed': rounded(_zero()), 'unattributed_share': None}
    return items, per_agent


def read_backfill(path):
    try:
        with open(path) as f:
            return [json.loads(line) for line in f if line.strip()]
    except FileNotFoundError:
        return []


def run_backfill(ledger_path, backfill_path, sessions_path):
    """Append the cost of every schema-1 row not yet backfilled; returns the new rows."""
    from . import ledger as led
    rows = led.read(ledger_path)
    old = read_backfill(backfill_path)
    done = {b['line'] for b in old}
    for b in old:
        r = rows[b['line']] if b['line'] < len(rows) else None
        if r is None or r.get('ts') != b['ts'] or r.get('agent') != b['agent'] \
                or r.get('item') != b['item']:
            raise ValueError(f'backfill line {b["line"]} no longer matches the ledger')
    agents = Agents(read_rows(load_sessions(sessions_path)))
    new = backfill_rows(rows, agents, done)
    with open(backfill_path, 'a') as f:
        for b in new:
            f.write(json.dumps(b, separators=(',', ':')) + '\n')
    return new


def register(sub, package):
    """`zmap cost backfill|agents`."""
    mp = os.path.join(package, 'map')
    c = sub.add_parser('cost', help='cost from session logs')
    csub = c.add_subparsers(dest='cost_cmd', required=True)

    def common(p):
        p.add_argument('--ledger', default=os.path.join(mp, 'ledger.jsonl'))
        p.add_argument('--backfill', default=os.path.join(mp, 'backfill.jsonl'))
        p.add_argument('--sessions', default=os.path.join(mp, 'sessions.json'))

    b = csub.add_parser('backfill', help='cost the schema-1 ledger rows once')
    common(b)

    def go_backfill(a):
        new = run_backfill(a.ledger, a.backfill, a.sessions)
        usd = sum(n['cost']['usd'] for n in new)
        print(f'zmap: backfilled {len(new)} rows (${usd:.2f}) -> {a.backfill}')
    b.set_defaults(func=go_backfill)

    g = csub.add_parser('agents', help='per-agent session, item and unattributed dollars')
    common(g)

    def go_agents(a):
        from . import ledger as led
        agents = Agents(read_rows(load_sessions(a.sessions)))
        _, per = attribute(led.read(a.ledger), read_backfill(a.backfill), agents)
        print('| agent | session $ | in items $ | unattributed $ | share | unknown-cost requests |')
        print('|---|---:|---:|---:|---:|---:|')
        for ag, v in sorted(per.items(), key=lambda kv: -kv[1]['session']['usd']):
            sh = v['unattributed_share']
            print(f'| {ag} | {v["session"]["usd"]:.2f} | {v["items"]["usd"]:.2f} | '
                  f'{v["unattributed"]["usd"]:.2f} | {"-" if sh is None else f"{100 * sh:.0f}%"} | '
                  f'{v["session"]["unknown"]} |')
    g.set_defaults(func=go_agents)
