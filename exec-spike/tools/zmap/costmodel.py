"""Cost model (programme plan S8, S10.4).

`render(map, items, rows, metrics)` returns the Markdown of `map/COSTMODEL.md` from the merged
map, the costed ledger items (`cost.attribute`: dollars, tokens, requests and builds from the
session logs; minutes from timestamps), the raw ledger rows (for automation share notes) and
`metrics.json`:

1. per item kind: count, median and total minutes and dollars, tokens, requests, builds;
2. plan leaves by state, manual and open leaves by residual class;
3. per function with proof material or items: static features beside its actual totals;
4. the share of leaves closed automatically before and after each automation item, read from
   ledger notes `auto_share <fn> <auto>/<total> -> <auto>/<total>`;
5. for the target set, function counts and feature sums by state;
6. cost drivers: dollars per cut point in proved functions with a class against those without;
7. unattributed cost per agent;
8. the forecast (25th, 50th, 75th percentile totals in dollars and tokens, from dollars and
   tokens per cut point of fully ledgered functions) from `metrics.json`.
"""
import os
import re
import statistics

from .merge import CLASSES, PROVED

FEATURES = ('cuts', 'loops', 'calls', 'joins', 'leaves_estimate', 'n_instr')
SHARE_RE = re.compile(r'auto_share\s+(\S+)\s+(\d+)/(\d+)\s*->\s*(\d+)/(\d+)')


def features(f):
    """The static feature vector of a map function."""
    return {'cuts': len(f.get('cuts') or []), 'loops': len(f.get('loops') or []),
            'calls': len(f.get('calls') or []), 'joins': len(f.get('joins') or []),
            'leaves_estimate': f.get('leaves_estimate') or 0, 'n_instr': f.get('n_instr') or 0}


def residual_class(residual):
    """A manual or open leaf's residual class: `leaf_diag`'s `class <c>` (the first stage of
    `leaf_auto` that did not close), else the head symbol `zesu_auto` recorded, or `none`."""
    if not residual:
        return 'none'
    m = re.search(r'class (\S+)', residual)
    if m:
        return m.group(1)
    m = re.search(r'head ([^\s;]+)', residual)
    return m.group(1) if m else residual.split(';')[0].strip()


def _num(x):
    return x if isinstance(x, (int, float)) else 0


def _fmt(x):
    if x is None:
        return '-'
    if isinstance(x, float):
        return f'{x:.2f}' if x != int(x) else str(int(x))
    return str(x)


def _usd(i):
    return _num((i.get('cost') or {}).get('usd'))


def kind_table(items):
    """{kind: (count, median min, total min, median usd, total usd, tokens, requests, builds)}."""
    out = {}
    for kind in sorted({i.get('kind') for i in items if i.get('kind')}):
        its = [i for i in items if i.get('kind') == kind]
        mins = [_num(i.get('minutes')) for i in its]
        usd = [_usd(i) for i in its]
        c = [i.get('cost') or {} for i in its]
        out[kind] = (len(its), statistics.median(mins), sum(mins), statistics.median(usd),
                     sum(usd), sum(_num(x.get('totalTokens')) for x in c),
                     sum(_num(x.get('requests')) for x in c), sum(_num(x.get('builds')) for x in c))
    return out


def leaves_by_state(m):
    """Counts of plan leaves by state, and manual and open leaves by residual class."""
    states = {'auto': 0, 'manual': 0, 'open': 0}
    classes = {}
    for f in m.get('functions', []):
        for c in f.get('vc_cuts') or []:
            for lf in c.get('leaves') or []:
                st = lf.get('state')
                if st in states:
                    states[st] += 1
                if st in ('manual', 'open'):
                    k = residual_class(lf.get('residual'))
                    classes[k] = classes.get(k, 0) + 1
    return states, classes


def share_history(rows):
    """(ts, item, fn, before auto, before total, after auto, after total) from ledger notes."""
    out = []
    for r in rows:
        mt = SHARE_RE.search(r.get('note') or '')
        if mt:
            fn, a0, t0, a1, t1 = mt.groups()
            out.append((r.get('ts'), r.get('item'), fn, int(a0), int(t0), int(a1), int(t1)))
    return sorted(out, key=lambda x: x[0] or '')


def drivers(m):
    """{class: (proved functions with it, $/cut with, $/cut without, multiplier)} over proved
    functions with costed items."""
    fs = [f for f in m.get('functions', []) if f.get('state') in PROVED
          and ((f.get('cost') or {}).get('all') or {}).get('usd')]

    def rate(g):
        cuts = sum(len(f.get('cuts') or []) for f in g)
        return sum(f['cost']['all']['usd'] for f in g) / cuts if cuts else None
    out = {}
    for c in CLASSES:
        w = [f for f in fs if c in (f.get('classes') or [])]
        wo = [f for f in fs if c not in (f.get('classes') or [])]
        rw, ro = rate(w), rate(wo)
        out[c] = (len(w), rw, ro, rw / ro if rw is not None and ro else None)
    return out


def _pct(a, t):
    return f'{100 * a / t:.0f}%' if t else '-'


def render(m, items, rows, met):
    lines = ['# Cost model (programme plan S8, S10.4)', '',
             'Generated by `python3 -m zmap costmodel` from `map/map.json`, `map/ledger.jsonl` '
             '(costed from the session logs of `map/sessions.json`; schema-1 rows through '
             '`map/backfill.jsonl`) and `map/metrics.json`. No number here is typed by hand.', '']

    lines += ['## Effort by item kind', '',
              '| kind | items | median min | total min | median $ | total $ | tokens | requests | builds |',
              '|---|---:|---:|---:|---:|---:|---:|---:|---:|']
    for kind, (n, mmed, mtot, umed, utot, tok, req, bld) in kind_table(items).items():
        lines.append(f'| {kind} | {n} | {_fmt(mmed)} | {_fmt(mtot)} | {_fmt(umed)} | '
                     f'{_fmt(utot)} | {int(tok)} | {_fmt(req)} | {_fmt(bld)} |')
    states, classes = leaves_by_state(m)
    total_leaves = sum(states.values())
    leaf_usd = sum(_usd(i) for i in items if i.get('kind') == 'leaf')
    lines += ['', f'Plan leaves: auto {states["auto"]}, manual {states["manual"]}, '
              f'open {states["open"]} (auto share {_pct(states["auto"], total_leaves)}). '
              f'Ledger `leaf` dollars per manual leaf: '
              f'{_fmt(leaf_usd / states["manual"]) if states["manual"] else "-"}.', '',
              '| residual class (manual and open leaves) | leaves |', '|---|---:|']
    for k, n in sorted(classes.items(), key=lambda kv: (-kv[1], kv[0])):
        lines.append(f'| {k} | {n} |')

    lines += ['', '## Functions: static features and actuals', '',
              '| function | state | ' + ' | '.join(FEATURES) +
              ' | leaves auto/manual/open | items | minutes | $ |',
              '|---|---|' + '---:|' * len(FEATURES) + '---|---:|---:|---:|']
    for f in m.get('functions', []):
        c = (f.get('cost') or {}).get('all') or {}
        lv = f.get('leaves') or {}
        if not c.get('items') and not f.get('registered') and not f.get('legacy'):
            continue
        fv = features(f)
        lines.append(f'| {f["id"]} {f.get("name", "")} | {f.get("state", "")} | '
                     + ' | '.join(str(fv[k]) for k in FEATURES)
                     + f' | {lv.get("auto", "-")}/{lv.get("manual", "-")}/{lv.get("open", "-")}'
                     + f' | {c.get("items", 0)} | {_fmt(c.get("minutes", 0))} | '
                     + f'{_fmt(c.get("usd", 0))} |')

    lines += ['', '## Auto-closed share before and after each automation item', '',
              '| when | item | function | before | after |', '|---|---|---|---:|---:|']
    for ts, item, fn, a0, t0, a1, t1 in share_history(rows):
        lines.append(f'| {ts} | {item} | {fn} | {a0}/{t0} ({_pct(a0, t0)}) | '
                     f'{a1}/{t1} ({_pct(a1, t1)}) |')

    summed = [k for k in FEATURES if k != 'leaves_estimate']
    lines += ['', '## Target set: functions and features by state', '',
              'Feature sums per state; `leaves_estimate` is the median (path counts grow '
              'exponentially, so a sum says nothing).', '',
              '| state | functions | ' + ' | '.join(summed) + ' | median leaves_estimate |',
              '|---|---:|' + '---:|' * (len(summed) + 1)]
    by_state = {}
    for f in m.get('functions', []):
        if f.get('set') != 'target':
            continue
        by_state.setdefault(f.get('state', '?'), []).append(features(f))
    for st, fvs in sorted(by_state.items()):
        sums = [sum(fv[k] for fv in fvs) for k in summed]
        med = statistics.median(fv['leaves_estimate'] for fv in fvs)
        lines.append(f'| {st} | {len(fvs)} | ' + ' | '.join(str(x) for x in sums)
                     + f' | {_fmt(med)} |')

    lines += ['', '## Cost drivers', '',
              'Dollars per cut point in proved functions with the class, against proved functions '
              'without it. `-` until both sides have a sample.', '',
              '| class | proved functions with it | $/cut with | $/cut without | multiplier |',
              '|---|---:|---:|---:|---:|']
    for c, (n, rw, ro, mult) in drivers(m).items():
        lines.append(f'| {c} | {n} | {_fmt(rw)} | {_fmt(ro)} | {_fmt(mult)} |')

    eff = (met or {}).get('effort') or {}
    lines += ['', '## Unattributed cost per agent', '',
              f'Session dollars {_fmt(eff.get("session_usd"))}, inside ledger items '
              f'{_fmt((eff.get("total") or {}).get("usd"))}, unattributed '
              f'{_fmt(eff.get("unattributed_usd"))} '
              f'({_pct(eff.get("unattributed_usd") or 0, eff.get("session_usd") or 0)}). '
              f'Requests without usage (unknown cost): {eff.get("unknown_cost_requests", "-")}.', '',
              '| agent | session $ | in items $ | unattributed $ | share |', '|---|---:|---:|---:|---:|']
    for row in (eff.get('by_agent') or {}).get('rows', []):
        a, s, i, u, sh, _ = row
        lines.append(f'| {a} | {_fmt(s)} | {_fmt(i)} | {_fmt(u)} | '
                     f'{"-" if sh is None else f"{100 * sh:.0f}%"} |')

    fc = (met or {}).get('forecast') or {}
    tot = fc.get('totals_usd') or {}
    tok = fc.get('totals_tokens') or {}
    lines += ['', '## Forecast', '',
              'Open cut points x dollars and tokens per cut point, measured only on functions '
              'whose whole proof is in the ledger (plan S29: proved or conditional, with a '
              '`contract` item, not in `waivers.json` `not_fully_ledgered`; sample: '
              f'{", ".join(fc.get("sample_functions") or []) or "none"}). Totals sum the size '
              'bands; a band without a sample uses the pooled sample. Revision 2 lifts the '
              '"no extrapolated total" rule.', '',
              f'Totals: p25 ${_fmt(tot.get("p25"))}, p50 ${_fmt(tot.get("p50"))}, '
              f'p75 ${_fmt(tot.get("p75"))}; tokens p25 {_fmt(tok.get("p25"))}, '
              f'p50 {_fmt(tok.get("p50"))}, p75 {_fmt(tok.get("p75"))}; '
              f'for {fc.get("open_cut_points", "-")} open cut points; '
              f'share of open cut points in a class with no closed sample: '
              f'{"-" if fc.get("unsampled_share") is None else f"{100 * fc["unsampled_share"]:.0f}%"}.']
    for key in ('sample', 'by_band', 'by_class'):
        t = fc.get(key) or {'columns': [], 'rows': []}
        if t['columns']:
            text = 3 if key == 'sample' else 1
            lines += ['', '| ' + ' | '.join(t['columns']) + ' |',
                      '|' + '---|' * text + '---:|' * (len(t['columns']) - text)]
            lines += ['| ' + ' | '.join(_fmt(x) for x in r) + ' |' for r in t['rows']]
    return '\n'.join(lines) + '\n'


def register(sub, package, load):
    mp = os.path.join(package, 'map')
    cm = sub.add_parser('costmodel', help='cost model (COSTMODEL.md)')
    cm.add_argument('--map', default=os.path.join(mp, 'map.json'))
    cm.add_argument('--ledger', default=os.path.join(mp, 'ledger.jsonl'))
    cm.add_argument('--backfill', default=os.path.join(mp, 'backfill.jsonl'))
    cm.add_argument('--sessions', default=os.path.join(mp, 'sessions.json'))
    cm.add_argument('--metrics', help='default: metrics.json beside --map')
    cm.add_argument('--out', required=True)

    def go(a):
        from . import cost, ledger
        rows = ledger.read(a.ledger)
        agents = cost.Agents(cost.read_rows(cost.load_sessions(a.sessions)))
        items, _ = cost.attribute(rows, cost.read_backfill(a.backfill), agents)
        mpath = a.metrics or os.path.join(os.path.dirname(os.path.abspath(a.map)), 'metrics.json')
        met = load(mpath) if os.path.exists(mpath) else {}
        with open(a.out, 'w') as f:
            f.write(render(load(a.map), items, rows, met))
        print(f'zmap: cost model -> {a.out}')
    cm.set_defaults(func=go)
