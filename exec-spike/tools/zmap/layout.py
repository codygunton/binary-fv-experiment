"""Offline layout of the graph viewer (plan S9). The browser never computes a layout.

Program level (`program`): the call graph of the target set. Longest-path layering from the root
with cycles broken at depth-first back edges; functions with the same stem in one layer form one
stacked item; each layer is ordered by barycentre (4 sweeps) within source-file bands; long edges
get dummy nodes whose positions become the edge's bend points. Every item reserves the width of
its expanded members, so collapsing or expanding a stack moves nothing else.

Function level (`function`): the block grid of the static map (`blocks[].x`, `.y`) in pixels,
orthogonal edge routes through the channels between grid cells (no route crosses a block), back
edges on lanes left of the grid, loop hulls, caller/callee stub rows, call and return routes per
call site, the exit bar, and one block path per proof leaf.
"""
import bisect
import math
import re
from collections import Counter, defaultdict

# Program level geometry (pixels).
R_MIN, R_MAX = 5.0, 26.0
GAP, BAND_GAP, DUMMY_W = 8.0, 26.0, 8.0
LAYER_PAD = 70.0          # vertical room between layers (band labels, edge bends)
SWEEPS = 4

# Function level geometry (pixels).
BW, BH = 132.0, 30.0      # block box
PX, PY = 156.0, 56.0      # grid pitch
CUT_H = 5.0               # cut bar height above the block
STUB_W, STUB_H, STUB_GAP = 150.0, 26.0, 14.0
LEAF_CAP = 4000           # paths enumerated per cut before giving up exact matching

ANON = re.compile(r'__anon_\d+$')


def stem(name):
    return ANON.sub('', name)


def radius(v, vmax):
    if not vmax or v is None:
        return R_MIN
    return R_MIN + (R_MAX - R_MIN) * math.sqrt(max(v, 0) / vmax)


# ---------------------------------------------------------------------------------------------
# Program level


def _back_edges(root, nodes, succ):
    """Depth-first back edges from `root`, then from any node not yet visited (sorted order)."""
    colour = {n: 0 for n in nodes}
    back = set()
    for start in [root] + sorted(nodes):
        if colour.get(start) != 0:
            continue
        stack = [(start, iter(succ[start]))]
        colour[start] = 1
        while stack:
            n, it = stack[-1]
            for m in it:
                if colour[m] == 1:
                    back.add((n, m))
                elif colour[m] == 0:
                    colour[m] = 1
                    stack.append((m, iter(succ[m])))
                    break
            else:
                colour[n] = 2
                stack.pop()
    return back


def _longest_path(nodes, fwd):
    indeg = Counter()
    for n in nodes:
        for m in fwd[n]:
            indeg[m] += 1
    layer = {n: 0 for n in nodes}
    ready = sorted(n for n in nodes if indeg[n] == 0)
    while ready:
        n = ready.pop()
        for m in fwd[n]:
            layer[m] = max(layer[m], layer[n] + 1)
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
    return layer


def program(fns, calls, root):
    """Layout of the program graph.

    fns: [{id, name, src_file, size: {metric: value}}]; calls: iterable of (caller, callee);
    root: id of the root function. Returns {items, functions, bands, layers, routes, width, height}.
    """
    ids = [f['id'] for f in fns]
    by_id = {f['id']: f for f in fns}
    succ = {i: [] for i in ids}
    pairs = sorted({(a, b) for a, b in calls if a in by_id and b in by_id})
    for a, b in pairs:
        if a != b:
            succ[a].append(b)
    for i in ids:
        succ[i].sort()
    back = _back_edges(root, ids, succ)
    fwd = {i: [m for m in succ[i] if (i, m) not in back] for i in ids}
    layer = _longest_path(ids, fwd)

    # Stems: equalise the layers of a stem's copies (push down to the deepest), then restore the
    # layering constraint. A stem whose copies call each other is not stacked.
    groups = defaultdict(list)
    for f in fns:
        groups[stem(f['name'])].append(f['id'])
    stackable = {}
    for s, members in groups.items():
        if len(members) < 2:
            continue
        ms = set(members)
        if any(m in ms for a in members for m in fwd[a]):
            continue
        stackable[s] = members
    for _ in range(len(ids) + 1):
        changed = False
        for members in stackable.values():
            top = max(layer[m] for m in members)
            for m in members:
                if layer[m] != top:
                    layer[m], changed = top, True
        for a in ids:
            for b in fwd[a]:
                if layer[b] <= layer[a]:
                    layer[b], changed = layer[a] + 1, True
        if not changed:
            break

    # Size: radius per metric; a function reserves its largest radius.
    metrics = sorted({k for f in fns for k in f['size']})
    vmax = {k: max((f['size'].get(k) or 0) for f in fns) for k in metrics}
    r_fn = {f['id']: {k: round(radius(f['size'].get(k), vmax[k]), 1) for k in metrics} for f in fns}

    # Items: stacks per (stem, layer, band); everything else is a single item.
    def band(fid):
        return by_id[fid]['src_file'] or '?'

    item_of = {}
    items = {}
    keyed = defaultdict(list)
    for s, members in stackable.items():
        for m in members:
            keyed[(s, layer[m], band(m))].append(m)
    for (s, ly, bd), members in sorted(keyed.items()):
        if len(members) < 2:
            continue
        members.sort(key=lambda m: by_id[m]['name'])
        iid = f's:{s}@{ly}'
        sum_size = {k: sum((by_id[m]['size'].get(k) or 0) for m in members) for k in metrics}
        items[iid] = {'id': iid, 'kind': 'stack', 'stem': s, 'members': members, 'layer': ly,
                      'band': bd, 'r': {k: round(radius(sum_size[k], vmax[k] * len(members)), 1)
                                        for k in metrics}}
        for m in members:
            item_of[m] = iid
    for f in fns:
        if f['id'] not in item_of:
            items[f['id']] = {'id': f['id'], 'kind': 'fn', 'members': [f['id']],
                              'layer': layer[f['id']], 'band': band(f['id']), 'r': r_fn[f['id']]}
            item_of[f['id']] = f['id']
    for it in items.values():
        rmax_members = [max(r_fn[m].values(), default=R_MIN) for m in it['members']]
        expanded = sum(2 * r + GAP for r in rmax_members) - GAP
        it['w'] = max(expanded, 2 * max(it['r'].values(), default=R_MIN))
        it['h'] = 2 * max(rmax_members + list(it['r'].values()))

    # Item graph, long edges split into dummies.
    ipairs = sorted({(item_of[a], item_of[b]) for a, b in pairs if (a, b) not in back
                     and item_of[a] != item_of[b] and a != b})
    nodes_in = defaultdict(list)          # layer -> node ids (items and dummies)
    width = {}
    group = {}                             # band key of an item; dummies are their own group
    for iid, it in items.items():
        nodes_in[it['layer']].append(iid)
        width[iid] = it['w']
        group[iid] = ('b', it['band'])
    up = defaultdict(list)
    down = defaultdict(list)
    chains = {}
    # Long edges into the same item share one dummy per layer (a trunk rising from the target),
    # so hubs like memcpy do not widen every layer above them.
    seen_links = set()
    for a, b in ipairs:
        la, lb = items[a]['layer'], items[b]['layer']
        chain = [a]
        for ly in range(la + 1, lb):
            d = f'd:{b}@{ly}'
            if d not in width:
                nodes_in[ly].append(d)
                width[d] = DUMMY_W
                group[d] = ('d', d)
            chain.append(d)
        chain.append(b)
        for u, v in zip(chain, chain[1:]):
            if (u, v) not in seen_links:
                seen_links.add((u, v))
                down[u].append(v)
                up[v].append(u)
        chains[(a, b)] = chain

    n_layers = max(nodes_in) + 1 if nodes_in else 0
    order = {}
    for ly in range(n_layers):
        row = sorted(nodes_in[ly], key=lambda n: (group[n], n))
        for i, n in enumerate(row):
            order[n] = i
        nodes_in[ly] = row

    def sweep(ly, nbrs):
        row = nodes_in[ly]
        bary = {}
        for n in row:
            ns = nbrs[n]
            bary[n] = sum(order[m] for m in ns) / len(ns) if ns else order[n]
        groups_ = defaultdict(list)
        for n in row:
            groups_[group[n]].append(n)
        gbary = {g: sum(bary[n] for n in ms) / len(ms) for g, ms in groups_.items()}
        new = []
        for g in sorted(groups_, key=lambda g: (gbary[g], g)):
            new.extend(sorted(groups_[g], key=lambda n: (bary[n], order[n])))
        nodes_in[ly] = new
        for i, n in enumerate(new):
            order[n] = i

    for s in range(SWEEPS):
        if s % 2 == 0:
            for ly in range(1, n_layers):
                sweep(ly, up)
        else:
            for ly in range(n_layers - 2, -1, -1):
                sweep(ly, down)

    # Coordinates: left-packed with gaps, each layer centred on x = 0.
    pos = {}
    layers = []
    bands = []
    y = 0.0
    for ly in range(n_layers):
        row = nodes_in[ly]
        h = max([items[n]['h'] for n in row if n in items] + [2 * R_MIN])
        cy = y + LAYER_PAD / 2 + h / 2
        xs = []
        x = 0.0
        prev = None
        for n in row:
            if prev is not None:
                x += BAND_GAP if group[n] != group[prev] else GAP
            xs.append(x)
            x += width[n]
            prev = n
        shift = -x / 2
        cur = None
        for n, x0 in zip(row, xs):
            x0 += shift
            pos[n] = (round(x0 + width[n] / 2, 1), round(cy, 1))
            if n in items:
                g = items[n]['band']
                if cur and cur['file'] == g and cur['_last'] == order[n] - 1:
                    cur['x1'] = round(x0 + width[n], 1)
                    cur['_last'] = order[n]
                else:
                    cur = {'layer': ly, 'file': g, 'x0': round(x0, 1), 'x1': round(x0 + width[n], 1),
                           'y0': round(cy - h / 2 - 6, 1), 'y1': round(cy + h / 2 + 6, 1),
                           '_last': order[n]}
                    bands.append(cur)
            else:
                cur = None
        layers.append({'layer': ly, 'y': round(cy, 1), 'h': h, 'x0': round(shift, 1),
                       'x1': round(shift + x, 1)})
        y += h + LAYER_PAD
    for b in bands:
        del b['_last']

    for iid, it in items.items():
        it['x'], it['y'] = pos[iid]
    functions = {}
    for it in items.values():
        rs = [max(r_fn[m].values(), default=R_MIN) for m in it['members']]
        total = sum(2 * r + GAP for r in rs) - GAP
        x = it['x'] - total / 2
        for m, r in zip(it['members'], rs):
            functions[m] = {'item': it['id'], 'layer': it['layer'], 'r': r_fn[m],
                            'x': round(x + r, 1), 'y': it['y']}
            x += 2 * r + GAP

    routes = {}
    for (a, b), chain in chains.items():
        pts = [list(pos[n]) for n in chain]
        routes[f'{a}>{b}'] = pts
    return {'items': list(items.values()), 'functions': functions, 'bands': bands,
            'layers': layers, 'routes': routes, 'back': sorted([a, b] for a, b in back),
            'metrics': metrics,
            'width': round(max([l['x1'] - l['x0'] for l in layers] + [0]), 1), 'height': round(y, 1)}


# ---------------------------------------------------------------------------------------------
# Function level


def block_index(fn):
    starts = [b['start'] for b in fn['blocks']]
    ends = {b['start']: b['end'] for b in fn['blocks']}

    def of(pc):
        i = bisect.bisect_right(starts, pc) - 1
        if i >= 0 and pc < ends[starts[i]]:
            return starts[i]
        return None
    return of


def _hull(points):
    pts = sorted(set(points))
    if len(pts) <= 2:
        return pts

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def block_exits(fn):
    """start -> how the block ends: call, tail, table, ret, or None (falls/branches on)."""
    of = block_index(fn)
    ex = {}
    for c in fn['calls']:
        s = of(c['site'])
        if s is not None:
            ex[s] = 'tail' if c['kind'] == 'tail' else 'call'
    for jt in fn['jump_tables']:
        s = of(jt['site'])
        if s is not None:
            ex[s] = 'table'
    for b in fn['blocks']:
        if b['start'] not in ex and not b['succ']:
            ex[b['start']] = 'ret'
    return ex


def leaf_paths(fn, exits):
    """Per proof cut: each leaf's block path, matched to an enumerated path by (exit, end, steps).

    A path runs from the cut's block until the next cut block ('at'), a call block ('call'), a
    block without successors ('ret'), or a jump-table block ('jumpInd'). `approx` marks a leaf
    whose (exit, end, steps) matched no enumerated path; its path is then the shortest one with
    the same exit and end, or the cut block alone.
    """
    blocks = {b['start']: b for b in fn['blocks']}
    # The proof plan's cuts end a leaf; they may differ from the static map's cut points.
    cut_set = {c['pc'] for c in fn.get('vc_cuts') or []} or {c['pc'] for c in fn['cuts']}
    call_target = {}
    of = block_index(fn)
    for c in fn['calls']:
        s = of(c['site'])
        if s is not None:
            call_target[s] = c['targets']
    # A plan cut inside a block ends a path there (instructions counted as 4 bytes each: the
    # executor supports no compressed forms).
    inner = defaultdict(list)
    for pc in cut_set:
        s = of(pc)
        if s is not None and s != pc:
            inner[s].append(pc)
    out = {}
    for vc in fn.get('vc_cuts') or []:
        start = of(vc['pc'])
        if start is None:
            continue
        paths = []          # (exit, end, steps, [blocks])
        stack = [(start, [start], -((vc['pc'] - start) // 4))]
        truncated = False
        while stack:
            n, path, steps = stack.pop()
            b = blocks[n]
            stop = [pc for pc in inner.get(n, ()) if pc > vc['pc'] or n != start]
            if stop:
                pc = min(stop)
                paths.append(('at', pc, steps + (pc - n) // 4, path))
                continue
            steps += b['n']
            ex = exits.get(n)
            if ex in ('call', 'tail'):
                paths.append(('call', call_target.get(n, []), steps, path))
            elif ex == 'table':
                paths.append(('jumpInd', None, steps, path))
            elif ex == 'ret' or not b['succ']:
                paths.append(('ret', None, steps, path))
            else:
                for m in b['succ']:
                    if m in cut_set or m not in blocks:
                        paths.append(('at', m, steps, path + [m] if m in blocks else path))
                    elif m not in path:
                        stack.append((m, path + [m], steps))
            if len(paths) > LEAF_CAP:
                truncated = True
                break
        used = set()
        rows = []
        for leaf in vc['leaves']:
            want_end = leaf.get('target')
            exit_ = leaf.get('exit')

            def calls_target(p):
                return p[0] == 'call' and (want_end is None or f'f_{want_end:08x}' in p[1])

            def fits(p):
                if exit_ == 'at' and want_end is not None and of(want_end) is None:
                    return calls_target(p)      # a cut outside this function: the callee entry
                if p[0] != exit_:
                    return False
                if exit_ == 'at':
                    return p[1] == want_end
                if exit_ == 'call':
                    return calls_target(p)
                return True
            cand = [i for i, p in enumerate(paths) if fits(p)]
            exact = [i for i in cand if paths[i][2] == leaf.get('steps') and i not in used]
            if exact:
                i, approx = exact[0], False
            elif cand:
                i, approx = min(cand, key=lambda i: (len(paths[i][3]), i)), True
            else:
                i, approx = None, True
            if i is not None:
                used.add(i)
            rows.append({'i': leaf.get('i'), 'state': leaf.get('state', 'open'),
                         'exit': exit_, 'target': want_end, 'steps': leaf.get('steps'),
                         'residual': leaf.get('residual'), 'thm': leaf.get('thm'),
                         'blocks': paths[i][3] if i is not None else [start],
                         'approx': approx or truncated})
        out[vc['pc']] = {'cut_lemma': vc.get('cut_lemma', 'open'), 'residual': vc.get('residual'),
                         'leaves': rows}
    return out


def function(fn, fn_names=None):
    """Pixel layout of one function's control-flow graph with stubs, routes, hulls, leaf paths."""
    fn_names = fn_names or {}
    blocks = fn['blocks']
    box = {}
    for b in blocks:
        x, y = b['x'] * PX, b['y'] * PY
        box[b['start']] = (x, y)
    ncol = max([b['x'] for b in blocks] + [0]) + 1
    nrow = max([b['y'] for b in blocks] + [0]) + 1
    grid_w = ncol * PX - (PX - BW)
    grid_h = nrow * PY - (PY - BH)
    col = {b['start']: b['x'] for b in blocks}
    row = {b['start']: b['y'] for b in blocks}
    chan = (PX - BW) / 2       # half width of a vertical channel
    hchan = (PY - BH) / 2      # half height of a horizontal channel

    def cx(s):
        return box[s][0] + BW / 2

    def below(r):              # y of the horizontal channel below row r
        return r * PY + BH + hchan

    def vchan(c, right=True):  # x of the vertical channel right (or left) of column c
        return c * PX + BW + chan if right else c * PX - chan

    # Loop nesting.
    loops = fn['loops']
    bodies = {l['head']: set(l['body']) for l in loops}
    depth = {h: sum(1 for g in bodies if g != h and h in bodies[g] and bodies[h] <= bodies[g])
             for h in bodies}
    height = {h: max([depth[g] - depth[h] for g in bodies if g != h and g in bodies[h]] + [0])
              for h in bodies}

    def jitter(i, span):
        return ((i * 7) % 5 - 2) * span / 5

    edges = []
    for i, e in enumerate(fn['edges']):
        a, b = e['from'], e['to']
        if a not in box or b not in box:
            continue
        ax, ay = box[a]
        bx, by = box[b]
        if e['kind'] == 'back':
            d = depth.get(b, 0)
            lane = -12 - 9 * d
            pts = [[cx(a) - 20, ay + BH], [cx(a) - 20, below(row[a]) + jitter(i, hchan)],
                   [lane, below(row[a]) + jitter(i, hchan)], [lane, by - hchan - CUT_H],
                   [bx + 10, by - hchan - CUT_H], [bx + 10, by - CUT_H]]
        else:
            ra, rb = row[a], row[b]
            j = jitter(i, chan)
            yj = jitter(i + 3, hchan)
            if rb == ra + 1:
                pts = [[cx(a), ay + BH], [cx(a), below(ra) + yj], [cx(b), below(ra) + yj],
                       [cx(b), by]]
            else:
                right = col[b] >= col[a]
                vx = vchan(col[a], right) + j
                pts = [[cx(a), ay + BH], [cx(a), below(ra) + yj], [vx, below(ra) + yj],
                       [vx, below(rb - 1) + yj], [cx(b), below(rb - 1) + yj], [cx(b), by]]
        edges.append({'from': a, 'to': b, 'kind': e['kind'], 'pts': [[round(p, 1) for p in q]
                                                                        for q in pts]})

    hulls = []
    for h in sorted(bodies, key=lambda h: depth[h]):
        pad = 5 + 7 * height[h]
        pts = []
        for s in bodies[h]:
            if s in box:
                x, y = box[s]
                pts += [(x - pad, y - pad - CUT_H), (x + BW + pad, y - pad - CUT_H),
                        (x - pad, y + BH + pad), (x + BW + pad, y + BH + pad)]
        hulls.append({'head': h, 'depth': depth[h], 'n': len(bodies[h]),
                      'pts': [[round(x, 1), round(y, 1)] for x, y in _hull(pts)]})

    exits = block_exits(fn)
    of = block_index(fn)

    # Stub rows: callers above, callees below (ordered by mean x of their call sites).
    callers = list(fn.get('callers') or [])
    site_x = defaultdict(list)
    call_rows = []
    for k, c in enumerate(fn['calls']):
        s = of(c['site'])
        if s is None:
            continue
        if c['kind'] == 'indirect' and (len(c['targets']) != 1):
            key = f'ind:{c["site"]:x}'
        else:
            key = c['targets'][0] if c['targets'] else f'ind:{c["site"]:x}'
        site_x[key].append(cx(s))
        call_rows.append((k, c, s, key))
    stub_keys = sorted(site_x, key=lambda k: (sum(site_x[k]) / len(site_x[k]), str(k)))
    exit_y = grid_h + 34
    callee_y = exit_y + 60 + 6 * min(len(call_rows), 24)
    total = len(stub_keys) * (STUB_W + STUB_GAP) - STUB_GAP
    x0 = max(0.0, (grid_w - total) / 2)
    callee_stubs = {}
    for i, k in enumerate(stub_keys):
        if str(k).startswith('ind:'):
            site = int(str(k)[4:], 16)
            c = next(c for c in fn['calls'] if c['site'] == site)
            label = f'indirect {c["resolution"]} ({len(c["targets"])} targets)'
            targets = c['targets']
        else:
            label = fn_names.get(k, k)
            targets = [k]
        callee_stubs[k] = {'key': str(k), 'label': label, 'targets': targets,
                           'x': round(x0 + i * (STUB_W + STUB_GAP), 1), 'y': round(callee_y, 1),
                           'w': STUB_W, 'h': STUB_H}
    caller_y = -110.0
    total = len(callers) * (STUB_W + STUB_GAP) - STUB_GAP
    x0 = max(0.0, (grid_w - total) / 2)
    caller_stubs = [{'key': c, 'label': fn_names.get(c, c), 'x': round(x0 + i * (STUB_W + STUB_GAP), 1),
                     'y': caller_y, 'w': STUB_W, 'h': STUB_H} for i, c in enumerate(callers)]

    calls = []
    for n, (k, c, s, key) in enumerate(call_rows):
        st = callee_stubs[key]
        sx, sy = box[s]
        lane_y = grid_h + 50 + 6 * (n % 24)
        vx = vchan(col[s], True) + jitter(n, chan) * 0.6
        tx = st['x'] + 12 + (n * 11) % (STUB_W - 24)
        call_pts = [[sx + BW, sy + BH / 2], [vx, sy + BH / 2], [vx, lane_y], [tx, lane_y],
                    [tx, st['y']]]
        ret_pts = None
        noreturn = bool(c.get('noreturn'))
        if c['kind'] != 'tail' and not noreturn and c['ret'] in box:
            r = c['ret']
            rx, ry = box[r]
            rvx = vchan(col[r], True) - jitter(n, chan) * 0.6 - 3
            ret_pts = [[tx + 6, st['y']], [tx + 6, lane_y + 3], [rvx, lane_y + 3],
                       [rvx, ry - hchan - CUT_H + 4], [rx + BW - 14, ry - hchan - CUT_H + 4],
                       [rx + BW - 14, ry - CUT_H]]
        calls.append({'n': n + 1, 'site': c['site'], 'ret': c['ret'], 'block': s, 'kind': c['kind'],
                      'resolution': c['resolution'], 'targets': c['targets'], 'stub': str(key),
                      'noreturn': noreturn,
                      # The return address lies outside the function (its last instruction is
                      # the call): no return site to draw a return edge to.
                      'no_return_site': c['kind'] != 'tail' and c['ret'] not in box,
                      'call': [[round(p, 1) for p in q] for q in call_pts],
                      'return': [[round(p, 1) for p in q] for q in ret_pts] if ret_pts else None})

    drains = []
    for s, ex in sorted(exits.items()):
        if ex == 'ret' and s in box:
            x, y = box[s]
            vx = vchan(col[s], False) + 4
            drains.append({'block': s, 'pts': [[round(cx(s) + 20, 1), y + BH],
                                              [round(cx(s) + 20, 1), round(below(row[s]) - 4, 1)],
                                              [round(vx, 1), round(below(row[s]) - 4, 1)],
                                              [round(vx, 1), exit_y]]})
    exit_bar = {'x0': -30.0, 'x1': round(grid_w + 30, 1), 'y': exit_y,
                'link': [[round(grid_w + 30, 1), exit_y], [round(grid_w + 60, 1), exit_y],
                         [round(grid_w + 60, 1), caller_y + STUB_H / 2],
                         [round(max([s['x'] + s['w'] for s in caller_stubs] + [grid_w]) + 4, 1),
                          caller_y + STUB_H / 2]] if caller_stubs else None}

    out_blocks = [{'start': b['start'], 'x': box[b['start']][0], 'y': box[b['start']][1],
                   'w': BW, 'h': BH, 'exit': exits.get(b['start'])} for b in blocks]
    xs = [p[0] for e in edges for p in e['pts']] + [-12 - 9 * (max(depth.values(), default=0) + 1)]
    return {'blocks': out_blocks, 'edges': edges, 'hulls': hulls, 'calls': calls,
            'callee_stubs': list(callee_stubs.values()), 'caller_stubs': caller_stubs,
            'drains': drains, 'exit_bar': exit_bar, 'loop_depth': depth,
            'leaf_paths': leaf_paths(fn, exits),
            'bounds': [round(min(xs + [-40]) - 20, 1), caller_y - 20,
                       round(max([grid_w + 80] + [s['x'] + s['w'] for s in callee_stubs.values()]
                                 + [s['x'] + s['w'] for s in caller_stubs]) + 20, 1),
                       round(callee_y + STUB_H + 20, 1)]}


# ---------------------------------------------------------------------------------------------
# Source view (S9.4)

def first_line(edge):
    """The source line of an edge's first call site (sites carry [file, line, ...]); None if none."""
    lines = [s[1] for s in edge['sites'] if s[1] is not None]
    return min(lines) if lines else None


def neighbourhood(functions, edges):
    """Display order of each source function's depth-one neighbourhood (the offline layout of the
    source view): for every function, the indices of its incoming and outgoing edges in the order
    their call sites appear in the source, top to bottom (an edge's first call-site line; edges
    without a line last), ties by the other end's name. The page places the i-th caller and the
    i-th callee on row i; self edges are left out."""
    ins, outs = defaultdict(list), defaultdict(list)
    for i, e in enumerate(edges):
        if e['from'] != e['to']:
            outs[e['from']].append(i)
            ins[e['to']].append(i)

    def key(i, other):
        line = first_line(edges[i])
        return line is None, line or 0, functions[other]['name'], other
    return [{'in': sorted(ins[f['id']], key=lambda i: key(i, edges[i]['from'])),
             'out': sorted(outs[f['id']], key=lambda i: key(i, edges[i]['to']))} for f in functions]
