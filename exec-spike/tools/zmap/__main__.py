"""zmap: static map of the Zesu ELF, merged proof map, work queue, page, effort ledger.

Run from `P/tools`: `python3 -m zmap <command> ...` (build, merge, queue, show, next, site,
ledger log).
"""
import argparse
import json
import os
import shutil
import sys

from . import analyze, elfread, ledger, merge, workqueue

PACKAGE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DEFAULT_LEDGER = os.path.join(PACKAGE, 'map', 'ledger.jsonl')
DEFAULT_MAP = os.path.join(PACKAGE, 'map', 'map.json')
DEFAULT_QUEUE = os.path.join(PACKAGE, 'map', 'queue.json')
UI = os.path.join(os.path.dirname(PACKAGE), 'tools', 'binary-regions-ui')


def load(path):
    with open(path) as f:
        return json.load(f)


def dump(obj, path, compact=True):
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    with open(path, 'w') as f:
        if compact:
            json.dump(obj, f, separators=(',', ':'))
        else:
            json.dump(obj, f, indent=1)
        f.write('\n')


def cmd_build(args):
    digest = elfread.sha256(args.elf)
    if digest != args.sha256.lower():
        sys.exit(f'zmap: {args.elf} has sha256 {digest}, expected {args.sha256}')
    static = analyze.build(args.elf, join_cuts=args.join_cuts)
    static['elf_sha256'] = digest
    static['join_cuts'] = args.join_cuts
    try:
        from . import hints
        static['hints'] = hints.attach(static, args.elf, args.debug_object)
        static['hints_error'] = None
    except Exception as e:  # the helper rejects the object: emit the map without hints
        for fn in static['functions']:
            for b in fn['blocks']:
                b['src'] = None
        static['hints'] = None
        static['hints_error'] = f'{type(e).__name__}: {e}'
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, 'w') as f:
        json.dump(static, f, separators=(',', ':'))
        f.write('\n')
    fns = static['functions']
    print(f'zmap: {len(fns)} functions, {sum(fn["n_instr"] for fn in fns)} instructions, '
          f'{sum(fn["set"] == "target" for fn in fns)} in target, '
          f'hints: {"error: " + static["hints_error"] if static["hints_error"] else "ok"} '
          f'-> {args.out}')


def cmd_merge(args):
    static = load(args.static)
    status = load(args.status)
    if status.get('schema') != 'zmap.status.v1':
        sys.exit(f'zmap: {args.status} is not zmap.status.v1')
    reviews = load(args.reviews) if args.reviews else {}
    rows = merge.read_ledger(args.ledger)
    out = merge.merge(static, status, reviews, rows, status_source=status.get('source', args.status))
    dump(out, args.out)
    print('zmap: ' + ', '.join(f'{k} {v}' for k, v in out['state_counts'].items() if v)
          + f' -> {args.out}')


def cmd_queue(args):
    items = workqueue.build_queue(load(args.map))
    dump(items, args.json, compact=False)
    with open(args.out, 'w') as f:
        f.write(workqueue.queue_markdown(items) + '\n')
    print(f'zmap: {len(items)} queue items -> {args.out}, {args.json}')


def cmd_show(args):
    m = load(args.map)
    try:
        f = workqueue.find(m, args.fn)
    except KeyError as e:
        sys.exit(f'zmap: no function {e}')
    print(workqueue.card(m, f))


def cmd_next(args):
    for it in load(args.queue)[:args.n]:
        print(f'{it["rank"]:4d}. {workqueue.describe(it)}')


def cmd_site(args):
    m = load(args.map)
    queue = load(args.queue) if os.path.exists(args.queue) else []
    os.makedirs(os.path.join(args.out, 'vendor'), exist_ok=True)
    shutil.copy(os.path.join(args.ui, 'map.html'), os.path.join(args.out, 'map.html'))
    shutil.copy(os.path.join(args.ui, 'vendor', 'd3.min.js'),
                os.path.join(args.out, 'vendor', 'd3.min.js'))
    with open(os.path.join(args.out, 'map-data.js'), 'w') as f:
        f.write('window.ZMAP = ')
        json.dump(m, f, separators=(',', ':'))
        f.write(';\nwindow.ZQUEUE = ')
        json.dump(queue, f, separators=(',', ':'))
        f.write(';\n')
    print(f'zmap: site -> {os.path.join(args.out, "map.html")}')


def cmd_ledger_log(args):
    row = ledger.log(args.ledger, args.fn, args.item, args.kind, args.agent, args.minutes,
                     args.outcome, usd=args.usd, requests=args.requests, note=args.note)
    print(json.dumps(row))


def main(argv=None):
    p = argparse.ArgumentParser(prog='zmap')
    sub = p.add_subparsers(dest='cmd', required=True)

    b = sub.add_parser('build', help='compute the static map')
    b.add_argument('--elf', required=True)
    b.add_argument('--sha256', required=True)
    b.add_argument('--debug-object', required=True)
    b.add_argument('--out', required=True)
    b.add_argument('--no-join-cuts', dest='join_cuts', action='store_false',
                   help='do not cut at the join cut candidates (fanin_paths >= 4); the default '
                        'cuts there (S5 probe 1 passed)')
    b.set_defaults(func=cmd_build)

    mg = sub.add_parser('merge', help='merge static map, status, reviews, ledger')
    mg.add_argument('--static', required=True)
    mg.add_argument('--status', required=True)
    mg.add_argument('--reviews')
    mg.add_argument('--ledger', default=DEFAULT_LEDGER)
    mg.add_argument('--out', required=True)
    mg.set_defaults(func=cmd_merge)

    q = sub.add_parser('queue', help='work queue')
    q.add_argument('--map', default=DEFAULT_MAP)
    q.add_argument('--out', required=True, help='QUEUE.md')
    q.add_argument('--json', required=True, help='queue.json')
    q.set_defaults(func=cmd_queue)

    sh = sub.add_parser('show', help='print a function card')
    sh.add_argument('fn', help='id, name, status id, or address')
    sh.add_argument('--map', default=DEFAULT_MAP)
    sh.set_defaults(func=cmd_show)

    nx = sub.add_parser('next', help='first queue items')
    nx.add_argument('-n', type=int, default=10)
    nx.add_argument('--queue', default=DEFAULT_QUEUE)
    nx.set_defaults(func=cmd_next)

    st = sub.add_parser('site', help='write the page (map.html, map-data.js)')
    st.add_argument('--map', default=DEFAULT_MAP)
    st.add_argument('--queue', default=DEFAULT_QUEUE)
    st.add_argument('--ui', default=UI, help='directory with map.html and vendor/d3.min.js')
    st.add_argument('--out', required=True)
    st.set_defaults(func=cmd_site)

    lg = sub.add_parser('ledger', help='effort ledger')
    lsub = lg.add_subparsers(dest='ledger_cmd', required=True)
    log = lsub.add_parser('log', help='append one work item')
    log.add_argument('--fn', required=True, help='function id, or - for none')
    log.add_argument('--item', required=True)
    log.add_argument('--kind', required=True, choices=ledger.KINDS)
    log.add_argument('--agent', required=True)
    log.add_argument('--minutes', required=True, type=float)
    log.add_argument('--usd', type=float)
    log.add_argument('--requests', type=int)
    log.add_argument('--outcome', required=True, choices=ledger.OUTCOMES)
    log.add_argument('--note')
    log.add_argument('--ledger', default=DEFAULT_LEDGER)
    log.set_defaults(func=cmd_ledger_log)

    def cmd_costmodel(args):
        from . import costmodel
        with open(args.out, 'w') as f:
            f.write(costmodel.render(load(args.map), merge.read_ledger(args.ledger)))
        print(f'zmap: cost model -> {args.out}')
    cm = sub.add_parser('costmodel', help='cost model (COSTMODEL.md) from map and ledger')
    cm.add_argument('--map', default=DEFAULT_MAP)
    cm.add_argument('--ledger', default=DEFAULT_LEDGER)
    cm.add_argument('--out', required=True)
    cm.set_defaults(func=cmd_costmodel)

    args = p.parse_args(argv)
    args.func(args)


if __name__ == '__main__':
    main()
