"""zmap: static map of the Zesu ELF, merged proof map, work queue, page, effort ledger, cost,
metrics.

Run from `P/tools`: `python3 -m zmap <command> ...` (build, merge, queue, show, next, site,
ledger start/stop, cost backfill/agents, metrics, brief, check, costmodel).
"""
import argparse
import json
import os
import sys

from . import analyze, cost, costmodel, elfread, ledger, merge, metrics, site, workqueue

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

    merge.register(sub, PACKAGE, load, dump)

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

    site.register(sub, PACKAGE, UI)

    ledger.register(sub, DEFAULT_LEDGER)
    cost.register(sub, PACKAGE)
    metrics.register(sub, PACKAGE, load)
    costmodel.register(sub, PACKAGE, load)

    args = p.parse_args(argv)
    args.func(args)


if __name__ == '__main__':
    main()
