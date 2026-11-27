"""zmap: static map of the Zesu ELF and the effort ledger.

Run from `P/tools`: `python3 -m zmap build ...`, `python3 -m zmap ledger log ...`.
"""
import argparse
import json
import os
import sys

from . import analyze, elfread, ledger

PACKAGE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DEFAULT_LEDGER = os.path.join(PACKAGE, 'map', 'ledger.jsonl')


def cmd_build(args):
    digest = elfread.sha256(args.elf)
    if digest != args.sha256.lower():
        sys.exit(f'zmap: {args.elf} has sha256 {digest}, expected {args.sha256}')
    static = analyze.build(args.elf)
    static['elf_sha256'] = digest
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
    b.set_defaults(func=cmd_build)

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

    args = p.parse_args(argv)
    args.func(args)


if __name__ == '__main__':
    main()
