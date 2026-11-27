#!/usr/bin/env python3
"""Count the registers read on the path of one `addi` step of a generated Sail Lean tree.

Usage: reach.py <tree>/LeanRV64DExecutable [--root try_step] [--via execute_ITYPE] [--list]

Walks definition bodies textually: every identifier in a body that names a definition of the
tree is a callee. `execute_*` definitions other than `--via` are not entered, so the walk follows
fetch, decode, the `addi` execute clause and the step postlude (including its trap paths).
Prints the number of reachable definitions, the number of distinct registers named by
`readReg <reg>` in them, and with `--list` the registers.
"""
import argparse
import pathlib
import re
import sys

DEF = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                 r"(?:partial\s+)?(?:def|abbrev|instance)\s+([A-Za-z_][\w'.]*)", re.M)
TOP = re.compile(r"^(?:@\[|private |protected |noncomputable |partial |def |abbrev |instance |"
                 r"theorem |structure |inductive |namespace |end |section |open |/--|mutual|"
                 r"termination_by|decreasing_by)", re.M)
IDENT = re.compile(r"[A-Za-z_][\w']*")
READ = re.compile(r"\breadReg\s+([A-Za-z_][\w']*)")


def load(tree: pathlib.Path) -> dict[str, str]:
    bodies: dict[str, str] = {}
    for f in sorted(tree.rglob("*.lean")):
        text = f.read_text()
        starts = [m for m in DEF.finditer(text)]
        for m in starts:
            name = m.group(1).split(".")[-1]
            rest = text[m.end():]
            nxt = TOP.search(rest, 1)
            body = rest[: nxt.start()] if nxt else rest
            bodies[name] = bodies.get(name, "") + "\n" + body
    return bodies


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("tree", type=pathlib.Path)
    ap.add_argument("--root", default="try_step")
    ap.add_argument("--via", default="execute_ITYPE")
    ap.add_argument("--list", action="store_true")
    args = ap.parse_args()

    bodies = load(args.tree)
    if args.root not in bodies:
        print(f"no definition {args.root}", file=sys.stderr)
        return 1
    seen: set[str] = set()
    work = [args.root]
    while work:
        name = work.pop()
        if name in seen:
            continue
        seen.add(name)
        for ident in IDENT.findall(bodies[name]):
            if ident in bodies and ident not in seen:
                if ident.startswith("execute_") and ident != args.via:
                    continue
                work.append(ident)
    regs = sorted({r for n in seen for r in READ.findall(bodies[n])})
    print(f"definitions {len(seen)} registers {len(regs)}")
    if args.list:
        print(" ".join(regs))
    return 0


if __name__ == "__main__":
    sys.exit(main())
