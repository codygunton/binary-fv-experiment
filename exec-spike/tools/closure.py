#!/usr/bin/env python3
"""Copy the import closure (within BinaryFv/) of the S3 seed modules into exec-spike/bfv.

Usage: closure.py --src <W> --dst <W>/exec-spike/bfv

Imports of modules under BinaryFv.Zesu are removed from the copies and reported; files that
contain `native_decide` are reported so that the declarations using it can be removed by hand.
"""
import argparse
import pathlib
import re
import shutil
import sys

SEEDS = [
    "BinaryFv.RiscV.Step.TryStep",
    "BinaryFv.RiscV.Step.GenericRetire",
    "BinaryFv.RiscV.Step.FallThrough",
    "BinaryFv.RiscV.Step.ControlFlow",
    "BinaryFv.RiscV.Step.Call",
    "BinaryFv.RiscV.Step.Store",
    "BinaryFv.RiscV.Instruction.Decode",
    "BinaryFv.RiscV.Instruction.DecodeTactic",
    "BinaryFv.RiscV.Proof.ImageFetch",
    "BinaryFv.RiscV.Platform.Fetch",
    "BinaryFv.RiscV.Platform.NormalState",
    "BinaryFv.RiscV.Logic.LoadedImage",
    "BinaryFv.RiscV.Model.State",
    "BinaryFv.RiscV.Execution.Runner",
]
EXECUTE_DIR = "BinaryFv/RiscV/Instruction/Execute"
IMPORT = re.compile(r"^import\s+(\S+)\s*$")


def module_path(root: pathlib.Path, mod: str) -> pathlib.Path:
    return root / (mod.replace(".", "/") + ".lean")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", required=True, type=pathlib.Path)
    ap.add_argument("--dst", required=True, type=pathlib.Path)
    args = ap.parse_args()

    seeds = list(SEEDS)
    for f in sorted((args.src / EXECUTE_DIR).glob("*.lean")):
        seeds.append(".".join(f.relative_to(args.src).with_suffix("").parts))

    seen: set[str] = set()
    work = list(seeds)
    removed: list[tuple[str, str]] = []
    while work:
        mod = work.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = module_path(args.src, mod)
        if not path.exists():
            print(f"missing module {mod}", file=sys.stderr)
            return 1
        for line in path.read_text().splitlines():
            m = IMPORT.match(line)
            if not m:
                continue
            dep = m.group(1)
            if dep.startswith("BinaryFv.Zesu"):
                removed.append((mod, dep))
            elif dep.startswith("BinaryFv"):
                work.append(dep)

    native: list[str] = []
    for mod in sorted(seen):
        src = module_path(args.src, mod)
        dst = module_path(args.dst, mod)
        dst.parent.mkdir(parents=True, exist_ok=True)
        text = src.read_text()
        lines = [
            l for l in text.splitlines(keepends=True)
            if not (IMPORT.match(l) and IMPORT.match(l).group(1).startswith("BinaryFv.Zesu"))
        ]
        dst.write_text("".join(lines))
        if "native_decide" in text:
            native.append(mod)

    print(f"copied {len(seen)} modules")
    for mod, dep in removed:
        print(f"removed import {dep} from {mod}")
    for mod in native:
        print(f"native_decide in {mod}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
