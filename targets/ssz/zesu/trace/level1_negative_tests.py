#!/usr/bin/env python3
"""Mutation checks for every boolean Level 1 admission observation."""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path


def accepted(condition: dict) -> bool:
    structural = all(value is True for value in condition["structural"].values()
                     if isinstance(value, bool))
    production = all(value is True for value in condition["production"].values())
    source = condition["sourceMeaningPasses"] is True
    interface = condition["interfaceCompatible"] is True
    exact = condition["exactMachineMeaningChecked"] is True
    return structural and production and source and interface and exact


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--evidence", required=True)
    a = ap.parse_args()
    evidence = json.loads(Path(a.evidence).read_text())
    caught = 0
    for original in evidence["conditions"]:
        # Normalize a passing synthetic baseline. This tests that every currently measurable clause
        # participates in the eventual admission predicate, even when the real trace has an explicit
        # gap (a gap must not make mutations of other clauses vacuously "caught").
        baseline = copy.deepcopy(original)
        for key, value in baseline["structural"].items():
            if isinstance(value, bool):
                baseline["structural"][key] = True
        for key in baseline["production"]:
            baseline["production"][key] = True
        baseline["sourceMeaningPasses"] = True
        baseline["interfaceCompatible"] = True
        baseline["exactMachineMeaningChecked"] = True
        if not accepted(baseline):
            raise SystemExit(f"internal error: normalized baseline rejected for {original['condition']}")
        for key in baseline["production"]:
            mutant = copy.deepcopy(baseline)
            mutant["production"][key] = False
            if accepted(mutant):
                raise SystemExit(f"surviving production mutation: {original['condition']}.{key}")
            caught += 1
        for key, value in baseline["structural"].items():
            if value is True:
                mutant = copy.deepcopy(baseline)
                mutant["structural"][key] = False
                if accepted(mutant):
                    raise SystemExit(f"surviving structural mutation: {original['condition']}.{key}")
                caught += 1
        mutant = copy.deepcopy(baseline)
        mutant["sourceMeaningPasses"] = False
        if accepted(mutant):
            raise SystemExit(f"surviving source-meaning mutation: {original['condition']}")
        caught += 1
        mutant = copy.deepcopy(baseline)
        mutant["interfaceCompatible"] = False
        if accepted(mutant):
            raise SystemExit(f"surviving interface mutation: {original['condition']}")
        caught += 1
        mutant = copy.deepcopy(baseline)
        mutant["exactMachineMeaningChecked"] = False
        if accepted(mutant):
            raise SystemExit(f"surviving exact-machine-meaning mutation: {original['condition']}")
        caught += 1
    print(f"Level 1 admission mutations caught: {caught}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
