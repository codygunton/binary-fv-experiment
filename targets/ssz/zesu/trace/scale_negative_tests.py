#!/usr/bin/env python3
"""Row C: negative tests for the SCALED checks, against the real captured evidence.

The two checks added after the third review round are the ones a weak predicate would have let through:

  * `derivedBindingsHold` — a loop-`derived` binding row's relation `value = index * stride + constant`,
    with `index * stride` in the loop register;
  * `allocationLedger` — the observed cursor-write history IS the allocation sequence the fixture
    requires (count, order, sizes, alignments, returned blocks).

A check that cannot fail is not a check, so this takes the REAL evidence `scale_occurrences.py` just
captured and corrupts copies of it, requiring each corruption to flip the responsible oracle predicate.
The Lean checker carries the same mutations as `negative_derived_*` / `negative_ledger_*` theorems over
the same evidence shape, so both sides reject the same corrupted evidence.

The production ELF is never modified; only in-memory copies of the reduced evidence are.
"""
from __future__ import annotations

import argparse
import copy
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import scale_occurrences as so  # noqa: E402


def derived_mutations(row):
    """Each corruption of a loop-derived row, and why it must not survive."""
    def m(**kw):
        return {**copy.deepcopy(row), **kw}
    return [
        ("wrong-stride", m(stride=row["stride"] - 1)),
        ("wrong-constant", m(constant=row["constant"] + 4)),
        ("wrong-register-value", m(registerValues=[v + 1 for v in row["registerValues"]])),
        ("wrong-index", m(registerValues=[v + row["stride"] for v in row["registerValues"]])),
        ("no-sample", m(registerValues=[], values=[])),
        ("unreadable-register", m(values=row["values"][:-1])),
    ]


def ledger_mutations(led):
    """Each corruption of a whole-run allocation ledger, and why it must not survive."""
    obs, exp = led["observed"], led["expected"]
    last = obs[-1]

    def m(observed=None, expected=None):
        return {**copy.deepcopy(led),
                "observed": copy.deepcopy(observed if observed is not None else obs),
                "expected": copy.deepcopy(expected if expected is not None else exp)}

    def bump(items, ordinal, **kw):
        return [{**x, **kw} if x["ordinal"] == ordinal else x for x in items]

    pad = next((e["ordinal"] for o, e in zip(obs, exp)
                if so.al.align_up(o["before"], e["alignment"]) != o["before"]), exp[0]["ordinal"])
    return [
        ("extra-event", m(observed=obs + [{"ordinal": len(obs), "before": last["after"],
                                           "after": last["after"] + 32,
                                           "returned": last["after"]}])),
        ("missing-event", m(observed=obs[:-1])),
        ("reordered-events", m(observed=obs[1:] + obs[:1])),
        ("wrong-size", m(expected=bump(exp, exp[0]["ordinal"], size=exp[0]["size"] + 8))),
        # Alignment is observable exactly where it produced padding; if this arm never needed any, the
        # mutation is applied to the first event anyway and caught by the size prediction.
        ("wrong-alignment", m(expected=bump(exp, pad, alignment=1 if pad != exp[0]["ordinal"] else 64))),
        ("wrong-returned-block", m(observed=bump(obs, obs[0]["ordinal"],
                                                 returned=obs[0]["before"] + 8))),
    ]


def occurrence_ledger_mutations(rec):
    """Corruptions of ONE occurrence's slice — the per-occurrence check must be discriminating too."""
    f = rec["facts"]
    obs, exp = f["ledgerObserved"], f["ledgerExpected"]
    return [
        ("occ-wrong-size", obs, [{**e, "size": e["size"] + 8} for e in exp]),
        ("occ-wrong-alignment", obs, [{**e, "alignment": e["alignment"] * 8 + 1} for e in exp]),
        ("occ-unexpected-event", obs, []),
        ("occ-missing-event", [], exp),
        ("occ-wrong-returned-block", [{**o, "returned": o["before"] + 8} for o in obs], exp),
    ]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--coverage", required=True, help="coverage.json emitted by scale_occurrences.py")
    a = ap.parse_args()
    data = json.loads(Path(a.coverage).read_text())
    failures, checked = [], 0

    # --- baseline: the real evidence passes ------------------------------------------------------
    derived_rows = [(r["index"], d) for r in data["occurrences"]
                    for d in (r["facts"].get("derivedRows") or [])]
    if len(derived_rows) != 8:
        failures.append(f"expected 8 loop-derived rows in the evidence, found {len(derived_rows)}")
    for idx, d in derived_rows:
        if not so.derived_row_holds(d):
            failures.append(f"occ {idx}: the real derived row does not hold")

    ledgers = data["summary"]["armLedgers"]
    for name, led in sorted(ledgers.items()):
        if not so.arm_ledger_holds(led):
            failures.append(f"arm {name}: the real whole-run ledger does not agree")

    allocating = [r for r in data["occurrences"]
                  if r["facts"].get("allocates") and r["facts"].get("covered")]
    for r in allocating:
        if not so.ledger_agrees(r["facts"]["ledgerObserved"], r["facts"]["ledgerExpected"]):
            failures.append(f"occ {r['index']}: the real occurrence ledger does not agree")

    # --- mutations: every corruption must be caught ----------------------------------------------
    for idx, d in derived_rows:
        for label, mutated in derived_mutations(d):
            checked += 1
            if so.derived_row_holds(mutated):
                failures.append(f"occ {idx}: derived mutation '{label}' NOT caught")

    for name, led in sorted(ledgers.items()):
        for label, mutated in ledger_mutations(led):
            checked += 1
            if so.arm_ledger_holds(mutated):
                failures.append(f"arm {name}: ledger mutation '{label}' NOT caught")

    for r in allocating:
        for label, obs, exp in occurrence_ledger_mutations(r):
            checked += 1
            if so.ledger_agrees(obs, exp):
                failures.append(f"occ {r['index']}: ledger mutation '{label}' NOT caught")

    if failures:
        print(f"SCALED NEGATIVE TESTS FAILED ({len(failures)}):", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        return 1
    print(f"scaled negative tests OK: {len(derived_rows)} loop-derived rows and "
          f"{len(ledgers)} arm ledgers + {len(allocating)} occurrence ledgers hold on the real "
          f"evidence; all {checked} corruptions caught (stride / constant / register value / index / "
          f"empty sample; extra / missing / reordered event, wrong size, wrong alignment, wrong "
          f"returned block)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
