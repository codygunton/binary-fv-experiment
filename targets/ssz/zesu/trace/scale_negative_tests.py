#!/usr/bin/env python3
"""Row C: negative tests for the SCALED checks, against the real captured evidence.

The checks a weak predicate would have let through:

  * `derivedBindingsHold` — a loop-`derived` binding row's relation `value = index * stride + constant`,
    with `index * stride` in the loop register;
  * `allocationLedger` — the observed cursor-write history IS the allocation sequence the fixture
    requires (count, order, sizes, alignments, returned blocks);
  * `exitsRespected` — `exits` agrees with the run at every observed transfer OUT of the regions.
    This one was narrowed after the extractor stopped counting every resolved call site as an exit of
    its caller, so it is tested in BOTH directions: an undeclared departure must fail, and so must a
    call site the trace saw come back being declared an exit. Only the second catches a relapse to
    the over-declaration, and a version of this check without it would have passed unchanged.

A check that cannot fail is not a check, so this takes the REAL evidence `scale_function_instances.py` just
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

import scale_function_instances as so  # noqa: E402


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


def function_instance_ledger_mutations(rec):
    """Corruptions of ONE function instance's slice — the per-function-instance check must be discriminating too."""
    f = rec["facts"]
    obs, exp = f["ledgerObserved"], f["ledgerExpected"]
    return [
        ("function instance-wrong-size", obs, [{**e, "size": e["size"] + 8} for e in exp]),
        ("function instance-wrong-alignment", obs, [{**e, "alignment": e["alignment"] * 8 + 1} for e in exp]),
        ("function instance-unexpected-event", obs, []),
        ("function instance-missing-event", [], exp),
        ("function instance-wrong-returned-block", [{**o, "returned": o["before"] + 8} for o in obs], exp),
    ]


def exit_mutations(f):
    """Corruptions of ONE function instance's exit evidence, each of which `exitsRespected` must reject.

    `exit_agreement` is re-run on every mutated copy, so a mutation of `exits` really does move the
    residues the oracle reads — otherwise these would test nothing."""
    def m(**kw):
        return so.exit_agreement({**copy.deepcopy(f), **kw})
    out = [("undeclared-departure", m(leavingSources=[999999] + (f.get("leavingSources") or []))),
           ("undeclared-dynamic-transfer",
            m(dynamicTransferSources=[999999] + (f.get("dynamicTransferSources") or [])))]
    if f.get("leavingSources"):
        # the departure is real; the declaration for it is gone
        dropped = f["leavingSources"][0]
        out.append(("declared-exit-removed",
                    m(exits=[x for x in f["exits"] if x != dropped])))
    if f.get("returningCallSites"):
        # the relapse: a call site the trace observed coming back, declared an exit anyway
        out.append(("returning-call-declared-exit",
                    m(exits=[f["returningCallSites"][0]] + f["exits"])))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--coverage", required=True, help="coverage.json emitted by scale_function_instances.py")
    a = ap.parse_args()
    data = json.loads(Path(a.coverage).read_text())
    failures, checked = [], 0

    # --- baseline: the real evidence passes ------------------------------------------------------
    derived_rows = [(r["index"], d) for r in data["function_instances"]
                    for d in (r["facts"].get("derivedRows") or [])]
    if len(derived_rows) != 8:
        failures.append(f"expected 8 loop-derived rows in the evidence, found {len(derived_rows)}")
    for idx, d in derived_rows:
        if not so.derived_row_holds(d):
            failures.append(f"function instance {idx}: the real derived row does not hold")

    ledgers = data["summary"]["armLedgers"]
    for name, led in sorted(ledgers.items()):
        if not so.arm_ledger_holds(led):
            failures.append(f"arm {name}: the real whole-run ledger does not agree")

    allocating = [r for r in data["function_instances"]
                  if r["facts"].get("allocates") and r["facts"].get("covered")]
    for r in allocating:
        if not so.ledger_agrees(r["facts"]["ledgerObserved"], r["facts"]["ledgerExpected"]):
            failures.append(f"function instance {r['index']}: the real function instance ledger does not agree")

    covered = [r for r in data["function_instances"] if r["facts"].get("covered")]
    with_calls = [r for r in covered if r["facts"].get("returningCallSites")]
    for r in covered:
        if so.evaluate_facts(so.exit_agreement(copy.deepcopy(r["facts"])))[0]["exitsRespected"] is not True:
            failures.append(f"function instance {r['index']}: the real exit evidence does not agree")
    if not with_calls:
        # Without one, the over-declaration direction is never exercised and the relapse it guards
        # against would go untested — that is a failure of this suite, not an absence of obligation.
        failures.append("no covered function instance carries a returning call site to mutate")

    # --- mutations: every corruption must be caught ----------------------------------------------
    for idx, d in derived_rows:
        for label, mutated in derived_mutations(d):
            checked += 1
            if so.derived_row_holds(mutated):
                failures.append(f"function instance {idx}: derived mutation '{label}' NOT caught")

    for name, led in sorted(ledgers.items()):
        for label, mutated in ledger_mutations(led):
            checked += 1
            if so.arm_ledger_holds(mutated):
                failures.append(f"arm {name}: ledger mutation '{label}' NOT caught")

    for r in allocating:
        for label, obs, exp in function_instance_ledger_mutations(r):
            checked += 1
            if so.ledger_agrees(obs, exp):
                failures.append(f"function instance {r['index']}: ledger mutation '{label}' NOT caught")

    over_declared_checked = 0
    for r in covered:
        for label, mutated in exit_mutations(r["facts"]):
            checked += 1
            over_declared_checked += (label == "returning-call-declared-exit")
            if so.evaluate_facts(mutated)[0]["exitsRespected"] is not False:
                failures.append(f"function instance {r['index']}: exit mutation '{label}' NOT caught")

    if failures:
        print(f"SCALED NEGATIVE TESTS FAILED ({len(failures)}):", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        return 1
    print(f"scaled negative tests OK: {len(derived_rows)} loop-derived rows and "
          f"{len(ledgers)} arm ledgers + {len(allocating)} function instance ledgers hold on the real "
          f"evidence; all {checked} corruptions caught (stride / constant / register value / index / "
          f"empty sample; extra / missing / reordered event, wrong size, wrong alignment, wrong "
          f"returned block; undeclared departure, undeclared dynamic transfer, removed exit, and "
          f"{over_declared_checked} returning call sites declared as exits over "
          f"{len(with_calls)} function instances)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
