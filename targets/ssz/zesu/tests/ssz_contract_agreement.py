#!/usr/bin/env python3
"""Row B agreement harness for the `ssz-contract-corpus-v1` contract-validation corpus.

Runs the canonical-JSONL runners over one shared corpus and checks they agree, both with each other
and with the corpus's own accept/reject expectation. This is falsification/regression evidence — it
is never a proof input. The existing three-way `ssz-value-v1` differential (`ssz_differential_audit.py`)
is preserved as an independent top-level check and is not replaced by this.

Parties (each optional; at least one runner is required):
  * `--lean-runner`  : the `ssz_contract_runner` executable (over the pinned oracle)
  * `--zesu-probe`   : the host probe over the private `ssz_raw.decode` routine (emits the decision)

For every top-level `ssz_raw.decode` case:
  * every present runner's `outcome` (accept/reject) must equal the corpus `expect.accept`;
  * every pair of present runners must agree on `outcome`, and on the decoded `value` among the
    runners that emit one.

The `value` field is compared only among runners that produce it, not required of all. The Lean
oracle runner renders the full `ssz-value-v1` value; the host Zig probe deliberately emits only the
decision (its allocation behavior goes to a separate ledger) because `raw.decode`'s value fidelity is
already certified by the preserved three-way `ssz-value-v1` audit over the same fixtures — see the
probe's module doc and DECISIONS.md. The reject `error` label is each runner's own taxonomy (Zig has
three variants; the oracle six) and is therefore never required to match across runners.

The runner may need an unlimited stack for multi-megabyte cases; this harness raises it before exec.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import resource
import subprocess
import sys
from pathlib import Path


def _load(path: Path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _unlimited_stack() -> None:
    try:
        resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    except (ValueError, OSError):
        pass


def _run(binary: str, corpus_path: Path) -> dict[str, dict]:
    """id -> outcome object, from one runner over the corpus."""
    result = subprocess.run([binary, str(corpus_path)], capture_output=True, text=True,
                            preexec_fn=_unlimited_stack)
    if result.returncode != 0:
        raise SystemExit(f"runner {binary} exited {result.returncode}\n{result.stderr[:2000]}")
    out: dict[str, dict] = {}
    for line in result.stdout.splitlines():
        if line.strip():
            row = json.loads(line)
            out[row["id"]] = row
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus-generator", required=True, help="path to ssz_contract_corpus.py")
    ap.add_argument("--fixtures", required=True, help="path to ssz_differential_audit.py")
    ap.add_argument("--lean-runner", help="the ssz_contract_runner executable (over the oracle)")
    ap.add_argument("--zesu-probe", help="the host private-routine probe executable")
    ap.add_argument("--corpus-out", default="corpus.jsonl")
    a = ap.parse_args()
    if not a.lean_runner and not a.zesu_probe:
        raise SystemExit("at least one of --lean-runner / --zesu-probe is required")

    gen = _load(Path(a.corpus_generator))
    fixtures = _load(Path(a.fixtures))
    corpus_path = Path(a.corpus_out)
    rows = gen.corpus_rows(fixtures)
    corpus_path.write_text("".join(json.dumps(r, sort_keys=True, separators=(",", ":")) + "\n"
                                   for r in rows))
    expect = {r["id"]: r["expect"]["accept"] for r in rows}

    runners: dict[str, dict[str, dict]] = {}
    if a.lean_runner:
        runners["lean"] = _run(a.lean_runner, corpus_path)
    if a.zesu_probe:
        runners["zesu"] = _run(a.zesu_probe, corpus_path)

    failures: list[str] = []
    for case_id, want_accept in expect.items():
        decisions: dict[str, str] = {}
        values: dict[str, str] = {}
        for party, results in runners.items():
            row = results.get(case_id)
            if row is None:
                failures.append(f"{case_id}: {party} produced no outcome")
                continue
            got = row["outcome"] == "accept"
            if got != want_accept:
                failures.append(f"{case_id}: {party} outcome={row['outcome']} but corpus expects "
                                f"{'accept' if want_accept else 'reject'}")
            decisions[party] = row["outcome"]
            if "value" in row:
                values[party] = row["value"]
        if len(set(decisions.values())) > 1:
            failures.append(f"{case_id}: runners disagree on outcome: "
                            + "; ".join(f"{p}={o}" for p, o in decisions.items()))
        if len(set(values.values())) > 1:
            failures.append(f"{case_id}: value-emitting runners disagree on value: "
                            + ", ".join(sorted(values)))

    parties = "+".join(runners)
    if failures:
        print(f"CONTRACT AGREEMENT FAILED ({parties}), {len(failures)} issue(s):", file=sys.stderr)
        for f in failures[:50]:
            print(f"  {f}", file=sys.stderr)
        return 1
    print(f"contract agreement OK: {len(expect)} cases, parties={parties}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
