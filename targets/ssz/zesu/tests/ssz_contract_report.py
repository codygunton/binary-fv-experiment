#!/usr/bin/env python3
"""Row B contract-validation report: consolidate the shared corpus, the host probe's canonical
outcomes, and its allocation ledger into one deterministic JSON + Markdown evidence artifact.

This is a *report over already-checked evidence*, not itself a gate: the probe check
(`sszContractProbeCheck`) is what fails the build on a disagreement, leak, or out-of-memory defect.
The report exists so a reviewer can see, in one place, the coverage the corpus achieves and the
per-case decision + allocation profile of the real `ssz_raw.decode` source.

Determinism: every table is sorted by a stable key and no wall-clock time is emitted, so the JSON and
Markdown are byte-identical across runs (the Nix derivation embeds them as build outputs).
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def _load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def build_report(corpus: list[dict], outcomes: list[dict], ledger: list[dict]) -> dict:
    by_id = {r["id"]: r for r in corpus}
    outcome_by_id = {r["id"]: r for r in outcomes}
    ledger_by_id = {r["id"]: r for r in ledger}

    coverage: dict[str, dict[str, int]] = {}
    cases = []
    accepts = rejects = leaks = oom_unsafe = aliasing = 0
    for cid in sorted(by_id):
        row = by_id[cid]
        cov = row.get("coverage", "unknown")
        expect_accept = row["expect"]["accept"]
        got = outcome_by_id.get(cid, {})
        led = ledger_by_id.get(cid, {})
        decided_accept = got.get("outcome") == "accept"
        agrees = decided_accept == expect_accept
        if decided_accept:
            accepts += 1
        else:
            rejects += 1
        if led.get("leaked"):
            leaks += 1
        if led.get("oom_safe") is False:
            oom_unsafe += 1
        if any(e.get("aliases") for e in led.get("events", [])):
            aliasing += 1
        bucket = coverage.setdefault(cov, {"cases": 0, "accept": 0, "reject": 0})
        bucket["cases"] += 1
        bucket["accept" if decided_accept else "reject"] += 1
        # Per-event allocation ledger (recording allocator): derive the aggregate columns from events.
        events = led.get("events", [])
        allocated_bytes = sum(e["size"] for e in events)
        freed_bytes = sum(e["size"] for e in events if e.get("freed"))
        aliases = any(e.get("aliases") for e in events)
        cases.append({
            "id": cid,
            "coverage": cov,
            "expect_accept": expect_accept,
            "probe_outcome": got.get("outcome", "missing"),
            "agrees": agrees,
            "allocations": led.get("allocations"),
            "allocated_bytes": allocated_bytes,
            "freed_bytes": freed_bytes,
            "aliases": aliases,
            "leaked": led.get("leaked"),
            "oom_safe": led.get("oom_safe"),
            "oom_injected": led.get("oom_injected"),
            "oom_sampled": led.get("oom_sampled"),
        })

    return {
        "schema": "ssz-contract-report-v1",
        "summary": {
            "cases": len(cases),
            "accept": accepts,
            "reject": rejects,
            "all_agree_with_corpus": all(c["agrees"] for c in cases),
            "leaks": leaks,
            "oom_unsafe": oom_unsafe,
            "aliasing": aliasing,
        },
        "coverage": {k: coverage[k] for k in sorted(coverage)},
        "cases": cases,
        # What certifies which property; keeps the report honest about the probe's deliberate scope.
        "provenance": {
            "decision_source": "ssz_raw.decode (pinned private routine, ReleaseSafe host build)",
            "decision_agreement": "probe outcome == corpus.expect.accept (this report) and, in Nix, "
                                  "probe == corpus and meanings == oracle == corpus (transitive)",
            "value_fidelity": "certified separately by the preserved three-way ssz-value-v1 audit; "
                              "the probe deliberately emits only the decision + ledger",
            "occurrence_granularity": "the 43 routines / 141 occurrences are validated in the Lean "
                                      "binding inventory (Row A) and production traces (Row C); the "
                                      "probe exercises their composed top-level entrypoint",
        },
    }


def render_md(report: dict) -> str:
    s = report["summary"]
    lines = [
        "# Row B contract-validation report",
        "",
        f"Schema `{report['schema']}`. Source of the decision column: the pinned private "
        "`ssz_raw.decode` routine, compiled ReleaseSafe for the host.",
        "",
        "## Summary",
        "",
        f"- cases: **{s['cases']}** ({s['accept']} accept / {s['reject']} reject)",
        f"- all decisions agree with the corpus expectation: **{s['all_agree_with_corpus']}**",
        f"- error-path leaks: **{s['leaks']}**",
        f"- out-of-memory-unsafe cases: **{s['oom_unsafe']}**",
        f"- cases with aliasing live allocations: **{s['aliasing']}**",
        "",
        "## Coverage",
        "",
        "| category | cases | accept | reject |",
        "| --- | ---: | ---: | ---: |",
    ]
    for cov, b in report["coverage"].items():
        lines.append(f"| {cov} | {b['cases']} | {b['accept']} | {b['reject']} |")
    lines += [
        "",
        "## Per-case decision and allocation ledger",
        "",
        "| id | coverage | outcome | agrees | allocs | bytes | oom-safe |",
        "| --- | --- | --- | :---: | ---: | ---: | :---: |",
    ]
    for c in report["cases"]:
        lines.append(
            f"| {c['id']} | {c['coverage']} | {c['probe_outcome']} | "
            f"{'✓' if c['agrees'] else '✗'} | {c['allocations']} | {c['allocated_bytes']} | "
            f"{'✓' if c['oom_safe'] else '✗'} |"
        )
    p = report["provenance"]
    lines += [
        "",
        "## What certifies what",
        "",
        f"- **decision**: {p['decision_source']}; agreement: {p['decision_agreement']}.",
        f"- **value fidelity**: {p['value_fidelity']}.",
        f"- **occurrence granularity**: {p['occurrence_granularity']}.",
        "",
    ]
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True)
    ap.add_argument("--outcomes", required=True)
    ap.add_argument("--ledger", required=True)
    ap.add_argument("--out-json", required=True)
    ap.add_argument("--out-md", required=True)
    a = ap.parse_args()

    report = build_report(
        _load_jsonl(Path(a.corpus)), _load_jsonl(Path(a.outcomes)), _load_jsonl(Path(a.ledger))
    )
    Path(a.out_json).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    Path(a.out_md).write_text(render_md(report))
    print(f"report: {report['summary']['cases']} cases, "
          f"agree={report['summary']['all_agree_with_corpus']}, "
          f"leaks={report['summary']['leaks']}, oom_unsafe={report['summary']['oom_unsafe']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
