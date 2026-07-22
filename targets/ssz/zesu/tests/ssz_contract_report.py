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


def _routine_id(qualified: str, specialization: list) -> str:
    """The routine identity used by the vectors: qualified name plus any specialization suffix
    (e.g. `ssz_raw.readArray[32]`). Bare names (`memcpy`) and non-readArray routines have no suffix."""
    return qualified + (f"[{','.join(specialization)}]" if specialization else "")


def build_routine_and_occurrence_tables(
    occurrences: list[dict], vectors: list[dict], outcomes: list[dict]
) -> dict:
    """Coverage keyed first by all 43 routine identities, then by all 141 generated occurrences.

    A routine is *covered* iff it has at least one non-gap typed vector whose probe outcome matched.
    Each occurrence inherits its routine's coverage. Routines / occurrences with no covering vector are
    reported as explicit gaps rather than silently omitted."""
    outcome_by_id = {o["id"]: o for o in outcomes}

    # Per-routine aggregation over the typed vectors.
    routines: dict[str, dict] = {}
    for v in vectors:
        rt = v["routine"]
        exp = v.get("expect", {})
        kind = exp.get("kind", "value")
        got = outcome_by_id.get(v["id"], {})
        matched = bool(got.get("match"))
        events = got.get("events", [])
        r = routines.setdefault(rt, {
            "vectors": 0, "matched": 0, "value": 0, "error": 0, "gap": 0,
            "categories": set(), "allocations": 0, "leaked": False, "oom_unsafe": False,
        })
        r["vectors"] += 1
        r["matched"] += 1 if matched else 0
        r[kind if kind in ("value", "error", "gap") else "value"] += 1
        r["categories"].add(v.get("coverage", "unknown"))
        r["allocations"] += len(events)
        if got.get("leaked"):
            r["leaked"] = True
        if got.get("oom_safe") is False:
            r["oom_unsafe"] = True

    # All routine identities that carry an occurrence, plus any the vectors exercise.
    occ_ids = [_routine_id(o.get("qualified", "?"), o.get("specialization", [])) for o in occurrences]
    all_routine_ids = sorted(set(occ_ids) | set(routines))

    def covered(rt: str) -> bool:
        r = routines.get(rt)
        return bool(r) and (r["value"] + r["error"]) > 0 and r["matched"] == r["vectors"]

    routine_rows = []
    for rt in all_routine_ids:
        r = routines.get(rt, {"vectors": 0, "matched": 0, "value": 0, "error": 0, "gap": 0,
                              "categories": set(), "allocations": 0, "leaked": False, "oom_unsafe": False})
        routine_rows.append({
            "routine": rt,
            "occurrences": occ_ids.count(rt),
            "vectors": r["vectors"],
            "matched": r["matched"],
            "value_cases": r["value"],
            "error_cases": r["error"],
            "gap_cases": r["gap"],
            "categories": sorted(r["categories"]),
            "allocation_events": r["allocations"],
            "leaked": r["leaked"],
            "oom_unsafe": r["oom_unsafe"],
            "covered": covered(rt),
        })

    occurrence_rows = []
    for idx, o in enumerate(occurrences):
        rt = _routine_id(o.get("qualified", "?"), o.get("specialization", []))
        occurrence_rows.append({
            "index": idx,
            "entry_pc": o.get("entryPc"),
            "routine": rt,
            "kind": o.get("kind", ""),
            "covered": covered(rt),
        })

    return {
        "routine_coverage": {
            "routines": len(all_routine_ids),
            "occurrences": len(occurrences),
            "all_routines_covered": all(r["covered"] for r in routine_rows),
            "all_occurrences_covered": all(o["covered"] for o in occurrence_rows),
            "uncovered_routines": [r["routine"] for r in routine_rows if not r["covered"]],
        },
        "routines": routine_rows,
        "occurrences": occurrence_rows,
    }


def build_report(corpus: list[dict], outcomes: list[dict], ledger: list[dict],
                 occurrences: list[dict] | None = None, vectors: list[dict] | None = None,
                 routine_outcomes: list[dict] | None = None) -> dict:
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

    routine_occurrence = (
        build_routine_and_occurrence_tables(occurrences, vectors, routine_outcomes or [])
        if occurrences is not None and vectors is not None else None
    )

    report = {
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
                                      "probe exercises each routine directly via typed vectors and the "
                                      "composed top-level entrypoint",
        },
    }
    if routine_occurrence is not None:
        report["routine_coverage"] = routine_occurrence["routine_coverage"]
        report["routines"] = routine_occurrence["routines"]
        report["occurrences"] = routine_occurrence["occurrences"]
    return report


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
    if "routines" in report:
        rc = report["routine_coverage"]
        lines += [
            "",
            "## Per-routine coverage (all 43 catalog identities)",
            "",
            f"- routine identities: **{rc['routines']}**; generated occurrences: **{rc['occurrences']}**",
            f"- all routines covered by a matching typed vector: **{rc['all_routines_covered']}**",
            f"- all occurrences covered: **{rc['all_occurrences_covered']}**",
        ]
        if rc["uncovered_routines"]:
            lines.append(f"- **uncovered (gap):** {', '.join(rc['uncovered_routines'])}")
        lines += [
            "",
            "| routine | occ | vectors | value | error | matched | alloc-events | leaked | oom-unsafe | covered |",
            "| --- | ---: | ---: | ---: | ---: | ---: | ---: | :---: | :---: | :---: |",
        ]
        for r in report["routines"]:
            lines.append(
                f"| {r['routine']} | {r['occurrences']} | {r['vectors']} | {r['value_cases']} | "
                f"{r['error_cases']} | {r['matched']}/{r['vectors']} | {r['allocation_events']} | "
                f"{'✗' if r['leaked'] else '·'} | {'✗' if r['oom_unsafe'] else '·'} | "
                f"{'✓' if r['covered'] else 'GAP'} |"
            )
        lines += [
            "",
            "## Per-occurrence coverage (all 141 generated occurrences)",
            "",
            "| # | entry-pc | routine | kind | covered |",
            "| ---: | ---: | --- | --- | :---: |",
        ]
        for o in report["occurrences"]:
            lines.append(
                f"| {o['index']} | {o['entry_pc']} | {o['routine']} | {o['kind']} | "
                f"{'✓' if o['covered'] else 'GAP'} |"
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
    # Optional inputs that add the 43-routine and 141-occurrence coverage tables.
    ap.add_argument("--program-json", help="elfling program.json (the 141 generated occurrences)")
    ap.add_argument("--routine-vectors", help="ssz-routine-vectors-v1 JSONL")
    ap.add_argument("--routine-outcomes", help="probe --routine-vectors output JSONL")
    a = ap.parse_args()

    occurrences = vectors = routine_outcomes = None
    if a.program_json:
        occurrences = json.loads(Path(a.program_json).read_text())["occurrences"]
    if a.routine_vectors:
        vectors = _load_jsonl(Path(a.routine_vectors))
    if a.routine_outcomes:
        routine_outcomes = _load_jsonl(Path(a.routine_outcomes))

    report = build_report(
        _load_jsonl(Path(a.corpus)), _load_jsonl(Path(a.outcomes)), _load_jsonl(Path(a.ledger)),
        occurrences=occurrences, vectors=vectors, routine_outcomes=routine_outcomes,
    )
    Path(a.out_json).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    Path(a.out_md).write_text(render_md(report))
    rc = report.get("routine_coverage")
    cov = (f", routines={rc['routines']} occ={rc['occurrences']} "
           f"all_covered={rc['all_routines_covered'] and rc['all_occurrences_covered']}") if rc else ""
    print(f"report: {report['summary']['cases']} cases, "
          f"agree={report['summary']['all_agree_with_corpus']}, "
          f"leaks={report['summary']['leaks']}, oom_unsafe={report['summary']['oom_unsafe']}{cov}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
