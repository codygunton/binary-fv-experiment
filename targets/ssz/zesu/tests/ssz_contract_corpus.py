#!/usr/bin/env python3
"""Versioned JSONL contract-validation corpus for Row B (direct source contract validation).

One corpus drives both runners: the host Zig probe over the pinned private decoder routines and a
Lean executable over the handwritten `meaning` definitions. Both emit canonical JSONL outcomes that
must agree exactly; this module only produces the shared *inputs* plus per-case provenance and the
required coverage category. Expected outcomes are produced by the runners (and cross-checked), never
guessed here.

Determinism: cases come from the pinned strict-V4 fixture builders in `ssz_differential_audit.py`
(seeded `bytes_from`, fixed `SCHEMA_ID`); rows are emitted in a fixed order with sorted JSON keys, so
two runs are byte-identical (the Nix derivation requires it).

Schema (`ssz-contract-corpus-v1`), one JSON object per line:
  schema      : corpus schema version string
  id          : stable case identifier
  seed        : deterministic seed (0 for fixture-derived cases)
  provenance  : {zesu, fixtures} source pins
  routine     : the pinned `FunctionId` string the case exercises (e.g. `ssz_raw.decode`)
  args        : typed arguments (for the top-level routine, `{input: <hex>}`)
  coverage    : the required coverage category the case satisfies
  expect      : minimal cross-check the corpus can assert without a reference decoder
                (`{accept: bool}` for the top-level routine); full value/ledger are runner output
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

SCHEMA = "ssz-contract-corpus-v1"
ZESU_PIN = "codygunton/zesu@96f1621468ba54755d653f19cbc9704e789be001"


def _load_fixtures(fixtures_path: Path):
    """Import the pinned fixture builders as a module without running their `main`."""
    spec = importlib.util.spec_from_file_location("ssz_fixtures", fixtures_path)
    module = importlib.util.module_from_spec(spec)
    # Register before exec so the module's own `@dataclass` decorators can resolve `__module__`.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _coverage_of(name: str, valid: bool) -> str:
    """The required coverage category a fixture case satisfies, from its stable name."""
    if valid:
        if "empty" in name:
            return "valid-empty-minimal"
        if "rich" in name:
            return "valid-nonempty-max-populated"
        if "ere" in name:
            return "valid-ere-prefixed"
        if "collision" in name:
            return "raw-ere-collision"
        return "valid-raw-canonical"
    if "schema" in name:
        return "reject-bad-schema-id"
    if "trunc" in name:
        return "reject-truncated"
    if "ere" in name:
        return "reject-ere-length-mismatch"
    if "offset" in name or "descending" in name or "out-of-range" in name or "first-offset" in name:
        return "reject-noncanonical-offset"
    if "over-bound" in name or "nondivisible" in name:
        return "reject-collection-bound"
    if "fork" in name:
        return "reject-unknown-fork"
    return "reject-malformed"


def top_level_rows(fixtures) -> list[dict]:
    """One row per strict-V4 fixture case, exercising the exported/top-level `ssz_raw.decode`."""
    rows: list[dict] = []
    for case in fixtures.cases():
        rows.append({
            "schema": SCHEMA,
            "id": f"decode/{case.name}",
            "seed": 0,
            "provenance": {"zesu": ZESU_PIN, "fixtures": "ssz_differential_audit.py"},
            "routine": "ssz_raw.decode",
            "args": {"input": case.data.hex()},
            "coverage": _coverage_of(case.name, case.valid),
            "expect": {"accept": case.valid},
        })
    return rows


def corpus_rows(fixtures) -> list[dict]:
    """The full corpus, in a fixed deterministic order."""
    rows = top_level_rows(fixtures)
    rows.sort(key=lambda r: r["id"])
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--fixtures", required=True, help="path to ssz_differential_audit.py")
    ap.add_argument("--out", help="output corpus.jsonl (default: stdout)")
    a = ap.parse_args()
    fixtures = _load_fixtures(Path(a.fixtures))
    rows = corpus_rows(fixtures)
    text = "".join(json.dumps(r, sort_keys=True, separators=(",", ":")) + "\n" for r in rows)
    if a.out:
        Path(a.out).write_text(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
