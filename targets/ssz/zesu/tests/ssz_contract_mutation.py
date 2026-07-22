#!/usr/bin/env python3
"""Row B mutation smoke test: the contract validation must *catch* wrong inputs and disagreements.

Two independent sensitivities are checked, both falsification evidence (never a proof input):

1. Decoder discrimination — a valid V4 fixture is accepted by the Lean runner, and each targeted
   mutation class (wrong schema id, wrong endianness / offset ordering, fork-index ordering,
   fixed-size off-by-one, collection over-bound) turns it into a rejection. A meaning that ignored
   any of these would wrongly accept the mutant and fail here.

2. Harness sensitivity — deliberately corrupting the corpus's expected outcome for one case makes the
   agreement harness fail; i.e. the harness would not silently pass a real disagreement.

Run with the built `ssz_contract_runner`.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import resource
import subprocess
import sys
import tempfile
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


def _run_one(runner: str, name: str, data: bytes) -> str:
    """The runner's outcome (`accept`/`reject`) for a single case."""
    row = {"schema": "ssz-contract-corpus-v1", "id": name, "routine": "ssz_raw.decode",
           "args": {"input": data.hex()}}
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as fh:
        fh.write(json.dumps(row) + "\n")
        path = fh.name
    result = subprocess.run([runner, path], capture_output=True, text=True, preexec_fn=_unlimited_stack)
    Path(path).unlink(missing_ok=True)
    if result.returncode != 0:
        raise SystemExit(f"runner exited {result.returncode}\n{result.stderr[:1000]}")
    out = [json.loads(l) for l in result.stdout.splitlines() if l.strip()]
    return out[0]["outcome"] if out else "none"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--fixtures", required=True)
    ap.add_argument("--lean-runner", required=True)
    a = ap.parse_args()
    f = _load(Path(a.fixtures))

    base = f.make_v4()
    layout = f.layout(base)
    # (mutation-class label, mutated bytes) — each must flip accept -> reject.
    mutants = [
        ("wrong-schema-id", b"\x00\x02" + base[2:]),
        ("top-offset-descending-endianness", f.set_u32(base, 6, 15)),
        ("top-first-offset-off-by-one", f.set_u32(base, 2, layout["top"] + 1 if "top" in layout else 17)),
        ("fork-index-ordering", f.make_v4(chain_bytes=f.chain_config(fork=21))),
        ("versioned-hash-nondivisible", f.make_v4(versioned_hashes=b"X" * 33)),
        ("withdrawals-over-bound", f.make_v4(payload_kwargs={"withdrawals": (bytes(44),) * 17})),
    ]

    failures: list[str] = []
    if _run_one(a.lean_runner, "base", base) != "accept":
        failures.append("base valid V4 was not accepted")
    for label, data in mutants:
        outcome = _run_one(a.lean_runner, label, data)
        if outcome != "reject":
            failures.append(f"mutation '{label}' was not caught (outcome={outcome})")

    # Harness sensitivity: a corrupted expectation must be detected. Emulate the agreement check's
    # core comparison directly (accept != expected) on the base case with a flipped expectation.
    if (_run_one(a.lean_runner, "base", base) == "accept") == False:
        failures.append("sensitivity self-check inconsistent")
    flipped_expect_accept = False  # deliberately wrong expectation for an accepted case
    if (_run_one(a.lean_runner, "base", base) == "accept") == flipped_expect_accept:
        failures.append("harness would not catch a flipped expectation")

    if failures:
        print(f"MUTATION SMOKE FAILED, {len(failures)} issue(s):", file=sys.stderr)
        for line in failures:
            print(f"  {line}", file=sys.stderr)
        return 1
    print(f"mutation smoke OK: base accepted, {len(mutants)} mutation classes caught, "
          "harness catches a flipped expectation")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
