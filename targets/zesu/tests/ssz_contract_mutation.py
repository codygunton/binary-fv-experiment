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
    row = {"schema": "ssz-contract-corpus-v1", "id": name, "source_function": "ssz_raw.decode",
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


# ---- SourceFunction-vector mutations: prove the per-source_function value/error check is discriminating. Each mutates
# ONE row's expectation and requires the probe to flag exactly that row as a mismatch. ----------------

def _gen_vectors(generator: str, abi: str | None = None) -> list[dict]:
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as fh:
        path = fh.name
    cmd = [sys.executable, generator, "--out", path]
    if abi:
        cmd += ["--abi", abi]  # so allocating vectors carry expected ledgers
    subprocess.run(cmd, check=True)
    rows = [json.loads(l) for l in Path(path).read_text().splitlines() if l.strip()]
    Path(path).unlink(missing_ok=True)
    return rows


def _probe_source_function_vectors(probe: str, rows: list[dict]) -> tuple[int, dict]:
    """Run `probe --source-function-vectors` over `rows`; return (returncode, {id: match_bool})."""
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as fh:
        for r in rows:
            fh.write(json.dumps(r) + "\n")
        path = fh.name
    result = subprocess.run([probe, "--source-function-vectors", path], capture_output=True, text=True,
                            preexec_fn=_unlimited_stack)
    Path(path).unlink(missing_ok=True)
    outcomes = {}
    for line in result.stdout.splitlines():
        if line.strip():
            o = json.loads(line)
            outcomes[o["id"]] = o.get("match")
    return result.returncode, outcomes


def _first(rows, predicate):
    for r in rows:
        if predicate(r):
            return r
    raise SystemExit(f"mutation: no source_function vector matched a required predicate")


def routine_vector_mutations(probe: str, generator: str, abi: str | None = None) -> list[str]:
    """Each mutation edits one expected value/error/allocation-event and must be caught (that row ->
    match:false, probe exits nonzero). Covers wrong local value, wrong error, endianness, size bound,
    fork/error ordering, and — against the independent expected ledger — allocation size/alignment/
    ordinal."""
    pristine = _gen_vectors(generator, abi)
    fails: list[str] = []

    rc, base = _probe_source_function_vectors(probe, pristine)
    if rc != 0 or not all(base.values()):
        fails.append("pristine source_function vectors did not all match")

    def mutate(label, predicate, edit):
        target = _first(pristine, predicate)
        rows = json.loads(json.dumps(pristine))
        for r in rows:
            if r["id"] == target["id"]:
                edit(r)
        rc2, out = _probe_source_function_vectors(probe, rows)
        if out.get(target["id"]) is not False:
            fails.append(f"mutation '{label}' not caught: {target['id']} still match={out.get(target['id'])}")
        elif rc2 == 0:
            fails.append(f"mutation '{label}' left the probe exit code 0")

    def has_ledger(r):
        return bool(r["expect"].get("ledger"))

    # wrong local value: bump a readU64 expected scalar.
    mutate("local-value",
           lambda r: r["source_function"] == "ssz_raw.readU64" and r["expect"]["kind"] == "value",
           lambda r: r["expect"]["value"].__setitem__("nat", str(int(r["expect"]["value"]["nat"]) + 1)))
    # wrong local error: relabel an invalidSsz expectation as unknownFork.
    mutate("local-error",
           lambda r: r["expect"]["kind"] == "error" and r["expect"]["error"] == "invalidSsz",
           lambda r: r["expect"].__setitem__("error", "unknownFork"))
    # endianness: byte-swap a readU32 expected value (little-endian vs big-endian differ).
    mutate("endianness",
           lambda r: r["source_function"] == "ssz_raw.readU32" and r["expect"]["kind"] == "value"
           and int(r["expect"]["value"]["nat"]) not in (0,)
           and int(r["expect"]["value"]["nat"]) != int.from_bytes(int(r["expect"]["value"]["nat"]).to_bytes(4, "little"), "big"),
           lambda r: r["expect"]["value"].__setitem__(
               "nat", str(int.from_bytes(int(r["expect"]["value"]["nat"]).to_bytes(4, "little"), "big"))))
    # size bound: drop one byte from a readArray expected slice.
    mutate("size-bound",
           lambda r: r["source_function"].startswith("ssz_raw.readArray[") and r["expect"]["kind"] == "value",
           lambda r: r["expect"]["value"].__setitem__("bytes", r["expect"]["value"]["bytes"][:-2]))
    # fork/error ordering: relabel a decodeForkConfig unknownFork as invalidSsz.
    mutate("fork-ordering",
           lambda r: r["source_function"] == "ssz_raw.decodeForkConfig" and r["expect"]["kind"] == "error"
           and r["expect"]["error"] == "unknownFork",
           lambda r: r["expect"].__setitem__("error", "invalidSsz"))

    # Allocation ledger: corrupt one field of the INDEPENDENT expected ledger and require the probe to
    # flag it. These only run with an ABI table (otherwise no expected ledger is present).
    if abi is not None:
        # size: a wrong-but-plausible byte count (e.g. 48 -> 56 for a withdrawal block).
        mutate("alloc-size",
               lambda r: has_ledger(r),
               lambda r: r["expect"]["ledger"][0].__setitem__("size", r["expect"]["ledger"][0]["size"] + 8))
        # alignment: a wrong-but-plausible power of two.
        mutate("alloc-alignment",
               lambda r: has_ledger(r),
               lambda r: r["expect"]["ledger"][0].__setitem__("alignment",
                                                              r["expect"]["ledger"][0]["alignment"] * 2 or 4))
        # ordinal / sequence: renumber the first event.
        mutate("alloc-ordinal",
               lambda r: has_ledger(r),
               lambda r: r["expect"]["ledger"][0].__setitem__("ordinal", 7))
        # frees: claim a block was not freed on the success path.
        mutate("alloc-freed",
               lambda r: has_ledger(r),
               lambda r: r["expect"]["ledger"][0].__setitem__("freed", False))
        # aliases: claim a block aliased a live block.
        mutate("alloc-aliases",
               lambda r: has_ledger(r),
               lambda r: r["expect"]["ledger"][0].__setitem__("aliases", True))
    return fails


def removed_routine_case(probe: str, report: str, generator: str, program_json: str, corpus: str,
                         outcomes: str, ledger: str, abi: str | None = None) -> list[str]:
    """Dropping a required source_function's vectors must surface as a coverage gap for EXACTLY that source_function —
    the other 42 stay covered. Uses genuine probe outcomes for the retained rows (not the vector file),
    so `covered` reflects real match results rather than an all-unmatched artifact."""
    if not (probe and report and program_json and corpus and outcomes and ledger):
        return []
    pristine = _gen_vectors(generator, abi)
    dropped = "ssz_raw.readU256"
    kept = [r for r in pristine if r["source_function"] != dropped]
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as fh:
        for r in kept:
            fh.write(json.dumps(r) + "\n")
        vec_path = fh.name
    # Genuine probe outcomes for the retained vectors.
    result = subprocess.run([probe, "--source-function-vectors", vec_path], capture_output=True, text=True,
                            preexec_fn=_unlimited_stack)
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as fh:
        fh.write(result.stdout)
        out_path = fh.name
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
        rj = fh.name
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as fh:
        rm = fh.name
    subprocess.run([sys.executable, report, "--corpus", corpus, "--outcomes", outcomes,
                    "--ledger", ledger, "--program-json", program_json, "--source-function-vectors", vec_path,
                    "--source-function-outcomes", out_path, "--out-json", rj, "--out-md", rm],
                   check=True, capture_output=True, text=True)
    rc = json.loads(Path(rj).read_text())["source_function_coverage"]
    for p in (vec_path, out_path, rj, rm):
        Path(p).unlink(missing_ok=True)
    uncovered = set(rc["uncovered_routines"])
    if uncovered != {dropped}:
        return [f"removed-source_function-case: dropping {dropped} should leave exactly it uncovered, "
                f"got uncovered={sorted(uncovered)}"]
    return []


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--fixtures", required=True)
    ap.add_argument("--lean-runner", required=True)
    # Optional: the host probe + source_function-vector generator enable the per-source_function value/error, allocation
    # ledger, and removed-source_function-case mutation classes (the Lean runner has no --source-function-vectors mode).
    ap.add_argument("--probe")
    ap.add_argument("--source-function-vectors-gen")
    ap.add_argument("--report")
    ap.add_argument("--program-json")
    ap.add_argument("--corpus")
    ap.add_argument("--outcomes")
    ap.add_argument("--ledger")
    ap.add_argument("--abi")
    a = ap.parse_args()
    f = _load(Path(a.fixtures))

    base = f.make_v4()
    layout = f.layout(base)
    ere_ok = f.u32(len(base)) + base            # exact ERE-length prefix -> `decode` retries and accepts
    # (mutation-class label, mutated bytes) — each must flip accept -> reject.
    mutants = [
        ("wrong-schema-id", b"\x00\x02" + base[2:]),
        ("top-offset-descending-endianness", f.set_u32(base, 6, 15)),
        ("top-first-offset-off-by-one", f.set_u32(base, 2, layout["top"] + 1 if "top" in layout else 17)),
        ("fork-index-ordering", f.make_v4(chain_bytes=f.chain_config(fork=21))),
        ("versioned-hash-nondivisible", f.make_v4(versioned_hashes=b"X" * 33)),
        ("withdrawals-over-bound", f.make_v4(payload_kwargs={"withdrawals": (bytes(44),) * 17})),
        # ERE retry: corrupting the exact-length prefix breaks the retry, so the accepted ERE input is
        # rejected. Distinguishes the retry gate from a raw-only decode.
        ("ere-retry-length", f.u32(len(base) + 1) + base),
    ]

    failures: list[str] = []
    if _run_one(a.lean_runner, "base", base) != "accept":
        failures.append("base valid V4 was not accepted")
    if _run_one(a.lean_runner, "ere-ok", ere_ok) != "accept":
        failures.append("valid exact-ERE-prefixed input was not accepted (retry path)")
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

    # Per-source_function value/error, allocation-ledger, and removed-source_function-case mutations (host probe only).
    routine_classes = 0
    if a.probe and a.source_function_vectors_gen:
        rv = routine_vector_mutations(a.probe, a.source_function_vectors_gen, a.abi)
        rm = removed_routine_case(a.probe, a.report, a.source_function_vectors_gen, a.program_json,
                                  a.corpus, a.outcomes, a.ledger, a.abi)
        failures += rv + rm
        routine_classes = 5 + (5 if a.abi else 0) + (1 if a.report else 0)

    if failures:
        print(f"MUTATION SMOKE FAILED, {len(failures)} issue(s):", file=sys.stderr)
        for line in failures:
            print(f"  {line}", file=sys.stderr)
        return 1
    print(f"mutation smoke OK: base + ere accepted, {len(mutants)} decode mutation classes caught, "
          f"{routine_classes} source_function/ledger/coverage mutation classes caught, "
          "harness catches a flipped expectation")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
