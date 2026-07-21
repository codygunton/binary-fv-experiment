#!/usr/bin/env python3
"""Negative tests for the Elfling generator's defect surfacing (review blocker #1).

Every one of these shows a defect is SURFACED and FAILS generation, never silently dropped:

  * unmapped region       — a linker map missing an object's `.text` placement makes the affected
                            occurrences unmappable; the generator emits `unmappedRegion` defects, writes
                            them into the JSON, and exits nonzero (end-to-end against the real sidecars).
  * ambiguous attribution — a `readArray(<unknown>)` whose width cannot be resolved from source is an
                            `ambiguousAttribution` (unit test of the pure resolution path).
  * sibling overlap       — two occurrences claiming a common PC without an inline ancestor relationship
                            are `overlappingOwnership` (unit test of the pure detector); the real,
                            correctly-nested program produces none.

`uncovered reachable instructions` are not decidable from DWARF alone (they need the decoded CFG); that
guard is the Lean reachable-partition proof, whose mutation test lives with the generator-backed
reachability (area #5).

Usage: generator_defects_test.py --generator GEN.py --readelf RE --decoder … --allocator … --sink …
                                 --runtime … --source DIR --runtime-c FILE --map MAP
"""
import argparse, importlib.util, json, os, subprocess, sys, tempfile

FAILURES = []


def check(name, cond, detail=""):
    print(f"  [{'ok' if cond else 'FAIL'}] {name}{('  — ' + detail) if detail else ''}")
    if not cond:
        FAILURES.append(name)


def load_generator(path):
    spec = importlib.util.spec_from_file_location("elfling_generator", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run_generator(args, extra):
    """Run the generator script as a subprocess; return (returncode, combined_output)."""
    cmd = [sys.executable, args.generator,
           "--readelf", args.readelf, "--decoder", args.decoder, "--allocator", args.allocator,
           "--sink", args.sink, "--runtime", args.runtime, "--source", args.source,
           "--runtime-c", args.runtime_c] + extra
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def test_unmapped_region(args, tmp):
    mutated = os.path.join(tmp, "no-runtime.map")
    with open(args.map) as f, open(mutated, "w") as out:
        for ln in f:
            if ".text.memcpy" in ln or ".text.memmove" in ln:
                continue
            out.write(ln)
    outj = os.path.join(tmp, "unmapped.json")
    rc, log = run_generator(args, ["--map", mutated, "--out-json", outj])
    check("unmapped: generation exits nonzero", rc != 0, f"rc={rc}")
    check("unmapped: reports unmappedRegion", "unmappedRegion" in log)
    if os.path.exists(outj):
        kinds = {d["kind"] for d in json.load(open(outj))["defects"]}
        check("unmapped: emitted JSON carries the defect", "unmappedRegion" in kinds, str(sorted(kinds)))


def test_ambiguous_width(gen):
    die = gen.DIE(0x10, 3, "DW_TAG_inlined_subroutine")
    die.attrs["DW_AT_call_line"] = "1"
    unresolved = gen.norm_identity("ssz_raw.readArray__anon_9", die,
                                   ["const x = readArray(zz_not_a_width, data, off);"], {})
    check("ambiguous: unknown readArray width is unresolved", unresolved is None, repr(unresolved))
    resolved = gen.norm_identity("ssz_raw.readArray__anon_9", die,
                                 ["const x = readArray(32, d, o);"], {})
    check("ambiguous: a resolvable width is NOT a defect",
          resolved == ("ssz_raw.readArray", ("32",)), repr(resolved))


def test_sibling_overlap(gen, args, tmp):
    occ = [
        {"parentIdx": None, "regions": [{"start": 0x1000, "size": 0x40}], "qualified": "a"},
        {"parentIdx": None, "regions": [{"start": 0x1020, "size": 0x40}], "qualified": "b"},  # overlaps a
        {"parentIdx": 0, "regions": [{"start": 0x1000, "size": 0x10}], "qualified": "child"},  # nested in a
    ]
    defs = gen.sibling_overlap_defects(occ)
    kinds = [d["kind"] for d in defs]
    check("overlap: sibling PC clash surfaced", "overlappingOwnership" in kinds, str(kinds))
    check("overlap: nested child is NOT flagged against its parent",
          all({d["firstIdx"], d["secondIdx"]} != {0, 2} for d in defs))

    outj = os.path.join(tmp, "canonical.json")
    rc, _ = run_generator(args, ["--map", args.map, "--out-json", outj])
    check("overlap: real program generates cleanly", rc == 0 and os.path.exists(outj), f"rc={rc}")
    if os.path.exists(outj):
        real = gen.sibling_overlap_defects(json.load(open(outj))["occurrences"])
        check("overlap: detector finds none on the real occurrences", real == [], str(real))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--generator", required=True)
    for k in ["readelf", "decoder", "allocator", "sink", "runtime", "source", "runtime-c", "map"]:
        ap.add_argument("--" + k, required=True)
    args = ap.parse_args()
    args.runtime_c = args.runtime_c  # argparse stores --runtime-c as runtime_c
    gen = load_generator(args.generator)

    with tempfile.TemporaryDirectory() as tmp:
        print("unmapped region:");       test_unmapped_region(args, tmp)
        print("ambiguous attribution:"); test_ambiguous_width(gen)
        print("sibling overlap:");       test_sibling_overlap(gen, args, tmp)

    if FAILURES:
        print(f"\nGENERATOR DEFECT TESTS FAILED: {FAILURES}", file=sys.stderr)
        sys.exit(1)
    print("\nALL GENERATOR DEFECT TESTS PASSED")


if __name__ == "__main__":
    main()
