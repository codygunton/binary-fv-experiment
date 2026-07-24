#!/usr/bin/env python3
"""Negative tests for the Elfling generator's defect surfacing (review blocker #1).

Every one of these shows a defect is SURFACED and FAILS generation, never silently dropped:

  * unmapped region       — a linker map missing an object's `.text` placement makes the affected
                            function_instances unmappable; the generator emits `unmappedRegion` defects, writes
                            them into the JSON, and exits nonzero (end-to-end against the real sidecars).
  * ambiguous attribution — a `readArray(<unknown>)` whose width cannot be resolved from source is an
                            `ambiguousAttribution` (unit test of the pure resolution path).
  * sibling overlap       — two function_instances claiming a common PC without an inline ancestor relationship
                            are `overlappingOwnership` (unit test of the pure detector); the real,
                            correctly-nested program produces none.
  * binding gap           — source/parent recovery produces concrete values, preserves the DWARF
                            stack-value distinction, and refuses a parameter left with no machine
                            meaning (which would make the function_instance's entry predicate unsatisfiable).
  * loop-derived offset   — a loop-carried reader offset resolves to the induction REGISTER recovered
                            from the loaded image; an ambiguous or non-zero-initialized candidate is
                            refused rather than guessed (unit tests of the pure analysis).

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
           "--runtime-c", args.runtime_c, "--elf", args.elf, "--objdump", args.objdump] + extra
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
                                 ["const x = readArray(32, d, function_instance);"], {})
    check("ambiguous: a resolvable width is NOT a defect",
          resolved == ("ssz_raw.readArray", ("32",)), repr(resolved))


def test_sibling_overlap(gen, args, tmp):
    function_instances = [
        {"parentIdx": None, "regions": [{"start": 0x1000, "size": 0x40}], "qualified": "a"},
        {"parentIdx": None, "regions": [{"start": 0x1020, "size": 0x40}], "qualified": "b"},  # overlaps a
        {"parentIdx": 0, "regions": [{"start": 0x1000, "size": 0x10}], "qualified": "child"},  # nested in a
    ]
    defs = gen.sibling_overlap_defects(function_instances)
    kinds = [d["kind"] for d in defs]
    check("overlap: sibling PC clash surfaced", "overlappingOwnership" in kinds, str(kinds))
    check("overlap: nested child is NOT flagged against its parent",
          all({d["firstIdx"], d["secondIdx"]} != {0, 2} for d in defs))

    outj = os.path.join(tmp, "canonical.json")
    rc, _ = run_generator(args, ["--map", args.map, "--out-json", outj])
    check("overlap: real program generates cleanly", rc == 0 and os.path.exists(outj), f"rc={rc}")
    if os.path.exists(outj):
        real = gen.sibling_overlap_defects(json.load(open(outj))["function_instances"])
        check("overlap: detector finds none on the real function_instances", real == [], str(real))


def test_binding_recovery(gen):
    lines = ["const x = readU64(data, 16);", "const bytes = bytesAt(data, offset, 8);"]
    function_instances = [
        {"qualified": "ssz_raw.readU64", "kind": "inlined", "callLine": 1,
         "callColumn": 11, "parentIdx": None, "specialization": [],
         "bindings": [("offset", "callerProvided", -1, 0)]},
        {"qualified": "ssz_raw.bytesAt", "kind": "inlined", "callLine": 2,
         "callColumn": 15, "parentIdx": 0, "specialization": [],
         "bindings": [("offset", "callerProvided", -1, 0),
                      ("len", "callerProvided", -1, 0)]},
    ]
    effective, recovered, derived = gen.recover_missing_bindings(function_instances, lines, {}, {})
    check("binding: source literal is concrete", effective[0] == [("offset", "const", -1, 16)],
          repr(effective[0]))
    check("binding: parent forwarding and literal length are concrete",
          effective[1] == [("offset", "const", -1, 16), ("len", "const", -1, 8)],
          repr(effective[1]))
    check("binding: all three recoveries are audited", len(recovered) == 3, repr(recovered))
    check("binding: nothing is loop-derived here", derived == [], repr(derived))
    check("binding: breg stack_value is a value, not a memory location",
          gen.decode_loc_expr("DW_OP_breg27 (s11): 48; DW_OP_stack_value") ==
          ("bregValue", 27, 48))
    check("binding: DWARF constant value is preserved",
          gen.decode_loc_expr("DW_OP_constu: 504; DW_OP_stack_value") == ("const", -1, 504))

    broken = [{"qualified": "ssz_raw.readU64", "kind": "inlined", "callLine": 1,
               "callColumn": 11, "parentIdx": None, "specialization": [],
               "bindings": [("different_name", "callerProvided", -1, 0)]}]
    try:
        gen.recover_missing_bindings(broken, lines, {}, {})
        refused = False
    except SystemExit as err:
        refused = "no machine meaning after recovery" in str(err)
    check("binding: a parameter with no machine meaning fails generation", refused)


# A minimal loop with ONE zero-initialized `+stride` induction register, in the objdump shape
# `disassemble` produces: {pc: (mnemonic, operands, resolved-comment)}.
#   100: li   s7,0            preheader: the induction variable starts at zero
#   104: addi a0,a0,-1        loop header (target of the back edge)
#   108: bnez a0,120 <end>    the function_instance's entry pc
#   10c: addi s7,s7,44        the induction step, by the pinned source stride
#   110: j    104 <header>    back edge
#   120: ret
def _loop_insns(extra=None):
    insns = {
        0x100: ("li", "s7,0", None),
        0x104: ("addi", "a0,a0,-1", None),
        0x108: ("bnez", "a0,120 <end>", None),
        0x10c: ("addi", "s7,s7,44", None),
        0x110: ("j", "104 <header>", None),
        0x120: ("ret", "", None),
    }
    insns.update(extra or {})
    return insns


LOOP_SRC = [
    "fn decodeWithdrawals(alloc: std.mem.Allocator, data: []const u8) DecodeError![]RawWithdrawal {",
    "    const offset = index * WITHDRAWAL_SIZE;",
    "    .validator_index = try readU64(data, offset + 8),",
]


def test_loop_induction_recovery(gen):
    """A loop-carried reader offset resolves to the induction REGISTER, not to a hole.

    `readU64(data, offset + 8)` inside `for (…) |*entry, index| { const offset = index *
    WITHDRAWAL_SIZE; … }` has no DWARF location. Emitting it as an absent/unlocated row would make the
    function_instance's generated entry predicate unsatisfiable, so the generator recovers the register the
    compiled loop keeps `index * WITHDRAWAL_SIZE` in — or fails."""
    consts = {"WITHDRAWAL_SIZE": 44}
    src = gen.loop_offset_source("offset + 8", 3, LOOP_SRC, consts)
    check("loop: the source relation is read from the pinned Zig", src == ("offset", 44, "WITHDRAWAL_SIZE", 8),
          repr(src))
    check("loop: an unrelated expression is not a loop relation",
          gen.loop_offset_source("data.len", 3, LOOP_SRC, consts) is None)

    insns = _loop_insns()
    preds = gen._direct_preds(insns)
    found, why = gen.loop_stride_register(0x108, 44, insns, preds)
    check("loop: the +stride induction register is recovered", found == (23, 0x104, 0x110),
          repr(found) + " " + repr(why))

    # A second register stepping by the same stride, also zero on entry, is AMBIGUOUS: two candidates
    # mean the generator cannot say which one holds the offset, so it refuses rather than picking one.
    ambiguous = _loop_insns({
        0x0fc: ("li", "s9,0", None),
        0x114: ("addi", "s9,s9,44", None),
        0x110: ("j", "114 <step2>", None),
        0x118: ("j", "104 <header>", None),
    })
    del ambiguous[0x100]
    ambiguous[0x0fc] = ("li", "s9,0", None)
    ambiguous[0x100] = ("li", "s7,0", None)
    found2, why2 = gen.loop_stride_register(0x108, 44, ambiguous, gen._direct_preds(ambiguous))
    check("loop: two candidate induction registers are refused, not guessed",
          found2 is None and "exactly one" in (why2 or ""), repr(why2))

    # A register stepping by the stride but NOT zero on entry is not the offset.
    not_zeroed = _loop_insns({0x100: ("addi", "s7,a0,7", None)})
    found3, why3 = gen.loop_stride_register(0x108, 44, not_zeroed, gen._direct_preds(not_zeroed))
    check("loop: an induction register that is not zero on entry is refused",
          found3 is None, repr(found3))

    # And the recovery is wired into the binding pass: the row becomes `derived`, with the register,
    # stride and constant audited.
    function_instances = [{"qualified": "ssz_raw.readU64", "kind": "inlined", "callLine": 3, "callColumn": 1,
            "parentIdx": None, "specialization": [], "entryPc": 0x108,
            "bindings": [("offset", "callerProvided", -1, 0)]}]
    effective, recovered, derived = gen.recover_missing_bindings(function_instances, LOOP_SRC, consts, insns)
    check("loop: the row is `derived`, carrying the register and the constant",
          effective[0] == [("offset", "derived", 23, 8)], repr(effective[0]))
    check("loop: the derivation is audited with stride, source expression and loop",
          derived == [(0, "offset", 23, 44, 8, "offset + 8", "WITHDRAWAL_SIZE", 0x104, 0x110)],
          repr(derived))
    check("loop: the recovery is recorded under its own rule",
          [r[2] for r in recovered] == ["loopInductionOffset"], repr(recovered))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--generator", required=True)
    for k in ["readelf", "decoder", "allocator", "sink", "runtime", "source", "runtime-c", "map",
              "elf", "objdump"]:
        ap.add_argument("--" + k, required=True)
    args = ap.parse_args()
    args.runtime_c = args.runtime_c  # argparse stores --runtime-c as runtime_c
    gen = load_generator(args.generator)

    with tempfile.TemporaryDirectory() as tmp:
        print("unmapped region:");       test_unmapped_region(args, tmp)
        print("ambiguous attribution:"); test_ambiguous_width(gen)
        print("sibling overlap:");       test_sibling_overlap(gen, args, tmp)
        print("binding recovery:");      test_binding_recovery(gen)
        print("loop-derived offsets:");  test_loop_induction_recovery(gen)

    if FAILURES:
        print(f"\nGENERATOR DEFECT TESTS FAILED: {FAILURES}", file=sys.stderr)
        sys.exit(1)
    print("\nALL GENERATOR DEFECT TESTS PASSED")


if __name__ == "__main__":
    main()
