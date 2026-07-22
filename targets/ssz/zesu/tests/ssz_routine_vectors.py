#!/usr/bin/env python3
"""Typed per-routine validation vectors for the Row B direct-source contract check.

Unlike `ssz_contract_corpus.py` (whole-input `ssz_raw.decode` cases), this generates *typed* input
vectors for individual catalog routines, each with the exact expected success value or the exact local
error (`invalidSsz` / `unknownFork` / `outOfMemory`). The same vectors drive:

  * the host probe (`ssz_contract_probe.zig --routine-vectors`), which calls the real private routine
    through the validation overlay and must match the expected value/error exactly; and
  * a Lean check (`RoutineMeaningVectors.lean`), which evaluates the handwritten `meaning*` and must
    match the same expected value/error by `native_decide`.

So expected ≡ Zig-routine ∧ expected ≡ Lean-meaning ⇒ Zig-routine ≡ handwritten meaning, per routine,
at the exact-value / exact-error granularity item 3 requires. Expected values are a small deterministic
SSZ reference computed here; a divergence in either runner is a real finding.

This module covers the leaf readers (scalar / slice / predicate). Container / option / collection /
runtime routines are added by their own vector groups.

JSONL row schema (`ssz-routine-vectors-v1`), keys sorted, one line per case:
  {"schema","id","routine","args":{...typed...},
   "expect":{"kind":"value"|"error"|"gap","value":<typed>|null,"error":<label>|null,"reason":<str>?},
   "coverage":<category>}

Value encodings (never host pointers; input-relative where slices):
  * scalar reads  -> {"nat": <int>}
  * slice reads   -> {"bytes": "<hex>"}          (the input subrange, so it is input-relative)
  * predicates    -> {"bool": true|false}
  * unit checks   -> {"ok": true}
"""
import argparse, json, sys

SCHEMA = "ssz-routine-vectors-v1"
ZESU_PIN = "codygunton/zesu@96f1621468ba54755d653f19cbc9704e789be001"

INVALID = {"kind": "error", "value": None, "error": "invalidSsz"}


def val_nat(n):
    # Decimal STRING so values above i64 (e.g. readU64 of all-0xff = 2^64-1, and readU256 later) survive
    # JSON parsing in every runner.
    return {"kind": "value", "value": {"nat": str(n)}, "error": None}


def val_bytes(b: bytes):
    return {"kind": "value", "value": {"bytes": b.hex()}, "error": None}


def val_bool(x: bool):
    return {"kind": "value", "value": {"bool": x}, "error": None}


def val_ok():
    return {"kind": "value", "value": {"ok": True}, "error": None}


# --- deterministic SSZ reference (matches both the Zig routine and the handwritten Lean meaning) -----

def ref_read_uint_le(data: bytes, offset: int, width: int):
    """readU32/readU64: little-endian unsigned of `width` bytes, or invalidSsz on out-of-bounds."""
    if offset + width > len(data):
        return INVALID
    return val_nat(int.from_bytes(data[offset:offset + width], "little"))


def ref_read_array(data: bytes, offset: int, n: int):
    """readArray(N)/bytesAt: the input subrange [offset, offset+n), or invalidSsz. Non-wrapping bound
    `offset <= len and n <= len - offset` (the pinned source's exact `bytesAt` predicate)."""
    if offset > len(data) or n > len(data) - offset:
        return INVALID
    return val_bytes(data[offset:offset + n])


def ref_require_u32_length(data: bytes):
    """requireU32Length: ok iff the slice length fits in a u32."""
    return val_ok() if len(data) <= 0xFFFFFFFF else INVALID


def ref_has_exact_ere_prefix(data: bytes):
    """hasExactErePrefix: true iff the leading u32 equals len-4 (never errors)."""
    if len(data) < 4:
        return val_bool(False)
    declared = int.from_bytes(data[0:4], "little")
    return val_bool(declared == len(data) - 4)


# --- vector construction ----------------------------------------------------------------------------

def rows():
    out = []

    def add(routine, args, expect, coverage):
        out.append({
            "schema": SCHEMA, "id": f"{routine}/{coverage}/{len(out)}",
            "routine": routine, "args": args, "expect": expect, "coverage": coverage,
        })

    # Patterned little-endian payloads so a wrong-endianness read is caught (0x01,0x02,... low byte
    # first => small distinctive values).
    pat32 = bytes(range(1, 33))          # 0x01..0x20
    pat8 = bytes([0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88])

    # readU32 / readOffset (readOffset == readU32 widened; same value, same bound).
    for routine in ("ssz_raw.readU32", "ssz_raw.readOffset"):
        add(routine, {"data": pat8.hex(), "offset": 0}, ref_read_uint_le(pat8, 0, 4), "endian-pattern")
        add(routine, {"data": pat8.hex(), "offset": 4}, ref_read_uint_le(pat8, 4, 4), "endian-pattern")
        add(routine, {"data": (b"\x00" * 4).hex(), "offset": 0}, val_nat(0), "boundary-length")
        add(routine, {"data": (b"\xff" * 4).hex(), "offset": 0}, val_nat(0xFFFFFFFF), "boundary-length")
        add(routine, {"data": (b"\x01\x02\x03").hex(), "offset": 0}, INVALID, "offset-failure")  # 3 < 4
        add(routine, {"data": pat8.hex(), "offset": 5}, INVALID, "offset-failure")               # 5+4>8

    # readU64
    add("ssz_raw.readU64", {"data": pat8.hex(), "offset": 0}, ref_read_uint_le(pat8, 0, 8), "endian-pattern")
    add("ssz_raw.readU64", {"data": (b"\x00" * 8).hex(), "offset": 0}, val_nat(0), "boundary-length")
    add("ssz_raw.readU64", {"data": (b"\xff" * 8).hex(), "offset": 0}, val_nat((1 << 64) - 1), "boundary-length")
    add("ssz_raw.readU64", {"data": (b"\x01" * 7).hex(), "offset": 0}, INVALID, "offset-failure")   # 7 < 8
    add("ssz_raw.readU64", {"data": pat8.hex(), "offset": 1}, INVALID, "offset-failure")            # 1+8>8

    # readArray[N] for each concrete width.
    for n in (20, 32, 48, 65, 96, 256):
        routine = f"ssz_raw.readArray[{n}]"
        body = bytes((i * 7 + 3) & 0xFF for i in range(n))
        add(routine, {"width": n, "data": body.hex(), "offset": 0}, ref_read_array(body, 0, n), "boundary-length")
        add(routine, {"width": n, "data": (body + b"XY").hex(), "offset": 2},
            ref_read_array(body + b"XY", 2, n), "boundary-length")             # exact fit at offset 2
        add(routine, {"width": n, "data": body[:-1].hex(), "offset": 0}, INVALID, "offset-failure")  # N-1 < N

    # bytesAt (runtime len).
    for (dl, off, ln) in [(8, 0, 8), (8, 2, 4), (8, 0, 0), (8, 8, 0), (8, 4, 5), (8, 9, 0), (0, 0, 0)]:
        body = bytes((i + 1) & 0xFF for i in range(dl))
        add("ssz_raw.bytesAt", {"data": body.hex(), "offset": off, "len": ln},
            ref_read_array(body, off, ln), "boundary-length" if off + ln <= dl else "offset-failure")

    # requireU32Length (short slices always fit; the >4 GiB case is an explicit gap, below).
    for dl in (0, 1, 4, 100):
        body = b"\x00" * dl
        add("ssz_raw.requireU32Length", {"data": body.hex()}, ref_require_u32_length(body), "boundary-length")
    out.append({
        "schema": SCHEMA, "id": "ssz_raw.requireU32Length/gap/oversize",
        "routine": "ssz_raw.requireU32Length", "args": {"data_len_gt_u32": True},
        "expect": {"kind": "gap", "value": None, "error": None,
                   "reason": "a >4 GiB input is infeasible to materialize on the host; the u32-overflow "
                             "reject arm is exercised only in the Lean meaning check"},
        "coverage": "boundary-length",
    })

    # hasExactErePrefix (never errors).
    for (name, body) in [
        ("empty", b""),
        ("too-short", b"\x01\x02\x03"),
        ("exact", (4).to_bytes(4, "little") + b"ABCD"),
        ("mismatch", (7).to_bytes(4, "little") + b"ABCD"),
    ]:
        add("ssz_raw.hasExactErePrefix", {"data": body.hex()}, ref_has_exact_ere_prefix(body), "raw-ere")

    return out


def _lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def emit_lean(all_rows) -> str:
    """Bake the leaf vectors into a Lean data module for the `native_decide` meaning check. Gaps are
    omitted (their arm is not value-checkable). Groups: scalar reads, slice reads, unit checks,
    predicates — matching the handwritten meaning families."""
    scalar, slice_, requ, ere = [], [], [], []
    for r in all_rows:
        if r["expect"]["kind"] == "gap":
            continue
        rt, a, e = r["routine"], r["args"], r["expect"]
        if rt in ("ssz_raw.readU32", "ssz_raw.readOffset", "ssz_raw.readU64"):
            v = f'some {e["value"]["nat"]}' if e["kind"] == "value" else "none"
            scalar.append(f'({_lean_str(rt)}, {_lean_str(r["id"])}, {_lean_str(a["data"])}, {a["offset"]}, {v})')
        elif rt == "ssz_raw.bytesAt":
            v = f'some {_lean_str(e["value"]["bytes"])}' if e["kind"] == "value" else "none"
            slice_.append(f'({_lean_str(rt)}, {_lean_str(r["id"])}, {_lean_str(a["data"])}, {a["offset"]}, {a["len"]}, {v})')
        elif rt.startswith("ssz_raw.readArray["):
            v = f'some {_lean_str(e["value"]["bytes"])}' if e["kind"] == "value" else "none"
            slice_.append(f'({_lean_str(rt)}, {_lean_str(r["id"])}, {_lean_str(a["data"])}, {a["offset"]}, {a["width"]}, {v})')
        elif rt == "ssz_raw.requireU32Length":
            requ.append(f'({_lean_str(r["id"])}, {_lean_str(a["data"])}, {"true" if e["kind"] == "value" else "false"})')
        elif rt == "ssz_raw.hasExactErePrefix":
            ere.append(f'({_lean_str(r["id"])}, {_lean_str(a["data"])}, {"true" if e["value"]["bool"] else "false"})')

    def block(name, ty, items):
        body = ",\n   ".join(items) if items else ""
        return f"def {name} : List ({ty}) :=\n  [{body}]\n"

    L = [
        "-- GENERATED FILE: produced by targets/ssz/zesu/tests/ssz_routine_vectors.py --out-lean. DO NOT EDIT.",
        "-- Typed per-routine leaf vectors baked for the handwritten-meaning agreement check",
        "-- (BinaryFv/SSZ/Zesu/Validation/RoutineMeaningVectors.lean). `some`=expected value, `none`=invalidSsz.",
        "namespace BinaryFv.SSZ.Zesu.Validation.GeneratedRoutineVectors",
        block("scalarVectors", "String × String × String × Nat × Option Nat", scalar),
        block("sliceVectors", "String × String × String × Nat × Nat × Option String", slice_),
        block("requireU32Vectors", "String × String × Bool", requ),
        block("erePrefixVectors", "String × String × Bool", ere),
        "end BinaryFv.SSZ.Zesu.Validation.GeneratedRoutineVectors",
    ]
    return "\n".join(L) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    ap.add_argument("--out-lean")
    args = ap.parse_args()
    all_rows = rows()
    lines = [json.dumps(r, sort_keys=True, separators=(",", ":")) for r in all_rows]
    text = "\n".join(lines) + "\n"
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
    elif not args.out_lean:
        sys.stdout.write(text)
    if args.out_lean:
        with open(args.out_lean, "w") as f:
            f.write(emit_lean(all_rows))


if __name__ == "__main__":
    main()
