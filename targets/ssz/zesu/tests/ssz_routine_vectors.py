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

This module covers the leaf readers (scalar / slice / predicate), the two non-allocating option
decoders (`decodeOptionalU64`, `decodeOptionalBlobSchedule`), and the three non-allocating containers
(`decodeForkActivation`, `decodeForkConfig`, `decodeChainConfig`). Allocating collections / containers
and the runtime routines are added by their own vector groups.

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
    # Decimal STRING so values above i64 (e.g. readU64 of all-0xff = 2^64-1, readU256 = 2^256-1) survive
    # JSON parsing in every runner.
    return {"kind": "value", "value": {"nat": str(n)}, "error": None}


def val_bytes(b: bytes):
    return {"kind": "value", "value": {"bytes": b.hex()}, "error": None}


def val_bool(x: bool):
    return {"kind": "value", "value": {"bool": x}, "error": None}


def val_ok():
    return {"kind": "value", "value": {"ok": True}, "error": None}


def val_opt_u64(v):
    """decodeOptionalU64 result: `None` (SSZ `none`) or an int (`some value`)."""
    inner = None if v is None else {"u64": str(v)}
    return {"kind": "value", "value": {"opt": inner}, "error": None}


def val_opt_blob(v):
    """decodeOptionalBlobSchedule result: `None`, or a `(target, max, bfuf)` triple of u64s."""
    inner = None if v is None else {"target": str(v[0]), "max": str(v[1]), "bfuf": str(v[2])}
    return {"kind": "value", "value": {"opt": inner}, "error": None}


UNKNOWN_FORK = {"kind": "error", "value": None, "error": "unknownFork"}


def val_scalars(xs):
    """A container/struct value flattened to a fixed-order list of u64 scalars (decimal strings). This
    is a lossless encoding of the decoded struct: every u64 field, with each option preceded by a 0/1
    presence bit. Both runners flatten in the SAME field order (documented at each container below)."""
    return {"kind": "value", "value": {"scalars": [str(x) for x in xs]}, "error": None}


# --- SSZ container fixture builders (mirror ssz_differential_audit.py; kept inline so this generator
# stays self-contained for the Nix probe invocation). Values are triple-checked by probe + Lean. ------

def _u32(v):
    return v.to_bytes(4, "little")


def _u64(v):
    return v.to_bytes(8, "little")


def fa_bytes(block_number, timestamp):
    """decodeForkActivation input: two u32 offsets (fixed_size 8), then two optional u64 regions."""
    block = b"" if block_number is None else _u64(block_number)
    time = b"" if timestamp is None else _u64(timestamp)
    return _u32(8) + _u32(8 + len(block)) + block + time


def fc_bytes(fork, activation, blob_schedule):
    """decodeForkConfig input: u64 fork, two u32 offsets (fixed_size 16), activation, blob region."""
    blob = b"" if blob_schedule is None else b"".join(_u64(v) for v in blob_schedule)
    return _u64(fork) + _u32(16) + _u32(16 + len(activation)) + activation + blob


def cc_bytes(chain_id, fork_config):
    """decodeChainConfig input: u64 chain_id, one u32 offset (fixed_size 12), then the fork config."""
    return _u64(chain_id) + _u32(12) + fork_config


# Flatteners: the exact field order both the Zig probe and the Lean meaning reproduce.
def flat_opt(v):                                        # option -> [presence, value|0]
    return [0, 0] if v is None else [1, v]


def flat_fa(block_number, timestamp):                   # ForkActivation -> 4 scalars
    return flat_opt(block_number) + flat_opt(timestamp)


def flat_blob(bs):                                      # Option BlobSchedule -> [presence, t, m, b]
    return [0, 0, 0, 0] if bs is None else [1, bs[0], bs[1], bs[2]]


def flat_fc(fork, block_number, timestamp, blob):       # ForkConfig -> 9 scalars
    return [fork] + flat_fa(block_number, timestamp) + flat_blob(blob)


def flat_cc(chain_id, fork, block_number, timestamp, blob):  # ChainConfig -> 10 scalars
    return [chain_id] + flat_fc(fork, block_number, timestamp, blob)


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


def ref_canonical_offsets(data_len: int, fixed_size: int, offsets: list):
    """requireCanonicalOffsets, transcribed from the source in its exact order: the slice must be at
    least `fixed_size`, the table must be non-empty, its first entry must *equal* `fixed_size`, and
    entries must be nondecreasing from there while staying within the slice."""
    if data_len < fixed_size or len(offsets) == 0 or offsets[0] != fixed_size:
        return INVALID
    previous = fixed_size
    for off in offsets:
        if off < previous or off > data_len:
            return INVALID
        previous = off
    return val_ok()


def ref_has_exact_ere_prefix(data: bytes):
    """hasExactErePrefix: true iff the leading u32 equals len-4 (never errors)."""
    if len(data) < 4:
        return val_bool(False)
    declared = int.from_bytes(data[0:4], "little")
    return val_bool(declared == len(data) - 4)


BLOB_SCHEDULE_SIZE = 24  # three little-endian u64 fields (target, max, base_fee_update_fraction)


def ref_optional_u64(data: bytes):
    """decodeOptionalU64: len 0 -> none; len 8 -> some(u64 LE); any other length -> invalidSsz."""
    if len(data) == 0:
        return val_opt_u64(None)
    if len(data) == 8:
        return val_opt_u64(int.from_bytes(data, "little"))
    return INVALID


def ref_optional_blob(data: bytes):
    """decodeOptionalBlobSchedule: len 0 -> none; len 24 -> some(three u64 LE fields); else invalidSsz."""
    if len(data) == 0:
        return val_opt_blob(None)
    if len(data) == BLOB_SCHEDULE_SIZE:
        target = int.from_bytes(data[0:8], "little")
        mx = int.from_bytes(data[8:16], "little")
        bfuf = int.from_bytes(data[16:24], "little")
        return val_opt_blob((target, mx, bfuf))
    return INVALID


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

    # readU256 (32-byte little-endian; the value encoding's `nat` carries the full u256 range).
    pat256 = bytes((i * 7 + 3) & 0xFF for i in range(32))
    add("ssz_raw.readU256", {"data": pat256.hex(), "offset": 0}, ref_read_uint_le(pat256, 0, 32), "endian-pattern")
    add("ssz_raw.readU256", {"data": (b"XY" + pat256).hex(), "offset": 2},
        ref_read_uint_le(b"XY" + pat256, 2, 32), "endian-pattern")                       # exact fit at offset 2
    add("ssz_raw.readU256", {"data": (b"\x00" * 32).hex(), "offset": 0}, val_nat(0), "boundary-length")
    add("ssz_raw.readU256", {"data": (b"\xff" * 32).hex(), "offset": 0}, val_nat((1 << 256) - 1), "boundary-length")
    add("ssz_raw.readU256", {"data": (b"\x00" * 31).hex(), "offset": 0}, INVALID, "offset-failure")   # 31 < 32
    add("ssz_raw.readU256", {"data": (b"\x11" * 33).hex(), "offset": 2}, INVALID, "offset-failure")    # 2+32>33

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

    # requireCanonicalOffsets: canonical prefix table (accept), wrong first offset, descending /
    # non-monotone, out-of-range, short slice, and empty table (all reject). Data content is
    # irrelevant (only its length matters), so a zero-filled slice of the right length is used.
    def canon(data_len, fixed_size, offsets, coverage):
        add("ssz_raw.requireCanonicalOffsets",
            {"data": (b"\x00" * data_len).hex(), "fixed_size": fixed_size, "offsets": offsets},
            ref_canonical_offsets(data_len, fixed_size, offsets), coverage)

    canon(16, 8, [8], "offset-canonical")             # first == fixed, within bounds
    canon(16, 8, [8, 12, 16], "offset-canonical")     # nondecreasing, last == len
    canon(16, 8, [8, 8], "offset-canonical")          # equal offsets are allowed (>= previous)
    canon(16, 8, [12], "offset-wrong-first")          # first (12) != fixed (8)
    canon(16, 8, [8, 12, 10], "offset-descending")    # 10 < previous 12
    canon(16, 8, [8, 20], "offset-out-of-range")      # 20 > len 16
    canon(4, 8, [8], "offset-short-slice")            # len 4 < fixed 8
    canon(16, 8, [], "offset-empty-table")            # empty table

    # decodeOptionalU64: absent (0 bytes), present (exactly 8), malformed (any other length).
    add("ssz_raw.decodeOptionalU64", {"data": b"".hex()}, ref_optional_u64(b""), "option-absent")
    add("ssz_raw.decodeOptionalU64", {"data": pat8.hex()}, ref_optional_u64(pat8), "option-present")
    add("ssz_raw.decodeOptionalU64", {"data": (b"\x00" * 8).hex()}, ref_optional_u64(b"\x00" * 8), "option-present")
    add("ssz_raw.decodeOptionalU64", {"data": (b"\xff" * 8).hex()}, ref_optional_u64(b"\xff" * 8), "option-present")
    add("ssz_raw.decodeOptionalU64", {"data": (b"\x11" * 7).hex()}, INVALID, "option-malformed")   # 7 != 0,8
    add("ssz_raw.decodeOptionalU64", {"data": (b"\x11" * 9).hex()}, INVALID, "option-malformed")   # 9 != 0,8

    # decodeOptionalBlobSchedule: absent (0), present (exactly 24), malformed (any other length).
    blob24 = bytes((i * 5 + 1) & 0xFF for i in range(BLOB_SCHEDULE_SIZE))
    add("ssz_raw.decodeOptionalBlobSchedule", {"data": b"".hex()}, ref_optional_blob(b""), "option-absent")
    add("ssz_raw.decodeOptionalBlobSchedule", {"data": blob24.hex()}, ref_optional_blob(blob24), "option-present")
    add("ssz_raw.decodeOptionalBlobSchedule", {"data": (b"\x00" * 24).hex()}, ref_optional_blob(b"\x00" * 24), "option-present")
    add("ssz_raw.decodeOptionalBlobSchedule", {"data": (b"\xff" * 24).hex()}, ref_optional_blob(b"\xff" * 24), "option-present")
    add("ssz_raw.decodeOptionalBlobSchedule", {"data": (b"\x22" * 23).hex()}, INVALID, "option-malformed")  # 23
    add("ssz_raw.decodeOptionalBlobSchedule", {"data": (b"\x22" * 25).hex()}, INVALID, "option-malformed")  # 25
    add("ssz_raw.decodeOptionalBlobSchedule", {"data": (b"\x22" * 16).hex()}, INVALID, "option-malformed")  # 16

    # --- Non-allocating containers: decodeForkActivation / decodeForkConfig / decodeChainConfig -------
    # Value = flattened u64 scalar list (field order in flat_fa/flat_fc/flat_cc above). These exercise
    # the offset-table + optional composition, and (fork config / chain config) the unknownFork arm and
    # its ordering: the offset-table check precedes the fork-bound check, which precedes child decodes.

    # decodeForkActivation
    add("ssz_raw.decodeForkActivation", {"data": fa_bytes(None, None).hex()}, val_scalars(flat_fa(None, None)), "container-forkactivation")
    add("ssz_raw.decodeForkActivation", {"data": fa_bytes(5, None).hex()}, val_scalars(flat_fa(5, None)), "container-forkactivation")
    add("ssz_raw.decodeForkActivation", {"data": fa_bytes(None, 7).hex()}, val_scalars(flat_fa(None, 7)), "container-forkactivation")
    add("ssz_raw.decodeForkActivation", {"data": fa_bytes(11, 22).hex()}, val_scalars(flat_fa(11, 22)), "container-forkactivation")
    add("ssz_raw.decodeForkActivation", {"data": (b"\x00" * 4).hex()}, INVALID, "container-malformed")          # < 8 bytes
    add("ssz_raw.decodeForkActivation", {"data": (_u32(9) + _u32(9)).hex()}, INVALID, "container-malformed")    # first offset != 8
    add("ssz_raw.decodeForkActivation", {"data": (_u32(8) + _u32(15) + b"\x00" * 7).hex()}, INVALID, "container-malformed")  # 7-byte option region

    # decodeForkConfig
    add("ssz_raw.decodeForkConfig", {"data": fc_bytes(20, fa_bytes(None, None), (1, 2, 3)).hex()},
        val_scalars(flat_fc(20, None, None, (1, 2, 3))), "container-forkconfig")
    add("ssz_raw.decodeForkConfig", {"data": fc_bytes(0, fa_bytes(4, 8), None).hex()},
        val_scalars(flat_fc(0, 4, 8, None)), "container-forkconfig")
    add("ssz_raw.decodeForkConfig", {"data": fc_bytes(20, fa_bytes(1, 2), (9, 9, 9)).hex()},
        val_scalars(flat_fc(20, 1, 2, (9, 9, 9))), "container-forkconfig")
    add("ssz_raw.decodeForkConfig", {"data": fc_bytes(21, fa_bytes(None, None), (1, 2, 3)).hex()},
        UNKNOWN_FORK, "fork-unknown")                                                                          # fork 21 > 20
    add("ssz_raw.decodeForkConfig", {"data": fc_bytes(255, fa_bytes(1, 2), None).hex()},
        UNKNOWN_FORK, "fork-unknown")                                                                          # fork 255
    # Ordering: fork 21 with a malformed CHILD still yields unknownFork (bound checked before children).
    add("ssz_raw.decodeForkConfig", {"data": fc_bytes(21, (_u32(8) + _u32(15) + b"\x00" * 7), (1, 2, 3)).hex()},
        UNKNOWN_FORK, "fork-ordering")
    # Ordering: a bad offset table with fork 21 yields invalidSsz (offset check precedes the bound).
    add("ssz_raw.decodeForkConfig", {"data": (_u64(21) + _u32(17) + _u32(17)).hex()},
        INVALID, "fork-ordering")                                                                              # first offset 17 != 16
    add("ssz_raw.decodeForkConfig", {"data": (b"\x00" * 8).hex()}, INVALID, "container-malformed")             # < 16 bytes

    # decodeChainConfig (nests a fork config; unknownFork propagates from the child)
    add("ssz_raw.decodeChainConfig", {"data": cc_bytes(1, fc_bytes(20, fa_bytes(None, None), (1, 2, 3))).hex()},
        val_scalars(flat_cc(1, 20, None, None, (1, 2, 3))), "container-chainconfig")
    add("ssz_raw.decodeChainConfig", {"data": cc_bytes(7, fc_bytes(0, fa_bytes(4, 8), None)).hex()},
        val_scalars(flat_cc(7, 0, 4, 8, None)), "container-chainconfig")
    add("ssz_raw.decodeChainConfig", {"data": cc_bytes(1, fc_bytes(21, fa_bytes(None, None), (1, 2, 3))).hex()},
        UNKNOWN_FORK, "fork-unknown")                                                                          # child fork 21
    add("ssz_raw.decodeChainConfig", {"data": (b"\x00" * 8).hex()}, INVALID, "container-malformed")            # < 12 bytes

    return out


def _lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def emit_lean(all_rows) -> str:
    """Bake the leaf vectors into a Lean data module for the `native_decide` meaning check. Gaps are
    omitted (their arm is not value-checkable). Groups: scalar reads, slice reads, unit checks,
    predicates — matching the handwritten meaning families."""
    scalar, slice_, requ, ere, optu64, optblob, canon = [], [], [], [], [], [], []
    fa_c, fc_c, cc_c = [], [], []

    def container_row(r, a, e):
        # expected : Option (List Nat) × String -- (some scalars, "") on success; (none, label) on error.
        if e["kind"] == "value":
            exp = f'(some [{", ".join(e["value"]["scalars"])}], "")'
        else:
            exp = f'(none, {_lean_str(e["error"])})'
        return f'({_lean_str(r["id"])}, {_lean_str(a["data"])}, {exp})'

    for r in all_rows:
        if r["expect"]["kind"] == "gap":
            continue
        rt, a, e = r["routine"], r["args"], r["expect"]
        if rt in ("ssz_raw.readU32", "ssz_raw.readOffset", "ssz_raw.readU64", "ssz_raw.readU256"):
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
        elif rt == "ssz_raw.requireCanonicalOffsets":
            offs = "[" + ", ".join(str(o) for o in a["offsets"]) + "]"
            canon.append(f'({_lean_str(r["id"])}, {_lean_str(a["data"])}, {a["fixed_size"]}, {offs}, '
                         f'{"true" if e["kind"] == "value" else "false"})')
        elif rt == "ssz_raw.hasExactErePrefix":
            ere.append(f'({_lean_str(r["id"])}, {_lean_str(a["data"])}, {"true" if e["value"]["bool"] else "false"})')
        elif rt == "ssz_raw.decodeOptionalU64":
            # `none` = error (only invalidSsz is reachable); `some none` = SSZ none; `some (some v)`.
            if e["kind"] != "value":
                ev = "none"
            else:
                inner = e["value"]["opt"]
                ev = "some none" if inner is None else f'some (some {inner["u64"]})'
            optu64.append(f'({_lean_str(r["id"])}, {_lean_str(a["data"])}, {ev})')
        elif rt == "ssz_raw.decodeOptionalBlobSchedule":
            if e["kind"] != "value":
                ev = "none"
            else:
                inner = e["value"]["opt"]
                ev = "some none" if inner is None else \
                    f'some (some ({inner["target"]}, {inner["max"]}, {inner["bfuf"]}))'
            optblob.append(f'({_lean_str(r["id"])}, {_lean_str(a["data"])}, {ev})')
        elif rt == "ssz_raw.decodeForkActivation":
            fa_c.append(container_row(r, a, e))
        elif rt == "ssz_raw.decodeForkConfig":
            fc_c.append(container_row(r, a, e))
        elif rt == "ssz_raw.decodeChainConfig":
            cc_c.append(container_row(r, a, e))

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
        block("canonicalOffsetsVectors", "String × String × Nat × List Nat × Bool", canon),
        block("erePrefixVectors", "String × String × Bool", ere),
        block("optionalU64Vectors", "String × String × Option (Option Nat)", optu64),
        block("optionalBlobVectors", "String × String × Option (Option (Nat × Nat × Nat))", optblob),
        block("forkActivationVectors", "String × String × (Option (List Nat) × String)", fa_c),
        block("forkConfigVectors", "String × String × (Option (List Nat) × String)", fc_c),
        block("chainConfigVectors", "String × String × (Option (List Nat) × String)", cc_c),
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
