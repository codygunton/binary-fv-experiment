import BinaryFv.SSZ.Zesu.Contracts.Leaves
import BinaryFv.SSZ.Zesu.Contracts.Options
import BinaryFv.SSZ.Zesu.Validation.GeneratedRoutineVectors

/-!
# Kernel-checked per-routine meaning agreement (Row B, item 3)

For every typed leaf-routine vector (`ssz-routine-vectors-v1`), the handwritten `meaning*` produces the
vector's exact expected success value or exact local error — checked in the kernel by `native_decide`.
The host probe checks the same vectors against the real Zig routine (`--routine-vectors`), so together
`expected ≡ Zig-routine` (probe) and `expected ≡ meaning` (here) give `Zig-routine ≡ handwritten meaning`
per routine, at the exact-value / exact-error granularity Row B requires.

This is a validation module — falsification evidence, not a proof premise — and is not imported by the
theorem umbrella `BinaryFv`. Leaf readers fail only with `invalidSsz`, so a `none` expectation pins that
exact error (there is only one).
-/

namespace BinaryFv.SSZ.Zesu.Validation

open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Validation.GeneratedRoutineVectors

/-- A single hex digit's value (`16` for a non-digit, which `hexToBytes` never receives). -/
private def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then 10 + (c.toNat - 'a'.toNat)
  else 16

/-- Decode a hex string to bytes (iterative, so large cases run without deep recursion). -/
def hexToBytes (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  let mut i := 0
  while _h : i + 1 < cs.size do
    out := out.push (UInt8.ofNat (hexVal cs[i]! * 16 + hexVal cs[i + 1]!))
    i := i + 2
  return out

/-- The scalar-read meaning selected by routine name, as an `Option Nat` (`none` = `invalidSsz`). -/
def scalarMeaning (routine : String) (bytes : ByteArray) (offset : Nat) : Option Nat :=
  if routine == "ssz_raw.readU32" then (meaningReadU32 bytes offset).toOption.map UInt32.toNat
  else if routine == "ssz_raw.readU64" then (meaningReadU64 bytes offset).toOption.map UInt64.toNat
  else if routine == "ssz_raw.readU256" then (meaningReadU256 bytes offset).toOption.map BitVec.toNat
  else (meaningReadOffset bytes offset).toOption

/-- The slice-read meaning selected by routine name (`bytesAt` vs `readArray[N]`, `len` = the width). -/
def sliceMeaning (routine : String) (bytes : ByteArray) (offset len : Nat) : Option ByteArray :=
  if routine == "ssz_raw.bytesAt" then (meaningBytesAt bytes offset len).toOption
  else (meaningReadArray len bytes offset).toOption

/-- **Scalar reads:** `readU32`/`readOffset`/`readU64` meanings match the expected value/error. -/
theorem scalar_meaning_agrees :
    scalarVectors.all
      (fun v => scalarMeaning v.1 (hexToBytes v.2.2.1) v.2.2.2.1 == v.2.2.2.2) = true := by
  native_decide

/-- **Slice reads:** `bytesAt`/`readArray[N]` meanings match the expected input-relative bytes/error. -/
theorem slice_meaning_agrees :
    sliceVectors.all
      (fun v => sliceMeaning v.1 (hexToBytes v.2.2.1) v.2.2.2.1 v.2.2.2.2.1
        == v.2.2.2.2.2.map hexToBytes) = true := by
  native_decide

/-- **`requireU32Length`:** the meaning accepts exactly when the vector expects `ok`. -/
theorem require_u32_meaning_agrees :
    requireU32Vectors.all
      (fun v => isAccepted (meaningRequireU32Length (hexToBytes v.2.1)) == v.2.2) = true := by
  native_decide

/-- **`hasExactErePrefix`:** the total predicate meaning matches the expected boolean. -/
theorem ere_prefix_meaning_agrees :
    erePrefixVectors.all
      (fun v => meaningHasExactErePrefix (hexToBytes v.2.1) == v.2.2) = true := by
  native_decide

/-- `decodeOptionalU64` as `Option (Option Nat)`: `none` = error, `some none` = SSZ `none`,
`some (some v)` = present. Options fail only with `invalidSsz`, so the outer `none` pins that error. -/
def optionU64Meaning (bytes : ByteArray) : Option (Option Nat) :=
  (meaningOptionalU64 bytes).toOption.map (fun o => o.map UInt64.toNat)

/-- `decodeOptionalBlobSchedule` as `Option (Option (target, max, baseFeeUpdateFraction))`. -/
def optionBlobMeaning (bytes : ByteArray) : Option (Option (Nat × Nat × Nat)) :=
  (meaningOptionalBlobSchedule bytes).toOption.map
    (fun o => o.map (fun s => (s.target.toNat, s.max.toNat, s.baseFeeUpdateFraction.toNat)))

/-- **`decodeOptionalU64`:** the meaning matches the expected absent/present/malformed outcome. -/
theorem optional_u64_meaning_agrees :
    optionalU64Vectors.all
      (fun v => optionU64Meaning (hexToBytes v.2.1) == v.2.2) = true := by
  native_decide

/-- **`decodeOptionalBlobSchedule`:** the meaning matches the expected absent/present/malformed
outcome, with exact `(target, max, baseFeeUpdateFraction)` fields on the present arm. -/
theorem optional_blob_meaning_agrees :
    optionalBlobVectors.all
      (fun v => optionBlobMeaning (hexToBytes v.2.1) == v.2.2) = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation
