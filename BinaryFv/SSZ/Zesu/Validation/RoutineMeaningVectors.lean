import BinaryFv.SSZ.Zesu.Contracts.Leaves
import BinaryFv.SSZ.Zesu.Contracts.Options
import BinaryFv.SSZ.Zesu.Contracts.Canonicality
import BinaryFv.SSZ.Zesu.Contracts.Containers
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

/-- **`requireCanonicalOffsets`:** the offset-table check accepts exactly when the vector expects it
(canonical prefix table), rejecting wrong-first, descending, out-of-range, short-slice, and empty. -/
theorem canonical_offsets_meaning_agrees :
    canonicalOffsetsVectors.all
      (fun v => isAccepted (meaningRequireCanonicalOffsets (hexToBytes v.2.1) v.2.2.1 v.2.2.2.1)
        == v.2.2.2.2) = true := by
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

/-!
## Non-allocating containers

`decodeForkActivation` / `decodeForkConfig` / `decodeChainConfig` return nested structs. Each is
flattened to a fixed-order list of `Nat` scalars (every `UInt64` field, each `Option` preceded by a
0/1 presence bit) — the SAME order the Zig probe and `ssz_routine_vectors.py` use, so all three encode
the same struct value. The expected outcome is `(Option (List Nat) × String)`: `(some scalars, "")` on
success, `(none, label)` on error, so `unknownFork` is pinned distinctly from `invalidSsz`.
-/

/-- The local error label, matching the probe's `errLabel` and the vectors' error strings. -/
def errLabelOf : SszDecodeError → String
  | .invalidSsz => "invalidSsz"
  | .unknownFork => "unknownFork"
  | .outOfMemory => "outOfMemory"

/-- One option field: presence bit then value (0 when absent). -/
def flatOptU64 (v : Option UInt64) : List Nat :=
  match v with | some x => [1, x.toNat] | none => [0, 0]

def flatForkActivation (fa : SszBridge.RawForkActivation) : List Nat :=
  flatOptU64 fa.blockNumber ++ flatOptU64 fa.timestamp

def flatBlob : Option SszBridge.RawBlobSchedule → List Nat
  | some s => [1, s.target.toNat, s.max.toNat, s.baseFeeUpdateFraction.toNat]
  | none => [0, 0, 0, 0]

def flatForkConfig (fc : SszBridge.RawForkConfig) : List Nat :=
  fc.fork.toNat :: (flatForkActivation fc.activation ++ flatBlob fc.blobSchedule)

def flatChainConfig (cc : SszBridge.RawChainConfig) : List Nat :=
  cc.chainId.toNat :: flatForkConfig cc.activeFork

/-- Normalize a container meaning to the vectors' `(Option (List Nat) × String)` encoding. -/
def containerEnc {α} (flat : α → List Nat) (r : Except SszDecodeError α) : Option (List Nat) × String :=
  match r with
  | .ok v => (some (flat v), "")
  | .error e => (none, errLabelOf e)

/-- **`decodeForkActivation`:** the flattened meaning matches the expected value/error. -/
theorem fork_activation_meaning_agrees :
    forkActivationVectors.all
      (fun v => containerEnc flatForkActivation (meaningForkActivation (hexToBytes v.2.1)) == v.2.2)
      = true := by
  native_decide

/-- **`decodeForkConfig`:** value + exact `unknownFork`/`invalidSsz`, including fork-bound ordering. -/
theorem fork_config_meaning_agrees :
    forkConfigVectors.all
      (fun v => containerEnc flatForkConfig (meaningForkConfig (hexToBytes v.2.1)) == v.2.2)
      = true := by
  native_decide

/-- **`decodeChainConfig`:** value + propagated `unknownFork` from the nested fork config. -/
theorem chain_config_meaning_agrees :
    chainConfigVectors.all
      (fun v => containerEnc flatChainConfig (meaningChainConfig (hexToBytes v.2.1)) == v.2.2)
      = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation
