import SizzLean.Proofs.Roundtrip

/-!
# Encoding after decoding

Upstream's pinned proofs give `decode_encode`: deserializing a *serialized* value returns it. The
oracle's canonicality test needs the other direction. `decodeCanonical` deserializes a body and then
asks whether re-serializing the result reproduces it byte for byte, so the value it re-serializes
came *out* of `deserialize`, not into it.

Those are different theorems, and the second does not follow from the first: from
`deserialize b = .ok (x, n)` and `deserialize (serialize x) = .ok (x, n)` one can only conclude
`serialize x = b` given that `deserialize` is injective — which is exactly the missing fact.
`serialize_injective` is injectivity of the other map and does not help. Nothing in upstream's
theorem set has this shape.

This module supplies the primitive the direction needs, at the one width the pinned V4 schema's
fixed records are built from. It is deliberately *not* a general `encode_decode` over
`BasicSupported`: that belongs upstream, next to `decode_encode`, and building it here by accident
inside a concrete lemma is how a general theory ends up in the wrong repository.

**Axioms.** `bv_decide` closes the eight byte extractions, so anything downstream of
`uint64LE_of_readUInt64LE` carries `Lean.ofReduceBool`/`Lean.trustCompiler`. That is already the
trust class the pinned artifact's `native_decide` facts put in the root — and the same class
upstream's own `decode_encode` carries, for the same reason — but it is worth knowing which
theorems have it.

**And it has since reached one.** `meaningTwentyFourIsSome_holds` uses this primitive, so
`catalogSemanticObligations_of_oracleAgreement` now carries both axioms where it previously carried
none. Recorded here as well as at that theorem because this module is where the class enters.
Nothing cheaper closes the arms — `omega` sees no constraints through `|||`/`<<<`, `decide` cannot
run on free variables, `simp` makes no progress — so removing it means hand-proving the bit-level
identities, which is not worth it for a class the root already carries.
-/

namespace BinaryFv.SSZ.Zesu.SpecCorrespondence

open SizzLean.Spec

/-! ## Byte arrays by index

`ByteArray`'s `getElem` carries a bounds proof, and two references to the same byte reached through
different proof terms are defeq but not syntactically equal — enough to make a bitblasting tactic
treat them as two different atoms. Going through `get!`, which carries no proof, avoids the whole
question. -/

theorem get!_eq_getElem (bytes : ByteArray) (index : Nat) (h : index < bytes.size) :
    bytes.get! index = bytes[index] := by
  show bytes.data[index]! = bytes[index]
  rw [getElem!_pos bytes.data index h]
  rfl

/-- Extensionality in the index-and-`get!` form the proofs below use. -/
theorem ext_of_get! {a b : ByteArray} (sizes : a.size = b.size)
    (bytes : ∀ index, index < a.size → a.get! index = b.get! index) : a = b := by
  apply ByteArray.ext
  refine Array.ext sizes ?_
  intro index h1 h2
  have h := bytes index h1
  rwa [get!_eq_getElem a index h1, get!_eq_getElem b index h2] at h

/-! ## The `u64` arm -/

theorem uint64LE_size (value : UInt64) : (uint64LE value).size = 8 := by
  simp [uint64LE, ByteArray.size_push]

/-- **Serializing a `u64` that was just read reproduces the eight bytes it was read from.**

This is the encode-after-decode direction at the one width the V4 fixed records need. The eight
goals are each "the `k`-th byte of the little-endian encoding of the OR of the shifted input bytes is
the `k`-th input byte", which is a bit-level identity `bv_decide` settles; the surrounding work is
only getting both sides to name the same eight atoms. -/
theorem uint64LE_of_readUInt64LE (bytes : ByteArray) (value : UInt64) (size : bytes.size = 8)
    (read : readUInt64LE bytes 0 = some value) : uint64LE value = bytes := by
  rw [readUInt64LE] at read
  split at read
  · simp only [Option.some.injEq] at read
    subst read
    refine ext_of_get! (by rw [uint64LE_size, size]) ?_
    intro index bound
    rw [uint64LE_size] at bound
    -- Name every input byte through `get!` so the two sides share atoms.
    rw [← get!_eq_getElem bytes 0 (by omega), ← get!_eq_getElem bytes 1 (by omega),
      ← get!_eq_getElem bytes 2 (by omega), ← get!_eq_getElem bytes 3 (by omega),
      ← get!_eq_getElem bytes 4 (by omega), ← get!_eq_getElem bytes 5 (by omega),
      ← get!_eq_getElem bytes 6 (by omega), ← get!_eq_getElem bytes 7 (by omega)]
    match index, bound with
    | 0, _ => show (_ : UInt64).toUInt8 = _; bv_decide
    | 1, _ => show ((_ : UInt64) >>> 8).toUInt8 = _; bv_decide
    | 2, _ => show ((_ : UInt64) >>> 16).toUInt8 = _; bv_decide
    | 3, _ => show ((_ : UInt64) >>> 24).toUInt8 = _; bv_decide
    | 4, _ => show ((_ : UInt64) >>> 32).toUInt8 = _; bv_decide
    | 5, _ => show ((_ : UInt64) >>> 40).toUInt8 = _; bv_decide
    | 6, _ => show ((_ : UInt64) >>> 48).toUInt8 = _; bv_decide
    | 7, _ => show ((_ : UInt64) >>> 56).toUInt8 = _; bv_decide
  · exact absurd read (by simp)

/-- The read itself succeeds on any buffer long enough, which is the half the caller needs before it
can apply the theorem above. -/
theorem readUInt64LE_isSome (bytes : ByteArray) (offset : Nat) (fits : offset + 8 ≤ bytes.size) :
    (readUInt64LE bytes offset).isSome = true := by
  rw [readUInt64LE]
  split
  · simp
  · omega

/-! ## Two `ByteArray` facts the canonicality proofs need

Both are about core's `ByteArray` rather than about SSZ, and both are missing upstream. -/

/-- `ByteArray` has no `ReflBEq` instance, and `decodeCanonical`'s re-serialization branch is a
`==`, so this is needed the moment the compared arrays are not both literals. -/
theorem byteArray_beq_self (bytes : ByteArray) : (bytes == bytes) = true := by
  show bytes.data == bytes.data
  exact beq_self_eq_true bytes.data

/-- Three 8-byte slices reassemble a 24-byte buffer.

The glue for the all-fixed container: `deserializeFixedFields` reads each field from its own
`extract`, so proving that re-serializing reproduces the input means putting the slices back
together. `ByteArray.extract_append_extract` twice, then `extract 0 size = self`. -/
theorem extract_three (bytes : ByteArray) (size : bytes.size = 24) :
    bytes.extract 0 8 ++ bytes.extract 8 16 ++ bytes.extract 16 24 = bytes := by
  rw [ByteArray.extract_append_extract,
    show min 0 8 = 0 from rfl, show max 8 16 = 16 from rfl,
    ByteArray.extract_append_extract,
    show min 0 16 = 0 from rfl, show max 16 24 = 24 from rfl, ← size]
  simp

end BinaryFv.SSZ.Zesu.SpecCorrespondence
