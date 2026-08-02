import SizzLean.Spec.Deserialize
import Std.Tactic.BVDecide

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

namespace BinaryFv.Zesu.MemoryRepresentation

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
  change (uint64LE value).data.size = 8
  simp [uint64LE, ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity] <;> rfl

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

/-! ## The `u32` arm

The same theorem at the width the *offset tables* are built from. `serializeFieldsAux` writes each
variable field's offset with `uint32LE`, so the entry composition theorem's re-serialization half
needs exactly this: the four bytes an offset was read from are the four bytes it serializes back to.

Stated in the encode-after-decode direction, which is the direction that is missing. The other
direction — `readUInt32LE (uint32LE value) 0 = some value` — is upstream's `decode_encode` and does
*not* give what `decodeCanonical` needs, because the value `decodeCanonical` re-serializes came
*out* of `deserialize` rather than into it. Writing that direction here by mistake would produce a
theorem that is true, provable, and useless. -/

theorem uint32LE_size (value : UInt32) : (uint32LE value).size = 4 := by
  change (uint32LE value).data.size = 4
  simp [uint32LE, ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity] <;> rfl

/-- **Serializing a `u32` that was just read reproduces the four bytes it was read from.** -/
theorem uint32LE_of_readUInt32LE (bytes : ByteArray) (value : UInt32) (size : bytes.size = 4)
    (read : readUInt32LE bytes 0 = some value) : uint32LE value = bytes := by
  rw [readUInt32LE] at read
  split at read
  · simp only [Option.some.injEq] at read
    subst read
    refine ext_of_get! (by rw [uint32LE_size, size]) ?_
    intro index bound
    rw [uint32LE_size] at bound
    -- Name every input byte through `get!` so the two sides share atoms.
    rw [← get!_eq_getElem bytes 0 (by omega), ← get!_eq_getElem bytes 1 (by omega),
      ← get!_eq_getElem bytes 2 (by omega), ← get!_eq_getElem bytes 3 (by omega)]
    match index, bound with
    | 0, _ => show (_ : UInt32).toUInt8 = _; bv_decide
    | 1, _ => show ((_ : UInt32) >>> 8).toUInt8 = _; bv_decide
    | 2, _ => show ((_ : UInt32) >>> 16).toUInt8 = _; bv_decide
    | 3, _ => show ((_ : UInt32) >>> 24).toUInt8 = _; bv_decide
  · exact absurd read (by simp)

/-- The read succeeds on any buffer long enough, which is the half the caller needs before it can
apply the theorem above. -/
theorem readUInt32LE_isSome (bytes : ByteArray) (offset : Nat) (fits : offset + 4 ≤ bytes.size) :
    (readUInt32LE bytes offset).isSome = true := by
  rw [readUInt32LE]
  split
  · simp
  · omega

/-! ### Decode after encode at width 32

The *other* direction, needed for one specific purpose: `uint32LE` injectivity, which the entry
theorem's offset-value equivalence needs in its forward direction. Upstream has `decode_encode` at
the type level over `BasicSupported`, but not at this width on the raw `uint32LE`/`readUInt32LE` pair,
and the offset table is built from exactly that pair.

Note this is the direction the module docstring warns is *not* what `decodeCanonical` needs — true,
and it is not being used for that. It is used only to cancel `uint32LE` on both sides of an equation.
Keeping both directions in one place, each labelled with what it is for, is what stops the two being
confused later. -/

/-- `uint32LE` as an explicit four-element literal, so `getElem` reduces without needing
`push`-indexing lemmas. -/
theorem uint32LE_eq_literal (value : UInt32) :
    uint32LE value = ⟨#[value.toUInt8, (value >>> 8).toUInt8, (value >>> 16).toUInt8,
      (value >>> 24).toUInt8]⟩ := rfl

/-- The `u64` counterpart, placed beside its sibling rather than in `ChainOffsets` where it is consumed:
the `uintNLE` family belongs together, and a reader checking one width against the other should not have
to cross modules. `rfl`, and it is the one prerequisite of the `u64` `eq_extract_iff` chain that carries
no `bv_decide` -- the round trip and injectivity above it do. -/
theorem uint64LE_eq_literal (value : UInt64) :
    uint64LE value = ⟨#[value.toUInt8, (value >>> 8).toUInt8, (value >>> 16).toUInt8,
      (value >>> 24).toUInt8, (value >>> 32).toUInt8, (value >>> 40).toUInt8,
      (value >>> 48).toUInt8, (value >>> 56).toUInt8]⟩ := rfl

theorem readUInt32LE_uint32LE (value : UInt32) : readUInt32LE (uint32LE value) 0 = some value := by
  rw [uint32LE_eq_literal, readUInt32LE, dif_pos (by simp [ByteArray.size])]
  show some (value.toUInt8.toUInt32 ||| (value >>> 8).toUInt8.toUInt32 <<< 8
    ||| (value >>> 16).toUInt8.toUInt32 <<< 16 ||| (value >>> 24).toUInt8.toUInt32 <<< 24)
      = some value
  simp only [Option.some.injEq]
  bv_decide

/-- **`uint32LE` is injective**, so it can be cancelled from both sides of an equation. -/
theorem uint32LE_injective {a b : UInt32} (h : uint32LE a = uint32LE b) : a = b := by
  have ha := readUInt32LE_uint32LE a
  rw [h, readUInt32LE_uint32LE b] at ha
  exact (Option.some.injEq _ _).mp ha.symm

theorem readUInt64LE_uint64LE (value : UInt64) :
    readUInt64LE (uint64LE value) 0 = some value := by
  rw [uint64LE_eq_literal, readUInt64LE, dif_pos (by simp [ByteArray.size])]
  -- `show` to the element-wise form rather than rewriting: ByteArray indexing lemmas do not exist
  -- under guessable names (module note), and the u32 sibling crosses this the same way. Defeq, so the
  -- restatement typechecks where a rewrite has nothing to fire on.
  show some (value.toUInt8.toUInt64 ||| (value >>> 8).toUInt8.toUInt64 <<< 8
      ||| (value >>> 16).toUInt8.toUInt64 <<< 16 ||| (value >>> 24).toUInt8.toUInt64 <<< 24
      ||| (value >>> 32).toUInt8.toUInt64 <<< 32 ||| (value >>> 40).toUInt8.toUInt64 <<< 40
      ||| (value >>> 48).toUInt8.toUInt64 <<< 48 ||| (value >>> 56).toUInt8.toUInt64 <<< 56)
    = some value
  simp only [Option.some.injEq]
  bv_decide

/-- **`uint64LE` is injective**, so it can be cancelled from both sides of an equation. Two lines off the
round trip, exactly as at `u32`. -/
theorem uint64LE_injective {a b : UInt64} (h : uint64LE a = uint64LE b) : a = b := by
  have ha := readUInt64LE_uint64LE a
  rw [h, readUInt64LE_uint64LE b] at ha
  exact (Option.some.injEq _ _).mp ha.symm

/-! ### The `u32` arm is not vacuous, and says something

A conditional equation can be true because its hypotheses are unsatisfiable, or because its
conclusion holds regardless — either way it would prove nothing while looking identical from
outside. These four witnesses rule both out, at `0x04030201`. They are kept rather than run once and
deleted: they are the same anti-vacuity discipline used throughout the contract layer,
and a later edit that breaks the width or the byte order fails here rather than silently. -/

/-- The hypotheses are satisfiable: a four-byte buffer really does read. -/
theorem readUInt32LE_witness : readUInt32LE ⟨#[1, 2, 3, 4]⟩ 0 = some 67305985 := by decide

/-- And the conclusion really does hold there, so hypotheses and conclusion are *jointly*
satisfiable — the lemma is not vacuously true. -/
theorem uint32LE_witness : uint32LE 67305985 = ⟨#[1, 2, 3, 4]⟩ := by decide

/-- The conclusion discriminates on `value`: it is not an equation that holds for anything. -/
theorem uint32LE_discriminates : uint32LE 0 ≠ (⟨#[1, 2, 3, 4]⟩ : ByteArray) := by decide

/-- And the byte order is pinned little-endian rather than absorbed: the reversed buffer is not a
solution. -/
theorem uint32LE_is_little_endian : uint32LE 67305985 ≠ (⟨#[4, 3, 2, 1]⟩ : ByteArray) := by decide

/-! ## Two `ByteArray` facts the canonicality proofs need

Both are about core's `ByteArray` rather than about SSZ, and both are missing upstream. -/

/-- `ByteArray` has no `ReflBEq` instance, and `decodeCanonical`'s re-serialization branch is a
`==`, so this is needed the moment the compared arrays are not both literals. -/
theorem byteArray_beq_self (bytes : ByteArray) : (bytes == bytes) = true := by
  show bytes.data == bytes.data
  exact beq_self_eq_true bytes.data

/-- The other direction, and the reason it needs stating: there is **no `LawfulBEq ByteArray`
instance**, so `eq_of_beq` does not apply and `simp` will not turn `==` into `=`. The conversion has
to go through `.data`, where `Array UInt8` *is* lawful.

`decodeCanonical`'s canonicality branch is a `==`, so every inversion of an acceptance needs this. -/
theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  have hdata : (a.data == b.data) = true := h
  exact ByteArray.ext (eq_of_beq hdata)

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

end BinaryFv.Zesu.MemoryRepresentation
