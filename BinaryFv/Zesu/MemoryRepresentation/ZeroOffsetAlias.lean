import BinaryFv.Zesu.Contracts.SemanticObligations
import BinaryFv.Zesu.MemoryRepresentation.EncodeDecode

/-!
# The all-zero first-offset alias

`zeroFirstOffsetAliasRejected`, the last of the four oracle-agreement facts. Its own module rather
than an addition to `EntryOffsets` or `ChainOffsets`: those are about two concrete schemas, while
this quantifies over *every* variable-size element type and every capacity. Nothing here mentions
the entry or the chain.

## What the obligation actually claims, and why that matters here

The statement was **false as originally written** and was corrected at `494c1f2` by restricting to
`elementType.isFixedSize = false`. That restriction is not a convenience: a leading `00 00 00 00` is
an *offset* only when the wire format has an offset table, which is exactly when the elements are
variable-size. For a fixed element type those four bytes are data — `.list (.uintN 8) 4` on four zero
bytes decodes to `#[0,0,0,0]`, re-serializes to the same four bytes, and is **accepted**.

So the proof below is expected to *depend* on `hvar`, and that dependence is checked rather than
assumed (see the power note at the end). A proof that went through without it would be proving the
corrected statement by an argument that also "proves" the false one, which would make the argument
unsound.

## The mechanism

The spec's variable-element list branch recovers the element count from the first offset as
`firstOff / BYTES_PER_LENGTH_OFFSET`. A zero first offset therefore yields count `0`, an empty offset
list, and an empty element array — and `deserialize` *succeeds*, returning `used = b.size`. So the
`used` check does not reject it. What rejects it is `decodeCanonical`'s re-serialization equality:
an empty list serializes to the empty `ByteArray`, and an empty buffer cannot equal a body of four or
more bytes.

That is worth stating explicitly because the two guards fail in opposite directions. The `used` test
passes precisely *because* the decoder consumed the whole buffer while producing nothing from it;
only the serialize-compare branch notices that nothing is not the same as four bytes.

Both spec-side walkers are dual-scrutinee matches whose return type depends on the element type, so
`rfl` does not reduce them even at `[]`; their equation lemmas do. That is the same obstruction the
chain module hit twice, recorded here so the third encounter is recognised rather than rediscovered.
-/

namespace BinaryFv.Zesu.MemoryRepresentation

open SizzLean.Spec
open BinaryFv.Zesu.Contracts

/-- **A zero first offset makes the decode succeed, not fail.** Count `0` from
`0 / BYTES_PER_LENGTH_OFFSET`, hence no offsets to walk and no elements to decode — and `used` is
`b.size`, so the whole buffer counts as consumed. This is the step that shows the `used` check cannot
be what rejects the alias. -/
theorem zeroFirstOffset_deserialize {bytes : ByteArray} (hsize : bytes.size ≥ 4)
    (hread : readUInt32LE bytes 0 = some 0) (t : SSZType) (cap : Nat)
    (hvar : t.isFixedSize = false) :
    SSZType.deserialize (.list t cap) bytes
      = .ok (⟨#[], by simp⟩, bytes.size) := by
  rw [SSZType.deserialize]
  have hne : ¬ bytes.size = 0 := by omega
  simp [hvar, hne, hread, SSZType.deserializeVarElems, SizzLean.Spec.extractCollOffsets,
    BYTES_PER_LENGTH_OFFSET]

/-- **And an empty variable-element list serializes to nothing.** No offset table, no bodies — the
offset table exists only to locate elements, so with no elements there is nothing to locate. -/
theorem zeroFirstOffset_serialize (t : SSZType) (cap : Nat) (hvar : t.isFixedSize = false)
    (h : (#[] : Array t.interp).size ≤ cap) :
    SSZType.serialize (.list t cap) ⟨#[], h⟩ = ByteArray.empty := by
  unfold SSZType.serialize
  simp [hvar, SSZType.serializeVarElemsAux]

/-- **The obligation, discharged.**

`readUInt32LE_zero_of_readU32LE` bridges the reader mismatch: the obligation is phrased with
`BinaryFv.Specs.SSZ.readU32LE?` while the spec's list branch reads with `readUInt32LE`, and its two hypotheses
are exactly the two this statement supplies. That bridge was written for this obligation and this is
where it is spent.

Everything after it is the two lemmas above plus the observation that the empty buffer is not `bytes`.
`ByteArray` has no `LawfulBEq` instance, so the `==` in `decodeCanonical` is discharged through
`byteArray_eq_of_beq` rather than by `simp`. -/
theorem zeroFirstOffsetAliasRejected_holds : zeroFirstOffsetAliasRejected := by
  intro bytes hsize hzero t cap hvar
  have hread : readUInt32LE bytes 0 = some 0 :=
    readUInt32LE_zero_of_readU32LE bytes hsize hzero
  rw [BinaryFv.Specs.SSZ.decodeCanonical]
  rw [zeroFirstOffset_deserialize hsize hread t cap hvar]
  simp only [bind, Except.bind, bne_self_eq_false]
  rw [zeroFirstOffset_serialize t cap hvar (by simp)]
  have hne : ¬ (ByteArray.empty = bytes) := by
    intro he
    rw [← he] at hsize
    simp at hsize
  have hbeq : (ByteArray.empty == bytes) = false := by
    cases hb : (ByteArray.empty == bytes) with
    | false => rfl
    | true => exact absurd (byteArray_eq_of_beq hb) hne
  simp [hbeq, Except.toOption]

/-! ### Power

Three must-fail probes, run and reverted:

1. **Drop `hvar` from `zeroFirstOffset_deserialize`'s `simp` set** — fails (6 errors). This is the
   important one: `hvar` is the hypothesis whose absence made the original statement false, so a
   proof that did not use it would be proving the corrected obligation by an argument that also
   "proves" the false one.
2. **Read `some 4` instead of `some 0`** — fails (8 errors). The zero is load-bearing, not incidental
   to the shape.
3. **Weaken the floor to `bytes.size ≥ 0`** — fails (2 errors), and *correctly*: the spec's
   `if b.size = 0 then .ok (⟨#[], _⟩, 0)` branch means an empty buffer really is accepted, so without
   the floor the obligation is false. The probe recovers that fact rather than merely breaking the
   proof.
-/

end BinaryFv.Zesu.MemoryRepresentation
