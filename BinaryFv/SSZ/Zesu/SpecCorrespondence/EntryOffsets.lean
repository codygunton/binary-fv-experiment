import BinaryFv.SSZ.Zesu.Contracts.Entry

/-!
# The entry offset table, on both sides

`meaningDecodeRaw` reads four `uint32`s at 0/4/8/12, checks them with `requireCanonicalOffsets`, and
slices four field bodies out of the body. `decodeCanonical statelessInputV4Type` reaches the same
four offsets through `extractFieldOffsets`, which walks the field list and emits one offset per
variable-size field. This module proves the two tables are the same list.

That reduction is the first half of the entry composition theorem, and it is the half that was
previously unreachable: `extractFieldOffsets` was `private` in the pinned `Spec/Deserialize.lean`
until the visibility shim widened to both offset-table walkers (`efb3793`). Everything here is a
statement *about* the pinned upstream walker rather than a re-implementation of it, which is the
whole point — a hand-rolled four-offset reader would prove nothing about what the oracle does.
-/

namespace BinaryFv.SSZ.Zesu.SpecCorrespondence

open SizzLean.Spec
open BinaryFv.SSZ.Zesu.Contracts

/-! ## The schema is four variable-size fields

Every step below depends on all four entry fields being variable-size: that is what makes the fixed
section exactly four `uint32` offsets, and what makes `extractFieldOffsets` emit one entry per field
rather than skipping some. Established by evaluation on the concrete schema rather than assumed. -/

/-- The entry schema's field list, named so the lemmas below can talk about it. -/
def entryFields : List SSZType :=
  [SszBridge.newPayloadRequestType, SszBridge.witnessType, SszBridge.chainConfigType,
    .list (SszBridge.byteVector SszBridge.publicKeyBytes) SszBridge.maxPublicKeys]

theorem statelessInputV4Type_eq : SszBridge.statelessInputV4Type = .container entryFields := rfl

/-- None of the four entry fields is fixed-size. Stated one field at a time as well as over the
list, because the offset-table reduction rewrites under `extractFieldOffsets`'s `if` and needs each
guard as its own rewrite. -/
theorem entryFields_none_fixed : ∀ t ∈ entryFields, t.isFixedSize = false := by
  decide

@[simp] theorem newPayloadRequestType_not_fixed :
    SszBridge.newPayloadRequestType.isFixedSize = false := by decide

@[simp] theorem witnessType_not_fixed : SszBridge.witnessType.isFixedSize = false := by decide

@[simp] theorem chainConfigType_not_fixed :
    SszBridge.chainConfigType.isFixedSize = false := by decide

@[simp] theorem publicKeysField_not_fixed :
    (SSZType.list (SszBridge.byteVector SszBridge.publicKeyBytes)
      SszBridge.maxPublicKeys).isFixedSize = false := by decide

/-- The entry container is not all-fixed, so `deserialize` takes its variable-size branch. -/
theorem entryFields_not_allFixed : SSZType.allFixedSize entryFields = false := by
  decide

/-- The fixed section is exactly the four offsets. -/
theorem entryFields_fixedSectionSize : SSZType.fixedSectionSizeFields entryFields = 16 := by
  decide

/-! ## The two tables coincide -/

/-- **The oracle's offset table is the source's four reads.**

`extractFieldOffsets` walks the field list once. With all four entry fields variable-size it takes
the `else` branch every time, so it reads a `uint32` at 0, 4, 8 and 12 — `BYTES_PER_LENGTH_OFFSET`
apart — and widens each with `UInt32.toNat`. Those are exactly the four `meaningReadOffset` calls at
the head of `meaningDecodeRaw`.

Every failure is `.tooShort`, on either side and at any of the four reads, so the flat match loses
nothing: a short buffer fails the first read and the deeper reads are never reached. -/
theorem extractFieldOffsets_entry (b : ByteArray) :
    extractFieldOffsets b entryFields 0 =
      match readUInt32LE b 0, readUInt32LE b 4, readUInt32LE b 8, readUInt32LE b 12 with
      | some o0, some o1, some o2, some o3 => .ok [o0.toNat, o1.toNat, o2.toNat, o3.toNat]
      | _, _, _, _ => .error .tooShort := by
  simp [entryFields, extractFieldOffsets, BYTES_PER_LENGTH_OFFSET]
  cases readUInt32LE b 0 <;> cases readUInt32LE b 4 <;> cases readUInt32LE b 8 <;>
    cases readUInt32LE b 12 <;> rfl

/-! ## The source reads the same table

`meaningDecodeRaw` does not call `extractFieldOffsets`; it calls `meaningReadOffset` four times.
This is the step that says those two descriptions produce the same four numbers, which is what lets
the entry composition theorem move between them. -/

/-- **The oracle's table and the source's four `readOffset` calls agree.**

Note the error taxonomies do *not* agree — a short buffer is `.tooShort` on the oracle side and
`.invalidSsz` on the source side — which is exactly why the entry obligation is stated at acceptance
granularity rather than at error-constructor granularity. This equivalence is about the accepting
case, where the taxonomy question does not arise. -/
theorem extractFieldOffsets_eq_meaningReads (b : ByteArray) (o0 o1 o2 o3 : Nat) :
    extractFieldOffsets b entryFields 0 = .ok [o0, o1, o2, o3] ↔
      (meaningReadOffset b 0 = .ok o0 ∧ meaningReadOffset b 4 = .ok o1 ∧
        meaningReadOffset b 8 = .ok o2 ∧ meaningReadOffset b 12 = .ok o3) := by
  rw [extractFieldOffsets_entry]
  simp only [meaningReadOffset, meaningReadU32, Option.toDecodeResult]
  cases readUInt32LE b 0 <;> cases readUInt32LE b 4 <;> cases readUInt32LE b 8 <;>
    cases readUInt32LE b 12 <;> simp [Except.map]

end BinaryFv.SSZ.Zesu.SpecCorrespondence
