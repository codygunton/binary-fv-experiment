import BinaryFv.SSZ.Zesu.SpecCorrespondence.EntryOffsets

/-!
# The activation / forkConfig / chainConfig chain

Item 6.2. Kept in its own module rather than appended to `EntryOffsets`: that file is about the
all-variable entry schema, and the mechanism here is different enough that mixing them would obscure
which lemmas depend on the leading-fixed skip.
-/

namespace BinaryFv.SSZ.Zesu.SpecCorrespondence

open SizzLean.Spec
open BinaryFv.SSZ.Zesu.Contracts

/-! # Item 6.2: the activation / forkConfig / chainConfig chain

Three nested source-shaped containers. Structurally these are **not** the entry schema repeated:
`entryFields` is all-variable, so its fixed section is exactly its offset table. Each of these three has
**leading fixed fields**, which `extractFieldOffsets` skips by advancing `off` by `fixedByteSize` rather
than reading, and which `deserializeVarFields` reads out of the prefix. That skip is the new mechanism,
and it is why the entry's offset-table lemma does not generalise by substitution.

The three fixed-section sizes are *derived* by `decide` from the field lists rather than quoted, exactly
as `entryFields_fixedSectionSize` is: 8, 16 and 12 are what the source hard-codes at each level, so if a
field is ever added the mismatch surfaces here instead of silently. -/

def forkActivationFields : List SSZType :=
  [.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues,
    .list SszBridge.u64 SszBridge.maxOptionalForkActivationValues]

def forkConfigFields : List SSZType :=
  [SszBridge.u64, SszBridge.forkActivationType,
    .list SszBridge.blobScheduleType SszBridge.maxBlobSchedulesPerFork]

def chainConfigFields : List SSZType :=
  [SszBridge.u64, SszBridge.forkConfigType]

/-! Transcription checks: hand-copied field lists, so the compiler holds them. -/

theorem forkActivationType_eq : SszBridge.forkActivationType = .container forkActivationFields := rfl
theorem forkConfigType_eq : SszBridge.forkConfigType = .container forkConfigFields := rfl
theorem chainConfigType_eq : SszBridge.chainConfigType = .container chainConfigFields := rfl

/-! The derived fixed-section sizes, matching the source's 8 / 16 / 12. -/

theorem forkActivationFields_fixedSection :
    SSZType.fixedSectionSizeFields forkActivationFields = 8 := by decide

theorem forkConfigFields_fixedSection :
    SSZType.fixedSectionSizeFields forkConfigFields = 16 := by decide

theorem chainConfigFields_fixedSection :
    SSZType.fixedSectionSizeFields chainConfigFields = 12 := by decide

/-! Each has a variable field, so `deserialize` takes the variable-container branch. -/

theorem forkActivationFields_not_allFixed :
    SSZType.allFixedSize forkActivationFields = false := by decide

theorem forkConfigFields_not_allFixed :
    SSZType.allFixedSize forkConfigFields = false := by decide

theorem chainConfigFields_not_allFixed :
    SSZType.allFixedSize chainConfigFields = false := by decide

/-! Per-field fixedness, one lemma each, for the same reason as the entry's: the offset-table
reduction rewrites under `extractFieldOffsets`' `if` and needs each guard separately. -/

@[simp] theorem u64_isFixed : SszBridge.u64.isFixedSize = true := by decide

@[simp] theorem u64_fixedByteSize : SszBridge.u64.fixedByteSize = 8 := by decide

@[simp] theorem forkActivationType_not_fixed :
    SszBridge.forkActivationType.isFixedSize = false := by decide

@[simp] theorem forkConfigType_not_fixed :
    SszBridge.forkConfigType.isFixedSize = false := by decide

@[simp] theorem optionalU64Field_not_fixed :
    (SSZType.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues).isFixedSize
      = false := by decide

@[simp] theorem blobScheduleListField_not_fixed :
    (SSZType.list SszBridge.blobScheduleType SszBridge.maxBlobSchedulesPerFork).isFixedSize
      = false := by decide

/-! ## The offset tables, with the leading-fixed skip

`chainConfigFields` is the sharpest case: one fixed `u64` then one variable field, so the table has a
single entry read at **8**, not at 0. The skip is what puts it there, and the source reads
`meaningReadOffset bytes 8` — so this lemma is where "the oracle reads the offset where the source does"
stops being trivial. -/

theorem extractFieldOffsets_chainConfig (b : ByteArray) :
    extractFieldOffsets b chainConfigFields 0 =
      match readUInt32LE b 8 with
      | some o => .ok [o.toNat]
      | none => .error .tooShort := by
  simp [chainConfigFields, extractFieldOffsets]
  cases readUInt32LE b 8 <;> rfl

theorem extractFieldOffsets_forkActivation (b : ByteArray) :
    extractFieldOffsets b forkActivationFields 0 =
      match readUInt32LE b 0, readUInt32LE b 4 with
      | some o0, some o1 => .ok [o0.toNat, o1.toNat]
      | _, _ => .error .tooShort := by
  simp [forkActivationFields, extractFieldOffsets, BYTES_PER_LENGTH_OFFSET]
  cases readUInt32LE b 0 <;> cases readUInt32LE b 4 <;> rfl

theorem extractFieldOffsets_forkConfig (b : ByteArray) :
    extractFieldOffsets b forkConfigFields 0 =
      match readUInt32LE b 8, readUInt32LE b 12 with
      | some o0, some o1 => .ok [o0.toNat, o1.toNat]
      | _, _ => .error .tooShort := by
  simp [forkConfigFields, extractFieldOffsets, BYTES_PER_LENGTH_OFFSET]
  cases readUInt32LE b 8 <;> cases readUInt32LE b 12 <;> rfl

/-! ## The tables are the source's reads

Same statement as `extractFieldOffsets_eq_meaningReads` at each of the three schemas, and the offsets
are the ones the source actually passes: 0/4 for activation, 8/12 for forkConfig, 8 for chainConfig. -/

theorem extractFieldOffsets_chainConfig_eq_meaningReads (b : ByteArray) (o : Nat) :
    extractFieldOffsets b chainConfigFields 0 = .ok [o] ↔ meaningReadOffset b 8 = .ok o := by
  rw [extractFieldOffsets_chainConfig]
  simp only [meaningReadOffset, meaningReadU32, Option.toDecodeResult]
  cases readUInt32LE b 8 <;> simp [Except.map]

theorem extractFieldOffsets_forkActivation_eq_meaningReads (b : ByteArray) (o0 o1 : Nat) :
    extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1] ↔
      (meaningReadOffset b 0 = .ok o0 ∧ meaningReadOffset b 4 = .ok o1) := by
  rw [extractFieldOffsets_forkActivation]
  simp only [meaningReadOffset, meaningReadU32, Option.toDecodeResult]
  cases readUInt32LE b 0 <;> cases readUInt32LE b 4 <;> simp [Except.map]

theorem extractFieldOffsets_forkConfig_eq_meaningReads (b : ByteArray) (o0 o1 : Nat) :
    extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1] ↔
      (meaningReadOffset b 8 = .ok o0 ∧ meaningReadOffset b 12 = .ok o1) := by
  rw [extractFieldOffsets_forkConfig]
  simp only [meaningReadOffset, meaningReadU32, Option.toDecodeResult]
  cases readUInt32LE b 8 <;> cases readUInt32LE b 12 <;> simp [Except.map]

/-! ## The chainConfig walk, with its leading fixed field

The first genuinely new shape in item 6.2. `deserializeVarFields` reads the `u64` out of the *prefix*
— `b.extract 0 8`, then `deserialize u64` on that slice — while the source reads it *in place* with
`meaningReadU64 b 0` → `readUInt64LE b 0`.

**That is a new reader pairing, not just a moved offset.** The entry schema is all-variable, so no field
was ever read from the fixed prefix and this bridge was never needed. It is the same *class* of problem
as the `readU32LE?`-versus-`readUInt32LE` mismatch (R2), one width and one position along: two
definitions of "read the integer here", where nothing forces them to agree unless it is proved. -/

/-- **Slice-then-deserialize equals read-in-place, at `u64`.** The bridge the leading-fixed skip needs. -/
theorem deserialize_u64_extract (b : ByteArray) (i : Nat) (h : i + 8 ≤ b.size) {v : UInt64}
    (hread : readUInt64LE b i = some v) :
    SSZType.deserialize SszBridge.u64 (b.extract i (i + 8)) = .ok (v, 8) := by
  -- `omega` needs the slice width; the unused-simp-arg linter flagged this only for the `simp` call
  -- below, not for the proof, and removing it outright broke the `dif_pos` side goal.
  have hslice : (b.extract i (i + 8)).size = 8 := by rw [ByteArray.size_extract]; omega
  have hlocal : readUInt64LE (b.extract i (i + 8)) 0 = some v := by
    rw [readUInt64LE, dif_pos (by omega : 0 + 8 ≤ (b.extract i (i + 8)).size)]
    rw [readUInt64LE, dif_pos h] at hread
    simp only [Option.some.injEq] at hread
    simp only [Option.some.injEq, ← hread]
    simp [ByteArray.getElem_extract]
  show SSZType.deserialize (.uintN 64) _ = _
  rw [SSZType.deserialize]
  simp only [hlocal]

end BinaryFv.SSZ.Zesu.SpecCorrespondence
