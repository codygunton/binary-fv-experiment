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

Three nested source-shaped containers. Structurally these are **not** uniformly the entry schema
repeated: `entryFields` is all-variable, so its fixed section is exactly its offset table, whereas
`forkConfig` and `chainConfig` have **leading fixed fields**, which `extractFieldOffsets` skips by
advancing `off` by `fixedByteSize` rather than reading, and which `deserializeVarFields` reads out of
the prefix. That skip is the new mechanism, and it is why the entry's offset-table lemma does not
generalise by substitution.

**`forkActivation` is the exception and is worth naming as one:** it is all-variable, like the entry
schema, so it has no leading fixed field and no skip. Its fixed-section size of 8 is
`2 * BYTES_PER_LENGTH_OFFSET` — two offsets — and coincides with `chainConfig`'s leading `u64` width by
accident. An earlier draft of this preamble asserted the skip at all three; reading the `8`s as the same
quantity is exactly the confusion that motivated a separate module.

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

/-- **The oracle slices `chainConfig` where the source does**, and reads its fixed field from the
prefix. Consumes `deserialize_u64_extract`: the `u64` arrives as a slice on the oracle side and as an
in-place read on the source side, and this is where those two meet. -/
theorem deserializeVarFields_chainConfig (b : ByteArray) (o : Nat)
    (h8 : 8 ≤ b.size) (ho : o ≤ b.size) {v : UInt64} (hv : readUInt64LE b 0 = some v) :
    SSZType.deserializeVarFields chainConfigFields b 0 [o] b.size =
      match SSZType.deserialize SszBridge.forkConfigType (b.extract o b.size) with
      | .error e => .error e
      | .ok (x, _) => .ok (v, x, PUnit.unit) := by
  have no : ¬ (o > b.size) := by omega
  have nend : ¬ (b.size > b.size) := by omega
  simp only [chainConfigFields, SSZType.deserializeVarFields, u64_isFixed, u64_fixedByteSize,
    forkConfigType_not_fixed, List.head?_nil, Option.getD_none,
    no, nend, decide_false, Bool.or_false, if_false, Bool.false_eq_true, if_true]
  rw [deserialize_u64_extract b 0 (by omega) hv]
  simp only [ne_eq, not_true_eq_false, if_false]
  cases SSZType.deserialize SszBridge.forkConfigType (b.extract o b.size) <;> rfl

/-! ## The `forkActivation` walk

The one container in the chain with **no** leading fixed field: `forkActivationFields` is all-variable,
so its fixed section *is* its offset table and its 8 is `2 * BYTES_PER_LENGTH_OFFSET`, not a `u64`. That
makes it the entry schema's shape at arity two rather than a new mechanism — no reader bridge is
involved, and `prefixOff` again never reaches the result.

Worth stating explicitly because the module's own preamble overreaches: it says all three chain
containers have leading fixed fields, and this one does not. The `8` coinciding with `chainConfig`'s
`u64` width is a numerical accident of two four-byte offsets, and reading it as "the same skip again"
is exactly the confusion the separate module was meant to prevent. -/

/-- **The oracle slices `forkActivation` where the source does.** Both fields are variable, so this is
`deserializeVarFields_entry` at arity two; the source's two slices are `bytes.extract first second` and
`bytes.extract second bytes.size`.

**What this lemma pins that its statement does not advertise: first-error-wins ORDERING.** Established
by a must-fail probe (run and reverted, per the transient-probe rule) that swapped the two slices. It
fails — but the informative part is *where*. In the `error.error` case the two sides disagree about
*which* error surfaces, not merely about which field a slice feeds. So the nested `match` is load-bearing
for error order and a flattened version would be strictly weaker while still looking equivalent. Recorded
here rather than only in the probe's report, because a reader checking whether this lemma is strong enough
to compose cannot see it from the statement. -/
theorem deserializeVarFields_forkActivation (b : ByteArray) (o0 o1 : Nat)
    (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) :
    SSZType.deserializeVarFields forkActivationFields b 0 [o0, o1] b.size =
      match SSZType.deserialize
          (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) (b.extract o0 o1) with
      | .error e => .error e
      | .ok (x0, _) =>
        match SSZType.deserialize
            (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues)
            (b.extract o1 b.size) with
        | .error e => .error e
        | .ok (x1, _) => .ok (x0, x1, PUnit.unit) := by
  have n01 : ¬ (o0 > o1) := by omega
  have n1 : ¬ (o1 > b.size) := by omega
  have nend : ¬ (b.size > b.size) := by omega
  simp only [forkActivationFields, SSZType.deserializeVarFields, optionalU64Field_not_fixed,
    List.head?_cons, List.head?_nil, Option.getD_some, Option.getD_none,
    n01, n1, nend, decide_false, Bool.or_false, if_false, Bool.false_eq_true]
  cases SSZType.deserialize
      (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) (b.extract o0 o1) <;>
    cases SSZType.deserialize
        (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues)
        (b.extract o1 b.size) <;> rfl

/-! ## The `forkConfig` walk

`chainConfig`'s shape with one more variable field: the leading `u64` comes out of the prefix through
`deserialize_u64_extract`, then two variable fields are walked from the offset table.

**The `fork > 20` test is deliberately absent here.** In the source it sits *between* the offset-table
check and the child decodes, and that ordering is what makes `forkErrorOrderingDiffers` true and the
obligation acceptance-only. This lemma is about the oracle's walk alone, so the test has no place in it;
it enters at the schema-level join, on the source side, in the position the source puts it. Commuting it
past the child decodes to make the join cheaper would be a statement defect, not a simplification. -/

/-- **The oracle slices `forkConfig` where the source does**, reading `fork` from the prefix. -/
theorem deserializeVarFields_forkConfig (b : ByteArray) (o0 o1 : Nat)
    (h8 : 8 ≤ b.size) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size)
    {v : UInt64} (hv : readUInt64LE b 0 = some v) :
    SSZType.deserializeVarFields forkConfigFields b 0 [o0, o1] b.size =
      match SSZType.deserialize SszBridge.forkActivationType (b.extract o0 o1) with
      | .error e => .error e
      | .ok (x0, _) =>
        match SSZType.deserialize
            (.list SszBridge.blobScheduleType SszBridge.maxBlobSchedulesPerFork)
            (b.extract o1 b.size) with
        | .error e => .error e
        | .ok (x1, _) => .ok (v, x0, x1, PUnit.unit) := by
  have n01 : ¬ (o0 > o1) := by omega
  have n1 : ¬ (o1 > b.size) := by omega
  have nend : ¬ (b.size > b.size) := by omega
  simp only [forkConfigFields, SSZType.deserializeVarFields, u64_isFixed, u64_fixedByteSize,
    forkActivationType_not_fixed, blobScheduleListField_not_fixed,
    List.head?_cons, List.head?_nil, Option.getD_some, Option.getD_none,
    n01, n1, nend, decide_false, Bool.or_false, if_false, Bool.false_eq_true, if_true]
  rw [deserialize_u64_extract b 0 (by omega) hv]
  simp only [ne_eq, not_true_eq_false, if_false]
  cases SSZType.deserialize SszBridge.forkActivationType (b.extract o0 o1) <;>
    cases SSZType.deserialize
        (.list SszBridge.blobScheduleType SszBridge.maxBlobSchedulesPerFork)
        (b.extract o1 b.size) <;> rfl

/-! ## The per-field `used` check is redundant at the chain's field types

Same obligation as at the entry schema, load-bearing for the same reason: the source decodes each child
with `decodeCanonical`, which checks `used = slice.size`, while `deserializeVarFields` **discards** each
field's `used`. If the check were not redundant the source would be strictly stronger than the oracle and
the agreement would be false.

**`chainConfig`'s case was already proved, and finding that out is the useful part.**
`deserialize_chainConfig_used` exists in `EntryOffsets.lean` — because `chainConfigType` *is* one of the
entry's four fields. The chain and the entry schema **overlap at chainConfig**: it is simultaneously the
bottom of the entry's field list and the top of this chain. So the two fronts were never disjoint, and the
compiler caught the duplicate when I tried to restate it. Worth recording because the module split was
justified on the two schemas being structurally different, which is true, and it would be easy to read
that as their *content* being disjoint, which is false.

`deserialize_container_used` being stated over an arbitrary field list is what makes the two genuinely new
container cases one-liners — the arity-free form written for the entry paying off rather than needing a
chain-specific repeat.

**Coverage, enumerated so the claim is checkable rather than asserted.** Every field of all three chain
containers is now accounted for:

| container        | field                      | discharged by                           |
|------------------|----------------------------|-----------------------------------------|
| `forkActivation` | `.list u64 N` (x2)         | `deserialize_optionalU64_used`           |
| `forkConfig`     | `u64` (prefix)             | `deserialize_u64_extract` (`used = 8 = sz`) |
| `forkConfig`     | `forkActivationType`       | `deserialize_forkActivation_used`        |
| `forkConfig`     | `.list blobScheduleType M` | `deserialize_blobScheduleList_used`      |
| `chainConfig`    | `u64` (prefix)             | `deserialize_u64_extract` (`used = 8 = sz`) |
| `chainConfig`    | `forkConfigType`           | `deserialize_forkConfig_used`            |

The two `u64`s are a different obligation from the rest and it is worth not eliding: they sit in the
*prefix*, where `deserializeVarFields` checks `used ≠ sz` against the field width 8 rather than against
`b.size`, so `deserialize_u64_extract`'s `.ok (v, 8)` is what discharges them. Reading the table as six
instances of one lemma shape would be wrong. -/

theorem deserialize_forkActivation_used {b : ByteArray}
    {x : SszBridge.forkActivationType.interp} {u : Nat}
    (h : SSZType.deserialize SszBridge.forkActivationType b = .ok (x, u)) : u = b.size :=
  deserialize_container_used _ b forkActivationType_not_fixed x u h

theorem deserialize_forkConfig_used {b : ByteArray}
    {x : SszBridge.forkConfigType.interp} {u : Nat}
    (h : SSZType.deserialize SszBridge.forkConfigType b = .ok (x, u)) : u = b.size :=
  deserialize_container_used _ b forkConfigType_not_fixed x u h

/-- The optional-`u64` field of `forkActivation`: a **fixed**-element list, so it takes the
`deserializeFixedElems` arm rather than the variable-container one. Same shape as the entry's
public-keys field, and the reason the two variable containers above cannot cover it. -/
theorem deserialize_optionalU64_used {b : ByteArray}
    {x : (SSZType.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues).interp} {u : Nat}
    (h : SSZType.deserialize
        (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) b = .ok (x, u)) :
    u = b.size := by
  rw [SSZType.deserialize, if_pos (by decide)] at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · rename_i hcount
        split at h
        · exact absurd h (by simp)
        · rename_i xs used hfixed
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            have := deserializeFixedElems_size _ _ b 0 _ [] 0 xs used hfixed
            omega
          · exact absurd h (by simp)

/-- `forkConfig`'s third field. `blobScheduleType` is `.container [u64, u64, u64]`, all-fixed, so this
is a **fixed**-element list and takes the `deserializeFixedElems` arm — the same shape as
`optionalU64` and the entry's public-keys field, and not reachable by either container lemma. -/
theorem deserialize_blobScheduleList_used {b : ByteArray}
    {x : (SSZType.list SszBridge.blobScheduleType SszBridge.maxBlobSchedulesPerFork).interp}
    {u : Nat}
    (h : SSZType.deserialize
        (.list SszBridge.blobScheduleType SszBridge.maxBlobSchedulesPerFork) b = .ok (x, u)) :
    u = b.size := by
  rw [SSZType.deserialize, if_pos (by decide)] at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · rename_i hcount
        split at h
        · exact absurd h (by simp)
        · rename_i xs used hfixed
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            have := deserializeFixedElems_size _ _ b 0 _ [] 0 xs used hfixed
            omega
          · exact absurd h (by simp)

/-! ## Schema-level decomposition, starting at the bottom of the chain

`forkActivation` first, and the order is forced rather than chosen: `chainConfig` nests through
`forkConfig` into `forkActivation`, so a decomposition of the outer ones consumes the inner ones. Bottom-up
is the dependency order.

`forkActivation` is also the cheapest, because it is all-variable — no leading-fixed skip, and no fork
bound. So it is the closest analogue of the entry schema in the whole chain, and these two lemmas are
`extractFieldOffsets_entry_fits` and `decodeCanonical_entry_unfold` at arity two.

**Where the fork bound does *not* go, recorded before it becomes tempting.** `forkConfig`'s decomposition
will have to place the source's `fork > 20` test, which sits *between* the offset-table check and the child
decodes. That ordering is what makes `forkErrorOrderingDiffers` true and is why the container obligation is
acceptance-only. A decomposition that commutes the test past the child decodes would be a fourth statement
defect, not a simplification — standing instruction from lead is to stop and escalate rather than write it. -/

/-- A successful `forkActivation` table read forces room for the table itself. -/
theorem extractFieldOffsets_forkActivation_fits (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1]) : 8 ≤ b.size := by
  rw [extractFieldOffsets_forkActivation] at hoffs
  split at hoffs
  · rename_i h1
    exact readUInt32LE_fits h1
  · exact absurd hoffs (by simp)

/-- `decodeCanonical` at `forkActivation`, reduced to the walk plus the re-serialization test. -/
theorem decodeCanonical_forkActivation_unfold (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1]) (h0 : o0 = 8) :
    SszBridge.decodeCanonical SszBridge.forkActivationType b =
      match SSZType.deserializeVarFields forkActivationFields b 0 [o0, o1] b.size with
      | .error e => .error e
      | .ok v =>
          if SSZType.serialize SszBridge.forkActivationType v == b then .ok v
          else .error .invalidOffset := by
  have hdes : SSZType.deserialize SszBridge.forkActivationType b =
      match SSZType.deserializeVarFields forkActivationFields b 0 [o0, o1] b.size with
      | .error e => .error e
      | .ok v => .ok (v, b.size) := by
    have h8 : 8 ≤ b.size := extractFieldOffsets_forkActivation_fits b o0 o1 hoffs
    show SSZType.deserialize (.container forkActivationFields) b = _
    rw [SSZType.deserialize, if_neg (by rw [forkActivationFields_not_allFixed]; simp)]
    simp only []
    rw [if_neg (by rw [forkActivationFields_fixedSection]; omega)]
    simp only [hoffs, List.head?_cons]
    rw [if_neg (by rw [forkActivationFields_fixedSection, h0]; simp)]
    cases SSZType.deserializeVarFields forkActivationFields b 0 [o0, o1] b.size <;> rfl
  rw [SszBridge.decodeCanonical, hdes]
  cases SSZType.deserializeVarFields forkActivationFields b 0 [o0, o1] b.size <;>
    simp [bind, Except.bind] <;> rfl

end BinaryFv.SSZ.Zesu.SpecCorrespondence
