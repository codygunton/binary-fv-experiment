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

/-! ### The other two unfolds, and the fork bound's conspicuous absence

`forkConfig` and `chainConfig`, completing the unfold layer for the chain. Both are mixed containers, so
their `fits` lemmas read the *last* offset position rather than the first: `forkConfig`'s table is read at
8 and 12, so a successful read forces `16 ≤ b.size`; `chainConfig`'s single offset is read at 8, forcing
`12 ≤ b.size`. Those are the derived fixed-section sizes, arrived at from the read positions rather than
quoted — the same two numbers, reached the other way round.

**The `fork > 20` test does not appear in `decodeCanonical_forkConfig_unfold`, and that is correct rather
than an omission.** These lemmas are pure oracle: `decodeCanonical` at a schema, and `forkConfigType`
types `fork` as an unbounded `u64`. The bound is *source*-side, applied inside `meaningForkConfig` between
the offset check and the child decodes, and it enters only at the join. So there is no ordering question at
this layer — the risk lead flagged arrives one layer up, where the two sides' orderings have to be matched,
and it is recorded at the head of this section.

`h0 : o = 12` for `chainConfig` is the canonicality requirement, and it is the same 12 the source
hard-codes at `Containers.lean:99` — the agreement of those two constants is what the extended differential's
read-position mutation now tests rather than assumes. -/

theorem extractFieldOffsets_forkConfig_fits (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1]) : 16 ≤ b.size := by
  rw [extractFieldOffsets_forkConfig] at hoffs
  split at hoffs
  · rename_i h1
    have := readUInt32LE_fits h1
    omega
  · exact absurd hoffs (by simp)

theorem extractFieldOffsets_chainConfig_fits (b : ByteArray) (o : Nat)
    (hoffs : extractFieldOffsets b chainConfigFields 0 = .ok [o]) : 12 ≤ b.size := by
  rw [extractFieldOffsets_chainConfig] at hoffs
  split at hoffs
  · rename_i h1
    have := readUInt32LE_fits h1
    omega
  · exact absurd hoffs (by simp)

theorem decodeCanonical_forkConfig_unfold (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1]) (h0 : o0 = 16) :
    SszBridge.decodeCanonical SszBridge.forkConfigType b =
      match SSZType.deserializeVarFields forkConfigFields b 0 [o0, o1] b.size with
      | .error e => .error e
      | .ok v =>
          if SSZType.serialize SszBridge.forkConfigType v == b then .ok v
          else .error .invalidOffset := by
  have hdes : SSZType.deserialize SszBridge.forkConfigType b =
      match SSZType.deserializeVarFields forkConfigFields b 0 [o0, o1] b.size with
      | .error e => .error e
      | .ok v => .ok (v, b.size) := by
    have h16 : 16 ≤ b.size := extractFieldOffsets_forkConfig_fits b o0 o1 hoffs
    show SSZType.deserialize (.container forkConfigFields) b = _
    rw [SSZType.deserialize, if_neg (by rw [forkConfigFields_not_allFixed]; simp)]
    simp only []
    rw [if_neg (by rw [forkConfigFields_fixedSection]; omega)]
    simp only [hoffs, List.head?_cons]
    rw [if_neg (by rw [forkConfigFields_fixedSection, h0]; simp)]
    cases SSZType.deserializeVarFields forkConfigFields b 0 [o0, o1] b.size <;> rfl
  rw [SszBridge.decodeCanonical, hdes]
  cases SSZType.deserializeVarFields forkConfigFields b 0 [o0, o1] b.size <;>
    simp [bind, Except.bind] <;> rfl

theorem decodeCanonical_chainConfig_unfold (b : ByteArray) (o : Nat)
    (hoffs : extractFieldOffsets b chainConfigFields 0 = .ok [o]) (h0 : o = 12) :
    SszBridge.decodeCanonical SszBridge.chainConfigType b =
      match SSZType.deserializeVarFields chainConfigFields b 0 [o] b.size with
      | .error e => .error e
      | .ok v =>
          if SSZType.serialize SszBridge.chainConfigType v == b then .ok v
          else .error .invalidOffset := by
  have hdes : SSZType.deserialize SszBridge.chainConfigType b =
      match SSZType.deserializeVarFields chainConfigFields b 0 [o] b.size with
      | .error e => .error e
      | .ok v => .ok (v, b.size) := by
    have h12 : 12 ≤ b.size := extractFieldOffsets_chainConfig_fits b o hoffs
    show SSZType.deserialize (.container chainConfigFields) b = _
    rw [SSZType.deserialize, if_neg (by rw [chainConfigFields_not_allFixed]; simp)]
    simp only []
    rw [if_neg (by rw [chainConfigFields_fixedSection]; omega)]
    simp only [hoffs, List.head?_cons]
    rw [if_neg (by rw [chainConfigFields_fixedSection, h0]; simp)]
    cases SSZType.deserializeVarFields chainConfigFields b 0 [o] b.size <;> rfl
  rw [SszBridge.decodeCanonical, hdes]
  cases SSZType.deserializeVarFields chainConfigFields b 0 [o] b.size <;>
    simp [bind, Except.bind] <;> rfl

/-! ### The source's offset check at the three chain tables

`requireCanonicalOffsets_entry` at the chain's arities. Each is `canonicalOffsetsCharacterization_holds`
specialised to the concrete call the source makes, and in each the first offset is pinned by **equality**
to the derived fixed-section size — 8, 16, 12 — not merely bounded by it. That equality is what forbids
padding between the fixed section and the first variable field.

**Arity one is not arity two with a conjunct deleted, which is the trap here.** For `chainConfig`'s
single-offset table `Nondecreasing` holds vacuously — there is no pair to compare — so `simp` discharges
that conjunct outright and the characterization has *three* components where the other two have four. The
destructuring patterns therefore differ, and writing the arity-two pattern at arity one fails with
"not an inductive datatype" rather than with anything that suggests the real cause. Noted in the proof.

These are what the joins will consume to turn "the source accepted the table" into the `o0 = fixedSection`
and monotonicity facts the unfold lemmas require. -/

theorem requireCanonicalOffsets_forkActivation (b : ByteArray) (o0 o1 : Nat) :
    meaningRequireCanonicalOffsets b 8 [o0, o1] = .ok () ↔
      (8 ≤ b.size ∧ o0 = 8 ∧ o0 ≤ o1 ∧ o1 ≤ b.size) := by
  rw [canonicalOffsetsCharacterization_holds b 8 [o0, o1]]
  simp only [Nondecreasing, List.mem_cons, List.not_mem_nil, List.headD_cons,
    ne_eq, reduceCtorEq, not_false_eq_true, true_and]
  constructor
  · rintro ⟨hfix, hhead, ⟨h01, -⟩, hall⟩
    exact ⟨hfix, hhead, h01, hall o1 (by simp)⟩
  · rintro ⟨hfix, hhead, h01, h1⟩
    refine ⟨hfix, hhead, ⟨h01, trivial⟩, ?_⟩
    intro offset hmem
    simp only [or_false] at hmem
    rcases hmem with rfl | rfl <;> omega

theorem requireCanonicalOffsets_forkConfig (b : ByteArray) (o0 o1 : Nat) :
    meaningRequireCanonicalOffsets b 16 [o0, o1] = .ok () ↔
      (16 ≤ b.size ∧ o0 = 16 ∧ o0 ≤ o1 ∧ o1 ≤ b.size) := by
  rw [canonicalOffsetsCharacterization_holds b 16 [o0, o1]]
  simp only [Nondecreasing, List.mem_cons, List.not_mem_nil, List.headD_cons,
    ne_eq, reduceCtorEq, not_false_eq_true, true_and]
  constructor
  · rintro ⟨hfix, hhead, ⟨h01, -⟩, hall⟩
    exact ⟨hfix, hhead, h01, hall o1 (by simp)⟩
  · rintro ⟨hfix, hhead, h01, h1⟩
    refine ⟨hfix, hhead, ⟨h01, trivial⟩, ?_⟩
    intro offset hmem
    simp only [or_false] at hmem
    rcases hmem with rfl | rfl <;> omega

theorem requireCanonicalOffsets_chainConfig (b : ByteArray) (o : Nat) :
    meaningRequireCanonicalOffsets b 12 [o] = .ok () ↔ (12 ≤ b.size ∧ o = 12 ∧ o ≤ b.size) := by
  rw [canonicalOffsetsCharacterization_holds b 12 [o]]
  simp only [Nondecreasing, List.mem_cons, List.not_mem_nil, List.headD_cons,
    ne_eq, reduceCtorEq, not_false_eq_true, true_and]
  constructor
  -- Arity one: `Nondecreasing` on a singleton is trivially true, so `simp` has already discharged
  -- that conjunct and only three remain -- unlike the two-offset cases above.
  · rintro ⟨hfix, hhead, hall⟩
    exact ⟨hfix, hhead, hall o (by simp)⟩
  · rintro ⟨hfix, hhead, h1⟩
    refine ⟨hfix, hhead, ?_⟩
    intro offset hmem
    simp only [or_false] at hmem
    subst hmem
    omega

/-! ### The rejection side of the `forkActivation` join

The three places the two sides differ, at this schema, closed the same way as at the entry: the
eight-byte test (source explicit, oracle via the derived `fixedSectionSizeFields`), the table's existence
above eight bytes, and the offset discipline — which again has to be run *backwards*, from a successful
walk to the inequalities it must have passed, because the oracle has no single counterpart check.

**One application of `deserializeVarFields_var_guard` suffices here where the entry needed three.** At
arity two the first application already reads `o1 ≤ b.size` off the last offset's sentinel, so both
conjuncts fall out at once. That is the arity-free guard paying off a third time — it was written for the
entry, reused at `chainConfig`, and here it collapses the whole iteration.

**Not gated.** Lead's differential gate is on the join to `meaningChainConfig` specifically, which is where
`sourceShapedContainersAgreeWithOracle` is stated and where a false statement gets expensive. Nothing here
touches that obligation: `forkActivation` carries no fork bound and no obligation is stated at it.

**Still owed for this join:** the accepting case — the value-level decomposition and the re-serialization
equality at arity two, which is what `serialize_entry` and the `append4_*` family did for the entry. That
is the larger half. -/

theorem decodeCanonical_forkActivation_short {b : ByteArray} (h : b.size < 8) :
    SszBridge.decodeCanonical SszBridge.forkActivationType b = .error .tooShort := by
  have hdes : SSZType.deserialize SszBridge.forkActivationType b = .error .tooShort := by
    show SSZType.deserialize (.container forkActivationFields) b = _
    rw [SSZType.deserialize, if_neg (by rw [forkActivationFields_not_allFixed]; simp)]
    simp only []
    rw [if_pos (by rw [forkActivationFields_fixedSection]; omega)]
  rw [SszBridge.decodeCanonical, hdes]
  rfl

theorem forkActivation_offsets_of_eight (b : ByteArray) (h : 8 ≤ b.size) :
    ∃ o0 o1, extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1] := by
  obtain ⟨w0, e0⟩ := readUInt32LE_exists b 0 (by omega)
  obtain ⟨w1, e1⟩ := readUInt32LE_exists b 4 (by omega)
  exact ⟨w0.toNat, w1.toNat, by rw [extractFieldOffsets_forkActivation, e0, e1]⟩

/-- A successful `forkActivation` walk forces the source's monotonicity conjuncts. One application of
the arity-free guard lemma suffices here, where the entry needed three: at arity two the first
application already reads `o1 <= b.size` off the last offset's sentinel. -/
theorem deserializeVarFields_forkActivation_offsets_sound {b : ByteArray} {o0 o1 : Nat}
    {v : SSZType.interpFields forkActivationFields}
    (h : SSZType.deserializeVarFields forkActivationFields b 0 [o0, o1] b.size = .ok v) :
    o0 ≤ o1 ∧ o1 ≤ b.size := by
  have h0 : SSZType.deserializeVarFields
      (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues ::
        [.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues])
      b 0 [o0, o1] b.size = .ok v := h
  obtain ⟨a01, a1, -, -⟩ := deserializeVarFields_var_guard optionalU64Field_not_fixed h0
  simp only [List.head?_cons, Option.getD_some] at a01 a1
  exact ⟨a01, a1⟩

/-- **The oracle rejects exactly the `forkActivation` tables the source rejects.** -/
theorem decodeCanonical_forkActivation_rejects_noncanonical (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1])
    (hbad : ¬ (o0 = 8 ∧ o0 ≤ o1 ∧ o1 ≤ b.size)) :
    (SszBridge.decodeCanonical SszBridge.forkActivationType b).toOption.isSome = false := by
  cases hdc : SszBridge.decodeCanonical SszBridge.forkActivationType b with
  | error e => rfl
  | ok v =>
      exfalso
      obtain ⟨hdes, -⟩ := decodeCanonical_inv hdc
      have hdes' : SSZType.deserialize (.container forkActivationFields) b = .ok (v, b.size) := hdes
      obtain ⟨offs, hext, hhead, hwalk⟩ :=
        deserialize_container_parts forkActivationFields_not_allFixed hdes'
      rw [hoffs] at hext
      have hoff : [o0, o1] = offs := by injection hext
      subst hoff
      rw [forkActivationFields_fixedSection, List.head?_cons, Option.some.injEq] at hhead
      exact hbad ⟨hhead, deserializeVarFields_forkActivation_offsets_sound hwalk⟩

/-! ### The re-serialization side at arity two, and a lemma that turned out not to be needed

`serialize_entry` at arity two: the fixed prefix is two `uint32LE` offsets, the first pinned at the derived
8 and the second at `8 + |s0|`.

**The arity-two slice reassembly needs no new lemma, and that is the point of the arity-free atoms rather
than a lucky break.** The entry's join needed `extract_four` and the `append4_*` family — four regions
hard-coded. Here the requirement is `s0 ++ s1 = b.extract o0 b.size ↔ (s0 = b.extract o0 o1 ∧ s1 = b.extract
o1 b.size)`, which is exactly `append_eq_extract_iff b o0 o1 b.size` with its width hypothesis. That lemma
was written in `EntryOffsets` under the argument that three parallel arity-specific copies would be worse
than two atoms iterated; this is the case it was written for, and the arity-2 instance is the atom itself
with nothing to iterate.

So the remaining gap in the accepting case is narrower than the entry's was: the value-level decomposition,
with the offset arithmetic and the reassembly both already in hand. -/

/-- **The `forkActivation` container's serialization, expanded.** `serialize_entry` at arity two: the
fixed prefix is two `uint32LE` offsets, the first pinned at the derived 8 and the second at
`8 + |s0|`. -/
theorem serialize_forkActivation (v : SSZType.interpFields forkActivationFields)
    (s0 s1 : ByteArray)
    (e0 : SSZType.serialize
        (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) v.1 = s0)
    (e1 : SSZType.serialize
        (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) v.2.1 = s1) :
    SSZType.serialize (.container forkActivationFields) v =
      (uint32LE (Nat.toUInt32 8) ++ uint32LE (Nat.toUInt32 (8 + s0.size))) ++ (s0 ++ s1) := by
  rw [SSZType.serialize]
  simp only [forkActivationFields, SSZType.serializeFieldsAux, optionalU64Field_not_fixed,
    Bool.false_eq_true, if_false, e0, e1, ByteArray.append_empty,
    SSZType.fixedSectionSizeFields, SSZType.fixedSectionSize, BYTES_PER_LENGTH_OFFSET]

/-! ### Recovering the reads behind the `forkActivation` table

`uint32LE_eq_extract_iff` is stated against a *read* at a position, while the decomposition carries the
table as a list of `Nat`s. These recover the two reads that produced them, which is what turns each
offset-**bytes** condition from the re-serialization equality into an offset-**value** condition the
canonicality check can discharge.

Note this pair is genuinely arity-specific and could not be made arity-free the way the walk and
concatenation lemmas were: `uint32LE_eq_extract_iff` is generic in the position, but the *number* of reads
is fixed by the schema's variable-field count, and the conclusion is a tuple of that many iffs. Worth
saying because the arity-free default earned four returns today and it would be easy to over-apply it —
the distinction is that a walk recurses over the list while this destructures it. -/

/-- The two reads behind a `forkActivation` table, recovered from the table itself. -/
theorem forkActivation_offset_reads (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1]) :
    ∃ w0 w1, readUInt32LE b 0 = some w0 ∧ readUInt32LE b 4 = some w1 ∧
      o0 = w0.toNat ∧ o1 = w1.toNat := by
  rw [extractFieldOffsets_forkActivation] at hoffs
  split at hoffs
  · rename_i w0 w1 r0 r1
    simp only [Except.ok.injEq, List.cons.injEq] at hoffs
    exact ⟨w0, w1, r0, r1, hoffs.1.symm, hoffs.2.1.symm⟩
  · exact absurd hoffs (by simp)

/-- Offset **bytes** to offset **values**, at `forkActivation`'s two table positions. The arity-two
analogue of `entry_offsetBytes_iff`, and the last piece the accepting case needs before the value-level
decomposition itself. -/
theorem forkActivation_offsetBytes_iff (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1])
    (n : Nat) (hn : n < UInt32.size) :
    (uint32LE (Nat.toUInt32 n) = b.extract 0 4 ↔ n = o0) ∧
      (uint32LE (Nat.toUInt32 n) = b.extract 4 8 ↔ n = o1) := by
  obtain ⟨w0, w1, r0, r1, e0, e1⟩ := forkActivation_offset_reads b o0 o1 hoffs
  subst e0; subst e1
  exact ⟨uint32LE_eq_extract_iff b 0 n w0 r0 hn, uint32LE_eq_extract_iff b 4 n w1 r1 hn⟩

/-! ### The join condition at arity two

`serialize_entry_eq_body_iff` at arity two: the re-serialization equality splits into the two
offset-table slots plus the variable region.

**A mechanical trap distinct from the defeq family, worth its own note.** The natural move is
`rw [← extract_split b 8 h8]` to open `b` up on the left of the iff. It does that — and *also* rewrites
every `b` under `b.extract` on the right, producing a goal where both sides have been split and no
subsequent lemma matches. `rw` has no notion of which side of an `Iff` you meant. The fix is
`conv => lhs` to scope it, and note `conv_lhs` is **not** available here — only the block form. Two
further wrinkles on the same lemma: rewriting to the *two-part* concatenation over-splits (the next
lemma wants `b.extract 0 b.size`, so rewrite with `ByteArray.extract_zero_size` instead), and that
lemma takes its buffer *implicitly*, so it needs `(b := b)` rather than a positional argument.

Four iterations, against first-try for everything else in this section. The difference is that all of
those were shape-preserving specialisations of an existing lemma, while this one had to *restructure* an
`Iff` — and rewriting inside an `Iff` is where scoping starts to matter. -/

/-- **The `forkActivation` join condition.** `serialize_entry_eq_body_iff` at arity two: the
re-serialization equality splits into the two offset-table slots plus the variable region. -/
theorem serialize_forkActivation_eq_body_iff (b : ByteArray)
    (v : SSZType.interpFields forkActivationFields) (s0 s1 : ByteArray)
    (e0 : SSZType.serialize
        (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) v.1 = s0)
    (e1 : SSZType.serialize
        (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) v.2.1 = s1)
    (h8 : 8 ≤ b.size) :
    SSZType.serialize (.container forkActivationFields) v = b ↔
      (uint32LE (Nat.toUInt32 8) = b.extract 0 4 ∧
        uint32LE (Nat.toUInt32 (8 + s0.size)) = b.extract 4 8 ∧
        s0 ++ s1 = b.extract 8 b.size) := by
  rw [serialize_forkActivation v s0 s1 e0 e1]
  have hp : (uint32LE (Nat.toUInt32 8) ++ uint32LE (Nat.toUInt32 (8 + s0.size))).size = 8 := by
    rw [ByteArray.size_append, uint32LE_size, uint32LE_size]
  -- Only the `b` on the right of the LEFT equation may be split; a bare `rw` rewrites the
  -- occurrences under `b.extract` on the other side of the iff too.
  conv =>
    lhs
    rw [← ByteArray.extract_zero_size (b := b)]
  rw [append_eq_extract_iff b 0 8 b.size (by omega) h8 h8 (by rw [hp])]
  rw [append_eq_extract_iff b 0 4 8 (by omega) (by omega) (by omega) (by rw [uint32LE_size])]
  rw [and_assoc]

/-! ### The accepting case, and `forkActivation`'s oracle-side decomposition is complete

Two canonical field decodes make the whole `forkActivation` decode canonical. This is where every piece
above meets: the unfold, the walk, the join condition, the bytes-to-values step, and the per-field `used`
redundancy.

It compiled first try, which is worth contrasting with the four iterations the join condition took one
section up. The difference is not difficulty but *kind*: the join condition had to restructure an `Iff`,
while this assembles named lemmas in the order the entry's proof already established. Porting a completed
argument is cheap; discovering the shape is not — and both were mostly the same amount of *content*.

**What remains for item 6.2** is now only the source-side halves: `forkActivation`'s two directions joined
into an acceptance statement about `meaningForkActivation`, then the same for `forkConfig` — where the
`fork > 20` test has to be placed and must not be commuted past the child decodes — and then
`chainConfig`, whose join is the one gated on the gate-level differential. -/

/-- **Two canonical field decodes make the `forkActivation` decode canonical.** -/
theorem decodeCanonical_forkActivation_eq_of_fields (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1])
    (h0 : o0 = 8) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) (hu32 : b.size < UInt32.size)
    {x0 x1 : (SSZType.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues).interp}
    (a0 : SszBridge.decodeCanonical
        (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) (b.extract o0 o1) = .ok x0)
    (a1 : SszBridge.decodeCanonical
        (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues)
        (b.extract o1 b.size) = .ok x1) :
    SszBridge.decodeCanonical SszBridge.forkActivationType b = .ok (x0, x1, PUnit.unit) := by
  have husz : UInt32.size = 4294967296 := rfl
  obtain ⟨d0, s0eq⟩ := decodeCanonical_inv a0
  obtain ⟨d1, s1eq⟩ := decodeCanonical_inv a1
  subst h0
  have w0 : (SSZType.serialize
      (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) x0).size = o1 - 8 := by
    rw [s0eq, ByteArray.size_extract]; omega
  have hcum : 8 + (SSZType.serialize
      (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) x0).size = o1 := by
    rw [w0]; omega
  rw [decodeCanonical_forkActivation_unfold b 8 o1 hoffs rfl,
    deserializeVarFields_forkActivation b 8 o1 h01 h1, d0, d1]
  have hser : SSZType.serialize SszBridge.forkActivationType
      ((x0, x1, PUnit.unit) : SSZType.interpFields forkActivationFields) = b := by
    show SSZType.serialize (.container forkActivationFields) _ = b
    rw [serialize_forkActivation_eq_body_iff b (x0, x1, PUnit.unit) _ _ rfl rfl (by omega)]
    simp only []
    refine ⟨?_, ?_, ?_⟩
    · exact ((forkActivation_offsetBytes_iff b 8 o1 hoffs 8 (by omega)).1).mpr rfl
    · exact ((forkActivation_offsetBytes_iff b 8 o1 hoffs _ (by omega)).2).mpr hcum
    · exact (append_eq_extract_iff b 8 o1 b.size h01 h1 h1 (by rw [w0])).mpr ⟨s0eq, s1eq⟩
  simp only []
  rw [hser, byteArray_beq_self]
  rfl

/-! ### Wiring to the source's field meanings

The source side of `forkActivation` is easier than the entry's was, and for a structural reason worth
naming: **both** its fields are `meaningOptionalU64`, which is `decodeCanonical` plus a projection. So both
agree with the oracle *by construction* rather than by theorem, and unlike the entry there is no
source-shaped field here at all — no `meaningChainConfig` analogue, no fork bound. The asymmetry that made
`entry_field_meanings_in_oracle_terms` interesting is simply absent at this schema.

That is also why `forkActivation` is where the chain should have been started: it is the one link whose
source side carries no assumption. -/

/-- `forkActivation`'s two field types are exactly the schema `meaningOptionalU64` decodes against.
Checked rather than assumed: the entry work needed the same check at `publicKeysType`, and "two
spellings of one schema" is where a source-side bridge silently fails to apply. -/
theorem optionalU64Type_eq_forkActivation_field :
    optionalU64Type = .list SszBridge.u64 SszBridge.maxOptionalForkActivationValues := rfl

/-- `meaningOptionalU64` is oracle-shaped: `decodeCanonical` plus a projection, so its acceptance is the
oracle's by construction. The projection is applied only on the `.ok` arm and cannot turn acceptance into
rejection or back. -/
theorem meaningOptionalU64_accepted (b : ByteArray) :
    isAccepted (meaningOptionalU64 b)
      = (SszBridge.decodeCanonical optionalU64Type b).toOption.isSome := by
  cases h : SszBridge.decodeCanonical optionalU64Type b <;>
    simp [meaningOptionalU64, isAccepted, Except.toOption, h]

/-! ### Acceptance granularity, in the form the composition holds

Two corollaries rather than one, and the second is the one that gets used. The composition's backward
direction arrives carrying `isSome` *facts* about the two fields, not *witnesses* for them — the values
were discarded by whatever produced the acceptance. `except_isSome_iff` recovers them, so
`_of_accepted` is `_of_fields` with that step folded in.

Stating both is deliberate: the value-level form is what the *proof* needs internally (the offset
arithmetic is about the serialized widths, which only exist once you have the values), while the
acceptance form is what the *caller* can supply. Collapsing them into one would force every call site to
produce witnesses it does not have. Same split as `decodeCanonical_entry_of_fields` versus the `mpr`
branch of `decodeCanonical_entry_iff_fields` at the entry. -/

/-- Acceptance-granularity corollary of the value-level statement. -/
theorem decodeCanonical_forkActivation_of_fields (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1])
    (h0 : o0 = 8) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) (hu32 : b.size < UInt32.size)
    {x0 x1 : (SSZType.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues).interp}
    (a0 : SszBridge.decodeCanonical
        (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues) (b.extract o0 o1) = .ok x0)
    (a1 : SszBridge.decodeCanonical
        (.list SszBridge.u64 SszBridge.maxOptionalForkActivationValues)
        (b.extract o1 b.size) = .ok x1) :
    (SszBridge.decodeCanonical SszBridge.forkActivationType b).toOption.isSome = true := by
  rw [decodeCanonical_forkActivation_eq_of_fields b o0 o1 hoffs h0 h01 h1 hu32 a0 a1]
  rfl

/-- The same, from *acceptance* of the two fields rather than from named values — the form the
composition's backward direction actually holds, since it arrives with `isSome` facts rather than
witnesses. `except_isSome_iff` supplies the witnesses. -/
theorem decodeCanonical_forkActivation_of_accepted (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1])
    (h0 : o0 = 8) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) (hu32 : b.size < UInt32.size)
    (a0 : (SszBridge.decodeCanonical optionalU64Type (b.extract o0 o1)).toOption.isSome = true)
    (a1 : (SszBridge.decodeCanonical optionalU64Type (b.extract o1 b.size)).toOption.isSome = true) :
    (SszBridge.decodeCanonical SszBridge.forkActivationType b).toOption.isSome = true := by
  obtain ⟨x0, e0⟩ := except_isSome_iff.mp a0
  obtain ⟨x1, e1⟩ := except_isSome_iff.mp a1
  exact decodeCanonical_forkActivation_of_fields b o0 o1 hoffs h0 h01 h1 hu32 e0 e1

/-! ### The forward direction, and `forkActivation`'s composition is both-ways

From the oracle's acceptance of the whole `forkActivation` body to the two per-field canonical decodes.
The same pieces as the backward direction run the other way: the re-serialization equality is *given*
here and has to be taken apart rather than assembled.

The one failure worth recording is the recurring family, arriving exactly where the module notes predict:
the goal carries `optionalU64Type` while `decodeCanonical_of_used_eq` produces the unfolded
`.list u64 maxOptionalForkActivationValues`. Defeq, not syntactically equal, so `rw` cannot see it and
`simp only [optionalU64Type]` crosses it. That is the fifth instance of this family in the project and the
first where the note was consulted *before* guessing — which is the only reason it cost one line instead
of a round trip.

With this and `_of_accepted`, `forkActivation`'s oracle-side composition holds in both directions. What
remains for the link is the join to `meaningForkActivation`, which now has both halves available. -/

theorem decodeCanonical_forkActivation_fields_of (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1])
    (h0 : o0 = 8) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) (hu32 : b.size < UInt32.size)
    (hacc : (SszBridge.decodeCanonical SszBridge.forkActivationType b).toOption.isSome = true) :
    (SszBridge.decodeCanonical optionalU64Type (b.extract o0 o1)).toOption.isSome = true ∧
      (SszBridge.decodeCanonical optionalU64Type (b.extract o1 b.size)).toOption.isSome = true := by
  have husz : UInt32.size = 4294967296 := rfl
  subst h0
  rw [decodeCanonical_forkActivation_unfold b 8 o1 hoffs rfl,
    deserializeVarFields_forkActivation b 8 o1 h01 h1] at hacc
  split at hacc
  · exact absurd hacc (by simp [Except.toOption])
  · rename_i v heq
    split at hacc
    · rename_i hser
      split at heq
      · exact absurd heq (by simp)
      · rename_i x0 u0 hd0
        split at heq
        · exact absurd heq (by simp)
        · rename_i x1 u1 hd1
          simp only [Except.ok.injEq] at heq
          subst heq
          have hu0 := deserialize_optionalU64_used hd0
          have hu1 := deserialize_optionalU64_used hd1
          subst hu0
          subst hu1
          have hb : SSZType.serialize SszBridge.forkActivationType
              ((x0, x1, PUnit.unit) : SSZType.interpFields forkActivationFields) = b :=
            byteArray_eq_of_beq hser
          have hsplit := (serialize_forkActivation_eq_body_iff b (x0, x1, PUnit.unit)
            _ _ rfl rfl (by omega)).mp hb
          simp only [] at hsplit
          obtain ⟨-, q1, qr⟩ := hsplit
          have hsz := congrArg ByteArray.size qr
          simp only [ByteArray.size_append, ByteArray.size_extract] at hsz
          have c1 := ((forkActivation_offsetBytes_iff b 8 o1 hoffs _ (by omega)).2).mp q1
          obtain ⟨r0, r1⟩ :=
            (append_eq_extract_iff b 8 o1 b.size h01 h1 h1 (by omega)).mp qr
          -- Goal carries the abbreviation, the lemma produces the unfolded list form: the
          -- defeq-not-spelled family. `simp only` on the abbreviation crosses it; `rw` does not.
          simp only [optionalU64Type]
          refine ⟨?_, ?_⟩
          · rw [decodeCanonical_of_used_eq _ _ x0 _ hd0 rfl, r0, byteArray_beq_self]
            rfl
          · rw [decodeCanonical_of_used_eq _ _ x1 _ hd1 rfl, r1, byteArray_beq_self]
            rfl
    · exact absurd hacc (by simp [Except.toOption])

/-! ### The source side's join

`isAccepted_entry_join` at arity two. Both fields' decoded values feed only the returned record, so
acceptance of the whole depends on their acceptance alone — which is what lets the source side be reduced
to a `Bool` conjunction and then matched against the oracle field by field.

Kept as its own lemma rather than inlined for the same reason as the entry's: the `do` block has to be
matched *syntactically* for the rewrite to fire, and unfolding `bind` first turns it into nested
`Except.bind` matches that no `do`-shaped lemma can then match. That was learned the hard way at the entry
and is the reason `except_bind_ok` exists as a targeted lemma instead. -/

/-- The two `forkActivation` field meanings join by conjunction: the decoded values feed only the
returned record, so acceptance of the whole depends on the two fields' acceptance alone.
`isAccepted_entry_join` at arity two. -/
theorem isAccepted_forkActivation_join (s0 s1 : ByteArray) :
    isAccepted (do
        let blockNumber ← meaningOptionalU64 s0
        let timestamp ← meaningOptionalU64 s1
        return ({ blockNumber := blockNumber
                  timestamp := timestamp } : SszBridge.RawForkActivation))
      = (isAccepted (meaningOptionalU64 s0) && isAccepted (meaningOptionalU64 s1)) := by
  cases meaningOptionalU64 s0 <;> cases meaningOptionalU64 s1 <;> rfl

/-! ### The last ingredient: one failing field

The contrapositive of the forward direction, in the disjunctive form the join's case analysis actually
produces. `entry_forkGuard_false` at arity two — **minus the fork-bound conjunct, which has no analogue
here.** At the entry that lemma had to carry a fourth disjunct whose shape differed from the other three,
because `meaningChainConfig` is source-shaped and its acceptance is not plain `isSome`. `forkActivation`
has no such field, so the disjunction is homogeneous.

That difference is the whole reason this link can be finished without
`sourceShapedContainersAgreeWithOracle` while the other two cannot, and it is visible right here in the
shape of the hypothesis rather than only in the prose. -/

/-- One failing field decode kills the whole `forkActivation` decode. The contrapositive of
`decodeCanonical_forkActivation_fields_of`, in the disjunctive form the join's case analysis produces —
`entry_forkGuard_false` at arity two, minus the fork-bound conjunct, which has no analogue here. -/
theorem decodeCanonical_forkActivation_rejects_of_field (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1])
    (h0 : o0 = 8) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) (hu32 : b.size < UInt32.size)
    (hbad :
      (SszBridge.decodeCanonical optionalU64Type (b.extract o0 o1)).toOption.isSome = false ∨
        (SszBridge.decodeCanonical optionalU64Type
          (b.extract o1 b.size)).toOption.isSome = false) :
    (SszBridge.decodeCanonical SszBridge.forkActivationType b).toOption.isSome = false := by
  cases hacc : (SszBridge.decodeCanonical SszBridge.forkActivationType b).toOption.isSome with
  | false => rfl
  | true =>
      obtain ⟨p0, p1⟩ :=
        decodeCanonical_forkActivation_fields_of b o0 o1 hoffs h0 h01 h1 hu32 hacc
      rcases hbad with hb | hb
      · rw [p0] at hb; exact absurd hb (by simp)
      · rw [p1] at hb; exact absurd hb (by simp)

/-! ## The first chain link is CLOSED

`forkActivation_acceptance_agrees`: the source-shaped `meaningForkActivation` and the oracle's
`decodeCanonical forkActivationType` accept the same buffers — **with no assumption at all.** Both fields
are oracle-shaped, so nothing here rests on `sourceShapedContainersAgreeWithOracle`, which makes this the
one link of the three that is unconditionally true rather than conditionally.

The only new lemma the assembly needed was `except_bind_pure`, and it is the defeq family a sixth time:
`let _ ← …` leaves a `pure PUnit.unit` bind, which is `Except.ok PUnit.unit` only up to defeq, so
`except_bind_ok` could not match it. One `rfl` lemma. Worth noting that the entry's assembly never hit
this because its offset check is followed immediately by a *value*-binding `let`, not a discarded one —
the same construct, differing only in whether the bound name is used. -/

/-- `except_bind_ok`'s `pure`-shaped twin. `let _ <- ...` leaves a `pure PUnit.unit` bind, which is
`Except.ok PUnit.unit` only up to defeq -- so `except_bind_ok` cannot match it. -/
theorem except_bind_pure {α β : Type} (a : α) (f : α → Except SszDecodeError β) :
    (pure a : Except SszDecodeError α) >>= f = f a := rfl

/-- **The `forkActivation` link, closed.** Acceptance agreement between the source-shaped
`meaningForkActivation` and the oracle's `decodeCanonical`, with **no assumption** -- both fields are
oracle-shaped, so nothing here rests on `sourceShapedContainersAgreeWithOracle`. -/
theorem forkActivation_acceptance_agrees (b : ByteArray) (hu32 : b.size < UInt32.size) :
    isAccepted (meaningForkActivation b)
      = (SszBridge.decodeCanonical SszBridge.forkActivationType b).toOption.isSome := by
  rw [meaningForkActivation]
  by_cases h8 : b.size < 8
  · rw [if_pos h8, decodeCanonical_forkActivation_short h8]
    rfl
  rw [if_neg h8]
  obtain ⟨o0, o1, hoffs⟩ := forkActivation_offsets_of_eight b (by omega)
  obtain ⟨r0, r1⟩ := (extractFieldOffsets_forkActivation_eq_meaningReads b o0 o1).mp hoffs
  simp only [r0, r1, except_bind_ok]
  by_cases hcan : meaningRequireCanonicalOffsets b 8 [o0, o1] = .ok ()
  · obtain ⟨-, hc0, hc01, hc1⟩ := (requireCanonicalOffsets_forkActivation b o0 o1).mp hcan
    rw [hcan, except_bind_ok, except_bind_pure, isAccepted_forkActivation_join,
      meaningOptionalU64_accepted, meaningOptionalU64_accepted]
    cases hd0 : SszBridge.decodeCanonical optionalU64Type (b.extract o0 o1) with
    | error e0 =>
        rw [decodeCanonical_forkActivation_rejects_of_field b o0 o1 hoffs hc0 hc01 hc1 hu32
          (.inl (by rw [hd0]; rfl))]
        rfl
    | ok x0 =>
      cases hd1 : SszBridge.decodeCanonical optionalU64Type (b.extract o1 b.size) with
      | error e1 =>
          rw [decodeCanonical_forkActivation_rejects_of_field b o0 o1 hoffs hc0 hc01 hc1 hu32
            (.inr (by rw [hd1]; rfl))]
          simp [Except.toOption]
      | ok x1 =>
          rw [decodeCanonical_forkActivation_of_accepted b o0 o1 hoffs hc0 hc01 hc1 hu32
            (by rw [hd0]; rfl) (by rw [hd1]; rfl)]
          simp [Except.toOption]
  · have herr : ∃ e, meaningRequireCanonicalOffsets b 8 [o0, o1] = .error e := by
      cases hc : meaningRequireCanonicalOffsets b 8 [o0, o1] with
      | error e => exact ⟨e, rfl⟩
      | ok u => exact absurd (by rw [hc]) hcan
    obtain ⟨e, he⟩ := herr
    rw [he, except_bind_error]
    have hbad : ¬ (o0 = 8 ∧ o0 ≤ o1 ∧ o1 ≤ b.size) := by
      intro hgood
      exact hcan ((requireCanonicalOffsets_forkActivation b o0 o1).mpr
        ⟨by omega, hgood.1, hgood.2.1, hgood.2.2⟩)
    rw [decodeCanonical_forkActivation_rejects_noncanonical b o0 o1 hoffs hbad]
    rfl

/-! ## Toward the other two links: short buffers and table existence

Direct ports of the `forkActivation` pair to the two mixed containers, and they port cleanly because
neither depends on the leading-fixed skip: the short-buffer case is the container arm's `b.size <
prefixSize` guard at the derived constant, and table existence only needs the reads to succeed at their
positions.

**Where the port will stop, flagged now rather than discovered later.** The next step for both is walk
soundness, and `deserializeVarFields_var_guard` does **not** apply at their heads — it is stated for a
*variable* head field, while `forkConfig` and `chainConfig` both begin with a fixed `u64` that
`deserializeVarFields` reads from the prefix before touching any offset. So a fixed-head step lemma is
genuinely new work, not another instance of the arity-free guard.

That is the same boundary as `forkActivation_offsetBytes_iff`: the arity-free machinery covers walks over
*variable* fields, and the leading-fixed shape sits outside it. Two independent places now where the
entry-derived toolkit stops exactly at the mixed containers, which is the structural reason this chain was
worth a separate module. -/

theorem decodeCanonical_forkConfig_short {b : ByteArray} (h : b.size < 16) :
    SszBridge.decodeCanonical SszBridge.forkConfigType b = .error .tooShort := by
  have hdes : SSZType.deserialize SszBridge.forkConfigType b = .error .tooShort := by
    show SSZType.deserialize (.container forkConfigFields) b = _
    rw [SSZType.deserialize, if_neg (by rw [forkConfigFields_not_allFixed]; simp)]
    simp only []
    rw [if_pos (by rw [forkConfigFields_fixedSection]; omega)]
  rw [SszBridge.decodeCanonical, hdes]
  rfl

theorem decodeCanonical_chainConfig_short {b : ByteArray} (h : b.size < 12) :
    SszBridge.decodeCanonical SszBridge.chainConfigType b = .error .tooShort := by
  have hdes : SSZType.deserialize SszBridge.chainConfigType b = .error .tooShort := by
    show SSZType.deserialize (.container chainConfigFields) b = _
    rw [SSZType.deserialize, if_neg (by rw [chainConfigFields_not_allFixed]; simp)]
    simp only []
    rw [if_pos (by rw [chainConfigFields_fixedSection]; omega)]
  rw [SszBridge.decodeCanonical, hdes]
  rfl

theorem forkConfig_offsets_of_sixteen (b : ByteArray) (h : 16 ≤ b.size) :
    ∃ o0 o1, extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1] := by
  obtain ⟨w0, e0⟩ := readUInt32LE_exists b 8 (by omega)
  obtain ⟨w1, e1⟩ := readUInt32LE_exists b 12 (by omega)
  exact ⟨w0.toNat, w1.toNat, by rw [extractFieldOffsets_forkConfig, e0, e1]⟩

theorem chainConfig_offsets_of_twelve (b : ByteArray) (h : 12 ≤ b.size) :
    ∃ o, extractFieldOffsets b chainConfigFields 0 = .ok [o] := by
  obtain ⟨w, e⟩ := readUInt32LE_exists b 8 (by omega)
  exact ⟨w.toNat, by rw [extractFieldOffsets_chainConfig, e]⟩

/-- **Stepping past a leading FIXED field.** What `deserializeVarFields_var_guard` cannot provide: that
lemma is stated for a variable head and yields offset inequalities, while this steps over a prefix-read
field and yields *no* inequality — a fixed field consumes no offset, so there is nothing to constrain.

`cases varOffs` is load-bearing and is the whole reason the obvious proof fails. `deserializeVarFields`
matches on the field list *and* on `varOffs`, so the generated equation lemmas are indexed by BOTH
scrutinees: there is no equation for an unconstrained `varOffs`, and `rw [SSZType.deserializeVarFields]`
reports "failed to rewrite using equation theorems" without saying which scrutinee was at fault. The
variable-head sibling never hits this because its statement already fixes `varOffs` to `curOff ::
restOffs`. Splitting first makes both equations available; the two branches are then identical, because a
fixed field does not look at the offsets. -/
theorem deserializeVarFields_fixed_step {t : SSZType} {ts : List SSZType} {b : ByteArray}
    {prefixOff : Nat} {varOffs : List Nat} {bufEnd : Nat}
    (hfix : t.isFixedSize = true)
    {v : SSZType.interpFields (t :: ts)}
    (h : SSZType.deserializeVarFields (t :: ts) b prefixOff varOffs bufEnd = .ok v) :
    ∃ v', SSZType.deserializeVarFields ts b (prefixOff + t.fixedByteSize) varOffs bufEnd
      = .ok v' := by
  cases varOffs with
  | nil =>
      rw [SSZType.deserializeVarFields, if_pos hfix] at h
      simp only [] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · rename_i hrec
            exact ⟨_, hrec⟩
  | cons c rest =>
      rw [SSZType.deserializeVarFields, if_pos hfix] at h
      simp only [] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · rename_i hrec
            exact ⟨_, hrec⟩

/-- A successful `forkConfig` walk forces the source's monotonicity conjuncts: step over the fixed `u64`,
then one variable-guard application. -/
theorem deserializeVarFields_forkConfig_offsets_sound {b : ByteArray} {o0 o1 : Nat}
    {v : SSZType.interpFields forkConfigFields}
    (h : SSZType.deserializeVarFields forkConfigFields b 0 [o0, o1] b.size = .ok v) :
    o0 ≤ o1 ∧ o1 ≤ b.size := by
  have h0 : SSZType.deserializeVarFields
      (SszBridge.u64 :: SszBridge.forkActivationType ::
        [.list SszBridge.blobScheduleType SszBridge.maxBlobSchedulesPerFork])
      b 0 [o0, o1] b.size = .ok v := h
  obtain ⟨v1, h1⟩ := deserializeVarFields_fixed_step u64_isFixed h0
  obtain ⟨a01, a1, -, -⟩ := deserializeVarFields_var_guard forkActivationType_not_fixed h1
  simp only [List.head?_cons, Option.getD_some] at a01 a1
  exact ⟨a01, a1⟩

/-- The same at `chainConfig`, whose table is a single offset — so the guard's sentinel supplies
`o ≤ b.size` directly and there is no monotonicity pair to recover. -/
theorem deserializeVarFields_chainConfig_offsets_sound {b : ByteArray} {o : Nat}
    {v : SSZType.interpFields chainConfigFields}
    (h : SSZType.deserializeVarFields chainConfigFields b 0 [o] b.size = .ok v) :
    o ≤ b.size := by
  have h0 : SSZType.deserializeVarFields
      (SszBridge.u64 :: [SszBridge.forkConfigType]) b 0 [o] b.size = .ok v := h
  obtain ⟨v1, h1⟩ := deserializeVarFields_fixed_step u64_isFixed h0
  obtain ⟨a0, -, -, -⟩ := deserializeVarFields_var_guard forkConfigType_not_fixed h1
  simp only [List.head?_nil, Option.getD_none] at a0
  exact a0

/-- **The oracle rejects exactly the `forkConfig` tables the source rejects.** -/
theorem decodeCanonical_forkConfig_rejects_noncanonical (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1])
    (hbad : ¬ (o0 = 16 ∧ o0 ≤ o1 ∧ o1 ≤ b.size)) :
    (SszBridge.decodeCanonical SszBridge.forkConfigType b).toOption.isSome = false := by
  cases hdc : SszBridge.decodeCanonical SszBridge.forkConfigType b with
  | error e => rfl
  | ok v =>
      exfalso
      obtain ⟨hdes, -⟩ := decodeCanonical_inv hdc
      have hdes' : SSZType.deserialize (.container forkConfigFields) b = .ok (v, b.size) := hdes
      obtain ⟨offs, hext, hhead, hwalk⟩ :=
        deserialize_container_parts forkConfigFields_not_allFixed hdes'
      rw [hoffs] at hext
      have hoff : [o0, o1] = offs := by injection hext
      subst hoff
      rw [forkConfigFields_fixedSection, List.head?_cons, Option.some.injEq] at hhead
      exact hbad ⟨hhead, deserializeVarFields_forkConfig_offsets_sound hwalk⟩

/-- **The oracle rejects exactly the `chainConfig` tables the source rejects.** The conjunction has two
parts rather than three: a single-offset table has no monotonicity pair. -/
theorem decodeCanonical_chainConfig_rejects_noncanonical (b : ByteArray) (o : Nat)
    (hoffs : extractFieldOffsets b chainConfigFields 0 = .ok [o])
    (hbad : ¬ (o = 12 ∧ o ≤ b.size)) :
    (SszBridge.decodeCanonical SszBridge.chainConfigType b).toOption.isSome = false := by
  cases hdc : SszBridge.decodeCanonical SszBridge.chainConfigType b with
  | error e => rfl
  | ok v =>
      exfalso
      obtain ⟨hdes, -⟩ := decodeCanonical_inv hdc
      have hdes' : SSZType.deserialize (.container chainConfigFields) b = .ok (v, b.size) := hdes
      obtain ⟨offs, hext, hhead, hwalk⟩ :=
        deserialize_container_parts chainConfigFields_not_allFixed hdes'
      rw [hoffs] at hext
      have hoff : [o] = offs := by injection hext
      subst hoff
      rw [chainConfigFields_fixedSection, List.head?_cons, Option.some.injEq] at hhead
      exact hbad ⟨hhead, deserializeVarFields_chainConfig_offsets_sound hwalk⟩

/-! ## Bytes to values at the mixed containers' table positions

The `forkActivation` pair ported to positions 8/12 and 8, where the leading `u64` has displaced the
table. `uint32LE_eq_extract_iff` is generic in the position, so the ports are mechanical — this is the
step whose *arity* is fixed by the schema but whose *position* is not, which is why it generalises along
one axis and not the other.

Still owed for both accepting cases: the serialization shape. `serialize_forkActivation` will **not**
port, because with a leading fixed field the prefix is `serialize u64 v.1 ++ uint32LE o0 ++ uint32LE o1`
— the fixed field's own bytes sit *before* the offsets, inline, where the all-variable case had offsets
only. That is a third genuinely new shape at the mixed containers, after the reader bridge and the
fixed-head walk step. -/

/-- The two reads behind a `forkConfig` table, recovered from the table itself. Positions 8 and 12 rather
than 0 and 4 — the leading `u64` occupies the first eight bytes. -/
theorem forkConfig_offset_reads (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1]) :
    ∃ w0 w1, readUInt32LE b 8 = some w0 ∧ readUInt32LE b 12 = some w1 ∧
      o0 = w0.toNat ∧ o1 = w1.toNat := by
  rw [extractFieldOffsets_forkConfig] at hoffs
  split at hoffs
  · rename_i w0 w1 r0 r1
    simp only [Except.ok.injEq, List.cons.injEq] at hoffs
    exact ⟨w0, w1, r0, r1, hoffs.1.symm, hoffs.2.1.symm⟩
  · exact absurd hoffs (by simp)

/-- The single read behind a `chainConfig` table. -/
theorem chainConfig_offset_read (b : ByteArray) (o : Nat)
    (hoffs : extractFieldOffsets b chainConfigFields 0 = .ok [o]) :
    ∃ w, readUInt32LE b 8 = some w ∧ o = w.toNat := by
  rw [extractFieldOffsets_chainConfig] at hoffs
  split at hoffs
  · rename_i w r
    simp only [Except.ok.injEq, List.cons.injEq] at hoffs
    exact ⟨w, r, hoffs.1.symm⟩
  · exact absurd hoffs (by simp)

/-- Offset bytes to offset values at `forkConfig`'s table positions. -/
theorem forkConfig_offsetBytes_iff (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1])
    (n : Nat) (hn : n < UInt32.size) :
    (uint32LE (Nat.toUInt32 n) = b.extract 8 12 ↔ n = o0) ∧
      (uint32LE (Nat.toUInt32 n) = b.extract 12 16 ↔ n = o1) := by
  obtain ⟨w0, w1, r0, r1, e0, e1⟩ := forkConfig_offset_reads b o0 o1 hoffs
  subst e0; subst e1
  exact ⟨uint32LE_eq_extract_iff b 8 n w0 r0 hn, uint32LE_eq_extract_iff b 12 n w1 r1 hn⟩

/-- The same at `chainConfig`: one slot, at 8. -/
theorem chainConfig_offsetBytes_iff (b : ByteArray) (o : Nat)
    (hoffs : extractFieldOffsets b chainConfigFields 0 = .ok [o])
    (n : Nat) (hn : n < UInt32.size) :
    uint32LE (Nat.toUInt32 n) = b.extract 8 12 ↔ n = o := by
  obtain ⟨w, r, e⟩ := chainConfig_offset_read b o hoffs
  subst e
  exact uint32LE_eq_extract_iff b 8 n w r hn

end BinaryFv.SSZ.Zesu.SpecCorrespondence
