import BinaryFv.Zesu.MemoryRepresentation.EntryOffsets
import SizzLean.Proofs.SizeBound

/-!
# The activation / forkConfig / chainConfig chain

Item 6.2. Kept in its own module rather than appended to `EntryOffsets`: that file is about the
all-variable entry schema, and the mechanism here is different enough that mixing them would obscure
which lemmas depend on the leading-fixed skip.
-/

namespace BinaryFv.Zesu.MemoryRepresentation

open SizzLean.Spec
open BinaryFv.Zesu.Contracts

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

## Why this module exists, with five independent confirmations

The separate module was originally argued on readability. That argument was weak; the real one is
structural, and it is that **the all-variable entry schema never reads or writes a field inside the fixed
prefix**, so every place the prefix is touched needs its own bridge between the schema vocabulary and the
byte-level one. Five independent pieces turned out not to port from `EntryOffsets`:

1. `deserialize_u64_extract` — the oracle reads the prefix field as a *slice* while the source reads it
   *in place*; a new reader pairing the entry never needed.
2. `deserializeVarFields_fixed_step` — the arity-free `_var_guard` is stated for a *variable* head and
   cannot step over a prefix-read field.
3. `serialize_forkConfig` / `serialize_chainConfig` — the fixed field's bytes sit *inline before* the
   offsets, where the all-variable case had offsets only.
4. `forkConfig_offsetBytes_iff` / `chainConfig_offsetBytes_iff` — the table is *displaced* to 8/12 and 8.
5. `serialize_u64_eq_uint64LE` — two definitions of "write eight little-endian bytes" that are **not**
   definitionally equal, so nothing forces them to agree until proved.

Five independent failures-to-port at the same structural feature is well past coincidence.

## The structural tell: which links carry an assumption

Visible in a *signature* rather than in prose, which makes it the most durable documentation here.
Compare the failing-field lemmas: `decodeCanonical_forkActivation_rejects_of_field`'s disjunction is
**homogeneous** — two conjuncts of the same `isSome = false` form — while the entry's
`entry_forkGuard_false` carries a fourth disjunct of *different shape*, because `meaningChainConfig` is
source-shaped and its acceptance is a match carrying `fork ≤ 20` rather than plain `isSome`.

So: **a homogeneous disjunction means the link rests on no oracle-agreement assumption; an inhomogeneous
one means it does.** `forkActivation` is homogeneous and is closed unconditionally; `forkConfig` and
`chainConfig` are not, and their acceptance joins consume
`sourceShapedContainersAgreeWithOracle`. A reader can check which is which without reading any comment.

The three fixed-section sizes are *derived* by `decide` from the field lists rather than quoted, exactly
as `entryFields_fixedSectionSize` is: 8, 16 and 12 are what the source hard-codes at each level, so if a
field is ever added the mismatch surfaces here instead of silently. -/

def forkActivationFields : List SSZType :=
  [.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues,
    .list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues]

def forkConfigFields : List SSZType :=
  [BinaryFv.Specs.SSZ.u64, BinaryFv.Specs.SSZ.forkActivationType,
    .list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork]

def chainConfigFields : List SSZType :=
  [BinaryFv.Specs.SSZ.u64, BinaryFv.Specs.SSZ.forkConfigType]

/-! Transcription checks: hand-copied field lists, so the compiler holds them. -/

theorem forkActivationType_eq : BinaryFv.Specs.SSZ.forkActivationType = .container forkActivationFields := rfl
theorem forkConfigType_eq : BinaryFv.Specs.SSZ.forkConfigType = .container forkConfigFields := rfl
theorem chainConfigType_eq : BinaryFv.Specs.SSZ.chainConfigType = .container chainConfigFields := rfl

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

@[simp] theorem u64_isFixed : BinaryFv.Specs.SSZ.u64.isFixedSize = true := by decide

@[simp] theorem u64_fixedByteSize : BinaryFv.Specs.SSZ.u64.fixedByteSize = 8 := by decide

@[simp] theorem forkActivationType_not_fixed :
    BinaryFv.Specs.SSZ.forkActivationType.isFixedSize = false := by decide

@[simp] theorem forkConfigType_not_fixed :
    BinaryFv.Specs.SSZ.forkConfigType.isFixedSize = false := by decide

@[simp] theorem optionalU64Field_not_fixed :
    (SSZType.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues).isFixedSize
      = false := by decide

@[simp] theorem blobScheduleListField_not_fixed :
    (SSZType.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork).isFixedSize
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
    SSZType.deserialize BinaryFv.Specs.SSZ.u64 (b.extract i (i + 8)) = .ok (v, 8) := by
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
      match SSZType.deserialize BinaryFv.Specs.SSZ.forkConfigType (b.extract o b.size) with
      | .error e => .error e
      | .ok (x, _) => .ok (v, x, PUnit.unit) := by
  have no : ¬ (o > b.size) := by omega
  have nend : ¬ (b.size > b.size) := by omega
  simp only [chainConfigFields, SSZType.deserializeVarFields, u64_isFixed, u64_fixedByteSize,
    forkConfigType_not_fixed, List.head?_nil, Option.getD_none,
    no, nend, decide_false, Bool.or_false, if_false, Bool.false_eq_true, if_true]
  rw [deserialize_u64_extract b 0 (by omega) hv]
  simp only [ne_eq, not_true_eq_false, if_false]
  cases SSZType.deserialize BinaryFv.Specs.SSZ.forkConfigType (b.extract o b.size) <;> rfl

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
          (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) (b.extract o0 o1) with
      | .error e => .error e
      | .ok (x0, _) =>
        match SSZType.deserialize
            (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues)
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
      (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) (b.extract o0 o1) <;>
    cases SSZType.deserialize
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues)
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
      match SSZType.deserialize BinaryFv.Specs.SSZ.forkActivationType (b.extract o0 o1) with
      | .error e => .error e
      | .ok (x0, _) =>
        match SSZType.deserialize
            (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork)
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
  cases SSZType.deserialize BinaryFv.Specs.SSZ.forkActivationType (b.extract o0 o1) <;>
    cases SSZType.deserialize
        (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork)
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
    {x : BinaryFv.Specs.SSZ.forkActivationType.interp} {u : Nat}
    (h : SSZType.deserialize BinaryFv.Specs.SSZ.forkActivationType b = .ok (x, u)) : u = b.size :=
  deserialize_container_used _ b forkActivationType_not_fixed x u h

theorem deserialize_forkConfig_used {b : ByteArray}
    {x : BinaryFv.Specs.SSZ.forkConfigType.interp} {u : Nat}
    (h : SSZType.deserialize BinaryFv.Specs.SSZ.forkConfigType b = .ok (x, u)) : u = b.size :=
  deserialize_container_used _ b forkConfigType_not_fixed x u h

/-- The optional-`u64` field of `forkActivation`: a **fixed**-element list, so it takes the
`deserializeFixedElems` arm rather than the variable-container one. Same shape as the entry's
public-keys field, and the reason the two variable containers above cannot cover it. -/
theorem deserialize_optionalU64_used {b : ByteArray}
    {x : (SSZType.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues).interp} {u : Nat}
    (h : SSZType.deserialize
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) b = .ok (x, u)) :
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
    {x : (SSZType.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork).interp}
    {u : Nat}
    (h : SSZType.deserialize
        (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork) b = .ok (x, u)) :
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
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b =
      match SSZType.deserializeVarFields forkActivationFields b 0 [o0, o1] b.size with
      | .error e => .error e
      | .ok v =>
          if SSZType.serialize BinaryFv.Specs.SSZ.forkActivationType v == b then .ok v
          else .error .invalidOffset := by
  have hdes : SSZType.deserialize BinaryFv.Specs.SSZ.forkActivationType b =
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
  rw [BinaryFv.Specs.SSZ.decodeCanonical, hdes]
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
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b =
      match SSZType.deserializeVarFields forkConfigFields b 0 [o0, o1] b.size with
      | .error e => .error e
      | .ok v =>
          if SSZType.serialize BinaryFv.Specs.SSZ.forkConfigType v == b then .ok v
          else .error .invalidOffset := by
  have hdes : SSZType.deserialize BinaryFv.Specs.SSZ.forkConfigType b =
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
  rw [BinaryFv.Specs.SSZ.decodeCanonical, hdes]
  cases SSZType.deserializeVarFields forkConfigFields b 0 [o0, o1] b.size <;>
    simp [bind, Except.bind] <;> rfl

theorem decodeCanonical_chainConfig_unfold (b : ByteArray) (o : Nat)
    (hoffs : extractFieldOffsets b chainConfigFields 0 = .ok [o]) (h0 : o = 12) :
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b =
      match SSZType.deserializeVarFields chainConfigFields b 0 [o] b.size with
      | .error e => .error e
      | .ok v =>
          if SSZType.serialize BinaryFv.Specs.SSZ.chainConfigType v == b then .ok v
          else .error .invalidOffset := by
  have hdes : SSZType.deserialize BinaryFv.Specs.SSZ.chainConfigType b =
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
  rw [BinaryFv.Specs.SSZ.decodeCanonical, hdes]
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
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b = .error .tooShort := by
  have hdes : SSZType.deserialize BinaryFv.Specs.SSZ.forkActivationType b = .error .tooShort := by
    show SSZType.deserialize (.container forkActivationFields) b = _
    rw [SSZType.deserialize, if_neg (by rw [forkActivationFields_not_allFixed]; simp)]
    simp only []
    rw [if_pos (by rw [forkActivationFields_fixedSection]; omega)]
  rw [BinaryFv.Specs.SSZ.decodeCanonical, hdes]
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
      (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues ::
        [.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues])
      b 0 [o0, o1] b.size = .ok v := h
  obtain ⟨a01, a1, -, -⟩ := deserializeVarFields_var_guard optionalU64Field_not_fixed h0
  simp only [List.head?_cons, Option.getD_some] at a01 a1
  exact ⟨a01, a1⟩

/-- **The oracle rejects exactly the `forkActivation` tables the source rejects.** -/
theorem decodeCanonical_forkActivation_rejects_noncanonical (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1])
    (hbad : ¬ (o0 = 8 ∧ o0 ≤ o1 ∧ o1 ≤ b.size)) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b).toOption.isSome = false := by
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b with
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
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) v.1 = s0)
    (e1 : SSZType.serialize
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) v.2.1 = s1) :
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
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) v.1 = s0)
    (e1 : SSZType.serialize
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) v.2.1 = s1)
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
    {x0 x1 : (SSZType.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues).interp}
    (a0 : BinaryFv.Specs.SSZ.decodeCanonical
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) (b.extract o0 o1) = .ok x0)
    (a1 : BinaryFv.Specs.SSZ.decodeCanonical
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues)
        (b.extract o1 b.size) = .ok x1) :
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b = .ok (x0, x1, PUnit.unit) := by
  have husz : UInt32.size = 4294967296 := rfl
  obtain ⟨d0, s0eq⟩ := decodeCanonical_inv a0
  obtain ⟨d1, s1eq⟩ := decodeCanonical_inv a1
  subst h0
  have w0 : (SSZType.serialize
      (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) x0).size = o1 - 8 := by
    rw [s0eq, ByteArray.size_extract]; omega
  have hcum : 8 + (SSZType.serialize
      (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) x0).size = o1 := by
    rw [w0]; omega
  rw [decodeCanonical_forkActivation_unfold b 8 o1 hoffs rfl,
    deserializeVarFields_forkActivation b 8 o1 h01 h1, d0, d1]
  have hser : SSZType.serialize BinaryFv.Specs.SSZ.forkActivationType
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
    optionalU64Type = .list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues := rfl

/-- `meaningOptionalU64` is oracle-shaped: `decodeCanonical` plus a projection, so its acceptance is the
oracle's by construction. The projection is applied only on the `.ok` arm and cannot turn acceptance into
rejection or back. -/
theorem meaningOptionalU64_accepted (b : ByteArray) :
    isAccepted (meaningOptionalU64 b)
      = (BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type b).toOption.isSome := by
  cases h : BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type b <;>
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
    {x0 x1 : (SSZType.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues).interp}
    (a0 : BinaryFv.Specs.SSZ.decodeCanonical
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) (b.extract o0 o1) = .ok x0)
    (a1 : BinaryFv.Specs.SSZ.decodeCanonical
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues)
        (b.extract o1 b.size) = .ok x1) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b).toOption.isSome = true := by
  rw [decodeCanonical_forkActivation_eq_of_fields b o0 o1 hoffs h0 h01 h1 hu32 a0 a1]
  rfl

/-- The same, from *acceptance* of the two fields rather than from named values — the form the
composition's backward direction actually holds, since it arrives with `isSome` facts rather than
witnesses. `except_isSome_iff` supplies the witnesses. -/
theorem decodeCanonical_forkActivation_of_accepted (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkActivationFields 0 = .ok [o0, o1])
    (h0 : o0 = 8) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) (hu32 : b.size < UInt32.size)
    (a0 : (BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type (b.extract o0 o1)).toOption.isSome = true)
    (a1 : (BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type (b.extract o1 b.size)).toOption.isSome = true) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b).toOption.isSome = true := by
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
    (hacc : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b).toOption.isSome = true) :
    (BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type (b.extract o0 o1)).toOption.isSome = true ∧
      (BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type (b.extract o1 b.size)).toOption.isSome = true := by
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
          have hb : SSZType.serialize BinaryFv.Specs.SSZ.forkActivationType
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
                  timestamp := timestamp } : BinaryFv.Specs.SSZ.RawForkActivation))
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
      (BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type (b.extract o0 o1)).toOption.isSome = false ∨
        (BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type
          (b.extract o1 b.size)).toOption.isSome = false) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b).toOption.isSome = false := by
  cases hacc : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b).toOption.isSome with
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
theorem except_bind_pure {α β : Type} (a : α) (f : α → Except DecodeError β) :
    (pure a : Except DecodeError α) >>= f = f a := rfl

/-- **The `forkActivation` link, closed.** Acceptance agreement between the source-shaped
`meaningForkActivation` and the oracle's `decodeCanonical`, with **no assumption** -- both fields are
oracle-shaped, so nothing here rests on `sourceShapedContainersAgreeWithOracle`. -/
theorem forkActivation_acceptance_agrees (b : ByteArray) (hu32 : b.size < UInt32.size) :
    isAccepted (meaningForkActivation b)
      = (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b).toOption.isSome := by
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
    cases hd0 : BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type (b.extract o0 o1) with
    | error e0 =>
        rw [decodeCanonical_forkActivation_rejects_of_field b o0 o1 hoffs hc0 hc01 hc1 hu32
          (.inl (by rw [hd0]; rfl))]
        rfl
    | ok x0 =>
      cases hd1 : BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type (b.extract o1 b.size) with
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
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b = .error .tooShort := by
  have hdes : SSZType.deserialize BinaryFv.Specs.SSZ.forkConfigType b = .error .tooShort := by
    show SSZType.deserialize (.container forkConfigFields) b = _
    rw [SSZType.deserialize, if_neg (by rw [forkConfigFields_not_allFixed]; simp)]
    simp only []
    rw [if_pos (by rw [forkConfigFields_fixedSection]; omega)]
  rw [BinaryFv.Specs.SSZ.decodeCanonical, hdes]
  rfl

theorem decodeCanonical_chainConfig_short {b : ByteArray} (h : b.size < 12) :
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b = .error .tooShort := by
  have hdes : SSZType.deserialize BinaryFv.Specs.SSZ.chainConfigType b = .error .tooShort := by
    show SSZType.deserialize (.container chainConfigFields) b = _
    rw [SSZType.deserialize, if_neg (by rw [chainConfigFields_not_allFixed]; simp)]
    simp only []
    rw [if_pos (by rw [chainConfigFields_fixedSection]; omega)]
  rw [BinaryFv.Specs.SSZ.decodeCanonical, hdes]
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
      (BinaryFv.Specs.SSZ.u64 :: BinaryFv.Specs.SSZ.forkActivationType ::
        [.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork])
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
      (BinaryFv.Specs.SSZ.u64 :: [BinaryFv.Specs.SSZ.forkConfigType]) b 0 [o] b.size = .ok v := h
  obtain ⟨v1, h1⟩ := deserializeVarFields_fixed_step u64_isFixed h0
  obtain ⟨a0, -, -, -⟩ := deserializeVarFields_var_guard forkConfigType_not_fixed h1
  simp only [List.head?_nil, Option.getD_none] at a0
  exact a0

/-- **The oracle rejects exactly the `forkConfig` tables the source rejects.** -/
theorem decodeCanonical_forkConfig_rejects_noncanonical (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1])
    (hbad : ¬ (o0 = 16 ∧ o0 ≤ o1 ∧ o1 ≤ b.size)) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b).toOption.isSome = false := by
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b with
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
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b).toOption.isSome = false := by
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b with
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

/-- **The `forkConfig` container's serialization, expanded.** The shape `serialize_forkActivation` could
not supply: with a leading fixed field the prefix is the field's own bytes *inline*, then the two offsets.
So `s0` sits before the table rather than the table starting at byte 0, and the derived 16 is
`u64.fixedByteSize + 2 * BYTES_PER_LENGTH_OFFSET` rather than `2 * BYTES_PER_LENGTH_OFFSET`. -/
theorem serialize_forkConfig (v : SSZType.interpFields forkConfigFields) (s0 s1 s2 : ByteArray)
    (e0 : SSZType.serialize BinaryFv.Specs.SSZ.u64 v.1 = s0)
    (e1 : SSZType.serialize BinaryFv.Specs.SSZ.forkActivationType v.2.1 = s1)
    (e2 : SSZType.serialize
        (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork) v.2.2.1 = s2) :
    SSZType.serialize (.container forkConfigFields) v =
      s0 ++ (uint32LE (Nat.toUInt32 16) ++ uint32LE (Nat.toUInt32 (16 + s1.size)))
        ++ (s1 ++ s2) := by
  rw [SSZType.serialize]
  simp only [forkConfigFields, SSZType.serializeFieldsAux, u64_isFixed, u64_fixedByteSize,
    forkActivationType_not_fixed, blobScheduleListField_not_fixed,
    Bool.false_eq_true, if_false, if_true, e0, e1, e2, ByteArray.append_empty,
    SSZType.fixedSectionSizeFields, SSZType.fixedSectionSize, BYTES_PER_LENGTH_OFFSET]

/-- **The `chainConfig` container's serialization, expanded.** One inline fixed field, one offset, one
body — the simplest of the three shapes, and the only one with no `++` nesting in its variable part at
all, because a single variable field needs no concatenation. -/
theorem serialize_chainConfig (v : SSZType.interpFields chainConfigFields) (s0 s1 : ByteArray)
    (e0 : SSZType.serialize BinaryFv.Specs.SSZ.u64 v.1 = s0)
    (e1 : SSZType.serialize BinaryFv.Specs.SSZ.forkConfigType v.2.1 = s1) :
    SSZType.serialize (.container chainConfigFields) v
      = s0 ++ uint32LE (Nat.toUInt32 12) ++ s1 := by
  rw [SSZType.serialize]
  simp only [chainConfigFields, SSZType.serializeFieldsAux, u64_isFixed, u64_fixedByteSize,
    forkConfigType_not_fixed, Bool.false_eq_true, if_false, if_true, e0, e1,
    ByteArray.append_empty, SSZType.fixedSectionSizeFields, SSZType.fixedSectionSize,
    BYTES_PER_LENGTH_OFFSET]

/-- The leading `u64` serializes to exactly eight bytes. Off upstream's
`size_serialize_eq_fixedByteSize` rather than proved locally — it is one of the thirteen `Proofs`
modules the pin was widened for, and this is the first time that widening has been drawn on for the
chain rather than the entry. -/
theorem serialize_u64_size (x : BinaryFv.Specs.SSZ.u64.interp) :
    (SSZType.serialize BinaryFv.Specs.SSZ.u64 x).size = 8 := by
  rw [SizzLean.Proofs.size_serialize_eq_fixedByteSize (s := BinaryFv.Specs.SSZ.u64)
    (by constructor) (by decide) x]
  exact u64_fixedByteSize

/-- **The `forkConfig` join condition.** Three cuts rather than two: the inline `u64` has to be separated
from the offset table before the table can be separated slot by slot. -/
theorem serialize_forkConfig_eq_body_iff (b : ByteArray)
    (v : SSZType.interpFields forkConfigFields) (s0 s1 s2 : ByteArray)
    (e0 : SSZType.serialize BinaryFv.Specs.SSZ.u64 v.1 = s0)
    (e1 : SSZType.serialize BinaryFv.Specs.SSZ.forkActivationType v.2.1 = s1)
    (e2 : SSZType.serialize
        (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork) v.2.2.1 = s2)
    (h16 : 16 ≤ b.size) :
    SSZType.serialize (.container forkConfigFields) v = b ↔
      (s0 = b.extract 0 8 ∧ uint32LE (Nat.toUInt32 16) = b.extract 8 12 ∧
        uint32LE (Nat.toUInt32 (16 + s1.size)) = b.extract 12 16 ∧
        s1 ++ s2 = b.extract 16 b.size) := by
  have hs0 : s0.size = 8 := by rw [← e0]; exact serialize_u64_size v.1
  rw [serialize_forkConfig v s0 s1 s2 e0 e1 e2]
  have hpre : (s0 ++ (uint32LE (Nat.toUInt32 16)
      ++ uint32LE (Nat.toUInt32 (16 + s1.size)))).size = 16 := by
    rw [ByteArray.size_append, ByteArray.size_append, uint32LE_size, uint32LE_size, hs0]
  conv =>
    lhs
    rw [← ByteArray.extract_zero_size (b := b)]
  rw [append_eq_extract_iff b 0 16 b.size (by omega) h16 h16 (by rw [hpre])]
  rw [append_eq_extract_iff b 0 8 16 (by omega) (by omega) (by omega) (by rw [hs0])]
  rw [append_eq_extract_iff b 8 12 16 (by omega) (by omega) (by omega) (by rw [uint32LE_size])]
  -- Three cuts leave `A ∧ (B ∧ C) ∧ D`; the statement is right-associated. `rw` fires at the wrong
  -- occurrence, `simp only` normalises both sides.
  simp only [and_assoc]

/-- **The `chainConfig` join condition.** Two cuts: the inline `u64`, then the single offset. There is no
table to split slot by slot, so the middle step of `forkConfig`'s three disappears rather than
degenerating -- the fourth time an arity-one case has lost a step outright. -/
theorem serialize_chainConfig_eq_body_iff (b : ByteArray)
    (v : SSZType.interpFields chainConfigFields) (s0 s1 : ByteArray)
    (e0 : SSZType.serialize BinaryFv.Specs.SSZ.u64 v.1 = s0)
    (e1 : SSZType.serialize BinaryFv.Specs.SSZ.forkConfigType v.2.1 = s1)
    (h12 : 12 ≤ b.size) :
    SSZType.serialize (.container chainConfigFields) v = b ↔
      (s0 = b.extract 0 8 ∧ uint32LE (Nat.toUInt32 12) = b.extract 8 12 ∧
        s1 = b.extract 12 b.size) := by
  have hs0 : s0.size = 8 := by rw [← e0]; exact serialize_u64_size v.1
  rw [serialize_chainConfig v s0 s1 e0 e1]
  have hpre : (s0 ++ uint32LE (Nat.toUInt32 12)).size = 12 := by
    rw [ByteArray.size_append, uint32LE_size, hs0]
  conv =>
    lhs
    rw [← ByteArray.extract_zero_size (b := b)]
  rw [append_eq_extract_iff b 0 12 b.size (by omega) h12 h12 (by rw [hpre])]
  rw [append_eq_extract_iff b 0 8 12 (by omega) (by omega) (by omega) (by rw [hs0])]
  simp only [and_assoc]

/-- The two vocabularies for eight little-endian bytes meet. `uint64LE` is the local spelling used by
`uint64LE_of_readUInt64LE`; `SSZType.serialize BinaryFv.Specs.SSZ.u64` is what the container serializer emits for
the inline field. Nothing forces them to agree until it is stated -- the same shape as the
`readU32LE?`-versus-`readUInt32LE` mismatch (R2), one width up and on the *write* side rather than the
read side. -/
theorem serialize_u64_eq_uint64LE (x : BinaryFv.Specs.SSZ.u64.interp) :
    SSZType.serialize BinaryFv.Specs.SSZ.u64 x = uint64LE x := by
  simp [SSZType.serialize, uint64LE]

/-! ## The `u64` read bridges

`readUInt32LE_fits` and `readUInt32LE_extract` one width up. Both port line for line — the `u32`
originals are generic in the offset and specific only in the width, so raising the width is textual.

That is the counterpart to the write-side surprise above: on the WRITE side the two vocabularies were not
definitionally equal and needed a real bridge, while on the READ side the machinery lifts mechanically.
The asymmetry is worth naming because it predicts where the remaining work is — the value-level
decompositions need `uint64LE_eq_extract_iff`, which composes these two with the `bv_decide` primitive
exactly as `uint32LE_eq_extract_iff` does, and so should also be a port rather than new content. -/

/-- A successful eight-byte read forces the room for it. `readUInt32LE_fits` one width up. -/
theorem readUInt64LE_fits {body : ByteArray} {i : Nat} {o : UInt64}
    (h : readUInt64LE body i = some o) : i + 8 ≤ body.size := by
  rw [readUInt64LE] at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- Reading a `uint64` at `i` is reading it at 0 in the eight-byte slice starting at `i`. -/
theorem readUInt64LE_extract (body : ByteArray) (i : Nat) (h : i + 8 ≤ body.size) :
    readUInt64LE (body.extract i (i + 8)) 0 = readUInt64LE body i := by
  have hslice : (body.extract i (i + 8)).size = 8 := by rw [ByteArray.size_extract]; omega
  rw [readUInt64LE, readUInt64LE, dif_pos (by omega : 0 + 8 ≤ (body.extract i (i + 8)).size),
    dif_pos h]
  simp [ByteArray.getElem_extract]

/-- Offset bytes to offset values at `u64` width. A line-for-line port of `uint32LE_eq_extract_iff`,
written from the sibling rather than reconstructed -- which is the lesson the previous two commits paid
for twice.

`hn` is load-bearing for TRUTH here as it is at `u32`: `Nat.toUInt64` wraps at `2 ^ 64`, so without the
bound two different `n` write the same eight bytes and the equivalence is false. -/
theorem uint64LE_eq_extract_iff (body : ByteArray) (i n : Nat) (o : UInt64)
    (hread : readUInt64LE body i = some o) (hn : n < UInt64.size) :
    uint64LE (Nat.toUInt64 n) = body.extract i (i + 8) ↔ n = o.toNat := by
  have hfits : i + 8 ≤ body.size := readUInt64LE_fits hread
  have hslice : (body.extract i (i + 8)).size = 8 := by rw [ByteArray.size_extract]; omega
  have hcanon : uint64LE o = body.extract i (i + 8) :=
    uint64LE_of_readUInt64LE _ o hslice (by rw [readUInt64LE_extract body i hfits]; exact hread)
  rw [← hcanon]
  constructor
  · intro h
    rw [← uint64LE_injective h]
    exact (UInt64.toNat_ofNat_of_lt hn).symm
  · intro h
    subst h
    rw [show Nat.toUInt64 o.toNat = o from UInt64.ofNat_toNat]

/-- **A canonical `forkConfig` child plus the inline `chainId` read make the `chainConfig` decode
canonical.** Note the asymmetry in the hypotheses: the variable field arrives as a `decodeCanonical`, the
fixed field as a raw `readUInt64LE`. That is not a stylistic choice -- the oracle reads the prefix field
directly rather than through `decodeCanonical`, so a `decodeCanonical` hypothesis there would be about a
function the oracle never calls at that position. -/
theorem decodeCanonical_chainConfig_eq_of_fields (b : ByteArray) (o : Nat)
    (hoffs : extractFieldOffsets b chainConfigFields 0 = .ok [o])
    (h0 : o = 12) (h1 : o ≤ b.size) (hu32 : b.size < UInt32.size)
    {x0 : BinaryFv.Specs.SSZ.u64.interp} {x1 : BinaryFv.Specs.SSZ.forkConfigType.interp}
    (a0 : readUInt64LE b 0 = some x0)
    (a1 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType (b.extract o b.size) = .ok x1) :
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b = .ok (x0, x1, PUnit.unit) := by
  have husz : UInt32.size = 4294967296 := rfl
  obtain ⟨d1, s1eq⟩ := decodeCanonical_inv a1
  subst h0
  have h12 : 12 ≤ b.size := extractFieldOffsets_chainConfig_fits b 12 hoffs
  rw [decodeCanonical_chainConfig_unfold b 12 hoffs rfl,
    deserializeVarFields_chainConfig b 12 (by omega) h1 a0, d1]
  have hser : SSZType.serialize BinaryFv.Specs.SSZ.chainConfigType
      ((x0, x1, PUnit.unit) : SSZType.interpFields chainConfigFields) = b := by
    show SSZType.serialize (.container chainConfigFields) _ = b
    rw [serialize_chainConfig_eq_body_iff b (x0, x1, PUnit.unit) _ _ rfl rfl h12]
    simp only []
    refine ⟨?_, ?_, ?_⟩
    · rw [serialize_u64_eq_uint64LE]
      exact uint64LE_of_readUInt64LE _ x0 (by rw [ByteArray.size_extract]; omega)
        (by rw [readUInt64LE_extract b 0 (by omega)]; exact a0)
    · exact (chainConfig_offsetBytes_iff b 12 hoffs 12 (by omega)).mpr rfl
    · exact s1eq
  simp only []
  rw [hser, byteArray_beq_self]
  rfl

/-- **`forkConfig`'s value-level decomposition.** The last of the three, and it carries the same
hypothesis asymmetry as `chainConfig`'s: the inline `fork` field arrives as a raw `readUInt64LE`, the two
variable children as `decodeCanonical`s.

**No `fork > 20` anywhere, deliberately.** This is pure oracle at the schema, and `forkConfigType` types
`fork` as an unbounded `u64`. The bound is the *source*'s, applied inside `meaningForkConfig` between the
offset check and the child decodes, and it enters only at the acceptance join. -/
theorem decodeCanonical_forkConfig_eq_of_fields (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) (hu32 : b.size < UInt32.size)
    {x0 : BinaryFv.Specs.SSZ.u64.interp} {x1 : BinaryFv.Specs.SSZ.forkActivationType.interp}
    {x2 : (SSZType.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork).interp}
    (a0 : readUInt64LE b 0 = some x0)
    (a1 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType (b.extract o0 o1) = .ok x1)
    (a2 : BinaryFv.Specs.SSZ.decodeCanonical
        (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork)
        (b.extract o1 b.size) = .ok x2) :
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b = .ok (x0, x1, x2, PUnit.unit) := by
  have husz : UInt32.size = 4294967296 := rfl
  obtain ⟨d1, s1eq⟩ := decodeCanonical_inv a1
  obtain ⟨d2, s2eq⟩ := decodeCanonical_inv a2
  subst h0
  have h16 : 16 ≤ b.size := extractFieldOffsets_forkConfig_fits b 16 o1 hoffs
  have w1 : (SSZType.serialize BinaryFv.Specs.SSZ.forkActivationType x1).size = o1 - 16 := by
    rw [s1eq, ByteArray.size_extract]; omega
  have hcum : 16 + (SSZType.serialize BinaryFv.Specs.SSZ.forkActivationType x1).size = o1 := by
    rw [w1]; omega
  rw [decodeCanonical_forkConfig_unfold b 16 o1 hoffs rfl,
    deserializeVarFields_forkConfig b 16 o1 (by omega) h01 h1 a0, d1, d2]
  have hser : SSZType.serialize BinaryFv.Specs.SSZ.forkConfigType
      ((x0, x1, x2, PUnit.unit) : SSZType.interpFields forkConfigFields) = b := by
    show SSZType.serialize (.container forkConfigFields) _ = b
    rw [serialize_forkConfig_eq_body_iff b (x0, x1, x2, PUnit.unit) _ _ _ rfl rfl rfl h16]
    simp only []
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [serialize_u64_eq_uint64LE]
      exact uint64LE_of_readUInt64LE _ x0 (by rw [ByteArray.size_extract]; omega)
        (by rw [readUInt64LE_extract b 0 (by omega)]; exact a0)
    · exact ((forkConfig_offsetBytes_iff b 16 o1 hoffs 16 (by omega)).1).mpr rfl
    · exact ((forkConfig_offsetBytes_iff b 16 o1 hoffs _ (by omega)).2).mpr hcum
    · exact (append_eq_extract_iff b 16 o1 b.size h01 h1 h1 (by rw [w1])).mpr ⟨s1eq, s2eq⟩
  simp only []
  rw [hser, byteArray_beq_self]
  rfl

/-! ## The acceptance joins, and why `fork > 20` needs no commuting

Lead's standing instruction is to stop and escalate if a decomposition wants to commute the source's
`fork > 20` test *past* the child decodes, since that ordering is what makes `forkErrorOrderingDiffers`
true. **It does not want to, and the reason is worth stating before the proof rather than discovered
inside it.**

The source checks the bound *before* decoding children; the oracle-shaped right-hand side decodes
everything and then applies it. Those differ in *which error* surfaces, and agree on *acceptance*, case by
case:

| buffer | source | oracle-shaped RHS |
|---|---|---|
| `fork > 20`, children fine | `unknownFork` | decodes, bound fails → `false` |
| `fork > 20`, child malformed | `unknownFork` | decode fails → `false` |
| `fork ≤ 20`, child malformed | child's error | decode fails → `false` |
| `fork ≤ 20`, children fine | accepts | decodes, bound holds → `true` |

Every case agrees on acceptance, and the two middle cases are exactly where the *error* differs. So no
commuting is required — the ordering is unobservable at acceptance granularity, which is precisely what
the obligation being acceptance-only buys, and precisely why stating it with error constructors would make
it and `forkErrorOrderingDiffers` jointly false.

Escalation therefore not triggered. Recorded here rather than only reported, because the next author to
look at this will be tempted by exactly the rearrangement lead warned about. -/

/-- `forkConfig`'s two child meanings join by conjunction. Note the `fork` value is already in hand by
this point in `meaningForkConfig` -- it is read and bound *before* the children -- so it appears as a
parameter rather than as a third conjunct. That asymmetry in the join mirrors the asymmetry in the
decomposition's hypotheses, and for the same reason: the fixed field is not decoded, it is read. -/
theorem isAccepted_forkConfig_join (fork : UInt64) (s1 s2 : ByteArray) :
    isAccepted (do
        let activation ← meaningForkActivation s1
        let blobSchedule ← meaningOptionalBlobSchedule s2
        return ({ fork := fork, activation := activation,
                  blobSchedule := blobSchedule } : BinaryFv.Specs.SSZ.RawForkConfig))
      = (isAccepted (meaningForkActivation s1) && isAccepted (meaningOptionalBlobSchedule s2)) := by
  cases meaningForkActivation s1 <;> cases meaningOptionalBlobSchedule s2 <;> rfl

/-- `forkConfig`'s third field type is exactly the schema `meaningOptionalBlobSchedule` decodes against.
Checked, not assumed -- the third such check in this module, after `publicKeysType` at the entry and
`optionalU64Type` at `forkActivation`. -/
theorem optionalBlobScheduleType_eq_forkConfig_field :
    optionalBlobScheduleType
      = .list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork := rfl

/-- `meaningOptionalBlobSchedule` is oracle-shaped: `decodeCanonical` plus a projection, so its
acceptance is the oracle's by construction. -/
theorem meaningOptionalBlobSchedule_accepted (b : ByteArray) :
    isAccepted (meaningOptionalBlobSchedule b)
      = (BinaryFv.Specs.SSZ.decodeCanonical optionalBlobScheduleType b).toOption.isSome := by
  cases h : BinaryFv.Specs.SSZ.decodeCanonical optionalBlobScheduleType b <;>
    simp [meaningOptionalBlobSchedule, isAccepted, Except.toOption, h]

/-- The source's inline `fork` read, in the form the oracle-side bridges consume. `meaningReadU64` is
`Option.toDecodeResult` over `readUInt64LE`, so this is a re-spelling rather than content -- but it is the
spelling that lets `deserialize_u64_extract` and `uint64LE_of_readUInt64LE` apply. -/
theorem meaningReadU64_eq_some {b : ByteArray} {i : Nat} {x : UInt64}
    (h : meaningReadU64 b i = .ok x) : readUInt64LE b i = some x := by
  -- `Option.toDecodeResult` matches on the option, so its equation lemmas are indexed by that
  -- scrutinee: case FIRST, then unfold. Same cause as the `varOffs` failure in
  -- `deserializeVarFields_fixed_step`, and the rule that came out of it.
  cases hr : readUInt64LE b i with
  | none =>
      rw [meaningReadU64, hr] at h
      exact absurd h (by simp [Option.toDecodeResult])
  | some w =>
      rw [meaningReadU64, hr] at h
      simp only [Option.toDecodeResult, Except.ok.injEq] at h
      exact congrArg some h

/-- **The fork bound is spelled two ways and they agree.** The source tests `fork.toNat > 20` -- a `Nat`
comparison on the widened value -- while `sourceShapedContainersAgreeWithOracle` states the bound as
`… .fork ≤ 20` at `UInt64`. Nothing forces those to coincide until it is proved: this is the same
two-spellings hazard as `readU32LE?`-versus-`readUInt32LE` (R2) and the `u64` write vocabularies, now on
the *comparison* rather than on a read or a write.

They do agree, because `UInt64`'s order is its `toNat` order and `20 < 2 ^ 64` so no wrapping intervenes.
Stated so the acceptance join can move between the two without an unremarked step. -/
theorem fork_bound_toNat_iff (x : UInt64) : x.toNat ≤ 20 ↔ x ≤ 20 := by
  rw [UInt64.le_iff_toNat_le, show ((20 : UInt64)).toNat = 20 from by decide]

/-- Above eight bytes the inline read succeeds. `readUInt32LE_exists` one width up, and the piece the
acceptance joins need to name the `fork`/`chainId` value before knowing anything about it. -/
theorem readUInt64LE_exists (bytes : ByteArray) (offset : Nat) (fits : offset + 8 ≤ bytes.size) :
    ∃ w, readUInt64LE bytes offset = some w := by
  rw [readUInt64LE, dif_pos fits]
  exact ⟨_, rfl⟩

/-- The source's inline read succeeds too, in `meaningReadU64` terms. Pairs with
`meaningReadU64_eq_some` to move between the two spellings in either direction. -/
theorem meaningReadU64_exists (b : ByteArray) (i : Nat) (fits : i + 8 ≤ b.size) :
    ∃ x, meaningReadU64 b i = .ok x := by
  obtain ⟨w, hw⟩ := readUInt64LE_exists b i fits
  exact ⟨w, by rw [meaningReadU64, hw]; rfl⟩

/-- **A successful `forkConfig` decode's `fork` field IS the inline read.** Stated narrowly rather than as
the full forward direction, because the acceptance join needs exactly this and nothing more: to compare the
source's `fork > 20` test against the oracle-shaped bound it must know the two are looking at the same
value. -/
theorem decodeCanonical_forkConfig_fork_eq (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size)
    {x0 : UInt64} (a0 : readUInt64LE b 0 = some x0)
    {v : BinaryFv.Specs.SSZ.forkConfigType.interp}
    (hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b = .ok v) :
    v.1 = x0 := by
  subst h0
  have h16 : 16 ≤ b.size := extractFieldOffsets_forkConfig_fits b 16 o1 hoffs
  rw [decodeCanonical_forkConfig_unfold b 16 o1 hoffs rfl,
    deserializeVarFields_forkConfig b 16 o1 (by omega) h01 h1 a0] at hdc
  split at hdc
  · exact absurd hdc (by simp)
  · -- The outer `split` binds the walk's own match into a hypothesis rather than splitting it; the
    -- remaining case analysis is on THAT, not on the goal.
    rename_i v' heq
    split at heq
    · exact absurd heq (by simp)
    · split at heq
      · exact absurd heq (by simp)
      · simp only [Except.ok.injEq] at heq
        subst heq
        split at hdc
        · simp only [Except.ok.injEq] at hdc
          subst hdc
          rfl
        · exact absurd hdc (by simp)

/-- **A canonical `forkConfig` decode makes both child decodes canonical.** The forward direction, owed
because the `fork ≤ 20` branch of the acceptance join needs decode-succeeds to be *equivalent* to
children-accept, not merely implied by it. Arity-three port of
`decodeCanonical_forkActivation_fields_of`, with the inline field stepped over. -/
theorem decodeCanonical_forkConfig_fields_of (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) (hu32 : b.size < UInt32.size)
    {x : UInt64} (ha0 : readUInt64LE b 0 = some x)
    (hacc : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b).toOption.isSome = true) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType (b.extract o0 o1)).toOption.isSome = true ∧
      (BinaryFv.Specs.SSZ.decodeCanonical
        (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork)
        (b.extract o1 b.size)).toOption.isSome = true := by
  have husz : UInt32.size = 4294967296 := rfl
  subst h0
  have h16 : 16 ≤ b.size := extractFieldOffsets_forkConfig_fits b 16 o1 hoffs
  rw [decodeCanonical_forkConfig_unfold b 16 o1 hoffs rfl,
    deserializeVarFields_forkConfig b 16 o1 (by omega) h01 h1 ha0] at hacc
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
          have hu0 := deserialize_forkActivation_used hd0
          have hu1 := deserialize_blobScheduleList_used hd1
          subst hu0
          subst hu1
          have hb : SSZType.serialize BinaryFv.Specs.SSZ.forkConfigType
              ((x, x0, x1, PUnit.unit) : SSZType.interpFields forkConfigFields) = b :=
            byteArray_eq_of_beq hser
          have hsplit := (serialize_forkConfig_eq_body_iff b (x, x0, x1, PUnit.unit)
            _ _ _ rfl rfl rfl h16).mp hb
          simp only [] at hsplit
          obtain ⟨-, -, q2, qr⟩ := hsplit
          have hsz := congrArg ByteArray.size qr
          simp only [ByteArray.size_append, ByteArray.size_extract] at hsz
          have c1 := ((forkConfig_offsetBytes_iff b 16 o1 hoffs _ (by omega)).2).mp q2
          obtain ⟨r0, r1⟩ :=
            (append_eq_extract_iff b 16 o1 b.size h01 h1 h1 (by omega)).mp qr
          refine ⟨?_, ?_⟩
          · rw [decodeCanonical_of_used_eq _ _ x0 _ hd0 rfl, r0, byteArray_beq_self]
            rfl
          · rw [decodeCanonical_of_used_eq _ _ x1 _ hd1 rfl, r1, byteArray_beq_self]
            rfl
    · exact absurd hacc (by simp [Except.toOption])

/-- One failing child decode kills the whole `forkConfig` decode. Contrapositive of the forward direction,
in the disjunctive form the acceptance join's case analysis produces.

**The disjunction is homogeneous** -- two conjuncts of the same `isSome = false` form -- even though
`forkConfig` is a link that DOES rest on an assumption. So the homogeneity tell recorded in the module
preamble is about the *acceptance join's* failing-field shape at the source level, not about every
`rejects_of_field` lemma: here both children are compared oracle-to-oracle, and the assumption enters
later, at the join, through `meaningForkActivation`. Worth stating so the tell is not over-read. -/
theorem decodeCanonical_forkConfig_rejects_of_field (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) (hu32 : b.size < UInt32.size)
    {x : UInt64} (ha0 : readUInt64LE b 0 = some x)
    (hbad :
      (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType
          (b.extract o0 o1)).toOption.isSome = false ∨
        (BinaryFv.Specs.SSZ.decodeCanonical
          (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork)
          (b.extract o1 b.size)).toOption.isSome = false) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b).toOption.isSome = false := by
  cases hacc : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b).toOption.isSome with
  | false => rfl
  | true =>
      obtain ⟨p0, p1⟩ :=
        decodeCanonical_forkConfig_fields_of b o0 o1 hoffs h0 h01 h1 hu32 ha0 hacc
      rcases hbad with hb | hb
      · rw [p0] at hb; exact absurd hb (by simp)
      · rw [p1] at hb; exact absurd hb (by simp)

/-- **`entry_forkGuard_false` at `forkConfig`.** The match-shaped counterpart of
`decodeCanonical_forkConfig_rejects_of_field`, which concludes about `toOption.isSome` and therefore cannot
rewrite the acceptance join's goal -- that goal is a `match` carrying the fork bound.

Two shapes are needed because `forkConfig` has two right siblings: `forkActivation` is the structural
analogue for the FILE, and its obligation target is plain `isSome` because it carries no bound; the ENTRY is
the analogue for any lemma whose consumer's target carries one. Porting the `isSome` shape here was a
faithful port from the wrong sibling. -/
theorem forkConfig_forkGuard_false (b : ByteArray) (o0 o1 : Nat)
    (hoffs : extractFieldOffsets b forkConfigFields 0 = .ok [o0, o1])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h1 : o1 ≤ b.size) (hu32 : b.size < UInt32.size)
    {x : UInt64} (ha0 : readUInt64LE b 0 = some x)
    (hbad :
      (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType
          (b.extract o0 o1)).toOption.isSome = false ∨
        (BinaryFv.Specs.SSZ.decodeCanonical
          (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork)
          (b.extract o1 b.size)).toOption.isSome = false) :
    (match BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b with
      | .ok v => decide ((BinaryFv.Specs.SSZ.rawForkConfigOf v).fork ≤ 20)
      | .error _ => false) = false := by
  have hrej :=
    decodeCanonical_forkConfig_rejects_of_field b o0 o1 hoffs h0 h01 h1 hu32 ha0 hbad
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b with
  | error e => rfl
  | ok v =>
      rw [hdc] at hrej
      exact absurd hrej (by simp [Except.toOption])

/-- **The `forkConfig` link, closed.** Acceptance agreement between the source-shaped `meaningForkConfig`
and the oracle's canonical decode with the fork bound applied after it.

The `fork > 20` test stays exactly where the source puts it -- between the offset-table check and the child
decodes -- and is never commuted past them. The four-case acceptance table at the head of this section is why
that costs nothing.

**Every leaf that faces the oracle's match destructures the scrutinee rather than rewriting through it.**
`rw` will not cross two `match` terms elaborated in different contexts even when they print identically; the
obstruction dissolves once the scrutinee is a constructor. Same lesson as the fixed-head walk step, where
`cases varOffs` had to come before the unfold. -/
theorem forkConfig_acceptance_agrees (b : ByteArray) (hu32 : b.size < UInt32.size) :
    isAccepted (meaningForkConfig b)
      = (match BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b with
          | .ok v => decide ((BinaryFv.Specs.SSZ.rawForkConfigOf v).fork ≤ 20)
          | .error _ => false) := by
  have husz : UInt32.size = 4294967296 := rfl
  rw [meaningForkConfig]
  by_cases h16 : b.size < 16
  · rw [if_pos h16, decodeCanonical_forkConfig_short h16]
    rfl
  rw [if_neg h16]
  obtain ⟨o0, o1, hoffs⟩ := forkConfig_offsets_of_sixteen b (by omega)
  obtain ⟨r0, r1⟩ := (extractFieldOffsets_forkConfig_eq_meaningReads b o0 o1).mp hoffs
  simp only [r0, r1, except_bind_ok]
  by_cases hcan : meaningRequireCanonicalOffsets b 16 [o0, o1] = .ok ()
  · obtain ⟨-, hc0, hc01, hc1⟩ := (requireCanonicalOffsets_forkConfig b o0 o1).mp hcan
    rw [hcan, except_bind_pure]
    obtain ⟨x, hx⟩ := meaningReadU64_exists b 0 (by omega)
    have ha0 : readUInt64LE b 0 = some x := meaningReadU64_eq_some hx
    simp only [hx, except_bind_ok]
    by_cases hf : x.toNat > 20
    · rw [if_pos hf]
      cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b with
      | error e => rfl
      | ok v =>
          have hv : (BinaryFv.Specs.SSZ.rawForkConfigOf v).fork = x :=
            decodeCanonical_forkConfig_fork_eq b o0 o1 hoffs hc0 hc01 hc1 ha0 hdc
          show (false : Bool) = decide ((BinaryFv.Specs.SSZ.rawForkConfigOf v).fork ≤ 20)
          rw [hv]
          refine (decide_eq_false ?_).symm
          intro hle
          exact absurd ((fork_bound_toNat_iff x).mpr hle) (by omega)
    · rw [if_neg hf, except_bind_pure]
      have hslice1 : (b.extract o0 o1).size < UInt32.size := by
        rw [ByteArray.size_extract]; omega
      rw [isAccepted_forkConfig_join, forkActivation_acceptance_agrees _ hslice1,
        meaningOptionalBlobSchedule_accepted]
      simp only [optionalBlobScheduleType]
      cases hd1 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType (b.extract o0 o1) with
      | error e1 =>
          cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b with
          | error e' => rfl
          | ok v =>
              have hrej := decodeCanonical_forkConfig_rejects_of_field b o0 o1 hoffs hc0 hc01 hc1
                hu32 ha0 (.inl (by rw [hd1]; rfl))
              rw [hdc] at hrej
              exact absurd hrej (by simp [Except.toOption])
      | ok y0 =>
        cases hd2 : BinaryFv.Specs.SSZ.decodeCanonical
            (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork)
            (b.extract o1 b.size) with
        | error e2 =>
            cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b with
            | error e' => simp [Except.toOption]
            | ok v =>
                have hrej := decodeCanonical_forkConfig_rejects_of_field b o0 o1 hoffs hc0 hc01 hc1
                  hu32 ha0 (.inr (by rw [hd2]; rfl))
                rw [hdc] at hrej
                exact absurd hrej (by simp [Except.toOption])
        | ok y1 =>
            have hle : x ≤ 20 := (fork_bound_toNat_iff x).mp (by omega)
            rw [decodeCanonical_forkConfig_eq_of_fields b o0 o1 hoffs hc0 hc01 hc1 hu32 ha0 hd1 hd2]
            simp [Except.toOption, BinaryFv.Specs.SSZ.rawForkConfigOf, hle]
  · have herr : ∃ e, meaningRequireCanonicalOffsets b 16 [o0, o1] = .error e := by
      cases hc : meaningRequireCanonicalOffsets b 16 [o0, o1] with
      | error e => exact ⟨e, rfl⟩
      | ok u => exact absurd (by rw [hc]) hcan
    obtain ⟨e, he⟩ := herr
    rw [he, except_bind_error]
    have hbad : ¬ (o0 = 16 ∧ o0 ≤ o1 ∧ o1 ≤ b.size) := by
      intro hgood
      exact hcan ((requireCanonicalOffsets_forkConfig b o0 o1).mpr
        ⟨by omega, hgood.1, hgood.2.1, hgood.2.2⟩)
    cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b with
    | error e' => rfl
    | ok v =>
        have hrej := decodeCanonical_forkConfig_rejects_noncanonical b o0 o1 hoffs hbad
        rw [hdc] at hrej
        exact absurd hrej (by simp [Except.toOption])

/-- **A canonical `chainConfig` decode makes its child decode canonical.** Forward direction, one child.
Port of `decodeCanonical_forkConfig_fields_of`; the conclusion is a single conjunct rather than a pair
because `chainConfig` has one variable field -- the fifth place arity one drops a component outright rather
than specialising. -/
theorem decodeCanonical_chainConfig_fields_of (b : ByteArray) (o : Nat)
    (hoffs : extractFieldOffsets b chainConfigFields 0 = .ok [o])
    (h0 : o = 12) (h1 : o ≤ b.size) (hu32 : b.size < UInt32.size)
    {x : UInt64} (ha0 : readUInt64LE b 0 = some x)
    (hacc : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b).toOption.isSome = true) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType (b.extract o b.size)).toOption.isSome
      = true := by
  have husz : UInt32.size = 4294967296 := rfl
  subst h0
  have h12 : 12 ≤ b.size := extractFieldOffsets_chainConfig_fits b 12 hoffs
  rw [decodeCanonical_chainConfig_unfold b 12 hoffs rfl,
    deserializeVarFields_chainConfig b 12 (by omega) h1 ha0] at hacc
  split at hacc
  · exact absurd hacc (by simp [Except.toOption])
  · rename_i v heq
    split at hacc
    · rename_i hser
      split at heq
      · exact absurd heq (by simp)
      · rename_i y u hd
        simp only [Except.ok.injEq] at heq
        subst heq
        have hu := deserialize_forkConfig_used hd
        subst hu
        have hb : SSZType.serialize BinaryFv.Specs.SSZ.chainConfigType
            ((x, y, PUnit.unit) : SSZType.interpFields chainConfigFields) = b :=
          byteArray_eq_of_beq hser
        have hsplit :=
          (serialize_chainConfig_eq_body_iff b (x, y, PUnit.unit) _ _ rfl rfl h12).mp hb
        simp only [] at hsplit
        obtain ⟨-, -, qr⟩ := hsplit
        rw [decodeCanonical_of_used_eq _ _ y _ hd rfl, qr, byteArray_beq_self]
        rfl
    · exact absurd hacc (by simp [Except.toOption])

/-- `chainConfig`'s single child meaning: no conjunction at all, since one child cannot disagree with
itself. The `chainId` is already bound when the child runs, so it is a parameter. -/
theorem isAccepted_chainConfig_join (chainId : UInt64) (s : ByteArray) :
    isAccepted (do
        let activeFork ← meaningForkConfig s
        return ({ chainId := chainId, activeFork := activeFork } : BinaryFv.Specs.SSZ.RawChainConfig))
      = isAccepted (meaningForkConfig s) := by
  cases meaningForkConfig s <;> rfl

/-- **The `chainConfig` link, closed -- third of three.** And this statement is
`sourceShapedContainersAgreeWithOracle`'s body verbatim, restricted to `b.size < UInt32.size`.

The parent's bound and the child's are the SAME projection, definitionally: `rawChainConfigOf` sets
`activeFork := rawForkConfigOf value.2.1` (`Core.lean:343-347`), so once
`forkConfig_acceptance_agrees` supplies the child agreement there is nothing left to relate. -/
theorem chainConfig_acceptance_agrees (b : ByteArray) (hu32 : b.size < UInt32.size) :
    isAccepted (meaningChainConfig b)
      = (match BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b with
          | .ok v => decide ((BinaryFv.Specs.SSZ.rawChainConfigOf v).activeFork.fork ≤ 20)
          | .error _ => false) := by
  have husz : UInt32.size = 4294967296 := rfl
  rw [meaningChainConfig]
  by_cases h12 : b.size < 12
  · rw [if_pos h12, decodeCanonical_chainConfig_short h12]
    rfl
  rw [if_neg h12]
  obtain ⟨o, hoffs⟩ := chainConfig_offsets_of_twelve b (by omega)
  have r0 := (extractFieldOffsets_chainConfig_eq_meaningReads b o).mp hoffs
  simp only [r0, except_bind_ok]
  by_cases hcan : meaningRequireCanonicalOffsets b 12 [o] = .ok ()
  · obtain ⟨-, hc0, hc1⟩ := (requireCanonicalOffsets_chainConfig b o).mp hcan
    rw [hcan, except_bind_pure]
    obtain ⟨x, hx⟩ := meaningReadU64_exists b 0 (by omega)
    have ha0 : readUInt64LE b 0 = some x := meaningReadU64_eq_some hx
    simp only [hx, except_bind_ok]
    have hslice : (b.extract o b.size).size < UInt32.size := by
      rw [ByteArray.size_extract]; omega
    rw [isAccepted_chainConfig_join, forkConfig_acceptance_agrees _ hslice]
    cases hd : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType (b.extract o b.size) with
    | error e =>
        -- Destructure rather than rewrite through the match, as at `forkConfig`.
        cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b with
        | error e' => rfl
        | ok v =>
            have hp := decodeCanonical_chainConfig_fields_of b o hoffs hc0 hc1 hu32 ha0
              (by rw [hdc]; rfl)
            rw [hd] at hp
            exact absurd hp (by simp [Except.toOption])
    | ok y =>
        rw [decodeCanonical_chainConfig_eq_of_fields b o hoffs hc0 hc1 hu32 ha0 hd]
        rfl
  · have herr : ∃ e, meaningRequireCanonicalOffsets b 12 [o] = .error e := by
      cases hc : meaningRequireCanonicalOffsets b 12 [o] with
      | error e => exact ⟨e, rfl⟩
      | ok u => exact absurd (by rw [hc]) hcan
    obtain ⟨e, he⟩ := herr
    rw [he, except_bind_error]
    have hbad : ¬ (o = 12 ∧ o ≤ b.size) := by
      intro hgood
      exact hcan ((requireCanonicalOffsets_chainConfig b o).mpr
        ⟨by omega, hgood.1, hgood.2⟩)
    cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b with
    | error e' => rfl
    | ok v =>
        have hrej := decodeCanonical_chainConfig_rejects_noncanonical b o hoffs hbad
        rw [hdc] at hrej
        exact absurd hrej (by simp [Except.toOption])

/-! ## Size bounds for the three chain schemas

Item 6.3. What makes this section short is a division of labour worth recording, because the
opposite conclusion was reached twice before the evidence was checked.

`SizzLean.Proofs.encode_size_le_max` is gated on `SSZType.BasicSupported`, and
`BasicSupported chainConfigType` is **false** — a container with variable-size fields has no
`BasicSupported` constructor. That much is right, and it is why no bound for these three types falls
out of the pin directly. But the predicate is *not* "all-fixed containers only": `BasicSupported`
carries a `listFixed` constructor (`Spec/BasicSupported.lean:96`) admitting `.list t cap` for any
fixed, `BasicSupported`, positively-sized `t`. So the gate does not bite at the two list leaves at
all. It bites at exactly the three variable-field containers, and nowhere else in this chain.

That leaves one structural fact to supply per container — serialization is the fixed section
followed by the concatenated children — and this module already proved it three times, for a
different purpose, in `serialize_forkActivation` / `serialize_forkConfig` / `serialize_chainConfig`.
So the bounds below are assembly: expand, `ByteArray.size_append`, discharge the leaves upstream,
`omega`.

Every statement is against `SSZType.maxByteLength`, never against a numeral. The `hmax` steps
decompose a cap into its constituent caps and offset widths by `decide`, so the concrete byte counts
are derived by the kernel at each use and appear nowhere in the source. Changing a cap in
`BinaryFv.Specs.SSZ` changes what these theorems say, rather than falsifying them silently. -/

/-- `blobScheduleType` is an all-fixed container of three `u64`s, so it is inside the gate. -/
theorem blobScheduleType_basicSupported :
    SSZType.BasicSupported BinaryFv.Specs.SSZ.blobScheduleType :=
  .containerFixed (.cons .uintN64 rfl (.cons .uintN64 rfl (.cons .uintN64 rfl .nil)))

/-- A list of fixed elements is itself `BasicSupported` — the constructor that makes the leaves free.
The third argument is the `0 < t.fixedByteSize` side condition that rules out the `.container []`
element pathology; for `u64` it is `decide`-able. -/
theorem optionalU64List_basicSupported :
    SSZType.BasicSupported
      (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) :=
  .listFixed .uintN64 rfl (by decide)

theorem blobScheduleList_basicSupported :
    SSZType.BasicSupported
      (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork) :=
  .listFixed blobScheduleType_basicSupported rfl (by decide)

theorem optionalU64List_size_le
    (v : (SSZType.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues).interp) :
    (SSZType.serialize
        (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) v).size
      ≤ SSZType.maxByteLength
          (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) :=
  SizzLean.Proofs.encode_size_le_max optionalU64List_basicSupported v

theorem blobScheduleList_size_le
    (v : (SSZType.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork).interp) :
    (SSZType.serialize
        (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork) v).size
      ≤ SSZType.maxByteLength
          (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork) :=
  SizzLean.Proofs.encode_size_le_max blobScheduleList_basicSupported v

/-- Named rather than inlined so `omega` gets the offset width as an equation instead of an opaque
atom; the alternative is writing `4` into each bound proof. -/
theorem bytesPerLengthOffset_eq : BYTES_PER_LENGTH_OFFSET = 4 := rfl

/-- **Base of the induction.** Two variable fields, so the fixed section is two offsets and the cap
is two offset widths plus the two list caps. -/
theorem forkActivation_size_le (v : BinaryFv.Specs.SSZ.forkActivationType.interp) :
    (SSZType.serialize BinaryFv.Specs.SSZ.forkActivationType v).size
      ≤ SSZType.maxByteLength BinaryFv.Specs.SSZ.forkActivationType := by
  have hmax : SSZType.maxByteLength BinaryFv.Specs.SSZ.forkActivationType
      = BYTES_PER_LENGTH_OFFSET + BYTES_PER_LENGTH_OFFSET
        + SSZType.maxByteLength (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues)
        + SSZType.maxByteLength (.list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues) :=
    by decide
  have h0 := optionalU64List_size_le v.1
  have h1 := optionalU64List_size_le v.2.1
  have hb := bytesPerLengthOffset_eq
  show (SSZType.serialize (.container forkActivationFields) v).size ≤ _
  rw [serialize_forkActivation v _ _ rfl rfl]
  simp only [ByteArray.size_append, uint32LE_size]
  omega

/-- **Inductive step, first application.** The leading fixed `u64` contributes its own bytes inline
rather than an offset, which is why `hu` is needed and why the cap has one `maxByteLength u64` term
where `forkActivation`'s has none. -/
theorem forkConfig_size_le (v : BinaryFv.Specs.SSZ.forkConfigType.interp) :
    (SSZType.serialize BinaryFv.Specs.SSZ.forkConfigType v).size
      ≤ SSZType.maxByteLength BinaryFv.Specs.SSZ.forkConfigType := by
  have hmax : SSZType.maxByteLength BinaryFv.Specs.SSZ.forkConfigType
      = SSZType.maxByteLength BinaryFv.Specs.SSZ.u64
        + BYTES_PER_LENGTH_OFFSET + BYTES_PER_LENGTH_OFFSET
        + SSZType.maxByteLength BinaryFv.Specs.SSZ.forkActivationType
        + SSZType.maxByteLength
            (.list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork) := by decide
  have hu : SSZType.maxByteLength BinaryFv.Specs.SSZ.u64 = 8 := by decide
  have h0 := serialize_u64_size v.1
  have h1 := forkActivation_size_le v.2.1
  have h2 := blobScheduleList_size_le v.2.2.1
  have hb := bytesPerLengthOffset_eq
  show (SSZType.serialize (.container forkConfigFields) v).size ≤ _
  rw [serialize_forkConfig v _ _ _ rfl rfl rfl]
  simp only [ByteArray.size_append, uint32LE_size]
  omega

/-- **Inductive step, second application — the bound 6.3 is after.** One inline fixed field and one
offset, so the cap is `maxByteLength u64 + BYTES_PER_LENGTH_OFFSET + maxByteLength forkConfigType`.
Stated against `maxByteLength chainConfigType`: the numeral it evaluates to is deliberately absent. -/
theorem chainConfig_size_le (v : BinaryFv.Specs.SSZ.chainConfigType.interp) :
    (SSZType.serialize BinaryFv.Specs.SSZ.chainConfigType v).size
      ≤ SSZType.maxByteLength BinaryFv.Specs.SSZ.chainConfigType := by
  have hmax : SSZType.maxByteLength BinaryFv.Specs.SSZ.chainConfigType
      = SSZType.maxByteLength BinaryFv.Specs.SSZ.u64 + BYTES_PER_LENGTH_OFFSET
        + SSZType.maxByteLength BinaryFv.Specs.SSZ.forkConfigType := by decide
  have hu : SSZType.maxByteLength BinaryFv.Specs.SSZ.u64 = 8 := by decide
  have h0 := serialize_u64_size v.1
  have h1 := forkConfig_size_le v.2.1
  have hb := bytesPerLengthOffset_eq
  show (SSZType.serialize (.container chainConfigFields) v).size ≤ _
  rw [serialize_chainConfig v _ _ rfl rfl]
  simp only [ByteArray.size_append, uint32LE_size]
  omega

/-! ### Rejection above the bound

The payoff. `decodeCanonical` is a *canonical* decoder: `decodeCanonical_inv` extracts from any
success the fact that the input is literally the re-serialization of the decoded value. So a buffer
longer than the schema's maximum serialization cannot be one, and acceptance is impossible — no
appeal to the decoder's internals, only to the bound above.

This is what subsumes the `hu32` hypothesis threaded through the chain's acceptance joins: a
`b.size < 2^32` side condition is implied by `b.size ≤ maxByteLength chainConfigType` on every
accepted buffer, and on rejected ones the join no longer needs it. -/

theorem decodeCanonical_forkActivation_rejects_oversized {b : ByteArray}
    (hb : SSZType.maxByteLength BinaryFv.Specs.SSZ.forkActivationType < b.size) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b).toOption.isSome = false := by
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b with
  | error e => simp [Except.toOption]
  | ok x =>
      obtain ⟨-, hser⟩ := decodeCanonical_inv hdc
      have hle := forkActivation_size_le x
      rw [hser] at hle
      omega

theorem decodeCanonical_forkConfig_rejects_oversized {b : ByteArray}
    (hb : SSZType.maxByteLength BinaryFv.Specs.SSZ.forkConfigType < b.size) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b).toOption.isSome = false := by
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b with
  | error e => simp [Except.toOption]
  | ok x =>
      obtain ⟨-, hser⟩ := decodeCanonical_inv hdc
      have hle := forkConfig_size_le x
      rw [hser] at hle
      omega

/-- **Both sides reject above the bound**, oracle side. -/
theorem decodeCanonical_chainConfig_rejects_oversized {b : ByteArray}
    (hb : SSZType.maxByteLength BinaryFv.Specs.SSZ.chainConfigType < b.size) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b).toOption.isSome = false := by
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b with
  | error e => simp [Except.toOption]
  | ok x =>
      obtain ⟨-, hser⟩ := decodeCanonical_inv hdc
      have hle := chainConfig_size_le x
      rw [hser] at hle
      omega

/-- Every accepted `chainConfig` buffer is within the schema's maximum, hence well inside `2^32`.
This is the form the acceptance joins consume: it turns `hu32` from a hypothesis that has to be
supplied into a consequence of acceptance. -/
theorem decodeCanonical_chainConfig_size_lt_u32 {b : ByteArray}
    (h : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b).toOption.isSome = true) :
    b.size < 2 ^ 32 := by
  have hcap : SSZType.maxByteLength BinaryFv.Specs.SSZ.chainConfigType < 2 ^ 32 := by decide
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b with
  | error e => rw [hdc] at h; simp [Except.toOption] at h
  | ok x =>
      obtain ⟨-, hser⟩ := decodeCanonical_inv hdc
      have hle := chainConfig_size_le x
      rw [hser] at hle
      omega

/-! ### The source side above the bound, and the obligation it discharges

The oracle side bounds acceptance because `decodeCanonical` re-serializes. The source-shaped side has
no such property -- `meaningChainConfig` never re-serializes anything -- so its bound has to be built
from the shape of the source itself. It bounds out to the *same* number, and the reason is worth
stating: at the leaves the source is not source-shaped at all. `meaningOptionalU64` and
`meaningOptionalBlobSchedule` are **defined as** `decodeCanonical` on `optionalU64Type` /
`optionalBlobScheduleType`, which are definitionally the two list types bounded above. So the leaf
bounds transfer verbatim and only the two variable-field containers need unfolding.

The mechanism of each unfolding is the same: acceptance forces the offset table canonical
(`requireCanonicalOffsets_*` gives `o0 = fixedSize` and monotonicity), which pins each child's slice
to a contiguous span, and the child bounds cap each span. The spans partition the buffer, so the sum
caps the buffer.

**Why this closes the obligation rather than merely supporting it.** `chainConfig_acceptance_agrees`
is the obligation's body verbatim but carries `hu32 : b.size < UInt32.size`. Above `2 ^ 32` neither
side can accept -- the oracle by `decodeCanonical_chainConfig_rejects_oversized`, the source by the
bound below -- so both sides are `false` and the equation holds for a different reason than in the
small case. Two branches, two mechanisms, one theorem, and `hu32` disappears entirely. -/

/-- Restatements at the names the source uses. `optionalU64Type` is *definitionally*
`.list u64 maxOptionalForkActivationValues`, so these are the same theorems -- but `rw` is
syntactic, and a consumer holding `serialize optionalU64Type v = b` cannot rewrite with a lemma
spelled the other way. Naming both spellings is cheaper than unfolding at each use. -/
theorem optionalU64Type_size_le (v : optionalU64Type.interp) :
    (SSZType.serialize optionalU64Type v).size ≤ SSZType.maxByteLength optionalU64Type :=
  optionalU64List_size_le v

theorem optionalBlobScheduleType_size_le (v : optionalBlobScheduleType.interp) :
    (SSZType.serialize optionalBlobScheduleType v).size
      ≤ SSZType.maxByteLength optionalBlobScheduleType :=
  blobScheduleList_size_le v

/-- The leaves, where the source **is** the oracle: `meaningOptionalU64` is defined as
`decodeCanonical optionalU64Type`, so acceptance re-serializes and the upstream bound applies. -/
theorem meaningOptionalU64_accepted_size_le {b : ByteArray}
    (h : isAccepted (meaningOptionalU64 b) = true) :
    b.size ≤ SSZType.maxByteLength optionalU64Type := by
  rw [meaningOptionalU64_accepted] at h
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type b with
  | error e => rw [hdc] at h; simp [Except.toOption] at h
  | ok v =>
      obtain ⟨-, hser⟩ := decodeCanonical_inv hdc
      have hle := optionalU64Type_size_le v
      rw [hser] at hle
      exact hle

theorem meaningOptionalBlobSchedule_accepted_size_le {b : ByteArray}
    (h : isAccepted (meaningOptionalBlobSchedule b) = true) :
    b.size ≤ SSZType.maxByteLength optionalBlobScheduleType := by
  rw [meaningOptionalBlobSchedule_accepted] at h
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical optionalBlobScheduleType b with
  | error e => rw [hdc] at h; simp [Except.toOption] at h
  | ok v =>
      obtain ⟨-, hser⟩ := decodeCanonical_inv hdc
      have hle := optionalBlobScheduleType_size_le v
      rw [hser] at hle
      exact hle

/-- **Base of the source-side induction.** Acceptance forces `first = 8` and `8 ≤ second ≤ size`,
so the two optional-`u64` slices are `[8, second)` and `[second, size)` -- a partition of everything
past the offset table. Each is capped by the leaf bound, so the buffer is capped by their sum plus
the table. -/
theorem meaningForkActivation_accepted_size_le {b : ByteArray}
    (h : isAccepted (meaningForkActivation b) = true) :
    b.size ≤ SSZType.maxByteLength BinaryFv.Specs.SSZ.forkActivationType := by
  have hmax : SSZType.maxByteLength BinaryFv.Specs.SSZ.forkActivationType
      = BYTES_PER_LENGTH_OFFSET + BYTES_PER_LENGTH_OFFSET
        + SSZType.maxByteLength optionalU64Type
        + SSZType.maxByteLength optionalU64Type := by decide
  have hb := bytesPerLengthOffset_eq
  rw [meaningForkActivation] at h
  by_cases h8 : b.size < 8
  · rw [if_pos h8] at h; simp [bind, Except.bind, isAccepted] at h
  rw [if_neg h8] at h
  cases hr0 : meaningReadOffset b 0 with
  | error e => rw [hr0, except_bind_error] at h; simp [isAccepted] at h
  | ok o0 =>
    cases hr1 : meaningReadOffset b 4 with
    | error e => rw [hr0, hr1, except_bind_ok, except_bind_error] at h; simp [isAccepted] at h
    | ok o1 =>
      by_cases hcan : meaningRequireCanonicalOffsets b 8 [o0, o1] = .ok ()
      · obtain ⟨-, hc0, hc01, hc1⟩ := (requireCanonicalOffsets_forkActivation b o0 o1).mp hcan
        rw [hr0, hr1, except_bind_ok, except_bind_ok, hcan, except_bind_ok, except_bind_pure,
          isAccepted_forkActivation_join, Bool.and_eq_true] at h
        obtain ⟨ha0, ha1⟩ := h
        have b0 := meaningOptionalU64_accepted_size_le ha0
        have b1 := meaningOptionalU64_accepted_size_le ha1
        have e0 : (b.extract o0 o1).size = o1 - o0 := by
          simp [ByteArray.size_extract]; omega
        have e1 : (b.extract o1 b.size).size = b.size - o1 := by
          simp [ByteArray.size_extract]
        rw [e0] at b0
        rw [e1] at b1
        omega
      · cases hc : meaningRequireCanonicalOffsets b 8 [o0, o1] with
        | error e =>
            simp [hr0, hr1, hc, bind, Except.bind, pure, Except.pure, isAccepted] at h
        | ok u => cases u; exact absurd hc hcan

/-- **Inductive step.** Same shape one level up, with two differences that both come from the
leading fixed field: the `u64` occupies the first eight bytes inline rather than an offset slot, and
the `fork > 20` test sits between the table check and the child decodes. The test is irrelevant to
the bound -- it can only *reject* -- but it has to be stepped over in the right place, because
commuting it past the child decodes is the statement defect `forkErrorOrderingDiffers` records. -/
theorem meaningForkConfig_accepted_size_le {b : ByteArray}
    (h : isAccepted (meaningForkConfig b) = true) :
    b.size ≤ SSZType.maxByteLength BinaryFv.Specs.SSZ.forkConfigType := by
  have hmax : SSZType.maxByteLength BinaryFv.Specs.SSZ.forkConfigType
      = SSZType.maxByteLength BinaryFv.Specs.SSZ.u64
        + BYTES_PER_LENGTH_OFFSET + BYTES_PER_LENGTH_OFFSET
        + SSZType.maxByteLength BinaryFv.Specs.SSZ.forkActivationType
        + SSZType.maxByteLength optionalBlobScheduleType := by decide
  have hu : SSZType.maxByteLength BinaryFv.Specs.SSZ.u64 = 8 := by decide
  have hb := bytesPerLengthOffset_eq
  rw [meaningForkConfig] at h
  by_cases h16 : b.size < 16
  · rw [if_pos h16] at h; simp [bind, Except.bind, isAccepted] at h
  rw [if_neg h16] at h
  cases hr0 : meaningReadOffset b 8 with
  | error e => rw [hr0, except_bind_error] at h; simp [isAccepted] at h
  | ok o0 =>
    cases hr1 : meaningReadOffset b 12 with
    | error e => rw [hr0, hr1, except_bind_ok, except_bind_error] at h; simp [isAccepted] at h
    | ok o1 =>
      by_cases hcan : meaningRequireCanonicalOffsets b 16 [o0, o1] = .ok ()
      · obtain ⟨-, hc0, hc01, hc1⟩ := (requireCanonicalOffsets_forkConfig b o0 o1).mp hcan
        simp only [hr0, hr1, except_bind_ok, hcan, except_bind_pure] at h
        cases hf : meaningReadU64 b 0 with
        | error e => simp [hf, bind, Except.bind, isAccepted] at h
        | ok fork =>
          simp only [hf, except_bind_ok] at h
          by_cases hfk : fork.toNat > 20
          · simp [if_pos hfk, bind, Except.bind, isAccepted] at h
          simp only [if_neg hfk, isAccepted_forkConfig_join, Bool.and_eq_true] at h
          obtain ⟨ha0, ha1⟩ := h
          have b0 := meaningForkActivation_accepted_size_le ha0
          have b1 := meaningOptionalBlobSchedule_accepted_size_le ha1
          have e0 : (b.extract o0 o1).size = o1 - o0 := by
            simp [ByteArray.size_extract]; omega
          have e1 : (b.extract o1 b.size).size = b.size - o1 := by
            simp [ByteArray.size_extract]
          rw [e0] at b0
          rw [e1] at b1
          omega
      · cases hc : meaningRequireCanonicalOffsets b 16 [o0, o1] with
        | error e =>
            simp [hr0, hr1, hc, bind, Except.bind, pure, Except.pure, isAccepted] at h
        | ok u => cases u; exact absurd hc hcan

/-- **The source-side bound.** One offset, so the single child slice is all of `[12, size)` and the
buffer is twelve bytes plus a `forkConfig`. -/
theorem meaningChainConfig_accepted_size_le {b : ByteArray}
    (h : isAccepted (meaningChainConfig b) = true) :
    b.size ≤ SSZType.maxByteLength BinaryFv.Specs.SSZ.chainConfigType := by
  have hmax : SSZType.maxByteLength BinaryFv.Specs.SSZ.chainConfigType
      = SSZType.maxByteLength BinaryFv.Specs.SSZ.u64 + BYTES_PER_LENGTH_OFFSET
        + SSZType.maxByteLength BinaryFv.Specs.SSZ.forkConfigType := by decide
  have hu : SSZType.maxByteLength BinaryFv.Specs.SSZ.u64 = 8 := by decide
  have hb := bytesPerLengthOffset_eq
  rw [meaningChainConfig] at h
  by_cases h12 : b.size < 12
  · rw [if_pos h12] at h; simp [bind, Except.bind, isAccepted] at h
  rw [if_neg h12] at h
  cases hr0 : meaningReadOffset b 8 with
  | error e => rw [hr0, except_bind_error] at h; simp [isAccepted] at h
  | ok o =>
    by_cases hcan : meaningRequireCanonicalOffsets b 12 [o] = .ok ()
    · obtain ⟨-, hc0, hc1⟩ := (requireCanonicalOffsets_chainConfig b o).mp hcan
      simp only [hr0, except_bind_ok, hcan, except_bind_pure] at h
      cases hi : meaningReadU64 b 0 with
      | error e => simp [hi, bind, Except.bind, isAccepted] at h
      | ok chainId =>
        simp only [hi, except_bind_ok, isAccepted_chainConfig_join] at h
        have b0 := meaningForkConfig_accepted_size_le h
        have e0 : (b.extract o b.size).size = b.size - o := by
          simp [ByteArray.size_extract]
        rw [e0] at b0
        omega
    · cases hc : meaningRequireCanonicalOffsets b 12 [o] with
      | error e =>
          simp [hr0, hc, bind, Except.bind, pure, Except.pure, isAccepted] at h
      | ok u => cases u; exact absurd hc hcan

/-- **ITEM 6.3. The obligation is discharged.**

`sourceShapedContainersAgreeWithOracle` was the single premise the whole oracle-agreement story
rested on -- load-bearing twice over, directly and through `sourceShapedDecodeAgreesWithOracle`.
It is now a theorem.

Below `2 ^ 32` this is `chainConfig_acceptance_agrees` verbatim. Above it, both sides reject and the
equation holds vacuously-in-the-useful-sense: the oracle cannot accept because acceptance would make
the buffer a re-serialization, and the source cannot accept because acceptance would make it a
partition of bounded spans. Neither branch subsumes the other, which is why the size bound was
needed on both sides rather than only on the oracle. -/
theorem sourceShapedContainersAgreeWithOracle_holds :
    sourceShapedContainersAgreeWithOracle := by
  intro bytes
  have husz : UInt32.size = 4294967296 := rfl
  by_cases hu32 : bytes.size < UInt32.size
  · exact chainConfig_acceptance_agrees bytes hu32
  have hcap : SSZType.maxByteLength BinaryFv.Specs.SSZ.chainConfigType < UInt32.size := by decide
  have hsrc : isAccepted (meaningChainConfig bytes) = false := by
    cases hs : isAccepted (meaningChainConfig bytes) with
    | false => rfl
    | true =>
        exfalso
        have := meaningChainConfig_accepted_size_le hs
        omega
  rw [hsrc]
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType bytes with
  | error e => rfl
  | ok v =>
      exfalso
      obtain ⟨-, hser⟩ := decodeCanonical_inv hdc
      have hle := chainConfig_size_le v
      rw [hser] at hle
      omega

/-! ## The chain, with the value

`sourceShapedContainersAgreeWithOracle` is acceptance-only **by construction** — it has to be, since
the source applies the fork bound before decoding children and the oracle after, so the two disagree
about the error constructor and only agree about acceptance (`forkErrorOrderingDiffers` records
exactly that). But `root_compliance`'s accepted branch needs the entry's *value*, and the entry's
third field is a `chainConfig`. So the acceptance-only obligation is not enough here and a genuinely
new statement is owed: **on the accepting branch the two produce the same `RawChainConfig`.**

That is the one place in this proof where new field-level content was required rather
than a restatement. The entry needed none: its other three fields are `decodeCanonical` plus a
projection, and its composition was already value-level backwards. Recorded plainly because the
prediction going in was that nothing new would be needed anywhere.

**What makes it cheap anyway.** Each link is the same three-line move as at the entry: the *backward*
composition is already value-level (`decodeCanonical_*_eq_of_fields` conclude `= .ok (…)`), the
*forward* one is already available at `isSome`, and injectivity of `.ok` closes the gap between
them. What is genuinely new is only the last step of each link — rewriting the source-shaped `do`
block with the children's values instead of with their acceptance — and the fork bound has to be
threaded down one level, from `rawChainConfigOf`'s projection to `rawForkConfigOf`'s, where it is the
same number by `rfl`. Nothing is commuted past the `fork > 20` test: it stays exactly where the
source puts it, and on this branch it simply does not fire. -/

/-- An accepted `forkActivation` buffer is well inside `2 ^ 32`, in the `UInt32.size` spelling the
decompositions want. `decodeCanonical_forkActivation_rejects_oversized` read forwards. -/
theorem forkActivation_size_lt_u32_of_ok {b : ByteArray}
    {x : BinaryFv.Specs.SSZ.forkActivationType.interp}
    (h : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b = .ok x) :
    b.size < UInt32.size := by
  have hcap : SSZType.maxByteLength BinaryFv.Specs.SSZ.forkActivationType < UInt32.size := by decide
  obtain ⟨-, hser⟩ := decodeCanonical_inv h
  have hle := forkActivation_size_le x
  rw [hser] at hle
  omega

theorem forkConfig_size_lt_u32_of_ok {b : ByteArray} {x : BinaryFv.Specs.SSZ.forkConfigType.interp}
    (h : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b = .ok x) :
    b.size < UInt32.size := by
  have hcap : SSZType.maxByteLength BinaryFv.Specs.SSZ.forkConfigType < UInt32.size := by decide
  obtain ⟨-, hser⟩ := decodeCanonical_inv h
  have hle := forkConfig_size_le x
  rw [hser] at hle
  omega

theorem chainConfig_size_lt_u32_of_ok {b : ByteArray} {x : BinaryFv.Specs.SSZ.chainConfigType.interp}
    (h : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b = .ok x) :
    b.size < UInt32.size := by
  have hcap : SSZType.maxByteLength BinaryFv.Specs.SSZ.chainConfigType < UInt32.size := by decide
  obtain ⟨-, hser⟩ := decodeCanonical_inv h
  have hle := chainConfig_size_le x
  rw [hser] at hle
  omega

/-- The two option leaves need no theorem: their meanings *are* `decodeCanonical` plus the bridge's
projection, so a canonical decode rewrites them outright. Stated so the joins below can `rw` rather
than unfold a meaning inside a `do` block. -/
theorem meaningOptionalU64_value {b : ByteArray} {x : optionalU64Type.interp}
    (h : BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type b = .ok x) :
    meaningOptionalU64 b = .ok x.1[0]? := by
  rw [meaningOptionalU64, h]

theorem meaningOptionalBlobSchedule_value {b : ByteArray} {x : optionalBlobScheduleType.interp}
    (h : BinaryFv.Specs.SSZ.decodeCanonical optionalBlobScheduleType b = .ok x) :
    meaningOptionalBlobSchedule b = .ok ((x.1[0]?).map BinaryFv.Specs.SSZ.rawBlobScheduleOf) := by
  rw [meaningOptionalBlobSchedule, h]

/-- **The `forkActivation` link, with the value.** Unconditional, like its acceptance twin and for
the same reason: both fields are oracle-shaped, so nothing here rests on an assumption. -/
theorem meaningForkActivation_value_agrees {b : ByteArray}
    {x : BinaryFv.Specs.SSZ.forkActivationType.interp}
    (hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b = .ok x) :
    meaningForkActivation b = .ok (BinaryFv.Specs.SSZ.rawForkActivationOf x) := by
  have hu32 := forkActivation_size_lt_u32_of_ok hdc
  have hacc : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkActivationType b).toOption.isSome = true := by
    rw [hdc]; rfl
  have h8 : ¬ b.size < 8 := by
    intro hlt
    rw [decodeCanonical_forkActivation_short hlt] at hdc
    exact absurd hdc (by simp)
  obtain ⟨o0, o1, hoffs⟩ := forkActivation_offsets_of_eight b (by omega)
  obtain ⟨r0, r1⟩ := (extractFieldOffsets_forkActivation_eq_meaningReads b o0 o1).mp hoffs
  have hcan : meaningRequireCanonicalOffsets b 8 [o0, o1] = .ok () := by
    cases hc : meaningRequireCanonicalOffsets b 8 [o0, o1] with
    | ok u => cases u; rfl
    | error e =>
        exfalso
        have hbad : ¬ (o0 = 8 ∧ o0 ≤ o1 ∧ o1 ≤ b.size) := by
          intro hgood
          have hok := (requireCanonicalOffsets_forkActivation b o0 o1).mpr
            ⟨by omega, hgood.1, hgood.2.1, hgood.2.2⟩
          rw [hc] at hok
          exact absurd hok (by simp)
        rw [decodeCanonical_forkActivation_rejects_noncanonical b o0 o1 hoffs hbad] at hacc
        exact absurd hacc (by simp)
  obtain ⟨-, hc0, hc01, hc1⟩ := (requireCanonicalOffsets_forkActivation b o0 o1).mp hcan
  obtain ⟨p0, p1⟩ := decodeCanonical_forkActivation_fields_of b o0 o1 hoffs hc0 hc01 hc1 hu32 hacc
  obtain ⟨x0, e0⟩ := except_isSome_iff.mp p0
  obtain ⟨x1, e1⟩ := except_isSome_iff.mp p1
  have hx : x = (x0, x1, PUnit.unit) := by
    have heq := decodeCanonical_forkActivation_eq_of_fields b o0 o1 hoffs hc0 hc01 hc1 hu32 e0 e1
    rw [hdc] at heq
    injection heq
  subst hx
  rw [meaningForkActivation, if_neg h8]
  simp only [r0, r1, except_bind_ok, hcan, except_bind_pure]
  rw [meaningOptionalU64_value e0, meaningOptionalU64_value e1]
  rfl

/-- **The `forkConfig` link, with the value.** The bound is a hypothesis rather than a case split:
this statement is only about the accepting branch, and there the source's `fork > 20` test does not
fire — `decodeCanonical_forkConfig_fork_eq` is what says the test is looking at the same number the
hypothesis bounds. -/
theorem meaningForkConfig_value_agrees {b : ByteArray} {x : BinaryFv.Specs.SSZ.forkConfigType.interp}
    (hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b = .ok x)
    (hfork : (BinaryFv.Specs.SSZ.rawForkConfigOf x).fork ≤ 20) :
    meaningForkConfig b = .ok (BinaryFv.Specs.SSZ.rawForkConfigOf x) := by
  have hu32 := forkConfig_size_lt_u32_of_ok hdc
  have hacc : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.forkConfigType b).toOption.isSome = true := by
    rw [hdc]; rfl
  have h16 : ¬ b.size < 16 := by
    intro hlt
    rw [decodeCanonical_forkConfig_short hlt] at hdc
    exact absurd hdc (by simp)
  obtain ⟨o0, o1, hoffs⟩ := forkConfig_offsets_of_sixteen b (by omega)
  obtain ⟨r0, r1⟩ := (extractFieldOffsets_forkConfig_eq_meaningReads b o0 o1).mp hoffs
  have hcan : meaningRequireCanonicalOffsets b 16 [o0, o1] = .ok () := by
    cases hc : meaningRequireCanonicalOffsets b 16 [o0, o1] with
    | ok u => cases u; rfl
    | error e =>
        exfalso
        have hbad : ¬ (o0 = 16 ∧ o0 ≤ o1 ∧ o1 ≤ b.size) := by
          intro hgood
          have hok := (requireCanonicalOffsets_forkConfig b o0 o1).mpr
            ⟨by omega, hgood.1, hgood.2.1, hgood.2.2⟩
          rw [hc] at hok
          exact absurd hok (by simp)
        rw [decodeCanonical_forkConfig_rejects_noncanonical b o0 o1 hoffs hbad] at hacc
        exact absurd hacc (by simp)
  obtain ⟨-, hc0, hc01, hc1⟩ := (requireCanonicalOffsets_forkConfig b o0 o1).mp hcan
  obtain ⟨fork, hfx⟩ := meaningReadU64_exists b 0 (by omega)
  have ha0 : readUInt64LE b 0 = some fork := meaningReadU64_eq_some hfx
  have hforkeq : x.1 = fork :=
    decodeCanonical_forkConfig_fork_eq b o0 o1 hoffs hc0 hc01 hc1 ha0 hdc
  have hnf : ¬ (fork.toNat > 20) := by
    have hle : x.1 ≤ 20 := hfork
    rw [hforkeq] at hle
    have := (fork_bound_toNat_iff fork).mpr hle
    omega
  obtain ⟨p0, p1⟩ := decodeCanonical_forkConfig_fields_of b o0 o1 hoffs hc0 hc01 hc1 hu32 ha0 hacc
  obtain ⟨y0, e0⟩ := except_isSome_iff.mp p0
  obtain ⟨y1, e1⟩ := except_isSome_iff.mp p1
  have hx : x = (fork, y0, y1, PUnit.unit) := by
    have heq := decodeCanonical_forkConfig_eq_of_fields b o0 o1 hoffs hc0 hc01 hc1 hu32 ha0 e0 e1
    rw [hdc] at heq
    injection heq
  subst hx
  rw [meaningForkConfig, if_neg h16]
  simp only [r0, r1, except_bind_ok, hcan, except_bind_pure, hfx, if_neg hnf]
  rw [meaningForkActivation_value_agrees e0, meaningOptionalBlobSchedule_value e1]
  rfl

/-- **The `chainConfig` link, with the value — third of three, and the one the entry consumes.**

The parent's bound and the child's are the same projection definitionally (`rawChainConfigOf` sets
`activeFork := rawForkConfigOf value.2.1`), so the hypothesis passes straight down to
`meaningForkConfig_value_agrees` with no step. -/
theorem meaningChainConfig_value_agrees {b : ByteArray} {x : BinaryFv.Specs.SSZ.chainConfigType.interp}
    (hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b = .ok x)
    (hfork : (BinaryFv.Specs.SSZ.rawChainConfigOf x).activeFork.fork ≤ 20) :
    meaningChainConfig b = .ok (BinaryFv.Specs.SSZ.rawChainConfigOf x) := by
  have hu32 := chainConfig_size_lt_u32_of_ok hdc
  have hacc : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b).toOption.isSome = true := by
    rw [hdc]; rfl
  have h12 : ¬ b.size < 12 := by
    intro hlt
    rw [decodeCanonical_chainConfig_short hlt] at hdc
    exact absurd hdc (by simp)
  obtain ⟨o, hoffs⟩ := chainConfig_offsets_of_twelve b (by omega)
  have r0 := (extractFieldOffsets_chainConfig_eq_meaningReads b o).mp hoffs
  have hcan : meaningRequireCanonicalOffsets b 12 [o] = .ok () := by
    cases hc : meaningRequireCanonicalOffsets b 12 [o] with
    | ok u => cases u; rfl
    | error e =>
        exfalso
        have hbad : ¬ (o = 12 ∧ o ≤ b.size) := by
          intro hgood
          have hok := (requireCanonicalOffsets_chainConfig b o).mpr ⟨by omega, hgood.1, hgood.2⟩
          rw [hc] at hok
          exact absurd hok (by simp)
        rw [decodeCanonical_chainConfig_rejects_noncanonical b o hoffs hbad] at hacc
        exact absurd hacc (by simp)
  obtain ⟨-, hc0, hc1⟩ := (requireCanonicalOffsets_chainConfig b o).mp hcan
  obtain ⟨chainId, hcx⟩ := meaningReadU64_exists b 0 (by omega)
  have ha0 : readUInt64LE b 0 = some chainId := meaningReadU64_eq_some hcx
  have p := decodeCanonical_chainConfig_fields_of b o hoffs hc0 hc1 hu32 ha0 hacc
  obtain ⟨y, e⟩ := except_isSome_iff.mp p
  have hx : x = (chainId, y, PUnit.unit) := by
    have heq := decodeCanonical_chainConfig_eq_of_fields b o hoffs hc0 hc1 hu32 ha0 e
    rw [hdc] at heq
    injection heq
  subst hx
  have hforky : (BinaryFv.Specs.SSZ.rawForkConfigOf y).fork ≤ 20 := hfork
  rw [meaningChainConfig, if_neg h12]
  simp only [r0, except_bind_ok, hcan, except_bind_pure, hcx]
  rw [meaningForkConfig_value_agrees e hforky]
  rfl

/-- The entry's chain-side hypothesis, discharged. -/
theorem chainConfigValue_holds : ChainConfigValueHypothesis :=
  fun _ _ hdc hfork => meaningChainConfig_value_agrees hdc hfork

/-! ## The obligation, joined

`EntryOffsets` proves the two halves separately — acceptance in one direction, value in the other —
and this is the two-line join. The `mp` direction is where the split pays off: a source success
implies *some* oracle success by the acceptance half, and the value half then names it, so
injectivity of `.ok` identifies the two. Neither half is a special case of the other, which is why
the obligation is a biconditional rather than an implication. -/

/-- **`sourceShapedDecodeAgreesWithOracle`, at value granularity.**

Its two explicit premises are unchanged from when this was the acceptance-only statement: the chain's
value agreement is *not* a third premise, because it is proved outright above. Stated here rather
than in `EntryOffsets` for exactly that reason — that module cannot see `meaningChainConfig`'s value
agreement, since the chain imports it. -/
theorem sourceShapedDecodeAgreesWithOracle_holds
    (containersAgree : sourceShapedContainersAgreeWithOracle)
    (retryTail : retryTailNeverSchemaValid) :
    sourceShapedDecodeAgreesWithOracle := by
  intro bytes h value
  constructor
  · intro hm
    have hacc : isAccepted (meaningDecode bytes) = true := by rw [hm]; rfl
    rw [meaningDecode_acceptance_agrees containersAgree retryTail bytes h] at hacc
    obtain ⟨w, hw⟩ := except_isSome_iff.mp hacc
    have hmw := meaningDecode_value_agrees containersAgree chainConfigValue_holds h hw
    rw [hm] at hmw
    have hvw : value = w := by injection hmw
    subst hvw
    exact hw
  · exact meaningDecode_value_agrees containersAgree chainConfigValue_holds h

end BinaryFv.Zesu.MemoryRepresentation
