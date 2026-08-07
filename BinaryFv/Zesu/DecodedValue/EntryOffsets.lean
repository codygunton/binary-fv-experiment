import BinaryFv.Zesu.Contracts.Entry
import BinaryFv.Zesu.Contracts.SemanticObligations

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
whole point — a hand-rolled four-offset reader would prove nothing about what the spec does.

## Mechanical notes for this project

Collected because each cost a round trip to rediscover, and five is past the point where the next
session should pay for them again. This project has no Mathlib, and the pinned spec's recursion is
well-founded, which together account for most of the list.

* **No `ring`.** For `n = accSz + (k+1) * sz` shapes, `rw [Nat.succ_mul]` then `omega`.
* **No `by_contra`.** `split` on the `dite` reaches the same contradiction.
* **`ByteArray` push-indexing lemmas do not exist under the guessable names** — not
  `getElem_push_lt`, `getElem_push_eq`, nor `getElem_eq_data_getElem`. Exposing the buffer as an
  explicit literal (`uint32LE_eq_literal`, `rfl`) sidesteps the whole question.
* **`rw` on a schema abbreviation can fail where `simp only` unfolds it** — `rw [publicKeysType]`
  reports "failed to rewrite using equation theorems"; `simp only [publicKeysType]` works. Likewise
  `rw [statelessInputV4Type_eq]` fails with "motive is not type correct" because rewriting the
  schema changes a bound value's type; `show` on the defeq container form has no motive to break.
* **`decide` cannot evaluate `deserialize`** — it is well-founded, so the kernel gets no unfolding.
  But `rw [SSZType.deserialize]` *does* unfold it through the generated equation lemmas. Those are
  different claims, and reading the first as "`deserialize` is opaque" rules out proofs that work.
* **Two syntactically identical `match` terms can fail `rfl`** when they carry different motives.
  `cases` on the scrutinee reduces both sides; `split` reduces only the left, which looks like
  progress and is not.
* **When a tactic cannot find a pattern that is visibly present, ask whether the terms are *spelled*
  alike, not whether they are equal.** Defeq is not syntactic equality and most tactics want the
  latter. Four failures in one proof, all this cause: a hypothesis stated at `publicKeysType` against
  a goal showing the unfolded `.list (byteVector 65) maxPublicKeys`; `omega` reading
  `(x0, x1, x2, x3, unit).fst` as an atom distinct from `x0`; `omega` reading `UInt32.size` as an
  atom rather than `4294967296`; and `match`es on `Except.ok` literals staying unreduced so the bound
  variable never became the tuple. The crossings are `simp only []` (beta/iota/projection), a
  restatement `have h' : <other spelling> := h` (defeq coercion), and `have : UInt32.size = 4294967296
  := rfl` to give `omega` the link. `rw` crosses none of them.
* **Match the diagnosis to the signal, not to your recent history with it.** The failure mode is
  *having a favourite explanation*: once a diagnosis has worked several times it starts getting
  applied to signals it does not fit. The defence is to ask what the signal specifically says.
  `omega` failing has at least three distinct causes here, and they are told apart by **what it
  printed**, not by which is most familiar:
  - *constraints listed, but the one you need is absent* — a hypothesis genuinely is not there. This
    caught a real gap in a case analysis: `raw_envelope_rejects_both` cased on the disjunction before
    the size, and in the `hasSchemaId` branch `2 ≤ bytes.size` does not hold, because a buffer can
    fail both tests. Reordering the split is the fix.
  - *constraints listed, and the one you need looks present* — the terms are spelled differently, the
    defeq family below. `simp only []` or a restatement crosses it.
  - *"No usable constraints found" with an empty atom list* — the goal is not `Nat`/`Int` arithmetic
    at all. `fork : UInt64` in `raw_acceptance_agrees`; the fix is `UInt64.not_le`, not a rewrite.

  The first two produce the same *words* and want opposite fixes, which is exactly why reading the
  atom list rather than pattern-matching the message is the discipline.
* **Anything reading through the LSP inherits its staleness, so `lake` is authoritative.** Two
  symptoms of one root cause, worth stating together because they look unrelated:
  - a *stale unknown identifier* for a declaration added to an imported module in the same session;
  - a *spurious `sorryAx`* from `lean_verify`, which reads through the LSP — a stale view of a
    partially elaborated file reports the one axiom that would mean unsoundness.

  Both are transient and both disappear on a rebuild; neither is a permanent property of the tool.
  The rule is therefore not "distrust `lean_verify`" but **`lake` decides any axiom claim** —
  `#print axioms` under `lake build`, or a scratch file under `lake env lean`. That also applies to
  the planned systematic axiom sweep: run it through `lake`, or it is a sweep with an unknown
  false-negative rate.
-/

namespace BinaryFv.Zesu.DecodedValue

open SizzLean.Spec
open BinaryFv.Zesu.Contracts

/-! ## The schema is four variable-size fields

Every step below depends on all four entry fields being variable-size: that is what makes the fixed
section exactly four `uint32` offsets, and what makes `extractFieldOffsets` emit one entry per field
rather than skipping some. Established by evaluation on the concrete schema rather than assumed. -/

/-- The entry schema's field list, named so the lemmas below can talk about it. -/
def entryFields : List SSZType :=
  [BinaryFv.Specs.SSZ.newPayloadRequestType, BinaryFv.Specs.SSZ.witnessType, BinaryFv.Specs.SSZ.chainConfigType,
    .list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes) BinaryFv.Specs.SSZ.maxPublicKeys]

theorem statelessInputV4Type_eq : BinaryFv.Specs.SSZ.statelessInputV4Type = .container entryFields := rfl

/-- None of the four entry fields is fixed-size. Stated one field at a time as well as over the
list, because the offset-table reduction rewrites under `extractFieldOffsets`'s `if` and needs each
guard as its own rewrite. -/
theorem entryFields_none_fixed : ∀ t ∈ entryFields, t.isFixedSize = false := by
  decide

@[simp] theorem newPayloadRequestType_not_fixed :
    BinaryFv.Specs.SSZ.newPayloadRequestType.isFixedSize = false := by decide

@[simp] theorem witnessType_not_fixed : BinaryFv.Specs.SSZ.witnessType.isFixedSize = false := by decide

@[simp] theorem chainConfigType_not_fixed :
    BinaryFv.Specs.SSZ.chainConfigType.isFixedSize = false := by decide

@[simp] theorem publicKeysField_not_fixed :
    (SSZType.list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes)
      BinaryFv.Specs.SSZ.maxPublicKeys).isFixedSize = false := by decide

/-- The entry container is not all-fixed, so `deserialize` takes its variable-size branch. -/
theorem entryFields_not_allFixed : SSZType.allFixedSize entryFields = false := by
  decide

/-- The fixed section is exactly the four offsets. -/
theorem entryFields_fixedSectionSize : SSZType.fixedSectionSizeFields entryFields = 16 := by
  decide

/-! ## The two tables coincide -/

/-- **The spec's offset table is the source's four reads.**

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

/-- **The spec's table and the source's four `readOffset` calls agree.**

Note the error taxonomies do *not* agree — a short buffer is `.tooShort` on the spec side and
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

/-! ## The source's offset check at the entry table -/

/-- `requireCanonicalOffsets` at the entry's four-offset table, unfolded to arithmetic.

A specialization of `canonicalOffsetsCharacterization_holds` to the concrete call in
`meaningDecodeRaw`. `o0 = 16` is an *equality*, not a bound: a table whose first entry merely
exceeds the fixed section is rejected, which is what forbids padding between the fixed section and
the first variable field.

The `≤ body.size` clauses for `o0`, `o1` and `o2` are absorbed: they follow from monotonicity and
`o3 ≤ body.size`, so the six conjuncts below are the whole content of the check. -/
theorem requireCanonicalOffsets_entry (body : ByteArray) (o0 o1 o2 o3 : Nat) :
    meaningRequireCanonicalOffsets body 16 [o0, o1, o2, o3] = .ok () ↔
      (16 ≤ body.size ∧ o0 = 16 ∧ o0 ≤ o1 ∧ o1 ≤ o2 ∧ o2 ≤ o3 ∧ o3 ≤ body.size) := by
  rw [canonicalOffsetsCharacterization_holds body 16 [o0, o1, o2, o3]]
  simp only [Nondecreasing, List.mem_cons, List.not_mem_nil, List.headD_cons,
    ne_eq, reduceCtorEq, not_false_eq_true, true_and]
  constructor
  · rintro ⟨hfix, hhead, ⟨h01, h12, h23, -⟩, hall⟩
    exact ⟨hfix, hhead, h01, h12, h23, hall o3 (by simp)⟩
  · rintro ⟨hfix, hhead, h01, h12, h23, h3⟩
    refine ⟨hfix, hhead, ⟨h01, h12, h23, trivial⟩, ?_⟩
    intro offset hmem
    simp only [or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;> omega

/-! ## The spec's field slices

`deserializeVarFields` walks the field list carrying the offset table, and for each variable field
takes the slice from its own offset to the *next* one — with `bufEnd` standing in as the sentinel
after the last field. Under the guards `requireCanonicalOffsets_entry` supplies, those slices are
exactly the four `body.extract` calls `meaningDecodeRaw` makes.

The `prefixOff` argument is threaded but never reaches the result on an all-variable field list: it
only advances the fixed-section cursor, which has no fixed fields to read. -/

/-- **The spec slices the entry body exactly where the source does.**

Stated as the full nested match rather than at acceptance granularity, because the composition
theorem needs the decoded *values*, not just whether the decode succeeded — and because the nesting
is what preserves first-error-wins ordering, which a flat match would silently discard. -/
theorem deserializeVarFields_entry (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (h01 : o0 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size) :
    SSZType.deserializeVarFields entryFields body 0 [o0, o1, o2, o3] body.size =
      match SSZType.deserialize BinaryFv.Specs.SSZ.newPayloadRequestType (body.extract o0 o1) with
      | .error e => .error e
      | .ok (x0, _) =>
        match SSZType.deserialize BinaryFv.Specs.SSZ.witnessType (body.extract o1 o2) with
        | .error e => .error e
        | .ok (x1, _) =>
          match SSZType.deserialize BinaryFv.Specs.SSZ.chainConfigType (body.extract o2 o3) with
          | .error e => .error e
          | .ok (x2, _) =>
            match SSZType.deserialize
                (.list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes) BinaryFv.Specs.SSZ.maxPublicKeys)
                (body.extract o3 body.size) with
            | .error e => .error e
            | .ok (x3, _) => .ok (x0, x1, x2, x3, PUnit.unit) := by
  have n01 : ¬ (o0 > o1) := by omega
  have n12 : ¬ (o1 > o2) := by omega
  have n23 : ¬ (o2 > o3) := by omega
  have n1 : ¬ (o1 > body.size) := by omega
  have n2 : ¬ (o2 > body.size) := by omega
  have n3 : ¬ (o3 > body.size) := by omega
  have nend : ¬ (body.size > body.size) := by omega
  simp only [entryFields, SSZType.deserializeVarFields, newPayloadRequestType_not_fixed,
    witnessType_not_fixed, chainConfigType_not_fixed, publicKeysField_not_fixed,
    List.head?_cons, List.head?_nil, Option.getD_some, Option.getD_none,
    n01, n12, n23, n1, n2, n3, nend, decide_false, Bool.or_false,
    if_false, Bool.false_eq_true]
  cases SSZType.deserialize BinaryFv.Specs.SSZ.newPayloadRequestType (body.extract o0 o1) <;>
    cases SSZType.deserialize BinaryFv.Specs.SSZ.witnessType (body.extract o1 o2) <;>
      cases SSZType.deserialize BinaryFv.Specs.SSZ.chainConfigType (body.extract o2 o3) <;>
        cases SSZType.deserialize
            (.list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes) BinaryFv.Specs.SSZ.maxPublicKeys)
            (body.extract o3 body.size) <;> rfl

/-! ## The per-field `used` check is redundant

**What breaks if this does not hold.** The source decodes each entry field with `decodeCanonical`,
which checks `used = slice.size`. The spec does *not*: the top-level check is vacuous at the entry
container — the variable-container arm returns `(v, b.size)`, so `used = body.size` unconditionally
— and `deserializeVarFields` discards each field's `used` (`Deserialize.lean:513` matches
`.ok (x, _)`). So the re-serialization equality is the only thing constraining the fields. If the
per-field `used` check were *not* redundant, the source side would be strictly stronger than the
spec, there would be a body the spec accepts and the source rejects, and
`sourceShapedDecodeAgreesWithSpec` would be **false**. This is a fourth statement defect avoided,
not a convenience lemma.

**It is not the general fact it looks like.** `used = (serialize value).size` for arbitrary shapes is
a size-consistency theorem that is neither free nor upstream — `SizzLean.Proofs.SerializeSize`
covers only `isFixedSize` shapes and `Roundtrip.decode_encode` runs the other way. What holds, and
all that is needed, is a per-field-type fact about the four shapes the entry schema actually uses. -/

/-- A field list with at least one variable-size field yields at least one offset.

Needed to rule out `deserialize`'s degenerate `offs.head? = none` arm, which falls back to
`deserializeFixedFields` and would return a `used` smaller than `b.size`. Upstream's own comment
calls that arm unreachable when `allFixedSize` is false; that is support, not proof. -/
theorem extractFieldOffsets_ne_nil (b : ByteArray) :
    ∀ (fs : List SSZType) (off : Nat) (offs : List Nat),
      SSZType.allFixedSize fs = false → extractFieldOffsets b fs off = .ok offs → offs ≠ [] := by
  intro fs
  induction fs with
  | nil => intro _ _ hvar; exact absurd hvar (by simp [SSZType.allFixedSize])
  | cons t ts ih =>
      intro off offs hvar hext
      by_cases hfix : t.isFixedSize
      · rw [SSZType.allFixedSize, hfix] at hvar
        simp only [Bool.true_and] at hvar
        rw [extractFieldOffsets, if_pos hfix] at hext
        exact ih _ _ hvar hext
      · rw [extractFieldOffsets, if_neg hfix] at hext
        split at hext
        · exact absurd hext (by simp)
        · split at hext
          · simp only [Except.ok.injEq] at hext; subst hext; simp
          · exact absurd hext (by simp)

/-- **A variable-size container reports consuming its whole buffer.**

So `decodeCanonical`'s `used = body.size` check is redundant at every variable container — which is
what makes the source's per-field `decodeCanonical` no stronger than what the spec does per field.
See the section docstring for what would break otherwise. -/
theorem deserialize_container_used (fs : List SSZType) (b : ByteArray)
    (hvar : SSZType.allFixedSize fs = false)
    (v : SSZType.interpFields fs) (u : Nat)
    (h : SSZType.deserialize (.container fs) b = .ok (v, u)) : u = b.size := by
  rw [SSZType.deserialize, if_neg (by simp [hvar])] at h
  -- Zeta-reduce the `have prefixSize := …` binding so `split` can reach the size guard first.
  simp only [] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i offs hext
      -- The degenerate `offs.head? = none` arm is unreachable: some field is variable.
      have hne := extractFieldOffsets_ne_nil b fs 0 offs hvar hext
      cases offs with
      | nil => exact absurd rfl hne
      | cons first rest =>
          simp only [List.head?_cons] at h
          split at h
          · simp at h
          · split at h
            · simp at h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              exact h.2.symm

/-- **`allFixedSize fs = false` is load-bearing above, not decoration.**

An *all-fixed* container reports only its fixed width, which does not depend on the buffer length at
all — so on any longer buffer `used < b.size` and the lemma above would be false without its
hypothesis. Kept rather than argued in a comment: this is what makes the variable-size restriction a
real precondition instead of an incidental one, and it is a passing check, so it can live here as a
regression guard.

`decide` cannot settle this by evaluation — `deserialize` is well-founded, so the kernel gets no
unfolding from it — which is why it is proved by the same unfolding route as the lemma above. -/
theorem deserialize_allFixed_container_used (t : SSZType) (b : ByteArray)
    (hfix : SSZType.allFixedSize [t] = true)
    (x : SSZType.interpFields [t]) (u : Nat)
    (h : SSZType.deserialize (.container [t]) b = .ok (x, u)) : u = t.fixedByteSize := by
  rw [SSZType.deserialize, if_pos hfix, SSZType.deserializeFixedFields] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rw [SSZType.deserializeFixedFields] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hu⟩ := h
      omega

/-! ## The re-serialization side

`decodeCanonical`'s canonicality test is `schema.serialize value == body`. For the entry container
that expands through `serializeFieldsAux`, which emits one `uint32LE` offset per variable field into
the fixed prefix — each offset being the *running* total of the preceding field bodies — and
concatenates the bodies after it.

This is ingredient (ii) of the decomposition: once the four per-field serialize equalities hold, the
offset table is forced, because each offset is by construction the cumulative sum of the earlier
body lengths. So (ii) is a consequence of (i) rather than a further obligation, which is what keeps
the decomposition non-circular. -/

/-- **The entry container's serialization, expanded.**

The field serializations are named through hypotheses rather than inlined so the offset arithmetic
stays legible: each offset is `16 + ` the sizes of the *preceding* bodies. -/
theorem serialize_entry (v : SSZType.interpFields entryFields)
    (s0 s1 s2 s3 : ByteArray)
    (e0 : SSZType.serialize BinaryFv.Specs.SSZ.newPayloadRequestType v.1 = s0)
    (e1 : SSZType.serialize BinaryFv.Specs.SSZ.witnessType v.2.1 = s1)
    (e2 : SSZType.serialize BinaryFv.Specs.SSZ.chainConfigType v.2.2.1 = s2)
    (e3 : SSZType.serialize (SSZType.list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes)
            BinaryFv.Specs.SSZ.maxPublicKeys) v.2.2.2.1 = s3) :
    SSZType.serialize (.container entryFields) v =
      (uint32LE (Nat.toUInt32 16)
        ++ (uint32LE (Nat.toUInt32 (16 + s0.size))
        ++ (uint32LE (Nat.toUInt32 (16 + s0.size + s1.size))
        ++ uint32LE (Nat.toUInt32 (16 + s0.size + s1.size + s2.size)))))
      ++ (s0 ++ (s1 ++ (s2 ++ s3))) := by
  rw [SSZType.serialize]
  simp only [entryFields, SSZType.serializeFieldsAux, newPayloadRequestType_not_fixed,
    witnessType_not_fixed, chainConfigType_not_fixed, publicKeysField_not_fixed,
    Bool.false_eq_true, if_false, e0, e1, e2, e3, ByteArray.append_empty,
    SSZType.fixedSectionSizeFields, SSZType.fixedSectionSize, BYTES_PER_LENGTH_OFFSET]

/-! ## Splitting a concatenation

The canonicality join needs to turn `fix ++ var = body` into its two halves. Core supplies the
*assembly* direction — `extract_append_extract` and `extract_zero_size` put a buffer back together
from its pieces — and cancellation when one side is syntactically shared (`append_left_inj`,
`append_right_inj`). It does **not** supply the split: recovering the left half of a concatenation as
an `extract`, or cancelling when the two left parts merely have equal size.

That corrects an earlier assessment. Checking that `append_assoc`, `size_append`
and `append_empty` exist established that the *arithmetic* needed nothing new; it did not establish
that the *split* did, and those are different questions. The two lemmas below fill the gap and are
the only ByteArray theory this item adds. -/

/-- The left half of a concatenation, recovered as an `extract`. -/
theorem extract_append_left (a b : ByteArray) : (a ++ b).extract 0 a.size = a := by
  refine ext_of_get! ?_ ?_
  · rw [ByteArray.size_extract, ByteArray.size_append]; omega
  · intro index bound
    rw [ByteArray.size_extract, ByteArray.size_append] at bound
    have hleft : index < a.size := by omega
    have hext : index < ((a ++ b).extract 0 a.size).size := by
      rw [ByteArray.size_extract, ByteArray.size_append]; omega
    rw [get!_eq_getElem _ index hext, get!_eq_getElem a index hleft,
      ByteArray.getElem_extract hext]
    simp only [Nat.zero_add]
    exact ByteArray.getElem_append_left hleft

/-- **Same-size left cancellation.** From `a ++ b = a' ++ b'` with `a.size = a'.size`, both halves
agree. This is the form the canonicality join consumes: the offset table and the body region are
compared against a buffer whose split point is known only by *width*, never syntactically. -/
theorem append_inj_of_size_eq {a b a' b' : ByteArray} (hsize : a.size = a'.size)
    (h : a ++ b = a' ++ b') : a = a' ∧ b = b' := by
  have hleft : a = a' := by
    have := extract_append_left a b
    rw [h, hsize, extract_append_left a' b'] at this
    exact this.symm
  refine ⟨hleft, ?_⟩
  subst hleft
  exact (ByteArray.append_right_inj a).mp h

/-- **`hsize` is load-bearing above, not decoration.** Without it a concatenation splits two ways:
`[1] ++ [2]` and `[1,2] ++ []` are the same buffer with different halves. Kept, since it passes — and
unlike the `deserialize` preconditions this one *can* be settled by evaluation, because `++` is
computable and `ByteArray` has `DecidableEq`. -/
theorem append_inj_needs_size :
    ((⟨#[1]⟩ : ByteArray) ++ ⟨#[2]⟩ = (⟨#[1, 2]⟩ : ByteArray) ++ ⟨#[]⟩) ∧
      (⟨#[1]⟩ : ByteArray) ≠ (⟨#[1, 2]⟩ : ByteArray) := by decide

/-! ### The two splits the join performs

`serialize_entry` produces a sixteen-byte offset table followed by the four bodies, so the join
splits `body` twice: once at width 16 into table and body region, and once inside the table into four
four-byte offsets. Both are stated in the right-nested form `serialize_entry` actually produces, so
no re-association is needed at the use site. -/

/-- Split a buffer at any width within it. -/
theorem extract_split (body : ByteArray) (n : Nat) (h : n ≤ body.size) :
    body.extract 0 n ++ body.extract n body.size = body := by
  rw [ByteArray.extract_append_extract, show min 0 n = 0 by omega,
    show max n body.size = body.size by omega, ByteArray.extract_zero_size]

/-- The offset table's sixteen bytes as four four-byte fields.

No size hypothesis: `extract` clamps out of range, so this holds on short buffers too — where both
sides are simply shorter than sixteen bytes. -/
theorem extract_sixteen (body : ByteArray) :
    body.extract 0 4 ++ (body.extract 4 8 ++ (body.extract 8 12 ++ body.extract 12 16))
      = body.extract 0 16 := by
  rw [ByteArray.extract_append_extract, show min 8 12 = 8 from rfl, show max 12 16 = 16 from rfl,
    ByteArray.extract_append_extract, show min 4 8 = 4 from rfl, show max 8 16 = 16 from rfl,
    ByteArray.extract_append_extract, show min 0 4 = 0 from rfl, show max 4 16 = 16 from rfl]

/-- `extract_sixteen`'s missing size hypothesis is a real claim, not an oversight — checked on a
five-byte buffer, where every field past the first is clamped or empty and both sides come out as the
whole buffer. Concrete counterexample-style check, available here because `extract` is computable. -/
theorem extract_sixteen_short_buffer :
    (⟨#[1, 2, 3, 4, 5]⟩ : ByteArray).extract 0 4
        ++ ((⟨#[1, 2, 3, 4, 5]⟩ : ByteArray).extract 4 8
        ++ ((⟨#[1, 2, 3, 4, 5]⟩ : ByteArray).extract 8 12
        ++ (⟨#[1, 2, 3, 4, 5]⟩ : ByteArray).extract 12 16))
      = (⟨#[1, 2, 3, 4, 5]⟩ : ByteArray) := by decide

/-- **`extract_split`'s hypothesis is NOT load-bearing for truth**, only for the proof route above:
past the end, `extract 0 n` clamps to the whole buffer and `extract n size` is empty, so the equation
still holds. Recorded rather than left implicit, so a later reader does not think the lemma is
narrower than it is and go proving `n ≤ size` at a use site that does not need it. Kept at `n ≤ size`
because every call in the join has that bound anyway, and the clamped proof needs a case split that
buys nothing here. -/
theorem extract_split_beyond_end :
    (⟨#[1, 2]⟩ : ByteArray).extract 0 5 ++ (⟨#[1, 2]⟩ : ByteArray).extract 5 2
      = (⟨#[1, 2]⟩ : ByteArray) := by decide

/-! ### Matching a four-entry offset table field by field -/

/-- A four-entry table of four-byte fields matches the buffer's first sixteen bytes exactly when
each field matches its own four bytes.

`16 ≤ body.size` is load-bearing for the *proof* — it is what makes each of the four `extract`s four
bytes wide, and the cancellation needs those widths — but **not for the truth** of the statement, the
same situation as `extract_split`. On a shorter buffer both sides are simply false: the left side has
width 16 against a narrower `extract 0 16`, and the right side asks a four-byte field to equal a
clamped `extract` narrower than four bytes. See `append4_needs_no_size_for_truth`.

An earlier version of this docstring claimed the hypothesis *was* needed for truth, "unlike in
`extract_split`". That was asserted rather than checked, one lemma after adopting the rule that every
hypothesis must be shown to do work — which is the point of the rule. -/
theorem append4_eq_extract_sixteen_iff {a0 a1 a2 a3 : ByteArray} (body : ByteArray)
    (hbody : 16 ≤ body.size)
    (h0 : a0.size = 4) (h1 : a1.size = 4) (h2 : a2.size = 4) (h3 : a3.size = 4) :
    a0 ++ (a1 ++ (a2 ++ a3)) = body.extract 0 16 ↔
      (a0 = body.extract 0 4 ∧ a1 = body.extract 4 8 ∧ a2 = body.extract 8 12 ∧
        a3 = body.extract 12 16) := by
  have w0 : (body.extract 0 4).size = 4 := by rw [ByteArray.size_extract]; omega
  have w1 : (body.extract 4 8).size = 4 := by rw [ByteArray.size_extract]; omega
  have w2 : (body.extract 8 12).size = 4 := by rw [ByteArray.size_extract]; omega
  constructor
  · intro h
    rw [← extract_sixteen] at h
    obtain ⟨p0, h'⟩ := append_inj_of_size_eq (by rw [h0, w0]) h
    obtain ⟨p1, h''⟩ := append_inj_of_size_eq (by rw [h1, w1]) h'
    obtain ⟨p2, p3⟩ := append_inj_of_size_eq (by rw [h2, w2]) h''
    exact ⟨p0, p1, p2, p3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact extract_sixteen body

/-- `append4_eq_extract_sixteen_iff`'s size hypothesis is needed for its proof, not for its truth.

On an eight-byte buffer with four four-byte fields, *both* sides of the equivalence are false — the
left has width 16 against an eight-byte `extract 0 16`, and the right asks a four-byte field to equal
the empty `extract 8 12` — so the equivalence itself still holds. Concrete counterexample-style, since
`extract` and `++` are computable. -/
theorem append4_needs_no_size_for_truth :
    ¬ ((⟨#[0, 0, 0, 0]⟩ : ByteArray) ++ (⟨#[0, 0, 0, 0]⟩ ++ (⟨#[0, 0, 0, 0]⟩ ++ ⟨#[0, 0, 0, 0]⟩))
        = (⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray).extract 0 16) ∧
      ¬ ((⟨#[0, 0, 0, 0]⟩ : ByteArray)
        = (⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray).extract 8 12) := by decide

/-! ## The join

`decodeCanonical`'s canonicality test, decomposed. This is where the pieces meet: `serialize_entry`
expands the left side, `extract_split` cuts the buffer at the table width, and
`append4_eq_extract_sixteen_iff` takes the table apart field by field.

What comes out is five conditions — four offset-bytes equalities and one body-region equality — and
that shape is the point. The body-region condition is where the per-field canonicality lives, and the
four offset conditions are forced by it, because each offset is the cumulative sum of the preceding
body widths. So the decomposition is (i)-implies-(ii), not two independent obligations. -/

/-- **The entry canonicality test, decomposed into four offset bytes plus the body region.** -/
theorem serialize_entry_eq_body_iff (body : ByteArray) (v : SSZType.interpFields entryFields)
    (s0 s1 s2 s3 : ByteArray)
    (e0 : SSZType.serialize BinaryFv.Specs.SSZ.newPayloadRequestType v.1 = s0)
    (e1 : SSZType.serialize BinaryFv.Specs.SSZ.witnessType v.2.1 = s1)
    (e2 : SSZType.serialize BinaryFv.Specs.SSZ.chainConfigType v.2.2.1 = s2)
    (e3 : SSZType.serialize (SSZType.list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes)
            BinaryFv.Specs.SSZ.maxPublicKeys) v.2.2.2.1 = s3)
    (hbody : 16 ≤ body.size) :
    SSZType.serialize (.container entryFields) v = body ↔
      (uint32LE (Nat.toUInt32 16) = body.extract 0 4 ∧
        uint32LE (Nat.toUInt32 (16 + s0.size)) = body.extract 4 8 ∧
        uint32LE (Nat.toUInt32 (16 + s0.size + s1.size)) = body.extract 8 12 ∧
        uint32LE (Nat.toUInt32 (16 + s0.size + s1.size + s2.size)) = body.extract 12 16 ∧
        s0 ++ (s1 ++ (s2 ++ s3)) = body.extract 16 body.size) := by
  rw [serialize_entry v s0 s1 s2 s3 e0 e1 e2 e3]
  have htab : (uint32LE (Nat.toUInt32 16)
      ++ (uint32LE (Nat.toUInt32 (16 + s0.size))
      ++ (uint32LE (Nat.toUInt32 (16 + s0.size + s1.size))
      ++ uint32LE (Nat.toUInt32 (16 + s0.size + s1.size + s2.size))))).size
        = (body.extract 0 16).size := by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
      uint32LE_size, uint32LE_size, uint32LE_size, uint32LE_size, ByteArray.size_extract]
    omega
  constructor
  · intro h
    obtain ⟨htable, hvar⟩ :=
      append_inj_of_size_eq htab (h.trans (extract_split body 16 hbody).symm)
    obtain ⟨p0, p1, p2, p3⟩ :=
      (append4_eq_extract_sixteen_iff body hbody (uint32LE_size _) (uint32LE_size _)
        (uint32LE_size _) (uint32LE_size _)).mp htable
    exact ⟨p0, p1, p2, p3, hvar⟩
  · rintro ⟨p0, p1, p2, p3, hvar⟩
    rw [(append4_eq_extract_sixteen_iff body hbody (uint32LE_size _) (uint32LE_size _)
      (uint32LE_size _) (uint32LE_size _)).mpr ⟨p0, p1, p2, p3⟩, hvar]
    exact extract_split body 16 hbody

/-! ### Load-bearing audit of the join

Run mechanically rather than on suspicion, which is the only way it fires when it is needed.

**`e0`–`e3` are load-bearing for truth.** They are what tie `s0`–`s3` to the actual field
serializations; with `s0` unconstrained the right side compares the buffer against arbitrary widths
and the equivalence fails outright.

**`hbody` is load-bearing for the proof only — the third such hypothesis in this module.** Below
`16 ≤ body.size` both sides are false, so the equivalence survives. The two halves of that are
recorded as theorems rather than asserted:

* the right side fails on *width* — `uint32LE` is always four bytes and `body.extract 12 16` is
  narrower than four on a short buffer, so the fourth conjunct cannot hold;
* the left side fails on *size* — the entry serialization is at least sixteen bytes wide, being a
  sixteen-byte table plus four bodies, so it cannot equal a shorter buffer.

It is kept because every call site has the bound and dropping it would buy a case analysis for
nothing. -/

/-- The entry serialization always has room for its own offset table. -/
theorem serialize_entry_size_ge_sixteen (v : SSZType.interpFields entryFields)
    (s0 s1 s2 s3 : ByteArray)
    (e0 : SSZType.serialize BinaryFv.Specs.SSZ.newPayloadRequestType v.1 = s0)
    (e1 : SSZType.serialize BinaryFv.Specs.SSZ.witnessType v.2.1 = s1)
    (e2 : SSZType.serialize BinaryFv.Specs.SSZ.chainConfigType v.2.2.1 = s2)
    (e3 : SSZType.serialize (SSZType.list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes)
            BinaryFv.Specs.SSZ.maxPublicKeys) v.2.2.2.1 = s3) :
    16 ≤ (SSZType.serialize (.container entryFields) v).size := by
  rw [serialize_entry v s0 s1 s2 s3 e0 e1 e2 e3, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
    uint32LE_size, uint32LE_size, uint32LE_size, uint32LE_size]
  omega

/-- The other half: on a short buffer the fourth offset conjunct fails on width alone, since
`uint32LE` is four bytes and the final table slot is not. Concrete counterexample-style, at an
eight-byte buffer. -/
theorem entry_join_fourth_conjunct_fails_short :
    ((⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray).extract 12 16).size ≠ (uint32LE 0).size := by decide

/-! ## Wiring to the source's field meanings

Three of `meaningDecodeRaw`'s four field decodes are `decodeCanonical` at their pinned schema
followed by a projection, so they agree with the spec **by construction** rather than by theorem:
the projection is applied only on the `.ok` arm and cannot turn acceptance into rejection or back.
The three lemmas below say exactly that and nothing more.

The fourth field decode is `meaningChainConfig`, which is *source-shaped* — its `fork > 20` check
sits between the offset-table check and the child decodes, so it is not `decodeCanonical` at any
schema. That is `sourceShapedContainersAgreeWithSpec`, a separate component of item 6, and nothing
in this module touches it.

Load-bearing audit: these four have no hypotheses, so there is nothing to audit. Recorded because the
audit is now mechanical, and "no hypotheses" is a result of running it rather than a reason to skip. -/

/-- The entry schema's fourth field is exactly the collection `meaningPublicKeys` decodes. -/
theorem publicKeysType_eq_entry_field :
    publicKeysType
      = .list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes) BinaryFv.Specs.SSZ.maxPublicKeys := rfl

theorem meaningNewPayloadRequest_accepted (b : ByteArray) :
    isAccepted (meaningNewPayloadRequest b)
      = (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.newPayloadRequestType b).toOption.isSome := by
  cases h : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.newPayloadRequestType b <;>
    simp [meaningNewPayloadRequest, isAccepted, Except.toOption, h]

theorem meaningExecutionWitness_accepted (b : ByteArray) :
    isAccepted (meaningExecutionWitness b)
      = (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.witnessType b).toOption.isSome := by
  cases h : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.witnessType b <;>
    simp [meaningExecutionWitness, isAccepted, Except.toOption, h]

theorem meaningPublicKeys_accepted (b : ByteArray) :
    isAccepted (meaningPublicKeys b)
      = (BinaryFv.Specs.SSZ.decodeCanonical publicKeysType b).toOption.isSome := by
  cases h : BinaryFv.Specs.SSZ.decodeCanonical publicKeysType b <;>
    simp [meaningPublicKeys, isAccepted, Except.toOption, h]

/-! ## From offset bytes to offset values

The join leaves four conditions of the form `uint32LE (Nat.toUInt32 cumulativeSum) = body.extract
(4 * i) (4 * i + 4)` — a claim about *bytes*. The offsets the source reads are *values*. Turning one
into the other is the last step before the entry theorem, and it goes through
`uint32LE_of_readUInt32LE`, which is stated at offset 0 on a four-byte buffer. So the read has to move
from position `i` in the body to position 0 in the slice there first. -/

/-- Reading a `uint32` at `i` is reading it at 0 in the four-byte slice starting at `i`.

`i + 4 ≤ body.size` is load-bearing for the *proof* and **not for the truth** — the fourth such
hypothesis in this module, not an exception to the pattern. Past the end both sides are `none`: the
right side fails its own `i + 4 ≤ size` guard, and the left side's slice clamps to fewer than four
bytes and fails the guard too. `readUInt32LE_extract_beyond_end` records it. -/
theorem readUInt32LE_extract (body : ByteArray) (i : Nat) (h : i + 4 ≤ body.size) :
    readUInt32LE (body.extract i (i + 4)) 0 = readUInt32LE body i := by
  have hslice : (body.extract i (i + 4)).size = 4 := by rw [ByteArray.size_extract]; omega
  rw [readUInt32LE, readUInt32LE, dif_pos (by omega : 0 + 4 ≤ (body.extract i (i + 4)).size),
    dif_pos h]
  simp only [ByteArray.getElem_extract, Nat.zero_add, Nat.add_zero]

/-- `readUInt32LE_extract` holds past the end too: both sides are `none`, so its size hypothesis is
needed only by the proof. Checked at a two-byte buffer read from 0, where the slice clamps to two
bytes and neither side can produce a value. Concrete counterexample-style. -/
theorem readUInt32LE_extract_beyond_end :
    readUInt32LE ((⟨#[7, 8]⟩ : ByteArray).extract 0 4) 0 = readUInt32LE (⟨#[7, 8]⟩ : ByteArray) 0
      ∧ readUInt32LE (⟨#[7, 8]⟩ : ByteArray) 0 = none := by decide

/-- A successful `uint32` read implies the buffer reaches four bytes past the offset.

Found by the load-bearing audit: the offset-value equivalence below was first stated with
`i + 4 ≤ body.size` as a separate hypothesis, and it is not merely non-load-bearing — it is
*derivable*, because `readUInt32LE` returns `none` past the end. So the audit's question has three
answers, not two: needed for truth, needed only by the proof, or already implied. -/
theorem readUInt32LE_fits {body : ByteArray} {i : Nat} {o : UInt32}
    (h : readUInt32LE body i = some o) : i + 4 ≤ body.size := by
  rw [readUInt32LE] at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- **An offset-table entry matches its four bytes exactly when its value is the offset read there.**

This is the step from the join's byte-level conditions to the source's offset values. The `n < 2^32`
bound is where `meaningRequireU32Length` earns its place at the head of `meaningDecodeRaw`: without it
`Nat.toUInt32` wraps and two different cumulative sums can write the same four bytes, so the table
would no longer determine the offsets. -/
theorem uint32LE_eq_extract_iff (body : ByteArray) (i n : Nat) (o : UInt32)
    (hread : readUInt32LE body i = some o) (hn : n < UInt32.size) :
    uint32LE (Nat.toUInt32 n) = body.extract i (i + 4) ↔ n = o.toNat := by
  have hfits : i + 4 ≤ body.size := readUInt32LE_fits hread
  have hslice : (body.extract i (i + 4)).size = 4 := by rw [ByteArray.size_extract]; omega
  have hcanon : uint32LE o = body.extract i (i + 4) :=
    uint32LE_of_readUInt32LE _ o hslice (by rw [readUInt32LE_extract body i hfits]; exact hread)
  rw [← hcanon]
  constructor
  · intro h
    rw [← uint32LE_injective h]
    exact (UInt32.toNat_ofNat_of_lt hn).symm
  · intro h
    subst h
    rw [show Nat.toUInt32 o.toNat = o from UInt32.ofNat_toNat]

/-- **`hn` above IS load-bearing for truth** — the first hypothesis in this module that is, rather
than being needed only by its proof. `Nat.toUInt32` wraps at `2 ^ 32`, so `2 ^ 32` and `0` write the
same four bytes while differing as offsets: the left side of the equivalence would hold and the right
side fail. Concrete counterexample-style, at the wrap point itself. -/
theorem uint32LE_eq_extract_needs_bound :
    Nat.toUInt32 4294967296 = Nat.toUInt32 0 ∧ (4294967296 : Nat) ≠ 0 := by decide

/-! ## (ii) from (i), concretely

The decomposition's whole non-circularity claim is that the offset-table conditions follow from the
per-field canonicality conditions rather than standing beside them. Here is that implication as
arithmetic: if each field's serialization *is* its slice, then each field's width is the gap between
consecutive offsets, so the cumulative sums the offset table encodes are the offsets themselves. -/

/-- **Per-field canonicality forces the cumulative sums to be the offsets.**

This is (ii)-from-(i). Nothing about serialization is used — only that each `s_i` is the slice between
its offsets, which pins its width.

Note the *fourth* field never appears: the table has four entries and the last field runs to the
buffer end, so no offset encodes `s3`'s width and no hypothesis about it is needed. The compiler
found that — an earlier version took `s3` and a canonicality hypothesis for it, both unused. -/
theorem cumulative_sums_eq_offsets (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (s0 s1 s2 : ByteArray)
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size)
    (c0 : s0 = body.extract o0 o1) (c1 : s1 = body.extract o1 o2)
    (c2 : s2 = body.extract o2 o3) :
    16 + s0.size = o1 ∧ 16 + s0.size + s1.size = o2 ∧
      16 + s0.size + s1.size + s2.size = o3 := by
  subst c0 c1 c2 h0
  rw [ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
  omega

/-! ## Assembling the entry theorem

`decodeCanonical` at the entry schema, unfolded to the two things it actually does: walk the four
field slices, then test re-serialization. The `used = body.size` check disappears here rather than
being discharged — the variable-container arm returns `(v, b.size)`, so it is satisfied by
construction, which is `deserialize_container_used` at this schema. -/

/-- A successful entry offset table forces the body to reach sixteen bytes.

Found by resolving a load-bearing question I had first left hedged: the table's fourth entry is read
at offset 12, so `readUInt32LE_fits` gives `16 ≤ body.size` for free. Another *derivable*
hypothesis — the third category again, and the second time it has appeared as a size bound sitting
next to a successful read. -/
theorem extractFieldOffsets_entry_fits (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3]) :
    16 ≤ body.size := by
  rw [extractFieldOffsets_entry] at hoffs
  split at hoffs
  · rename_i h3
    exact readUInt32LE_fits h3
  · exact absurd hoffs (by simp)

theorem decodeCanonical_entry_unfold (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3])
    (h0 : o0 = 16) :
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body =
      match SSZType.deserializeVarFields entryFields body 0 [o0, o1, o2, o3] body.size with
      | .error e => .error e
      | .ok v =>
          if SSZType.serialize BinaryFv.Specs.SSZ.statelessInputV4Type v == body then .ok v
          else .error .invalidOffset := by
  have hdes : SSZType.deserialize BinaryFv.Specs.SSZ.statelessInputV4Type body =
      match SSZType.deserializeVarFields entryFields body 0 [o0, o1, o2, o3] body.size with
      | .error e => .error e
      | .ok v => .ok (v, body.size) := by
    have h16 : 16 ≤ body.size := extractFieldOffsets_entry_fits body o0 o1 o2 o3 hoffs
    show SSZType.deserialize (.container entryFields) body = _
    rw [SSZType.deserialize, if_neg (by rw [entryFields_not_allFixed]; simp)]
    simp only []
    rw [if_neg (by rw [entryFields_fixedSectionSize]; omega)]
    simp only [hoffs, List.head?_cons]
    rw [if_neg (by rw [entryFields_fixedSectionSize, h0]; simp)]
    -- Both sides are the same `match`, but on different motives, so `rfl` needs the scrutinee
    -- reduced on both rather than on the left alone.
    cases SSZType.deserializeVarFields entryFields body 0 [o0, o1, o2, o3] body.size <;> rfl
  rw [BinaryFv.Specs.SSZ.decodeCanonical]
  rw [hdes]
  cases SSZType.deserializeVarFields entryFields body 0 [o0, o1, o2, o3] body.size <;>
    simp [bind, Except.bind] <;> rfl

/-- **`decodeCanonical` where the deserialize consumes its whole buffer** reduces to the
re-serialization test alone.

The per-field workhorse: the composition needs this four times, once per entry field, and the
`used = b.size` premise is exactly what `deserialize_container_used` supplies for the three
containers and what the fixed-element list arm's `trailingBytes` guard supplies for the fourth. -/
theorem decodeCanonical_of_used_eq (t : SSZType) (b : ByteArray) (x : t.interp) (u : Nat)
    (hdes : SSZType.deserialize t b = .ok (x, u)) (hused : u = b.size) :
    BinaryFv.Specs.SSZ.decodeCanonical t b =
      if SSZType.serialize t x == b then .ok x else .error .invalidOffset := by
  subst hused
  rw [BinaryFv.Specs.SSZ.decodeCanonical, hdes]
  simp [bind, Except.bind]
  rfl

/-! ### Discharging the workhorse premise per field

`decodeCanonical_of_used_eq` needs `used = b.size` at each entry field. For the three containers
that is `deserialize_container_used`, and the `allFixedSize` premise is exactly the `isFixedSize`
fact already proved by `decide` — `isFixedSize (.container fs)` *is* `allFixedSize fs`, so the two
statements are definitionally the same and no bridging lemma is needed. -/

theorem deserialize_newPayloadRequest_used {b : ByteArray}
    {x : BinaryFv.Specs.SSZ.newPayloadRequestType.interp} {u : Nat}
    (h : SSZType.deserialize BinaryFv.Specs.SSZ.newPayloadRequestType b = .ok (x, u)) : u = b.size :=
  deserialize_container_used _ b newPayloadRequestType_not_fixed x u h

theorem deserialize_witness_used {b : ByteArray}
    {x : BinaryFv.Specs.SSZ.witnessType.interp} {u : Nat}
    (h : SSZType.deserialize BinaryFv.Specs.SSZ.witnessType b = .ok (x, u)) : u = b.size :=
  deserialize_container_used _ b witnessType_not_fixed x u h

theorem deserialize_chainConfig_used {b : ByteArray}
    {x : BinaryFv.Specs.SSZ.chainConfigType.interp} {u : Nat}
    (h : SSZType.deserialize BinaryFv.Specs.SSZ.chainConfigType b = .ok (x, u)) : u = b.size :=
  deserialize_container_used _ b chainConfigType_not_fixed x u h

/-! ### The fourth field: a fixed-element list

`publicKeysType` is `.list (byteVector 65) maxPublicKeys`, and `byteVector 65` is `.vector u8 65`,
which is *fixed*-size. So it takes `deserialize`'s fixed-element list arm, and its `used = b.size`
comes from a different mechanism than the three containers: the arm rejects with `trailingBytes`
unless `count * sz = b.size`, and `deserializeFixedElems` accumulates exactly `count * sz`.

That second half does not fall out definitionally — it needs an induction on the element count,
which is why this field was sized separately from the three one-liners. -/

/-- `deserializeFixedElems` reports exactly `count * sz` bytes past whatever it started with. -/
theorem deserializeFixedElems_size (t : SSZType) :
    ∀ (count : Nat) (b : ByteArray) (off sz : Nat) (acc : List t.interp) (accSz : Nat)
      (xs : List t.interp) (n : Nat),
      SSZType.deserializeFixedElems t count b off sz acc accSz = .ok (xs, n) →
        n = accSz + count * sz := by
  intro count
  induction count with
  | zero =>
      intro b off sz acc accSz xs n h
      rw [SSZType.deserializeFixedElems] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      omega
  | succ k ih =>
      intro b off sz acc accSz xs n h
      rw [SSZType.deserializeFixedElems] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · have := ih b (off + sz) sz _ (accSz + sz) xs n h
          rw [this, Nat.succ_mul]
          omega

/-- The public-keys list reports consuming its whole buffer. -/
theorem deserialize_publicKeys_used {b : ByteArray} {x : publicKeysType.interp} {u : Nat}
    (h : SSZType.deserialize publicKeysType b = .ok (x, u)) : u = b.size := by
  simp only [publicKeysType] at h
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

/-! ### Splitting the body region four ways

The join's fifth condition is `s0 ++ (s1 ++ (s2 ++ s3)) = body.extract 16 body.size` — the whole
variable region against the four field bodies. Taking it apart needs the same treatment as the
offset table, but at *offset-determined* widths rather than a fixed four bytes. -/

/-- Four consecutive slices reassemble the span they cover. -/
theorem extract_four (body : ByteArray) (a b c d e : Nat)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e) :
    body.extract a b ++ (body.extract b c ++ (body.extract c d ++ body.extract d e))
      = body.extract a e := by
  rw [ByteArray.extract_append_extract, show min c d = c by omega, show max d e = e by omega,
    ByteArray.extract_append_extract, show min b c = b by omega, show max c e = e by omega,
    ByteArray.extract_append_extract, show min a b = a by omega, show max b e = e by omega]

/-- **The variable region matches exactly when each field body matches its own slice.**

The widths come from the offsets rather than from a constant, so each is `o_{i+1} - o_i`; that is
what `cumulative_sums_eq_offsets` supplies from the per-field canonicality conditions. -/
theorem append4_eq_extract_region_iff (body : ByteArray) (o1 o2 o3 : Nat)
    {s0 s1 s2 s3 : ByteArray}
    (h01 : 16 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size)
    (w0 : s0.size = o1 - 16) (w1 : s1.size = o2 - o1) (w2 : s2.size = o3 - o2) :
    s0 ++ (s1 ++ (s2 ++ s3)) = body.extract 16 body.size ↔
      (s0 = body.extract 16 o1 ∧ s1 = body.extract o1 o2 ∧ s2 = body.extract o2 o3 ∧
        s3 = body.extract o3 body.size) := by
  have e0 : (body.extract 16 o1).size = o1 - 16 := by rw [ByteArray.size_extract]; omega
  have e1 : (body.extract o1 o2).size = o2 - o1 := by rw [ByteArray.size_extract]; omega
  have e2 : (body.extract o2 o3).size = o3 - o2 := by rw [ByteArray.size_extract]; omega
  constructor
  · intro h
    rw [← extract_four body 16 o1 o2 o3 body.size h01 h12 h23 h3] at h
    obtain ⟨p0, h'⟩ := append_inj_of_size_eq (by rw [w0, e0]) h
    obtain ⟨p1, h''⟩ := append_inj_of_size_eq (by rw [w1, e1]) h'
    obtain ⟨p2, p3⟩ := append_inj_of_size_eq (by rw [w2, e2]) h''
    exact ⟨p0, p1, p2, p3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact extract_four body 16 o1 o2 o3 body.size h01 h12 h23 h3

/-! ### Inverting `decodeCanonical`

`decodeCanonical_of_used_eq` runs one way — from a deserialize to the canonicality test. The chain
needs the other: from an *acceptance*, recover both the deserialize and the re-serialization
equality. Every per-field hypothesis in the composition arrives as an acceptance, so this is the
entry point to all four. -/

/-- **Acceptance gives back both halves**: the deserialize that produced the value, consuming the
whole buffer, and the re-serialization equality that certified it canonical. -/
theorem decodeCanonical_inv {t : SSZType} {b : ByteArray} {x : t.interp}
    (h : BinaryFv.Specs.SSZ.decodeCanonical t b = .ok x) :
    SSZType.deserialize t b = .ok (x, b.size) ∧ SSZType.serialize t x = b := by
  rw [BinaryFv.Specs.SSZ.decodeCanonical] at h
  revert h
  cases hd : SSZType.deserialize t b with
  | error e => intro h; simp [bind, Except.bind] at h
  | ok pair =>
      obtain ⟨value, used⟩ := pair
      simp only [bind, Except.bind]
      split
      · intro h; exact absurd h (by simp)
      · rename_i hused
        split
        · rename_i hser
          intro h
          -- `pure value` is `Except.ok value` only up to defeq, so coerce before injecting.
          have h' : (Except.ok value : Except SSZError t.interp) = Except.ok x := h
          injection h' with hvx
          subst hvx
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hused
          subst hused
          exact ⟨rfl, byteArray_eq_of_beq hser⟩
        · intro h; exact absurd h (by simp)

/-! ### Recovering the reads behind the table

`uint32LE_eq_extract_iff` is stated against a *read* at an offset, but the composition carries the
table as a list of `Nat`s. This recovers the four reads that produced them, which is what lets each
offset-bytes condition become an offset-value condition. -/

theorem entry_offset_reads (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3]) :
    ∃ w0 w1 w2 w3 : UInt32,
      readUInt32LE body 0 = some w0 ∧ readUInt32LE body 4 = some w1 ∧
      readUInt32LE body 8 = some w2 ∧ readUInt32LE body 12 = some w3 ∧
      o0 = w0.toNat ∧ o1 = w1.toNat ∧ o2 = w2.toNat ∧ o3 = w3.toNat := by
  rw [extractFieldOffsets_entry] at hoffs
  split at hoffs
  · rename_i w0 w1 w2 w3 h0 h1 h2 h3
    simp only [Except.ok.injEq, List.cons.injEq] at hoffs
    exact ⟨w0, w1, w2, w3, h0, h1, h2, h3, hoffs.1.symm, hoffs.2.1.symm,
      hoffs.2.2.1.symm, hoffs.2.2.2.1.symm⟩
  · exact absurd hoffs (by simp)

/-- Each offset-bytes condition, as an offset-value condition. -/
theorem entry_offsetBytes_iff (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3])
    (n : Nat) (hn : n < UInt32.size) :
    (uint32LE (Nat.toUInt32 n) = body.extract 0 4 ↔ n = o0) ∧
    (uint32LE (Nat.toUInt32 n) = body.extract 4 8 ↔ n = o1) ∧
    (uint32LE (Nat.toUInt32 n) = body.extract 8 12 ↔ n = o2) ∧
    (uint32LE (Nat.toUInt32 n) = body.extract 12 16 ↔ n = o3) := by
  obtain ⟨w0, w1, w2, w3, r0, r1, r2, r3, e0, e1, e2, e3⟩ := entry_offset_reads body o0 o1 o2 o3 hoffs
  subst e0; subst e1; subst e2; subst e3
  exact ⟨uint32LE_eq_extract_iff body 0 n w0 r0 hn,
    uint32LE_eq_extract_iff body 4 n w1 r1 hn,
    uint32LE_eq_extract_iff body 8 n w2 r2 hn,
    uint32LE_eq_extract_iff body 12 n w3 r3 hn⟩

/-! ## The entry composition, backward direction

From the four per-field canonical decodes to the spec's acceptance of the whole body. This is the
direction that has to *construct* the accepted value and show its re-serialization reproduces the
buffer, so it is where every piece built above finally meets. -/

/-- **Four canonical field decodes make the entry decode canonical.** -/
theorem decodeCanonical_entry_eq_of_fields
    (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size)
    (hu32 : body.size < UInt32.size)
    {x0 : BinaryFv.Specs.SSZ.newPayloadRequestType.interp} {x1 : BinaryFv.Specs.SSZ.witnessType.interp}
    {x2 : BinaryFv.Specs.SSZ.chainConfigType.interp} {x3 : publicKeysType.interp}
    (a0 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.newPayloadRequestType (body.extract o0 o1) = .ok x0)
    (a1 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.witnessType (body.extract o1 o2) = .ok x1)
    (a2 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType (body.extract o2 o3) = .ok x2)
    (a3 : BinaryFv.Specs.SSZ.decodeCanonical publicKeysType (body.extract o3 body.size) = .ok x3) :
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body
      = .ok (x0, x1, x2, x3, PUnit.unit) := by
  -- `omega` treats `UInt32.size` as an atom; this links it to the numeral.
  have husz : UInt32.size = 4294967296 := rfl
  obtain ⟨d0, s0eq⟩ := decodeCanonical_inv a0
  obtain ⟨d1, s1eq⟩ := decodeCanonical_inv a1
  obtain ⟨d2, s2eq⟩ := decodeCanonical_inv a2
  obtain ⟨d3, s3eq⟩ := decodeCanonical_inv a3
  subst h0
  -- Each field body is exactly its slice, so its width is the gap between consecutive offsets.
  have w0 : (SSZType.serialize BinaryFv.Specs.SSZ.newPayloadRequestType x0).size = o1 - 16 := by
    rw [s0eq, ByteArray.size_extract]; omega
  have w1 : (SSZType.serialize BinaryFv.Specs.SSZ.witnessType x1).size = o2 - o1 := by
    rw [s1eq, ByteArray.size_extract]; omega
  have w2 : (SSZType.serialize BinaryFv.Specs.SSZ.chainConfigType x2).size = o3 - o2 := by
    rw [s2eq, ByteArray.size_extract]; omega
  obtain ⟨c1, c2, c3⟩ :=
    cumulative_sums_eq_offsets body 16 o1 o2 o3 _ _ _ rfl h01 h12 h23 h3 s0eq s1eq s2eq
  -- `d3` is stated at `publicKeysType`; the walker's goal shows the unfolded list type. Defeq, so a
  -- restatement crosses it, but `rw` needs the syntactic form.
  have d3' : SSZType.deserialize
      (.list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes) BinaryFv.Specs.SSZ.maxPublicKeys)
      (body.extract o3 body.size) = .ok (x3, (body.extract o3 body.size).size) := d3
  rw [decodeCanonical_entry_unfold body 16 o1 o2 o3 hoffs rfl,
    deserializeVarFields_entry body 16 o1 o2 o3 h01 h12 h23 h3, d0, d1, d2, d3']
  have s3eq' : SSZType.serialize
      (.list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes) BinaryFv.Specs.SSZ.maxPublicKeys) x3
      = body.extract o3 body.size := s3eq
  have hser : SSZType.serialize BinaryFv.Specs.SSZ.statelessInputV4Type
      ((x0, x1, x2, x3, PUnit.unit) : SSZType.interpFields entryFields) = body := by
    show SSZType.serialize (.container entryFields) _ = body
    rw [serialize_entry_eq_body_iff body (x0, x1, x2, x3, PUnit.unit) _ _ _ _ rfl rfl rfl rfl
      (by omega)]
    -- Reduce `(x0, x1, x2, x3, unit).fst` etc. so `omega` sees the same atoms as `c1`/`c2`/`c3`.
    simp only []
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact ((entry_offsetBytes_iff body 16 o1 o2 o3 hoffs 16 (by omega)).1).mpr rfl
    · exact ((entry_offsetBytes_iff body 16 o1 o2 o3 hoffs _ (by omega)).2.1).mpr c1
    · exact ((entry_offsetBytes_iff body 16 o1 o2 o3 hoffs _ (by omega)).2.2.1).mpr c2
    · exact ((entry_offsetBytes_iff body 16 o1 o2 o3 hoffs _ (by omega)).2.2.2).mpr c3
    · exact (append4_eq_extract_region_iff body o1 o2 o3 h01 h12 h23 h3 w0 w1 w2).mpr
        ⟨s0eq, s1eq, s2eq, s3eq'⟩
  -- The four matches are on `Except.ok` literals; reduce them so `v` is the actual tuple.
  simp only []
  rw [hser, byteArray_beq_self]
  rfl

/-- Acceptance-granularity corollary of the value-level statement. -/
theorem decodeCanonical_entry_of_fields
    (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size)
    (hu32 : body.size < UInt32.size)
    {x0 : BinaryFv.Specs.SSZ.newPayloadRequestType.interp} {x1 : BinaryFv.Specs.SSZ.witnessType.interp}
    {x2 : BinaryFv.Specs.SSZ.chainConfigType.interp} {x3 : publicKeysType.interp}
    (a0 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.newPayloadRequestType (body.extract o0 o1) = .ok x0)
    (a1 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.witnessType (body.extract o1 o2) = .ok x1)
    (a2 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType (body.extract o2 o3) = .ok x2)
    (a3 : BinaryFv.Specs.SSZ.decodeCanonical publicKeysType (body.extract o3 body.size) = .ok x3) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body).toOption.isSome = true := by
  rw [decodeCanonical_entry_eq_of_fields body o0 o1 o2 o3 hoffs h0 h01 h12 h23 h3 hu32 a0 a1 a2 a3]
  rfl

/-! ### The fork bound is the same projection on both sides

`decodeRawInput` throws `unknownFork` on `raw.chainConfig.activeFork.fork > 20`, where
`raw = statelessInputOfInterp value`. `sourceShapedContainersAgreeWithSpec` bounds
`(rawChainConfigOf value').activeFork.fork` for the chainConfig *field's* decode. Those are the same
number, and the reason is definitional rather than analogous: `statelessInputOfInterp` sets
`chainConfig := rawChainConfigOf value.2.2.1`, so the whole-body projection *is* the field
projection applied to the third component.

This is why the value-level decomposition matters and the acceptance-level one does not suffice: the
bound is a predicate on the decoded VALUE, so matching it needs to know the entry decode's third
component is exactly what the chainConfig field decode returned. -/

theorem statelessInput_fork_eq_field_fork (value : BinaryFv.Specs.SSZ.statelessInputV4Type.interp) :
    (BinaryFv.Specs.SSZ.statelessInputOfInterp value).chainConfig.activeFork.fork
      = (BinaryFv.Specs.SSZ.rawChainConfigOf value.2.2.1).activeFork.fork := rfl

/-! ## The entry composition, forward direction

From the spec's acceptance of the whole body to the four per-field canonical decodes. The same
pieces as the backward direction, run the other way: the re-serialization equality is *given* here
and has to be taken apart, rather than assembled. -/

/-- **A canonical entry decode makes all four field decodes canonical.** -/
theorem decodeCanonical_entry_fields_of
    (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size)
    (hu32 : body.size < UInt32.size)
    (hacc : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body).toOption.isSome = true) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.newPayloadRequestType (body.extract o0 o1)).toOption.isSome
        = true ∧
      (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.witnessType (body.extract o1 o2)).toOption.isSome = true ∧
      (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType (body.extract o2 o3)).toOption.isSome
        = true ∧
      (BinaryFv.Specs.SSZ.decodeCanonical publicKeysType (body.extract o3 body.size)).toOption.isSome
        = true := by
  have husz : UInt32.size = 4294967296 := rfl
  subst h0
  rw [decodeCanonical_entry_unfold body 16 o1 o2 o3 hoffs rfl,
    deserializeVarFields_entry body 16 o1 o2 o3 h01 h12 h23 h3] at hacc
  split at hacc
  · exact absurd hacc (by simp [Except.toOption])
  · rename_i v heq
    split at hacc
    · rename_i hser
      -- Unpack the four field deserializes out of `heq`.
      split at heq
      · exact absurd heq (by simp)
      · rename_i x0 u0 hd0
        split at heq
        · exact absurd heq (by simp)
        · rename_i x1 u1 hd1
          split at heq
          · exact absurd heq (by simp)
          · rename_i x2 u2 hd2
            split at heq
            · exact absurd heq (by simp)
            · rename_i x3 u3 hd3
              simp only [Except.ok.injEq] at heq
              subst heq
              have hu0 := deserialize_newPayloadRequest_used hd0
              have hu1 := deserialize_witness_used hd1
              have hu2 := deserialize_chainConfig_used hd2
              have hu3 := deserialize_publicKeys_used hd3
              subst hu0; subst hu1; subst hu2; subst hu3
              have hb : SSZType.serialize BinaryFv.Specs.SSZ.statelessInputV4Type
                  ((x0, x1, x2, x3, PUnit.unit) : SSZType.interpFields entryFields) = body :=
                byteArray_eq_of_beq hser
              have hsplit := (serialize_entry_eq_body_iff body (x0, x1, x2, x3, PUnit.unit)
                _ _ _ _ rfl rfl rfl rfl (by omega)).mp hb
              simp only [] at hsplit
              obtain ⟨q0, q1, q2, q3, qr⟩ := hsplit
              -- The region equality bounds every cumulative sum by `body.size`, which is what the
              -- wrap-bound side conditions below need.
              have hsz := congrArg ByteArray.size qr
              simp only [ByteArray.size_append, ByteArray.size_extract] at hsz
              have c1 := ((entry_offsetBytes_iff body 16 o1 o2 o3 hoffs _ (by omega)).2.1).mp q1
              have c2 := ((entry_offsetBytes_iff body 16 o1 o2 o3 hoffs _ (by omega)).2.2.1).mp q2
              have c3 := ((entry_offsetBytes_iff body 16 o1 o2 o3 hoffs _ (by omega)).2.2.2).mp q3
              obtain ⟨r0, r1, r2, r3⟩ :=
                (append4_eq_extract_region_iff body o1 o2 o3 h01 h12 h23 h3
                  (by omega) (by omega) (by omega)).mp qr
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [decodeCanonical_of_used_eq _ _ x0 _ hd0 rfl, r0, byteArray_beq_self]; rfl
              · rw [decodeCanonical_of_used_eq _ _ x1 _ hd1 rfl, r1, byteArray_beq_self]; rfl
              · rw [decodeCanonical_of_used_eq _ _ x2 _ hd2 rfl, r2, byteArray_beq_self]; rfl
              · -- Defeq-not-syntactic again: goal at `publicKeysType`, hypotheses at the unfolded
                -- list type. `show` crosses it.
                show (BinaryFv.Specs.SSZ.decodeCanonical
                    (.list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes) BinaryFv.Specs.SSZ.maxPublicKeys)
                    (body.extract o3 body.size)).toOption.isSome = true
                rw [decodeCanonical_of_used_eq _ _ x3 _ hd3 rfl, r3, byteArray_beq_self]; rfl
    · exact absurd hacc (by simp [Except.toOption])

/-! ## The entry composition theorem

Both directions together. This is what item 6 was sized around: the spec's canonical decode of the
whole body and the four per-field canonical decodes accept **the same inputs**, not merely one
implying the other.

**Where the container obligation does *not* enter, and why that is not an omission.**
`sourceShapedContainersAgreeWithSpec` equates `isAccepted (meaningChainConfig bytes)` with
`decodeCanonical chainConfigType bytes` succeeding *and* `fork ≤ 20`. That bound is not part of the
schema: `chainConfigType` types `fork` as an unbounded `u64`, and the spec applies the bound one
layer up in `decodeRawInput`, after a complete canonical decode. So at *this* layer — `decodeCanonical`
against `decodeCanonical` — neither side applies it, and stating the theorem with the container
hypothesis would be stating a hypothesis it does not use.

The bound enters when this decomposition is composed towards `decodeRawInput` and `meaningDecodeRaw`,
where the spec's post-decode `fork > 20` check has to be matched against the source's check inside
`meaningChainConfig`. That is exactly the layering `sourceShapedContainersAgreeWithSpec` was
corrected for (`d652aff`), and it is why the container fact is an *ingredient* of the entry agreement
rather than a corollary of it. -/

theorem except_isSome_iff {α ε : Type} {e : Except ε α} :
    e.toOption.isSome = true ↔ ∃ x, e = .ok x := by
  cases e <;> simp [Except.toOption]

/-- **The entry composition theorem, both directions.** -/
theorem decodeCanonical_entry_iff_fields
    (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size)
    (hu32 : body.size < UInt32.size) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body).toOption.isSome = true ↔
      ((BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.newPayloadRequestType
            (body.extract o0 o1)).toOption.isSome = true ∧
        (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.witnessType (body.extract o1 o2)).toOption.isSome
            = true ∧
        (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType (body.extract o2 o3)).toOption.isSome
            = true ∧
        (BinaryFv.Specs.SSZ.decodeCanonical publicKeysType (body.extract o3 body.size)).toOption.isSome
            = true) := by
  constructor
  · exact decodeCanonical_entry_fields_of body o0 o1 o2 o3 hoffs h0 h01 h12 h23 h3 hu32
  · rintro ⟨a0, a1, a2, a3⟩
    obtain ⟨x0, e0⟩ := except_isSome_iff.mp a0
    obtain ⟨x1, e1⟩ := except_isSome_iff.mp a1
    obtain ⟨x2, e2⟩ := except_isSome_iff.mp a2
    obtain ⟨x3, e3⟩ := except_isSome_iff.mp a3
    exact decodeCanonical_entry_of_fields body o0 o1 o2 o3 hoffs h0 h01 h12 h23 h3 hu32 e0 e1 e2 e3

/-! ## Arity-free slicing

The `extract_four` / `append4_*` family above is generic over offsets but hard-coded at **four**
regions, so none of it reaches the chain containers: `forkActivation` has two variable fields,
`forkConfig` two, `chainConfig` one. Rather than three parallel copies, these two atoms cover every
arity by iteration — `extract_four` and `extract_sixteen` are just their arity-4 compositions.

Kept alongside the arity-4 lemmas rather than replacing them: those are already consumed by the entry
proofs, and rewriting working proofs to route through the atoms would be churn with no proof content.

**Two routes to one proposition do not create two sources of truth.** We refused a
second source for the manifest step bound because a proof-relevant *constant* with two sources can
drift silently. `extract_four` and its atom-composed equivalent are two *proofs* of one proposition,
each kernel-checked, and neither is a source of truth for a value — the proposition is. Nothing can
drift. -/

/-- Two consecutive slices reassemble the span they cover. The atom behind every `extract_*`
reassembly at any arity. -/
theorem extract_pair (body : ByteArray) (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) :
    body.extract a b ++ body.extract b c = body.extract a c := by
  rw [ByteArray.extract_append_extract, show min a b = a by omega, show max b c = c by omega]

/-- **Splitting a concatenation against a span at one point.** Iterating this gives the `n`-way split
at any arity; the width hypothesis is what fixes where the cut falls. -/
theorem append_eq_extract_iff (body : ByteArray) (a b c : Nat) {s t : ByteArray}
    (hab : a ≤ b) (hbc : b ≤ c) (hb : b ≤ body.size) (hs : s.size = b - a) :
    s ++ t = body.extract a c ↔ (s = body.extract a b ∧ t = body.extract b c) := by
  have hw : (body.extract a b).size = b - a := by rw [ByteArray.size_extract]; omega
  constructor
  · intro h
    rw [← extract_pair body a b c hab hbc] at h
    exact append_inj_of_size_eq (by rw [hs, hw]) h
  · rintro ⟨rfl, rfl⟩
    exact extract_pair body a b c hab hbc

/-! ## The four field meanings in spec terms

**This is where `sourceShapedContainersAgreeWithSpec` is consumed.** Three of the four field
meanings are `decodeCanonical` plus a projection, so their acceptance equals the spec's by
construction. The fourth, `meaningChainConfig`, is source-shaped and its acceptance carries the
`fork ≤ 20` bound that the schema does not — which is exactly what the container obligation states,
and why its conjunct below has a different shape from the other three.

That asymmetry is the whole content of this step. A reader looking for where the container fact is
discharged should find it here, and should see that it is *not* discharged by the four-field
decomposition, which is pure spec on both sides. -/

theorem entry_field_meanings_in_spec_terms
    (containersAgree : sourceShapedContainersAgreeWithSpec) (b : ByteArray) :
    isAccepted (meaningNewPayloadRequest b)
        = (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.newPayloadRequestType b).toOption.isSome ∧
      isAccepted (meaningExecutionWitness b)
        = (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.witnessType b).toOption.isSome ∧
      isAccepted (meaningPublicKeys b)
        = (BinaryFv.Specs.SSZ.decodeCanonical publicKeysType b).toOption.isSome ∧
      isAccepted (meaningChainConfig b)
        = (match BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType b with
            | .ok value => decide ((BinaryFv.Specs.SSZ.rawChainConfigOf value).activeFork.fork ≤ 20)
            | .error _ => false) :=
  ⟨meaningNewPayloadRequest_accepted b, meaningExecutionWitness_accepted b,
    meaningPublicKeys_accepted b, containersAgree b⟩

/-! ## A successful container decode pins its first offset

The V3 exclusion needs this at three nesting levels — entry body, then
`newPayloadRequestType`, then `executionPayloadType` — so it is worth stating once over an arbitrary
field list rather than three times concretely. The fact is small: the container arm rejects with
`invalidOffset` unless the first offset *equals* the fixed section size, so a successful decode
determines that offset exactly.

That equality is the whole mechanism behind `v3ShapeExcludesCanonicalV4`. The V3 classifier reads the
`u32` at execution-payload byte 436 and demands `528`; canonicality forces `540` there. 436 is where
`executionPayloadType`'s first *variable* field offset is written — the six byte-vectors and four
`u64`s before it occupy `32+20+32+32+256+32 = 404` then `4 * 8 = 32`, so 436 — and 540 is that
schema's fixed section size, not a constant taken from the V4 spec. If a field is ever added to
`executionPayloadType`, 540 moves and the exclusion argument changes with it; the derivation is what
makes that visible rather than silent. -/

theorem deserialize_container_firstOffset {fs : List SSZType} {b : ByteArray}
    (hvar : SSZType.allFixedSize fs = false)
    {v : SSZType.interpFields fs} {u : Nat}
    (h : SSZType.deserialize (.container fs) b = .ok (v, u)) :
    ∃ offs, extractFieldOffsets b fs 0 = .ok offs ∧
      offs.head? = some (SSZType.fixedSectionSizeFields fs) := by
  rw [SSZType.deserialize, if_neg (by simp [hvar])] at h
  simp only [] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i offs hext
      have hne := extractFieldOffsets_ne_nil b fs 0 offs hvar hext
      cases offs with
      | nil => exact absurd rfl hne
      | cons first rest =>
          simp only [List.head?_cons] at h
          split at h
          · simp at h
          · rename_i hfirst
            refine ⟨first :: rest, hext, ?_⟩
            simp only [List.head?_cons, Option.some.injEq]
            exact Classical.byContradiction fun hc => hfirst hc

/-! ### The 540 and the 436, machine-checked

The derivation above is prose; these make it a fact the compiler holds. If a field is added to
`executionPayloadType`, one of these `decide`s fails and the V3 exclusion argument is forced open
rather than quietly becoming wrong. That is the point of deriving the constants instead of quoting
them. -/

/-- `executionPayloadType`'s field list, named so the sizes below can be stated about it. -/
def executionPayloadFields : List SSZType :=
  [BinaryFv.Specs.SSZ.byteVector 32, BinaryFv.Specs.SSZ.byteVector 20, BinaryFv.Specs.SSZ.byteVector 32,
    BinaryFv.Specs.SSZ.byteVector 32, BinaryFv.Specs.SSZ.byteVector 256, BinaryFv.Specs.SSZ.byteVector 32,
    BinaryFv.Specs.SSZ.u64, BinaryFv.Specs.SSZ.u64, BinaryFv.Specs.SSZ.u64, BinaryFv.Specs.SSZ.u64,
    BinaryFv.Specs.SSZ.byteList BinaryFv.Specs.SSZ.maxExtraDataBytes,
    BinaryFv.Specs.SSZ.u256,
    BinaryFv.Specs.SSZ.byteVector 32,
    .list (BinaryFv.Specs.SSZ.byteList BinaryFv.Specs.SSZ.maxBytesPerTransaction) BinaryFv.Specs.SSZ.maxTransactionsPerPayload,
    .list BinaryFv.Specs.SSZ.withdrawalType BinaryFv.Specs.SSZ.maxWithdrawalsPerPayload,
    BinaryFv.Specs.SSZ.u64, BinaryFv.Specs.SSZ.u64,
    BinaryFv.Specs.SSZ.byteList BinaryFv.Specs.SSZ.maxBytesPerTransaction,
    BinaryFv.Specs.SSZ.u64]

theorem executionPayloadType_eq :
    BinaryFv.Specs.SSZ.executionPayloadType = .container executionPayloadFields := rfl

/-- **540 is derived.** The fixed section size canonicality forces the first variable offset to
equal. -/
theorem executionPayloadFields_fixedSection :
    SSZType.fixedSectionSizeFields executionPayloadFields = 540 := by decide

/-- **436 is derived.** The ten leading fixed fields occupy exactly that much, which is where the
first variable field's offset slot falls — the byte the V3 classifier reads. -/
theorem executionPayloadFields_leadingFixed :
    SSZType.fixedSectionSizeFields (executionPayloadFields.take 10) = 436 := by decide

/-- And the two constants genuinely conflict: the V3 classifier's `528` is neither of them. -/
theorem v3Constant_ne_v4FixedSection : (528 : Nat) ≠ 540 := by decide

/-- `newPayloadRequestType`'s field list, the middle level of the V3 classifier's descent. -/
def newPayloadRequestFields : List SSZType :=
  [BinaryFv.Specs.SSZ.executionPayloadType,
    .list (BinaryFv.Specs.SSZ.byteVector 32) BinaryFv.Specs.SSZ.maxBlobCommitmentsPerBlock,
    BinaryFv.Specs.SSZ.byteVector 32,
    BinaryFv.Specs.SSZ.executionRequestsType]

theorem newPayloadRequestType_eq :
    BinaryFv.Specs.SSZ.newPayloadRequestType = .container newPayloadRequestFields := rfl

/-- **44 is derived too** — offsets at 0 and 4, the fixed `byteVector 32` across bytes 8–39, the
last offset at 40. -/
theorem newPayloadRequestFields_fixedSection :
    SSZType.fixedSectionSizeFields newPayloadRequestFields = 44 := by decide

/-! ### Why the V3 classifier looks like it should discriminate, and does not until the last test

All three constants the classifier keys on are now derived from field lists rather than quoted, and
laid out together the story is legible: **the first two agree with V4 and only the third conflicts.**

* `requestOffset = 16` — and `entryFields`' fixed section is 16, so V4 passes.
* `payloadOffset = 44` — and `newPayloadRequestFields`' fixed section is 44, so V4 passes again.
* the `u32` at payload byte 436 must be `528` — but `executionPayloadFields`' fixed section is 540,
  and canonicality *forces* that byte to be the fixed section size. V4 cannot pass.

So the exclusion is not "the shapes obviously differ". A V4 buffer satisfies two thirds of the
classifier exactly, and the conflict is one decidable inequality deep — which is why it is invisible
by eye, and why 528 being itself a plausible intermediate offset in the same fixed section makes it
more so. -/

theorem v3Classifier_constants_derived :
    SSZType.fixedSectionSizeFields entryFields = 16 ∧
      SSZType.fixedSectionSizeFields newPayloadRequestFields = 44 ∧
      SSZType.fixedSectionSizeFields executionPayloadFields = 540 ∧
      (528 : Nat) ≠ 540 :=
  ⟨entryFields_fixedSectionSize, newPayloadRequestFields_fixedSection,
    executionPayloadFields_fixedSection, by decide⟩

/-! ### Where a container's first offset is read

`deserialize_container_firstOffset` says what the first offset must *equal*; this says where it is
*read from*. Together they are the pincer the V3 exclusion closes with: at each nesting level the
byte at the leading-fixed width must hold the fixed section size, and the classifier demands a
different value at exactly that byte.

Stated over an arbitrary field list, so the same lemma gives 0 for `entryFields` and
`newPayloadRequestFields` — whose first fields are variable — and 436 for `executionPayloadFields`,
whose ten leading fixed fields push the first offset slot that far in. The `436` in the docstrings
above is this lemma applied, not a separate observation. -/

theorem extractFieldOffsets_head_position (b : ByteArray) :
    ∀ (fs : List SSZType) (off : Nat) (offs : List Nat),
      extractFieldOffsets b fs off = .ok offs → offs ≠ [] →
        offs.head? =
          (readUInt32LE b (off + SSZType.fixedSectionSizeFields
            (fs.takeWhile SSZType.isFixedSize))).map UInt32.toNat := by
  intro fs
  induction fs with
  | nil =>
      intro off offs hext hne
      rw [extractFieldOffsets] at hext
      simp only [Except.ok.injEq] at hext
      exact absurd hext.symm hne
  | cons t ts ih =>
      intro off offs hext hne
      by_cases hfix : t.isFixedSize
      · rw [extractFieldOffsets, if_pos hfix] at hext
        have := ih (off + t.fixedByteSize) offs hext hne
        rw [this, List.takeWhile_cons_of_pos (by simpa using hfix),
          SSZType.fixedSectionSizeFields, SSZType.fixedSectionSize, if_pos hfix, Nat.add_assoc]
      · rw [extractFieldOffsets, if_neg hfix] at hext
        rw [List.takeWhile_cons_of_neg (by simpa using hfix), SSZType.fixedSectionSizeFields]
        split at hext
        · exact absurd hext (by simp)
        · rename_i o hread
          split at hext
          · rename_i rest hrest
            simp only [Except.ok.injEq] at hext
            subst hext
            simp only [List.head?_cons, Nat.add_zero, hread, Option.map_some]
          · exact absurd hext (by simp)

/-! ### Descending one level: the first field's slice

The V3 exclusion only needs the *first* field at each level, never the others, so this is deliberately
weaker than a full decomposition: a successful walk decodes its first field on `[o0, o1)`, and that is
all. Writing the whole mixed-arity decomposition for `newPayloadRequestType` would be the specialised
work we agreed not to generalise — and for this argument it would also be work nothing consumes.

Stated over an arbitrary field list whose first field is variable, so it serves the entry level and
the request level alike. -/

@[simp] theorem executionPayloadType_not_fixed :
    BinaryFv.Specs.SSZ.executionPayloadType.isFixedSize = false := by decide

/-- A successful variable-first field walk decodes its first field on the slice between the first two
offsets. -/
theorem deserializeVarFields_first_field {t : SSZType} {ts : List SSZType} {b : ByteArray}
    (hvar : t.isFixedSize = false) (o0 o1 : Nat) (rest : List Nat) (bufEnd : Nat)
    {v : SSZType.interpFields (t :: ts)}
    (h : SSZType.deserializeVarFields (t :: ts) b 0 (o0 :: o1 :: rest) bufEnd = .ok v) :
    ∃ x u, SSZType.deserialize t (b.extract o0 o1) = .ok (x, u) := by
  rw [SSZType.deserializeVarFields, if_neg (by simp [hvar])] at h
  simp only [List.head?_cons, Option.getD_some] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i x u hpair
      exact ⟨x, u, hpair⟩

/-! ### The container arm's parts, in one extraction

`deserialize_container_firstOffset` returns the offset fact and drops the walk; the descent needs the
walk. Returning both from one traversal is what lets the V3 argument chain levels **without any
specialised decomposition** — each level yields its offset table, its pinned first offset, and the
walk that the next level's first field comes out of, all from the same generic lemma.

That is the whole of item 4's structural content. The remaining work is arithmetic on three field
lists, which is already `decide`d. -/

theorem deserialize_container_parts {fs : List SSZType} {b : ByteArray}
    (hvar : SSZType.allFixedSize fs = false)
    {v : SSZType.interpFields fs} {u : Nat}
    (h : SSZType.deserialize (.container fs) b = .ok (v, u)) :
    ∃ offs, extractFieldOffsets b fs 0 = .ok offs ∧
      offs.head? = some (SSZType.fixedSectionSizeFields fs) ∧
      SSZType.deserializeVarFields fs b 0 offs b.size = .ok v := by
  rw [SSZType.deserialize, if_neg (by simp [hvar])] at h
  simp only [] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i offs hext
      have hne := extractFieldOffsets_ne_nil b fs 0 offs hvar hext
      cases offs with
      | nil => exact absurd rfl hne
      | cons first rest =>
          simp only [List.head?_cons] at h
          split at h
          · simp at h
          · rename_i hfirst
            split at h
            · simp at h
            · rename_i w hwalk
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              refine ⟨first :: rest, hext, ?_, ?_⟩
              · simp only [List.head?_cons, Option.some.injEq]
                exact Classical.byContradiction fun hc => hfirst hc
              · rw [hwalk, h.1]

/-! ### What the V3 classifier actually asserts

`hasV3PayloadShape` is nested `if`s and `match`es over three levels of slice. This extracts its
content in the form the exclusion consumes: the schema id, the two body offsets with the first pinned
to 16, the two request offsets with the first pinned to 44, and the payload byte 436 demanded to be
528.

The two pinned constants are stated as literals rather than variables because the classifier tests
them with `!=` and rejects otherwise — so a buffer that passes has exactly those values, and carrying
them as variables would lose the fact the exclusion turns on.

**Do not helpfully generalise them.** The instinct that a statement quantified over its constants is
stronger fails here: `16` and `44` are what meet the derived fixed-section sizes, so a version with
variables would not be weaker-but-safer, it would be about something else. That is the
not-about-this-layer failure appearing as over-generalisation rather than as a spurious hypothesis. -/

theorem hasV3PayloadShape_parts {bytes : ByteArray}
    (h : BinaryFv.Specs.SSZ.hasV3PayloadShape bytes = true) :
    ∃ hashesOffset payloadEnd,
      BinaryFv.Specs.SSZ.hasSchemaId bytes = true ∧
      BinaryFv.Specs.SSZ.readU32LE? (bytes.extract 2 bytes.size) 0 = some 16 ∧
      BinaryFv.Specs.SSZ.readU32LE? (bytes.extract 2 bytes.size) 4 = some hashesOffset ∧
      BinaryFv.Specs.SSZ.readU32LE? ((bytes.extract 2 bytes.size).extract 16 hashesOffset) 0 = some 44 ∧
      BinaryFv.Specs.SSZ.readU32LE? ((bytes.extract 2 bytes.size).extract 16 hashesOffset) 4
        = some payloadEnd ∧
      BinaryFv.Specs.SSZ.readU32LE?
        (((bytes.extract 2 bytes.size).extract 16 hashesOffset).extract 44 payloadEnd) 436
          = some 528 := by
  rw [BinaryFv.Specs.SSZ.hasV3PayloadShape] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hschema
    simp only [Bool.not_eq_true'] at hschema
    simp only [] at h
    split at h
    · rename_i req hashes hr hh
      split at h
      · exact absurd h (by simp)
      · rename_i hbad
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hbad
        split at h
        · rename_i po pe hp hpe
          split at h
          · exact absurd h (by simp)
          · rename_i hbad2
            simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hbad2
            have hreq : req = 16 := by simpa using hbad.1.1
            have hpo : po = 44 := by simpa using hbad2.1.1
            subst hreq
            subst hpo
            exact ⟨hashes, pe, by simpa using hschema, hr, hh, hp, hpe, by simpa using h⟩
        · exact absurd h (by simp)
    · exact absurd h (by simp)

/-! ### The sharp end: byte 436 must read 540

This is where the exclusion actually bites, and where the **second `bv_decide` door** enters, exactly
as pre-announced: the classifier reads with `BinaryFv.Specs.SSZ.readU32LE?` while canonicality constrains
`readUInt32LE`, and `readU32LE?_eq_map_readUInt32LE` is the only bridge general enough in offset and
value to cross that. The zero-specific bridge does not apply.

Everything else here is already proved: `deserialize_container_parts` pins the first offset to the
fixed section size, `extractFieldOffsets_head_position` puts it at the leading-fixed width, and both
numbers come from `decide` on the field list. -/

theorem executionPayloadFields_not_allFixed :
    SSZType.allFixedSize executionPayloadFields = false := by decide

/-- The leading-fixed width in the exact form `extractFieldOffsets_head_position` produces. -/
theorem executionPayloadFields_takeWhile_fixed :
    SSZType.fixedSectionSizeFields
      (executionPayloadFields.takeWhile SSZType.isFixedSize) = 436 := by decide

/-- **A canonical execution-payload decode forces byte 436 to read 540**, which is exactly what the
V3 classifier demands be 528. -/
theorem executionPayload_byte436_eq_540 {payload : ByteArray}
    {y : SSZType.interpFields executionPayloadFields} {u : Nat}
    (h : SSZType.deserialize (.container executionPayloadFields) payload = .ok (y, u)) :
    BinaryFv.Specs.SSZ.readU32LE? payload 436 = some 540 := by
  obtain ⟨offs, hext, hhead, _⟩ := deserialize_container_parts executionPayloadFields_not_allFixed h
  have hne : offs ≠ [] := by
    intro hc; rw [hc] at hhead; exact absurd hhead (by simp)
  have hpos := extractFieldOffsets_head_position payload executionPayloadFields 0 offs hext hne
  rw [executionPayloadFields_takeWhile_fixed, Nat.zero_add] at hpos
  rw [hhead, executionPayloadFields_fixedSection] at hpos
  -- `hpos : some 540 = (readUInt32LE payload 436).map UInt32.toNat`; the bridge turns the classifier's
  -- reader into that same expression.
  rw [readU32LE?_eq_map_readUInt32LE, ← hpos]

/-! ### The request level's offset table

The one place the V3 chain needs a *specialised* reduction rather than a generic lemma, and it is
small: identifying the classifier's `payloadEnd` with the second offset needs to know that offset is
read at byte 4. `newPayloadRequestFields` puts its three offsets at 0, 4 and 40 — the fixed
`byteVector 32` occupying 8–39 between the second and third — so unlike `entryFields` the table is not
a uniform stride and the reduction cannot come from an arity-free lemma.

This is exactly the mixed-interleaving case the generalise-versus-parallel decision put on the
specialised side, and it is the whole of that side for item 4: one table reduction, no decomposition.

The extra `isFixedSize` facts below are not friction, they are the content: needing
`(byteVector 32).isFixedSize = true` *positively* is precisely what makes the stride non-uniform, so
the lemma is harder to prove for the same reason it cannot be generic. -/

theorem newPayloadRequestFields_not_allFixed :
    SSZType.allFixedSize newPayloadRequestFields = false := by decide

theorem newPayloadRequestFields_takeWhile_fixed :
    SSZType.fixedSectionSizeFields
      (newPayloadRequestFields.takeWhile SSZType.isFixedSize) = 0 := by decide

@[simp] theorem blobCommitmentsField_not_fixed :
    (SSZType.list (BinaryFv.Specs.SSZ.byteVector 32) BinaryFv.Specs.SSZ.maxBlobCommitmentsPerBlock).isFixedSize
      = false := by decide

@[simp] theorem byteVector32_is_fixed :
    (BinaryFv.Specs.SSZ.byteVector 32).isFixedSize = true := by decide

@[simp] theorem byteVector32_fixedByteSize :
    (BinaryFv.Specs.SSZ.byteVector 32).fixedByteSize = 32 := by decide

@[simp] theorem executionRequestsType_not_fixed :
    BinaryFv.Specs.SSZ.executionRequestsType.isFixedSize = false := by decide

theorem extractFieldOffsets_newPayloadRequest (b : ByteArray) :
    extractFieldOffsets b newPayloadRequestFields 0 =
      match readUInt32LE b 0, readUInt32LE b 4, readUInt32LE b 40 with
      | some p0, some p1, some p2 => .ok [p0.toNat, p1.toNat, p2.toNat]
      | _, _, _ => .error .tooShort := by
  simp [newPayloadRequestFields, extractFieldOffsets, BYTES_PER_LENGTH_OFFSET]
  cases readUInt32LE b 0 <;> cases readUInt32LE b 4 <;> cases readUInt32LE b 40 <;> rfl

/-! ### Chaining the request level to the payload level -/

/-- **A canonical `newPayloadRequest` decode forces byte 436 of its payload slice to read 540.**

The middle link: `parts` pins this level's first offset to 44, the table reduction identifies the
second offset with the classifier's `payloadEnd`, the descent hands over the payload slice, and the
sharp end applies there. -/
theorem newPayloadRequest_payload_byte436_eq_540 {request : ByteArray}
    {x : SSZType.interpFields newPayloadRequestFields} {u : Nat}
    (h : SSZType.deserialize (.container newPayloadRequestFields) request = .ok (x, u))
    {pe : Nat} (hpe : BinaryFv.Specs.SSZ.readU32LE? request 4 = some pe) :
    BinaryFv.Specs.SSZ.readU32LE? (request.extract 44 pe) 436 = some 540 := by
  obtain ⟨offs, hext, hhead, hwalk⟩ :=
    deserialize_container_parts newPayloadRequestFields_not_allFixed h
  rw [extractFieldOffsets_newPayloadRequest] at hext
  split at hext
  · rename_i p0 p1 p2 h0 h1 h2
    simp only [Except.ok.injEq] at hext
    subst hext
    simp only [List.head?_cons, Option.some.injEq] at hhead
    rw [newPayloadRequestFields_fixedSection] at hhead
    have hb : BinaryFv.Specs.SSZ.readU32LE? request 4 = some p1.toNat := by
      rw [readU32LE?_eq_map_readUInt32LE, h1]; rfl
    rw [hb, Option.some.injEq] at hpe
    obtain ⟨y, u', hy⟩ := deserializeVarFields_first_field
      (t := BinaryFv.Specs.SSZ.executionPayloadType) executionPayloadType_not_fixed
      p0.toNat p1.toNat _ _ hwalk
    rw [hhead, hpe] at hy
    -- Defeq-not-syntactic: `hy` is at `executionPayloadType`, the sharp end at its field list.
    have hy' : SSZType.deserialize (.container executionPayloadFields) (request.extract 44 pe)
        = .ok (y, u') := hy
    exact executionPayload_byte436_eq_540 hy'
  · exact absurd hext (by simp)

/-! ## The V3 exclusion

The top link, and item 4 closed. A V3-shaped buffer never decodes canonically as V4 — not because
the shapes differ at the offsets the classifier checks first, which they do not, but because the byte
it checks last is forced to a different value by canonicality. -/

/-- **`v3ShapeExcludesCanonicalV4`.** -/
theorem v3ShapeExcludesCanonicalV4_holds : v3ShapeExcludesCanonicalV4 := by
  intro bytes hv3
  obtain ⟨hashes, pe, hschema, hr16, hh, hp44, hpe, h528⟩ := hasV3PayloadShape_parts hv3
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type
      (bytes.extract 2 bytes.size) with
  | error e => simp [Except.toOption]
  | ok v =>
      exfalso
      obtain ⟨hdes, _⟩ := decodeCanonical_inv hdc
      have hdes' : SSZType.deserialize (.container entryFields) (bytes.extract 2 bytes.size)
          = .ok (v, (bytes.extract 2 bytes.size).size) := hdes
      obtain ⟨offs, hext, hhead, hwalk⟩ :=
        deserialize_container_parts entryFields_not_allFixed hdes'
      rw [extractFieldOffsets_entry] at hext
      split at hext
      · rename_i w0 w1 w2 w3 r0 r1 r2 r3
        simp only [Except.ok.injEq] at hext
        subst hext
        simp only [List.head?_cons, Option.some.injEq] at hhead
        rw [entryFields_fixedSectionSize] at hhead
        -- The classifier's `hashesOffset` is the entry table's second offset.
        have hb : BinaryFv.Specs.SSZ.readU32LE? (bytes.extract 2 bytes.size) 4 = some w1.toNat := by
          rw [readU32LE?_eq_map_readUInt32LE, r1]; rfl
        rw [hb, Option.some.injEq] at hh
        obtain ⟨x, u, hx⟩ := deserializeVarFields_first_field
          (t := BinaryFv.Specs.SSZ.newPayloadRequestType) newPayloadRequestType_not_fixed
          w0.toNat w1.toNat _ _ hwalk
        rw [hhead, hh] at hx
        have hx' : SSZType.deserialize (.container newPayloadRequestFields)
            ((bytes.extract 2 bytes.size).extract 16 hashes) = .ok (x, u) := hx
        rw [newPayloadRequest_payload_byte436_eq_540 hx' hpe] at h528
        exact absurd h528 (by decide)
      · exact absurd hext (by simp)

/-! ## The `tooLarge` gate is dead inside the root's scope

`decodeStatelessInput` opens with `size ≥ 2 ^ 32 → tooLarge`, and `decodeRawInput` repeats it. Inside
`rootComplianceScope` — `size < 2 * 1024 * 1024` — neither can fire, because 2 MiB is three orders of
magnitude below 2^32.

This is why the scope hypothesis is on the obligation rather than being an incidental convenience:
`ereGateDivergesAboveU32` exhibits a witness *above* the bound where the two sides genuinely disagree,
so the agreement is true because of the scope, not despite it. Recording the gate as unreachable in
scope is what connects those two facts, which otherwise sit in different files with nothing linking
them.

**The strong form: remove the scope hypothesis and the obligation is FALSE at an exhibited witness**,
not merely unproved. That is the difference between a narrowing a later reader might tidy away and one
that cannot be. It is also the mirror of the not-about-this-layer category — that is a hypothesis which
*looks* discharged and is not; this is one that *looks* incidental and is essential. Both are
signature-versus-content mismatches with opposite signs, which is why the audit has to run in both
directions. -/

theorem tooLarge_gate_unreachable_in_scope {bytes : ByteArray}
    (h : rootComplianceScope bytes) : ¬ (bytes.size ≥ 2 ^ 32) := by
  rw [rootComplianceScope] at h
  omega

/-- `decodeStatelessInput` with the dead gate removed: inside scope it *is* the
raw-or-quarantine path plus the ERE retry. -/
theorem decodeStatelessInput_in_scope {bytes : ByteArray} (h : rootComplianceScope bytes) :
    BinaryFv.Specs.SSZ.decodeStatelessInput bytes =
      match BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3 bytes with
      | .ok value => .ok value
      | .error rawError =>
          match rawError with
          | .v3Quarantined => .error rawError
          | _ =>
              match BinaryFv.Specs.SSZ.readU32LE? bytes 0 with
              | some declaredLength =>
                  if declaredLength == bytes.size - 4 then
                    BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3 (bytes.extract 4 bytes.size)
                  else .error rawError
              | none => .error rawError := by
  rw [BinaryFv.Specs.SSZ.decodeStatelessInput, if_neg (tooLarge_gate_unreachable_in_scope h)]
  -- Same match on both sides, differing motives: reduce the scrutinee on both rather than the left.
  cases BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3 bytes <;> rfl

/-! ## Item 5: the ERE retry arm

The source retries only on `invalidSsz`; the spec retries on any non-quarantine error. So the two
disagree about *whether to retry* exactly when the source's error is `unknownFork` or `outOfMemory`,
and the agreement survives only if the spec's retry then fails.

`outOfMemory` is excluded in scope by `outOfMemoryUnreachableBelowBound`. `unknownFork` is this lemma:
for the source to raise it at all, `meaningForkConfig` must have been reached, which means
`meaningDecodeRaw` got past `hasSchemaId` *and* past `requireCanonicalOffsets`, and that check demands
the first offset equal 16. Those are exactly `retryTailNeverSchemaValid`'s two hypotheses — so the
lemma stated about the *source* retry is what kills the *spec* one. -/

/-- **The spec's ERE retry rejects** whenever the body's first offset is canonical. -/
theorem spec_retry_rejects {bytes : ByteArray}
    (hschema : BinaryFv.Specs.SSZ.hasSchemaId bytes = true)
    (hfirst : BinaryFv.Specs.SSZ.readU32LE? (bytes.extract 2 bytes.size) 0 = some 16) :
    (BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3 (bytes.extract 4 bytes.size)).toOption = none := by
  have htail : BinaryFv.Specs.SSZ.hasSchemaId (bytes.extract 4 bytes.size) = false :=
    retryTailNeverSchemaValid_holds bytes hschema hfirst
  rw [BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3]
  split
  · rfl
  · rw [BinaryFv.Specs.SSZ.decodeRawInput]
    split
    · rfl
    · split
      · rfl
      · rw [if_pos (by simp [htail])]
        rfl

/-! ## Envelope alignment at the raw level

Before the four-field content can be used, the two entry points' *envelope* checks have to be matched.
The source runs `requireU32Length`, then `size < 2`, then `hasSchemaId`, then `body.size < 16`. The
spec runs `size ≥ 2 ^ 32`, then `size < 2`, then `hasSchemaId`, then hands the body to
`decodeCanonical`, whose container arm rejects when the body is shorter than the sixteen-byte prefix.

Inside scope the first check on each side is dead — `requireU32Length` always succeeds and the
`tooLarge` gate never fires — so the two envelopes reduce to the same three tests in the same order.
The differing error constructors do not matter: the obligation compares acceptance. -/

/-- The source's `requireU32Length` is free inside the root's scope. -/
theorem meaningRequireU32Length_ok_in_scope {bytes : ByteArray} (h : rootComplianceScope bytes) :
    meaningRequireU32Length bytes = .ok () := by
  rw [rootComplianceScope] at h
  rw [meaningRequireU32Length, if_pos (by omega)]

/-- Both `tooLarge`-class gates are dead in scope: the spec's `2 ^ 32` test and the source's
`requireU32Length` are the same bound seen from the two sides, and neither fires below 2 MiB. -/
theorem both_size_gates_dead_in_scope {bytes : ByteArray} (h : rootComplianceScope bytes) :
    meaningRequireU32Length bytes = .ok () ∧ ¬ (bytes.size ≥ 2 ^ 32) :=
  ⟨meaningRequireU32Length_ok_in_scope h, tooLarge_gate_unreachable_in_scope h⟩

/-- `decodeRawInput` with its dead `tooLarge` gate removed — the spec-side reduction at the raw level,
the analogue of `decodeStatelessInput_in_scope` one layer up. What is left is exactly the three
envelope tests the source also runs, then the canonical decode, then the fork bound. -/
theorem decodeRawInput_in_scope {bytes : ByteArray} (h : rootComplianceScope bytes) :
    BinaryFv.Specs.SSZ.decodeRawInput bytes =
      (if bytes.size < 2 then .error .tooShort
        else if !(BinaryFv.Specs.SSZ.hasSchemaId bytes) then .error .badSchema
        else
          match BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type
              (bytes.extract 2 bytes.size) with
          | .ok value =>
              if (BinaryFv.Specs.SSZ.statelessInputOfInterp value).chainConfig.activeFork.fork > 20 then
                .error .unknownFork
              else .ok (BinaryFv.Specs.SSZ.statelessInputOfInterp value)
          | .error error => .error (.ssz error)) := by
  rw [BinaryFv.Specs.SSZ.decodeRawInput, if_neg (tooLarge_gate_unreachable_in_scope h)]
  split
  · rfl
  · split
    · rfl
    · cases BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type (bytes.extract 2 bytes.size) <;>
        rfl

/-! ### The fork bound, matched across the layer boundary

The source checks `fork > 20` *inside* `meaningChainConfig`; the spec checks it in `decodeRawInput`,
after a complete canonical decode of the whole body. These two lemmas move the bound across the layer boundary.

**Nothing here is discharged, and the wording matters.** `sourceShapedContainersAgreeWithSpec`
already states the `fork ≤ 20` bound in the spec's terms — the bound is written into the obligation
at `Containers.lean:365`. So `chainConfig_acceptance_is_fork_bound` is that *assumed* fact specialised
to its accepting branch, and the only new content in the pair is `statelessInput_fork_eq_field_fork`, which is
`rfl`. What these lemmas do is move a supplied bound to the layer that consumes it; they do not prove
the two checks agree. A reader must not mistake this for the match having been established. -/

theorem chainConfig_acceptance_is_fork_bound
    (containersAgree : sourceShapedContainersAgreeWithSpec)
    {slice : ByteArray} {value : BinaryFv.Specs.SSZ.chainConfigType.interp}
    (hdec : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType slice = .ok value) :
    isAccepted (meaningChainConfig slice)
      = decide ((BinaryFv.Specs.SSZ.rawChainConfigOf value).activeFork.fork ≤ 20) := by
  rw [containersAgree slice, hdec]

/-- The same bound, stated against the whole-body value the spec actually reads it from. -/
theorem chainConfig_acceptance_is_statelessInput_fork_bound
    (containersAgree : sourceShapedContainersAgreeWithSpec)
    {slice : ByteArray} {v : BinaryFv.Specs.SSZ.statelessInputV4Type.interp}
    (hdec : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType slice = .ok v.2.2.1) :
    isAccepted (meaningChainConfig slice)
      = decide ((BinaryFv.Specs.SSZ.statelessInputOfInterp v).chainConfig.activeFork.fork ≤ 20) := by
  rw [chainConfig_acceptance_is_fork_bound containersAgree hdec, statelessInput_fork_eq_field_fork]

/-- **The source side at the raw level, with its length check eliminated.**

In scope `requireU32Length` always succeeds, so `meaningDecodeRaw` is its own body: three envelope
tests, four offset reads, the canonical-offsets check, then the four field meanings.

The right-hand side is a transcription of the definition, which is why the equation is worth stating
even though it looks like a restatement — if it were mistranscribed the equation would not hold, so
the compiler is the check on it, the same guard `executionPayloadType_eq` gives the field list.

Supplied-versus-proved, per the standing rule: nothing here comes from an assumption. Every conjunct
is the definition, and the only input is the scope hypothesis, which kills the first bind. -/
theorem meaningDecodeRaw_in_scope {bytes : ByteArray} (h : rootComplianceScope bytes) :
    meaningDecodeRaw bytes =
      (if bytes.size < 2 then .error .invalidSsz
        else if !(BinaryFv.Specs.SSZ.hasSchemaId bytes) then .error .invalidSsz
        else
          let body := bytes.extract 2 bytes.size
          if body.size < 16 then .error .invalidSsz
          else do
            let zeroth ← meaningReadOffset body 0
            let first ← meaningReadOffset body 4
            let second ← meaningReadOffset body 8
            let third ← meaningReadOffset body 12
            let _ ← meaningRequireCanonicalOffsets body 16 [zeroth, first, second, third]
            let newPayloadRequest ← meaningNewPayloadRequest (body.extract zeroth first)
            let witness ← meaningExecutionWitness (body.extract first second)
            let chainConfig ← meaningChainConfig (body.extract second third)
            let publicKeys ← meaningPublicKeys (body.extract third body.size)
            return {
              newPayloadRequest := newPayloadRequest
              witness := witness
              chainConfig := chainConfig
              publicKeys := publicKeys
            }) := by
  rw [meaningDecodeRaw, meaningRequireU32Length_ok_in_scope h]
  rfl

/-! ### The envelope cases, disposed of on both sides at once

With both entry points reduced, the first two tests are literally the same conditions in the same
order — `size < 2` then `hasSchemaId` — differing only in which error they raise. Since the obligation
compares acceptance, a single lemma retires those cases for both directions, leaving the raw-level
intermediate to reason only about bodies that pass the envelope.

Supplied-versus-proved: nothing here is assumed. Both sides come from their definitions and the scope
hypothesis. -/

theorem raw_envelope_rejects_both {bytes : ByteArray} (h : rootComplianceScope bytes)
    (henv : bytes.size < 2 ∨ BinaryFv.Specs.SSZ.hasSchemaId bytes = false) :
    isAccepted (meaningDecodeRaw bytes) = false ∧
      (BinaryFv.Specs.SSZ.decodeRawInput bytes).toOption.isSome = false := by
  rw [meaningDecodeRaw_in_scope h, decodeRawInput_in_scope h]
  by_cases hsize : bytes.size < 2
  · rw [if_pos hsize, if_pos hsize]
    exact ⟨rfl, rfl⟩
  · rcases henv with h2 | hschema
    · exact absurd h2 hsize
    · rw [if_neg hsize, if_neg hsize, if_pos (by simp [hschema]), if_pos (by simp [hschema])]
      exact ⟨rfl, rfl⟩

/-! ### Bodies too short for the offset table

The source tests `body.size < 16` explicitly. The spec has no such test: sixteen is the container
arm's `b.size < prefixSize` guard, and `prefixSize` is `fixedSectionSizeFields entryFields`, *derived*
from the schema rather than written down. So the two sides reach the same number by different routes,
and `entryFields_fixedSectionSize` being a `decide` rather than a numeral is what makes the agreement
a check instead of a coincidence. -/

theorem decodeCanonical_entry_short {body : ByteArray} (h : body.size < 16) :
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body = .error .tooShort := by
  have hdes : SSZType.deserialize BinaryFv.Specs.SSZ.statelessInputV4Type body = .error .tooShort := by
    show SSZType.deserialize (.container entryFields) body = _
    rw [SSZType.deserialize, if_neg (by rw [entryFields_not_allFixed]; simp)]
    simp only []
    rw [if_pos (by rw [entryFields_fixedSectionSize]; omega)]
  rw [BinaryFv.Specs.SSZ.decodeCanonical, hdes]
  rfl

/-- Above sixteen bytes all four table reads succeed, so the table always *exists*. This is what lets
the body-passing case name `o0 … o3` before knowing anything about them. -/
theorem readUInt32LE_exists (bytes : ByteArray) (offset : Nat) (fits : offset + 4 ≤ bytes.size) :
    ∃ w, readUInt32LE bytes offset = some w := by
  rw [readUInt32LE, dif_pos fits]
  exact ⟨_, rfl⟩

theorem entry_offsets_of_sixteen (body : ByteArray) (h : 16 ≤ body.size) :
    ∃ o0 o1 o2 o3, extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3] := by
  obtain ⟨w0, e0⟩ := readUInt32LE_exists body 0 (by omega)
  obtain ⟨w1, e1⟩ := readUInt32LE_exists body 4 (by omega)
  obtain ⟨w2, e2⟩ := readUInt32LE_exists body 8 (by omega)
  obtain ⟨w3, e3⟩ := readUInt32LE_exists body 12 (by omega)
  exact ⟨w0.toNat, w1.toNat, w2.toNat, w3.toNat, by
    rw [extractFieldOffsets_entry, e0, e1, e2, e3]⟩

/-! ### The spec's offset discipline, recovered from a successful walk

The source rejects a non-canonical table with `requireCanonicalOffsets`, one explicit check. The
spec has no such check: its discipline is spread across the container arm's first-offset test and
`deserializeVarFields`' per-field `curOff > nextOff || nextOff > bufEnd` guard. To match a *rejection*
the argument therefore has to run backwards — from a successful walk to the inequalities it must have
passed — which is why this is stated as soundness of the walk rather than as a rejection lemma.

Stated over an arbitrary head field rather than four times at the entry's concrete fields: the guard
is per-field and identical each time, so one arity-free step iterated three times covers the table.
Three, not four — the third application already reads `o3 ≤ body.size` off the last offset's sentinel,
so the fourth field's guard adds nothing. -/

theorem deserializeVarFields_var_guard {t : SSZType} {ts : List SSZType} {b : ByteArray}
    {prefixOff curOff : Nat} {restOffs : List Nat} {bufEnd : Nat}
    (hvar : t.isFixedSize = false)
    {v : SSZType.interpFields (t :: ts)}
    (h : SSZType.deserializeVarFields (t :: ts) b prefixOff (curOff :: restOffs) bufEnd = .ok v) :
    curOff ≤ restOffs.head?.getD bufEnd ∧ restOffs.head?.getD bufEnd ≤ bufEnd ∧
      ∃ v', SSZType.deserializeVarFields ts b (prefixOff + BYTES_PER_LENGTH_OFFSET) restOffs bufEnd
        = .ok v' := by
  rw [SSZType.deserializeVarFields, if_neg (by simp [hvar])] at h
  -- Zeta-reduce `let nextOff := …` so `split` reaches the guard.
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hguard
    have hle : curOff ≤ restOffs.head?.getD bufEnd ∧ restOffs.head?.getD bufEnd ≤ bufEnd := by
      by_cases hc : curOff > restOffs.head?.getD bufEnd
      · simp [hc] at hguard
      · by_cases hd : restOffs.head?.getD bufEnd > bufEnd
        · simp [hd] at hguard
        · omega
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · rename_i hrec
        exact ⟨hle.1, hle.2, _, hrec⟩

/-- **A successful entry walk forces the source's monotonicity conjuncts.** -/
theorem deserializeVarFields_entry_offsets_sound {body : ByteArray} {o0 o1 o2 o3 : Nat}
    {v : SSZType.interpFields entryFields}
    (h : SSZType.deserializeVarFields entryFields body 0 [o0, o1, o2, o3] body.size = .ok v) :
    o0 ≤ o1 ∧ o1 ≤ o2 ∧ o2 ≤ o3 ∧ o3 ≤ body.size := by
  -- `entryFields` is the cons literal the guard lemma is stated at; defeq, so a restatement crosses.
  have h0 : SSZType.deserializeVarFields
      (BinaryFv.Specs.SSZ.newPayloadRequestType :: BinaryFv.Specs.SSZ.witnessType :: BinaryFv.Specs.SSZ.chainConfigType ::
        [.list (BinaryFv.Specs.SSZ.byteVector BinaryFv.Specs.SSZ.publicKeyBytes) BinaryFv.Specs.SSZ.maxPublicKeys])
      body 0 [o0, o1, o2, o3] body.size = .ok v := h
  obtain ⟨a01, -, v1, h1⟩ := deserializeVarFields_var_guard newPayloadRequestType_not_fixed h0
  simp only [List.head?_cons, Option.getD_some] at a01
  obtain ⟨a12, -, v2, h2⟩ := deserializeVarFields_var_guard witnessType_not_fixed h1
  simp only [List.head?_cons, Option.getD_some] at a12
  obtain ⟨a23, a3, -, -⟩ := deserializeVarFields_var_guard chainConfigType_not_fixed h2
  simp only [List.head?_cons, Option.getD_some] at a23 a3
  exact ⟨a01, a12, a23, a3⟩

/-- **The spec rejects exactly the tables `requireCanonicalOffsets` rejects.**

The `16 ≤ body.size` conjunct of the source's check is absent from the hypothesis because a successful
table read already forces it (`extractFieldOffsets_entry_fits`) — the fifth already-implied hypothesis
in this module, found by the same audit rather than by noticing it. -/
theorem decodeCanonical_entry_rejects_noncanonical (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3])
    (hbad : ¬ (o0 = 16 ∧ o0 ≤ o1 ∧ o1 ≤ o2 ∧ o2 ≤ o3 ∧ o3 ≤ body.size)) :
    (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body).toOption.isSome = false := by
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body with
  | error e => rfl
  | ok v =>
      exfalso
      obtain ⟨hdes, -⟩ := decodeCanonical_inv hdc
      have hdes' : SSZType.deserialize (.container entryFields) body = .ok (v, body.size) := hdes
      obtain ⟨offs, hext, hhead, hwalk⟩ :=
        deserialize_container_parts entryFields_not_allFixed hdes'
      rw [hoffs] at hext
      have hoff : [o0, o1, o2, o3] = offs := by injection hext
      subst hoff
      rw [entryFields_fixedSectionSize, List.head?_cons, Option.some.injEq] at hhead
      exact hbad ⟨hhead, deserializeVarFields_entry_offsets_sound hwalk⟩

/-! ## The raw-level intermediate

`meaningDecodeRaw` against `decodeRawInput`, at acceptance granularity, inside the root's scope. This is
the lower half of `sourceShapedDecodeAgreesWithSpec`: everything above this point is machinery, and
everything below the outer assembly's two retry arms consumes it.

The two sides are *not* the same shape, and the whole difficulty is in the three places they differ.

* **The sixteen-byte test.** The source tests `body.size < 16` explicitly; the spec reaches the same
  number as `fixedSectionSizeFields entryFields` inside the container arm.
* **The offset discipline.** The source has one check, `requireCanonicalOffsets`. The spec spreads it
  across the container arm's first-offset equality and `deserializeVarFields`' per-field guard, so
  matching a *rejection* runs backwards — from a successful walk to the inequalities it must have
  passed.
* **The fork bound.** The source applies it inside `meaningChainConfig`, before decoding children; the
  spec applies it in `decodeRawInput`, after a complete canonical decode. This is the one place an
  assumption enters: `sourceShapedContainersAgreeWithSpec` is what carries the bound, and it is
  consumed here through `containersAgree`.

**Supplied versus proved.** `containersAgree` is a hypothesis, so the fork-bound half of the agreement
is *assumed*, not established. Everything else — both envelopes, the sixteen-byte test, the offset
table, the four field slices, and the four-field composition — is proved. A reader must not read the
theorem as discharging the container obligation; it consumes it. -/

/-- Reducing a `>>=` whose left argument is already `.ok`. Stated rather than unfolding `bind`, because
unfolding turns the remaining `do` block into raw `Except.bind` matches and then no `do`-shaped lemma
matches it any more. -/
theorem except_bind_ok {α β : Type} (a : α) (f : α → Except DecodeError β) :
    (Except.ok a : Except DecodeError α) >>= f = f a := rfl

/-- The four field meanings join by conjunction: the decoded values feed only the returned record, so
acceptance of the whole depends on the four fields' acceptance alone. -/
theorem isAccepted_entry_join (s0 s1 s2 s3 : ByteArray) :
    isAccepted (do
        let newPayloadRequest ← meaningNewPayloadRequest s0
        let witness ← meaningExecutionWitness s1
        let chainConfig ← meaningChainConfig s2
        let publicKeys ← meaningPublicKeys s3
        return ({ newPayloadRequest := newPayloadRequest
                  witness := witness
                  chainConfig := chainConfig
                  publicKeys := publicKeys } : BinaryFv.Specs.SSZ.StatelessInput))
      = (isAccepted (meaningNewPayloadRequest s0) && isAccepted (meaningExecutionWitness s1) &&
          isAccepted (meaningChainConfig s2) && isAccepted (meaningPublicKeys s3)) := by
  cases meaningNewPayloadRequest s0 <;> cases meaningExecutionWitness s1 <;>
    cases meaningChainConfig s2 <;> cases meaningPublicKeys s3 <;> rfl

/-- One failing field decode kills the whole entry decode, so the spec's post-decode fork test never
runs. The `chainConfig` disjunct is included even though its *meaning* can reject a body the spec's
field decode accepts (`fork > 20`): that case is not this lemma's, and is handled by the fork bound. -/
theorem entry_forkGuard_false (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size)
    (hu32 : body.size < UInt32.size)
    (hbad :
      (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.newPayloadRequestType
          (body.extract o0 o1)).toOption.isSome = false ∨
      (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.witnessType (body.extract o1 o2)).toOption.isSome
          = false ∨
      (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType (body.extract o2 o3)).toOption.isSome
          = false ∨
      (BinaryFv.Specs.SSZ.decodeCanonical publicKeysType (body.extract o3 body.size)).toOption.isSome
          = false) :
    (match BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body with
      | .ok value => decide ((BinaryFv.Specs.SSZ.statelessInputOfInterp value).chainConfig.activeFork.fork ≤ 20)
      | .error _ => false) = false := by
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body with
  | error e => rfl
  | ok v =>
      obtain ⟨p0, p1, p2, p3⟩ :=
        decodeCanonical_entry_fields_of body o0 o1 o2 o3 hoffs h0 h01 h12 h23 h3 hu32
          (by rw [hdc]; rfl)
      rcases hbad with hb | hb | hb | hb
      · rw [p0] at hb; exact absurd hb (by simp)
      · rw [p1] at hb; exact absurd hb (by simp)
      · rw [p2] at hb; exact absurd hb (by simp)
      · rw [p3] at hb; exact absurd hb (by simp)

/-- **The body-passing case of the raw-level intermediate.**

Stated about the body alone, with the spec side written as the fork-bounded acceptance of the whole
container rather than as `decodeRawInput`'s `Result`. That keeps the spec's error taxonomy out of a
statement whose whole point is that acceptance agrees while the taxonomies do not.

Both halves of the statement have been shown load-bearing by must-fail probes: replacing the RHS's
`fork ≤ 20` with `true` breaks the proof, and moving the source's threshold from sixteen to twelve
breaks it too. Neither probe is kept — a check that must fail cannot also be a regression guard. -/
theorem raw_body_agrees (containersAgree : sourceShapedContainersAgreeWithSpec)
    (body : ByteArray) (hu32 : body.size < UInt32.size) :
    isAccepted
        (if body.size < 16 then (.error .invalidSsz : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput)
          else do
            let zeroth ← meaningReadOffset body 0
            let first ← meaningReadOffset body 4
            let second ← meaningReadOffset body 8
            let third ← meaningReadOffset body 12
            let _ ← meaningRequireCanonicalOffsets body 16 [zeroth, first, second, third]
            let newPayloadRequest ← meaningNewPayloadRequest (body.extract zeroth first)
            let witness ← meaningExecutionWitness (body.extract first second)
            let chainConfig ← meaningChainConfig (body.extract second third)
            let publicKeys ← meaningPublicKeys (body.extract third body.size)
            return {
              newPayloadRequest := newPayloadRequest
              witness := witness
              chainConfig := chainConfig
              publicKeys := publicKeys
            })
      = (match BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body with
          | .ok value => decide ((BinaryFv.Specs.SSZ.statelessInputOfInterp value).chainConfig.activeFork.fork ≤ 20)
          | .error _ => false) := by
  by_cases h16 : body.size < 16
  · rw [if_pos h16, decodeCanonical_entry_short h16]
    rfl
  rw [if_neg h16]
  obtain ⟨o0, o1, o2, o3, hoffs⟩ := entry_offsets_of_sixteen body (by omega)
  obtain ⟨r0, r1, r2, r3⟩ := (extractFieldOffsets_eq_meaningReads body o0 o1 o2 o3).mp hoffs
  simp only [r0, r1, r2, r3, except_bind_ok]
  by_cases hcan : meaningRequireCanonicalOffsets body 16 [o0, o1, o2, o3] = .ok ()
  · obtain ⟨-, hc0, hc01, hc12, hc23, hc3⟩ :=
      (requireCanonicalOffsets_entry body o0 o1 o2 o3).mp hcan
    rw [hcan, except_bind_ok, isAccepted_entry_join, meaningNewPayloadRequest_accepted,
      meaningExecutionWitness_accepted, meaningPublicKeys_accepted, containersAgree]
    cases hd0 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.newPayloadRequestType (body.extract o0 o1) with
    | error e0 =>
        rw [entry_forkGuard_false body o0 o1 o2 o3 hoffs hc0 hc01 hc12 hc23 hc3 hu32
          (.inl (by rw [hd0]; rfl))]
        rfl
    | ok x0 =>
      cases hd1 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.witnessType (body.extract o1 o2) with
      | error e1 =>
          rw [entry_forkGuard_false body o0 o1 o2 o3 hoffs hc0 hc01 hc12 hc23 hc3 hu32
            (.inr (.inl (by rw [hd1]; rfl)))]
          rfl
      | ok x1 =>
        cases hd2 : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType (body.extract o2 o3) with
        | error e2 =>
            rw [entry_forkGuard_false body o0 o1 o2 o3 hoffs hc0 hc01 hc12 hc23 hc3 hu32
              (.inr (.inr (.inl (by rw [hd2]; rfl))))]
            rfl
        | ok x2 =>
          cases hd3 : BinaryFv.Specs.SSZ.decodeCanonical publicKeysType (body.extract o3 body.size) with
          | error e3 =>
              rw [entry_forkGuard_false body o0 o1 o2 o3 hoffs hc0 hc01 hc12 hc23 hc3 hu32
                (.inr (.inr (.inr (by rw [hd3]; rfl))))]
              -- Only the *last* conjunct fails to short-circuit, which is why the three branches
              -- above close by `rfl` and this one needs `Bool.and_false`.
              simp [Except.toOption]
          | ok x3 =>
              rw [decodeCanonical_entry_eq_of_fields body o0 o1 o2 o3 hoffs hc0 hc01 hc12 hc23 hc3
                hu32 hd0 hd1 hd2 hd3]
              simp [statelessInput_fork_eq_field_fork, Except.toOption]
  · -- The source's offset check fails; the spec's spread-out discipline has to reject too.
    have herr : ∃ e, meaningRequireCanonicalOffsets body 16 [o0, o1, o2, o3] = .error e := by
      cases hc : meaningRequireCanonicalOffsets body 16 [o0, o1, o2, o3] with
      | error e => exact ⟨e, rfl⟩
      | ok u => exact absurd (by rw [hc]) hcan
    obtain ⟨e, he⟩ := herr
    rw [he]
    have hbad : ¬ (o0 = 16 ∧ o0 ≤ o1 ∧ o1 ≤ o2 ∧ o2 ≤ o3 ∧ o3 ≤ body.size) := by
      intro hgood
      exact hcan ((requireCanonicalOffsets_entry body o0 o1 o2 o3).mpr
        ⟨extractFieldOffsets_entry_fits body o0 o1 o2 o3 hoffs, hgood.1, hgood.2.1, hgood.2.2.1,
          hgood.2.2.2.1, hgood.2.2.2.2⟩)
    cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type body with
    | error e' => rfl
    | ok v =>
        have hrej := decodeCanonical_entry_rejects_noncanonical body o0 o1 o2 o3 hoffs hbad
        rw [hdc] at hrej
        exact absurd hrej (by simp [Except.toOption])

/-- **The raw-level intermediate.** `meaningDecodeRaw` and `decodeRawInput` accept the same buffers inside
the root's scope, given the container obligation.

The scope hypothesis is load-bearing in the strong sense recorded above: `ereGateDivergesAboveU32`
exhibits a witness beyond the bound where the two genuinely disagree, so this is not a narrowing a
later reader can tidy away. -/
theorem raw_acceptance_agrees (containersAgree : sourceShapedContainersAgreeWithSpec)
    {bytes : ByteArray} (h : rootComplianceScope bytes) :
    isAccepted (meaningDecodeRaw bytes) = (BinaryFv.Specs.SSZ.decodeRawInput bytes).toOption.isSome := by
  have hscope : bytes.size < 2 * 1024 * 1024 := h
  have hu32 : (bytes.extract 2 bytes.size).size < UInt32.size := by
    have husz : UInt32.size = 4294967296 := rfl
    rw [ByteArray.size_extract, husz]
    omega
  have hb := raw_body_agrees containersAgree (bytes.extract 2 bytes.size) hu32
  rw [meaningDecodeRaw_in_scope h, decodeRawInput_in_scope h]
  by_cases hsize : bytes.size < 2
  · rw [if_pos hsize, if_pos hsize]; rfl
  by_cases hschema : BinaryFv.Specs.SSZ.hasSchemaId bytes = false
  · have hschemaT : (!BinaryFv.Specs.SSZ.hasSchemaId bytes) = true := by simp [hschema]
    rw [if_neg hsize, if_neg hsize, if_pos hschemaT, if_pos hschemaT]
    rfl
  -- The condition must be pinned by a named hypothesis: with `if_neg (by simp …)` the `c`
  -- metavariable is solved from whichever `ite` the traversal reaches first, which here is the
  -- source's *inner* `body.size < 16` rather than the spec's schema test.
  have hschema' : ¬ ((!BinaryFv.Specs.SSZ.hasSchemaId bytes) = true) := by simp [hschema]
  rw [if_neg hsize, if_neg hsize, if_neg hschema', if_neg hschema']
  simp only []
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type
      (bytes.extract 2 bytes.size) with
  | error e =>
      rw [hdc] at hb
      rw [hb]
      rfl
  | ok v =>
      rw [hdc] at hb
      rw [hb]
      -- Both sides still show `match Except.ok v with …`; iota-reduce so the fork test is reachable.
      simp only []
      by_cases hf : (BinaryFv.Specs.SSZ.statelessInputOfInterp v).chainConfig.activeFork.fork > 20
      -- `fork : UInt64`, so `omega` cannot see this comparison at all.
      · rw [if_pos hf]
        simp only [Except.toOption, Option.isSome_none, decide_eq_false_iff_not]
        exact UInt64.not_le.mpr hf
      · rw [if_neg hf]
        simp only [Except.toOption, Option.isSome_some, decide_eq_true_eq]
        exact UInt64.not_lt.mp hf

/-! ## The outer assembly: the two retry arms

`meaningDecode` against `decodeStatelessInput`. The raw-level intermediate above matches the two
decoders; what is left is that the two *retry* behaviours agree on acceptance despite being triggered
differently, and that is genuinely three separate arguments rather than one.

* **The V3-quarantine arm** (below). The spec does not retry at all on `v3Quarantined`; the source
  does retry if its error was `invalidSsz`. The gap is closed from the *source* side, by
  `retryTailNeverSchemaValid`.
* **The `unknownFork` / `outOfMemory` arm** (still open). Here it is the other way round: the spec
  retries and the source does not, so the spec's retry has to fail. `spec_retry_rejects` is the
  lemma, and `outOfMemoryUnreachableBelowBound` covers the second constructor.
* **The both-retry arm** (still open). Needs `meaningHasExactErePrefix` and the spec's length test
  to be the same condition, then the intermediate applied a second time at the stripped tail.

Recording which direction each asymmetry runs matters, because the reflex is to assume one lemma
covers "the retries differ" and it does not: the two arms need opposite facts, and the first is about
the source's retry while the second is about the spec's. -/

theorem hasSchemaId_size {bytes : ByteArray} (h : BinaryFv.Specs.SSZ.hasSchemaId bytes = true) :
    2 ≤ bytes.size := by
  rw [BinaryFv.Specs.SSZ.hasSchemaId] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- The source's outer entry point rejects whenever the raw decode and its ERE retry both reject.
The retry condition is not examined: whichever way it goes the result is a rejection, which is what
lets the two retry *triggers* differ without acceptance differing. -/
theorem meaningDecode_rejects_of {bytes : ByteArray}
    (hraw : isAccepted (meaningDecodeRaw bytes) = false)
    (hretry : isAccepted (meaningDecodeRaw (bytes.extract 4 bytes.size)) = false) :
    isAccepted (meaningDecode bytes) = false := by
  rw [meaningDecode]
  cases hr : meaningDecodeRaw bytes with
  | ok v => rw [hr] at hraw; exact absurd hraw (by simp [isAccepted])
  | error e =>
      cases e with
      | invalidSsz =>
          by_cases hp : meaningHasExactErePrefix bytes = true
          · rw [if_pos hp]; exact hretry
          · rw [if_neg hp]; rfl
      | unknownFork => rfl
      | outOfMemory => rfl

/-- The spec quarantines a V3-shaped buffer and never reaches its ERE retry. -/
theorem decodeStatelessInput_quarantines {bytes : ByteArray} (h : rootComplianceScope bytes)
    (hv3 : BinaryFv.Specs.SSZ.hasV3PayloadShape bytes = true) :
    (BinaryFv.Specs.SSZ.decodeStatelessInput bytes).toOption.isSome = false := by
  rw [decodeStatelessInput_in_scope h, BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3, if_pos hv3]
  rfl

/-- The source's raw decode rejects a V3-shaped buffer, via the proved exclusion. -/
theorem meaningDecodeRaw_rejects_of_v3
    (containersAgree : sourceShapedContainersAgreeWithSpec)
    {bytes : ByteArray} (h : rootComplianceScope bytes)
    (hv3 : BinaryFv.Specs.SSZ.hasV3PayloadShape bytes = true) :
    isAccepted (meaningDecodeRaw bytes) = false := by
  obtain ⟨hashes, pe, hschema, hr16, _, _, _, _⟩ := hasV3PayloadShape_parts hv3
  have hsize : ¬ (bytes.size < 2) := by have := hasSchemaId_size hschema; omega
  have hnot : ¬ ((!BinaryFv.Specs.SSZ.hasSchemaId bytes) = true) := by simp [hschema]
  rw [raw_acceptance_agrees containersAgree h, decodeRawInput_in_scope h, if_neg hsize, if_neg hnot]
  have hexcl := v3ShapeExcludesCanonicalV4_holds bytes hv3
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type
      (bytes.extract 2 bytes.size) with
  | error e => rfl
  | ok v => rw [hdc] at hexcl; exact absurd hexcl (by simp [Except.toOption])

/-- **The V3-quarantine arm.** Both sides reject, and for genuinely different reasons: the spec
because it quarantines before decoding, the source because the exclusion makes its canonical decode
fail and `retryTailNeverSchemaValid` then kills its retry.

The asymmetry is real and is why this arm needs its own proof: the spec **does not retry at all** on
`v3Quarantined`, while the source *does* retry if its error was `invalidSsz`. Acceptance still agrees
because the source's retry cannot succeed — a V3-shaped buffer satisfies exactly the two hypotheses of
`retryTailNeverSchemaValid`, so the four-byte-stripped tail fails `hasSchemaId`. So the lemma stated
about the *source's* retry is what closes a gap created by the *spec's* refusal to retry. -/
theorem v3_arm_rejects_both
    (containersAgree : sourceShapedContainersAgreeWithSpec)
    (retryTail : retryTailNeverSchemaValid)
    {bytes : ByteArray} (h : rootComplianceScope bytes)
    (hv3 : BinaryFv.Specs.SSZ.hasV3PayloadShape bytes = true) :
    isAccepted (meaningDecode bytes) = false ∧
      (BinaryFv.Specs.SSZ.decodeStatelessInput bytes).toOption.isSome = false := by
  obtain ⟨hashes, pe, hschema, hr16, _, _, _, _⟩ := hasV3PayloadShape_parts hv3
  refine ⟨meaningDecode_rejects_of
    (meaningDecodeRaw_rejects_of_v3 containersAgree h hv3) ?_,
    decodeStatelessInput_quarantines h hv3⟩
  -- The retry: the stripped tail fails `hasSchemaId`, so the envelope rejects it.
  have htail : BinaryFv.Specs.SSZ.hasSchemaId (bytes.extract 4 bytes.size) = false :=
    retryTail bytes hschema hr16
  have hscope : rootComplianceScope (bytes.extract 4 bytes.size) := by
    have hb : bytes.size < 2 * 1024 * 1024 := h
    rw [rootComplianceScope, ByteArray.size_extract]
    omega
  exact (raw_envelope_rejects_both hscope (.inr htail)).1

/-- **The quarantine wrapper, matched.** The two arms above combine into one statement about the
function `decodeStatelessInput` actually calls, which is what the outer assembly consumes twice —
once for the first attempt and once for the ERE retry. -/
theorem rawOrQuarantine_acceptance_agrees
    (containersAgree : sourceShapedContainersAgreeWithSpec)
    {bytes : ByteArray} (h : rootComplianceScope bytes) :
    isAccepted (meaningDecodeRaw bytes)
      = (BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3 bytes).toOption.isSome := by
  rw [BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3]
  by_cases hv3 : BinaryFv.Specs.SSZ.hasV3PayloadShape bytes = true
  · rw [if_pos hv3, meaningDecodeRaw_rejects_of_v3 containersAgree h hv3]
    rfl
  · rw [if_neg hv3]
    exact raw_acceptance_agrees containersAgree h

/-- `decodeRawInput` never raises `v3Quarantined`: that constructor belongs to the wrapper, not to the
V4 decoder. Needed so that seeing `v3Quarantined` at the top level identifies the V3 arm rather than
leaving it as one more error to reason about. -/
theorem decodeRawInput_ne_quarantined {bytes : ByteArray} (h : rootComplianceScope bytes) :
    BinaryFv.Specs.SSZ.decodeRawInput bytes ≠ .error .v3Quarantined := by
  rw [decodeRawInput_in_scope h]
  split
  · simp
  · split
    · simp
    · cases BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type
          (bytes.extract 2 bytes.size) with
      | error e => simp
      | ok v =>
          -- Iota-reduce `match Except.ok v with …` so the fork test is reachable.
          simp only []
          by_cases hf : (BinaryFv.Specs.SSZ.statelessInputOfInterp v).chainConfig.activeFork.fork > 20
          · rw [if_pos hf]; simp
          · rw [if_neg hf]; simp

theorem quarantined_of_rawOrQuarantine {bytes : ByteArray} (hs : rootComplianceScope bytes)
    (h : BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3 bytes = .error .v3Quarantined) :
    BinaryFv.Specs.SSZ.hasV3PayloadShape bytes = true := by
  rw [BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3] at h
  split at h
  · assumption
  · exact absurd h (decodeRawInput_ne_quarantined hs)

/-! ### Arm 3's condition, and arm 2's groundwork

Arm 3 turned out to be transcription rather than content, which was the prediction recorded before
checking it: the source tests `size >= 4 && declared == size - 4` and the spec tests only
`declared == size - 4`, and the extra conjunct is already implied by `readU32LE?` returning `some`.
Recorded as a confirmed prediction rather than silently, because a predicted-easy step is where this
proof was previously expected to be easy and was not.

Arm 2 needs the opposite kind of fact, and the lemmas below are what make `unknownFork` *locate its own
cause*: every step of `meaningDecodeRaw` before the four field decodes fails only with `invalidSsz`,
and so do the three field meanings defined directly from the specification, because `sszToDecodeError` is the constant function.
So an `unknownFork` can only have come from `meaningChainConfig`, which pins how far the decode got —
and that is exactly what supplies `spec_retry_rejects`' two hypotheses. -/

/-- A successful `readU32LE?` at offset 0 already forces four bytes. -/
theorem readU32LE?_fits {bytes : ByteArray} {d : Nat}
    (h : BinaryFv.Specs.SSZ.readU32LE? bytes 0 = some d) : 4 ≤ bytes.size := by
  rw [BinaryFv.Specs.SSZ.readU32LE?] at h
  split at h
  · exact absurd h (by simp)
  · omega

/-- **The two retry conditions are the same condition.** -/
theorem meaningHasExactErePrefix_eq (bytes : ByteArray) {d : Nat}
    (hd : BinaryFv.Specs.SSZ.readU32LE? bytes 0 = some d) :
    meaningHasExactErePrefix bytes = (d == bytes.size - 4) := by
  rw [meaningHasExactErePrefix, hd]
  simp [readU32LE?_fits hd]

/-- With no readable length prefix neither side retries. -/
theorem meaningHasExactErePrefix_none {bytes : ByteArray}
    (hd : BinaryFv.Specs.SSZ.readU32LE? bytes 0 = none) : meaningHasExactErePrefix bytes = false := by
  rw [meaningHasExactErePrefix, hd]

/-! ### The offset check cannot raise `unknownFork`

Needed for arm 2, and it is the fact that makes `unknownFork` *locate* its own cause: if every step of
`meaningDecodeRaw` before the four field decodes can only fail with `invalidSsz`, then an
`unknownFork` pins down how far the decode got, which is what supplies `spec_retry_rejects`'
hypotheses. -/

theorem canonicalOffsets_walk_only_invalidSsz (bytes : ByteArray) :
    ∀ (offs : List Nat) (prev : Nat),
      meaningRequireCanonicalOffsets.walk bytes prev offs = .ok () ∨
        meaningRequireCanonicalOffsets.walk bytes prev offs = .error .invalidSsz := by
  intro offs
  induction offs with
  | nil => intro prev; exact .inl rfl
  | cons o rest ih =>
      intro prev
      rw [meaningRequireCanonicalOffsets.walk]
      split
      · exact .inr rfl
      · exact ih o

theorem meaningRequireCanonicalOffsets_only_invalidSsz (bytes : ByteArray) (fixedSize : Nat)
    (offs : List Nat) :
    meaningRequireCanonicalOffsets bytes fixedSize offs = .ok () ∨
      meaningRequireCanonicalOffsets bytes fixedSize offs = .error .invalidSsz := by
  rw [meaningRequireCanonicalOffsets]
  split
  · exact .inr rfl
  · exact canonicalOffsets_walk_only_invalidSsz bytes offs fixedSize

/-! ### Arm 2: `unknownFork` pins how far the decode got

`spec_retry_rejects` needs `hasSchemaId bytes` and a first offset of exactly 16. Both follow from the
source having raised `unknownFork` at all, and the reason is the offset check: it can only fail with
`invalidSsz`, so an `unknownFork` proves it *succeeded*, and a successful check pins the first offset to
16 by equality rather than by bound.

**A prediction that did not hold, and the lemma it produced has been deleted.** I expected this to need
a fact that the three field meanings defined directly from the specification cannot raise `unknownFork` either, in order to locate
the error at `meaningChainConfig`, and wrote one. It is not needed: the conclusion is only about the
offset check, so *which* field decode raised the error is irrelevant. It was kept for one commit on the
theory that the `outOfMemory` half would want its shape — and that half turned out to be four lines
routed through `outOfMemoryUnreachableBelowBound_holds`, wanting nothing of the sort. So it was
needed-only-by-proofs-nobody-wrote, twice over, and is gone. An unused lemma in a proof file reads as
content; leaving it would have overstated what this section establishes. -/

/-- The error counterpart of `except_bind_ok`. -/
theorem except_bind_error {α β : Type} (e : DecodeError) (f : α → Except DecodeError β) :
    (Except.error e : Except DecodeError α) >>= f = .error e := rfl

theorem unknownFork_forces_canonical_prefix {bytes : ByteArray} (h : rootComplianceScope bytes)
    (herr : meaningDecodeRaw bytes = .error .unknownFork) :
    BinaryFv.Specs.SSZ.hasSchemaId bytes = true ∧
      BinaryFv.Specs.SSZ.readU32LE? (bytes.extract 2 bytes.size) 0 = some 16 := by
  rw [meaningDecodeRaw_in_scope h] at herr
  by_cases hsize : bytes.size < 2
  · rw [if_pos hsize] at herr; exact absurd herr (by simp)
  have hschemaTrue : BinaryFv.Specs.SSZ.hasSchemaId bytes = true := by
    cases hb : BinaryFv.Specs.SSZ.hasSchemaId bytes with
    | true => rfl
    | false =>
        have hT : (!BinaryFv.Specs.SSZ.hasSchemaId bytes) = true := by simp [hb]
        rw [if_neg hsize, if_pos hT] at herr
        exact absurd herr (by simp)
  have hnot : ¬ ((!BinaryFv.Specs.SSZ.hasSchemaId bytes) = true) := by simp [hschemaTrue]
  rw [if_neg hsize, if_neg hnot] at herr
  simp only [] at herr
  refine ⟨hschemaTrue, ?_⟩
  by_cases h16 : (bytes.extract 2 bytes.size).size < 16
  · rw [if_pos h16] at herr; exact absurd herr (by simp)
  rw [if_neg h16] at herr
  obtain ⟨o0, o1, o2, o3, hoffs⟩ := entry_offsets_of_sixteen (bytes.extract 2 bytes.size) (by omega)
  obtain ⟨r0, r1, r2, r3⟩ :=
    (extractFieldOffsets_eq_meaningReads (bytes.extract 2 bytes.size) o0 o1 o2 o3).mp hoffs
  simp only [r0, r1, r2, r3, except_bind_ok] at herr
  -- The offset check cannot have failed: it only raises `invalidSsz`.
  rcases meaningRequireCanonicalOffsets_only_invalidSsz (bytes.extract 2 bytes.size) 16
      [o0, o1, o2, o3] with hcan | hcan
  · obtain ⟨-, hc0, -, -, -, -⟩ :=
      (requireCanonicalOffsets_entry (bytes.extract 2 bytes.size) o0 o1 o2 o3).mp hcan
    subst hc0
    exact readU32LE?_of_meaningReadOffset (bytes.extract 2 bytes.size) 0 16 r0
  · rw [hcan, except_bind_error] at herr
    exact absurd herr (by simp)

/-- **The `outOfMemory` half of arm 2.** The source's raw decode never demands an allocation failure,
so the spec's retry has nothing to be matched against on that constructor.

Routed through `outOfMemoryUnreachableBelowBound_holds` rather than proved again structurally:
`meaningDecode` propagates every non-`invalidSsz` raw error unchanged, so the raw-level statement is
the outer one read backwards. Four lines, and it is why the lemma this section previously carried for
the purpose is gone. -/
theorem meaningDecodeRaw_ne_outOfMemory {bytes : ByteArray} (h : rootComplianceScope bytes) :
    meaningDecodeRaw bytes ≠ .error .outOfMemory := by
  intro hoom
  have hne := outOfMemoryUnreachableBelowBound_holds bytes h
  rw [meaningDecode, hoom] at hne
  exact hne rfl

/-! ## The outer assembly: the acceptance half of `sourceShapedDecodeAgreesWithSpec`

The three arms joined. What makes this provable at all is that the two entry points agree on
*acceptance* while disagreeing about *when to retry* in both directions at once:

* on `v3Quarantined` the spec refuses to retry and the source retries — closed from the source side
  by `retryTailNeverSchemaValid`;
* on `unknownFork` the spec retries and the source refuses — closed from the spec side by
  `spec_retry_rejects`, whose two hypotheses the error constructor itself supplies;
* on `outOfMemory` the question does not arise, because the source cannot raise it;
* on `invalidSsz` both retry on the same condition, and the intermediate applies again at the tail.

**Supplied versus proved.** Two hypotheses: `sourceShapedContainersAgreeWithSpec`, which carries the
`fork ≤ 20` bound the schema does not, and `retryTailNeverSchemaValid`. Everything else is proved —
both envelopes, the sixteen-byte test, the offset table, the four field slices, the four-field
composition, the V3 exclusion, and all three retry arms.

**A dead lemma removed on the spot rather than left in.** The proof was written expecting to need an
explicit collapse of the spec's six-way error match once `v3Quarantined` was excluded; `simp only []`
reduces it without help, so the lemma was deleted before this landed. Third dead lemma this session,
all three predicted-necessary and none necessary — the pattern being that I over-estimate how much
case analysis an error-taxonomy argument needs. -/

theorem tail_scope {bytes : ByteArray} (h : rootComplianceScope bytes) :
    rootComplianceScope (bytes.extract 4 bytes.size) := by
  have hb : bytes.size < 2 * 1024 * 1024 := h
  rw [rootComplianceScope, ByteArray.size_extract]
  omega

/-- **The acceptance half of `sourceShapedDecodeAgreesWithSpec`.**

This *was* the obligation, and is now half of it: the obligation carries the decoded value, and this
says only that the two entry points accept the same buffers. The value half is
`meaningDecode_value_agrees` below, and `ChainOffsets.sourceShapedDecodeAgreesWithSpec_holds`
joins them.

Why the split rather than one proof of the biconditional: the three retry arms below are a case
analysis on *errors*, which is a `Bool` argument end to end, and re-running it carrying a value would
duplicate it for no content. The value half runs the other way — from a specification success — and shares
none of this case analysis. -/
theorem meaningDecode_acceptance_agrees
    (containersAgree : sourceShapedContainersAgreeWithSpec)
    (retryTail : retryTailNeverSchemaValid) :
    ∀ (bytes : ByteArray), rootComplianceScope bytes →
      isAccepted (meaningDecode bytes) = (BinaryFv.Specs.SSZ.decodeStatelessInput bytes).toOption.isSome := by
  intro bytes h
  by_cases hv3 : BinaryFv.Specs.SSZ.hasV3PayloadShape bytes = true
  · obtain ⟨hs, ho⟩ := v3_arm_rejects_both containersAgree retryTail h hv3
    rw [hs, ho]
  rw [decodeStatelessInput_in_scope h, meaningDecode]
  have hagree := rawOrQuarantine_acceptance_agrees containersAgree h
  have htail := rawOrQuarantine_acceptance_agrees containersAgree (tail_scope h)
  cases hA : meaningDecodeRaw bytes with
  | ok v =>
      rw [hA] at hagree
      cases hW : BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3 bytes with
      | ok w => rfl
      | error rawError =>
          rw [hW] at hagree
          exact absurd hagree (by simp [isAccepted, Except.toOption])
  | error e =>
      cases hW : BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3 bytes with
      | ok w =>
          rw [hA, hW] at hagree
          exact absurd hagree (by simp [isAccepted, Except.toOption])
      | error rawError =>
          have hne : rawError ≠ .v3Quarantined := by
            intro hq
            exact hv3 (quarantined_of_rawOrQuarantine h (by rw [hW, hq]))
          -- Iota-reduce both outer matches on `Except.error _` so the inner ones are reachable.
          simp only []
          -- Both sides are now: retry when the length prefix matches, reject otherwise.
          cases hd : BinaryFv.Specs.SSZ.readU32LE? bytes 0 with
          | none =>
              -- Neither side retries.
              have hpre : meaningHasExactErePrefix bytes = false :=
                meaningHasExactErePrefix_none hd
              cases e with
              | invalidSsz => rw [if_neg (by simp [hpre])]; rfl
              | unknownFork => rfl
              | outOfMemory => rfl
          | some d =>
              have hpre : meaningHasExactErePrefix bytes = (d == bytes.size - 4) :=
                meaningHasExactErePrefix_eq bytes hd
              -- Reduce `match some d with …` so the length test is reachable.
              simp only []
              by_cases hmatch : (d == bytes.size - 4) = true
              · rw [if_pos hmatch]
                cases e with
                | invalidSsz => rw [if_pos (by rw [hpre]; exact hmatch)]; exact htail
                | unknownFork =>
                    -- The spec retries and the source does not; the spec's retry must fail.
                    obtain ⟨hschema, hfirst⟩ := unknownFork_forces_canonical_prefix h hA
                    have := spec_retry_rejects hschema hfirst
                    rw [this]
                    rfl
                | outOfMemory => exact absurd hA (meaningDecodeRaw_ne_outOfMemory h)
              · rw [if_neg hmatch]
                cases e with
                | invalidSsz => rw [if_neg (by rw [hpre]; exact hmatch)]; rfl
                | unknownFork => rfl
                | outOfMemory => rfl

/-! ## The value half: the two sides produce the *same* `StatelessInput`

Acceptance agreement is not what `root_compliance` needs. Its accepted branch has
`BinaryFv.Specs.SSZ.decode input = .accepted value`, which *is* `decodeStatelessInput input = .ok value`, and it
must produce that exact `value` — while the machine stores `meaningDecode input`'s. An acceptance
equation gives only `meaningDecode input = .ok v'` for some `v'`. So the obligation carries the
value, and this section is the direction that supplies it: **from a specification success to the same
success on the source side.**

Only one direction is proved here. The converse — meaning-accepts-with-`v` implies
spec-returns-`v` — is a two-line consequence of this one plus the acceptance half, since the two
values must then coincide by injectivity of `.ok`; `ChainOffsets.sourceShapedDecodeAgreesWithSpec_holds`
does that join.

**What was already available and what was not, recorded because the estimate was tested.** The
machinery above turned out to be value-level *in the backward direction only*
(`decodeCanonical_entry_eq_of_fields` concludes `= .ok (x0, x1, x2, x3, unit)`), with every forward
decomposition stated at `isSome`. That is enough: forward-with-values is backward-with-values plus
forward-at-`isSome` plus injectivity of `.ok`, and every step below is that three-line move. So no
new decomposition of the spec was needed at the entry. It was **not** enough at the chain: the
container obligation is acceptance-only by construction, so `meaningChainConfig` had to gain a
genuinely new value-level agreement, and that is `ChainOffsets.meaningChainConfig_value_agrees`.
This module consumes it as a hypothesis, exactly as it consumes the acceptance-level container fact. -/

/-- The chain-side hypothesis this module consumes: a canonical `chainConfig` decode inside the fork
bound is reproduced *with its value* by the source-shaped meaning.

A hypothesis rather than a theorem for the same reason `sourceShapedContainersAgreeWithSpec` is:
the chain lives in `ChainOffsets`, which imports this module. It is discharged there by
`chainConfigValue_holds`. -/
abbrev ChainConfigValueHypothesis : Prop :=
  ∀ (slice : ByteArray) (value : BinaryFv.Specs.SSZ.chainConfigType.interp),
    BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.chainConfigType slice = .ok value →
    (BinaryFv.Specs.SSZ.rawChainConfigOf value).activeFork.fork ≤ 20 →
    meaningChainConfig slice = .ok (BinaryFv.Specs.SSZ.rawChainConfigOf value)

/-- **The raw level, with the value.** `decodeRawInput` and `meaningDecodeRaw` return the same `StatelessInput`.

The three fields defined directly from the specification need no lemma: each meaning *is* `decodeCanonical` at its schema
followed by the bridge's own projection, so a field decode `= .ok xᵢ` rewrites the meaning to
`.ok (rawᵢOf xᵢ)` by definition. Only `meaningChainConfig` needs `containersMatch`, and the fork
bound it needs is the one the spec's own `fork > 20` guard just failed — the same projection on
both sides by `statelessInput_fork_eq_field_fork`. -/
theorem meaningDecodeRaw_value_agrees (containersMatch : ChainConfigValueHypothesis)
    {bytes : ByteArray} (h : rootComplianceScope bytes) {value : BinaryFv.Specs.SSZ.StatelessInput}
    (hdec : BinaryFv.Specs.SSZ.decodeRawInput bytes = .ok value) :
    meaningDecodeRaw bytes = .ok value := by
  rw [decodeRawInput_in_scope h] at hdec
  by_cases hsize : bytes.size < 2
  · rw [if_pos hsize] at hdec; exact absurd hdec (by simp)
  by_cases hschema : BinaryFv.Specs.SSZ.hasSchemaId bytes = false
  · rw [if_neg hsize, if_pos (by simp [hschema])] at hdec
    exact absurd hdec (by simp)
  have hschema' : ¬ ((!BinaryFv.Specs.SSZ.hasSchemaId bytes) = true) := by simp [hschema]
  rw [if_neg hsize, if_neg hschema'] at hdec
  have hu32 : (bytes.extract 2 bytes.size).size < UInt32.size := by
    have hscope : bytes.size < 2 * 1024 * 1024 := h
    have husz : UInt32.size = 4294967296 := rfl
    rw [ByteArray.size_extract, husz]; omega
  cases hdc : BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type
      (bytes.extract 2 bytes.size) with
  | error e => rw [hdc] at hdec; exact absurd hdec (by simp)
  | ok v =>
      rw [hdc] at hdec
      -- Iota-reduce `match Except.ok v with …` so the fork guard is reachable.
      simp only [] at hdec
      by_cases hf : (BinaryFv.Specs.SSZ.statelessInputOfInterp v).chainConfig.activeFork.fork > 20
      · rw [if_pos hf] at hdec; exact absurd hdec (by simp)
      rw [if_neg hf] at hdec
      have hval : BinaryFv.Specs.SSZ.statelessInputOfInterp v = value := by injection hdec
      subst hval
      have hacc : (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type
          (bytes.extract 2 bytes.size)).toOption.isSome = true := by rw [hdc]; rfl
      have h16 : ¬ (bytes.extract 2 bytes.size).size < 16 := by
        intro hlt
        rw [decodeCanonical_entry_short hlt] at hdc
        exact absurd hdc (by simp)
      obtain ⟨o0, o1, o2, o3, hoffs⟩ :=
        entry_offsets_of_sixteen (bytes.extract 2 bytes.size) (by omega)
      obtain ⟨r0, r1, r2, r3⟩ :=
        (extractFieldOffsets_eq_meaningReads (bytes.extract 2 bytes.size) o0 o1 o2 o3).mp hoffs
      have hcan : meaningRequireCanonicalOffsets (bytes.extract 2 bytes.size) 16
          [o0, o1, o2, o3] = .ok () := by
        cases hc : meaningRequireCanonicalOffsets (bytes.extract 2 bytes.size) 16
            [o0, o1, o2, o3] with
        | ok u => cases u; rfl
        | error e =>
            exfalso
            have hbad : ¬ (o0 = 16 ∧ o0 ≤ o1 ∧ o1 ≤ o2 ∧ o2 ≤ o3 ∧
                o3 ≤ (bytes.extract 2 bytes.size).size) := by
              intro hgood
              have hok := (requireCanonicalOffsets_entry (bytes.extract 2 bytes.size)
                o0 o1 o2 o3).mpr
                ⟨extractFieldOffsets_entry_fits (bytes.extract 2 bytes.size) o0 o1 o2 o3 hoffs,
                  hgood.1, hgood.2.1, hgood.2.2.1, hgood.2.2.2.1, hgood.2.2.2.2⟩
              rw [hc] at hok
              exact absurd hok (by simp)
            rw [decodeCanonical_entry_rejects_noncanonical (bytes.extract 2 bytes.size)
              o0 o1 o2 o3 hoffs hbad] at hacc
            exact absurd hacc (by simp)
      obtain ⟨-, hc0, hc01, hc12, hc23, hc3⟩ :=
        (requireCanonicalOffsets_entry (bytes.extract 2 bytes.size) o0 o1 o2 o3).mp hcan
      obtain ⟨q0, q1, q2, q3⟩ :=
        decodeCanonical_entry_fields_of (bytes.extract 2 bytes.size) o0 o1 o2 o3 hoffs
          hc0 hc01 hc12 hc23 hc3 hu32 hacc
      obtain ⟨x0, e0⟩ := except_isSome_iff.mp q0
      obtain ⟨x1, e1⟩ := except_isSome_iff.mp q1
      obtain ⟨x2, e2⟩ := except_isSome_iff.mp q2
      obtain ⟨x3, e3⟩ := except_isSome_iff.mp q3
      -- Forward-with-values: the backward value-level composition pins `v` to the four witnesses.
      have hv : v = (x0, x1, x2, x3, PUnit.unit) := by
        have heq := decodeCanonical_entry_eq_of_fields (bytes.extract 2 bytes.size) o0 o1 o2 o3
          hoffs hc0 hc01 hc12 hc23 hc3 hu32 e0 e1 e2 e3
        rw [hdc] at heq
        injection heq
      subst hv
      have hfork : (BinaryFv.Specs.SSZ.rawChainConfigOf x2).activeFork.fork ≤ 20 := UInt64.not_lt.mp hf
      rw [meaningDecodeRaw_in_scope h, if_neg hsize, if_neg hschema']
      simp only []
      rw [if_neg h16]
      simp only [r0, r1, r2, r3, except_bind_ok, hcan]
      rw [show meaningNewPayloadRequest ((bytes.extract 2 bytes.size).extract o0 o1)
            = .ok (BinaryFv.Specs.SSZ.rawNewPayloadRequestOf x0) from by rw [meaningNewPayloadRequest, e0],
        show meaningExecutionWitness ((bytes.extract 2 bytes.size).extract o1 o2)
            = .ok (BinaryFv.Specs.SSZ.rawWitnessOf x1) from by rw [meaningExecutionWitness, e1],
        containersMatch ((bytes.extract 2 bytes.size).extract o2 o3) x2 e2 hfork,
        show meaningPublicKeys ((bytes.extract 2 bytes.size).extract o3
              (bytes.extract 2 bytes.size).size) = .ok x3.1 from by rw [meaningPublicKeys, e3]]
      rfl

/-- The quarantine wrapper, with the value. A quarantined buffer never returns `.ok`, so the arm
that made `rawOrQuarantine_acceptance_agrees` interesting collapses outright here. -/
theorem rawOrQuarantine_value_agrees (containersMatch : ChainConfigValueHypothesis)
    {bytes : ByteArray} (h : rootComplianceScope bytes) {value : BinaryFv.Specs.SSZ.StatelessInput}
    (hdec : BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3 bytes = .ok value) :
    meaningDecodeRaw bytes = .ok value := by
  rw [BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3] at hdec
  split at hdec
  · exact absurd hdec (by simp)
  · exact meaningDecodeRaw_value_agrees containersMatch h hdec

/-- **The outer assembly, with the value.** An spec success is reproduced by `meaningDecode`, value
and all.

The retry arms enter differently from the acceptance proof and it is worth saying how. Here the
spec has *succeeded*, so the only live question is which of its two routes it took. On the direct
route the source's raw decode succeeds with the same value and `meaningDecode` returns it
unchanged. On the retry route the source's raw decode must have failed — that is the acceptance
half — and its error must be `invalidSsz`: `unknownFork` would force the spec's own retry to
reject (`spec_retry_rejects`), contradicting its success, and `outOfMemory` is unreachable in
scope. So the source retries on exactly the same condition, at exactly the same tail, and the raw
lemma applies a second time. -/
theorem meaningDecode_value_agrees
    (containersAgree : sourceShapedContainersAgreeWithSpec)
    (containersMatch : ChainConfigValueHypothesis)
    {bytes : ByteArray} (h : rootComplianceScope bytes) {value : BinaryFv.Specs.SSZ.StatelessInput}
    (hdec : BinaryFv.Specs.SSZ.decodeStatelessInput bytes = .ok value) :
    meaningDecode bytes = .ok value := by
  rw [decodeStatelessInput_in_scope h] at hdec
  have hagree := rawOrQuarantine_acceptance_agrees containersAgree h
  cases hW : BinaryFv.Specs.SSZ.decodeRawOrQuarantineV3 bytes with
  | ok w =>
      rw [hW] at hdec
      have hwv : w = value := by injection hdec
      subst hwv
      rw [meaningDecode, rawOrQuarantine_value_agrees containersMatch h hW]
  | error e =>
      rw [hW] at hdec
      simp only [] at hdec
      rw [hW] at hagree
      have hraw : ∃ e', meaningDecodeRaw bytes = .error e' := by
        cases hA : meaningDecodeRaw bytes with
        | ok v => rw [hA] at hagree; exact absurd hagree (by simp [isAccepted, Except.toOption])
        | error e' => exact ⟨e', rfl⟩
      obtain ⟨e', hA⟩ := hraw
      cases e with
      | v3Quarantined => exact absurd hdec (by simp)
      | tooLarge | tooShort | badSchema | unknownFork | ssz _ =>
        all_goals (
          simp only [] at hdec
          cases hd : BinaryFv.Specs.SSZ.readU32LE? bytes 0 with
          | none => rw [hd] at hdec; exact absurd hdec (by simp)
          | some d =>
              rw [hd] at hdec
              simp only [] at hdec
              by_cases hmatch : (d == bytes.size - 4) = true
              · rw [if_pos hmatch] at hdec
                have hpre : meaningHasExactErePrefix bytes = true := by
                  rw [meaningHasExactErePrefix_eq bytes hd]; exact hmatch
                have hinv : e' = DecodeError.invalidSsz := by
                  cases e' with
                  | invalidSsz => rfl
                  | unknownFork =>
                      exfalso
                      obtain ⟨hs, hfirst⟩ := unknownFork_forces_canonical_prefix h hA
                      have hrej := spec_retry_rejects hs hfirst
                      rw [hdec] at hrej
                      exact absurd hrej (by simp [Except.toOption])
                  | outOfMemory => exact absurd hA (meaningDecodeRaw_ne_outOfMemory h)
                rw [meaningDecode, hA, hinv]
                simp only []
                rw [if_pos hpre]
                exact rawOrQuarantine_value_agrees containersMatch (tail_scope h) hdec
              · rw [if_neg hmatch] at hdec
                exact absurd hdec (by simp))

end BinaryFv.Zesu.DecodedValue
