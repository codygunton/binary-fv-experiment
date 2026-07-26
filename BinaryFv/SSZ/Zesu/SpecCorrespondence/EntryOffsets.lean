import BinaryFv.SSZ.Zesu.Contracts.Entry
import BinaryFv.SSZ.Zesu.Contracts.SemanticObligations

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

/-! ## The oracle's field slices

`deserializeVarFields` walks the field list carrying the offset table, and for each variable field
takes the slice from its own offset to the *next* one — with `bufEnd` standing in as the sentinel
after the last field. Under the guards `requireCanonicalOffsets_entry` supplies, those slices are
exactly the four `body.extract` calls `meaningDecodeRaw` makes.

The `prefixOff` argument is threaded but never reaches the result on an all-variable field list: it
only advances the fixed-section cursor, which has no fixed fields to read. -/

/-- **The oracle slices the entry body exactly where the source does.**

Stated as the full nested match rather than at acceptance granularity, because the composition
theorem needs the decoded *values*, not just whether the decode succeeded — and because the nesting
is what preserves first-error-wins ordering, which a flat match would silently discard. -/
theorem deserializeVarFields_entry (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (h01 : o0 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size) :
    SSZType.deserializeVarFields entryFields body 0 [o0, o1, o2, o3] body.size =
      match SSZType.deserialize SszBridge.newPayloadRequestType (body.extract o0 o1) with
      | .error e => .error e
      | .ok (x0, _) =>
        match SSZType.deserialize SszBridge.witnessType (body.extract o1 o2) with
        | .error e => .error e
        | .ok (x1, _) =>
          match SSZType.deserialize SszBridge.chainConfigType (body.extract o2 o3) with
          | .error e => .error e
          | .ok (x2, _) =>
            match SSZType.deserialize
                (.list (SszBridge.byteVector SszBridge.publicKeyBytes) SszBridge.maxPublicKeys)
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
  cases SSZType.deserialize SszBridge.newPayloadRequestType (body.extract o0 o1) <;>
    cases SSZType.deserialize SszBridge.witnessType (body.extract o1 o2) <;>
      cases SSZType.deserialize SszBridge.chainConfigType (body.extract o2 o3) <;>
        cases SSZType.deserialize
            (.list (SszBridge.byteVector SszBridge.publicKeyBytes) SszBridge.maxPublicKeys)
            (body.extract o3 body.size) <;> rfl

/-! ## The per-field `used` check is redundant

**What breaks if this does not hold.** The source decodes each entry field with `decodeCanonical`,
which checks `used = slice.size`. The oracle does *not*: the top-level check is vacuous at the entry
container — the variable-container arm returns `(v, b.size)`, so `used = body.size` unconditionally
— and `deserializeVarFields` discards each field's `used` (`Deserialize.lean:513` matches
`.ok (x, _)`). So the re-serialization equality is the only thing constraining the fields. If the
per-field `used` check were *not* redundant, the source side would be strictly stronger than the
oracle, there would be a body the oracle accepts and the source rejects, and
`sourceShapedDecodeAgreesWithOracle` would be **false**. This is a fourth statement defect avoided,
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
what makes the source's per-field `decodeCanonical` no stronger than what the oracle does per field.
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
    (e0 : SSZType.serialize SszBridge.newPayloadRequestType v.1 = s0)
    (e1 : SSZType.serialize SszBridge.witnessType v.2.1 = s1)
    (e2 : SSZType.serialize SszBridge.chainConfigType v.2.2.1 = s2)
    (e3 : SSZType.serialize (SSZType.list (SszBridge.byteVector SszBridge.publicKeyBytes)
            SszBridge.maxPublicKeys) v.2.2.2.1 = s3) :
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

That is a correction to an earlier reading of this row. Checking that `append_assoc`, `size_append`
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
    (e0 : SSZType.serialize SszBridge.newPayloadRequestType v.1 = s0)
    (e1 : SSZType.serialize SszBridge.witnessType v.2.1 = s1)
    (e2 : SSZType.serialize SszBridge.chainConfigType v.2.2.1 = s2)
    (e3 : SSZType.serialize (SSZType.list (SszBridge.byteVector SszBridge.publicKeyBytes)
            SszBridge.maxPublicKeys) v.2.2.2.1 = s3)
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
    (e0 : SSZType.serialize SszBridge.newPayloadRequestType v.1 = s0)
    (e1 : SSZType.serialize SszBridge.witnessType v.2.1 = s1)
    (e2 : SSZType.serialize SszBridge.chainConfigType v.2.2.1 = s2)
    (e3 : SSZType.serialize (SSZType.list (SszBridge.byteVector SszBridge.publicKeyBytes)
            SszBridge.maxPublicKeys) v.2.2.2.1 = s3) :
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
followed by a projection, so they agree with the oracle **by construction** rather than by theorem:
the projection is applied only on the `.ok` arm and cannot turn acceptance into rejection or back.
The three lemmas below say exactly that and nothing more.

The fourth field decode is `meaningChainConfig`, which is *source-shaped* — its `fork > 20` check
sits between the offset-table check and the child decodes, so it is not `decodeCanonical` at any
schema. That is `sourceShapedContainersAgreeWithOracle`, a separate component of item 6, and nothing
in this module touches it.

Load-bearing audit: these four have no hypotheses, so there is nothing to audit. Recorded because the
audit is now mechanical, and "no hypotheses" is a result of running it rather than a reason to skip. -/

/-- The entry schema's fourth field is exactly the collection `meaningPublicKeys` decodes. -/
theorem publicKeysType_eq_entry_field :
    publicKeysType
      = .list (SszBridge.byteVector SszBridge.publicKeyBytes) SszBridge.maxPublicKeys := rfl

theorem meaningNewPayloadRequest_accepted (b : ByteArray) :
    isAccepted (meaningNewPayloadRequest b)
      = (SszBridge.decodeCanonical SszBridge.newPayloadRequestType b).toOption.isSome := by
  cases h : SszBridge.decodeCanonical SszBridge.newPayloadRequestType b <;>
    simp [meaningNewPayloadRequest, isAccepted, Except.toOption, h]

theorem meaningExecutionWitness_accepted (b : ByteArray) :
    isAccepted (meaningExecutionWitness b)
      = (SszBridge.decodeCanonical SszBridge.witnessType b).toOption.isSome := by
  cases h : SszBridge.decodeCanonical SszBridge.witnessType b <;>
    simp [meaningExecutionWitness, isAccepted, Except.toOption, h]

theorem meaningPublicKeys_accepted (b : ByteArray) :
    isAccepted (meaningPublicKeys b)
      = (SszBridge.decodeCanonical publicKeysType b).toOption.isSome := by
  cases h : SszBridge.decodeCanonical publicKeysType b <;>
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
    SszBridge.decodeCanonical SszBridge.statelessInputV4Type body =
      match SSZType.deserializeVarFields entryFields body 0 [o0, o1, o2, o3] body.size with
      | .error e => .error e
      | .ok v =>
          if SSZType.serialize SszBridge.statelessInputV4Type v == body then .ok v
          else .error .invalidOffset := by
  have hdes : SSZType.deserialize SszBridge.statelessInputV4Type body =
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
  rw [SszBridge.decodeCanonical]
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
    SszBridge.decodeCanonical t b =
      if SSZType.serialize t x == b then .ok x else .error .invalidOffset := by
  subst hused
  rw [SszBridge.decodeCanonical, hdes]
  simp [bind, Except.bind]
  rfl

/-! ### Discharging the workhorse premise per field

`decodeCanonical_of_used_eq` needs `used = b.size` at each entry field. For the three containers
that is `deserialize_container_used`, and the `allFixedSize` premise is exactly the `isFixedSize`
fact already proved by `decide` — `isFixedSize (.container fs)` *is* `allFixedSize fs`, so the two
statements are definitionally the same and no bridging lemma is needed. -/

theorem deserialize_newPayloadRequest_used {b : ByteArray}
    {x : SszBridge.newPayloadRequestType.interp} {u : Nat}
    (h : SSZType.deserialize SszBridge.newPayloadRequestType b = .ok (x, u)) : u = b.size :=
  deserialize_container_used _ b newPayloadRequestType_not_fixed x u h

theorem deserialize_witness_used {b : ByteArray}
    {x : SszBridge.witnessType.interp} {u : Nat}
    (h : SSZType.deserialize SszBridge.witnessType b = .ok (x, u)) : u = b.size :=
  deserialize_container_used _ b witnessType_not_fixed x u h

theorem deserialize_chainConfig_used {b : ByteArray}
    {x : SszBridge.chainConfigType.interp} {u : Nat}
    (h : SSZType.deserialize SszBridge.chainConfigType b = .ok (x, u)) : u = b.size :=
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
    (h : SszBridge.decodeCanonical t b = .ok x) :
    SSZType.deserialize t b = .ok (x, b.size) ∧ SSZType.serialize t x = b := by
  rw [SszBridge.decodeCanonical] at h
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

From the four per-field canonical decodes to the oracle's acceptance of the whole body. This is the
direction that has to *construct* the accepted value and show its re-serialization reproduces the
buffer, so it is where every piece built above finally meets. -/

/-- **Four canonical field decodes make the entry decode canonical.** -/
theorem decodeCanonical_entry_eq_of_fields
    (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size)
    (hu32 : body.size < UInt32.size)
    {x0 : SszBridge.newPayloadRequestType.interp} {x1 : SszBridge.witnessType.interp}
    {x2 : SszBridge.chainConfigType.interp} {x3 : publicKeysType.interp}
    (a0 : SszBridge.decodeCanonical SszBridge.newPayloadRequestType (body.extract o0 o1) = .ok x0)
    (a1 : SszBridge.decodeCanonical SszBridge.witnessType (body.extract o1 o2) = .ok x1)
    (a2 : SszBridge.decodeCanonical SszBridge.chainConfigType (body.extract o2 o3) = .ok x2)
    (a3 : SszBridge.decodeCanonical publicKeysType (body.extract o3 body.size) = .ok x3) :
    SszBridge.decodeCanonical SszBridge.statelessInputV4Type body
      = .ok (x0, x1, x2, x3, PUnit.unit) := by
  -- `omega` treats `UInt32.size` as an atom; this links it to the numeral.
  have husz : UInt32.size = 4294967296 := rfl
  obtain ⟨d0, s0eq⟩ := decodeCanonical_inv a0
  obtain ⟨d1, s1eq⟩ := decodeCanonical_inv a1
  obtain ⟨d2, s2eq⟩ := decodeCanonical_inv a2
  obtain ⟨d3, s3eq⟩ := decodeCanonical_inv a3
  subst h0
  -- Each field body is exactly its slice, so its width is the gap between consecutive offsets.
  have w0 : (SSZType.serialize SszBridge.newPayloadRequestType x0).size = o1 - 16 := by
    rw [s0eq, ByteArray.size_extract]; omega
  have w1 : (SSZType.serialize SszBridge.witnessType x1).size = o2 - o1 := by
    rw [s1eq, ByteArray.size_extract]; omega
  have w2 : (SSZType.serialize SszBridge.chainConfigType x2).size = o3 - o2 := by
    rw [s2eq, ByteArray.size_extract]; omega
  obtain ⟨c1, c2, c3⟩ :=
    cumulative_sums_eq_offsets body 16 o1 o2 o3 _ _ _ rfl h01 h12 h23 h3 s0eq s1eq s2eq
  -- `d3` is stated at `publicKeysType`; the walker's goal shows the unfolded list type. Defeq, so a
  -- restatement crosses it, but `rw` needs the syntactic form.
  have d3' : SSZType.deserialize
      (.list (SszBridge.byteVector SszBridge.publicKeyBytes) SszBridge.maxPublicKeys)
      (body.extract o3 body.size) = .ok (x3, (body.extract o3 body.size).size) := d3
  rw [decodeCanonical_entry_unfold body 16 o1 o2 o3 hoffs rfl,
    deserializeVarFields_entry body 16 o1 o2 o3 h01 h12 h23 h3, d0, d1, d2, d3']
  have s3eq' : SSZType.serialize
      (.list (SszBridge.byteVector SszBridge.publicKeyBytes) SszBridge.maxPublicKeys) x3
      = body.extract o3 body.size := s3eq
  have hser : SSZType.serialize SszBridge.statelessInputV4Type
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
    {x0 : SszBridge.newPayloadRequestType.interp} {x1 : SszBridge.witnessType.interp}
    {x2 : SszBridge.chainConfigType.interp} {x3 : publicKeysType.interp}
    (a0 : SszBridge.decodeCanonical SszBridge.newPayloadRequestType (body.extract o0 o1) = .ok x0)
    (a1 : SszBridge.decodeCanonical SszBridge.witnessType (body.extract o1 o2) = .ok x1)
    (a2 : SszBridge.decodeCanonical SszBridge.chainConfigType (body.extract o2 o3) = .ok x2)
    (a3 : SszBridge.decodeCanonical publicKeysType (body.extract o3 body.size) = .ok x3) :
    (SszBridge.decodeCanonical SszBridge.statelessInputV4Type body).toOption.isSome = true := by
  rw [decodeCanonical_entry_eq_of_fields body o0 o1 o2 o3 hoffs h0 h01 h12 h23 h3 hu32 a0 a1 a2 a3]
  rfl

/-! ### The fork bound is the same projection on both sides

`decodeRawV4` throws `unknownFork` on `raw.chainConfig.activeFork.fork > 20`, where
`raw = rawV4OfInterp value`. `sourceShapedContainersAgreeWithOracle` bounds
`(rawChainConfigOf value').activeFork.fork` for the chainConfig *field's* decode. Those are the same
number, and the reason is definitional rather than analogous: `rawV4OfInterp` sets
`chainConfig := rawChainConfigOf value.2.2.1`, so the whole-body projection *is* the field
projection applied to the third component.

This is why the value-level decomposition matters and the acceptance-level one does not suffice: the
bound is a predicate on the decoded VALUE, so matching it needs to know the entry decode's third
component is exactly what the chainConfig field decode returned. -/

theorem rawV4_fork_eq_field_fork (value : SszBridge.statelessInputV4Type.interp) :
    (SszBridge.rawV4OfInterp value).chainConfig.activeFork.fork
      = (SszBridge.rawChainConfigOf value.2.2.1).activeFork.fork := rfl

/-! ## The entry composition, forward direction

From the oracle's acceptance of the whole body to the four per-field canonical decodes. The same
pieces as the backward direction, run the other way: the re-serialization equality is *given* here
and has to be taken apart, rather than assembled. -/

/-- **A canonical entry decode makes all four field decodes canonical.** -/
theorem decodeCanonical_entry_fields_of
    (body : ByteArray) (o0 o1 o2 o3 : Nat)
    (hoffs : extractFieldOffsets body entryFields 0 = .ok [o0, o1, o2, o3])
    (h0 : o0 = 16) (h01 : o0 ≤ o1) (h12 : o1 ≤ o2) (h23 : o2 ≤ o3) (h3 : o3 ≤ body.size)
    (hu32 : body.size < UInt32.size)
    (hacc : (SszBridge.decodeCanonical SszBridge.statelessInputV4Type body).toOption.isSome = true) :
    (SszBridge.decodeCanonical SszBridge.newPayloadRequestType (body.extract o0 o1)).toOption.isSome
        = true ∧
      (SszBridge.decodeCanonical SszBridge.witnessType (body.extract o1 o2)).toOption.isSome = true ∧
      (SszBridge.decodeCanonical SszBridge.chainConfigType (body.extract o2 o3)).toOption.isSome
        = true ∧
      (SszBridge.decodeCanonical publicKeysType (body.extract o3 body.size)).toOption.isSome
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
              have hb : SSZType.serialize SszBridge.statelessInputV4Type
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
                show (SszBridge.decodeCanonical
                    (.list (SszBridge.byteVector SszBridge.publicKeyBytes) SszBridge.maxPublicKeys)
                    (body.extract o3 body.size)).toOption.isSome = true
                rw [decodeCanonical_of_used_eq _ _ x3 _ hd3 rfl, r3, byteArray_beq_self]; rfl
    · exact absurd hacc (by simp [Except.toOption])

/-! ## The entry composition theorem

Both directions together. This is what item 6 was sized around: the oracle's canonical decode of the
whole body and the four per-field canonical decodes accept **the same inputs**, not merely one
implying the other.

**Where the container obligation does *not* enter, and why that is not an omission.**
`sourceShapedContainersAgreeWithOracle` equates `isAccepted (meaningChainConfig bytes)` with
`decodeCanonical chainConfigType bytes` succeeding *and* `fork ≤ 20`. That bound is not part of the
schema: `chainConfigType` types `fork` as an unbounded `u64`, and the oracle applies the bound one
layer up in `decodeRawV4`, after a complete canonical decode. So at *this* layer — `decodeCanonical`
against `decodeCanonical` — neither side applies it, and stating the theorem with the container
hypothesis would be stating a hypothesis it does not use.

The bound enters when this decomposition is composed towards `decodeRawV4` and `meaningDecodeRaw`,
where the oracle's post-decode `fork > 20` check has to be matched against the source's check inside
`meaningChainConfig`. That is exactly the layering `sourceShapedContainersAgreeWithOracle` was
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
    (SszBridge.decodeCanonical SszBridge.statelessInputV4Type body).toOption.isSome = true ↔
      ((SszBridge.decodeCanonical SszBridge.newPayloadRequestType
            (body.extract o0 o1)).toOption.isSome = true ∧
        (SszBridge.decodeCanonical SszBridge.witnessType (body.extract o1 o2)).toOption.isSome
            = true ∧
        (SszBridge.decodeCanonical SszBridge.chainConfigType (body.extract o2 o3)).toOption.isSome
            = true ∧
        (SszBridge.decodeCanonical publicKeysType (body.extract o3 body.size)).toOption.isSome
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

**Two routes to one proposition is not the duplication this row rejects elsewhere.** We refused a
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

/-! ## The four field meanings in oracle terms

**This is where `sourceShapedContainersAgreeWithOracle` is consumed.** Three of the four field
meanings are `decodeCanonical` plus a projection, so their acceptance equals the oracle's by
construction. The fourth, `meaningChainConfig`, is source-shaped and its acceptance carries the
`fork ≤ 20` bound that the schema does not — which is exactly what the container obligation states,
and why its conjunct below has a different shape from the other three.

That asymmetry is the whole content of this step. A reader looking for where the container fact is
discharged should find it here, and should see that it is *not* discharged by the four-field
decomposition, which is pure oracle on both sides. -/

theorem entry_field_meanings_in_oracle_terms
    (containersAgree : sourceShapedContainersAgreeWithOracle) (b : ByteArray) :
    isAccepted (meaningNewPayloadRequest b)
        = (SszBridge.decodeCanonical SszBridge.newPayloadRequestType b).toOption.isSome ∧
      isAccepted (meaningExecutionWitness b)
        = (SszBridge.decodeCanonical SszBridge.witnessType b).toOption.isSome ∧
      isAccepted (meaningPublicKeys b)
        = (SszBridge.decodeCanonical publicKeysType b).toOption.isSome ∧
      isAccepted (meaningChainConfig b)
        = (match SszBridge.decodeCanonical SszBridge.chainConfigType b with
            | .ok value => decide ((SszBridge.rawChainConfigOf value).activeFork.fork ≤ 20)
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
  [SszBridge.byteVector 32, SszBridge.byteVector 20, SszBridge.byteVector 32,
    SszBridge.byteVector 32, SszBridge.byteVector 256, SszBridge.byteVector 32,
    SszBridge.u64, SszBridge.u64, SszBridge.u64, SszBridge.u64,
    SszBridge.byteList SszBridge.maxExtraDataBytes,
    SszBridge.u256,
    SszBridge.byteVector 32,
    .list (SszBridge.byteList SszBridge.maxBytesPerTransaction) SszBridge.maxTransactionsPerPayload,
    .list SszBridge.withdrawalType SszBridge.maxWithdrawalsPerPayload,
    SszBridge.u64, SszBridge.u64,
    SszBridge.byteList SszBridge.maxBytesPerTransaction,
    SszBridge.u64]

theorem executionPayloadType_eq :
    SszBridge.executionPayloadType = .container executionPayloadFields := rfl

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
  [SszBridge.executionPayloadType,
    .list (SszBridge.byteVector 32) SszBridge.maxBlobCommitmentsPerBlock,
    SszBridge.byteVector 32,
    SszBridge.executionRequestsType]

theorem newPayloadRequestType_eq :
    SszBridge.newPayloadRequestType = .container newPayloadRequestFields := rfl

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
    SszBridge.executionPayloadType.isFixedSize = false := by decide

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
    (h : SszBridge.hasV3PayloadShape bytes = true) :
    ∃ hashesOffset payloadEnd,
      SszBridge.hasSchemaId bytes = true ∧
      SszBridge.readU32LE? (bytes.extract 2 bytes.size) 0 = some 16 ∧
      SszBridge.readU32LE? (bytes.extract 2 bytes.size) 4 = some hashesOffset ∧
      SszBridge.readU32LE? ((bytes.extract 2 bytes.size).extract 16 hashesOffset) 0 = some 44 ∧
      SszBridge.readU32LE? ((bytes.extract 2 bytes.size).extract 16 hashesOffset) 4
        = some payloadEnd ∧
      SszBridge.readU32LE?
        (((bytes.extract 2 bytes.size).extract 16 hashesOffset).extract 44 payloadEnd) 436
          = some 528 := by
  rw [SszBridge.hasV3PayloadShape] at h
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
        simp only [Bool.not_or, Bool.not_eq_true, bne_iff_ne, ne_eq, Decidable.not_not,
          decide_eq_true_eq, Bool.decide_or, Bool.or_eq_false_iff] at hbad
        split at h
        · rename_i po pe hp hpe
          split at h
          · exact absurd h (by simp)
          · rename_i hbad2
            simp only [Bool.not_or, Bool.not_eq_true, bne_iff_ne, ne_eq, Decidable.not_not,
              decide_eq_true_eq, Bool.decide_or, Bool.or_eq_false_iff] at hbad2
            have hreq : req = 16 := by simpa using hbad.1.1
            have hpo : po = 44 := by simpa using hbad2.1.1
            subst hreq
            subst hpo
            exact ⟨hashes, pe, by simpa using hschema, hr, hh, hp, hpe, by simpa using h⟩
        · exact absurd h (by simp)
    · exact absurd h (by simp)

/-! ### The sharp end: byte 436 must read 540

This is where the exclusion actually bites, and where the **second `bv_decide` door** enters, exactly
as pre-announced: the classifier reads with `SszBridge.readU32LE?` while canonicality constrains
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
    SszBridge.readU32LE? payload 436 = some 540 := by
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
specialised side, and it is the whole of that side for item 4: one table reduction, no decomposition. -/

theorem newPayloadRequestFields_not_allFixed :
    SSZType.allFixedSize newPayloadRequestFields = false := by decide

theorem newPayloadRequestFields_takeWhile_fixed :
    SSZType.fixedSectionSizeFields
      (newPayloadRequestFields.takeWhile SSZType.isFixedSize) = 0 := by decide

@[simp] theorem blobCommitmentsField_not_fixed :
    (SSZType.list (SszBridge.byteVector 32) SszBridge.maxBlobCommitmentsPerBlock).isFixedSize
      = false := by decide

@[simp] theorem byteVector32_is_fixed :
    (SszBridge.byteVector 32).isFixedSize = true := by decide

@[simp] theorem byteVector32_fixedByteSize :
    (SszBridge.byteVector 32).fixedByteSize = 32 := by decide

@[simp] theorem executionRequestsType_not_fixed :
    SszBridge.executionRequestsType.isFixedSize = false := by decide

theorem extractFieldOffsets_newPayloadRequest (b : ByteArray) :
    extractFieldOffsets b newPayloadRequestFields 0 =
      match readUInt32LE b 0, readUInt32LE b 4, readUInt32LE b 40 with
      | some p0, some p1, some p2 => .ok [p0.toNat, p1.toNat, p2.toNat]
      | _, _, _ => .error .tooShort := by
  simp [newPayloadRequestFields, extractFieldOffsets, BYTES_PER_LENGTH_OFFSET]
  cases readUInt32LE b 0 <;> cases readUInt32LE b 4 <;> cases readUInt32LE b 40 <;> rfl

end BinaryFv.SSZ.Zesu.SpecCorrespondence




