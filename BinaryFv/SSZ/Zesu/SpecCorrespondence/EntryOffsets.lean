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

end BinaryFv.SSZ.Zesu.SpecCorrespondence
