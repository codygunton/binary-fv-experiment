import BinaryFv.SSZ.Zesu.Contracts.RepresentationAudit

/-!
# Footprints: where a representation actually lives

`RepresentationAudit` proves every canonical representation is `LocalTo` the **universal** region.
That closes `Ownership.localTo_is_a_real_obligation` and buys eligibility — and nothing more, because
a sibling's writes are never disjoint from everything. Protection needs the *tight* region a
representation actually reads. This module computes those.

## Why widening is the failure mode, and why tightness therefore needs its own check

`LocalTo` gets **weaker** as the region grows: a bigger region assumes more agreement, so it
transports more easily. The universal region is the weakest possible statement and is already proved.
So a footprint claim cannot be validated by "the proof went through" — a padded footprint proves just
as easily as a tight one, and a maximally padded one is exactly the vacuous result already in hand.

That makes this the check-that-cannot-fail shape in a new disguise, and it is why every footprint here
carries a companion:

* **`LocalTo … footprint`** — soundness. Agreement on the footprint transports the representation.
* **`…_tight`** — power. For *each* address in the footprint, two states that agree everywhere else
  and disagree on the representation. This is what fails if the footprint is padded, and it is the
  only direction in which a footprint can be wrong in a way that matters.

Soundness alone would be satisfied by `fun _ => True`. Tightness alone would be satisfied by the empty
region. Only the pair pins the answer.
-/

namespace BinaryFv.SSZ.Zesu.Contracts.Footprint

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.SSZ.Zesu.Contracts.Ownership
open BinaryFv.SSZ.Zesu.Contracts.RepresentationAudit

/-- A half-open byte range, the shape every container footprint takes. -/
def range (base size : Nat) : Region := fun address => base ≤ address ∧ address < base + size

/-- Determinacy relative to a region rather than to all of memory. `MemDetermined` is this at the
universal region. -/
def MemDeterminedOn (region : Region) (P : State → Prop) : Prop :=
  ∀ s1 s2, (∀ address, region address → s1.mem.get? address = s2.mem.get? address) → P s1 → P s2

/-- **Widening weakens.** The formal statement of why soundness alone proves nothing: any footprint
result implies every larger one, up to the universal region already proved in
`RepresentationAudit`. -/
theorem memDeterminedOn_mono {small large : Region} {P : State → Prop}
    (sub : ∀ address, small address → large address)
    (h : MemDeterminedOn small P) : MemDeterminedOn large P :=
  fun s1 s2 agree => h s1 s2 fun address hsmall => agree address (sub address hsmall)

theorem memDeterminedOn_and {r : Region} {P Q : State → Prop}
    (hp : MemDeterminedOn r P) (hq : MemDeterminedOn r Q) :
    MemDeterminedOn r (fun s => P s ∧ Q s) :=
  fun s1 s2 agree h => ⟨hp s1 s2 agree h.1, hq s1 s2 agree h.2⟩

theorem memDeterminedOn_const {r : Region} {p : Prop} : MemDeterminedOn r (fun _ => p) :=
  fun _ _ _ h => h

/-- Union of two regions. Needed under **either** footprint policy: a container's read set is not one
contiguous range once heap arrays and borrowed input slices are involved — `RawV4Rep` touches the root
allocation, ten separately-based heap arrays, a descriptor table and input-relative slices, and no
choice of "tight" versus "record boundary" makes those contiguous. -/
def Region.union (r1 r2 : Region) : Region := fun address => r1 address ∨ r2 address

/-- **The assembly combinator.** Two claims, each determined on its own region, are jointly determined
on the union — which is where a container footprint actually comes from.

Contrast `memDeterminedOn_and`, which requires both conjuncts on the *same* region and so forces the
caller to widen each side to cover the other. That widening is how padding enters at the assembly step,
which is exactly where `forkActivation`'s `range base 32` went wrong. -/
theorem memDeterminedOn_and_union {r1 r2 : Region} {P Q : State → Prop}
    (hp : MemDeterminedOn r1 P) (hq : MemDeterminedOn r2 Q) :
    MemDeterminedOn (Region.union r1 r2) (fun s => P s ∧ Q s) :=
  fun s1 s2 agree h =>
    ⟨hp s1 s2 (fun address ha => agree address (Or.inl ha)) h.1,
      hq s1 s2 (fun address ha => agree address (Or.inr ha)) h.2⟩

/-! ## Primitive footprints -/

theorem word64_footprint (base value : Nat) :
    MemDeterminedOn (range base 8) (fun s => Word64LERep s base value) :=
  fun _ _ agree h index hindex =>
    (agree (base + index) ⟨Nat.le_add_right _ _, by omega⟩).symm.trans (h index hindex)

theorem optionTag_footprint (base : Nat) (present : Bool) :
    MemDeterminedOn (range base 1) (fun s => OptionTagRep s base present) :=
  fun _ _ agree h => (agree base ⟨Nat.le_refl _, by omega⟩).symm.trans h

/-! ## `forkActivation`, the first container footprint

32 bytes: two `?u64`s, each an 8-byte payload with its tag at +8, at offsets 0 and 16. The two
`OptionU64Rep`s land in `[base, base+9)` and `[base+16, base+25)`, both inside `range base 32`. -/

theorem optionU64_footprint (base : Nat) (value : Option UInt64) :
    MemDeterminedOn (range base 9) (fun s => OptionU64Rep s base value) := by
  cases value with
  | none =>
      exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
        (optionTag_footprint (base + 8) false)
  | some v =>
      refine memDeterminedOn_and ?_ ?_
      · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
          (word64_footprint base v.toNat)
      · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
          (optionTag_footprint (base + 8) true)

theorem forkActivation_footprint (base : Nat) (value : SszBridge.RawForkActivation) :
    MemDeterminedOn (range base 32) (fun s => ForkActivationRep s base value) := by
  refine memDeterminedOn_and ?_ ?_
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (optionU64_footprint base value.blockNumber)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (optionU64_footprint (base + 16) value.timestamp)

/-- The footprint result as a `LocalTo` fact about the canonical representation — the form the
ownership discipline consumes. -/
theorem localTo_canonicalRepForkActivation_range32 :
    LocalTo canonicalRepForkActivation (fun base => range base 32) :=
  fun _ _ value s1 s2 base agree h => forkActivation_footprint base value s1 s2 agree h

/-- **The tight read set**, assembled through the union combinator instead of by widening both
conjuncts to a common range: `[base, base+9)` for `blockNumber` and `[base+16, base+25)` for
`timestamp`. Eighteen bytes in two runs, against the record's thirty-two.

Both this and `forkActivation_footprint` are correct; they are different policies, not a right and a
wrong answer, and `forkActivation_range32_not_tight` below measures the gap between them. -/
theorem forkActivation_footprint_tightRegion (base : Nat)
    (value : SszBridge.RawForkActivation) :
    MemDeterminedOn (Region.union (range base 9) (range (base + 16) 9))
      (fun s => ForkActivationRep s base value) :=
  memDeterminedOn_and_union (optionU64_footprint base value.blockNumber)
    (optionU64_footprint (base + 16) value.timestamp)

/-! ## Record-boundary footprints

The ruled policy. A parent discharges disjointness against what the *allocator* gave it — records, not
read sets — so record-versus-record is the fact that exists at the call site.

A record-boundary footprint **cannot have a tightness half**: its padding bytes are not load-bearing by
construction. Two obligations replace it, and both are enforced structurally here rather than by
convention.

* **Containment is a HYPOTHESIS, not a side note.** `forkActivation_footprint_record` cannot be stated
  without exhibiting the read set inside the claimed record, so a footprint that drifts free of what it
  describes does not typecheck. This is where the leaf tightness earns its keep: containment would be
  vacuous for a container whose children read nothing, and `word64_footprint_tight` /
  `optionTag_footprint_tight` are what rule that out.
* **The size is DERIVED, never a literal.** `range base 32` with a hand-written 32 is unfalsifiable —
  `range base 4096` proves just as smoothly and nothing objects. The corollary below takes its size
  from `BinaryFv.SSZ.Zesu.Artifact.fork_activation_layout`, the same compiler-reflected manifest the ABI and allocator
  use. My original 32 came off a layout *comment*, and a comment is not a constant. -/

/-- The read set: what `ForkActivationRep`'s conjuncts actually touch. -/
def forkActivationReadSet (base : Nat) : Region :=
  Region.union (range base 9) (range (base + 16) 9)

/-- **The record-boundary footprint, with containment as a proof obligation.**

`recordSize` is a parameter and `contained` must be discharged for it, so this cannot be instantiated
at an unrelated size — the containment premise is what ties the region to the representation. -/
theorem forkActivation_footprint_record (base recordSize : Nat)
    (value : SszBridge.RawForkActivation)
    (contained : ∀ address, forkActivationReadSet base address → range base recordSize address) :
    MemDeterminedOn (range base recordSize) (fun s => ForkActivationRep s base value) :=
  memDeterminedOn_mono contained (forkActivation_footprint_tightRegion base value)

/-- Containment at the manifest's record size. Discharged arithmetically against the read set rather
than assumed from the layout. -/
theorem forkActivation_readSet_contained (base : Nat) :
    ∀ address, forkActivationReadSet base address → range base 32 address := by
  rintro address (⟨hl, hr⟩ | ⟨hl, hr⟩) <;> exact ⟨by omega, by omega⟩

/-- **The footprint at the ABI-derived record size.** The `32` is obtained from
`BinaryFv.SSZ.Zesu.Artifact.fork_activation_layout` rather than written down, so a layout change surfaces here instead
of silently widening the footprint. -/
theorem forkActivation_footprint_abi (base : Nat) (value : SszBridge.RawForkActivation)
    {recordSize : Nat} (hsize : BinaryFv.SSZ.Zesu.Artifact.forkActivationSize = some recordSize) :
    MemDeterminedOn (range base recordSize) (fun s => ForkActivationRep s base value) := by
  have h32 : recordSize = 32 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.fork_activation_layout.1
    rw [hsize] at hlayout
    exact Option.some.inj hlayout
  subst h32
  exact forkActivation_footprint_record base 32 value (forkActivation_readSet_contained base)

/-! ## Tightness

The half that can fail. Soundness above would hold just as well for a padded footprint, so each
address the footprint claims must be shown to *matter*: two states agreeing everywhere except there,
disagreeing on the representation.

Proved for both primitives: `OptionTagRep` (one address, single-insert witness) and `Word64LERep`
(eight addresses, via `withBytes` below). Since every container footprint here is assembled from those
two, a padded container footprint would now have to be padded at the assembly step rather than at a
leaf — which narrows where the remaining risk can live. -/

/-- **`OptionTagRep`'s footprint address is load-bearing.** Two states differing only at `base`, one
satisfying the representation and one not.

Small, but it is the shape the rest need, and it establishes that `range base 1` is not padding. -/
theorem optionTag_footprint_tight (base : Nat) :
    ∃ s1 s2 : State,
      (∀ address, address ≠ base → s1.mem.get? address = s2.mem.get? address) ∧
        OptionTagRep s1 base true ∧ ¬ OptionTagRep s2 base true := by
  refine ⟨{ (default : State) with mem := (default : State).mem.insert base (BitVec.ofNat 8 1) },
          { (default : State) with mem := (default : State).mem.insert base (BitVec.ofNat 8 0) },
          ?_, ?_, ?_⟩
  · intro address hne
    show ((default : State).mem.insert base (BitVec.ofNat 8 1)).get? address
        = ((default : State).mem.insert base (BitVec.ofNat 8 0)).get? address
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp [Ne.symm hne]
  · show ((default : State).mem.insert base (BitVec.ofNat 8 1)).get? base
        = some (BitVec.ofNat 8 (if true then 1 else 0))
    simp [Std.ExtHashMap.get?_eq_getElem?]
  · show ¬ ((default : State).mem.insert base (BitVec.ofNat 8 0)).get? base
        = some (BitVec.ofNat 8 (if true then 1 else 0))
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp

/-! ### Multi-byte witnesses

The obstacle to tightness beyond a single address was construction: a witness must exhibit a state
that *satisfies* the representation, and an eight-byte word needs eight writes whose lookups can then
be separated. `withBytes` supplies exactly that, once, for every multi-byte footprint. -/

/-- Memory with `count` bytes written from `base`, byte `i` taking value `f i`. -/
def withBytes (m : Std.ExtHashMap Nat (BitVec 8)) (base : Nat) (f : Nat → BitVec 8) :
    Nat → Std.ExtHashMap Nat (BitVec 8)
  | 0 => m
  | n + 1 => (withBytes m base f n).insert (base + n) (f n)

theorem withBytes_inside (m : Std.ExtHashMap Nat (BitVec 8)) (base : Nat) (f : Nat → BitVec 8)
    {count i : Nat} (h : i < count) :
    (withBytes m base f count).get? (base + i) = some (f i) := by
  induction count with
  | zero => exact absurd h (by omega)
  | succ n ih =>
      show ((withBytes m base f n).insert (base + n) (f n)).get? (base + i) = some (f i)
      simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
      by_cases hi : i = n
      · subst hi; simp
      · rw [if_neg (by omega : ¬ (base + n = base + i))]
        simpa [Std.ExtHashMap.get?_eq_getElem?] using ih (by omega : i < n)

theorem withBytes_outside (m : Std.ExtHashMap Nat (BitVec 8)) (base : Nat) (f : Nat → BitVec 8)
    {count a : Nat} (h : ∀ i, i < count → a ≠ base + i) :
    (withBytes m base f count).get? a = m.get? a := by
  induction count with
  | zero => rfl
  | succ n ih =>
      show ((withBytes m base f n).insert (base + n) (f n)).get? a = m.get? a
      simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
      rw [if_neg (fun heq => h n (by omega) heq.symm)]
      simpa [Std.ExtHashMap.get?_eq_getElem?] using ih (fun i hi => h i (by omega))

/-- **Every address in a `Word64LERep`'s footprint is load-bearing.** For each of the eight bytes,
two states agreeing everywhere else and disagreeing on the representation.

This is the half that can fail, and it is what makes `word64_footprint` a claim rather than a
formality: shrink `range base 8` and soundness breaks; pad it and this breaks. Since every container
footprint here is assembled from `Word64LERep` and `OptionTagRep`, padding a container footprint would
now have to happen at the assembly step rather than at a leaf. -/
theorem word64_footprint_tight (base offset : Nat) (hoffset : offset < 8) :
    ∃ s1 s2 : State,
      (∀ address, address ≠ base + offset → s1.mem.get? address = s2.mem.get? address) ∧
        Word64LERep s1 base 0 ∧ ¬ Word64LERep s2 base 0 := by
  refine ⟨{ (default : State) with
            mem := withBytes (default : State).mem base (fun _ => BitVec.ofNat 8 0) 8 },
          { (default : State) with
            mem := (withBytes (default : State).mem base (fun _ => BitVec.ofNat 8 0) 8).insert
              (base + offset) (BitVec.ofNat 8 1) },
          ?_, ?_, ?_⟩
  · intro address hne
    show (withBytes (default : State).mem base (fun _ => BitVec.ofNat 8 0) 8).get? address
        = ((withBytes (default : State).mem base (fun _ => BitVec.ofNat 8 0) 8).insert
            (base + offset) (BitVec.ofNat 8 1)).get? address
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (fun heq => hne heq.symm)]
  · intro index hindex
    show (withBytes (default : State).mem base (fun _ => BitVec.ofNat 8 0) 8).get? (base + index)
        = some (BitVec.ofNat 8 ((0 / 256 ^ index) % 256))
    rw [withBytes_inside _ _ _ hindex]
    simp
  · intro hrep
    have h := hrep offset hoffset
    have hget : ((withBytes (default : State).mem base (fun _ => BitVec.ofNat 8 0) 8).insert
        (base + offset) (BitVec.ofNat 8 1)).get? (base + offset) = some (BitVec.ofNat 8 1) := by
      simp [Std.ExtHashMap.get?_eq_getElem?]
    rw [hget] at h
    simp at h

/-- Byte values making `ForkActivationRep` hold at a base: two zero `u64` payloads with their
presence tags at offsets 8 and 24. The bytes between are irrelevant, which is the point. -/
def forkActivationWitnessBytes : Nat → BitVec 8 :=
  fun i => if i = 8 ∨ i = 24 then BitVec.ofNat 8 1 else BitVec.ofNat 8 0

/-- **`range base 32` is genuinely padded: byte 12 is not load-bearing.** Two states differing exactly
there, both satisfying `ForkActivationRep`.

Previously this was asserted in prose — "bytes 9–15 and 25–31 are structure padding" — on the strength
of reading the conjuncts. That is the same unproved-negative shape the module warns about, so it is a
theorem now. The proof consumes `forkActivation_footprint_tightRegion`: the two states agree on the
tight read set, so the representation transports, and the byte they differ at is therefore idle. -/
theorem forkActivation_range32_not_tight (base : Nat) :
    ∃ (value : SszBridge.RawForkActivation) (s1 s2 : State),
      range base 32 (base + 12) ∧
        s1.mem.get? (base + 12) ≠ s2.mem.get? (base + 12) ∧
        ForkActivationRep s1 base value ∧ ForkActivationRep s2 base value := by
  refine ⟨⟨some 0, some 0⟩,
          { (default : State) with mem := withBytes (default : State).mem base forkActivationWitnessBytes 25 },
          { (default : State) with
            mem := (withBytes (default : State).mem base forkActivationWitnessBytes 25).insert (base + 12)
              (BitVec.ofNat 8 7) },
          ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · show (withBytes (default : State).mem base forkActivationWitnessBytes 25).get? (base + 12)
        ≠ ((withBytes (default : State).mem base forkActivationWitnessBytes 25).insert (base + 12)
            (BitVec.ofNat 8 7)).get? (base + 12)
    rw [withBytes_inside _ _ _ (by omega : 12 < 25)]
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    simp [forkActivationWitnessBytes]
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro index hindex
        show (withBytes (default : State).mem base forkActivationWitnessBytes 25).get? (base + index) = _
        rw [withBytes_inside _ _ _ (by omega : index < 25)]
        simp [forkActivationWitnessBytes, show ¬ (index = 8 ∨ index = 24) by omega]
      · show (withBytes (default : State).mem base forkActivationWitnessBytes 25).get? (base + 8) = _
        rw [withBytes_inside _ _ _ (by omega : 8 < 25)]
        simp [forkActivationWitnessBytes]
    · refine ⟨?_, ?_⟩
      · intro index hindex
        show (withBytes (default : State).mem base forkActivationWitnessBytes 25).get? (base + 16 + index) = _
        rw [show base + 16 + index = base + (16 + index) by omega,
          withBytes_inside _ _ _ (by omega : 16 + index < 25)]
        simp [forkActivationWitnessBytes, show ¬ (16 + index = 8 ∨ 16 + index = 24) by omega]
      · show (withBytes (default : State).mem base forkActivationWitnessBytes 25).get? (base + 16 + 8) = _
        rw [show base + 16 + 8 = base + 24 by omega, withBytes_inside _ _ _ (by omega : 24 < 25)]
        simp [forkActivationWitnessBytes]
  · refine forkActivation_footprint_tightRegion base ⟨some 0, some 0⟩
      { (default : State) with
        mem := withBytes (default : State).mem base forkActivationWitnessBytes 25 } _ ?_ ?_
    · rintro address (⟨hl, hr⟩ | ⟨hl, hr⟩) <;>
        · show (withBytes (default : State).mem base forkActivationWitnessBytes 25).get? address
              = ((withBytes (default : State).mem base forkActivationWitnessBytes 25).insert (base + 12)
                  (BitVec.ofNat 8 7)).get? address
          simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
          rw [if_neg (by omega)]
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro index hindex
          show (withBytes (default : State).mem base forkActivationWitnessBytes 25).get? (base + index) = _
          rw [withBytes_inside _ _ _ (by omega : index < 25)]
          simp [forkActivationWitnessBytes, show ¬ (index = 8 ∨ index = 24) by omega]
        · show (withBytes (default : State).mem base forkActivationWitnessBytes 25).get? (base + 8) = _
          rw [withBytes_inside _ _ _ (by omega : 8 < 25)]
          simp [forkActivationWitnessBytes]
      · refine ⟨?_, ?_⟩
        · intro index hindex
          show (withBytes (default : State).mem base forkActivationWitnessBytes 25).get? (base + 16 + index) = _
          rw [show base + 16 + index = base + (16 + index) by omega,
            withBytes_inside _ _ _ (by omega : 16 + index < 25)]
          simp [forkActivationWitnessBytes, show ¬ (16 + index = 8 ∨ 16 + index = 24) by omega]
        · show (withBytes (default : State).mem base forkActivationWitnessBytes 25).get? (base + 16 + 8) = _
          rw [show base + 16 + 8 = base + 24 by omega, withBytes_inside _ _ _ (by omega : 24 < 25)]
          simp [forkActivationWitnessBytes]

/-! ### What tightness is NOT yet proved for, and why it is listed rather than assumed

Both **primitives** are now tight. The **containers** are not: `ForkActivationRep`'s `range base 32`
has no witness that each of its thirty-two addresses is load-bearing, and in fact **it is not tight** —
the two `OptionU64Rep`s occupy `[base, base+9)` and `[base+16, base+25)`, so bytes `9–15` and `25–31`
are structure padding that no conjunct reads. The 32 is the ABI record size, not the read set.

That is exactly the padding the module warns about, and it is benign only because it is *deliberate*:
a footprint may legitimately over-approximate to a record boundary, provided the over-approximation is
stated rather than mistaken for tightness. What must not happen is a disjointness obligation being
discharged against `range base 32` while someone believes it was tight. The precise read set is
`range base 9 ∪ range (base+16) 9`, and a tight container footprint should be stated that way.

So the container result is named `localTo_canonicalRepForkActivation_range32`, **not** `…_tight`. It
is sound and unwitnessed, and its name now says only what it proves: the representation transports
across agreement on a 32-byte range. A `_tight` suffix would have promised the missing half, which is
the name-versus-content defect this row keeps finding — cheaper to avoid in the name than to annotate
afterwards. The suffix becomes available when the witness does. -/

end BinaryFv.SSZ.Zesu.Contracts.Footprint
