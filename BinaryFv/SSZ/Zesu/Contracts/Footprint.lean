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
ownership discipline consumes.

**Specialised at a literal 32 and therefore not the one to build on.** It is kept because the
not-tight theorem is stated against it; `localTo_canonicalRepForkActivation_record` below is the
version whose size traces to the manifest. -/
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

/-- **The form the discipline should consume: the size is never written down.** `recordSize` is
whatever the compiler-reflected manifest says `RawForkActivation` occupies, so a struct-layout change
moves the manifest and this follows, rather than the footprint quietly describing the wrong region.

The offsets need no equivalent treatment, and checking that was worth more than assuming it:
`MemoryRepresentation/Containers.lean:132`, `container_field_offsets_valid`, already pins
`RawForkActivation|block_number = 0` and `|timestamp = 16` against the same manifest by
`native_decide`. `ForkActivationRep`'s literals are audited there, at the representation layer, and
this footprint inherits the pinning by having to transport that exact representation. Re-deriving the
offsets here would be a second copy of an existing check, not new coverage. **The size was different —
nothing pinned 32 anywhere except a docstring**, which is why `fork_activation_layout` had to be
added. -/
theorem localTo_canonicalRepForkActivation_record {recordSize : Nat}
    (hsize : BinaryFv.SSZ.Zesu.Artifact.forkActivationSize = some recordSize) :
    LocalTo canonicalRepForkActivation (fun base => range base recordSize) :=
  fun _ _ value s1 s2 base agree h =>
    forkActivation_footprint_abi base value hsize s1 s2 agree h

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

/-! ## `optionU64`: the same split one level down, plus a complication the container did not have

`?u64|size = 16` in the manifest against a 9-byte read set, so `range base 9` is the read set and 16
is the record — structurally identical to `forkActivation`.

**But `optionU64`'s read set depends on the VALUE, which `forkActivation`'s did not.** At `some v` the
representation reads the payload at `[base, base+8)` and the tag at `base+8`: nine bytes, all
load-bearing. At `none` it reads **only the tag** — one byte — and `range base 9` is padded by eight.

That matters for the discipline rather than being a curiosity: a parent discharging disjointness knows
the record it allocated, not the value that ended up in it. So a value-dependent footprint is not
usable at a call site, and over-approximating past it is not laziness — it is what makes the footprint
a statement about the allocation. It is another argument for the record-boundary policy, arrived at
from a direction the ruling did not consider. -/

/-- Containment of the read set in the record. -/
theorem optionU64_readSet_contained (base : Nat) :
    ∀ address, range base 9 address → range base 16 address := by
  rintro address ⟨hl, hr⟩; exact ⟨hl, by omega⟩

/-- **The record-boundary footprint, size taken from the manifest.** `optionalU64Size` rather than a
written 16, for the same reason as `forkActivation`. -/
theorem optionU64_footprint_abi (base : Nat) (value : Option UInt64)
    {recordSize : Nat} (hsize : BinaryFv.SSZ.Zesu.Artifact.optionalU64Size = some recordSize) :
    MemDeterminedOn (range base recordSize) (fun s => OptionU64Rep s base value) := by
  have h16 : recordSize = 16 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.optional_u64_layout.1
    rw [hsize] at hlayout
    exact Option.some.inj hlayout
  subst h16
  exact memDeterminedOn_mono (optionU64_readSet_contained base) (optionU64_footprint base value)

/-- **The record footprint is padded**: byte 12 lies in `range base 16` and is read by nothing, at
either value. Same obligation as `forkActivation_range32_not_tight`, discharged the same way. -/
theorem optionU64_range16_not_tight (base : Nat) :
    ∃ (value : Option UInt64) (s1 s2 : State),
      range base 16 (base + 12) ∧
        s1.mem.get? (base + 12) ≠ s2.mem.get? (base + 12) ∧
        OptionU64Rep s1 base value ∧ OptionU64Rep s2 base value := by
  refine ⟨some 0,
          { (default : State) with
            mem := withBytes (default : State).mem base forkActivationWitnessBytes 16 },
          { (default : State) with
            mem := (withBytes (default : State).mem base forkActivationWitnessBytes 16).insert
              (base + 12) (BitVec.ofNat 8 7) },
          ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · show (withBytes (default : State).mem base forkActivationWitnessBytes 16).get? (base + 12) ≠ _
    rw [withBytes_inside _ _ _ (by omega : 12 < 16)]
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    simp [forkActivationWitnessBytes]
  · refine ⟨?_, ?_⟩
    · intro index hindex
      show (withBytes (default : State).mem base forkActivationWitnessBytes 16).get? (base + index) = _
      rw [withBytes_inside _ _ _ (by omega : index < 16)]
      simp [forkActivationWitnessBytes, show ¬ (index = 8 ∨ index = 24) by omega]
    · show (withBytes (default : State).mem base forkActivationWitnessBytes 16).get? (base + 8) = _
      rw [withBytes_inside _ _ _ (by omega : 8 < 16)]
      simp [forkActivationWitnessBytes]
  · refine optionU64_footprint base (some 0)
      { (default : State) with
        mem := withBytes (default : State).mem base forkActivationWitnessBytes 16 } _ ?_ ?_
    · rintro address ⟨hl, hr⟩
      show (withBytes (default : State).mem base forkActivationWitnessBytes 16).get? address = _
      simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
      rw [if_neg (by omega)]
    · refine ⟨?_, ?_⟩
      · intro index hindex
        show (withBytes (default : State).mem base forkActivationWitnessBytes 16).get?
            (base + index) = _
        rw [withBytes_inside _ _ _ (by omega : index < 16)]
        simp [forkActivationWitnessBytes, show ¬ (index = 8 ∨ index = 24) by omega]
      · show (withBytes (default : State).mem base forkActivationWitnessBytes 16).get? (base + 8) = _
        rw [withBytes_inside _ _ _ (by omega : 8 < 16)]
        simp [forkActivationWitnessBytes]

/-- **Even the read set is padded at `none`, and this one is not a policy choice.**

At `value = none` the representation reads only the tag, so byte 0 lies in `range base 9` and is
load-bearing for nothing. `forkActivation` had no analogue: its read set was the same shape whatever
the values were.

Recorded because it is the reason a footprint must not be stated per-value: the parent knows the
record it allocated, not what was decoded into it. -/
theorem optionU64_readSet_not_tight_at_none (base : Nat) :
    ∃ s1 s2 : State,
      range base 9 base ∧
        s1.mem.get? base ≠ s2.mem.get? base ∧
        OptionU64Rep s1 base none ∧ OptionU64Rep s2 base none := by
  refine ⟨{ (default : State) with
            mem := ((default : State).mem.insert (base + 8) (BitVec.ofNat 8 0)).insert base
              (BitVec.ofNat 8 3) },
          { (default : State) with
            mem := ((default : State).mem.insert (base + 8) (BitVec.ofNat 8 0)).insert base
              (BitVec.ofNat 8 5) },
          ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · show (((default : State).mem.insert (base + 8) (BitVec.ofNat 8 0)).insert base
        (BitVec.ofNat 8 3)).get? base ≠ _
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    simp
  · show (((default : State).mem.insert (base + 8) (BitVec.ofNat 8 0)).insert base
        (BitVec.ofNat 8 3)).get? (base + 8) = _
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (by omega)]
    simp
  · show (((default : State).mem.insert (base + 8) (BitVec.ofNat 8 0)).insert base
        (BitVec.ofNat 8 5)).get? (base + 8) = _
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (by omega)]
    simp

/-! ## The nesting containers, and where the padding actually lives

`forkConfig` (72 bytes) and `chainConfig` (80). Under the record-boundary policy each child
contributes its **record** range rather than its read set, so composition is `memDeterminedOn_and`
into the parent's record — the union combinator is not needed here, because record ranges of adjacent
fields are contiguous by construction.

**Both records are exactly packed:** `72 = 8 + 32 + 32` and `80 = 8 + 72`, confirmed against the
manifest in `Artifact.fork_chain_config_layout`. So the nesting introduces **no padding of its own** —
every padding byte in the whole chain lives inside an option leaf, where `optionU64`'s tag sits at +8
in a 16-byte record and `optionBlobSchedule`'s at +24 in a 32-byte one.

That is worth stating because it bounds the cost of the policy: the record-versus-read-set gap does
*not* compound with nesting depth, which is what I expected it to do. It is fixed at the leaves. -/

theorem blobSchedule_footprint (base : Nat) (value : SszBridge.RawBlobSchedule) :
    MemDeterminedOn (range base 24) (fun s => BlobScheduleRep s base value) := by
  refine memDeterminedOn_and ?_ (memDeterminedOn_and ?_ ?_)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩) (word64_footprint base _)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (word64_footprint (base + 8) _)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (word64_footprint (base + 16) _)

theorem optionBlobSchedule_footprint (base : Nat)
    (value : Option SszBridge.RawBlobSchedule) :
    MemDeterminedOn (range base 32) (fun s => OptionBlobScheduleRep s base value) := by
  cases value with
  | none =>
      exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
        (optionTag_footprint (base + 24) false)
  | some v =>
      refine memDeterminedOn_and ?_ ?_
      · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
          (blobSchedule_footprint base v)
      · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
          (optionTag_footprint (base + 24) true)

/-- **Containment is a real obligation here, not arithmetic.** `forkConfig` holds a `u64`, a whole
`forkActivation` record and a whole `optionBlobSchedule` record, so this is the first footprint whose
children are themselves records with their own footprints. -/
theorem forkConfig_footprint (base : Nat) (value : SszBridge.RawForkConfig) :
    MemDeterminedOn (range base 72) (fun s => ForkConfigRep s base value) := by
  refine memDeterminedOn_and ?_ (memDeterminedOn_and ?_ ?_)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩) (word64_footprint base _)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (forkActivation_footprint (base + 8) value.activation)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (optionBlobSchedule_footprint (base + 40) value.blobSchedule)

theorem chainConfig_footprint (base : Nat) (value : SszBridge.RawChainConfig) :
    MemDeterminedOn (range base 80) (fun s => ChainConfigRep s base value) := by
  refine memDeterminedOn_and ?_ ?_
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩) (word64_footprint base _)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (forkConfig_footprint (base + 8) value.activeFork)

/-- The consumable forms, sizes taken from the manifest rather than written. -/
theorem localTo_canonicalRepForkConfig_record {recordSize : Nat}
    (hsize : BinaryFv.SSZ.Zesu.Artifact.forkConfigSize = some recordSize) :
    LocalTo canonicalRepForkConfig (fun base => range base recordSize) := by
  have h72 : recordSize = 72 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.fork_chain_config_layout.1
    rw [hsize] at hlayout
    exact Option.some.inj hlayout
  subst h72
  exact fun _ _ value s1 s2 base agree h => forkConfig_footprint base value s1 s2 agree h

theorem localTo_canonicalRepChainConfig_record {recordSize : Nat}
    (hsize : BinaryFv.SSZ.Zesu.Artifact.chainConfigSize = some recordSize) :
    LocalTo canonicalRepChainConfig (fun base => range base recordSize) := by
  have h80 : recordSize = 80 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.fork_chain_config_layout.2.2.2.2.1
    rw [hsize] at hlayout
    exact Option.some.inj hlayout
  subst h80
  exact fun _ _ value s1 s2 base agree h => chainConfig_footprint base value s1 s2 agree h

/-! ## Heap-allocated children: the allocation interval

The ruled shape for the four non-chain containers and for `RawV4Rep`. A heap-allocated child's
footprint is its **record/descriptor range** together with the **allocation interval it consumed** —
and nothing else. There is no input component: `InputSliceRep` is an address equation, not a memory
claim (`subst` its first conjunct and the second becomes `x = x`), so a borrowed-input descriptor's
whole footprint is its own descriptor, which already lies inside the parent's allocation.

**The interval is a parameter, never read from the state.** That is what keeps the discipline
non-circular: a region computed from memory a sibling may write cannot guard against that sibling.
The numbers arrive from the composition — `Runtime.CursorChain` is successive cursor values, which is
the shape a composed trace already hands over.

**And that is where sibling disjointness comes from, for free.** `CursorChain.step` carries
`advances : before ≤ middle` structurally, so successive intervals cannot overlap. No appeal to the
allocator's implementation, and no extra hypothesis — which is why this works where an arena-wide
footprint does not: ten sibling arrays all allocate from one arena and would all overlap, but their
cursor intervals are pairwise disjoint by monotonicity alone. -/

/-- A half-open cursor interval: the bytes one allocation consumed. -/
def interval (before after : Nat) : Region := fun address => before ≤ address ∧ address < after

/-- What a heap-allocated child owns: its record, plus what it allocated. -/
def allocatedRegion (recordBase recordSize before after : Nat) : Region :=
  Region.union (range recordBase recordSize) (interval before after)

/-- **Allocation intervals are disjoint when the first ends at or before the second begins.**

`ordered` is what `CursorChain` supplies: successive cursor values are non-decreasing, so an earlier
allocation ends at or before a later one starts.

**Stated on four independent bounds, and it has to be.** The first version of this lemma wrote the
two intervals as `[before, middle)` and `[middle, after)` — sharing an endpoint — and carried
`before ≤ middle` as its hypothesis. That version is true, and its hypothesis is **never used**:
naming the two intervals so they meet at one point already *is* the disjointness, so the premise
about the allocator did no work while the docstring called it "the load-bearing fact of the whole
policy". The compiler said so, as an unused-variable warning, and it shipped anyway.

The repair is not to delete the hypothesis but to state the lemma where it earns its place. Adjacent
siblings need nothing; **non-adjacent** ones — field 1 against field 3, which the four-field entry
schema requires — have intervals `[c0, c1)` and `[c2, c3)` with a gap between, and there `c1 ≤ c2` is
exactly the monotonicity of the chain. The old shape could not express that case at all. -/
theorem interval_disjoint {first firstEnd second secondEnd : Nat} (ordered : firstEnd ≤ second) :
    ∀ address, interval first firstEnd address → ¬ interval second secondEnd address := by
  rintro address ⟨_, hlt⟩ ⟨hge, _⟩
  omega

/-- The adjacent instance, which is what one `CursorChain.step` hands over directly.

Separated so that the general lemma is the one carrying a hypothesis that does work, and this one is
visibly the special case that needs none — rather than the free fact wearing a premise it ignores. -/
theorem interval_disjoint_adjacent {before middle after : Nat} :
    ∀ address, interval before middle address → ¬ interval middle after address :=
  interval_disjoint (Nat.le_refl middle)

/-- **`ordered` is load-bearing, and this is the check the old statement could not run.** Drop it and
the conclusion is false: `[0, 10)` and `[5, 15)` both contain `7`.

The adjacent-only form admitted no such witness — its two intervals could not be put in the wrong
order — which is precisely why its unused hypothesis went unnoticed. A premise that cannot be
falsified is not evidence that it matters. -/
theorem interval_disjoint_needs_ordered :
    ∃ first firstEnd second secondEnd address,
      ¬ firstEnd ≤ second ∧
        interval first firstEnd address ∧ interval second secondEnd address :=
  ⟨0, 10, 5, 15, 7, by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- The same fact in the form `representation_survives_sibling` consumes.

**Three of the four cases are parent obligations, and only one is free.** Expanding
`allocatedRegion` on both sides gives record-vs-record, record-vs-interval, interval-vs-record and
interval-vs-interval. `ordered` discharges **only the last**. The other three are facts about where
the parent placed the records, and no property of the allocator supplies them:

* `records` — the two record ranges do not overlap. Placement.
* `recordBelowSibling` — the earlier child's record is not inside the later sibling's allocation.
  Non-trivial: a record placed on the heap *could* fall inside a later allocation if the parent
  reused the region.
* `siblingRecordOutside` — the later sibling's record is not inside the earlier child's allocation.
  The mirror image, and the one I initially omitted; the case analysis is what surfaced it.

So "sibling disjointness comes free from bump monotonicity" is true of the **allocations** and not of
the records. Worth stating in that form, because the free half is the memorable one and a reader who
generalises it would believe the obligation is discharged when three quarters of it is not.

And the free quarter is free for a smaller reason than it first appears — see `interval_disjoint`:
between *adjacent* siblings it needs nothing at all, and monotonicity only starts doing work between
non-adjacent ones. This lemma takes the general `ordered` so it covers both. -/
theorem allocatedRegion_disjoint_of_later {recordBase recordSize siblingBase siblingSize
    first firstEnd second secondEnd : Nat}
    (ordered : firstEnd ≤ second)
    (records : ∀ address, range recordBase recordSize address →
      ¬ range siblingBase siblingSize address)
    (recordBelowSibling : ∀ address, range recordBase recordSize address →
      ¬ interval second secondEnd address)
    (siblingRecordOutside : ∀ address, interval first firstEnd address →
      ¬ range siblingBase siblingSize address) :
    ∀ address, allocatedRegion recordBase recordSize first firstEnd address →
      ¬ allocatedRegion siblingBase siblingSize second secondEnd address := by
  rintro address (hrec | hint) (hsrec | hsint)
  · exact records address hrec hsrec
  · exact recordBelowSibling address hrec hsint
  · exact siblingRecordOutside address hint hsrec
  · exact interval_disjoint ordered address hint hsint

/-! ## Witnessed locality: when the read set is not a function of the base

`Ownership.LocalTo` takes `region : Nat → Region` — the read set as a function of the result base.
That fits every container whose fields sit at fixed offsets, and **fails for the four whose heap
arrays are at allocator-chosen bases bound existentially inside the representation**. No bounded
region computed from `base` can cover a witness `base` does not determine.

**The fix needs no new definition**, which is worth saying because I expected it to. `MemDeterminedOn`
already takes an arbitrary `Region`, so the caller — the composition, which allocated the arrays and
therefore holds their bases — supplies the region directly. What was missing is only the composition
lemma stated against an arbitrary region rather than against `LocalTo`'s base-indexed family.

So this is an **addition beside** `Ownership.representation_survives_sibling`, not a change to it. The
approved core keeps its shape and gains a sibling for the case it cannot express.

**The general pattern, since this is its second instance:** the read set is not a function of the
thing you would expect to determine it. At `optionU64` it depended on the *value*, which the caller
does not know; here it depends on the *allocation*, which the base does not determine. Both resolve
the same way — supply the missing determinant as a parameter, from whoever actually knows it. -/

/-- **The composition lemma for a witnessed footprint.** Identical in force to
`Ownership.representation_survives_sibling`, but the earlier child's region is supplied by the caller
rather than computed from its result base — so it can name allocator-chosen addresses.

`confined` is `MemDeterminedOn` at that region, which is exactly what the container footprint theorems
produce once their existential witnesses are destructured. -/
theorem representation_survives_sibling_witnessed {α : Type} {rep : ContainerRepresentation α}
    {region ownedSibling : Region} {s1 s2 : State}
    {base resultBase : Nat} {bytes : ByteArray} {value : α}
    (confined : MemDeterminedOn region (fun s => rep base bytes value s resultBase))
    (disjoint : ∀ address, region address → ¬ ownedSibling address)
    (writes : WritesOnlyWithin ownedSibling s1 s2)
    (established : rep base bytes value s1 resultBase) :
    rep base bytes value s2 resultBase :=
  confined s1 s2 (fun address hregion => (writes address (disjoint address hregion)).symm) established

/-- The witnessed form subsumes the base-indexed one: a `LocalTo` fact is a witnessed fact whose
region happens to be computable from the result base. Recorded so the two are known to be one
mechanism rather than two, and so a future consumer can be written against the witnessed form alone. -/
theorem memDeterminedOn_of_localTo {α : Type} {rep : ContainerRepresentation α}
    {region : Nat → Region} (local_ : LocalTo rep region)
    (base : Nat) (bytes : ByteArray) (value : α) (resultBase : Nat) :
    MemDeterminedOn (region resultBase) (fun s => rep base bytes value s resultBase) :=
  fun s1 s2 agree => local_ base bytes value s1 s2 resultBase agree

/-! # The heap layer

Everything above works at the chain containers, whose fields sit at fixed offsets from one base. The
four remaining containers and `RawV4Rep` instead hold *heap arrays*: a slice descriptor pointing at an
allocator-chosen base, a `HeapArrayRep` asserting the array's bytes exist, and a contents
representation pinning the records inside it. This section computes the footprints of that layer, and
it is the foundation the container footprints will be assembled from — so it carries its power half
rather than deferring it.

## Two leaf footprints the chain layer did not need

`FixedByteVectorRep` and `BitVectorLERep` are the remaining primitives. Both are pointwise value
claims like `Word64LERep`, so both are `range base <width>`.

## The finding: at this layer the record-versus-read-set gap CLOSES

At the chain layer a record footprint strictly over-approximates its read set — that is what
`forkActivation_range32_not_tight` and `optionU64_range16_not_tight` measure, and the earlier result
was that every padding byte in the chain lives inside an option leaf.

Two of the four heap record shapes are padded the same way (`RawWithdrawal` reads 44 of 48 bytes,
`RawWithdrawalRequest` 76 of 80; `RawConsolidationRequest` and `RawDepositRequest` are exactly
packed). **But the padding is not idle in the representation the containers actually use.** Every
container conjoins `HeapArrayRep`, which claims each byte of `count * elementSize` is *present*,
padding included. So the pair is tight over the whole stride even where the contents representation
alone is not — `heapWithdrawalArray_with_presence_tight` below proves exactly that.

That bounds the policy's cost a second time, and in the opposite direction from the chain-layer
result: there the record boundary cost real padding and the bound was that nesting does not compound
it; here the record boundary costs nothing at all.

**So the policy's cost is layer-dependent, and neither layer's experience predicts the other's.** The
chain layer's padding comes from option leaves — a tag at +8 in a 16-byte record — and is idle because
nothing else claims those bytes. The heap layer's records are padded too, by the same kind of
alignment, and it costs nothing only because a *different conjunct* happens to claim every byte. That
is a fact about how these representations are written, not a consequence of being a record, and it
has to be looked at again for each layer rather than generalised from either. `ExecutionRequests`
below is a third answer: its record has no padding at all. -/

theorem fixedByteVector_footprint {length : Nat} (base : Nat)
    (value : SszBridge.RawByteVector length) :
    MemDeterminedOn (range base length) (fun s => FixedByteVectorRep s base value) :=
  fun _ _ agree h index hindex =>
    (agree (base + index) ⟨Nat.le_add_right _ _, by omega⟩).symm.trans (h index hindex)

theorem bitVectorLE_footprint {width : Nat} (base : Nat) (value : BitVec width) :
    MemDeterminedOn (range base (width / 8)) (fun s => BitVectorLERep s base value) :=
  fun _ _ agree h index hindex =>
    (agree (base + index) ⟨Nat.le_add_right _ _, by omega⟩).symm.trans (h index hindex)

/-- **The array's own footprint.** `HeapArrayRep` claims presence rather than a value, but presence is
still a claim about `get?` at a named address, so it transports the same way.

Unlike every other footprint in this module this one is **tight by construction**: the region is
exactly the set of addresses the definition quantifies over. `heapArray_footprint_tight` proves it. -/
theorem heapArray_footprint (base count elementSize : Nat) :
    MemDeterminedOn (range base (count * elementSize))
      (fun s => HeapArrayRep s base count elementSize) :=
  fun _ _ agree h =>
    ⟨h.1, fun index hindex =>
      (agree (base + index) ⟨Nat.le_add_right _ _, by omega⟩) ▸ h.2 index hindex⟩

theorem heapFixedVectorArray_footprint {length : Nat} (base : Nat)
    (values : Array (SszBridge.RawByteVector length)) :
    MemDeterminedOn (range base (length * values.size))
      (fun s => HeapFixedVectorArrayRep s base values) := by
  intro s1 s2 agree h index hindex
  have hstride : length * index + length ≤ length * values.size := by
    have hle : length * (index + 1) ≤ length * values.size :=
      Nat.mul_le_mul_left length (by omega)
    rw [Nat.mul_succ] at hle
    exact hle
  exact fixedByteVector_footprint (base + length * index) values[index] s1 s2
    (fun address ⟨hl, hr⟩ => agree address ⟨by omega, by omega⟩) (h index hindex)

/-! ## The four heap record shapes

Each is a conjunction of `Word64LERep` and `FixedByteVectorRep` at fixed offsets, so each read set is
one contiguous run starting at the record base. The runs are computed here rather than assumed:

| record | read set | ABI record size | padding |
| --- | --- | --- | --- |
| `RawWithdrawal` | 44 | 48 | 4 |
| `RawWithdrawalRequest` | 76 | 80 | 4 |
| `RawConsolidationRequest` | 116 | 116 | none |
| `RawDepositRequest` | 192 | 192 | none |

The read-set footprints come first and the record footprints widen to them, so the containment is a
proof rather than a restatement. -/

theorem rawWithdrawal_footprint_readSet (base : Nat) (value : SszBridge.RawWithdrawal) :
    MemDeterminedOn (range base 44) (fun s => RawWithdrawalRep s base value) := by
  refine memDeterminedOn_and ?_ (memDeterminedOn_and ?_ (memDeterminedOn_and ?_ ?_))
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩) (word64_footprint base _)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (word64_footprint (base + 8) _)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (word64_footprint (base + 16) _)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (fixedByteVector_footprint (base + 24) value.address)

theorem rawWithdrawal_footprint (base : Nat) (value : SszBridge.RawWithdrawal) :
    MemDeterminedOn (range base 48) (fun s => RawWithdrawalRep s base value) :=
  memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
    (rawWithdrawal_footprint_readSet base value)

theorem rawWithdrawalRequest_footprint_readSet (base : Nat)
    (value : SszBridge.RawWithdrawalRequest) :
    MemDeterminedOn (range base 76) (fun s => RawWithdrawalRequestRep s base value) := by
  refine memDeterminedOn_and ?_ (memDeterminedOn_and ?_ ?_)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩) (word64_footprint base _)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (fixedByteVector_footprint (base + 8) value.sourceAddress)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (fixedByteVector_footprint (base + 28) value.validatorPubkey)

theorem rawWithdrawalRequest_footprint (base : Nat) (value : SszBridge.RawWithdrawalRequest) :
    MemDeterminedOn (range base 80) (fun s => RawWithdrawalRequestRep s base value) :=
  memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
    (rawWithdrawalRequest_footprint_readSet base value)

/-- Exactly packed: `20 + 48 + 48 = 116`, the ABI record size. So this footprint *is* the read set,
and there is no `_not_tight` companion to write. -/
theorem rawConsolidationRequest_footprint (base : Nat)
    (value : SszBridge.RawConsolidationRequest) :
    MemDeterminedOn (range base 116) (fun s => RawConsolidationRequestRep s base value) := by
  refine memDeterminedOn_and ?_ (memDeterminedOn_and ?_ ?_)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (fixedByteVector_footprint base value.sourceAddress)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (fixedByteVector_footprint (base + 20) value.sourcePubkey)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (fixedByteVector_footprint (base + 68) value.targetPubkey)

/-- Exactly packed: `8 + 8 + 48 + 32 + 96 = 192`. -/
theorem rawDepositRequest_footprint (base : Nat) (value : SszBridge.RawDepositRequest) :
    MemDeterminedOn (range base 192) (fun s => RawDepositRequestRep s base value) := by
  refine memDeterminedOn_and ?_ (memDeterminedOn_and ?_ (memDeterminedOn_and ?_
    (memDeterminedOn_and ?_ ?_)))
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩) (word64_footprint base _)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (word64_footprint (base + 8) _)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (fixedByteVector_footprint (base + 16) value.pubkey)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (fixedByteVector_footprint (base + 64) value.withdrawalCredentials)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (fixedByteVector_footprint (base + 96) value.signature)

/-! ## The record arrays

Each element footprint lands inside `range base (stride * count)` because `stride * index + stride =
stride * (index + 1) ≤ stride * count`. With a literal stride that is linear arithmetic, so `omega`
discharges it; `heapFixedVectorArray_footprint` above needed `Nat.mul_succ` only because its stride is
a variable. -/

theorem heapWithdrawalArray_footprint (base : Nat) (values : Array SszBridge.RawWithdrawal) :
    MemDeterminedOn (range base (48 * values.size))
      (fun s => HeapWithdrawalArrayRep s base values) := by
  intro s1 s2 agree h index hindex
  have hstride : 48 * index + 48 ≤ 48 * values.size := by
    have hle : 48 * (index + 1) ≤ 48 * values.size := Nat.mul_le_mul_left 48 (by omega)
    omega
  exact rawWithdrawal_footprint (base + 48 * index) values[index] s1 s2
    (fun address ⟨hl, hr⟩ => agree address ⟨by omega, by omega⟩) (h index hindex)

theorem heapWithdrawalRequestArray_footprint (base : Nat)
    (values : Array SszBridge.RawWithdrawalRequest) :
    MemDeterminedOn (range base (80 * values.size))
      (fun s => HeapWithdrawalRequestArrayRep s base values) := by
  intro s1 s2 agree h index hindex
  have hstride : 80 * index + 80 ≤ 80 * values.size := by
    have hle : 80 * (index + 1) ≤ 80 * values.size := Nat.mul_le_mul_left 80 (by omega)
    omega
  exact rawWithdrawalRequest_footprint (base + 80 * index) values[index] s1 s2
    (fun address ⟨hl, hr⟩ => agree address ⟨by omega, by omega⟩) (h index hindex)

theorem heapConsolidationRequestArray_footprint (base : Nat)
    (values : Array SszBridge.RawConsolidationRequest) :
    MemDeterminedOn (range base (116 * values.size))
      (fun s => HeapConsolidationRequestArrayRep s base values) := by
  intro s1 s2 agree h index hindex
  have hstride : 116 * index + 116 ≤ 116 * values.size := by
    have hle : 116 * (index + 1) ≤ 116 * values.size := Nat.mul_le_mul_left 116 (by omega)
    omega
  exact rawConsolidationRequest_footprint (base + 116 * index) values[index] s1 s2
    (fun address ⟨hl, hr⟩ => agree address ⟨by omega, by omega⟩) (h index hindex)

theorem heapDepositRequestArray_footprint (base : Nat)
    (values : Array SszBridge.RawDepositRequest) :
    MemDeterminedOn (range base (192 * values.size))
      (fun s => HeapDepositRequestArrayRep s base values) := by
  intro s1 s2 agree h index hindex
  have hstride : 192 * index + 192 ≤ 192 * values.size := by
    have hle : 192 * (index + 1) ≤ 192 * values.size := Nat.mul_le_mul_left 192 (by omega)
    omega
  exact rawDepositRequest_footprint (base + 192 * index) values[index] s1 s2
    (fun address ⟨hl, hr⟩ => agree address ⟨by omega, by omega⟩) (h index hindex)

/-! ## The strides, taken from the manifest

The literal strides above appear in the *representations* (`HeapWithdrawalArrayRep` is defined with
`base + 48 * index`) and are already pinned there by `Artifact.raw_v4_heap_element_sizes_valid`. That
pinning does **not** carry to the region, for the same reason `range base 4096` proves as easily as
`range base 32`: a footprint may over-state its size and nothing objects. So the consumable forms take
the stride from `Artifact.heap_element_size_layout` instead. -/

theorem rawWithdrawal_footprint_abi (base : Nat) (value : SszBridge.RawWithdrawal)
    {recordSize : Nat} (hsize : BinaryFv.SSZ.Zesu.Artifact.rawWithdrawalSize = some recordSize) :
    MemDeterminedOn (range base recordSize) (fun s => RawWithdrawalRep s base value) := by
  have h48 : recordSize = 48 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.heap_element_size_layout.1
    rw [hsize] at hlayout
    exact Option.some.inj hlayout
  subst h48
  exact rawWithdrawal_footprint base value

theorem heapWithdrawalArray_footprint_abi (base : Nat) (values : Array SszBridge.RawWithdrawal)
    {elementSize : Nat} (hsize : BinaryFv.SSZ.Zesu.Artifact.rawWithdrawalSize = some elementSize) :
    MemDeterminedOn (range base (elementSize * values.size))
      (fun s => HeapWithdrawalArrayRep s base values) := by
  have h48 : elementSize = 48 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.heap_element_size_layout.1
    rw [hsize] at hlayout
    exact Option.some.inj hlayout
  subst h48
  exact heapWithdrawalArray_footprint base values

theorem heapWithdrawalRequestArray_footprint_abi (base : Nat)
    (values : Array SszBridge.RawWithdrawalRequest) {elementSize : Nat}
    (hsize : BinaryFv.SSZ.Zesu.Artifact.rawWithdrawalRequestSize = some elementSize) :
    MemDeterminedOn (range base (elementSize * values.size))
      (fun s => HeapWithdrawalRequestArrayRep s base values) := by
  have h80 : elementSize = 80 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.heap_element_size_layout.2.2.1
    rw [hsize] at hlayout
    exact Option.some.inj hlayout
  subst h80
  exact heapWithdrawalRequestArray_footprint base values

theorem heapConsolidationRequestArray_footprint_abi (base : Nat)
    (values : Array SszBridge.RawConsolidationRequest) {elementSize : Nat}
    (hsize : BinaryFv.SSZ.Zesu.Artifact.rawConsolidationRequestSize = some elementSize) :
    MemDeterminedOn (range base (elementSize * values.size))
      (fun s => HeapConsolidationRequestArrayRep s base values) := by
  have h116 : elementSize = 116 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.heap_element_size_layout.2.2.2
    rw [hsize] at hlayout
    exact Option.some.inj hlayout
  subst h116
  exact heapConsolidationRequestArray_footprint base values

theorem heapDepositRequestArray_footprint_abi (base : Nat)
    (values : Array SszBridge.RawDepositRequest) {elementSize : Nat}
    (hsize : BinaryFv.SSZ.Zesu.Artifact.rawDepositRequestSize = some elementSize) :
    MemDeterminedOn (range base (elementSize * values.size))
      (fun s => HeapDepositRequestArrayRep s base values) := by
  have h192 : elementSize = 192 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.heap_element_size_layout.2.1
    rw [hsize] at hlayout
    exact Option.some.inj hlayout
  subst h192
  exact heapDepositRequestArray_footprint base values

/-- **One declaration reaching every manifest-derived footprint in this layer.**

The content is nothing new — it is the five `_abi` results conjoined. Its purpose is the axiom-hygiene
guard: an anchor's coverage is whatever that one declaration reaches, so anchoring a single theorem
leaves a door added to any of its siblings invisible. The chain layer already needed two anchors for
one door, and per-theorem anchoring does not survive `RawV4Rep`.

Offered as a candidate answer to the open anchor-collapse question rather than a decision on it — the
question is whether a *layer* can be anchored at one declaration, and a conjunction that reaches the
whole layer is the cheapest way to make that true. Whether the discipline adopts it is not this
module's call. -/
theorem heapLayer_footprints_abi (base : Nat) (withdrawal : SszBridge.RawWithdrawal)
    (withdrawals : Array SszBridge.RawWithdrawal)
    (withdrawalRequests : Array SszBridge.RawWithdrawalRequest)
    (consolidations : Array SszBridge.RawConsolidationRequest)
    (deposits : Array SszBridge.RawDepositRequest) {sizeW sizeR sizeC sizeD : Nat}
    (hw : BinaryFv.SSZ.Zesu.Artifact.rawWithdrawalSize = some sizeW)
    (hr : BinaryFv.SSZ.Zesu.Artifact.rawWithdrawalRequestSize = some sizeR)
    (hc : BinaryFv.SSZ.Zesu.Artifact.rawConsolidationRequestSize = some sizeC)
    (hd : BinaryFv.SSZ.Zesu.Artifact.rawDepositRequestSize = some sizeD) :
    MemDeterminedOn (range base sizeW) (fun s => RawWithdrawalRep s base withdrawal) ∧
      MemDeterminedOn (range base (sizeW * withdrawals.size))
        (fun s => HeapWithdrawalArrayRep s base withdrawals) ∧
      MemDeterminedOn (range base (sizeR * withdrawalRequests.size))
        (fun s => HeapWithdrawalRequestArrayRep s base withdrawalRequests) ∧
      MemDeterminedOn (range base (sizeC * consolidations.size))
        (fun s => HeapConsolidationRequestArrayRep s base consolidations) ∧
      MemDeterminedOn (range base (sizeD * deposits.size))
        (fun s => HeapDepositRequestArrayRep s base deposits) :=
  ⟨rawWithdrawal_footprint_abi base withdrawal hw,
    heapWithdrawalArray_footprint_abi base withdrawals hw,
    heapWithdrawalRequestArray_footprint_abi base withdrawalRequests hr,
    heapConsolidationRequestArray_footprint_abi base consolidations hc,
    heapDepositRequestArray_footprint_abi base deposits hd⟩

/-! ## The power half

Witnesses for this layer need something the chain-layer witnesses did not: a byte that is genuinely
**absent**. `HeapArrayRep` claims presence, so the only way to break it is to remove a byte, and the
only base memory that supplies absence is `∅`.

That also retires a hazard the chain-layer witnesses carried. Those started from
`(default : State).mem`, which nothing asserts is empty — two drafts silently depended on it being so
and had to be rewritten to write every byte they named. Starting from `∅` makes the dependency a
theorem instead of an assumption. -/

/-- Memory holding `count` zero bytes from `base`, and nothing anywhere else. -/
def zeroBytes (base count : Nat) : Std.ExtHashMap Nat (BitVec 8) :=
  withBytes ∅ base (fun _ => BitVec.ofNat 8 0) count

theorem zeroBytes_inside {base count index : Nat} (h : index < count) :
    (zeroBytes base count).get? (base + index) = some (BitVec.ofNat 8 0) :=
  withBytes_inside _ _ _ h

theorem zeroBytes_outside {base count address : Nat}
    (h : ∀ index, index < count → address ≠ base + index) :
    (zeroBytes base count).get? address = none := by
  rw [zeroBytes, withBytes_outside _ _ _ h]
  simp [Std.ExtHashMap.get?_eq_getElem?]

/-- Any all-zero byte run satisfies `Word64LERep … 0` at any offset it covers. -/
theorem word64_of_zeroBytes {s : State} {base count offset : Nat}
    (bytes : ∀ index, index < count → s.mem.get? (base + index) = some (BitVec.ofNat 8 0))
    (fits : offset + 8 ≤ count) : Word64LERep s (base + offset) 0 := by
  intro index hindex
  rw [show base + offset + index = base + (offset + index) by omega,
    bytes (offset + index) (by omega)]
  simp

/-- The same for a zero fixed-width vector. -/
theorem fixedByteVector_of_zeroBytes {s : State} {base count offset length : Nat}
    (bytes : ∀ index, index < count → s.mem.get? (base + index) = some (BitVec.ofNat 8 0))
    (fits : offset + length ≤ count) :
    FixedByteVectorRep s (base + offset) (Vector.replicate length 0) := by
  intro index hindex
  rw [show base + offset + index = base + (offset + index) by omega,
    bytes (offset + index) (by omega)]
  simp

/-- **Every address of `range base (count * elementSize)` is load-bearing for `HeapArrayRep`.**

Uniform in `offset`, not a single-address exhibit: the statement quantifies over every byte the
footprint claims. So `heapArray_footprint` is exactly tight — shrink the region and soundness breaks,
widen it and this breaks.

That matters more than a leaf tightness result, because `HeapArrayRep` is the conjunct every heap
container carries, and it is what makes the record-boundary footprint tight at this layer
(`heapWithdrawalArray_with_presence_tight`). -/
theorem heapArray_footprint_tight (base count elementSize offset : Nat)
    (hoffset : offset < count * elementSize) (hwrap : base + count * elementSize ≤ 2 ^ 64) :
    ∃ s1 s2 : State,
      (∀ address, address ≠ base + offset → s1.mem.get? address = s2.mem.get? address) ∧
        HeapArrayRep s1 base count elementSize ∧ ¬ HeapArrayRep s2 base count elementSize := by
  refine ⟨{ (default : State) with mem := zeroBytes base (count * elementSize) },
          { (default : State) with
            mem := (zeroBytes base (count * elementSize)).erase (base + offset) },
          ?_, ⟨hwrap, ?_⟩, ?_⟩
  · intro address hne
    show (zeroBytes base (count * elementSize)).get? address
        = ((zeroBytes base (count * elementSize)).erase (base + offset)).get? address
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_erase, beq_iff_eq]
    rw [if_neg (fun heq => hne heq.symm)]
  · intro index hindex
    show ((zeroBytes base (count * elementSize)).get? (base + index)).isSome
    rw [zeroBytes_inside hindex]
    rfl
  · intro hrep
    have hsome := hrep.2 offset hoffset
    have hnone : ((zeroBytes base (count * elementSize)).erase (base + offset)).get?
        (base + offset) = none := by
      simp [Std.ExtHashMap.get?_eq_getElem?]
    rw [show ({ (default : State) with
        mem := (zeroBytes base (count * elementSize)).erase (base + offset) } : State).mem.get?
          (base + offset) = _ from hnone] at hsome
    exact absurd hsome (by simp)

/-- The tightness hypotheses are satisfiable, so the result above is not an existential under
premises that cannot all hold. One line, and the recurring defect in this row is exactly a statement
nobody checked could apply. -/
theorem heapArray_footprint_tight_hypotheses_satisfiable :
    ∃ base count elementSize offset : Nat,
      offset < count * elementSize ∧ base + count * elementSize ≤ 2 ^ 64 :=
  ⟨0, 1, 1, 0, by omega, by decide⟩

/-! ### The two padded record shapes

`RawWithdrawal` reads 44 of its 48 bytes and `RawWithdrawalRequest` 76 of its 80, so each has four
tail bytes no conjunct touches. Both are witnessed rather than asserted, for the reason the chain
layer learned the hard way: an unproved negative in a module about unproved negatives.

The witnesses are cleaner than the chain-layer ones because `∅` supplies absence directly — the two
states differ at the padding byte as `none` against `some 7`, with no ambient memory to reason
about. -/

/-- Every field zero, so every byte of the 44-byte read set is `0x00`. -/
def zeroWithdrawal : SszBridge.RawWithdrawal where
  index := 0
  validatorIndex := 0
  address := Vector.replicate 20 0
  amount := 0

theorem zeroWithdrawal_rep {s : State} {base count : Nat}
    (bytes : ∀ index, index < count → s.mem.get? (base + index) = some (BitVec.ofNat 8 0))
    (fits : 44 ≤ count) : RawWithdrawalRep s base zeroWithdrawal := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact word64_of_zeroBytes (offset := 0) bytes (by omega)
  · exact word64_of_zeroBytes (offset := 8) bytes (by omega)
  · exact word64_of_zeroBytes (offset := 16) bytes (by omega)
  · exact fixedByteVector_of_zeroBytes (offset := 24) (length := 20) bytes (by omega)

/-- **`range base 48` is genuinely padded: byte 44 is not load-bearing.** -/
theorem rawWithdrawal_range48_not_tight (base : Nat) :
    ∃ (value : SszBridge.RawWithdrawal) (s1 s2 : State),
      range base 48 (base + 44) ∧
        s1.mem.get? (base + 44) ≠ s2.mem.get? (base + 44) ∧
        RawWithdrawalRep s1 base value ∧ RawWithdrawalRep s2 base value := by
  refine ⟨zeroWithdrawal,
          { (default : State) with mem := zeroBytes base 44 },
          { (default : State) with
            mem := (zeroBytes base 44).insert (base + 44) (BitVec.ofNat 8 7) },
          ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · show (zeroBytes base 44).get? (base + 44)
        ≠ ((zeroBytes base 44).insert (base + 44) (BitVec.ofNat 8 7)).get? (base + 44)
    rw [zeroBytes_outside (fun index hindex => by omega)]
    simp [Std.ExtHashMap.get?_eq_getElem?]
  · exact zeroWithdrawal_rep (fun index hindex => zeroBytes_inside hindex) (by omega)
  · refine zeroWithdrawal_rep (count := 44) (fun index hindex => ?_) (by omega)
    show ((zeroBytes base 44).insert (base + 44) (BitVec.ofNat 8 7)).get? (base + index) = _
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (by omega)]
    simpa [Std.ExtHashMap.get?_eq_getElem?] using zeroBytes_inside (base := base) hindex

/-- Every field zero, so every byte of the 76-byte read set is `0x00`. -/
def zeroWithdrawalRequest : SszBridge.RawWithdrawalRequest where
  sourceAddress := Vector.replicate 20 0
  validatorPubkey := Vector.replicate 48 0
  amount := 0

theorem zeroWithdrawalRequest_rep {s : State} {base count : Nat}
    (bytes : ∀ index, index < count → s.mem.get? (base + index) = some (BitVec.ofNat 8 0))
    (fits : 76 ≤ count) : RawWithdrawalRequestRep s base zeroWithdrawalRequest := by
  refine ⟨?_, ?_, ?_⟩
  · exact word64_of_zeroBytes (offset := 0) bytes (by omega)
  · exact fixedByteVector_of_zeroBytes (offset := 8) (length := 20) bytes (by omega)
  · exact fixedByteVector_of_zeroBytes (offset := 28) (length := 48) bytes (by omega)

/-- **`range base 80` is genuinely padded: byte 76 is not load-bearing.** -/
theorem rawWithdrawalRequest_range80_not_tight (base : Nat) :
    ∃ (value : SszBridge.RawWithdrawalRequest) (s1 s2 : State),
      range base 80 (base + 76) ∧
        s1.mem.get? (base + 76) ≠ s2.mem.get? (base + 76) ∧
        RawWithdrawalRequestRep s1 base value ∧ RawWithdrawalRequestRep s2 base value := by
  refine ⟨zeroWithdrawalRequest,
          { (default : State) with mem := zeroBytes base 76 },
          { (default : State) with
            mem := (zeroBytes base 76).insert (base + 76) (BitVec.ofNat 8 7) },
          ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · show (zeroBytes base 76).get? (base + 76)
        ≠ ((zeroBytes base 76).insert (base + 76) (BitVec.ofNat 8 7)).get? (base + 76)
    rw [zeroBytes_outside (fun index hindex => by omega)]
    simp [Std.ExtHashMap.get?_eq_getElem?]
  · exact zeroWithdrawalRequest_rep (fun index hindex => zeroBytes_inside hindex) (by omega)
  · refine zeroWithdrawalRequest_rep (count := 76) (fun index hindex => ?_) (by omega)
    show ((zeroBytes base 76).insert (base + 76) (BitVec.ofNat 8 7)).get? (base + index) = _
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (by omega)]
    simpa [Std.ExtHashMap.get?_eq_getElem?] using zeroBytes_inside (base := base) hindex

/-- **The padding is not idle in the representation the containers actually use.**

`ExecutionPayloadRep` states `HeapArrayRep … 48 ∧ HeapWithdrawalArrayRep …`, never the contents alone.
`rawWithdrawal_range48_not_tight` shows the contents leave bytes 44–47 of each element idle; this
shows the **pair** reads every byte of `range base (48 * count)`, padding included, because
`HeapArrayRep` claims presence there.

So the record-boundary policy — which costs real padding at the chain layer — costs nothing at the
heap layer. Stated at one element, since interior padding repeats per element and a witness at
element zero is a witness at the stride. -/
theorem heapWithdrawalArray_with_presence_tight (base offset : Nat) (hoffset : offset < 48)
    (hwrap : base + 48 ≤ 2 ^ 64) :
    ∃ (values : Array SszBridge.RawWithdrawal) (s1 s2 : State),
      values.size = 1 ∧ range base (48 * values.size) (base + offset) ∧
        (∀ address, address ≠ base + offset → s1.mem.get? address = s2.mem.get? address) ∧
        (HeapArrayRep s1 base values.size 48 ∧ HeapWithdrawalArrayRep s1 base values) ∧
        ¬ (HeapArrayRep s2 base values.size 48 ∧ HeapWithdrawalArrayRep s2 base values) := by
  refine ⟨#[zeroWithdrawal],
          { (default : State) with mem := zeroBytes base 48 },
          { (default : State) with mem := (zeroBytes base 48).erase (base + offset) },
          rfl, ⟨Nat.le_add_right _ _, by simpa using hoffset⟩, ?_, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro address hne
    show (zeroBytes base 48).get? address
        = ((zeroBytes base 48).erase (base + offset)).get? address
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_erase, beq_iff_eq]
    rw [if_neg (fun heq => hne heq.symm)]
  · simpa using hwrap
  · intro index hindex
    show ((zeroBytes base 48).get? (base + index)).isSome
    rw [zeroBytes_inside (by simpa using hindex : index < 48)]
    rfl
  · intro index hindex
    have hone : index < 1 := by simpa using hindex
    have hzero : index = 0 := by omega
    subst hzero
    show RawWithdrawalRep _ (base + 48 * 0) _
    rw [show base + 48 * 0 = base by omega]
    exact zeroWithdrawal_rep (count := 48) (fun index hindex => zeroBytes_inside hindex) (by omega)
  · rintro ⟨harray, -⟩
    have hsome := harray.2 offset (by simpa using hoffset)
    have hnone : ((zeroBytes base 48).erase (base + offset)).get? (base + offset) = none := by
      simp [Std.ExtHashMap.get?_eq_getElem?]
    rw [show ({ (default : State) with mem := (zeroBytes base 48).erase (base + offset) }
        : State).mem.get? (base + offset) = _ from hnone] at hsome
    exact absurd hsome (by simp)

/-! # The container layer

`ExecutionRequests` first: three slice descriptors, three heap arrays, no borrowed input slices. That
is the machinery unconfounded — every ingredient the four allocating containers need, and none of the
input aliasing that only `ExecutionWitness` and above introduce.

## Why the statement has this shape, and why the two obvious ones do not work

`Ownership.LocalTo` takes `region : Nat → Region`, the read set as a function of the result base. Here
the read set includes three allocator-chosen array bases, bound **existentially inside the
representation**. So:

* **The witnesses cannot be theorem parameters.** A caller holds a *proof* that the representation
  holds, not three numbers. A theorem taking `depositsBase` as an argument would be asking the caller
  for something it does not have and cannot compute.
* **The region cannot be a function of `base`.** No bounded region derived from `base` covers a
  witness `base` does not determine — `Footprint.representation_survives_sibling_witnessed` exists
  precisely for this case.

What works is to take the representation at `s1` as a hypothesis, **extract** the witnesses from it,
and return a transport valid at every `s2` agreeing on the region they name. The caller then owes
disjointness against bases it received rather than bases it guessed. -/

theorem sliceDescriptor_footprint (base data count : Nat) :
    MemDeterminedOn (range base 16) (fun s => SliceDescriptorRep s base data count) := by
  refine memDeterminedOn_and memDeterminedOn_const
    (memDeterminedOn_and memDeterminedOn_const (memDeterminedOn_and ?_ ?_))
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩) (word64_footprint base data)
  · exact memDeterminedOn_mono (fun _ ⟨hl, hr⟩ => ⟨by omega, by omega⟩)
      (word64_footprint (base + 8) count)

/-- **The 48-byte record is exactly its three descriptor ranges, with nothing left over.**

An `↔`, not an inclusion: the reverse direction is containment and would hold for any record size at
least 48, but the forward direction fails the moment the record has a byte no descriptor covers. So
this is the statement that would break if `RawExecutionRequests` were padded, which is what makes
"there is no padding in this record" checkable instead of prose.

It matters because the chain layer's record footprints all *were* padded. Nothing about being a
record implies being packed; it has to be looked at each time. -/
theorem executionRequests_record_exactly_covered (base : Nat) :
    ∀ address, range base 48 address ↔
      (range base 16 address ∨ range (base + 16) 16 address ∨ range (base + 32) 16 address) := by
  intro address
  constructor
  · rintro ⟨hl, hr⟩
    by_cases hfirst : address < base + 16
    · exact Or.inl ⟨by omega, by omega⟩
    · by_cases hsecond : address < base + 32
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  · rintro (⟨hl, hr⟩ | ⟨hl, hr⟩ | ⟨hl, hr⟩) <;> exact ⟨by omega, by omega⟩

/-- A zero slice descriptor: null pointer, zero count. Both side conditions (`< 2 ^ 64`) hold. -/
theorem sliceDescriptorZero_rep {s : State} {base count : Nat}
    (bytes : ∀ index, index < count → s.mem.get? (base + index) = some (BitVec.ofNat 8 0))
    (fits : 16 ≤ count) : SliceDescriptorRep s base 0 0 :=
  ⟨by decide, by decide, word64_of_zeroBytes (offset := 0) bytes (by omega),
    word64_of_zeroBytes (offset := 8) bytes (by omega)⟩

/-- **Every address of a descriptor's 16 bytes is load-bearing.** Uniform in the offset, so the
record region of `ExecutionRequests` — which `executionRequests_record_exactly_covered` shows is
exactly three of these — carries no padding anywhere. -/
theorem sliceDescriptor_footprint_tight (base offset : Nat) (hoffset : offset < 16) :
    ∃ s1 s2 : State,
      (∀ address, address ≠ base + offset → s1.mem.get? address = s2.mem.get? address) ∧
        SliceDescriptorRep s1 base 0 0 ∧ ¬ SliceDescriptorRep s2 base 0 0 := by
  refine ⟨{ (default : State) with mem := zeroBytes base 16 },
          { (default : State) with
            mem := (zeroBytes base 16).insert (base + offset) (BitVec.ofNat 8 1) },
          ?_, sliceDescriptorZero_rep (fun index hindex => zeroBytes_inside hindex) (by omega), ?_⟩
  · intro address hne
    show (zeroBytes base 16).get? address
        = ((zeroBytes base 16).insert (base + offset) (BitVec.ofNat 8 1)).get? address
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (fun heq => hne heq.symm)]
  · intro hrep
    have hclobbered : ((zeroBytes base 16).insert (base + offset) (BitVec.ofNat 8 1)).get?
        (base + offset) = some (BitVec.ofNat 8 1) := by
      simp [Std.ExtHashMap.get?_eq_getElem?]
    have hzero : ((zeroBytes base 16).insert (base + offset) (BitVec.ofNat 8 1)).get?
        (base + offset) = some (BitVec.ofNat 8 0) := by
      by_cases hlow : offset < 8
      · simpa using hrep.2.2.1 offset hlow
      · have h8 := hrep.2.2.2 (offset - 8) (by omega)
        rw [show base + 8 + (offset - 8) = base + offset by omega] at h8
        simp at h8
    rw [hclobbered] at hzero
    exact absurd hzero (by decide)

/-- The read set of `ExecutionRequestsRep`: the record, plus the three heap arrays it points at.

The array bases are **parameters** of the region rather than functions of `base`, because the
representation binds them existentially. The extents are `count * elementSize` in the order
`HeapArrayRep` uses. -/
def executionRequestsRegion (base recordSize depositsBase withdrawalsBase consolidationsBase
    depositCount withdrawalCount consolidationCount depositSize withdrawalSize
    consolidationSize : Nat) : Region :=
  Region.union (range base recordSize)
    (Region.union (range depositsBase (depositCount * depositSize))
      (Region.union (range withdrawalsBase (withdrawalCount * withdrawalSize))
        (range consolidationsBase (consolidationCount * consolidationSize))))

/-- **The witnessed footprint of `ExecutionRequestsRep`.**

Read the shape from the module note above: the representation at `s1` goes in, the three
allocator-chosen bases come out, and what comes back is a transport valid at any `s2` agreeing on the
region those bases name.

Nine conjuncts, three regions, and no input component — the `InputSliceRep` question does not arise
until `ExecutionWitness`. -/
theorem executionRequests_footprint (base : Nat) (value : SszBridge.RawExecutionRequests)
    (s1 : State) (established : ExecutionRequestsRep s1 base value) :
    ∃ depositsBase withdrawalsBase consolidationsBase,
      ∀ s2 : State,
        (∀ address, executionRequestsRegion base 48 depositsBase withdrawalsBase consolidationsBase
            value.deposits.size value.withdrawals.size value.consolidations.size 192 80 116
            address →
          s1.mem.get? address = s2.mem.get? address) →
        ExecutionRequestsRep s2 base value := by
  obtain ⟨depositsBase, withdrawalsBase, consolidationsBase,
    hDepositDescriptor, hDepositArray, hDepositContents,
    hWithdrawalDescriptor, hWithdrawalArray, hWithdrawalContents,
    hConsolidationDescriptor, hConsolidationArray, hConsolidationContents⟩ := established
  refine ⟨depositsBase, withdrawalsBase, consolidationsBase, fun s2 agree => ?_⟩
  have agreeRecord : ∀ address, range base 48 address →
      s1.mem.get? address = s2.mem.get? address :=
    fun address ha => agree address (Or.inl ha)
  have agreeDeposits : ∀ address, range depositsBase (value.deposits.size * 192) address →
      s1.mem.get? address = s2.mem.get? address :=
    fun address ha => agree address (Or.inr (Or.inl ha))
  have agreeWithdrawals : ∀ address, range withdrawalsBase (value.withdrawals.size * 80) address →
      s1.mem.get? address = s2.mem.get? address :=
    fun address ha => agree address (Or.inr (Or.inr (Or.inl ha)))
  have agreeConsolidations :
      ∀ address, range consolidationsBase (value.consolidations.size * 116) address →
      s1.mem.get? address = s2.mem.get? address :=
    fun address ha => agree address (Or.inr (Or.inr (Or.inr ha)))
  exact ⟨depositsBase, withdrawalsBase, consolidationsBase,
    sliceDescriptor_footprint base _ _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeRecord _ ⟨by omega, by omega⟩) hDepositDescriptor,
    heapArray_footprint depositsBase _ 192 s1 s2 agreeDeposits hDepositArray,
    heapDepositRequestArray_footprint depositsBase _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeDeposits _ ⟨by omega, by omega⟩) hDepositContents,
    sliceDescriptor_footprint (base + 16) _ _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeRecord _ ⟨by omega, by omega⟩) hWithdrawalDescriptor,
    heapArray_footprint withdrawalsBase _ 80 s1 s2 agreeWithdrawals hWithdrawalArray,
    heapWithdrawalRequestArray_footprint withdrawalsBase _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeWithdrawals _ ⟨by omega, by omega⟩) hWithdrawalContents,
    sliceDescriptor_footprint (base + 32) _ _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeRecord _ ⟨by omega, by omega⟩) hConsolidationDescriptor,
    heapArray_footprint consolidationsBase _ 116 s1 s2 agreeConsolidations hConsolidationArray,
    heapConsolidationRequestArray_footprint consolidationsBase _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeConsolidations _ ⟨by omega, by omega⟩) hConsolidationContents⟩

/-- The same at manifest-derived sizes: the record boundary and all three element strides come from
`Artifact`, so a layout change moves the region instead of leaving it silently describing the wrong
bytes. Four size hypotheses because the region genuinely depends on four numbers. -/
theorem executionRequests_footprint_abi (base : Nat) (value : SszBridge.RawExecutionRequests)
    (s1 : State) (established : ExecutionRequestsRep s1 base value)
    {recordSize depositSize withdrawalSize consolidationSize : Nat}
    (hrecord : BinaryFv.SSZ.Zesu.Artifact.executionRequestsSize = some recordSize)
    (hdeposit : BinaryFv.SSZ.Zesu.Artifact.rawDepositRequestSize = some depositSize)
    (hwithdrawal : BinaryFv.SSZ.Zesu.Artifact.rawWithdrawalRequestSize = some withdrawalSize)
    (hconsolidation :
      BinaryFv.SSZ.Zesu.Artifact.rawConsolidationRequestSize = some consolidationSize) :
    ∃ depositsBase withdrawalsBase consolidationsBase,
      ∀ s2 : State,
        (∀ address, executionRequestsRegion base recordSize depositsBase withdrawalsBase
            consolidationsBase value.deposits.size value.withdrawals.size
            value.consolidations.size depositSize withdrawalSize consolidationSize address →
          s1.mem.get? address = s2.mem.get? address) →
        ExecutionRequestsRep s2 base value := by
  have h48 : recordSize = 48 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.allocating_container_size_layout.1
    rw [hrecord] at hlayout
    exact Option.some.inj hlayout
  have h192 : depositSize = 192 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.heap_element_size_layout.2.1
    rw [hdeposit] at hlayout
    exact Option.some.inj hlayout
  have h80 : withdrawalSize = 80 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.heap_element_size_layout.2.2.1
    rw [hwithdrawal] at hlayout
    exact Option.some.inj hlayout
  have h116 : consolidationSize = 116 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.heap_element_size_layout.2.2.2
    rw [hconsolidation] at hlayout
    exact Option.some.inj hlayout
  subst h48; subst h192; subst h80; subst h116
  exact executionRequests_footprint base value s1 established

/-- **The form the ownership discipline consumes.**

The caller holds a representation and a confined sibling; it receives the three array bases, owes
disjointness against *those*, and gets the representation back at the later state. That the bases
arrive from the representation rather than being supplied to it is the whole content of the witnessed
shape — a caller cannot name what the allocator chose.

This is `representation_survives_sibling_witnessed` specialised; the general lemma already had the
right force, and what was missing was a container whose footprint it could be applied to. -/
theorem executionRequests_survives_sibling (base : Nat) (value : SszBridge.RawExecutionRequests)
    (s1 s2 : State) (ownedSibling : Region)
    (established : ExecutionRequestsRep s1 base value)
    (writes : WritesOnlyWithin ownedSibling s1 s2) :
    ∃ depositsBase withdrawalsBase consolidationsBase,
      (∀ address, executionRequestsRegion base 48 depositsBase withdrawalsBase consolidationsBase
          value.deposits.size value.withdrawals.size value.consolidations.size 192 80 116 address →
        ¬ ownedSibling address) →
      ExecutionRequestsRep s2 base value := by
  obtain ⟨depositsBase, withdrawalsBase, consolidationsBase, transport⟩ :=
    executionRequests_footprint base value s1 established
  exact ⟨depositsBase, withdrawalsBase, consolidationsBase, fun disjoint =>
    transport s2 fun address hregion =>
      (writes address (disjoint address hregion)).symm⟩

/-! ## `ExecutionWitness`, and the input slices

The prediction on record before this container was written: **borrowed input slices need no witnessed
region at all.** It holds, and `inputSlice_footprint` is the reason — but the reason is worth stating
exactly, because it is not "the input contribution is small".

`InputSliceRep` is
```
sliceBase = inputBase + inputOffset ∧
  ∀ index < length, get? (sliceBase + index) = get? (inputBase + inputOffset + index)
```
The first conjunct is a pure address equation with no state in it. Substituting it into the second
turns that one into `x = x`. So the aliasing claim **reads no memory whatsoever**: it is a statement
about where the pointer points, not about what is there. Its footprint is the *empty* region, which
is the strongest footprint a claim can have, not a degenerate one — see `memDeterminedOn_empty_iff`.

### What this settles, and the part it does not

The recorded disconfirming condition was: if input slices *do* need a witnessed region, then the
"wrong determinant" unification is weaker than claimed and the pattern is really about existential
binding. They do not, so the unification stands — but the alternative is worth refuting directly
rather than by elimination, because `InputSliceDescriptorArrayRep` **is** existentially bound
(`∀ index, ∃ inputOffset sliceBase, …`) and is nonetheless `MemDeterminedOn` a region computed from
its base alone.

So existential binding is neither necessary nor sufficient for needing the witnessed shape. What
forces it is an existential over something that **contributes a region** — the heap array bases do,
`inputOffset` and `sliceBase` do not. The determinant is the right axis; the binder is not. -/

/-- The empty region: no address at all. -/
def Region.empty : Region := fun _ => False

/-- **A footprint on the empty region is the strongest possible claim, not a vacuous one.** It says
the predicate transports between *any* two states — that it does not depend on memory at all. Worth
stating because "footprint is empty" reads like a degenerate result and is the opposite: the empty
region is where `memDeterminedOn_mono` starts, not where it ends. -/
theorem memDeterminedOn_empty_iff {P : State → Prop} :
    MemDeterminedOn Region.empty P ↔ ∀ s1 s2, P s1 → P s2 :=
  ⟨fun h s1 s2 => h s1 s2 (fun _ hfalse => hfalse.elim), fun h s1 s2 _ => h s1 s2⟩

/-- **The scored prediction: a borrowed input slice reads no memory.**

Not "reads little" — reads *nothing*. The address equation is what makes the aliasing claim true, and
once it is substituted the pointwise claim is a tautology. So a container that borrows from the
caller's input adds **no** input component to its footprint, and a sibling writing anywhere in the
input buffer cannot disturb the aliasing fact.

That is a statement about `InputSliceRep` as written, and it is worth being explicit that this is a
*weakness* of the representation as much as a convenience for the discipline: the predicate does not
say the slice's bytes equal the input's bytes at the later state, because it does not say anything
about bytes. `InputBytesAt`, the conjunct beside it in `InputSliceDescriptorRep`, is what relates the
decoded array to the input — and it mentions no state either. -/
theorem inputSlice_footprint (inputBase inputOffset length sliceBase : Nat) :
    MemDeterminedOn Region.empty
      (fun s => InputSliceRep s inputBase inputOffset length sliceBase) := by
  rintro s1 s2 - ⟨haddress, -⟩
  exact ⟨haddress, fun index hindex => by rw [haddress]⟩

/-- A borrowed slice's whole footprint is its own descriptor: sixteen bytes, the pointer and the
count. The aliasing conjunct contributes nothing and `InputBytesAt` mentions no state. -/
theorem inputSliceDescriptor_footprint (inputBase : Nat) (input : ByteArray)
    (descriptorBase inputOffset sliceBase : Nat) (bytes : Array UInt8) :
    MemDeterminedOn (range descriptorBase 16)
      (fun s => InputSliceDescriptorRep s inputBase input descriptorBase inputOffset sliceBase
        bytes) :=
  memDeterminedOn_and (sliceDescriptor_footprint descriptorBase sliceBase bytes.size)
    (memDeterminedOn_and
      (memDeterminedOn_mono (fun _ hfalse => hfalse.elim)
        (inputSlice_footprint inputBase inputOffset bytes.size sliceBase))
      memDeterminedOn_const)

/-- **Existentially bound, and still `MemDeterminedOn` a base-computed region.** The per-index
`inputOffset` and `sliceBase` are extracted from the `s1` proof and handed straight back at `s2`;
neither names an address, so neither enlarges the region. This is the direct refutation of
"existential binding is what forces the witnessed shape". -/
theorem inputSliceDescriptorArray_footprint (inputBase : Nat) (input : ByteArray)
    (descriptorBase : Nat) (slices : Array (Array UInt8)) :
    MemDeterminedOn (range descriptorBase (16 * slices.size))
      (fun s => InputSliceDescriptorArrayRep s inputBase input descriptorBase slices) := by
  intro s1 s2 agree h index hindex
  obtain ⟨inputOffset, sliceBase, hslice⟩ := h index hindex
  have hstride : 16 * index + 16 ≤ 16 * slices.size := by
    have hle : 16 * (index + 1) ≤ 16 * slices.size := Nat.mul_le_mul_left 16 (by omega)
    omega
  exact ⟨inputOffset, sliceBase,
    inputSliceDescriptor_footprint inputBase input (descriptorBase + 16 * index) inputOffset
      sliceBase slices[index] s1 s2 (fun _ ⟨hl, hr⟩ => agree _ ⟨by omega, by omega⟩) hslice⟩

/-- The read set of `ExecutionWitnessRep`: structurally identical to `ExecutionRequests`, because the
input contributes nothing. Three descriptors in the record, three heap arrays of descriptors.

`descriptorSize` is 16, and **that number is not a manifest datum** — unlike the record boundaries and
element strides, no ABI entry names it. It is the width of `SliceDescriptorRep` itself, two
`Word64LERep`s at `+0` and `+8`. That is a stronger justification than a reflected constant rather
than a weaker one: `sliceDescriptor_footprint` and `sliceDescriptor_footprint_tight` together prove
the 16 exact, where a manifest lookup would only assert it. -/
def executionWitnessRegion (base recordSize stateBase codesBase headersBase
    stateCount codesCount headersCount descriptorSize : Nat) : Region :=
  Region.union (range base recordSize)
    (Region.union (range stateBase (stateCount * descriptorSize))
      (Region.union (range codesBase (codesCount * descriptorSize))
        (range headersBase (headersCount * descriptorSize))))

/-- **The witnessed footprint of `ExecutionWitnessRep`.** Same shape as `ExecutionRequests`, and
carrying neither `inputBase` nor `input` in its region — which is the prediction, discharged at the
container rather than at the primitive. -/
theorem executionWitness_footprint (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : SszBridge.RawExecutionWitness) (s1 : State)
    (established : ExecutionWitnessRep s1 inputBase input base value) :
    ∃ stateBase codesBase headersBase,
      ∀ s2 : State,
        (∀ address, executionWitnessRegion base 48 stateBase codesBase headersBase
            value.state.size value.codes.size value.headers.size 16 address →
          s1.mem.get? address = s2.mem.get? address) →
        ExecutionWitnessRep s2 inputBase input base value := by
  obtain ⟨stateBase, codesBase, headersBase,
    hStateDescriptor, hStateArray, hStateContents,
    hCodesDescriptor, hCodesArray, hCodesContents,
    hHeadersDescriptor, hHeadersArray, hHeadersContents⟩ := established
  refine ⟨stateBase, codesBase, headersBase, fun s2 agree => ?_⟩
  have agreeRecord : ∀ address, range base 48 address →
      s1.mem.get? address = s2.mem.get? address :=
    fun address ha => agree address (Or.inl ha)
  have agreeState : ∀ address, range stateBase (value.state.size * 16) address →
      s1.mem.get? address = s2.mem.get? address :=
    fun address ha => agree address (Or.inr (Or.inl ha))
  have agreeCodes : ∀ address, range codesBase (value.codes.size * 16) address →
      s1.mem.get? address = s2.mem.get? address :=
    fun address ha => agree address (Or.inr (Or.inr (Or.inl ha)))
  have agreeHeaders : ∀ address, range headersBase (value.headers.size * 16) address →
      s1.mem.get? address = s2.mem.get? address :=
    fun address ha => agree address (Or.inr (Or.inr (Or.inr ha)))
  exact ⟨stateBase, codesBase, headersBase,
    sliceDescriptor_footprint base _ _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeRecord _ ⟨by omega, by omega⟩) hStateDescriptor,
    heapArray_footprint stateBase _ 16 s1 s2 agreeState hStateArray,
    inputSliceDescriptorArray_footprint inputBase input stateBase _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeState _ ⟨by omega, by omega⟩) hStateContents,
    sliceDescriptor_footprint (base + 16) _ _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeRecord _ ⟨by omega, by omega⟩) hCodesDescriptor,
    heapArray_footprint codesBase _ 16 s1 s2 agreeCodes hCodesArray,
    inputSliceDescriptorArray_footprint inputBase input codesBase _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeCodes _ ⟨by omega, by omega⟩) hCodesContents,
    sliceDescriptor_footprint (base + 32) _ _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeRecord _ ⟨by omega, by omega⟩) hHeadersDescriptor,
    heapArray_footprint headersBase _ 16 s1 s2 agreeHeaders hHeadersArray,
    inputSliceDescriptorArray_footprint inputBase input headersBase _ s1 s2
      (fun _ ⟨hl, hr⟩ => agreeHeaders _ ⟨by omega, by omega⟩) hHeadersContents⟩

/-- The consumable form, identical in shape to `executionRequests_survives_sibling`. Deliberately
says nothing about the input: the input claim is `inputSlice_survives_clobber_of_its_own_bytes`
below, and mixing the two is how the near-miss recorded there happened. -/
theorem executionWitness_survives_sibling (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : SszBridge.RawExecutionWitness) (s1 s2 : State) (ownedSibling : Region)
    (established : ExecutionWitnessRep s1 inputBase input base value)
    (writes : WritesOnlyWithin ownedSibling s1 s2) :
    ∃ stateBase codesBase headersBase,
      (∀ address, executionWitnessRegion base 48 stateBase codesBase headersBase
          value.state.size value.codes.size value.headers.size 16 address →
        ¬ ownedSibling address) →
      ExecutionWitnessRep s2 inputBase input base value := by
  obtain ⟨stateBase, codesBase, headersBase, transport⟩ :=
    executionWitness_footprint inputBase input base value s1 established
  exact ⟨stateBase, codesBase, headersBase, fun disjoint =>
    transport s2 fun address hregion => (writes address (disjoint address hregion)).symm⟩

/-- **The power half of the prediction: a sibling may overwrite the aliased bytes themselves.**

The slice's bytes lie *inside* the caller's input buffer, at `inputBase + inputOffset`. A naive
footprint would therefore include them. This exhibits, for every offset the slice covers, two states
differing exactly there with the aliasing claim holding at both. If `InputSliceRep` carried any
content about byte values, this would be false.

**Written because the obvious corollary could not fail.** The first version of this was a statement
that the witness representation survives a sibling owning the input buffer, *given* the footprint is
disjoint from that buffer. That proves identically whether or not the input is in the footprint — if
it were, the disjointness premise would simply be unsatisfiable and the theorem vacuously true. It
had the shape of evidence and the power of none, which is the defect this module was written to
catch, drafted by the person writing the module. This one distinguishes the two cases. -/
theorem inputSlice_survives_clobber_of_its_own_bytes
    (inputBase inputOffset length offset : Nat) (hoffset : offset < length) (byte : BitVec 8) :
    ∃ s1 s2 : State,
      range (inputBase + inputOffset) length (inputBase + inputOffset + offset) ∧
        s1.mem.get? (inputBase + inputOffset + offset)
          ≠ s2.mem.get? (inputBase + inputOffset + offset) ∧
        InputSliceRep s1 inputBase inputOffset length (inputBase + inputOffset) ∧
        InputSliceRep s2 inputBase inputOffset length (inputBase + inputOffset) := by
  refine ⟨{ (default : State) with mem := ∅ },
          { (default : State) with
            mem := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert
              (inputBase + inputOffset + offset) byte },
          ⟨by omega, by omega⟩, ?_, ⟨rfl, fun _ _ => rfl⟩, ⟨rfl, fun _ _ => rfl⟩⟩
  show (∅ : Std.ExtHashMap Nat (BitVec 8)).get? (inputBase + inputOffset + offset)
      ≠ ((∅ : Std.ExtHashMap Nat (BitVec 8)).insert
          (inputBase + inputOffset + offset) byte).get? (inputBase + inputOffset + offset)
  simp [Std.ExtHashMap.get?_eq_getElem?]

/-- The manifest-derived form. `ExecutionWitness` has the same 48-byte record as
`ExecutionRequests`, and the two are separate manifest entries rather than one shared constant, so
this derives its own. -/
theorem executionWitness_footprint_abi (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : SszBridge.RawExecutionWitness) (s1 : State)
    (established : ExecutionWitnessRep s1 inputBase input base value)
    {recordSize : Nat}
    (hrecord : BinaryFv.SSZ.Zesu.Artifact.executionWitnessSize = some recordSize) :
    ∃ stateBase codesBase headersBase,
      ∀ s2 : State,
        (∀ address, executionWitnessRegion base recordSize stateBase codesBase headersBase
            value.state.size value.codes.size value.headers.size 16 address →
          s1.mem.get? address = s2.mem.get? address) →
        ExecutionWitnessRep s2 inputBase input base value := by
  have h48 : recordSize = 48 := by
    have hlayout := BinaryFv.SSZ.Zesu.Artifact.allocating_container_size_layout.2.1
    rw [hrecord] at hlayout
    exact Option.some.inj hlayout
  subst h48
  exact executionWitness_footprint inputBase input base value s1 established

/-- The container layer's manifest-derived footprints, gathered for the axiom-hygiene anchor. Same
reason as `heapLayer_footprints_abi`: an anchor sees only what its declaration reaches, so a layer is
anchored by one statement reaching the layer.

It has one conjunct today and grows as `ExecutionWitness`, `ExecutionPayload`, `NewPayloadRequest`
and `RawV4Rep` land. **A footprint added to the layer and not added here is invisible to the guard** —
that gap is real and is recorded beside the door set in `BinaryFv/SSZ/AxiomHygiene.lean`, together
with why it closes when the composition's entry point is anchored. -/
theorem containerLayer_footprints_abi (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : SszBridge.RawExecutionRequests) (witness : SszBridge.RawExecutionWitness)
    (s1 : State) (established : ExecutionRequestsRep s1 base value)
    (witnessEstablished : ExecutionWitnessRep s1 inputBase input base witness)
    {recordSize witnessSize depositSize withdrawalSize consolidationSize : Nat}
    (hrecord : BinaryFv.SSZ.Zesu.Artifact.executionRequestsSize = some recordSize)
    (hwitness : BinaryFv.SSZ.Zesu.Artifact.executionWitnessSize = some witnessSize)
    (hdeposit : BinaryFv.SSZ.Zesu.Artifact.rawDepositRequestSize = some depositSize)
    (hwithdrawal : BinaryFv.SSZ.Zesu.Artifact.rawWithdrawalRequestSize = some withdrawalSize)
    (hconsolidation :
      BinaryFv.SSZ.Zesu.Artifact.rawConsolidationRequestSize = some consolidationSize) :
    (∃ depositsBase withdrawalsBase consolidationsBase,
        ∀ s2 : State,
          (∀ address, executionRequestsRegion base recordSize depositsBase withdrawalsBase
              consolidationsBase value.deposits.size value.withdrawals.size
              value.consolidations.size depositSize withdrawalSize consolidationSize address →
            s1.mem.get? address = s2.mem.get? address) →
          ExecutionRequestsRep s2 base value) ∧
      (∃ stateBase codesBase headersBase,
        ∀ s2 : State,
          (∀ address, executionWitnessRegion base witnessSize stateBase codesBase headersBase
              witness.state.size witness.codes.size witness.headers.size 16 address →
            s1.mem.get? address = s2.mem.get? address) →
          ExecutionWitnessRep s2 inputBase input base witness) :=
  ⟨executionRequests_footprint_abi base value s1 established hrecord hdeposit hwithdrawal
      hconsolidation,
    executionWitness_footprint_abi inputBase input base witness s1 witnessEstablished hwitness⟩

end BinaryFv.SSZ.Zesu.Contracts.Footprint
