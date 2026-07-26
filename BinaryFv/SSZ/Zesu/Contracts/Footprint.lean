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

/-! ## Tightness

The half that can fail. Soundness above would hold just as well for a padded footprint, so each
address the footprint claims must be shown to *matter*: two states agreeing everywhere except there,
disagreeing on the representation.

Proved for `OptionTagRep`. Its footprint is a single address, so the witness is a single-insert pair
and the result is complete rather than gestured at. -/

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

/-! ### What tightness is NOT yet proved for, and why it is listed rather than assumed

`Word64LERep` and the container footprints have **no** tightness result yet. The obstacle is
construction, not doubt: a witness must exhibit a state that *satisfies* the representation, and for
an eight-byte word that is eight `insert`s whose `get?`s must then be separated pairwise. Nothing
suggests those footprints are padded — the ranges are read straight off the layouts — but "nothing
suggests" is not a proof, and by the argument at the top of this module a soundness proof alone
cannot distinguish a tight footprint from a padded one.

So the container result is named `localTo_canonicalRepForkActivation_range32`, **not** `…_tight`. It
is sound and unwitnessed, and its name now says only what it proves: the representation transports
across agreement on a 32-byte range. A `_tight` suffix would have promised the missing half, which is
the name-versus-content defect this row keeps finding — cheaper to avoid in the name than to annotate
afterwards. The suffix becomes available when the witness does. -/

end BinaryFv.SSZ.Zesu.Contracts.Footprint
