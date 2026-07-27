import BinaryFv.SSZ.Zesu.Contracts.FrameGap

/-!
# Memory ownership for composed local summaries

The discipline that closes the gap `FrameGap.lean` exhibits. That module shows a parent cannot
conclude its `representation … after …` from its children's postconditions, because nothing stops a
later sibling overwriting an earlier one's result. This module says what a boundary must guarantee
for that to become impossible, and proves it does.

## Why this is a new layer rather than a hook into the existing boundary machinery

`RiscV/Elfling/Boundary.lean` — `CallSite`, `InlineBoundary`, `validFor` — is where a call site's
obligations are discharged, and it is the right *place* for the ownership obligation to live. But it
carries **control-flow** confinement only: pcs, edges, occupancy, exit boundaries. It contains no
reference to memory at all. So the memory-ownership predicate is genuinely new content and is defined
here rather than recovered from `validFor`.

## The shape of the fix, and why it is not a frame clause in a postcondition

"This routine writes nowhere else" is false of real routines: they use scratch stack and they
allocate. The true fact is "this routine writes only within what it **owns**". And "siblings do not
overlap" is not a property of either child — it is a property of how the **parent** allocated their
result buffers, so it cannot be stated in a child's postcondition without putting a caller's
obligation in a callee's contract.

Hence two separate pieces, composed at the boundary:

* `WritesOnlyWithin` — a *callee* fact: writes are confined to an owned region.
* `LocalTo` — a *representation* fact: the representation is determined by the region around its own
  result base, so it cannot be disturbed by writes elsewhere.

Disjointness of two children's owned regions is then the *parent's* obligation, discharged once per
call site, rather than a clause every routine re-proves.

## The honest limit, inherited from `FrameGap`

`representation_may_read_beyond_memory` shows a `ContainerRepresentation` receives the whole `State`
and may constrain registers or any other component. Everything here is **memory-only**, so a
representation that reads outside memory is not `LocalTo` any region and gets no protection from this
discipline. That is a real obligation on the container representations, not a gap in these lemmas:
each real representation must be shown `LocalTo` something, and one that reads registers cannot be.
No such check is performed here — see `localTo_is_a_real_obligation` for why that matters.
-/

namespace BinaryFv.SSZ.Zesu.Contracts.Ownership

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.Contracts.FrameGap

/-- A set of addresses. Kept as a predicate rather than a range because owned regions are not
contiguous in general — a container owns its result buffer and whatever it allocated. -/
abbrev Region := Nat → Prop

/-- **The callee's obligation:** every write lands inside `owned`.

Note the direction. This is *not* "the routine writes all of `owned`" — it is permission, not
requirement, so a routine that writes nothing satisfies it for any region. -/
def WritesOnlyWithin (owned : Region) (before after : State) : Prop :=
  ∀ address, ¬ owned address → after.mem.get? address = before.mem.get? address

/-- **The representation's obligation:** `rep` at result base `r` is determined by `region r`.

Stated as one-directional transport rather than an `iff` because that is all composition consumes,
and the weaker form is what the real representations will actually be able to prove. -/
def LocalTo {α : Type} (rep : ContainerRepresentation α) (region : Nat → Region) : Prop :=
  ∀ base bytes value s1 s2 resultBase,
    (∀ address, region resultBase address → s1.mem.get? address = s2.mem.get? address) →
    rep base bytes value s1 resultBase → rep base bytes value s2 resultBase

/-- **The composition lemma the parent needs.** An earlier child's representation survives a later
sibling's execution, given the three pieces: the representation is local, the sibling's writes are
confined, and the two regions are disjoint.

This is the fact `FrameGap.sibling_clobber_permitted` shows is *missing*. Nothing here is proved
about any particular contract — it is the statement of what a boundary must supply. -/
theorem representation_survives_sibling {α : Type} {rep : ContainerRepresentation α}
    {region : Nat → Region} {ownedSibling : Region} {s1 s2 : State}
    {base resultBase : Nat} {bytes : ByteArray} {value : α}
    (local_ : LocalTo rep region)
    (disjoint : ∀ address, region resultBase address → ¬ ownedSibling address)
    (confined : WritesOnlyWithin ownedSibling s1 s2)
    (established : rep base bytes value s1 resultBase) :
    rep base bytes value s2 resultBase :=
  local_ base bytes value s1 s2 resultBase
    (fun address hmem => (confined address (disjoint address hmem)).symm) established

/-- Confinement composes along a chain of siblings, so a representation established before *several*
later children survives all of them. This is what makes the discipline usable at a container with
more than two fields — the four-field entry schema being the case that matters. -/
theorem writesOnlyWithin_trans {owned : Region} {s1 s2 s3 : State}
    (first : WritesOnlyWithin owned s1 s2) (second : WritesOnlyWithin owned s2 s3) :
    WritesOnlyWithin owned s1 s3 :=
  fun address h => (second address h).trans (first address h)

/-- Widening the owned region weakens the obligation, which is the direction a caller needs when it
discharges disjointness against a coarse over-approximation of what a child touched. -/
theorem writesOnlyWithin_mono {owned wider : Region} {s1 s2 : State}
    (sub : ∀ address, owned address → wider address)
    (confined : WritesOnlyWithin owned s1 s2) :
    WritesOnlyWithin wider s1 s2 :=
  fun address h => confined address (fun howned => h (sub address howned))

/-! ## The discipline closes the exhibit

The regression lead asked for: with the discipline in place, `FrameGap.sibling_clobber_permitted`'s
conclusion becomes unreachable. These two theorems are the *target*, and if a future change lets the
clobber back in, they are what fails. -/

/-- `bytePinned` is local to the single byte at its result base — the smallest possible region, and
the reason it is the right witness for both directions. -/
theorem bytePinned_localTo (value : BitVec 8) :
    LocalTo (bytePinned value) (fun resultBase address => address = resultBase) := by
  intro base bytes _ s1 s2 resultBase agree established
  unfold bytePinned at established ⊢
  rw [← agree resultBase rfl]; exact established

/-- **Under ownership, the clobber `FrameGap` exhibits cannot happen.**

Read against `FrameGap.sibling_clobber_permitted`, which produces exactly this situation *without*
the confinement hypothesis. The single added premise — the sibling does not own A's result byte — is
the entire content of the fix. -/
theorem no_sibling_clobber_under_ownership {value : BitVec 8} {ownedSibling : Region}
    {s1 s2 : State} {base resultBase : Nat} {bytes : ByteArray}
    (unowned : ¬ ownedSibling resultBase)
    (confined : WritesOnlyWithin ownedSibling s1 s2)
    (established : bytePinned value base bytes () s1 resultBase) :
    bytePinned value base bytes () s2 resultBase :=
  representation_survives_sibling (bytePinned_localTo value)
    (fun _ h => h ▸ unowned) confined established

/-- The same statement in refutation form, which is the shape a regression test wants: the exhibit's
conclusion and the discipline are jointly unsatisfiable. -/
theorem discipline_and_clobber_incompatible {value : BitVec 8} {ownedSibling : Region}
    {s1 s2 : State} {base resultBase : Nat} {bytes : ByteArray} :
    ¬ (¬ ownedSibling resultBase ∧ WritesOnlyWithin ownedSibling s1 s2 ∧
        bytePinned value base bytes () s1 resultBase ∧
        ¬ bytePinned value base bytes () s2 resultBase) := by
  rintro ⟨unowned, confined, established, broken⟩
  exact broken (no_sibling_clobber_under_ownership unowned confined established)

/-- **The `unowned` hypothesis is necessary, not decorative.** Drop it and the conclusion is FALSE:
a sibling that owns everything may destroy the representation while remaining perfectly confined.

This is what makes `no_sibling_clobber_under_ownership` a real theorem rather than one that would
hold for an incidental reason. Together with `FrameGap.frame_gap_is_real` it brackets the discipline
from both sides: without confinement the clobber is realisable, with it the clobber is impossible,
and the single hypothesis separating the two is the content of the fix. -/
theorem unowned_hypothesis_is_necessary :
    ∃ (ownedSibling : Region) (s1 s2 : State) (base resultBase : Nat) (bytes : ByteArray),
      WritesOnlyWithin ownedSibling s1 s2 ∧
        bytePinned 7 base bytes () s1 resultBase ∧
        ¬ bytePinned 7 base bytes () s2 resultBase := by
  refine ⟨fun _ => True,
          { (default : State) with mem := (default : State).mem.insert 0 7 },
          { (default : State) with mem := ((default : State).mem.insert 0 7).insert 0 0 },
          0, 0, ByteArray.empty, fun _ h => absurd trivial h, ?_, ?_⟩
  · show ((default : State).mem.insert 0 7).get? 0 = some 7
    simp [Std.ExtHashMap.get?_eq_getElem?]
  · show ¬ (((default : State).mem.insert 0 7).insert 0 0).get? 0 = some 7
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp

/-! ## What is deliberately not proved here

Two obligations remain open, and naming them is the point — a discipline whose obligations are
unstated is indistinguishable from one that is already discharged. -/

/-- **`LocalTo` is a real obligation, not a formality.** A representation that reads any state
component other than memory is `LocalTo` *no* region whatsoever — not even the universal one. So
`FrameGap.representation_may_read_beyond_memory` is not a curiosity; it is the reason each real
container representation must be checked rather than assumed.

Proved at the universal region, which is the strongest form: if even "owns everything" fails to
transport it, no region succeeds. -/
theorem localTo_is_a_real_obligation :
    ∃ rep : ContainerRepresentation Unit,
      ¬ LocalTo rep (fun _ _ => True) := by
  refine ⟨fun _ _ _ state _ => state.cycleCount = (default : State).cycleCount, ?_⟩
  intro h
  have := h 0 ByteArray.empty () default
    { (default : State) with cycleCount := (default : State).cycleCount + 1 } 0
    (fun _ _ => rfl) rfl
  simp only at this
  omega

end BinaryFv.SSZ.Zesu.Contracts.Ownership
