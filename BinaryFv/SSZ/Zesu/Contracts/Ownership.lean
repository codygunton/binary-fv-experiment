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

/-! `Region` and `WritesOnlyWithin` are **not** defined here any more. They moved down to
`Contracts/Environment.lean` — unchanged — because the `post*` predicates now carry the clause and
every contract module sits below this one in the import order. They resolve here by name from the
enclosing `Contracts` namespace, so there is still exactly one definition of each. -/

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

This is the fact `FrameGap.sibling_clobber_permitted_historical` shows was *missing*. Nothing here is
proved about any particular contract — it is the statement of what a boundary must supply, and
`fixed_container_cannot_clobber_sibling` below is where it is finally run against one. -/
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

The regression lead asked for: with the discipline in place, the conclusion of
`FrameGap.sibling_clobber_permitted_historical` becomes unreachable. These theorems are the *target*,
and if a future change lets the clobber back in, they are what fails.

The first three are stated at an abstract `ownedSibling`, which is what the composition consumes.
`fixed_container_cannot_clobber_sibling` is the same fact run against the **actual strengthened
contract** — the step that was missing while the clause lived only in `OwnershipComposition`. -/

/-- `bytePinned` is local to the single byte at its result base — the smallest possible region, and
the reason it is the right witness for both directions. -/
theorem bytePinned_localTo (value : BitVec 8) :
    LocalTo (bytePinned value) (fun resultBase address => address = resultBase) := by
  intro base bytes _ s1 s2 resultBase agree established
  unfold bytePinned at established ⊢
  rw [← agree resultBase rfl]; exact established

/-- **Under ownership, the clobber `FrameGap` exhibits cannot happen.**

Read against `FrameGap.sibling_clobber_permitted_historical`, which produces exactly this situation
*without* the confinement hypothesis. The single added premise — the sibling does not own A's result
byte — is the entire content of the fix. -/
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

/-- **A fixed container cannot clobber an earlier sibling's byte.** The positive replacement for
`FrameGap.sibling_clobber_permitted_historical`, stated against the live `postFixedContainer` rather
than against an abstract region.

The only hypothesis beyond the contract is `outside`: A's result byte is not inside B's record. That
is the *parent's* obligation — where it placed the two result buffers — and it is the one thing the
callee cannot be asked to know, which is why the discipline is split this way in the first place.

**Why the exhibit specifically dies.** It quantified over any `rA ≠ rB`, so it had to work for
`rA < rB`, where `¬ range rB size rA` holds for every `size`. No choice of record size rescues it: an
over-large record only reaches *upward*. That is the sense in which the regression fired for the right
reason rather than by accident of the witness. -/
theorem fixed_container_cannot_clobber_sibling {α : Type} {env : DecoderEnvironment}
    {argsA argsB : ContainerArgs} {rep : ContainerRepresentation α} {recordSize : Nat}
    {result : Except SszDecodeError α} {value : BitVec 8} {s1 s2 : State}
    (outside : ¬ range argsB.resultBase recordSize argsA.resultBase)
    (postB : postFixedContainer env argsB rep recordSize result s1 s2)
    (established : bytePinned value argsA.base argsA.bytes () s1 argsA.resultBase) :
    bytePinned value argsA.base argsA.bytes () s2 argsA.resultBase :=
  no_sibling_clobber_under_ownership
    (ownedSibling := allocatedRegion argsB.resultBase recordSize 0 0)
    (fun h => h.elim outside (fun hint => absurd hint.2 (Nat.not_lt_zero _)))
    postB.2.2.2.1 established

/-- The refutation form, which is the shape a regression test wants: the exhibit's conclusion and the
strengthened contract are jointly unsatisfiable.

Compare `FrameGap.frame_gap_is_real`, which realises exactly this conjunction against the *historical*
predicate. The two together are the before/after of the strengthening. -/
theorem strengthened_contract_and_clobber_incompatible {α : Type} {env : DecoderEnvironment}
    {argsA argsB : ContainerArgs} {rep : ContainerRepresentation α} {recordSize : Nat}
    {result : Except SszDecodeError α} {value : BitVec 8} {s1 s2 : State} :
    ¬ (¬ range argsB.resultBase recordSize argsA.resultBase ∧
        postFixedContainer env argsB rep recordSize result s1 s2 ∧
        bytePinned value argsA.base argsA.bytes () s1 argsA.resultBase ∧
        ¬ bytePinned value argsA.base argsA.bytes () s2 argsA.resultBase) := by
  rintro ⟨outside, postB, established, broken⟩
  exact broken (fixed_container_cannot_clobber_sibling outside postB established)

/-- **The exhibit's own run is now refuted, not merely unproven**, and the distinction is the whole
value of this theorem.

A strengthening that made `FrameGap.sibling_clobber_permitted` stop compiling would be consistent with
the clause being unusable — "I could not reproduce the proof" is not "the situation is impossible". So
the regression is recorded in the form that can only hold for the right reason: at the exhibit's own
numbers (`rA = 0`, `rB = 1`) the conjunction it used to realise is **contradictory**, for every
environment and every record size B could claim.

`rA < rB` is what does it, and no record size rescues it, since a record only reaches upward from its
base. `FrameGap.frame_gap_is_real` realises the same conjunction against the historical predicate, so
the pair is a genuine before/after rather than two unrelated statements. -/
theorem exhibit_run_is_refuted (env : DecoderEnvironment) (recordSizeB : Nat) :
    ¬ ∃ (s1 s2 : State) (argsA argsB : ContainerArgs),
        argsA.resultBase = 0 ∧ argsB.resultBase = 1 ∧
        postFixedContainer env argsB (bytePinned 3) recordSizeB (.ok ()) s1 s2 ∧
        bytePinned 7 argsA.base argsA.bytes () s1 argsA.resultBase ∧
        ¬ bytePinned 7 argsA.base argsA.bytes () s2 argsA.resultBase := by
  rintro ⟨s1, s2, argsA, argsB, hA, hB, postB, established, broken⟩
  refine strengthened_contract_and_clobber_incompatible ⟨?_, postB, established, broken⟩
  rw [hA, hB]
  rintro ⟨hlo, _⟩
  omega

/-- **`outside` is necessary, and this is the check the abstract version could not run.** Drop it and
the conclusion is false *for a contract-satisfying sibling*: a container whose own record covers A's
byte may overwrite it and still satisfy `postFixedContainer` in full.

`unowned_hypothesis_is_necessary` above makes the same point about an abstract region, where the
counterexample is a sibling owning literally everything and is easy to dismiss as degenerate. Here the
sibling is a two-byte record at address 0 that writes inside itself — the ordinary case, which is what
makes the parent's placement obligation real rather than a formality. -/
theorem outside_hypothesis_is_necessary :
    ∃ (argsA argsB : ContainerArgs) (recordSize : Nat) (s1 s2 : State),
      postFixedContainer FrameGap.gapEnv argsB (bytePinned 3) recordSize (.ok ()) s1 s2 ∧
        bytePinned 7 argsA.base argsA.bytes () s1 argsA.resultBase ∧
        ¬ bytePinned 7 argsA.base argsA.bytes () s2 argsA.resultBase := by
  refine ⟨⟨0, ByteArray.empty, 0, 1⟩, ⟨0, ByteArray.empty, 0, 0⟩, 2,
          { (default : State) with mem := (default : State).mem.insert 1 7 },
          { (default : State) with
            mem := (((default : State).mem.insert 1 7).insert 0 3).insert 1 0 },
          ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro index h; exact absurd h (by simp)
  · intro a b h; exact absurd h (by rw [FrameGap.gapEnv_readFileByte]; simp)
  · intro _ h; exact h.elim
  · intro address houtside
    have hlo : address ≠ 0 := by
      intro heq
      refine houtside (Or.inl ?_)
      show (0 : Nat) ≤ address ∧ address < 0 + 2
      omega
    have hhi : address ≠ 1 := by
      intro heq
      refine houtside (Or.inl ?_)
      show (0 : Nat) ≤ address ∧ address < 0 + 2
      omega
    show ((((default : State).mem.insert 1 7).insert 0 3).insert 1 0).get? address
        = ((default : State).mem.insert 1 7).get? address
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (fun heq => hhi heq.symm), if_neg (fun heq => hlo heq.symm)]
  · show ((((default : State).mem.insert 1 7).insert 0 3).insert 1 0).get? 0 = some 3
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp
  · show ((default : State).mem.insert 1 7).get? 1 = some 7
    simp [Std.ExtHashMap.get?_eq_getElem?]
  · show ¬ ((((default : State).mem.insert 1 7).insert 0 3).insert 1 0).get? 1 = some 7
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
