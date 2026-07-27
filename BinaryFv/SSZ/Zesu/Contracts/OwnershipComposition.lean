import BinaryFv.SSZ.Zesu.Contracts.Footprint

/-!
# Composing the ownership discipline, conditionally

`Footprint` computes where every canonical representation lives. `Ownership` says what a callee must
promise (`WritesOnlyWithin`) and what a parent must discharge (disjointness). Nothing has yet put
them together over a *run*, which is the only thing that makes either useful: a parent does not face
one sibling, it faces every sibling that executes after its child returns.

## The contracts now supply the clause

This module used to say it changed no contract, and that the ownership promises were left as explicit
hypotheses because `postEntry`, `postAllocatingContainer`, `postCollection` and `postZesuDecodeRaw`
were reviewed meanings and the human's call. That call has since been made: `WritesOnlyWithinAllocation`
lives in `Contracts/Environment.lean` and 17 of the 18 `post*` predicates carry it as a conjunct.

The theorems here are unchanged, and their shape is why the wiring was cheap when it came: the clause
they consume is *the* clause, so what the contracts state is exactly what the composition eats —
`siblingChain_of_writesOnlyWithinAllocation` is the join, and a mismatch would show up there.

`root_compliance_of_local_contracts` still takes `LocalContractAssumptions` as a premise rather than
proving it, which is what made the strengthening free today and is also why nothing here has yet been
run against a real callee.

## The shape every container footprint already has

`Footprint`'s container results all read `∃ witnesses, ∀ s2, agreement-on-their-region → rep s2`.
That is exactly what `chain_agrees_on_region` feeds: agreement on a region propagates along a run of
siblings whenever each sibling's writes are confined and its permitted region misses the one being
protected. So one lemma serves all five containers, and the per-container corollaries are three lines
each rather than five separate arguments.

## The premises are exhibited satisfiable, with a sibling that really writes

A composition theorem whose ownership premises could not all hold would prove cleanly and mean
nothing — the failure this row has caught twice, once in this very stream. `sibling_chain_is_real`
discharges it against a concrete run, and it is *discriminating*: the sibling genuinely modifies
memory (a byte changes across the chain), so the conclusion is not surviving a no-op.
-/

namespace BinaryFv.SSZ.Zesu.Contracts.OwnershipComposition

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.SSZ.Zesu.Contracts.Ownership
open BinaryFv.SSZ.Zesu.Contracts.Footprint

/-! ## A run of siblings -/

/-- One later sibling: the state it finishes in, and the region it was permitted to write.

A pair rather than a structure because the region is *not* recovered from the state — it is the
callee's declared ownership, supplied by whoever composed the run. A region read out of memory a
sibling may write could not guard against that sibling, which is the non-circularity condition
already recorded in `Footprint`. -/
abbrev SiblingStep := State × Region

/-- Every step's writes are confined to the region it declared. -/
def SiblingChain : State → List SiblingStep → Prop
  | _, [] => True
  | start, step :: rest => WritesOnlyWithin step.2 start step.1 ∧ SiblingChain step.1 rest

/-- The state the run ends in. -/
def chainFinal : State → List SiblingStep → State
  | start, [] => start
  | _, step :: rest => chainFinal step.1 rest

/-- **The core lemma: agreement on a protected region survives an entire run.**

Everything else in this module is an application of it. Note what it does *not* need: no ordering on
the siblings, no allocator, no cursor monotonicity — only that each sibling stayed inside a region
that misses the protected one. Those other facts are how a parent *discharges* `disjoint`; they are
not part of why the composition works. -/
theorem chain_agrees_on_region {region : Region} :
    ∀ (start : State) (steps : List SiblingStep),
      SiblingChain start steps →
      (∀ step ∈ steps, ∀ address, region address → ¬ step.2 address) →
      ∀ address, region address →
        start.mem.get? address = (chainFinal start steps).mem.get? address := by
  intro start steps
  induction steps generalizing start with
  | nil => intro _ _ address _; rfl
  | cons step rest ih =>
      rintro ⟨writes, chain⟩ disjoint address hregion
      have hstep : start.mem.get? address = step.1.mem.get? address :=
        (writes address (disjoint step (by simp) address hregion)).symm
      exact hstep.trans
        (ih step.1 chain (fun s hs => disjoint s (by simp [hs])) address hregion)

/-- **The composition, stated once for the shape every container footprint has.**

`Witness` is whatever the representation bound existentially — three heap bases, six, or a whole
`RawV4DescriptorBases`. The caller receives it and owes disjointness against the region it names,
exactly as at a single call site; the run adds nothing to what the parent must discharge except that
it must hold for every sibling rather than one. -/
theorem witnessed_survives_chain {Witness : Type} {P : State → Prop} {region : Witness → Region}
    {start : State}
    (footprint : ∃ w : Witness, ∀ s2 : State,
      (∀ address, region w address → start.mem.get? address = s2.mem.get? address) → P s2)
    (steps : List SiblingStep) (chain : SiblingChain start steps) :
    ∃ w : Witness,
      (∀ step ∈ steps, ∀ address, region w address → ¬ step.2 address) →
      P (chainFinal start steps) := by
  obtain ⟨w, transport⟩ := footprint
  exact ⟨w, fun disjoint => transport _ (chain_agrees_on_region start steps chain disjoint)⟩

/-! ## The clause, written once

**This section is no longer hypothetical.** `WritesOnlyWithinAllocation` moved down to
`Contracts/Environment.lean` and every `post*` predicate now carries it — `WritesOnlyWithinRecord`
(the clause at an empty allocation interval) for the non-allocating routines,
`DecoderEnvironment.WritesOnlyWithinOwnAllocation` for the allocating ones. The earlier wording here
— "it is not added to any contract, and `Containers.lean`, `Collections.lean` and `Entry.lean` are
unmodified" — described the state of the tree before that change and is retained nowhere.

One thing that wording got **wrong** is worth keeping visible, because the correction is now baked
into the contracts: it said an allocating routine "writes nowhere outside those two regions". A bump
allocator also advances `ZKVM_HEAP_POS`, which is in neither region, so the two-region clause is false
of every allocating routine in the decoder. `WritesOnlyWithinOwnAllocation` therefore adds
`env.allocatorState`, and `siblingChain_of_writesOnlyWithinOwnAllocation` below is its join with the
run. The clause still does not cover a callee's stack frame — see that definition's docstring. -/

/-- The clause as a `SiblingStep`, which is the form the run consumes. -/
def allocationStep (recordBase recordSize cursorBefore cursorAfter : Nat) (after : State) :
    SiblingStep :=
  (after, allocatedRegion recordBase recordSize cursorBefore cursorAfter)

/-- A one-step run built from the clause is a `SiblingChain`. Trivial, and it is the join between the
clause's shape and the run's — the place a mismatch between them would show up. -/
theorem siblingChain_of_writesOnlyWithinAllocation
    {recordBase recordSize cursorBefore cursorAfter : Nat} {before after : State}
    (clause : WritesOnlyWithinAllocation recordBase recordSize cursorBefore cursorAfter
      before after) :
    SiblingChain before [allocationStep recordBase recordSize cursorBefore cursorAfter after] :=
  ⟨clause, trivial⟩

/-- A non-allocating routine's clause is the same step at an empty interval, so it needs no separate
lemma — only the observation that `WritesOnlyWithinRecord` is definitionally the clause at `0 0`. -/
theorem siblingChain_of_writesOnlyWithinRecord {recordBase recordSize : Nat} {before after : State}
    (clause : WritesOnlyWithinRecord recordBase recordSize before after) :
    SiblingChain before [allocationStep recordBase recordSize 0 0 after] :=
  siblingChain_of_writesOnlyWithinAllocation clause

/-- The allocating routine's step: its record, its arena interval, and the allocator's own state. -/
def allocatingStep (env : DecoderEnvironment) (recordBase recordSize cursorBefore cursorAfter : Nat)
    (after : State) : SiblingStep :=
  (after, Region.union (allocatedRegion recordBase recordSize cursorBefore cursorAfter)
    env.allocatorState)

/-- **The join for an allocating callee.** The cursor pair is existential in the contract — the
callee reports where the cursor was, it is not told — so the step it produces is existential too, and
a parent that already knows the cursor values (from `postAlloc` or a `Runtime.CursorChain`) reads
them off here rather than guessing.

A parent consuming this owes disjointness against `env.allocatorState` as well as against the record
and the interval. That is not extra work in practice — a representation that lived in the allocator's
own state could not survive any allocation at all — but it is an extra conjunct, and it exists
because the narrow clause was false rather than because the discipline wanted it. -/
theorem siblingChain_of_writesOnlyWithinOwnAllocation {env : DecoderEnvironment}
    {recordBase recordSize : Nat} {before after : State}
    (clause : env.WritesOnlyWithinOwnAllocation recordBase recordSize before after) :
    ∃ cursorBefore cursorAfter,
      SiblingChain before [allocatingStep env recordBase recordSize cursorBefore cursorAfter after] :=
  let ⟨cursorBefore, cursorAfter, _, _, writes⟩ := clause
  ⟨cursorBefore, cursorAfter, writes, trivial⟩

/-! ## The five containers

Each is `witnessed_survives_chain` at the corresponding `Footprint` result. Written out rather than
claimed to follow, because "the rest are identical" is the kind of statement this row has learned not
to accept from itself. -/

theorem executionRequests_survives_chain (base : Nat) (value : SszBridge.RawExecutionRequests)
    (start : State) (established : ExecutionRequestsRep start base value)
    (steps : List SiblingStep) (chain : SiblingChain start steps) :
    ∃ depositsBase withdrawalsBase consolidationsBase,
      (∀ step ∈ steps, ∀ address,
          executionRequestsRegion base 48 depositsBase withdrawalsBase consolidationsBase
            value.deposits.size value.withdrawals.size value.consolidations.size 192 80 116
            address →
          ¬ step.2 address) →
      ExecutionRequestsRep (chainFinal start steps) base value := by
  obtain ⟨depositsBase, withdrawalsBase, consolidationsBase, transport⟩ :=
    executionRequests_footprint base value start established
  exact ⟨depositsBase, withdrawalsBase, consolidationsBase, fun disjoint =>
    transport _ (chain_agrees_on_region start steps chain disjoint)⟩

theorem executionWitness_survives_chain (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : SszBridge.RawExecutionWitness) (start : State)
    (established : ExecutionWitnessRep start inputBase input base value)
    (steps : List SiblingStep) (chain : SiblingChain start steps) :
    ∃ stateBase codesBase headersBase,
      (∀ step ∈ steps, ∀ address,
          executionWitnessRegion base 48 stateBase codesBase headersBase
            value.state.size value.codes.size value.headers.size 16 address →
          ¬ step.2 address) →
      ExecutionWitnessRep (chainFinal start steps) inputBase input base value := by
  obtain ⟨stateBase, codesBase, headersBase, transport⟩ :=
    executionWitness_footprint inputBase input base value start established
  exact ⟨stateBase, codesBase, headersBase, fun disjoint =>
    transport _ (chain_agrees_on_region start steps chain disjoint)⟩

theorem executionPayload_survives_chain (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : SszBridge.RawExecutionPayload) (start : State)
    (established : ExecutionPayloadRep start inputBase input base value)
    (steps : List SiblingStep) (chain : SiblingChain start steps) :
    ∃ transactionsBase withdrawalsBase,
      (∀ step ∈ steps, ∀ address,
          executionPayloadRegion base 592 transactionsBase withdrawalsBase
            value.transactions.size value.withdrawals.size 16 48 address →
          ¬ step.2 address) →
      ExecutionPayloadRep (chainFinal start steps) inputBase input base value := by
  obtain ⟨transactionsBase, withdrawalsBase, transport⟩ :=
    executionPayload_footprint inputBase input base value start established
  exact ⟨transactionsBase, withdrawalsBase, fun disjoint =>
    transport _ (chain_agrees_on_region start steps chain disjoint)⟩

theorem newPayloadRequest_survives_chain (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : SszBridge.RawNewPayloadRequest) (start : State)
    (established : NewPayloadRequestRep start inputBase input base value)
    (steps : List SiblingStep) (chain : SiblingChain start steps) :
    ∃ transactionsBase payloadWithdrawalsBase versionedHashesBase depositsBase
      requestWithdrawalsBase consolidationsBase,
      (∀ step ∈ steps, ∀ address,
          newPayloadRequestRegion base 688 transactionsBase payloadWithdrawalsBase
            versionedHashesBase depositsBase requestWithdrawalsBase consolidationsBase value
            address →
          ¬ step.2 address) →
      NewPayloadRequestRep (chainFinal start steps) inputBase input base value := by
  obtain ⟨transactionsBase, payloadWithdrawalsBase, versionedHashesBase, depositsBase,
    requestWithdrawalsBase, consolidationsBase, transport⟩ :=
    newPayloadRequest_footprint inputBase input base value start established
  exact ⟨transactionsBase, payloadWithdrawalsBase, versionedHashesBase, depositsBase,
    requestWithdrawalsBase, consolidationsBase, fun disjoint =>
      transport _ (chain_agrees_on_region start steps chain disjoint)⟩

/-- **The root.** This is the one the entry point needs: the decoded `RawV4` must still be there when
control reaches the sentinel, however many siblings ran in between. -/
theorem rawV4_survives_chain (inputBase : Nat) (input : ByteArray) (rootBase rootSize : Nat)
    (value : SszBridge.RawV4) (start : State) (fits : 832 ≤ rootSize)
    (hsize : BinaryFv.SSZ.Zesu.Artifact.rawStatelessInputSize = some rootSize)
    (established : RawV4Rep start inputBase input rootBase value)
    (steps : List SiblingStep) (chain : SiblingChain start steps) :
    ∃ bases : RawV4DescriptorBases,
      (∀ step ∈ steps, ∀ address, rawV4Region rootBase rootSize value bases address →
        ¬ step.2 address) →
      RawV4Rep (chainFinal start steps) inputBase input rootBase value := by
  obtain ⟨bases, transport⟩ :=
    rawV4_footprint inputBase input rootBase rootSize value start fits hsize established
  exact ⟨bases, fun disjoint =>
    transport _ (chain_agrees_on_region start steps chain disjoint)⟩

/-! ## The premises can hold, and the sibling really writes

The obligation this module owes itself. Everything above is an implication; an implication whose
antecedent is unsatisfiable proves cleanly and carries nothing, which is the exact defect caught in
this stream's own input-slice corollary. So the premises are discharged against a concrete run.

**Discriminating, not merely satisfiable.** The witness includes `sibling_writes` — a byte that
genuinely changes across the chain — so the surviving representation is surviving a real write rather
than a sibling that did nothing. A no-op sibling would satisfy `SiblingChain` for any region at all
and would prove the conclusion for reasons having nothing to do with the discipline. -/

/-- A concrete run: a withdrawal record at 1000, one sibling owning `[2000, 2048)` and writing in it.

Deliberately *not* stated with abstract bases. The point is that the whole conjunction holds at once
for actual numbers, and abstract bases would let a hidden arithmetic obstruction survive. -/
theorem sibling_chain_is_real :
    ∃ (start : State) (steps : List SiblingStep),
      steps ≠ [] ∧
        SiblingChain start steps ∧
        (∀ step ∈ steps, ∀ address, range 1000 48 address → ¬ step.2 address) ∧
        RawWithdrawalRep start 1000 zeroWithdrawal ∧
        start.mem.get? 2000 ≠ (chainFinal start steps).mem.get? 2000 ∧
        RawWithdrawalRep (chainFinal start steps) 1000 zeroWithdrawal := by
  refine ⟨{ (default : State) with mem := zeroBytes 1000 48 },
          [({ (default : State) with
              mem := (zeroBytes 1000 48).insert 2000 (BitVec.ofNat 8 7) }, range 2000 48)],
          by simp, ⟨?_, trivial⟩, ?_, ?_, ?_, ?_⟩
  · intro address houtside
    show ((zeroBytes 1000 48).insert 2000 (BitVec.ofNat 8 7)).get? address
        = (zeroBytes 1000 48).get? address
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (fun heq => houtside ⟨by omega, by omega⟩)]
  · intro step hstep address ⟨hl, hr⟩
    have hshape : step = ({ (default : State) with
        mem := (zeroBytes 1000 48).insert 2000 (BitVec.ofNat 8 7) }, range 2000 48) := by
      simpa using hstep
    subst hshape
    rintro ⟨hlo, hhi⟩
    omega
  · exact zeroWithdrawal_rep (fun index hindex => zeroBytes_inside hindex) (by omega)
  · show (zeroBytes 1000 48).get? 2000
        ≠ ((zeroBytes 1000 48).insert 2000 (BitVec.ofNat 8 7)).get? 2000
    rw [zeroBytes_outside (fun index hindex => by omega)]
    simp [Std.ExtHashMap.get?_eq_getElem?]
  · refine zeroWithdrawal_rep (base := 1000) (count := 48) (fun index hindex => ?_) (by omega)
    show ((zeroBytes 1000 48).insert 2000 (BitVec.ofNat 8 7)).get? (1000 + index) = _
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (by omega)]
    simpa [Std.ExtHashMap.get?_eq_getElem?] using zeroBytes_inside (base := 1000) hindex

/-- The same run, arrived at through `WritesOnlyWithinAllocation` rather than by naming a region —
so the clause proposed for the contracts is shown to *produce* a usable step, not merely to resemble
one. The record is `[1000, 1048)` and the allocation interval is empty, which is the shape of a
container that allocates nothing. -/
theorem allocation_clause_yields_a_real_step :
    ∃ (before after : State),
      WritesOnlyWithinAllocation 2000 48 3000 3000 before after ∧
        SiblingChain before [allocationStep 2000 48 3000 3000 after] ∧
        RawWithdrawalRep before 1000 zeroWithdrawal ∧
        before.mem.get? 2000 ≠ after.mem.get? 2000 := by
  refine ⟨{ (default : State) with mem := zeroBytes 1000 48 },
          { (default : State) with
            mem := (zeroBytes 1000 48).insert 2000 (BitVec.ofNat 8 7) }, ?_, ?_, ?_, ?_⟩
  · intro address houtside
    show ((zeroBytes 1000 48).insert 2000 (BitVec.ofNat 8 7)).get? address
        = (zeroBytes 1000 48).get? address
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    refine if_neg (fun heq => houtside (Or.inl ⟨by omega, by omega⟩))
  · refine siblingChain_of_writesOnlyWithinAllocation ?_
    intro address houtside
    show ((zeroBytes 1000 48).insert 2000 (BitVec.ofNat 8 7)).get? address
        = (zeroBytes 1000 48).get? address
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    refine if_neg (fun heq => houtside (Or.inl ⟨by omega, by omega⟩))
  · exact zeroWithdrawal_rep (fun index hindex => zeroBytes_inside hindex) (by omega)
  · show (zeroBytes 1000 48).get? 2000
        ≠ ((zeroBytes 1000 48).insert 2000 (BitVec.ofNat 8 7)).get? 2000
    rw [zeroBytes_outside (fun index hindex => by omega)]
    simp [Std.ExtHashMap.get?_eq_getElem?]

/-! ## What the clause cost

Counted rather than estimated, and now counted after the fact rather than before it.

* **18 `post*` predicates** in `Contracts/`. The clause is a conjunct on `post`, so this is the
  number of *places* it is written. 17 carry it; `postZesuDecodeRaw` does not, and its docstring says
  why (its owned set is three separately-addressed globals, which the single-range shape cannot name,
  and it has no siblings).
* **37 post-supplying sites**, not 36. The earlier count came from `grep '^  post :='`, which sees 36
  `FunctionContract` records and misses `ExportedDecoder.lean:280` — the exported wrapper supplies
  `exit := postZesuDecodeRaw …` on a `FunctionInstanceContract`, whose binding field is named `exit`
  rather than `post`. The number is fixed here rather than the grep.
* **The record size was *not* already in scope**, contrary to the estimate. `args.resultBase` and
  `postAlloc`'s cursor pair were; the ABI record size was in scope only for the options
  (`env.optionalU64.size`), `readArray` (its `length`) and `memcpy` (`args.length`). The seven
  containers and the entry had nothing, so `DecoderEnvironment` gained a `record : ResultRecordSizes`
  field sourced from the manifest — a literal per contract site was rejected for the reason
  `Artifact.AbiManifest` already gives about footprints, with the sign flipped: an over-large
  permission weakens the clause and proves exactly as easily.
* **`contractAllocatorFree` needs nothing**: `Runtime.lean` already states an unrestricted total
  frame, which implies the clause for every region. It is the one contract in the layer that did —
  and it is also the proof that the vocabulary and the ability to state a frame were available here
  all along, so the absence elsewhere was a choice or an oversight rather than a framework limit.

**On "linear, not quadratic" — true of the contracts, and only a quarter true of the discharge.**
Each callee promises confinement to its own region, one clause per contract, and that side really is
linear: 17 clauses, not 17² sibling pairs. But the parent's side is not free.
`Footprint.allocatedRegion_disjoint_of_later` has **four** hypotheses, and only `ordered` comes from
bump monotonicity. `records`, `recordBelowSibling` and `siblingRecordOutside` are placement facts the
parent supplies **per sibling pair** — so three quarters of each pairwise discharge is parent work
that no contract clause removes. `Footprint.lean`'s own docstring on that lemma says exactly this
("sibling disjointness comes free from bump monotonicity is true of the **allocations** and not of
the records"); the summary here used to contradict it, which is how the claim survived. -/

end BinaryFv.SSZ.Zesu.Contracts.OwnershipComposition
