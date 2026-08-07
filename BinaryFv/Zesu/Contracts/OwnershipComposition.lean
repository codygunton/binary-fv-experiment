import BinaryFv.Zesu.Contracts.Footprint

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

These generic composition lemmas remain available for later hierarchical refinements; their contract
premises still need to be proved against real callees.

## The shape every container footprint already has

`Footprint`'s container results all read `∃ witnesses, ∀ s2, agreement-on-their-region → rep s2`.
That is exactly what `chain_agrees_on_region` feeds: agreement on a region propagates along a run of
siblings whenever each sibling's writes are confined and its permitted region misses the one being
protected. So one lemma serves all five containers, and the per-container corollaries are three lines
each rather than five separate arguments.

## The premises are exhibited satisfiable, with a sibling that really writes

A composition theorem whose ownership premises could not all hold would prove cleanly and mean
nothing. `sibling_chain_is_real`
discharges it against a concrete run, and it is *discriminating*: the sibling genuinely modifies
memory (a byte changes across the chain), so the conclusion is not surviving a no-op.
-/

namespace BinaryFv.Zesu.Contracts.OwnershipComposition

open BinaryFv.RiscV
open BinaryFv.Zesu.DecodedValue
open BinaryFv.Zesu.Contracts.Ownership
open BinaryFv.Zesu.Contracts.Footprint

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
`StatelessInputDescriptorBases`. The caller receives it and owes disjointness against the region it names,
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

**This section is no longer hypothetical.** The ownership vocabulary lives in
`Contracts/Environment.lean` and every `post*` predicate but one now carries a clause built from it —
`DecoderEnvironment.WritesOnlyWithinOwnRecord` for the non-allocating function instances,
`DecoderEnvironment.WritesOnlyWithinOwnAllocation` for the allocating ones. The earlier wording here
— "it is not added to any contract, and `Containers.lean`, `Collections.lean` and `Entry.lean` are
unmodified" — described the state of the tree before that change and is retained nowhere.

**The permitted region was wrong twice, in the same direction, and both corrections are now baked
in.** First: an allocating function instance was said to "write nowhere outside those two regions", but a bump
allocator advances `ZKVM_HEAP_POS`, which is in neither, so the two-region clause was false of every
allocating function instance in the decoder. Then: *every* compiled function instance writes its stack frame, which is in
none of the three, so the three-region clause was false of every function instance whatsoever.
`DecoderEnvironment.ownedRegion` is the corrected four-region form and
`siblingChain_of_writesOnlyWithinOwnAllocation` is its join with the run.

Both corrections have the same shape and the same justification, and it is worth naming because the
error is easy to repeat: a *permission* clause is weakened by adding a region, so the tempting
instinct is to keep it narrow. That instinct is right only while the clause remains satisfiable. Past
that point the clause is not strong but false, and a false contract premise makes a conditional root
vacuous. `stack_writing_routine_satisfies_the_clause` below is the standing check that the current
form has not crossed that line. -/

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

/-- A **non-allocating** function instance's step: its record and its stack frame. -/
def recordStep (env : DecoderEnvironment) (recordBase recordSize : Nat) (after : State) :
    SiblingStep :=
  (after, Region.union (allocatedRegion recordBase recordSize 0 0) env.stack)

/-- The join for a non-allocating callee. -/
theorem siblingChain_of_writesOnlyWithinOwnRecord {env : DecoderEnvironment}
    {recordBase recordSize : Nat} {before after : State}
    (clause : env.WritesOnlyWithinOwnRecord recordBase recordSize before after) :
    SiblingChain before [recordStep env recordBase recordSize after] :=
  ⟨clause, trivial⟩

/-- The allocating function instance's step: `DecoderEnvironment.ownedRegion` — record, arena interval,
allocator state, stack. -/
def allocatingStep (env : DecoderEnvironment) (recordBase recordSize cursorBefore cursorAfter : Nat)
    (after : State) : SiblingStep :=
  (after, env.ownedRegion recordBase recordSize cursorBefore cursorAfter)

/-- **The join for an allocating callee.** The cursor pair is existential in the contract — the
callee reports where the cursor was, it is not told — so the step it produces is existential too, and
a parent that already knows the cursor values (from `postAlloc` or a `Runtime.CursorChain`) reads
them off here rather than guessing.

A parent consuming this owes disjointness against `env.allocatorState` and `env.stack` as well as
against the record and the interval. Neither is extra work in practice — a representation living in
the allocator's own state could not survive any allocation, and one living in the machine stack could
not survive any call — but both are extra conjuncts, and they exist because the narrower clauses were
*false* rather than because the discipline wanted them. -/
theorem siblingChain_of_writesOnlyWithinOwnAllocation {env : DecoderEnvironment}
    {recordBase recordSize : Nat} {before after : State}
    (clause : env.WritesOnlyWithinOwnAllocation recordBase recordSize before after) :
    ∃ cursorBefore cursorAfter,
      SiblingChain before [allocatingStep env recordBase recordSize cursorBefore cursorAfter after] :=
  let ⟨cursorBefore, cursorAfter, _, _, writes⟩ := clause
  ⟨cursorBefore, cursorAfter, writes, trivial⟩

/-! ## The five containers

Each is `witnessed_survives_chain` at the corresponding `Footprint` result. Written out rather than
claimed to follow, because "the rest are identical" is not a proof
to accept from itself. -/

theorem executionRequests_survives_chain (base : Nat) (value : BinaryFv.Specs.SSZ.RawExecutionRequests)
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
    (value : BinaryFv.Specs.SSZ.RawExecutionWitness) (start : State)
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
    (value : BinaryFv.Specs.SSZ.RawExecutionPayload) (start : State)
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
    (value : BinaryFv.Specs.SSZ.RawNewPayloadRequest) (start : State)
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

/-- **The root.** This is the one the entry point needs: the decoded `StatelessInput` must still be there when
control reaches the sentinel, however many siblings ran in between. -/
theorem statelessInput_survives_chain (inputBase : Nat) (input : ByteArray) (rootBase rootSize : Nat)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (start : State) (fits : 832 ≤ rootSize)
    (hsize : BinaryFv.Zesu.Artifacts.rawStatelessInputSize = some rootSize)
    (established : StatelessInputRep start inputBase input rootBase value)
    (steps : List SiblingStep) (chain : SiblingChain start steps) :
    ∃ bases : StatelessInputDescriptorBases,
      (∀ step ∈ steps, ∀ address, statelessInputRegion rootBase rootSize value bases address →
        ¬ step.2 address) →
      StatelessInputRep (chainFinal start steps) inputBase input rootBase value := by
  obtain ⟨bases, transport⟩ :=
    statelessInput_footprint inputBase input rootBase rootSize value start fits hsize established
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

/-! ## The clause is satisfiable by a function instance that touches its stack frame

**The obligation this whole layer stands or falls on.** If no compiled function instance could satisfy the
clause, any conditional theorem consuming it would be vacuous while reading as though it had been
strengthened — strictly worse than the gap the clause was closing. `sibling_chain_is_real` above
shows the *composition's* premises can hold; this shows the **contract's** can, at the shape a real
function instance actually has.

Real, here, means all three at once: the function instance writes its result record, it advances the bump
cursor and writes inside the interval it consumed, **and it writes an address in the machine stack
that is in none of the other regions.** The last is what the previous clause could not survive, and
the theorem's final conjunct says so directly — at this very run, the region without `env.stack` is
**refuted** while `ownedRegion` is satisfied. That pair is the change.

The stack byte's disjointness from the other three regions is stated as conjuncts rather than left to
be read off the numbers, because that is the whole difference between a witness and a witness with
power: without it, an identical-looking theorem would prove even if the stack union were redundant.
The record and the allocation interval *do* overlap here (`[100, 108) ⊆ [0, 256)`) and that is
faithful rather than sloppy — an allocated record lies inside the interval it was cut from, which is
exactly what `postAlloc`'s containment clause exists to give. -/

/-- A concrete environment: allocator state `[900, 908)`, an arena the cursor runs through from `0`,
and a 64-byte stack at `[1000, 1064)`, well away from both.

Minimal like `FrameGap.gapEnv`, and for the same reason — its only job is to witness that the clause
can be met — but unlike `gapEnv` its stack is **not** empty, because that is the whole point here. -/
def frameEnv : DecoderEnvironment where
  image := ⟨#[]⟩
  allocatorState := range 900 8
  heapPosAddr := 900
  arenaBase := 0
  optionalBlobSchedule := default
  blobSchedule := ⟨0, 0, 0⟩
  optionalU64 := default
  record := default
  stack := range 1000 64

theorem frameEnv_readFileByte (address : Nat) : frameEnv.image.readFileByte? address = none := rfl

/-! ### The two states

Named rather than inlined: the witness has to say things about the same pair of states from a dozen
directions, and an inlined `Std.ExtHashMap` insert chain makes each of those a wall. -/

/-- Before the call: 1100 zero bytes, covering every address the witness names. The cursor at `900`
therefore reads `0`. -/
def frameBefore : State := { (default : State) with mem := zeroBytes 0 1100 }

/-- After the call. Four writes, one per owned region: the record byte at `100`, a byte at `220`
inside the arena interval the function instance consumed, the cursor's second byte at `901` (advancing it from
`0` to `256`), and `1016` — **the stack frame**. -/
def frameAfter : State :=
  { (default : State) with
    mem := ((((zeroBytes 0 1100).insert 100 (BitVec.ofNat 8 3)).insert 220
      (BitVec.ofNat 8 7)).insert 901 (BitVec.ofNat 8 1)).insert 1016 (BitVec.ofNat 8 9) }

theorem frameBefore_get {address : Nat} (h : address < 1100) :
    frameBefore.mem.get? address = some (BitVec.ofNat 8 0) := by
  simpa [frameBefore] using zeroBytes_inside (base := 0) (count := 1100) h

/-- Away from the four written addresses the two states agree — which is the whole content of the
ownership clause, stated once and applied at every address the proof needs. -/
theorem frameAfter_get_of_ne {address : Nat}
    (h100 : address ≠ 100) (h220 : address ≠ 220) (h901 : address ≠ 901) (h1016 : address ≠ 1016) :
    frameAfter.mem.get? address = frameBefore.mem.get? address := by
  show (((((zeroBytes 0 1100).insert 100 (BitVec.ofNat 8 3)).insert 220
    (BitVec.ofNat 8 7)).insert 901 (BitVec.ofNat 8 1)).insert 1016
      (BitVec.ofNat 8 9)).get? address = (zeroBytes 0 1100).get? address
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  rw [if_neg (fun heq => h1016 heq.symm), if_neg (fun heq => h901 heq.symm),
    if_neg (fun heq => h220 heq.symm), if_neg (fun heq => h100 heq.symm)]

theorem frameAfter_get_100 : frameAfter.mem.get? 100 = some (BitVec.ofNat 8 3) := by
  show (((((zeroBytes 0 1100).insert 100 (BitVec.ofNat 8 3)).insert 220
    (BitVec.ofNat 8 7)).insert 901 (BitVec.ofNat 8 1)).insert 1016
      (BitVec.ofNat 8 9)).get? 100 = _
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
  simp

theorem frameAfter_get_220 : frameAfter.mem.get? 220 = some (BitVec.ofNat 8 7) := by
  show (((((zeroBytes 0 1100).insert 100 (BitVec.ofNat 8 3)).insert 220
    (BitVec.ofNat 8 7)).insert 901 (BitVec.ofNat 8 1)).insert 1016
      (BitVec.ofNat 8 9)).get? 220 = _
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
  simp

theorem frameAfter_get_901 : frameAfter.mem.get? 901 = some (BitVec.ofNat 8 1) := by
  show (((((zeroBytes 0 1100).insert 100 (BitVec.ofNat 8 3)).insert 220
    (BitVec.ofNat 8 7)).insert 901 (BitVec.ofNat 8 1)).insert 1016
      (BitVec.ofNat 8 9)).get? 901 = _
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
  simp

theorem frameAfter_get_1016 : frameAfter.mem.get? 1016 = some (BitVec.ofNat 8 9) := by
  show (((((zeroBytes 0 1100).insert 100 (BitVec.ofNat 8 3)).insert 220
    (BitVec.ofNat 8 7)).insert 901 (BitVec.ofNat 8 1)).insert 1016
      (BitVec.ofNat 8 9)).get? 1016 = _
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
  simp

/-- Every byte of the cursor word except the one the function instance advanced is still zero. -/
theorem frameAfter_get_cursorByte {index : Nat} (h : index < 8) (hne : index ≠ 1) :
    frameAfter.mem.get? (900 + index) = some (BitVec.ofNat 8 0) := by
  rw [frameAfter_get_of_ne (address := 900 + index) (by omega) (by omega) (by omega) (by omega)]
  exact frameBefore_get (by omega)

/-- The bump cursor stood at `0`. -/
theorem frameEnv_cursor_before : frameEnv.cursor? frameBefore = some 0 := by
  refine observe_word64_of_rep _ _ _ (by omega) ?_
  intro index hindex
  show frameBefore.mem.get? (900 + index) = _
  rw [frameBefore_get (by omega)]
  have : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨
      index = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The function instance allocated:** the cursor stands at `256` afterwards, so the interval `[0, 256)` is
what it consumed. -/
theorem frameEnv_cursor_after : frameEnv.cursor? frameAfter = some 256 := by
  refine observe_word64_of_rep _ _ _ (by omega) ?_
  intro index hindex
  show frameAfter.mem.get? (900 + index) = _
  have : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨
      index = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [frameAfter_get_cursorByte (by omega) (by omega)]
  · show frameAfter.mem.get? 901 = _
    rw [frameAfter_get_901]
  all_goals rw [frameAfter_get_cursorByte (by omega) (by omega)]

/-- **A function instance shaped like a real one satisfies the strengthened clause, and refutes the previous
one.**

The run: the record byte at `100` goes `0 → 3`; the cursor at `900` advances `0 → 256` and the
function instance writes at `220`, inside the interval it consumed; and it writes `1016`, in its stack frame.

The conjuncts after the contract are what make the stack union load-bearing rather than decorative —
that address is in `env.stack` and in none of the other three regions — and the last conjunct of all
records that the clause **as it stood before this change is false of this run**. A satisfiability
witness alone would not have shown that: it would look identical if the stack union were redundant.

Concrete rather than abstract for the reason `sibling_chain_is_real` gives: abstract bases let a
hidden arithmetic obstruction survive. -/
theorem stack_writing_routine_satisfies_the_clause :
    ∃ args : ContainerArgs,
      args.resultBase = 100 ∧
      postAllocatingContainer frameEnv args (FrameGap.bytePinned 3) 8 (.ok ())
          frameBefore frameAfter ∧
        -- it wrote its record
        frameBefore.mem.get? 100 ≠ frameAfter.mem.get? 100 ∧
        -- it advanced the allocator
        frameEnv.cursor? frameBefore = some 0 ∧ frameEnv.cursor? frameAfter = some 256 ∧
        -- it wrote inside the interval it consumed
        frameBefore.mem.get? 220 ≠ frameAfter.mem.get? 220 ∧
        -- and it touched its stack frame, at an address nothing else owns
        frameBefore.mem.get? 1016 ≠ frameAfter.mem.get? 1016 ∧
        frameEnv.stack 1016 ∧
        ¬ allocatedRegion 100 8 0 256 1016 ∧ ¬ frameEnv.allocatorState 1016 ∧
        -- so the clause without the stack is refuted by this very run
        ¬ WritesOnlyWithin (Region.union (allocatedRegion 100 8 0 256) frameEnv.allocatorState)
            frameBefore frameAfter := by
  refine ⟨⟨0, ByteArray.empty, 0, 100⟩, rfl,
    ⟨?_, ?_, ⟨0, 256, frameEnv_cursor_before, frameEnv_cursor_after, ?_⟩, ?_⟩,
    ?_, frameEnv_cursor_before, frameEnv_cursor_after, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro index h; exact absurd h (by simp)
  · intro a b h; exact absurd h (by rw [frameEnv_readFileByte]; simp)
  · -- every write landed inside the owned region
    intro address houtside
    refine frameAfter_get_of_ne ?_ ?_ ?_ ?_
    · intro heq
      refine houtside (Or.inl (Or.inl ?_))
      show (100 : Nat) ≤ address ∧ address < 100 + 8
      omega
    · intro heq
      refine houtside (Or.inl (Or.inr ?_))
      show (0 : Nat) ≤ address ∧ address < 256
      omega
    · intro heq
      refine houtside (Or.inr (Or.inl ?_))
      show (900 : Nat) ≤ address ∧ address < 900 + 8
      omega
    · intro heq
      refine houtside (Or.inr (Or.inr ?_))
      show (1000 : Nat) ≤ address ∧ address < 1000 + 64
      omega
  · show frameAfter.mem.get? 100 = some 3
    exact frameAfter_get_100
  · rw [frameBefore_get (address := 100) (by omega), frameAfter_get_100]; simp
  · rw [frameBefore_get (address := 220) (by omega), frameAfter_get_220]; simp
  · rw [frameBefore_get (address := 1016) (by omega), frameAfter_get_1016]; simp
  · show (1000 : Nat) ≤ 1016 ∧ (1016 : Nat) < 1000 + 64
    omega
  · rintro (⟨_, h⟩ | ⟨_, h⟩) <;>
      · revert h; show ¬ (1016 : Nat) < _; omega
  · show ¬ ((900 : Nat) ≤ 1016 ∧ (1016 : Nat) < 900 + 8)
    omega
  · -- the stackless region cannot explain the stack write
    intro confined
    have hagree : frameAfter.mem.get? 1016 = frameBefore.mem.get? 1016 := by
      refine confined 1016 ?_
      rintro ((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) <;>
        · revert h; show ¬ (1016 : Nat) < _; omega
    rw [frameBefore_get (address := 1016) (by omega), frameAfter_get_1016] at hagree
    simp at hagree

/-! ## What the clause cost

Counted rather than estimated, and now counted after the fact rather than before it.

* **18 `post*` predicates** in `Contracts/`. The clause is a conjunct on `post`, so this is the
  number of *places* it is written. 17 carry it; `postZesuDecodeRaw` does not, and its docstring says
  why (its owned set is three separately-addressed globals, which the single-range shape cannot name,
  and it has no siblings).
* **37 post-supplying sites**, not 36. The earlier count came from `grep '^  post :='`, which sees 36
  `FunctionContract` records and misses `ExportedDecoder.lean:365` — the exported wrapper supplies
  `exit := postZesuDecodeRaw …` on a `FunctionInstanceContract`, whose binding field is named `exit`
  rather than `post`. The number is fixed here rather than the grep.
* **The record size was *not* already in scope**, contrary to the estimate. `args.resultBase` and
  `postAlloc`'s cursor pair were; the ABI record size was in scope only for the options
  (`env.optionalU64.size`), `readArray` (its `length`) and `memcpy` (`args.length`). The seven
  containers and the entry had nothing, so `DecoderEnvironment` gained a `record : ResultRecordSizes`
  field sourced from the manifest — a literal per contract site was rejected for the reason
  `Artifacts.AbiManifest` already gives about footprints, with the sign flipped: an over-large
  permission weakens the clause and proves exactly as easily.
* **`contractAllocatorFree` was read as needing nothing, and that reading was wrong.** It stated an
  unrestricted total memory frame, which does imply the clause for every region — but only a function instance
  that never touches the stack can satisfy it, so it was the same unsatisfiability defect wearing the
  opposite costume: too strong rather than too weak, and equally fatal to an assumed hypothesis. It
  now carries `env.WritesOnlyWithinOwnRecord 0 0` like the other no-op function instances.
* **`contractAllocatorCtor` was the remaining hole and is closed.** It writes an `AllocatorObjectRep`
  at its result base and carried no clause at all; it now carries one at
  `env.record.allocatorObject`, the span that representation pins.
* **`contractAllocatorResize` and `contractAllocatorRemap` still carry no ownership clause.** Not a
  falsehood — they simply say less than they could — but recorded so the gap is visible rather than
  discovered.

**On "linear, not quadratic" — true of the contracts, and only a quarter true of the discharge.**
Each callee promises confinement to its own region, one clause per contract, and that side really is
linear: 17 clauses, not 17² sibling pairs. But the parent's side is not free.
`Footprint.allocatedRegion_disjoint_of_later` has **four** hypotheses, and only `ordered` comes from
bump monotonicity. `records`, `recordBelowSibling` and `siblingRecordOutside` are placement facts the
parent supplies **per sibling pair** — so three quarters of each pairwise discharge is parent work
that no contract clause removes. `Footprint.lean`'s own docstring on that lemma says exactly this
("sibling disjointness comes free from bump monotonicity is true of the **allocations** and not of
the records"); the summary here used to contradict it, which is how the claim survived. -/

end BinaryFv.Zesu.Contracts.OwnershipComposition
