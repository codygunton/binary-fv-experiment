import BinaryFv.RiscV.Elfling.Boundary
import BinaryFv.RiscV.Elfling.ProgramGeometry

/-!
# The sequential splice: composing two adjacent disjoint regions

`Boundary.lean` gives four `ScopedTrace` constructors. Read literally, none of them is "compose two
adjacent disjoint regions": `exitAt` and `ownStep` do not mention a child at all, `callStep` demands
a call/return pair, and `inlineStep` demands that control re-enter the parent.

That last demand is the whole question, and the answer turns on what *the parent* is. If the parent
owns only the code between its children, then a segment whose successor is the next segment does not
re-enter it and nothing composes. If the parent's region is the union of the segments — which is
exactly the geometry real inlining already has, a child's addresses lying inside its parent's — then
"re-enter the parent" is satisfied by landing in the *next segment*, and `inlineStep` composes the
pair with no change to the inductive type.

This module builds that out.

* `SequentialCut` is the static side: two units and the crossing edge, with the side conditions the
  splice actually consumes (§1). `SequentialCut.firstBoundary_validFor` turns a checked cut into the
  `InlineBoundary.validFor` the constructor demands.
* `ScopedTrace.spliceSegment` spends one segment's summary and resumes at the next segment's entry;
  `ScopedTrace.spliceTail` spends the last one and stops on the parent's exit (§2).
* `ConfinedPrefix` / `SegmentChain` fold a chain of `k` segments into one trace of exactly
  `Σ usedᵢ + k` steps (§3).
* §4 handles a tail child body directly. `ScopedTrace.childBody` consumes only the selected summary,
  so its continuation can stop on the parent's exit without inventing an outgoing edge. The separate
  `inlineTransfer_needs_outgoing_edge` theorem still records why `InlineTransfer` itself cannot do so.
* §5 records the corresponding flat composition — `FunctionTrace.spliceAdjacent` composes
  adjacent regions even when the second owns the exit — so the deficiency is specific to
  `ScopedTrace`.

Nothing here adds a constructor, changes an inductive type, or touches an existing proof.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV

/-! ## 1. The static side of a cut

A cut is two units of one parent plus the control-flow edge that leaves the first and enters the
second. The fields of `SequentialCut.Valid` are exactly the checks `InlineBoundary.validFor` and
`InlineTransfer` will consume — no more, no less — so "what the splice requires of a cut" is a
readable list rather than a claim. -/

/-- Two adjacent units of one parent, and the crossing edge between them. -/
structure SequentialCut where
  /-- The complete generated program whose edge inventory validates the cut. -/
  program : Program
  /-- The unit whose region contains both segments. -/
  parent : FunctionInstance
  /-- The segment control leaves. -/
  first : FunctionInstance
  /-- The segment control enters. -/
  second : FunctionInstance
  /-- The crossing edge: its source is `first`'s stopping pc, its target is `second`'s entry. -/
  cross : DirectEdge

namespace SequentialCut

/-- The inline boundary a cut presents to `ScopedTrace.inlineStep`.

`entries` is empty on purpose. The entry edge of an inlined child is retired by the parent step that
*precedes* the splice; for the first segment of a chain there is no such step, because the parent is
entered directly at that segment's entry. `InlineBoundary.validFor` quantifies over `entries`, so an
empty array is honest rather than convenient: it asserts nothing. -/
def firstBoundary (c : SequentialCut) : InlineBoundary :=
  { child := c.first.id, entries := #[], exits := #[c.cross] }

/--
**What a sequential cut must satisfy.** Every field is a decidable check on generated data.

`crossTargetInParent` together with `crossTargetNotInFirst` is the "re-enters the parent" condition:
it is met by landing in the *second* segment, provided the second segment is inside the parent.
`disjoint` is what makes the two units a genuine split rather than a re-covering.
-/
structure Valid (c : SequentialCut) : Prop where
  /-- The first segment is a declared child of the parent. -/
  childListed : c.first.id ∈ c.parent.children
  /-- The crossing edge is one of the parent's recorded edges. -/
  crossIsRealEdge : programContainsEdge c.program c.cross = true
  /-- The edge leaves from inside the first segment. -/
  crossLeavesFirst : c.first.containsAddress c.cross.source = true
  /-- …and lands outside it. -/
  crossTargetNotInFirst : c.first.containsAddress c.cross.target = false
  /-- …but still inside the parent. This is what `inlineStep` calls re-entering the parent. -/
  crossTargetInParent : c.parent.containsAddress c.cross.target = true
  /-- The landing address is the second segment's own entry pc, so the next splice can fire there. -/
  crossTargetIsSecondEntry : c.cross.target = c.second.entryPc
  /-- The second segment lies inside the parent. -/
  secondInsideParent : ∀ a, c.second.containsAddress a = true → c.parent.containsAddress a = true
  /-- The two segments are disjoint. -/
  segmentsDisjoint : ∀ a, c.first.containsAddress a = true → c.second.containsAddress a = false

/-- A checked cut presents a valid inline boundary. This is the only place the cut's fields are
converted into the constructor's premise. -/
theorem firstBoundary_validFor {c : SequentialCut} (h : c.Valid) :
    c.firstBoundary.validFor c.program c.parent c.first := by
  refine ⟨rfl, h.childListed, ?_, ?_⟩
  · intro e he
    simp [firstBoundary] at he
  · intro e he
    simp only [firstBoundary, Array.mem_singleton] at he
    subst he
    exact ⟨h.crossIsRealEdge, h.crossLeavesFirst, h.crossTargetNotInFirst, h.crossTargetInParent⟩

end SequentialCut

/-! ## 2. One splice

Both lemmas below are `ScopedTrace.inlineStep` with the `InlineTransfer` assembled from a checked
cut. They are stated in the cut's vocabulary so the hypothesis list *is* the answer to "what does
the splice require". -/

/--
**The sequential splice.** Spend the first segment's summary, retire the crossing edge, and continue
at the second segment's entry.

The step arithmetic is the constructor's: `used` steps inside the segment plus exactly one for the
crossing edge. Nothing here can drop the edge or invent a body length.
-/
theorem ScopedTrace.spliceSegment {own exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {c : SequentialCut} (hcut : c.Valid)
    {fromStep used count : Nat} {s sExit sResume s'' : State}
    {entryPc crossPc resumePc : BitVec 64}
    (hAtEntry : s.regs.get? PC = some entryPc)
    (hEntryIsSegmentEntry : entryPc.toNat = c.first.entryPc)
    (hEntryInRegion : own entryPc)
    (hEntryNotExit : ¬ exit entryPc)
    (hBody : childSummary c.first.id fromStep used s sExit)
    (hAtCross : sExit.regs.get? PC = some crossPc)
    (hCrossIsEdgeSource : crossPc.toNat = c.cross.source)
    (hCrossInRegion : own crossPc)
    (hCrossNotExit : ¬ exit crossPc)
    (hRetireCross : Runs (try_step (fromStep + used) false) sExit sResume false)
    (hAtResume : sResume.regs.get? PC = some resumePc)
    (hResumeIsEdgeTarget : resumePc.toNat = c.cross.target)
    (hResumeInRegion : own resumePc)
    (hrest : ScopedTrace own exit childSummary (fromStep + used + 1) count sResume s'') :
    ScopedTrace own exit childSummary fromStep (used + 1 + count) s s'' :=
  ScopedTrace.inlineStep fromStep used count c.firstBoundary c.program c.parent c.first
    s sResume s''
    { valid := SequentialCut.firstBoundary_validFor hcut
      entryPc := entryPc
      atEntry := hAtEntry
      entryAccepted := Or.inl hEntryIsSegmentEntry
      entryInRegion := hEntryInRegion
      entryNotExit := hEntryNotExit
      sExit := sExit
      body := hBody
      exitEdge := c.cross
      exitEdgeMem := by simp [SequentialCut.firstBoundary]
      childExitPc := crossPc
      atExit := hAtCross
      exitIsEdgeSource := hCrossIsEdgeSource
      exitInRegion := hCrossInRegion
      exitNotExit := hCrossNotExit
      doExit := hRetireCross
      resumePc := resumePc
      atResume := hAtResume
      resumeIsEdgeTarget := hResumeIsEdgeTarget
      resumeInRegion := hResumeInRegion }
    hrest

/--
**The terminal splice.** Identical to `spliceSegment` except the parent stops after retiring the
crossing edge, because the address it lands on is one of the parent's own exits.

This is the case the parent's exit pc must be *left to the parent* for. `c.second` here is the
degenerate "segment" consisting of the exit address itself; `Valid.crossTargetNotInFirst` is exactly
the requirement that the last real segment does not own it.
-/
theorem ScopedTrace.spliceTail {own exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {c : SequentialCut} (hcut : c.Valid)
    {fromStep used : Nat} {s sExit sResume : State}
    {entryPc crossPc resumePc : BitVec 64}
    (hAtEntry : s.regs.get? PC = some entryPc)
    (hEntryIsSegmentEntry : entryPc.toNat = c.first.entryPc)
    (hEntryInRegion : own entryPc)
    (hEntryNotExit : ¬ exit entryPc)
    (hBody : childSummary c.first.id fromStep used s sExit)
    (hAtCross : sExit.regs.get? PC = some crossPc)
    (hCrossIsEdgeSource : crossPc.toNat = c.cross.source)
    (hCrossInRegion : own crossPc)
    (hCrossNotExit : ¬ exit crossPc)
    (hRetireCross : Runs (try_step (fromStep + used) false) sExit sResume false)
    (hAtResume : sResume.regs.get? PC = some resumePc)
    (hResumeIsEdgeTarget : resumePc.toNat = c.cross.target)
    (hResumeInRegion : own resumePc)
    (hResumeIsExit : exit resumePc) :
    ScopedTrace own exit childSummary fromStep (used + 1) s sResume :=
  ScopedTrace.spliceSegment hcut hAtEntry hEntryIsSegmentEntry hEntryInRegion hEntryNotExit hBody
    hAtCross hCrossIsEdgeSource hCrossInRegion hCrossNotExit hRetireCross hAtResume
    hResumeIsEdgeTarget hResumeInRegion
    (ScopedTrace.exitAt (fromStep + used + 1) sResume resumePc hAtResume hResumeIsExit)

/-! ## 3. A chain of segments

The splice above is one link. A `k`-segment chain is folded by the same continuation-transformer
device a loop uses: a segment is not a trace (it does not stop at a parent exit), it is a thing that
turns any continuation into a longer trace. -/

/-- `len` retired steps that stay inside `own`, off every `exit`, expressed by what they do to a
continuation. A spliced segment is one of these; so is a retired own instruction. -/
def ConfinedPrefix (own exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop)
    (fromStep len : Nat) (s s' : State) : Prop :=
  ∀ (m : Nat) (t : State),
    ScopedTrace own exit childSummary (fromStep + len) m s' t →
      ScopedTrace own exit childSummary fromStep (len + m) s t

namespace ConfinedPrefix

variable {own exit : BitVec 64 → Prop}
  {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}

theorem nil {a : Nat} {s : State} : ConfinedPrefix own exit childSummary a 0 s s := by
  intro m t h; simpa using h

/-- One parent-owned, in-region, non-exit instruction is a one-step confined prefix. -/
theorem ownStep {a : Nat} {s s' : State} {pc : BitVec 64}
    (atPc : s.regs.get? PC = some pc) (inRegion : own pc) (notExit : ¬ exit pc)
    (step : Runs (try_step a false) s s' false) :
    ConfinedPrefix own exit childSummary a 1 s s' := by
  intro count final rest
  simpa [Nat.add_comm] using
    ScopedTrace.ownStep a count pc s s' final atPc inRegion notExit step rest

/-- A checked emitted call, child body, and return form one confined prefix. -/
theorem ofCall {a used : Nat} {s s' : State} {call : CallSite} {program : Program}
    {functionInstance callee : FunctionInstance}
    (transfer : CallTransfer own exit childSummary call program functionInstance callee
      a used s s') :
    ConfinedPrefix own exit childSummary a (1 + used + 1) s s' := by
  intro count final rest
  have shift : a + (1 + used + 1) = a + 1 + used + 1 := by omega
  rw [shift] at rest
  exact ScopedTrace.callStep a used count call program functionInstance callee s s' final
    transfer rest

/-- One spliced segment is a prefix of length `used + 1`: the summary's own steps plus the crossing
edge. -/
theorem ofSegment {c : SequentialCut} (hcut : c.Valid)
    {fromStep used : Nat} {s sExit sResume : State} {entryPc crossPc resumePc : BitVec 64}
    (hAtEntry : s.regs.get? PC = some entryPc)
    (hEntryIsSegmentEntry : entryPc.toNat = c.first.entryPc)
    (hEntryInRegion : own entryPc)
    (hEntryNotExit : ¬ exit entryPc)
    (hBody : childSummary c.first.id fromStep used s sExit)
    (hAtCross : sExit.regs.get? PC = some crossPc)
    (hCrossIsEdgeSource : crossPc.toNat = c.cross.source)
    (hCrossInRegion : own crossPc)
    (hCrossNotExit : ¬ exit crossPc)
    (hRetireCross : Runs (try_step (fromStep + used) false) sExit sResume false)
    (hAtResume : sResume.regs.get? PC = some resumePc)
    (hResumeIsEdgeTarget : resumePc.toNat = c.cross.target)
    (hResumeInRegion : own resumePc) :
    ConfinedPrefix own exit childSummary fromStep (used + 1) s sResume := by
  intro m t h
  have hshift : fromStep + (used + 1) = fromStep + used + 1 := by omega
  rw [hshift] at h
  have := ScopedTrace.spliceSegment hcut hAtEntry hEntryIsSegmentEntry hEntryInRegion hEntryNotExit
    hBody hAtCross hCrossIsEdgeSource hCrossInRegion hCrossNotExit hRetireCross hAtResume
    hResumeIsEdgeTarget hResumeInRegion h
  simpa using this

theorem trans {a n m : Nat} {s s1 s2 : State}
    (h1 : ConfinedPrefix own exit childSummary a n s s1)
    (h2 : ConfinedPrefix own exit childSummary (a + n) m s1 s2) :
    ConfinedPrefix own exit childSummary a (n + m) s s2 := by
  intro k t h
  have hshift : a + (n + m) = a + n + m := by omega
  have h' : ScopedTrace own exit childSummary (a + n + m) k s2 t := by rwa [hshift] at h
  have hcount : n + m + k = n + (m + k) := by omega
  rw [hcount]
  exact h1 (m + k) t (h2 k t h')

end ConfinedPrefix

/-- A chain of confined prefixes, with the retired length of each link recorded. -/
inductive SegmentChain (own exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop) :
    Nat → State → List Nat → State → Prop where
  | nil (a : Nat) (s : State) : SegmentChain own exit childSummary a s [] s
  | cons (a len : Nat) (lens : List Nat) (s s1 s' : State)
      (link : ConfinedPrefix own exit childSummary a len s s1)
      (rest : SegmentChain own exit childSummary (a + len) s1 lens s') :
      SegmentChain own exit childSummary a s (len :: lens) s'

namespace SegmentChain

variable {own exit : BitVec 64 → Prop}
  {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}

/-- **A chain of segments is one confined prefix of the summed length.** -/
theorem toPrefix {a : Nat} {s s' : State} {lens : List Nat}
    (h : SegmentChain own exit childSummary a s lens s') :
    ConfinedPrefix own exit childSummary a lens.sum s s' := by
  induction h with
  | nil a s => simpa using ConfinedPrefix.nil
  | cons a len lens s s1 s' link _ ih =>
      have : ConfinedPrefix own exit childSummary a (len + lens.sum) s s' :=
        ConfinedPrefix.trans link ih
      simpa [List.sum_cons] using this

/--
**The sequential decomposition theorem.** A parent whose run is a chain of spliced segments and which
then sits on one of its own exits has a `ScopedTrace` of exactly the summed length.

Every step is accounted: each segment contributes its summary's `used` plus the one crossing edge the
parent retires, and the parent's own exit costs nothing because a trace halts *on* an exit.
-/
theorem toScopedTrace {a : Nat} {s s' : State} {lens : List Nat} {pc : BitVec 64}
    (h : SegmentChain own exit childSummary a s lens s')
    (hAt : s'.regs.get? PC = some pc) (hExit : exit pc) :
    ScopedTrace own exit childSummary a lens.sum s s' := by
  have := h.toPrefix 0 s' (ScopedTrace.exitAt (a + lens.sum) s' pc hAt hExit)
  simpa using this

end SegmentChain

/-! ## 4. A final child body may stop on the parent's selected exit -/

/-- Consume a selected child body and stop at the parent's exit without retiring an additional
instruction. This is deliberately distinct from `InlineTransfer`: the child summary already ends at
the instruction the parent may either execute or recognize as its outcome-selected exit. -/
theorem ScopedTrace.spliceChildTail {own exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {child : FunctionInstanceId} {a used : Nat} {s s' : State} {pc : BitVec 64}
    (body : childSummary child a used s s')
    (atExit : s'.regs.get? PC = some pc) (isExit : exit pc) :
    ScopedTrace own exit childSummary a used s s' := by
  simpa using ScopedTrace.childBody a used 0 child s s' s' body
    (ScopedTrace.exitAt (a + used) s' pc atExit isExit)

/--
**The structural reason, in the boundary data.** `InlineTransfer` pins its stopping pc to the source
of an edge *in* `ib.exits`, and `InlineBoundary.validFor` requires every such edge to land outside the
child and inside the parent. A last segment that owns the parent's exit pc has no real edge leaving it
back into the parent, so `ib.exits` is empty and no `InlineTransfer` for it exists at all.

This is the check to run against generated data: it fails by *emptiness*, which is exactly the failure
mode a "the shape looks right" argument misses.
-/
theorem inlineTransfer_needs_outgoing_edge {own exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {ib : InlineBoundary} {program : Program} {parent child : FunctionInstance}
    {a used : Nat} {s s' : State}
    (hEmpty : ib.exits = #[])
    (h : InlineTransfer own exit childSummary ib program parent child a used s s') : False := by
  have hmem := h.exitEdgeMem
  rw [hEmpty] at hmem
  simp at hmem

/-! ## 5. Flat adjacent-region composition

`FunctionTrace` composes adjacent regions even when the second owns the exit, using only
`append_within`, `step` and `mono_region`. -/

/--
**Adjacent regions compose at the flat level.** `first` runs confined to its own addresses and stops
on the crossing pc; the parent retires the crossing instruction; `second` runs confined to its
addresses and stops on a real exit. The result is one confined run of the enclosing extent.

`outerExitsStopFirst` is `append_within`'s side condition specialized to the cut: an enclosing exit
lying inside the first segment must already stop it. Where the parent's exits lie outside the first
segment — the case a sequential cut arranges — it is vacuous.
-/
theorem FunctionTrace.spliceAdjacent {firstPcs secondPcs outer firstExit exit : BitVec 64 → Prop}
    {a n m : Nat} {s sCross sResume s' : State} {crossPc : BitVec 64}
    (hFirstSub : ∀ pc, firstPcs pc → outer pc)
    (hSecondSub : ∀ pc, secondPcs pc → outer pc)
    (hOuterExitsStopFirst : ∀ pc, firstPcs pc → exit pc → firstExit pc)
    (hFirst : FunctionTrace firstPcs firstExit a n s sCross)
    (hAtCross : sCross.regs.get? PC = some crossPc)
    (hCrossInFirst : firstPcs crossPc)
    (hCrossNotExit : ¬ exit crossPc)
    (hRetireCross : Runs (try_step (a + n) false) sCross sResume false)
    (hSecond : FunctionTrace secondPcs exit (a + n + 1) m sResume s') :
    FunctionTrace outer exit a (n + (m + 1)) s s' :=
  FunctionTrace.append_within hFirstSub hOuterExitsStopFirst hFirst
    (FunctionTrace.step (a + n) m crossPc sCross sResume s' hAtCross (hFirstSub _ hCrossInFirst)
      hCrossNotExit hRetireCross (hSecond.mono_region hSecondSub))

end BinaryFv.RiscV.Elfling

/-! ## 6. Composition combinators for `ConfinedPrefix`

`Trace` and `ConfinedPrefix` are proved side by side from the same `Runs` facts, but `Trace` has
`trace_step`/`trace_steps` (`BinaryFv.RiscV.Logic.BlockStep`) and `ConfinedPrefix` had nothing, so
every confined site paid by hand for the same three things:

* the two pc-literal side conditions of `ownStep` — "this address is owned" and "this address is not
  a generated exit" — each spelled out as a four-line `apply … native_decide` / `simp […]` block;
* a re-association of the step index and the step count, because `trans` demands the second prefix
  start at the *syntactic* index `a + n` and produces the *syntactic* count `n + m`;
* nothing at all for chaining: a `k`-link chain was `k - 1` nested `trans`es, each with its own
  `simpa [Nat.add_assoc]`.

This section supplies the three missing pieces: `owned_pc` decides the side conditions, `reindex`
and `trans'` state the index and the count instead of computing them, and `confined_steps` folds a
list of links. None of them touches the step *counts* the child-summary interface consumes: a link
still carries the literal number of machine steps it retires, and `trans'`/`confined_steps` only
choose how that number is spelled.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV

/--
Discharge one pc-literal side condition of a confined step against the generated program data.

Two goal shapes are handled, both decidable checks on the generated tables:

* `functionInstanceExecutionPcs program functionInstance pc` — the address is inside the function
  instance's execution ranges, decided through `functionInstanceExecutionPcs_iff_ranges` and
  `RegionPcs.iff_inRanges`;
* `¬ functionInstanceExitPred functionInstance pc` — the address is not one of the generated exit
  pcs, decided by unfolding `FunctionInstance.isExit` to array membership.

This is a decision procedure over the generated image, not a search: on an address outside the
region the `native_decide` evaluates to `false` and the tactic *fails*. It therefore cannot be used
to claim ownership of an address the generator did not attribute to the function instance.
-/
macro "owned_pc" : tactic =>
  `(tactic|
    first
    | (apply functionInstanceExecutionPcs_iff_ranges.mpr
       apply RegionPcs.iff_inRanges.mpr
       native_decide)
    | (simp only [functionInstanceExitPred, FunctionInstance.isExit] <;> native_decide)
    | fail "owned_pc: the goal is neither a provable `functionInstanceExecutionPcs …` membership \
            nor a provable `¬ functionInstanceExitPred …`; check the address against the \
            generated ranges and exit pcs")

namespace ConfinedPrefix

variable {own exit : BitVec 64 → Prop}
  {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}

/-- Restate a confined prefix at an equal start index and length, proved by `omega` rather than by
`simpa [Nat.add_assoc]` at the use site. The prefix itself is unchanged: only the spelling of two
`Nat`s is. -/
theorem reindex {a n : Nat} (a' n' : Nat) {s s' : State}
    (h : ConfinedPrefix own exit childSummary a n s s')
    (ha : a' = a := by omega) (hn : n' = n := by omega) :
    ConfinedPrefix own exit childSummary a' n' s s' := by
  subst ha; subst hn; exact h

/-- `trans` at a *stated* total length `k`, with both index obligations discharged by `omega`.

`trans` forces the second prefix to be written at the syntactic index `a + n` and yields the
syntactic count `n + m`; every real site then had to re-associate. Here the caller writes the total
it wants and the arithmetic is checked, not reshaped. -/
theorem trans' {a n m b : Nat} (k : Nat) {s s1 s2 : State}
    (h1 : ConfinedPrefix own exit childSummary a n s s1)
    (h2 : ConfinedPrefix own exit childSummary b m s1 s2)
    (hb : b = a + n := by omega) (hk : k = n + m := by omega) :
    ConfinedPrefix own exit childSummary a k s s2 := by
  subst hb; subst hk; exact h1.trans h2

/-- Peel the first `n` steps off a goal of length `k`, leaving the remaining `k - n`. This is the
link `confined_steps` folds with: `h1` fixes `n` and the intermediate state, so the residual goal is
fully determined and the fold needs no annotation. -/
theorem consume {a n k : Nat} {s s1 s2 : State}
    (h1 : ConfinedPrefix own exit childSummary a n s s1)
    (h2 : ConfinedPrefix own exit childSummary (a + n) (k - n) s1 s2)
    (hn : n ≤ k := by omega) :
    ConfinedPrefix own exit childSummary a k s s2 := by
  have joined := h1.trans h2
  have hk : n + (k - n) = k := by omega
  rwa [hk] at joined

/-- One retired owned instruction as a confined prefix, with the two pc-literal side conditions
discharged by `owned_pc` unless the caller supplies them. Same statement as `ownStep`, same
premises; only the two decidable checks move from the call site into the default. -/
theorem ownStep' {a : Nat} {s s' : State} {pc : BitVec 64}
    (atPc : s.regs.get? PC = some pc)
    (step : Runs (try_step a false) s s' false)
    (inRegion : own pc := by owned_pc)
    (notExit : ¬ exit pc := by owned_pc) :
    ConfinedPrefix own exit childSummary a 1 s s' :=
  ConfinedPrefix.ownStep atPc inRegion notExit step

end ConfinedPrefix

/--
Fold a list of confined prefixes into one, mirroring `trace_steps` for `Trace`.

Each `hᵢ` supplies its own retired length and intermediate state; the goal supplies the total. The
lengths must add up — `consume`'s `n ≤ k` and the final `reindex`'s `n' = n` are checked by `omega`,
so a chain that does not account for exactly the goal's steps fails rather than being absorbed.

`SegmentChain` (§3) is the same fold as an inductive family, and `SegmentChain.toPrefix` is this
tactic's term-level counterpart. The difference is only where the total lives: the chain carries the
list of lengths and yields `lens.sum`, which a use site must then normalize, whereas here the goal
states the total and the tactic checks it.
-/
syntax "confined_steps " "[" term,* "]" : tactic
macro_rules
  | `(tactic| confined_steps []) => `(tactic| exact ConfinedPrefix.nil)
  | `(tactic| confined_steps [$h:term]) => `(tactic| exact ConfinedPrefix.reindex _ _ $h)
  | `(tactic| confined_steps [$h:term, $hs:term,*]) =>
      `(tactic| refine ConfinedPrefix.consume $h ?_; confined_steps [$hs,*])

end BinaryFv.RiscV.Elfling
