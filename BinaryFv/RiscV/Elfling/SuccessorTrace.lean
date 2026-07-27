import BinaryFv.RiscV.Elfling.FunctionTrace

/-!
# Successor-classified function traces

The legacy `FunctionTrace` stops before every address in a static exit set. That is too coarse for
optimized code: one successor of an instruction at an exit address can remain in the occurrence
while another leaves it.

`SuccessorTrace` instead stops with one actual retiring transfer pending. Its body count excludes
that final transfer, so an occurrence whose entry is itself a completing exit has a zero-step body.
The pending `ExitTransfer` still carries the real `Runs (try_step ...)`, both endpoint states, and
both endpoint PCs.

This module is deliberately generic. It supplies the execution vocabulary and the two nested
composition operations, but does not migrate any target contract or generated boundary inventory.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

/-- The current PC of `state` exists and belongs to `addresses`. -/
def StatePcIn (addresses : BitVec 64 → Prop) (state : State) : Prop :=
  ∃ pc, state.regs.get? PC = some pc ∧ addresses pc

/-- One actual retiring machine step with its source and successor PCs made explicit. -/
structure RetiringStep (fromStep : Nat) (before after : State) where
  sourcePc : BitVec 64
  successorPc : BitVec 64
  atSource : before.regs.get? PC = some sourcePc
  retires : Runs (try_step fromStep false) before after false
  atSuccessor : after.regs.get? PC = some successorPc

namespace RetiringStep

/-- A state-level source classification applies to the source carried by the actual step. -/
theorem source_mem {addresses : BitVec 64 → Prop} {fromStep : Nat} {before after : State}
    (step : RetiringStep fromStep before after) (h : StatePcIn addresses before) :
    addresses step.sourcePc := by
  obtain ⟨pc, atPc, inAddresses⟩ := h
  have samePc : pc = step.sourcePc := Option.some.inj (atPc.symm.trans step.atSource)
  simpa [samePc] using inAddresses

/-- A state-level successor classification applies to the successor carried by the actual step. -/
theorem successor_mem {addresses : BitVec 64 → Prop} {fromStep : Nat} {before after : State}
    (step : RetiringStep fromStep before after) (h : StatePcIn addresses after) :
    addresses step.successorPc := by
  obtain ⟨pc, atPc, inAddresses⟩ := h
  have samePc : pc = step.successorPc := Option.some.inj (atPc.symm.trans step.atSuccessor)
  simpa [samePc] using inAddresses

/-- If the post-state PC is not in a set, neither is the actual successor carried by the step. -/
theorem successor_not_mem {addresses : BitVec 64 → Prop} {fromStep : Nat}
    {before after : State} (step : RetiringStep fromStep before after)
    (h : ¬ StatePcIn addresses after) : ¬ addresses step.successorPc :=
  fun successorIn => h ⟨step.successorPc, step.atSuccessor, successorIn⟩

end RetiringStep

/-- An actual retiring step whose source is a generated exit of the current occurrence. -/
structure ExitTransfer (exit : BitVec 64 → Prop) (fromStep : Nat)
    (before after : State) extends RetiringStep fromStep before after where
  sourceIsExit : exit sourcePc

namespace ExitTransfer

/-- Reclassify the same pending step at an enclosing occurrence's exit predicate. -/
def reclassify {innerExit outerExit : BitVec 64 → Prop} {fromStep : Nat}
    {before after : State} (transfer : ExitTransfer innerExit fromStep before after)
    (sourceIsOuterExit : outerExit transfer.sourcePc) :
    ExitTransfer outerExit fromStep before after :=
  { transfer.toRetiringStep with sourceIsExit := sourceIsOuterExit }

/-- Reclassification changes only the proof attached to the source, never the pending step. -/
@[simp] theorem reclassify_toRetiringStep {innerExit outerExit : BitVec 64 → Prop}
    {fromStep : Nat} {before after : State}
    (transfer : ExitTransfer innerExit fromStep before after)
    (sourceIsOuterExit : outerExit transfer.sourcePc) :
    (transfer.reclassify sourceIsOuterExit).toRetiringStep = transfer.toRetiringStep :=
  rfl

end ExitTransfer

/--
An instruction-by-instruction run that stops with one completing transfer pending.

`count` counts only steps already retired in the occurrence body. The terminal constructor requires
the actual successor to leave `region`; the recursive constructor requires the actual successor to
remain in `region`. In particular, the recursive constructor deliberately does not require its
source to be absent from `exit`: an internal arm from a statically classified exit source continues.
-/
inductive SuccessorTrace (region exit : BitVec 64 → Prop) :
    Nat → Nat → State → State → State → Prop where
  /-- Stop before a real exit transfer whose actual successor leaves this occurrence. -/
  | exitAt (fromStep : Nat) (atExit afterExit : State)
      (transfer : ExitTransfer exit fromStep atExit afterExit)
      (sourceInRegion : region transfer.sourcePc)
      (successorOutside : ¬ region transfer.successorPc) :
      SuccessorTrace region exit fromStep 0 atExit atExit afterExit
  /-- Retire one step whose actual successor remains inside this occurrence, then continue. -/
  | step (fromStep count : Nat) (before after atExit afterExit : State)
      (transfer : RetiringStep fromStep before after)
      (sourceInRegion : region transfer.sourcePc)
      (successorInRegion : region transfer.successorPc)
      (rest : SuccessorTrace region exit (fromStep + 1) count after atExit afterExit) :
      SuccessorTrace region exit fromStep (count + 1) before atExit afterExit

namespace SuccessorTrace

/-- A zero-step body starts at the pending transfer's pre-state. -/
theorem start_eq_exit_of_count_zero {region exit : BitVec 64 → Prop} {fromStep : Nat}
    {start atExit afterExit : State}
    (run : SuccessorTrace region exit fromStep 0 start atExit afterExit) :
    start = atExit := by
  cases run
  rfl

/-- Every run exposes one actual pending transfer at body offset `count`. -/
theorem final_transfer {region exit : BitVec 64 → Prop} {fromStep count : Nat}
    {start atExit afterExit : State}
    (run : SuccessorTrace region exit fromStep count start atExit afterExit) :
    ∃ transfer : ExitTransfer exit (fromStep + count) atExit afterExit,
      region transfer.sourcePc ∧ ¬ region transfer.successorPc := by
  induction run with
  | exitAt fromStep atExit afterExit transfer sourceInRegion successorOutside =>
      simpa using ⟨transfer, sourceInRegion, successorOutside⟩
  | step fromStep count before after atExit afterExit transfer sourceInRegion
      successorInRegion rest ih =>
      have arithmetic : fromStep + (count + 1) = fromStep + 1 + count := by omega
      rw [arithmetic]
      exact ih

/-- Consuming the pending transfer yields an ordinary trace of `count + 1` retired steps. -/
theorem toTrace {region exit : BitVec 64 → Prop} {fromStep count : Nat}
    {start atExit afterExit : State}
    (run : SuccessorTrace region exit fromStep count start atExit afterExit) :
    Trace fromStep (count + 1) start afterExit := by
  induction run with
  | exitAt fromStep atExit afterExit transfer _ _ =>
      simpa using Trace.one fromStep atExit afterExit transfer.retires
  | step fromStep count before after atExit afterExit transfer _ _ rest ih =>
      exact Trace.step fromStep (count + 1) before after afterExit transfer.retires ih

/--
Lift a completed nested run when its actual pending successor resumes in the enclosing occurrence.

The pending transfer is consumed exactly once: it contributes the single `+ 1` between the nested
body and `continuation`. The continuation starts at the transfer's indexed post-state.
-/
theorem resume {inner outer innerExit outerExit : BitVec 64 → Prop}
    {fromStep used count : Nat} {start atExit afterExit finalExit finalAfter : State}
    (innerSubset : ∀ pc, inner pc → outer pc)
    (successorInOuter : StatePcIn outer afterExit)
    (innerRun : SuccessorTrace inner innerExit fromStep used start atExit afterExit)
    (continuation :
      SuccessorTrace outer outerExit (fromStep + used + 1) count
        afterExit finalExit finalAfter) :
    SuccessorTrace outer outerExit fromStep (used + 1 + count)
      start finalExit finalAfter := by
  induction innerRun generalizing count finalExit finalAfter with
  | exitAt fromStep atExit afterExit transfer sourceInInner successorOutsideInner =>
      have sourceInOuter : outer transfer.sourcePc :=
        innerSubset transfer.sourcePc sourceInInner
      have actualSuccessorInOuter : outer transfer.successorPc :=
        transfer.toRetiringStep.successor_mem successorInOuter
      simpa [Nat.add_comm] using
        SuccessorTrace.step fromStep count atExit afterExit finalExit finalAfter
          transfer.toRetiringStep sourceInOuter actualSuccessorInOuter continuation
  | step fromStep used before after atExit afterExit transfer sourceInInner
      successorInInner rest ih =>
      have continuation' :
          SuccessorTrace outer outerExit (fromStep + 1 + used + 1) count
            afterExit finalExit finalAfter := by
        have arithmetic :
            fromStep + (used + 1) + 1 = fromStep + 1 + used + 1 := by omega
        rw [← arithmetic]
        exact continuation
      have tail := ih successorInOuter continuation'
      have sourceInOuter : outer transfer.sourcePc :=
        innerSubset transfer.sourcePc sourceInInner
      have actualSuccessorInOuter : outer transfer.successorPc :=
        innerSubset transfer.successorPc successorInInner
      have arithmetic : used + 1 + count + 1 = used + 1 + 1 + count := by omega
      rw [← arithmetic]
      exact SuccessorTrace.step fromStep (used + 1 + count) before after
        finalExit finalAfter transfer sourceInOuter actualSuccessorInOuter tail

/--
Lift a nested run whose pending transfer also completes the enclosing occurrence.

The body count is unchanged. The identical pending `RetiringStep` is reclassified at the enclosing
exit and propagated; it is not retired by this operation.
-/
theorem propagate {inner outer innerExit outerExit : BitVec 64 → Prop}
    {fromStep used : Nat} {start atExit afterExit : State}
    (innerSubset : ∀ pc, inner pc → outer pc)
    (sourceIsOuterExit : StatePcIn outerExit atExit)
    (successorOutsideOuter : ¬ StatePcIn outer afterExit)
    (innerRun : SuccessorTrace inner innerExit fromStep used start atExit afterExit) :
    SuccessorTrace outer outerExit fromStep used start atExit afterExit := by
  induction innerRun with
  | exitAt fromStep atExit afterExit transfer sourceInInner successorOutsideInner =>
      have sourceInOuter : outer transfer.sourcePc :=
        innerSubset transfer.sourcePc sourceInInner
      have actualSourceIsOuterExit : outerExit transfer.sourcePc :=
        transfer.toRetiringStep.source_mem sourceIsOuterExit
      have actualSuccessorOutside : ¬ outer transfer.successorPc :=
        transfer.toRetiringStep.successor_not_mem successorOutsideOuter
      exact SuccessorTrace.exitAt fromStep atExit afterExit
        (transfer.reclassify actualSourceIsOuterExit) sourceInOuter actualSuccessorOutside
  | step fromStep used before after atExit afterExit transfer sourceInInner
      successorInInner rest ih =>
      exact SuccessorTrace.step fromStep used before after atExit afterExit transfer
        (innerSubset transfer.sourcePc sourceInInner)
        (innerSubset transfer.successorPc successorInInner)
        (ih sourceIsOuterExit successorOutsideOuter)

end SuccessorTrace

/--
A successor-classified trace that begins at the generated entry.

There is deliberately no `entryNotExit`: an entry can be the source of a completing transfer. Such
a trace has a zero-step body but still carries one real pending retirement.
-/
structure EnteredSuccessorTrace (region exit : BitVec 64 → Prop) (entry : BitVec 64)
    (fromStep count : Nat) (start atExit afterExit : State) : Prop where
  startsAtEntry : start.regs.get? PC = some entry
  entryInRegion : region entry
  trace : SuccessorTrace region exit fromStep count start atExit afterExit

namespace EnteredSuccessorTrace

/-- Forget entry metadata and consume the pending transfer into a nonempty ordinary trace. -/
theorem toTrace {region exit : BitVec 64 → Prop} {entry : BitVec 64}
    {fromStep count : Nat} {start atExit afterExit : State}
    (run : EnteredSuccessorTrace region exit entry fromStep count start atExit afterExit) :
    Trace fromStep (count + 1) start afterExit :=
  run.trace.toTrace

end EnteredSuccessorTrace

end BinaryFv.RiscV.Elfling
