import BinaryFv.RiscV.Elfling.SuccessorTrace
import BinaryFv.RiscV.Step.AbstractPremise

/-!
# Closed regressions for successor-classified traces

These tests execute the generated `try_step` on a tiny RISC-V image. They do not assume a machine
transition. The image has a conditional branch at `0x1000` and ordinary `nop` instructions at
`0x1000`/`0x1004`, all inside the concrete platform supplied by `Step.AbstractPremise`.

The module lives under target validation because the closed `try_step` computations need
`native_decide`; the generic layer's hermetic audit forbids that tactic outside `BinaryFv/SSZ`.
Nothing here imports target contracts or enters the production theorem graph.

The four regression groups pin the semantic decisions the successor layer exists to express:

* an entered occurrence can have a zero-step body when its entry is a completing exit;
* the same conditional source continues on its internal arm and completes on its leaving arm;
* nested resumption consumes the pending transfer exactly once;
* nested propagation retains the identical pending transfer.
-/

namespace BinaryFv.SSZ.Zesu.Validation.SuccessorTraceTests

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling

def testEntry : BitVec 64 := 0x1000#64
def testResume : BitVec 64 := 0x1004#64
def testOutside : BitVec 64 := 0x1008#64

abbrev pairRegion (pc : BitVec 64) : Prop := pc = testEntry ∨ pc = testResume
abbrev entryRegion (pc : BitVec 64) : Prop := pc = testEntry
abbrev resumeRegion (pc : BitVec 64) : Prop := pc = testResume
abbrev pairExits (pc : BitVec 64) : Prop := pc = testEntry ∨ pc = testResume
abbrev entryExit (pc : BitVec 64) : Prop := pc = testEntry
abbrev resumeExit (pc : BitVec 64) : Prop := pc = testResume

private def insertWord (state : State) (pc : Nat)
    (b0 b1 b2 b3 : BitVec 8) : State :=
  let mem0 := state.mem.insert pc b0
  let mem1 := mem0.insert (pc + 1) b1
  let mem2 := mem1.insert (pc + 2) b2
  let mem3 := mem2.insert (pc + 3) b3
  { state with mem := mem3 }

private def insertNop (state : State) (pc : Nat) : State :=
  insertWord state pc 0x13#8 0x00#8 0x00#8 0x00#8

private def stepResult? (stepNo : Nat) (state : State) : Option State :=
  match (try_step stepNo false).run state with
  | .ok false after => some after
  | _ => none

private theorem runs_getD_of_isSome (stepNo : Nat) (state : State)
    (h : (stepResult? stepNo state).isSome = true) :
    Runs (try_step stepNo false) state
      ((stepResult? stepNo state).getD initialState) false := by
  unfold stepResult? at h
  split at h <;> simp_all [Runs, stepResult?]

/-! ## A real conditional has one staying arm and one leaving arm -/

/--
`beq x5, x0, +8` at `testEntry`, followed by a `nop` at the fall-through address.
`x5 = 0` takes the leaving arm to `testOutside`; `x5 = 1` stays at `testResume`.
-/
def branchStart (x5Value : BitVec 64) : State :=
  let withFallthrough := insertNop (witnessState testEntry) testResume.toNat
  let withBranch := insertWord withFallthrough testEntry.toNat
    0x63#8 0x84#8 0x02#8 0x00#8
  { withBranch with regs := withBranch.regs.insert x5 x5Value }

def branchLeaveStart : State := branchStart 0
def branchStayStart : State := branchStart 1
def branchLeaveAfter : State := (stepResult? 0 branchLeaveStart).getD initialState
def branchStayAfter : State := (stepResult? 0 branchStayStart).getD initialState
def branchStayFinal : State := (stepResult? 1 branchStayAfter).getD initialState

theorem branch_leave_runs :
    Runs (try_step 0 false) branchLeaveStart branchLeaveAfter false :=
  runs_getD_of_isSome 0 branchLeaveStart (by native_decide)

theorem branch_stay_runs :
    Runs (try_step 0 false) branchStayStart branchStayAfter false :=
  runs_getD_of_isSome 0 branchStayStart (by native_decide)

theorem branch_stay_final_runs :
    Runs (try_step 1 false) branchStayAfter branchStayFinal false :=
  runs_getD_of_isSome 1 branchStayAfter (by native_decide)

def branchLeaveStep : RetiringStep 0 branchLeaveStart branchLeaveAfter where
  sourcePc := testEntry
  successorPc := testOutside
  atSource := by native_decide
  retires := branch_leave_runs
  atSuccessor := by native_decide

def branchStayStep : RetiringStep 0 branchStayStart branchStayAfter where
  sourcePc := testEntry
  successorPc := testResume
  atSource := by native_decide
  retires := branch_stay_runs
  atSuccessor := by native_decide

def branchStayFinalTransfer : ExitTransfer pairExits 1 branchStayAfter branchStayFinal where
  sourcePc := testResume
  successorPc := testOutside
  atSource := by native_decide
  retires := branch_stay_final_runs
  atSuccessor := by native_decide
  sourceIsExit := Or.inr rfl

def branchLeaveTransfer : ExitTransfer pairExits 0 branchLeaveStart branchLeaveAfter where
  toRetiringStep := branchLeaveStep
  sourceIsExit := Or.inl rfl

def branchLeaveTrace :
    SuccessorTrace pairRegion pairExits 0 0
      branchLeaveStart branchLeaveStart branchLeaveAfter :=
  SuccessorTrace.exitAt 0 branchLeaveStart branchLeaveAfter branchLeaveTransfer
    (Or.inl rfl) (by decide)

def branchStayTrace :
    SuccessorTrace pairRegion pairExits 0 1
      branchStayStart branchStayAfter branchStayFinal :=
  SuccessorTrace.step 0 0 branchStayStart branchStayAfter branchStayAfter branchStayFinal
    branchStayStep (Or.inl rfl) (Or.inr rfl)
    (SuccessorTrace.exitAt 1 branchStayAfter branchStayFinal branchStayFinalTransfer
      (Or.inr rfl) (by decide))

/-- The same decoded branch source completes on one actual arm and continues on the other. -/
theorem conditional_successors_stay_and_leave :
    SuccessorTrace pairRegion pairExits 0 0
        branchLeaveStart branchLeaveStart branchLeaveAfter ∧
      SuccessorTrace pairRegion pairExits 0 1
        branchStayStart branchStayAfter branchStayFinal :=
  ⟨branchLeaveTrace, branchStayTrace⟩

/--
The entry is a generated exit, yet the entered trace is inhabited with a zero-step body and one
actual pending retirement.
-/
theorem entry_exit_zero_body :
    EnteredSuccessorTrace pairRegion pairExits testEntry 0 0
      branchLeaveStart branchLeaveStart branchLeaveAfter where
  startsAtEntry := by native_decide
  entryInRegion := Or.inl rfl
  trace := branchLeaveTrace

theorem entry_exit_zero_body_completes_one_step :
    Trace 0 1 branchLeaveStart branchLeaveAfter :=
  entry_exit_zero_body.toTrace

/-- Restoring the old `entryNotExit` premise would reject the closed zero-body witness. -/
theorem entry_not_exit_mutation_fails : ¬ (¬ pairExits testEntry) := by
  simp

/-- The leaving arm cannot be fed to the recursive constructor's internal-successor premise. -/
theorem leave_as_internal_mutation_fails : ¬ pairRegion branchLeaveStep.successorPc := by
  decide

/-- The staying arm cannot be misclassified as an immediate completion. -/
theorem stay_as_completion_mutation_fails :
    ¬ SuccessorTrace pairRegion pairExits 0 0
      branchStayStart branchStayStart branchStayAfter := by
  intro run
  obtain ⟨transfer, _, successorOutside⟩ := run.final_transfer
  exact successorOutside
    (transfer.toRetiringStep.successor_mem
      ⟨testResume, by native_decide, Or.inr rfl⟩)

/-! ## Nested resumption consumes the pending transfer exactly once -/

def nopStart : State :=
  insertNop (insertNop (witnessState testEntry) testEntry.toNat) testResume.toNat

def nopAfterFirst : State := (stepResult? 0 nopStart).getD initialState
def nopAfterSecond : State := (stepResult? 1 nopAfterFirst).getD initialState

theorem nop_first_runs :
    Runs (try_step 0 false) nopStart nopAfterFirst false :=
  runs_getD_of_isSome 0 nopStart (by native_decide)

theorem nop_second_runs :
    Runs (try_step 1 false) nopAfterFirst nopAfterSecond false :=
  runs_getD_of_isSome 1 nopAfterFirst (by native_decide)

def nestedResumeTransfer : ExitTransfer entryExit 0 nopStart nopAfterFirst where
  sourcePc := testEntry
  successorPc := testResume
  atSource := by native_decide
  retires := nop_first_runs
  atSuccessor := by native_decide
  sourceIsExit := rfl

def enclosingCompletionTransfer : ExitTransfer resumeExit 1 nopAfterFirst nopAfterSecond where
  sourcePc := testResume
  successorPc := testOutside
  atSource := by native_decide
  retires := nop_second_runs
  atSuccessor := by native_decide
  sourceIsExit := rfl

def nestedResumeTrace :
    SuccessorTrace entryRegion entryExit 0 0 nopStart nopStart nopAfterFirst :=
  SuccessorTrace.exitAt 0 nopStart nopAfterFirst nestedResumeTransfer rfl (by decide)

def enclosingContinuation :
    SuccessorTrace pairRegion resumeExit 1 0
      nopAfterFirst nopAfterFirst nopAfterSecond :=
  SuccessorTrace.exitAt 1 nopAfterFirst nopAfterSecond enclosingCompletionTransfer
    (Or.inr rfl) (by decide)

theorem resume_consumes_pending_once :
    SuccessorTrace pairRegion resumeExit 0 1
      nopStart nopAfterFirst nopAfterSecond :=
  SuccessorTrace.resume (inner := entryRegion) (outer := pairRegion)
    (innerExit := entryExit) (outerExit := resumeExit)
    (fun pc hpc => Or.inl hpc)
    ⟨testResume, by native_decide, Or.inr rfl⟩
    nestedResumeTrace enclosingContinuation

/-- One nested body step plus one pending completion becomes exactly two machine retirements. -/
theorem resume_completed_trace_has_two_steps :
    Trace 0 2 nopStart nopAfterSecond :=
  resume_consumes_pending_once.toTrace

theorem nop_start_ne_after_first : nopStart ≠ nopAfterFirst := by
  intro sameState
  have samePc := congrArg (fun state : State => state.regs.get? PC) sameState
  change nopStart.regs.get? PC = nopAfterFirst.regs.get? PC at samePc
  have startPc : nopStart.regs.get? PC = some testEntry := by native_decide
  have afterPc : nopAfterFirst.regs.get? PC = some testResume := by native_decide
  rw [startPc, afterPc] at samePc
  exact absurd (Option.some.inj samePc) (by decide)

/-- Dropping the nested completion transfer would falsely claim a zero-step enclosing body. -/
theorem resume_drop_transfer_mutation_fails :
    ¬ SuccessorTrace pairRegion resumeExit 0 0
      nopStart nopAfterFirst nopAfterSecond := by
  intro run
  exact nop_start_ne_after_first run.start_eq_exit_of_count_zero

/-! ## Nested propagation retains the identical pending transfer -/

def nestedPropagationTransfer : ExitTransfer resumeExit 1 nopAfterFirst nopAfterSecond :=
  enclosingCompletionTransfer

def nestedPropagationTrace :
    SuccessorTrace resumeRegion resumeExit 1 0
      nopAfterFirst nopAfterFirst nopAfterSecond :=
  SuccessorTrace.exitAt 1 nopAfterFirst nopAfterSecond nestedPropagationTransfer
    rfl (by decide)

theorem propagation_keeps_pending :
    SuccessorTrace pairRegion resumeExit 1 0
      nopAfterFirst nopAfterFirst nopAfterSecond :=
  SuccessorTrace.propagate
    (fun pc hpc => Or.inr hpc)
    ⟨testResume, by native_decide, rfl⟩
    (by
      rintro ⟨pc, atPc, inRegion⟩
      have outsidePc : nopAfterSecond.regs.get? PC = some testOutside := by native_decide
      rw [outsidePc] at atPc
      have : pc = testOutside := Option.some.inj atPc.symm
      subst pc
      exact (by decide : ¬ pairRegion testOutside) inRegion)
    nestedPropagationTrace

/-- Propagation changes only the outer-exit proof, not the pending machine step. -/
theorem propagation_preserves_identical_transfer :
    (nestedPropagationTransfer.reclassify (show resumeExit testResume from rfl)).toRetiringStep =
      nestedPropagationTransfer.toRetiringStep :=
  rfl

/-- Treating this propagation as a resume is impossible: its actual successor left the parent. -/
theorem propagation_as_resume_mutation_fails : ¬ StatePcIn pairRegion nopAfterSecond := by
  rintro ⟨pc, atPc, inRegion⟩
  have outsidePc : nopAfterSecond.regs.get? PC = some testOutside := by native_decide
  rw [outsidePc] at atPc
  have : pc = testOutside := Option.some.inj atPc.symm
  subst pc
  exact (by decide : ¬ pairRegion testOutside) inRegion

end BinaryFv.SSZ.Zesu.Validation.SuccessorTraceTests
