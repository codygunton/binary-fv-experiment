import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.Level2TerminalRouteFrame
import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps

/-!
# Level 2 result-tag dispatch

The wrapper owns the instructions after either inlined `decode` segment reaches `0x103fc`.
These Sail proofs distinguish the internal result tags before entering the shared wrapper tail.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem wrapperDispatchBranchNotTakenAfter_agree (state : State) (pc retired : BitVec 64) :
    Agree platformPreserved state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
        (Sail.BitVec.addInt pc 4) retired) := by
  intro register preserved
  have notRetired : minstret ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notPc : PC ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notNextPc : nextPC ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notIncrement : minstret_increment ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, notRetired, notPc,
    notNextPc, notIncrement]

theorem wrapperDispatchJumpAfter_agree (state : State) (pc target retired : BitVec 64) :
    Agree platformPreserved state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) := by
  intro register preserved
  have notRetired : minstret ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notPc : PC ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notNextPc : nextPC ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notIncrement : minstret_increment ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    notRetired, notPc, notNextPc, notIncrement]

end BinaryFv.Zesu.MachineExecution
