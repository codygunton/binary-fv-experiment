import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.Level2TerminalRouteFrame
import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_2
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_3
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_4
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_5
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_6
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_7
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_8
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_9

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

def WrapperDispatchRouteFrame.terminal
    (route : WrapperDispatchRouteFrame base before after fromStep steps terminalPc result status) :
    WrapperTerminalRouteFrame base before after fromStep steps terminalPc result status :=
  { trace := route.trace
    atTerminal := route.atTerminal
    resultValue := route.resultValue
    statusValue := route.statusValue
    platform := route.platform
    code := route.code
    retired := route.retired }

theorem wrapperDispatchTag3BranchAfter_agree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (wrapperDispatchTag3BranchAfter state retired) := by
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
  simp [wrapperDispatchTag3BranchAfter, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, notRetired, notPc,
    notNextPc, notIncrement]

end BinaryFv.Zesu.MachineExecution
