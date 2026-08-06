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

/-- A result-tag route whose flat Sail trace and Level 2 ownership have the same endpoint. -/
structure WrapperOwnedTerminalRouteFrame (base before after : State) (fromStep steps : Nat)
    (terminalPc result status : BitVec 64) : Prop where
  route : WrapperDispatchRouteFrame base before after fromStep steps terminalPc result status
  confined : ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep steps before after

structure Tag3OwnedPath (base : State) (fromStep : Nat) (entry : State) : Prop where
  evidence : ∃ after, WrapperDispatchRouteFrame base entry after fromStep 5
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 3) ∧
    ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 5 entry after

end BinaryFv.Zesu.MachineExecution
