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
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_2
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_3
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_4
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_5
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_6
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_7
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_8
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_9
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_10
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_11
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_12
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L3_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L3_2

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

/-- Tag three supplies one terminal state carrying both its five-step Sail trace and wrapper ownership. -/
theorem wrapper_dispatch_tag3_owned_terminal_route {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 3)) :
    ∃ after, WrapperOwnedTerminalRouteFrame base state after stepNo 5
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 3) := by
  obtain ⟨⟨after, terminal, confined⟩⟩ := wrapper_dispatch_tag3_owned_path machine agree retiredPresent
    code stepNo atPc tag
  exact ⟨after, ⟨terminal, confined⟩⟩

end BinaryFv.Zesu.MachineExecution
