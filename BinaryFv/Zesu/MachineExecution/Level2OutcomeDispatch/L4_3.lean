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

/-- Tag one supplies one terminal state carrying both its seven-step Sail trace and wrapper ownership. -/
theorem wrapper_dispatch_tag1_owned_terminal_route {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1)) :
    ∃ after, WrapperOwnedTerminalRouteFrame base state after stepNo 7
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 4) := by
  obtain ⟨⟨s4, prefixTrace, prefixConfined, pc4, _tag4, _status4, retired4, memory4, agree4,
    code4, x18_4, x2_4⟩⟩ := wrapper_dispatch_tag1_prefix machine agree retiredPresent code stepNo atPc tag
  obtain ⟨⟨after, suffixTrace, suffixConfined, pc, result, status, retired, memory, platform,
    finalCode, x18, x2⟩⟩ := wrapper_dispatch_tag1_suffix machine agree4 retired4 code4 (stepNo + 4) pc4
  let route : WrapperDispatchRouteFrame base state after stepNo 7
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 4) :=
    { trace := Trace.append prefixTrace suffixTrace
      atTerminal := pc
      resultValue := result
      statusValue := status
      platform := platform
      code := finalCode
      retired := retired
      memory := memory.trans memory4
      savedS2 := x18.trans x18_4
      savedStack := x2.trans x2_4 }
  refine ⟨after, ⟨route, ?_⟩⟩
  simpa [Nat.add_assoc] using ConfinedPrefix.trans prefixConfined suffixConfined

/-- The original tag-three route frame projected from its richer shared-state proof. -/
theorem wrapper_dispatch_tag3_path {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 3)) :
    DispatchPath base stepNo 5 state (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 3) := by
  obtain ⟨⟨after, route, -⟩⟩ := wrapper_dispatch_tag3_owned_path machine agree retiredPresent code
    stepNo atPc tag
  exact ⟨⟨after, route.trace, route.atTerminal, route.resultValue, route.statusValue, route.retired,
    route.memory, route.platform, route.code, route.savedS2, route.savedStack⟩⟩

end BinaryFv.Zesu.MachineExecution
