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

/-- Public lossless frame of the three-instruction tag-one rejection tail. -/
theorem wrapper_dispatch_tag1_suffix_frame {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base) (agree : Agree platformPreserved base state)
    (retired : RetiredCounterPresent state) (code : canonicalContractParams.env.CodeIntact state)
    (stepNo : Nat) (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10428)) :
    ∃ after, Trace stepNo 3 state after ∧ ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 3 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x1035c) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 0) ∧ after.regs.get? x11 = some (BitVec.ofNat 64 4) ∧
      RetiredCounterPresent after ∧ after.mem = state.mem ∧ Agree platformPreserved base after ∧
      canonicalContractParams.env.CodeIntact after ∧ after.regs.get? x18 = state.regs.get? x18 ∧
      after.regs.get? x2 = state.regs.get? x2 := by
  obtain ⟨⟨after, trace, tailPrefix, pc, result, status, retired, memory, platform, code, x18,
    x2⟩⟩ :=
    wrapper_dispatch_tag1_suffix machine agree retired code stepNo atPc
  exact ⟨after, trace, tailPrefix, pc, result, status, retired, memory, platform, code, x18, x2⟩

/-- The tag-one route reaches the shared rejection continuation with `(a0, a1) = (0, 4)`. -/
theorem wrapper_dispatch_tag1_path {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1)) :
    DispatchPath base stepNo 7 state (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 4) := by
  obtain ⟨⟨s4, prefixTrace, _prefixConfined, pc4, tag4, status4, retired4, memory4, agree4, code4, x18_4,
    x2_4⟩⟩ :=
    wrapper_dispatch_tag1_prefix machine agree retiredPresent code stepNo atPc tag
  obtain ⟨⟨s7, suffixTrace, _suffixPrefix, pc7, result7, status7, retired7, memory7, agree7,
    code7, x18_7, x2_7⟩⟩ :=
    wrapper_dispatch_tag1_suffix machine agree4 retired4 code4 (stepNo + 4) pc4
  refine ⟨⟨s7, Trace.append prefixTrace suffixTrace, pc7, result7, status7, retired7, ?_, agree7,
    code7, ?_, ?_⟩⟩
  · exact memory7.trans memory4
  · exact x18_7.trans x18_4
  · exact x2_7.trans x2_4

end BinaryFv.Zesu.MachineExecution
