import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryPrefix
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.Zesu.MachineExecution.OwnedPc

/-!
# Sail proof for the inlined `decode` scope

This file executes the 31 instructions owned directly by the compiler's inlined `decode` instance
and composes them with the three Level 3 child summaries. The inventory below is the reviewable
starting point: every owned word is checked against the pinned program image before any path proof
uses it.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep
open BinaryFv.RiscV.Sep

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def decodeInlineRetryLengthBranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10394))
    (BitVec.ofNat 64 0x10398) retired

/-- Execute the parent-owned `or a0, a4, a0` at `0x103c0`, assembling the complete little-endian
prefix value and reaching the result branch at `0x103c4`. -/
theorem decodeInline_retry_prefix_or_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103c0))
    (low high : BitVec 64) (lowRead : state.regs.get? x10 = some low)
    (highRead : state.regs.get? x14 = some high) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) false ∧
      (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10
        (high ||| low)).regs.get? PC = some (BitVec.ofNat 64 0x103c4) ∧
      Agree decoderPreserved state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) ∧
      RetiredCounterPresent
        (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) ∧
      (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10
        (high ||| low)).mem = state.mem := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) false :=
    decoderRTypeStep machine (Agree.refl state) retiredPresent
      (hasExactErePrefix_programImage_of_codeIntact code)
      stepNo 0x103c0 0x33 0x65 0xa7 0x00 10#5 14#5 10#5 .OR atPc
      (rX_x14_run _ _ (decoderExecuteState_get? highRead))
      (rX_x10_run _ _ (decoderExecuteState_get? lowRead)) (wX_x10_run _ _)
  refine ⟨retired, run, ?_, ?_, ?_, rfl⟩
  · simpa using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103c0) retired x10
      (high ||| low)
  · exact afterRegisterWrite_agree_of
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
  · exact afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103c0) retired x10
      (high ||| low)

end BinaryFv.Zesu.MachineExecution
