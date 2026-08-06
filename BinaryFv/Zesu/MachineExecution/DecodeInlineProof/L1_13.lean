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

/-- Execute `slli a0, a0, 32`, producing `2^64 - 2^32`. -/
theorem decodeInline_retry_shift_constant_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10388))
    (constant : state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 1))) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10388) retired x10
          (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderShiftIopStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10388 0x13 0x15 0x05 0x02 32#6 10#5 10#5 .SLLI atPc
    (rX_bits_run_x10 _ _ (decoderExecuteState_get? constant))
    (by rw [show shiftIopResult .SLLI 32#6 (BitVec.ofNat 64 (2 ^ 64 - 1)) =
              BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32) from by native_decide]
        exact wX_x10_run _ _)

/-- Execute `addi a2, a0, -4`, completing the constants consumed by the prefix length gate. -/
theorem decodeInline_retry_minus_four_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1038c))
    (constant : state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x1038c) retired x12
          (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x1038c 0x13 0x06 0xc5 0xff 0xffc#12 10#5 12#5 .ADDI atPc
    (rX_bits_run_x10 _ _ (decoderExecuteState_get? constant))
    (by rw [show iTypeResult .ADDI 0xffc#12 (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) =
              BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4) from by native_decide]
        exact wX_x12_run _ _)

end BinaryFv.Zesu.MachineExecution
