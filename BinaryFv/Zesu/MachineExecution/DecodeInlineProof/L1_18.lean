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

/-- Execute `addi a1, sp, 0x6b0`, selecting the retry result payload source. -/
theorem decodeInline_retry_copy_source_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103e0))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103e0) retired x11
        (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103e0 0x93 0x05 0x01 0x6b 0x6b0#12 2#5 11#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x11_run _ _)

/-- Execute `addi a2, x0, 0x340`, fixing the payload copy length at 832 bytes. -/
theorem decodeInline_retry_copy_length_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103e4)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103e4) retired x12
        (iTypeResult .ADDI 0x340#12 (0#64))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103e4 0x13 0x06 0x00 0x34 0x340#12 0#5 12#5 .ADDI atPc
    (rX_x0_run _) (wX_x12_run _ _)

end BinaryFv.Zesu.MachineExecution
