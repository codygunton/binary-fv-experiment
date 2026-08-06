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

/-- Execute the decoder-owned `add a0, sp, a0`, reaching the outgoing result-tag load. -/
theorem decodeInline_retry_final_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103f4))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (pageRead : state.regs.get? x10 = some (BitVec.ofNat 64 0x1000)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103f4) retired x10
          (BitVec.ofNat 64 (args.stackBase + 0x1000))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderRTypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103f4 0x33 0x05 0xa1 0x00 10#5 2#5 10#5 .ADD atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead))
    (rX_bits_run_x10 _ _ (decoderExecuteState_get? pageRead))
    (by rw [show rTypeResult .ADD (BitVec.ofNat 64 args.stackBase) (BitVec.ofNat 64 0x1000) =
              BitVec.ofNat 64 (args.stackBase + 0x1000) from by
            show BitVec.ofNat 64 args.stackBase + BitVec.ofNat 64 0x1000 = _
            rw [← BitVec.ofNat_add]]
        exact wX_x10_run _ _)

end BinaryFv.Zesu.MachineExecution
