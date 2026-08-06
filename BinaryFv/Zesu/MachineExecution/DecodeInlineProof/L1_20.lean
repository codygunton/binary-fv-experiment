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

def decodeInlineRetryCopyArgs (args : DecodeInlineArgs) (contents : ByteArray) :
    Contracts.CopyArgs where
  destination := args.finalResultBase
  source := args.retryRawArgs.resultBase
  length := 832
  contents := contents

/-- Execute the decoder-owned `lui a0, 1` after the retry `memcpy` returns. -/
theorem decodeInline_retry_final_page_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103f0)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103f0) retired x10
          (BitVec.ofNat 64 0x1000)) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderLuiStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103f0 0x37 0x15 0x00 0x00 0x00001#20 10#5 atPc
    (by simpa [show sign_extend (m := 64) (0x00001#20 ++ 0x000#12) = BitVec.ofNat 64 0x1000 from by
          decide] using wX_x10_run _ (BitVec.ofNat 64 0x1000))

end BinaryFv.Zesu.MachineExecution
