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

theorem decodeInline_first_input_length_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree platformPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10314))
    (lengthRead : state.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10314) retired x13
          (iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.bytes.size))) false := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderITypeStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10314 0x93 0x86 0x04 0x00 0x000#12 9#5 13#5 .ADDI atPc
    (rX_x9_run _ _ (decoderExecuteState_get? lengthRead)) (wX_x13_run _ _)

theorem decodeInline_first_call_page_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree platformPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10318)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10318) retired x1
          (BitVec.ofNat 64 0x10318)) false := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderAuipcStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10318 0x97 0x00 0x00 0x00 0x00000#20 1#5 atPc
    (by simpa using wX_bits_run_x1 _ (BitVec.ofNat 64 0x10318))

end BinaryFv.Zesu.MachineExecution
