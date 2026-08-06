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

theorem decodeInline_first_allocator_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree platformPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1030c))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x1030c) retired x11
          (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))) false := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderITypeStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x1030c 0x93 0x05 0x01 0x01 0x010#12 2#5 11#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x11_run _ _)

theorem decodeInline_first_input_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree platformPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10310))
    (inputRead : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10310) retired x12
          (iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.inputBase))) false := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderITypeStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10310 0x13 0x06 0x04 0x00 0x000#12 8#5 12#5 .ADDI atPc
    (rX_x8_run _ _ (decoderExecuteState_get? inputRead)) (wX_x12_run _ _)

end BinaryFv.Zesu.MachineExecution
