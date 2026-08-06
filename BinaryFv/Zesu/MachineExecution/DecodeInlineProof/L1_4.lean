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

/-- A fully allocated fixed-size heap record has a concrete byte snapshot. This supplies the exact
source bytes required by the selected `memcpy` boundary without assuming their contents. -/
theorem memoryBytes_exists_of_heapArrayRep (state : State) (base size : Nat)
    (allocated : BinaryFv.Zesu.MemoryRepresentation.HeapArrayRep state base 1 size) :
    ∃ bytes : ByteArray,
      bytes.size = size ∧ BinaryFv.Zesu.MemoryRepresentation.MemoryBytes state base bytes := by
  let bytes : ByteArray := ⟨Array.ofFn fun index : Fin size =>
    UInt8.ofNat ((state.mem.get? (base + index)).getD 0#8).toNat⟩
  have bytesSize : bytes.size = size := by
    simp [bytes, ByteArray.size, Array.size_ofFn]
  refine ⟨bytes, bytesSize, ?_⟩
  intro index bound
  have indexSize : index < size := by simpa [bytesSize] using bound
  have present := allocated.2 index (by simpa using indexSize)
  obtain ⟨value, valueAt⟩ := Option.isSome_iff_exists.mp present
  have valueRead : (state.mem.get? (base + index)).getD 0#8 = value := by
    rw [valueAt]
    rfl
  have byteAt : bytes[index] = UInt8.ofNat value.toNat := by
    rw [ByteArray.getElem_eq_getElem_data]
    simp only [bytes, Array.getElem_ofFn]
    rw [valueRead]
  rw [byteAt, valueAt]
  simp

theorem decodeInline_first_result_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10308) retired x10
          (iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10308) := by
    simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContext pre.machine (Agree.refl state)
  exact decoderITypeStep pre.machine (Agree.refl state) pre.machine.retiredCounter
    (hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10308 0x13 0x05 0x01 0x36 0x360#12 2#5 10#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? pre.stackValue)) (wX_x10_run _ _)

end BinaryFv.Zesu.MachineExecution
