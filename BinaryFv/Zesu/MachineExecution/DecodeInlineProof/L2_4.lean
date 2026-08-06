import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryPrefix
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_5
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_6
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_7
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_8
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_9
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_10
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_11
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_12
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_13
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_14
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_15
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_16
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_17
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_18
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_19
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_20
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_21

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

/-- The selected emitted `decodeRaw` region is contained in its enclosing inlined `decode` region.
This is checked from the generated call relation, not handwritten address bounds. -/
theorem decodeRaw_executionPcs_subset_decodeInline (pc : BitVec 64)
    (pcIn : functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw pc) :
    decodeInlineOwnPcs pc := by
  have parentMember :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨3, by native_decide, rfl⟩
  have childMember : functionInstance_ssz_raw_decodeRaw ∈
      generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨6, by native_decide, rfl⟩
  have childIsCallee : functionInstance_ssz_raw_decodeRaw ∈
      BinaryFv.RiscV.Elfling.calleeFunctionInstances generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 := by
    apply Array.mem_filter.mpr
    exact ⟨childMember, by native_decide⟩
  exact BinaryFv.Zesu.Elflings.Validation.generated_program_geometry.calleeWithinExecution
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
    parentMember functionInstance_ssz_raw_decodeRaw childIsCallee pc pcIn

theorem decodeRawReturnAfter_agree (returnPc : BitVec 64) (state : State)
    (retired : BitVec 64) :
    Agree decoderPreserved state (decodeRawReturnAfter returnPc state retired) :=
  Agree.weaken (fun _ preserved => preserved.2)
    ((jumpRetirement_writes _ _ _ _).agree platformPreserved_disjoint)

end BinaryFv.Zesu.MachineExecution
