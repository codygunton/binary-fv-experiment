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

/-- Every listed instruction lies in the generated execution extent of this compiled instance.
This checks completeness against the proof's confinement predicate independently of DWARF labels. -/
theorem decodeInline_owned_in_execution_region :
    ∀ entry ∈ decodeInlineOwnedInstructionWords, decodeInlineOwnPcs (BitVec.ofNat 64 entry.1) := by
  intro entry member
  simp only [decodeInlineOwnedInstructionWords, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals owned_pc

/-- `postEntry` is memory-only at the canonical `RawV4` representation. This rebases its relative
write frame and transports its result representation when surrounding instructions change only
registers. -/
theorem canonicalPostEntry_of_mem_eq (args : Contracts.EntryArgs)
    (result : Except Contracts.DecodeError BinaryFv.Specs.SSZ.RawV4)
    {before after before' after' : State}
    (beforeMemory : before'.mem = before.mem) (afterMemory : after'.mem = after.mem)
    (post : Contracts.postEntry Contracts.canonicalContractParams.env args
      Contracts.canonicalContractParams.repRawV4 result before after) :
    Contracts.postEntry Contracts.canonicalContractParams.env args
      Contracts.canonicalContractParams.repRawV4 result before' after' := by
  rcases post with ⟨input, code, writes, status, outcome⟩
  refine ⟨?_, ?_, writesOnlyWithinOwnAllocation_of_mem_eq _ _ _ beforeMemory afterMemory writes,
    ?_, ?_⟩
  · intro index bound
    rw [afterMemory]
    exact input index bound
  · change Contracts.canonicalContractParams.env.image.fileBytesMatchMemory after'.mem
    rw [afterMemory]
    exact code
  · rcases status with ⟨tagBound, low, high⟩
    exact ⟨tagBound, by simpa [afterMemory] using low, by simpa [afterMemory] using high⟩
  · cases result with
    | ok value =>
        exact rawV4Rep_of_mem_eq afterMemory outcome
    | error error => exact outcome

/-! ## First segment: preparing the initial `decodeRaw` call -/

end BinaryFv.Zesu.MachineExecution
