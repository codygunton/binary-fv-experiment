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
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_5
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_6
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_7
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_8
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_9
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L4_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L4_2

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

/-- The first Level 3 condition is consumed only after the six parent-owned instructions have
executed and established its complete machine entry predicate. -/
theorem decodeInline_first_uses_decodeRaw_contract
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ childEntry childUsed childExit,
      Trace fromStep 6 state childEntry ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      Level3ChildSummary functionInstance_ssz_raw_decodeRawId
        (fromStep + 6) childUsed childEntry childExit := by
  obtain ⟨childEntry, parentTrace, childPre, -⟩ :=
    decodeInline_first_enters_decodeRaw fromStep args state pre phase
  obtain ⟨childUsed, childExit, bound, childSummary⟩ :=
    compiledDecodeRawSummary_of_contract contract args.firstRawArgs (fromStep + 6)
      childEntry childPre
  exact ⟨childEntry, childUsed, childExit, parentTrace, bound,
    Level3ChildSummary.decodeRaw childSummary⟩

theorem decodeInline_first_decodeRaw_run
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ childEntry childUsed childExit,
      Trace fromStep 6 state childEntry ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      EnteredFunctionTrace
        (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
        (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
        (Contracts.functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
        (fromStep + 6) childUsed childEntry childExit ∧
      childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x10320) ∧
      compiledDecodeRawContract.binding.exit args.firstRawArgs
        (compiledDecodeRawContract.spec.meaning args.firstRawArgs) childEntry childExit := by
  obtain ⟨childEntry, parentTrace, childPre, childLink⟩ :=
    decodeInline_first_enters_decodeRaw fromStep args state pre phase
  obtain ⟨childUsed, childExit, bound, childTrace, childPost⟩ :=
    contract args.firstRawArgs (fromStep + 6) childEntry childPre
  exact ⟨childEntry, childUsed, childExit, parentTrace, bound, childTrace, childLink, childPost⟩

end BinaryFv.Zesu.MachineExecution
