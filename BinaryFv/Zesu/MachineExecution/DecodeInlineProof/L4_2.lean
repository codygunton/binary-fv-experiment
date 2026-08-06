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

/-- Consume the proved one-instruction prefix length segment after the four parent-owned retry
instructions. The result remains at the outgoing `bltu` for the enclosing `decode` proof to execute. -/
theorem decodeInline_retry_uses_length_gate (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) :
    ∃ childUsed childAfter,
      childUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep (4 + childUsed) state childAfter ∧
      HasExactErePrefixInlinePost
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } childAfter ∧
      Agree decoderPreserved state childAfter ∧
      RetiredCounterPresent childAfter ∧
      childAfter.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      childAfter.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      childAfter.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      childAfter.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      childAfter.regs.get? x11 = some (BitVec.ofNat 64 2) ∧
      Contracts.canonicalContractParams.env.CodeIntact childAfter ∧
      childAfter.mem = state.mem := by
  obtain ⟨childEntry, parentPrefix, entryPc, x10Constant, x12Constant, parentAgree,
    parentCounter, parentStackPointer, parentStatus, parentCode, parentMemory, childPre⟩ :=
    decodeInline_retry_reaches_length_gate fromStep args state pre phase
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes }
  have childPre' : HasExactErePrefixInlinePre childArgs childEntry := by
    simpa [childArgs] using childPre
  obtain ⟨childAfter, childTrace, childPost, childAgree, childCounter, childStackFrame,
    childInputPointer, childInputLength, childGlobals, childStatusEq, childMemory⟩ :=
    hasExactErePrefix_length_segment (fromStep + 4) childArgs childEntry childPre' rfl
  have childStatus : childAfter.regs.get? x11 = some (BitVec.ofNat 64 2) :=
    childStatusEq.trans parentStatus
  have childStackPointer : childAfter.regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) := childStackFrame.trans parentStackPointer
  let childUsed := 1
  have childBound : childUsed ≤ hasExactErePrefixInlineStepBound childArgs := by
    simp [childUsed, hasExactErePrefixInlineStepBound]
  have exactSummary : hasExactErePrefixInlineSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + 4) childUsed childEntry childAfter :=
    ⟨rfl, childArgs, childPre', childBound, childTrace, childPost⟩
  have selectedSummary : Level3ChildSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + 4) childUsed childEntry childAfter :=
    .hasExactErePrefix exactSummary
  have childPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 4) childUsed childEntry childAfter := by
    intro count final rest
    exact ScopedTrace.childBody (fromStep + 4) childUsed count _ childEntry childAfter final
      selectedSummary rest
  have completePrefix := ConfinedPrefix.trans parentPrefix childPrefix
  have completeAgree : Agree decoderPreserved state childAfter :=
    Agree.trans parentAgree childAgree
  have childCode : Contracts.canonicalContractParams.env.CodeIntact childAfter := by
    rw [Contracts.DecoderEnvironment.CodeIntact, childMemory]
    exact parentCode
  refine ⟨childUsed, childAfter, ?_, ?_, ?_, completeAgree, childCounter, childStackPointer,
    childInputPointer, childInputLength, childGlobals, childStatus, childCode,
    childMemory.trans parentMemory⟩
  · simpa [childArgs] using childBound
  · simpa [Nat.add_assoc] using completePrefix
  · simpa [childArgs] using childPost

end BinaryFv.Zesu.MachineExecution
