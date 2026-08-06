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

/-- Execute the internal retry `memcpy` call at `0x103ec` through Sail. -/
theorem decodeInline_retry_memcpy_call_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103ec))
    (callBase : state.regs.get? x1 = some (BitVec.ofNat 64 0x143e8)) :
    ∃ retired,
      Runs (try_step stepNo false) state (decodeInlineMemcpyCallAfter state retired) false ∧
      (decodeInlineMemcpyCallAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x13eb8) ∧
      (decodeInlineMemcpyCallAfter state retired).regs.get? x1 =
        some (BitVec.ofNat 64 0x103f0) ∧
      (decodeInlineMemcpyCallAfter state retired).regs.get? x10 = state.regs.get? x10 ∧
      (decodeInlineMemcpyCallAfter state retired).regs.get? x11 = state.regs.get? x11 ∧
      (decodeInlineMemcpyCallAfter state retired).regs.get? x12 = state.regs.get? x12 ∧
      (decodeInlineMemcpyCallAfter state retired).regs.get? x2 = state.regs.get? x2 ∧
      Agree decoderPreserved state (decodeInlineMemcpyCallAfter state retired) ∧
      (decodeInlineMemcpyCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (decodeInlineMemcpyCallAfter state retired) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContextOfDecoderAgree pre.machine agree
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) state
      (decodeInlineMemcpyCallAfter state retired) false :=
    decoderJalrCallStep pre.machine agree retiredPresent
      (hasExactErePrefix_programImage_of_codeIntact code)
      stepNo 0x103ec 0xe7 0x80 0x00 0xad 0xad0#12 1#5 1#5 (BitVec.ofNat 64 0x143e8)
      (BitVec.ofNat 64 0x103f0) (BitVec.ofNat 64 0x13eb8) atPc
      (rX_bits_run_x1 _ _ (decoderExecuteState_get? callBase)) (wX_bits_run_x1 _ _)
  have callWrites : WritesOnlyRegs _ state (decodeInlineMemcpyCallAfter state retired) :=
    callRetirement_writes _ _ _ _ _ _
  fail_if_success (have : (decodeInlineMemcpyCallAfter state retired).regs.get? x1 =
    state.regs.get? x1 := by grind)
  refine ⟨retired, run, ?_, ?_, by grind, by grind, by grind, by grind, ?_,
    jalrCallAfterRetired_mem _ _ _ _ _ _, ?_⟩
  · simp [decodeInlineMemcpyCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  · apply tryStepControlFlowAfterRetired_preserves_register
    · exact callLinkState_link _ _ _ x1 (BitVec.ofNat 64 0x103f0)
    · decide
    · decide
  · apply jalrCallAfterRetired_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  · exact ⟨Sail.BitVec.addInt retired 1, by
      simp [decodeInlineMemcpyCallAfter, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick]⟩

/-- The enclosing decoder's configured-machine premise supplies the proved emitted `memcpy` at
the retry call site. Both copy intervals are concrete stack objects; no ABI premise is used. -/
theorem decodeInline_retry_memcpy_machine_pre (args : DecodeInlineArgs) (contents : ByteArray)
    (baseState childEntry : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState childEntry)
    (counter : RetiredCounterPresent childEntry)
    (atEntry : childEntry.regs.get? PC = some (BitVec.ofNat 64 0x13eb8))
    (returnAddress : childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x103f0)) :
    MemcpyMachinePre Contracts.canonicalContractParams.env
      (decodeInlineRetryCopyArgs args contents)
      childEntry := by
  let copyArgs := decodeInlineRetryCopyArgs args contents
  change MemcpyMachinePre Contracts.canonicalContractParams.env copyArgs childEntry
  have machineAtEntry : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono agree counter
  have resultSize : Contracts.canonicalContractParams.env.record.entryResult = 848 := by
    have pinned := congrArg (fun record => record.entryResult) Contracts.canonicalRecordSizes_pinned
    simpa [Contracts.canonicalContractParams, Contracts.canonicalEnvironment] using pinned
  have sourceFits : copyArgs.source + copyArgs.length ≤ 2 ^ 64 := by
    dsimp [copyArgs, decodeInlineRetryCopyArgs, DecodeInlineArgs.retryRawArgs]
    have stackFit := pre.stackObjectsFit
    rw [resultSize] at stackFit
    omega
  have destinationFits : copyArgs.destination + copyArgs.length ≤ 2 ^ 64 := by
    dsimp [copyArgs, decodeInlineRetryCopyArgs, DecodeInlineArgs.finalResultBase]
    have stackFit := pre.stackObjectsFit
    rw [resultSize] at stackFit
    omega
  have sourceReadable : ∀ index, index < copyArgs.length →
      DecoderReadableByte args.machineArgs (copyArgs.source + index) := by
    intro index bound
    right; right; left
    dsimp [copyArgs, decodeInlineRetryCopyArgs, DecodeInlineArgs.retryRawArgs] at bound ⊢
    have stack := pre.stackObjectsReadable (0x6b0 + index) (by rw [resultSize]; omega)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stack
  have destinationWritable : ∀ index, index < copyArgs.length →
      DecoderWritableByte (copyArgs.destination + index) := by
    intro index bound
    left
    dsimp [copyArgs, decodeInlineRetryCopyArgs, DecodeInlineArgs.finalResultBase] at bound ⊢
    have stack := pre.stackObjectsReadable (0x20 + index) (by rw [resultSize]; omega)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stack
  have destinationNotFile : ∀ index, index < copyArgs.length →
      Contracts.canonicalContractParams.env.image.readFileByte?
        (copyArgs.destination + index) = none := by
    intro index bound
    cases read : Contracts.canonicalContractParams.env.image.readFileByte?
        (copyArgs.destination + index) with
    | none => rfl
    | some byte =>
        have segmentInfo := BinaryFv.Binary.ProgramImage.readFileByte?_mem_segment read
        obtain ⟨segment, member, -, addressHigh⟩ := segmentInfo
        have fileSegmentsBelow : Artifacts.programImage.segments.toList.all
            (fun segment => decide
              (segment.initialEndAddress ≤ Entrypoints.ZesuDecodeRaw.loadedCeiling)) = true := by
          native_decide
        have segmentHigh : segment.initialEndAddress ≤
            Entrypoints.ZesuDecodeRaw.loadedCeiling :=
          of_decide_eq_true (List.all_eq_true.mp fileSegmentsBelow segment (by
            simpa [Contracts.canonicalContractParams, Contracts.canonicalEnvironment] using member))
        have stackByte : Contracts.canonicalContractParams.env.stack
            (copyArgs.destination + index) := by
          dsimp [copyArgs, decodeInlineRetryCopyArgs, DecodeInlineArgs.finalResultBase] at bound ⊢
          have stack := pre.stackObjectsReadable (0x20 + index) (by rw [resultSize]; omega)
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stack
        have below : copyArgs.destination + index < Entrypoints.ZesuDecodeRaw.loadedCeiling :=
          Nat.lt_of_lt_of_le addressHigh segmentHigh
        exact absurd stackByte (Contracts.canonicalStack_above_loaded _ below)
  have destinationNotAllocator : ∀ address,
      Contracts.canonicalContractParams.env.allocatorState address →
      address < copyArgs.destination ∨ copyArgs.destination + copyArgs.length ≤ address := by
    intro address allocator
    by_cases before : address < copyArgs.destination
    · exact Or.inl before
    right
    by_cases after : copyArgs.destination + copyArgs.length ≤ address
    · exact after
    exfalso
    have overlap : copyArgs.destination ≤ address ∧
        address < copyArgs.destination + copyArgs.length :=
      ⟨Nat.le_of_not_gt before, Nat.lt_of_not_ge after⟩
    have indexBound : address - copyArgs.destination < copyArgs.length := by omega
    have stackByte : Contracts.canonicalContractParams.env.stack
        (copyArgs.destination + (address - copyArgs.destination)) := by
      dsimp [copyArgs, decodeInlineRetryCopyArgs, DecodeInlineArgs.finalResultBase] at indexBound ⊢
      have stack := pre.stackObjectsReadable (0x20 + (address - (args.stackBase + 0x20)))
        (by rw [resultSize]; omega)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stack
    have addressEq : copyArgs.destination + (address - copyArgs.destination) = address := by omega
    have canonicalStack : Contracts.canonicalContractParams.env.stack address := by
      rw [← addressEq]
      exact stackByte
    exact Contracts.canonicalStack_disjoint_from_allocatorState address allocator canonicalStack
  apply memcpyMachinePre_of_decoder copyArgs childEntry machineAtEntry
  · intro pc bodyPc
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    rcases bodyPc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide
  · exact atEntry
  · exact ⟨BitVec.ofNat 64 0x103f0, returnAddress, by decide⟩
  · rfl
  · simp [copyArgs, decodeInlineRetryCopyArgs]
  · dsimp [copyArgs, decodeInlineRetryCopyArgs, DecodeInlineArgs.retryRawArgs]
    have stackFit := pre.stackObjectsFit
    rw [resultSize] at stackFit
    omega
  · dsimp [copyArgs, decodeInlineRetryCopyArgs, DecodeInlineArgs.finalResultBase]
    have stackFit := pre.stackObjectsFit
    rw [resultSize] at stackFit
    omega
  · exact sourceFits
  · exact destinationFits
  · exact destinationNotFile
  · exact destinationNotAllocator
  · exact sourceReadable
  · exact destinationWritable

end BinaryFv.Zesu.MachineExecution
