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
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_3

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

/-- The successful first-result path now crosses the outcome branch: the child condition supplies
tag zero, the parent loads it through Sail, and the real `bne` falls through to `0x10328`. -/
theorem decodeInline_first_success_through_branch
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first)
    (value : BinaryFv.Specs.SSZ.RawV4)
    (success : Contracts.meaningDecodeRaw args.bytes = .ok value) :
    ∃ beforeCall childUsed resumed tagRetired branchRetired,
      Trace fromStep 5 state beforeCall ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      Nonempty (CallTransfer decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed) ∧
      Runs (try_step (fromStep + 7 + childUsed) false) resumed
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64)) false ∧
      Runs (try_step (fromStep + 8 + childUsed) false)
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64))
        (decodeInlineFirstSuccessBranchAfter
          (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64))
          branchRetired) false ∧
      (decodeInlineFirstSuccessBranchAfter
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64))
        branchRetired).regs.get? PC = some (BitVec.ofNat 64 0x10328) := by
  obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, -, bound, transfer,
    tagRun, tagPc, tagCode, tagAgree, tagCounter, -, -, -, tagValue, -, -, -⟩ :=
    decodeInline_first_through_result_tag contract fromStep args state pre phase
  have internalTag : Contracts.decodeInternalResultTag
      (Contracts.meaningDecodeRaw args.bytes) = 0 := by
    simp [success, Contracts.decodeInternalResultTag]
  -- The tag written on this path is the literal `0#64`, so one rewrite retypes every retained
  -- fact into the form the conclusion and the branch step both expect.
  rw [internalTag] at tagRun tagPc tagCode tagAgree tagCounter tagValue
  obtain ⟨branchRetired, branchRun, branchPc⟩ := decodeInline_first_success_branch_step
    (fromStep + 8 + childUsed) args state
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64)) pre
      tagCode tagAgree tagCounter tagPc tagValue
  exact ⟨beforeCall, childUsed, resumed, tagRetired, branchRetired, parentTrace, bound,
    transfer, tagRun, branchRun, branchPc⟩

/-- A successful first `decodeRaw` now closes the complete first `decode` segment. Every
parent-owned instruction is executed by Sail, while the emitted child body is represented only by
its selected Level 3 condition. The resulting state is exactly the `memcpy` call boundary. -/
theorem decodeInline_first_success_reaches_post
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first)
    (value : BinaryFv.Specs.SSZ.RawV4)
    (success : Contracts.meaningDecodeRaw args.bytes = .ok value) :
    ∃ childUsed final,
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      DecodeInlineExit args (BitVec.ofNat 64 0x10338) ∧
      DecodeInlineFirstPost args state final ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep (childUsed + 13) state final ∧
      DecodeInlineMachinePost state final ∧
      final.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      DecodeInlineCallerSaveArea args state final := by
  obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, parentPrefix, bound, transfer,
    tagRun, tagPc, tagCode, tagAgree, tagCounter, tagStackRaw, -, -, tagValue, tagGlobals, tagPost,
    tagSaveArea⟩ :=
    decodeInline_first_through_result_tag contract fromStep args state pre phase
  have internalTag : Contracts.decodeInternalResultTag
      (Contracts.meaningDecodeRaw args.bytes) = 0 := by
    simp [success, Contracts.decodeInternalResultTag]
  -- The tag written on this path is the literal `0#64`, so one rewrite retypes every retained
  -- fact about the tagged state; a second selects the outcome inside the source postcondition.
  rw [internalTag] at tagRun tagPc tagCode tagAgree tagCounter tagStackRaw
  rw [internalTag] at tagGlobals tagValue tagPost tagSaveArea
  rw [success] at tagPost
  let tagState := afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64)
  obtain ⟨branchRetired, branchRun, branchPc⟩ := decodeInline_first_success_branch_step
    (fromStep + 8 + childUsed) args state tagState pre tagCode tagAgree tagCounter
    tagPc tagValue
  let branchState := decodeInlineFirstSuccessBranchAfter tagState branchRetired
  have branchMemory : branchState.mem = tagState.mem := by
    rfl
  have branchCode : Contracts.canonicalContractParams.env.CodeIntact branchState := by
    simpa [branchMemory] using tagCode
  have branchPreserves : Agree decoderPreserved tagState branchState :=
    Agree.weaken (fun _ preserved => preserved.2)
      ((fallThroughRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
  have branchAgree : Agree decoderPreserved state branchState :=
    Agree.trans tagAgree branchPreserves
  have branchCounter : RetiredCounterPresent branchState := by
    refine ⟨Sail.BitVec.addInt branchRetired 1, ?_⟩
    simp [branchState, decodeInlineFirstSuccessBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]
  have branchStack : branchState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    ((fallThroughRetirement_writes _ _ _ _).get x2 (by decide)).trans tagStackRaw
  have branchGlobals : branchState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    ((fallThroughRetirement_writes _ _ _ _).get x18 (by decide)).trans tagGlobals
  have branchPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (.ok value) state branchState := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (.ok value) rfl branchMemory
    exact tagPost
  have branchSaveArea : DecodeInlineCallerSaveArea args state branchState := by
    simpa [branchMemory] using tagSaveArea
  obtain ⟨final, setupTrace, setupPrefix, finalPc, finalDestination, finalSource, finalLength,
    finalLink, finalGlobals, finalStack, finalAgree, finalCounter, finalCode, finalPost, finalMemory⟩ :=
    decodeInline_first_success_copy_setup (fromStep + 9 + childUsed) args state branchState pre
      phase value success branchAgree branchCounter branchCode branchPc branchStack branchGlobals
      (by simpa [success] using branchPost)
  have representation : BinaryFv.Zesu.MemoryRepresentation.RawV4Rep final args.inputBase args.bytes
      args.firstTemporaryResultBase value := by
    simpa [success] using finalPost.2.2.2.2
  obtain ⟨bases, allocation, descriptors⟩ := representation.layout
  have rootAllocated := BinaryFv.Zesu.MemoryRepresentation.raw_v4_allocation_root_size final
    args.firstTemporaryResultBase value bases allocation
  obtain ⟨rootBytes, rootSize, rootMemory⟩ :=
    memoryBytes_exists_of_heapArrayRep final args.firstTemporaryResultBase 832 rootAllocated
  have exit : DecodeInlineExit args (BitVec.ofNat 64 0x10338) := by
    simp [DecodeInlineExit, phase, success]
  have post : DecodeInlineFirstPost args state final := by
    simp only [DecodeInlineFirstPost, success]
    exact ⟨by simpa [success] using finalPost, finalPc, finalDestination, finalSource, finalLength,
      finalLink, rootBytes, rootSize, rootMemory⟩
  have finalSaveArea : DecodeInlineCallerSaveArea args state final := by
    unfold DecodeInlineCallerSaveArea
    rw [finalMemory]
    exact branchSaveArea
  obtain ⟨callTransfer⟩ := transfer
  have callPrefix := ConfinedPrefix.ofCall callTransfer
  have tagNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10320) := by
    simp [DecodeInlineExit, phase, success]
  have branchNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10324) := by
    simp [DecodeInlineExit, phase, success]
  have resumePc : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10320) := by
    have returnPcEq : callTransfer.returnPc = BitVec.ofNat 64 0x10320 := by
      apply BitVec.eq_of_toNat_eq
      simpa [decodeRawFirstAttemptCall] using callTransfer.returnMatches
    simpa [returnPcEq] using callTransfer.atResume
  have tagPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 7 + childUsed) 1 resumed tagState :=
    ConfinedPrefix.ownStep' resumePc tagRun (notExit := tagNotExit)
  have branchPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 8 + childUsed) 1 tagState branchState :=
    ConfinedPrefix.ownStep' tagPc (by simpa [branchState] using branchRun)
      (notExit := branchNotExit)
  have finalExit : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 13 + childUsed) 0 final final :=
    ScopedTrace.exitAt (fromStep + 13 + childUsed) final
      (BitVec.ofNat 64 0x10338) finalPc exit
  have afterSetup := setupPrefix 0 final (by
    have stepEq : fromStep + 9 + childUsed + 4 = fromStep + 13 + childUsed := by omega
    rw [stepEq]
    exact finalExit)
  have afterBranch := branchPrefix 4 final (by
    have stepEq : fromStep + 8 + childUsed + 1 = fromStep + 9 + childUsed := by omega
    rw [stepEq]
    exact afterSetup)
  have afterTag := tagPrefix 5 final (by
    have stepEq : fromStep + 7 + childUsed + 1 = fromStep + 8 + childUsed := by omega
    rw [stepEq]
    exact afterBranch)
  have afterCall := callPrefix 6 final (by
    have stepEq : fromStep + 5 + (1 + childUsed + 1) = fromStep + 7 + childUsed := by omega
    rw [stepEq]
    exact afterTag)
  have afterCallCount : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 5) (childUsed + 8)
      beforeCall final := by
    have countEq : 1 + childUsed + 1 + 6 = childUsed + 8 := by omega
    rw [countEq] at afterCall
    exact afterCall
  have complete := parentPrefix (childUsed + 8) final (by
    exact afterCallCount)
  refine ⟨childUsed, final, bound, exit, post, ?_,
    ⟨finalAgree, finalCounter, finalCode, finalGlobals.trans pre.globalsValue.symm⟩, finalStack,
    finalSaveArea⟩
  have countEq : 5 + (childUsed + 8) = childUsed + 13 := by omega
  rw [countEq] at complete
  exact complete

end BinaryFv.Zesu.MachineExecution
