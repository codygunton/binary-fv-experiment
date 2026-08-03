import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level3Contracts
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep

/-!
# Sail proof for the inlined exact-ERE-prefix check

The selected compiler instance is split at two generated outgoing instructions. Eleven body
instructions belong to the child; `bltu` at `0x10394` and the final `or` at `0x103c0` are executed
by the enclosing inlined-`decode` proof. This file first pins that complete 13-word partition to the
immutable image before constructing the two body traces.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- One little-endian instruction word read directly from the pinned program image. -/
def hasExactErePrefixImageWord? (address : Nat) : Option Nat := do
  let byte0 ← Artifacts.programImage.readByte? address
  let byte1 ← Artifacts.programImage.readByte? (address + 1)
  let byte2 ← Artifacts.programImage.readByte? (address + 2)
  let byte3 ← Artifacts.programImage.readByte? (address + 3)
  pure (byte0.toNat + byte1.toNat * 2 ^ 8 + byte2.toNat * 2 ^ 16 + byte3.toNat * 2 ^ 24)

/-- All words in the two attributed segments, including the two separately executed outgoing
instructions. Keeping the addresses beside the words makes omissions and shifted boundaries visible. -/
def hasExactErePrefixInstructionWords : List (Nat × Nat) :=
  [(0x10390, 0x00c48633), (0x10394, 0x08a66663),
    (0x10398, 0x00144503), (0x1039c, 0x00044603),
    (0x103a0, 0x00244703), (0x103a4, 0x00344783),
    (0x103a8, 0x00851513), (0x103ac, 0x00c56533),
    (0x103b0, 0xffc48693), (0x103b4, 0x01071713),
    (0x103b8, 0x01879793), (0x103bc, 0x00e7e733),
    (0x103c0, 0x00a76533)]

def hasExactErePrefixBodyPcs : List Nat :=
  [0x10390, 0x10398, 0x1039c, 0x103a0, 0x103a4, 0x103a8,
    0x103ac, 0x103b0, 0x103b4, 0x103b8, 0x103bc]

def hasExactErePrefixOutgoingPcs : List Nat := [0x10394, 0x103c0]

/-- Kernel-checked identity of all 13 words against the pinned image. -/
theorem hasExactErePrefix_instruction_words_pinned :
    ∀ entry ∈ hasExactErePrefixInstructionWords,
      hasExactErePrefixImageWord? entry.1 = some entry.2 := by
  native_decide

/-- The eleven child-body words are exactly in the generated execution region and are not exits. -/
theorem hasExactErePrefix_body_classification :
    ∀ pc ∈ hasExactErePrefixBodyPcs,
      functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
          (BitVec.ofNat 64 pc) ∧
        ¬ functionInstanceExitPred
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
          (BitVec.ofNat 64 pc) := by
  intro pc member
  simp only [hasExactErePrefixBodyPcs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals first
    | (apply functionInstanceExecutionPcs_iff_ranges.mpr
       apply RegionPcs.iff_inRanges.mpr
       native_decide)
    | simp [functionInstanceExitPred, FunctionInstance.isExit,
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35]

/-- The other two attributed words are the generated outgoing-instruction sources. -/
theorem hasExactErePrefix_outgoing_classification :
    ∀ pc ∈ hasExactErePrefixOutgoingPcs,
      functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
          (BitVec.ofNat 64 pc) ∧
        functionInstanceExitPred
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
          (BitVec.ofNat 64 pc) := by
  intro pc member
  simp only [hasExactErePrefixOutgoingPcs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals constructor
  all_goals first
    | (apply functionInstanceExecutionPcs_iff_ranges.mpr
       apply RegionPcs.iff_inRanges.mpr
       native_decide)
    | simp [functionInstanceExitPred, FunctionInstance.isExit,
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35]

/-! ## Common configured-machine step context -/

theorem decoderStepPlatform {instructionPcs : BitVec 64 → Prop} {args}
    {base state : State} (machine : Entrypoints.ZesuDecodeRaw.DecoderMachinePre
      instructionPcs args base) (agree : Agree platformPreserved base state)
    (pc : BitVec 64) (atPc : state.regs.get? PC = some pc) (pcIn : instructionPcs pc)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3) :
    ∃ mseccfgBits, StepPlatform state pc byte0 byte1 byte2 byte3 mseccfgBits := by
  have afterIncrementAgree : Agree platformPreserved base
      (tryStepControlFlowAfterIncrement state) :=
    Agree.trans agree (agree_afterIncrement state)
  have atPcAfter : (tryStepControlFlowAfterIncrement state).regs.get? PC = some pc :=
    pc_afterIncrement state pc atPc
  obtain ⟨fetch, noMMIO, interrupts, notExpected⟩ :=
    machine.platform _ pc afterIncrementAgree atPcAfter pcIn
  obtain ⟨mseccfgBits, mseccfgRead, -⟩ := machine.mseccfg
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (afterIncrementAgree cur_privilege (by simp [platformPreserved])).trans machine.normal.2.1
  have mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg =
      some mseccfgBits :=
    (afterIncrementAgree Register.mseccfg (by simp [platformPreserved])).trans mseccfgRead
  exact ⟨mseccfgBits, fetch, noMMIO, bytes, interrupts, notExpected, privilege, mseccfg⟩

theorem decoderStepCounters {base state : State}
    (normal : NormalExecutionState base) (agree : Agree platformPreserved base state)
    (retiredPresent : RetiredCounterPresent state) :
    ∃ retired inhibit config, StepCounters state retired inhibit config := by
  obtain ⟨retired, retiredRead⟩ := retiredPresent
  refine ⟨retired, 0, 0, ?_, ?_, ?_, by decide, by decide, retiredRead⟩
  · exact (agree hart_state (by simp [platformPreserved])).trans normal.1
  · exact (agree mcountinhibit (by simp [platformPreserved])).trans normal.2.2.2.2.2.2.2.2.1
  · exact (agree minstretcfg (by simp [platformPreserved])).trans
      normal.2.2.2.2.2.2.2.2.2.1

/-! ## First child segment: the length-gate arithmetic -/

theorem hasExactErePrefix_length_add_fetch (state : State)
    (code : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10390)
      0x33#8 0x86#8 0xc4#8 0x00#8 :=
  fetchFileInstruction state 0x10390 0x33 0x86 0xc4 0x00 code
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem hasExactErePrefix_programImage_of_codeIntact {state : State}
    (code : Contracts.canonicalContractParams.env.CodeIntact state) :
    Artifacts.programImage.fileBytesMatchMemory state.mem := by
  have imageEq : Contracts.canonicalEnvironment.image = Artifacts.programImage := by
    simp only [Contracts.canonicalEnvironment]
  have canonicalCode : Contracts.canonicalEnvironment.image.fileBytesMatchMemory state.mem := code
  rwa [imageEq] at canonicalCode

theorem hasExactErePrefix_length_add_step (stepNo : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args state)
    (phase : args.phase = .lengthGate) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10390) retired x12
          (BitVec.ofNat 64 args.bytes.size +
            BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))) false := by
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10390) := by
    simpa [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs.entryPc, phase] using pre.atEntry
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
      (BitVec.ofNat 64 0x10390) :=
    (hasExactErePrefix_body_classification 0x10390 (by simp [hasExactErePrefixBodyPcs])).1
  have bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10390) 0x33#8 0x86#8 0xc4#8 0x00#8 :=
    hasExactErePrefix_length_add_fetch state (hasExactErePrefix_programImage_of_codeIntact pre.code)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine
    (Agree.refl state) (BitVec.ofNat 64 0x10390) atPc pcIn _ _ _ _ bytes
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters pre.machine.normal (Agree.refl state) pre.machine.retiredCounter
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have wordEq : fetchWord 0x33#8 0x86#8 0xc4#8 0x00#8 =
      (0x00c48633 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x86#8 0xc4#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 12#5, .Regidx 9#5, .Regidx 12#5, .ADD)) := by
    rw [wordEq]
    decode_run
  have base : BaseInstructionEncoding 0x33#8 := by
    unfold BaseInstructionEncoding
    decide
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10390)
  have lengthAtExecute : executeState.regs.get? x9 =
      some (BitVec.ofNat 64 args.bytes.size) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.inputLength]
  have constantAtExecute : executeState.regs.get? x12 =
      some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)) := by
    obtain ⟨-, constant⟩ := pre.preparedConstants phase
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, constant]
  let result := BitVec.ofNat 64 args.bytes.size +
    BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)
  have execute : Runs
      (execute (.RTYPE (.Regidx 12#5, .Regidx 9#5, .Regidx 12#5, .ADD))) executeState
      { executeState with regs := executeState.regs.insert x12 result }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 12#5) (.Regidx 9#5) (.Regidx 12#5) .ADD) _ _ _
    apply execute_RTYPE_run executeState _ (.Regidx 12#5) (.Regidx 9#5) (.Regidx 12#5) .ADD
      (BitVec.ofNat 64 args.bytes.size) (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))
    · exact rX_x9_run executeState _ lengthAtExecute
    · exact rX_x12_run executeState _ constantAtExecute
    · exact wX_x12_run executeState _
  refine ⟨retired, ?_⟩
  simpa [executeState, afterRegisterWrite] using
    tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10390) retired inhibit config
      0x33#8 0x86#8 0xc4#8 0x00#8
      (.RTYPE (.Regidx 12#5, .Regidx 9#5, .Regidx 12#5, .ADD)) x12
      result
      fetch noMMIO fetched interrupts base decode notExpected execute
      (by decide) (by decide) (by decide) (by decide)
      hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

theorem hasExactErePrefix_length_segment (fromStep : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args state)
    (phase : args.phase = .lengthGate) :
    ∃ after,
      FunctionTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
        (functionInstanceExitPred
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
        fromStep 1 state after ∧
      Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePost args after := by
  obtain ⟨retired, step⟩ := hasExactErePrefix_length_add_step fromStep args state pre phase
  let result := BitVec.ofNat 64 args.bytes.size +
    BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)
  let after := afterRegisterWrite state (BitVec.ofNat 64 0x10390) retired x12 result
  have atStart : state.regs.get? PC = some (BitVec.ofNat 64 0x10390) := by
    simpa [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs.entryPc, phase] using pre.atEntry
  have classified := hasExactErePrefix_body_classification 0x10390
    (by simp [hasExactErePrefixBodyPcs])
  have atExit : after.regs.get? PC = some (BitVec.ofNat 64 0x10394) := by
    simpa [after] using
      afterRegisterWrite_pc state (BitVec.ofNat 64 0x10390) retired x12 result
  have trace : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
      (functionInstanceExitPred
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
      fromStep 1 state after := by
    refine .step fromStep 0 _ state after after atStart classified.1 classified.2 ?_ ?_
    · simpa [after, result] using step
    · exact .exitAt (fromStep + 1) after (BitVec.ofNat 64 0x10394) atExit
        Entrypoints.ZesuDecodeRaw.hasExactErePrefixInline_length_exit
  refine ⟨after, trace, ?_⟩
  simp only [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePost, phase]
  refine ⟨atExit, ?_, ?_⟩
  · obtain ⟨constant, -⟩ := pre.preparedConstants phase
    simpa [after, result, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using constant
  · have value : result = BitVec.ofNat 64
        (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4)) := by
      simp [result, BitVec.ofNat_add]
    simpa [after, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, value]

end BinaryFv.Zesu.MachineExecution
