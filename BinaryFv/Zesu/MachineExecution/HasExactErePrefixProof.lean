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
open BinaryFv.RiscV.Sep

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

theorem agree_coreControlFlowNextState (state : State) (pc : BitVec 64) :
    Agree platformPreserved state (coreControlFlowNextState state pc) := by
  intro register preserved
  have notNextPc : nextPC ≠ register := by
    intro equal
    subst register
    simpa [platformPreserved] using preserved
  simp [coreControlFlowNextState, Std.ExtDHashMap.get?_insert, notNextPc]

theorem agree_decoderExecuteState (state : State) (pc : BitVec 64) :
    Agree platformPreserved state
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) :=
  Agree.trans (agree_afterIncrement state)
    (agree_coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)

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

/-! ## Second child segment: reading and assembling the four-byte prefix -/

theorem hasExactErePrefix_prefix_first_lbu_step (stepNo : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args state)
    (phase : args.phase = .prefixBytes) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10398) retired x10
          (BitVec.ofNat 64 (args.bytes[1]'(by
            have := pre.prefixExists phase
            omega)).toNat)) false := by
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10398) := by
    simpa [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs.entryPc, phase] using pre.atEntry
  have pcIn := (hasExactErePrefix_body_classification 0x10398
    (by simp [hasExactErePrefixBodyPcs])).1
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10398) 0x03#8 0x45#8 0x14#8 0x00#8 :=
    fetchFileInstruction state 0x10398 0x03 0x45 0x14 0x00
      (hasExactErePrefix_programImage_of_codeIntact pre.code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine
    (Agree.refl state) (BitVec.ofNat 64 0x10398) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters pre.machine.normal (Agree.refl state) pre.machine.retiredCounter
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x03#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x03#8 0x45#8 0x14#8 0x00#8 =
      (0x00144503 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x03#8 0x45#8 0x14#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (1#12, .Regidx 8#5, .Regidx 10#5, true, 1)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10398)
  let address := BitVec.ofNat 64 (args.inputBase + 1)
  have inputBound : 1 < args.bytes.size := by
    have := pre.prefixExists phase
    omega
  have inputBaseFits : args.inputBase + 1 < 2 ^ 64 := by
    have := pre.inputFits
    omega
  have inputAtExecute : executeState.regs.get? x8 =
      some (BitVec.ofNat 64 args.inputBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.inputPointer]
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := pre.machine.mstatus
  obtain ⟨machineMseccfgBits, machineMseccfgRead, pmmDisabled⟩ := pre.machine.mseccfg
  have mstatusAtExecute : executeState.regs.get? mstatus = some mstatusBits := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, mstatusRead]
  have privilegeAtExecute : executeState.regs.get? cur_privilege = some Privilege.Machine := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.machine.normal.2.1]
  have mseccfgAtExecute : executeState.regs.get? Register.mseccfg =
      some machineMseccfgBits := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, machineMseccfgRead]
  have addressEq : BitVec.ofNat 64 args.inputBase + sign_extend (m := 64) 1#12 = address := by
    have offsetEq : sign_extend (m := 64) 1#12 = (1 : BitVec 64) := by decide
    rw [offsetEq]
    apply BitVec.eq_of_toNat_eq
    simp [address, BitVec.toNat_add]
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 8#5) (sign_extend (m := 64) 1#12)
        (MemoryAccessType.Load mem_payload.Data) 1)
      executeState executeState (.Ext_DataAddr_OK (virtaddr.Virtaddr address)) := by
    rw [← addressEq]
    exact get_transformed_data_addr_machine_load_run executeState (.Regidx 8#5)
      (BitVec.ofNat 64 args.inputBase) (sign_extend (m := 64) 1#12) mstatusBits
      machineMseccfgBits
      (rX_x8_run executeState _ inputAtExecute) mstatusAtExecute privilegeAtExecute mprvZero
      mseccfgAtExecute pmmDisabled
  have executeAgree : Agree platformPreserved state executeState := by
    exact agree_decoderExecuteState state (BitVec.ofNat 64 0x10398)
  have allowed : Entrypoints.ZesuDecodeRaw.DecoderAccessRange
      (Entrypoints.ZesuDecodeRaw.DecoderReadableByte args.machineArgs) address 1 := by
    refine ⟨?_, ?_⟩
    · simp [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt inputBaseFits]
      omega
    · intro index indexLt
      have indexZero : index = 0 := by omega
      subst index
      right
      left
      simp [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs.machineArgs, address,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt inputBaseFits]
      omega
  obtain ⟨physAccess, loadNoMMIO⟩ :=
    pre.machine.dataAccess.load executeState address 1 executeAgree allowed
  let inputByte := args.bytes[1]'inputBound
  have memoryByte : ∀ (index : Nat)
      (indexLt : index < (leBytes 1 (BitVec.ofNat 8 inputByte.toNat)).length),
      executeState.mem.get? (address.toNat + index) =
        some (leBytes 1 (BitVec.ofNat 8 inputByte.toNat))[index] := by
    intro index indexLt
    rw [leBytes_length] at indexLt
    have indexZero : index = 0 := by omega
    subst index
    simpa [executeState, address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt inputBaseFits,
      leBytes, inputByte] using
      pre.inputMemory 1 inputBound
  let loadedValue := BitVec.ofNat 64 inputByte.toNat
  have execute : Runs (execute (.LOAD (1#12, .Regidx 8#5, .Regidx 10#5, true, 1)))
      executeState
      { executeState with regs := executeState.regs.insert x10 loadedValue }
      (.Retire_Success ()) := by
    have zeroExtend : zero_extend (m := 64) (BitVec.ofNat 8 inputByte.toNat) =
        loadedValue := by
      apply BitVec.eq_of_toNat_eq
      simp [zero_extend, Sail.BitVec.zeroExtend, loadedValue]
    change Runs (execute_LOAD 1#12 (.Regidx 8#5) (.Regidx 10#5) true 1) _ _ _
    have run := execute_LOAD_lbu_run executeState _ 1#12 (.Regidx 8#5) (.Regidx 10#5)
      address mstatusBits (BitVec.ofNat 8 inputByte.toNat) mstatusAtExecute
      privilegeAtExecute mprvZero addressRun (is_aligned_vaddr_one _) physAccess loadNoMMIO
      memoryByte (wX_x10_run executeState _)
    rw [zeroExtend] at run
    exact run
  refine ⟨retired, ?_⟩
  simpa [executeState, afterRegisterWrite, loadedValue] using
    tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10398) retired inhibit config
      0x03#8 0x45#8 0x14#8 0x00#8 (.LOAD (1#12, .Regidx 8#5, .Regidx 10#5, true, 1)) x10
      loadedValue fetch noMMIO fetched interrupts base decode
      notExpected execute (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead
      configRead notInhibited machineEnabled retiredRead

theorem hasExactErePrefix_prefix_second_lbu_step (stepNo : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (baseState state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args baseState)
    (phase : args.phase = .prefixBytes)
    (agree : Agree platformPreserved baseState state)
    (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1039c))
    (inputPointer : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x1039c) retired x12
          (BitVec.ofNat 64 (args.bytes[0]'(by
            have := pre.prefixExists phase
            omega)).toNat)) false := by
  have pcIn := (hasExactErePrefix_body_classification 0x1039c
    (by simp [hasExactErePrefixBodyPcs])).1
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1039c) 0x03#8 0x46#8 0x04#8 0x00#8 :=
    fetchFileInstruction state 0x1039c 0x03 0x46 0x04 0x00 code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine agree
    (BitVec.ofNat 64 0x1039c) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters pre.machine.normal agree retiredPresent
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x03#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x03#8 0x46#8 0x04#8 0x00#8 =
      (0x00044603 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x03#8 0x46#8 0x04#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0#12, .Regidx 8#5, .Regidx 12#5, true, 1)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1039c)
  let address := BitVec.ofNat 64 args.inputBase
  have inputBound : 0 < args.bytes.size := by
    have := pre.prefixExists phase
    omega
  have inputBaseFits : args.inputBase < 2 ^ 64 := by
    have := pre.inputFits
    omega
  have inputAtExecute : executeState.regs.get? x8 =
      some (BitVec.ofNat 64 args.inputBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, inputPointer]
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := pre.machine.mstatus
  obtain ⟨machineMseccfgBits, machineMseccfgRead, pmmDisabled⟩ := pre.machine.mseccfg
  have mstatusState : state.regs.get? mstatus = some mstatusBits :=
    (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegeState : state.regs.get? cur_privilege = some Privilege.Machine :=
    (agree cur_privilege (by simp [platformPreserved])).trans pre.machine.normal.2.1
  have mseccfgState : state.regs.get? Register.mseccfg = some machineMseccfgBits :=
    (agree Register.mseccfg (by simp [platformPreserved])).trans machineMseccfgRead
  have mstatusAtExecute : executeState.regs.get? mstatus = some mstatusBits := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, mstatusState]
  have privilegeAtExecute : executeState.regs.get? cur_privilege = some Privilege.Machine := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, privilegeState]
  have mseccfgAtExecute : executeState.regs.get? Register.mseccfg =
      some machineMseccfgBits := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, mseccfgState]
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 8#5) (sign_extend (m := 64) 0#12)
        (MemoryAccessType.Load mem_payload.Data) 1)
      executeState executeState (.Ext_DataAddr_OK (virtaddr.Virtaddr address)) := by
    have addressEq : BitVec.ofNat 64 args.inputBase + sign_extend (m := 64) 0#12 = address := by
      have offsetEq : sign_extend (m := 64) 0#12 = (0 : BitVec 64) := by decide
      simp [address, offsetEq]
    rw [← addressEq]
    exact get_transformed_data_addr_machine_load_run executeState (.Regidx 8#5)
      (BitVec.ofNat 64 args.inputBase) (sign_extend (m := 64) 0#12) mstatusBits
      machineMseccfgBits (rX_x8_run executeState _ inputAtExecute) mstatusAtExecute
      privilegeAtExecute mprvZero mseccfgAtExecute pmmDisabled
  have executeAgree : Agree platformPreserved baseState executeState :=
    Agree.trans agree (agree_decoderExecuteState state (BitVec.ofNat 64 0x1039c))
  have allowed : Entrypoints.ZesuDecodeRaw.DecoderAccessRange
      (Entrypoints.ZesuDecodeRaw.DecoderReadableByte args.machineArgs) address 1 := by
    refine ⟨?_, ?_⟩
    · simp [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt inputBaseFits]
      omega
    · intro index indexLt
      have indexZero : index = 0 := by omega
      subst index
      right
      left
      simp [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs.machineArgs, address,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt inputBaseFits, inputBound]
  obtain ⟨physAccess, loadNoMMIO⟩ :=
    pre.machine.dataAccess.load executeState address 1 executeAgree allowed
  let inputByte := args.bytes[0]'inputBound
  have memoryByte : ∀ (index : Nat)
      (indexLt : index < (leBytes 1 (BitVec.ofNat 8 inputByte.toNat)).length),
      executeState.mem.get? (address.toNat + index) =
        some (leBytes 1 (BitVec.ofNat 8 inputByte.toNat))[index] := by
    intro index indexLt
    rw [leBytes_length] at indexLt
    have indexZero : index = 0 := by omega
    subst index
    have memEq : executeState.mem = baseState.mem := by
      exact memory
    rw [memEq]
    simpa [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt inputBaseFits,
      leBytes, inputByte] using pre.inputMemory 0 inputBound
  let loadedValue := BitVec.ofNat 64 inputByte.toNat
  have execute : Runs (execute (.LOAD (0#12, .Regidx 8#5, .Regidx 12#5, true, 1)))
      executeState { executeState with regs := executeState.regs.insert x12 loadedValue }
      (.Retire_Success ()) := by
    have zeroExtend : zero_extend (m := 64) (BitVec.ofNat 8 inputByte.toNat) =
        loadedValue := by
      apply BitVec.eq_of_toNat_eq
      simp [zero_extend, Sail.BitVec.zeroExtend, loadedValue]
    change Runs (execute_LOAD 0#12 (.Regidx 8#5) (.Regidx 12#5) true 1) _ _ _
    have run := execute_LOAD_lbu_run executeState _ 0#12 (.Regidx 8#5) (.Regidx 12#5)
      address mstatusBits (BitVec.ofNat 8 inputByte.toNat) mstatusAtExecute
      privilegeAtExecute mprvZero addressRun (is_aligned_vaddr_one _) physAccess loadNoMMIO
      memoryByte (wX_x12_run executeState _)
    rw [zeroExtend] at run
    exact run
  refine ⟨retired, ?_⟩
  simpa [executeState, afterRegisterWrite, loadedValue] using
    tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x1039c) retired inhibit config
      0x03#8 0x46#8 0x04#8 0x00#8 (.LOAD (0#12, .Regidx 8#5, .Regidx 12#5, true, 1)) x12
      loadedValue fetch noMMIO fetched interrupts base decode notExpected execute
      (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
      machineEnabled retiredRead

theorem hasExactErePrefix_prefix_first_two_lbu_steps (fromStep : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args state)
    (phase : args.phase = .prefixBytes) :
    ∃ retired1 retired2,
      let byte1 := args.bytes[1]'(by have := pre.prefixExists phase; omega)
      let byte0 := args.bytes[0]'(by have := pre.prefixExists phase; omega)
      let after1 := afterRegisterWrite state (BitVec.ofNat 64 0x10398) retired1 x10
        (BitVec.ofNat 64 byte1.toNat)
      let after2 := afterRegisterWrite after1 (BitVec.ofNat 64 0x1039c) retired2 x12
        (BitVec.ofNat 64 byte0.toNat)
      Runs (try_step fromStep false) state after1 false ∧
        Runs (try_step (fromStep + 1) false) after1 after2 false := by
  obtain ⟨retired1, first⟩ := hasExactErePrefix_prefix_first_lbu_step fromStep args state pre phase
  let byte1 := args.bytes[1]'(by have := pre.prefixExists phase; omega)
  let after1 := afterRegisterWrite state (BitVec.ofNat 64 0x10398) retired1 x10
    (BitVec.ofNat 64 byte1.toNat)
  have agree1 : Agree platformPreserved state after1 := by
    exact afterRegisterWrite_agree (by simp [platformPreserved])
  have atSecond : after1.regs.get? PC = some (BitVec.ofNat 64 0x1039c) := by
    simpa [after1] using
      afterRegisterWrite_pc state (BitVec.ofNat 64 0x10398) retired1 x10
        (BitVec.ofNat 64 byte1.toNat)
  have inputPointer : after1.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [after1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      pre.inputPointer]
  obtain ⟨retired2, second⟩ := hasExactErePrefix_prefix_second_lbu_step (fromStep + 1)
    args state after1 pre phase agree1 rfl
    (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10398) retired1 x10
      (BitVec.ofNat 64 byte1.toNat)) atSecond inputPointer
  refine ⟨retired1, retired2, ?_⟩
  dsimp only
  exact ⟨by simpa [after1, byte1] using first, by simpa [after1, byte1] using second⟩

end BinaryFv.Zesu.MachineExecution
