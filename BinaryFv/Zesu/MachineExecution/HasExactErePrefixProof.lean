import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level3Contracts
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
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

/-- One retiring `try_step` from `state` at `pc` that writes `value` to `destination`. The
retired-counter witness stays existential because `try_step` picks it. Reducible on purpose: the
underlying `∃ retired, Runs …` is what every proof and caller manipulates. -/
abbrev StepWritesRegister (stepNo : Nat) (state : State) (pc : Nat)
    (destination : Register) (value : RegisterType destination) : Prop :=
  ∃ retired, Runs (try_step stepNo false) state
    (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination value) false

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

/-- Every explicitly attributed child word is an aligned fetch start as well as a byte-range member. -/
theorem hasExactErePrefix_body_fetch_classification :
    ∀ pc ∈ hasExactErePrefixBodyPcs,
      DecoderFetchPc
          (functionInstanceExecutionPcs generatedProgram
            functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
          (BitVec.ofNat 64 pc) := by
  intro pc member
  refine ⟨(hasExactErePrefix_body_classification pc member).1, ?_⟩
  simp only [hasExactErePrefixBodyPcs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    native_decide

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

/-- Shared Sail semantics for an input-relative unsigned-byte load. Concrete instruction theorems
still pin their own ELF word, decode result, destination write, PC, and retirement. -/
theorem decoderInputLbuExecute
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (base state executeAfter : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args base)
    (offset : Nat) (offsetBound : offset < args.bytes.size) (addressFits : args.inputBase + offset < 2 ^ 64)
    (immediate : BitVec 12)
    (immediateValue : sign_extend (m := 64) immediate = BitVec.ofNat 64 offset)
    (destination : regidx)
    (agree : Agree platformPreserved base state)
    (memory : state.mem = base.mem)
    (inputPointer : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase))
    (write : Runs (wX_bits destination
      (zero_extend (m := 64) (BitVec.ofNat 8 (args.bytes[offset]'offsetBound).toNat)))
      state executeAfter ()) :
    Runs (execute_LOAD immediate (.Regidx 8#5) destination true 1) state executeAfter
      (.Retire_Success ()) := by
  let address := BitVec.ofNat 64 (args.inputBase + offset)
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := pre.machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := pre.machine.mseccfg
  have mstatusState : state.regs.get? mstatus = some mstatusBits :=
    (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegeState : state.regs.get? cur_privilege = some Privilege.Machine :=
    (agree cur_privilege (by simp [platformPreserved])).trans pre.machine.normal.2.1
  have mseccfgState : state.regs.get? Register.mseccfg = some mseccfgBits :=
    (agree Register.mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have addressEq : BitVec.ofNat 64 args.inputBase + sign_extend (m := 64) immediate = address := by
    rw [immediateValue, ← BitVec.ofNat_add]
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 8#5) (sign_extend (m := 64) immediate)
        (MemoryAccessType.Load mem_payload.Data) 1)
      state state (.Ext_DataAddr_OK (virtaddr.Virtaddr address)) := by
    rw [← addressEq]
    exact get_transformed_data_addr_machine_load_run state (.Regidx 8#5)
      (BitVec.ofNat 64 args.inputBase) (sign_extend (m := 64) immediate) mstatusBits mseccfgBits
      (rX_x8_run state _ inputPointer) mstatusState privilegeState mprvZero mseccfgState pmmDisabled
  have allowed : Entrypoints.ZesuDecodeRaw.DecoderAccessRange
      (Entrypoints.ZesuDecodeRaw.DecoderReadableByte args.machineArgs) address 1 := by
    refine ⟨by decide, ?_, ?_⟩
    · simp [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressFits]
      have := pre.inputFits
      omega
    · intro index indexLt
      have indexZero : index = 0 := by omega
      subst index
      right
      left
      simp [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs.machineArgs, address,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressFits]
      omega
  obtain ⟨physAccess, loadNoMMIO⟩ := pre.machine.dataAccess.load state address 1
    (Agree.weaken (fun _ preserved => preserved.2) agree) allowed (by simp [is_aligned_paddr])
  let inputByte := args.bytes[offset]'offsetBound
  have memoryByte : ∀ (index : Nat)
      (indexLt : index < (leBytes 1 (BitVec.ofNat 8 inputByte.toNat)).length),
      state.mem.get? (address.toNat + index) =
        some (leBytes 1 (BitVec.ofNat 8 inputByte.toNat))[index] := by
    intro index indexLt
    rw [leBytes_length] at indexLt
    have indexZero : index = 0 := by omega
    subst index
    rw [memory]
    simpa [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressFits,
      leBytes, inputByte] using pre.inputMemory offset offsetBound
  exact execute_LOAD_lbu_run state executeAfter immediate (.Regidx 8#5) destination address
    mstatusBits (BitVec.ofNat 8 inputByte.toNat) mstatusState privilegeState mprvZero addressRun
    (is_aligned_vaddr_one _) physAccess loadNoMMIO memoryByte (by simpa [inputByte] using write)

/-! ## First child segment: the length-gate arithmetic -/

theorem hasExactErePrefix_length_add_fetch (state : State)
    (code : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10390)
      0x33#8 0x86#8 0xc4#8 0x00#8 :=
  fetchInstruction state 0x10390 0x33 0x86 0xc4 0x00 code

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
    StepWritesRegister stepNo state 0x10390 x12
      (BitVec.ofNat 64 args.bytes.size + BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)) := by
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10390) := by
    simpa [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs.entryPc, phase] using pre.atEntry
  obtain ⟨-, constant⟩ := pre.preparedConstants phase
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContext pre.machine (Agree.refl state)
  exact decoderRTypeStep pre.machine (Agree.refl state) pre.machine.retiredCounter
    (hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10390 0x33 0x86 0xc4 0x00 12#5 9#5 12#5 .ADD atPc
    (rX_x9_run _ _ (decoderExecuteState_get? pre.inputLength))
    (rX_x12_run _ _ (decoderExecuteState_get? constant)) (wX_x12_run _ _)

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
      Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePost args after ∧
      Agree Entrypoints.ZesuDecodeRaw.decoderPreserved state after ∧
      RetiredCounterPresent after ∧
      after.regs.get? x2 = state.regs.get? x2 ∧
      after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      after.regs.get? x11 = state.regs.get? x11 ∧
      after.mem = state.mem := by
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
  have post : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePost args after := by
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
  have agree : Agree Entrypoints.ZesuDecodeRaw.decoderPreserved state after :=
    afterRegisterWrite_agree_of
      (by simp [Entrypoints.ZesuDecodeRaw.decoderPreserved, platformPreserved])
      (by simp [Entrypoints.ZesuDecodeRaw.decoderPreserved, platformPreserved])
      (by simp [Entrypoints.ZesuDecodeRaw.decoderPreserved, platformPreserved])
      (by simp [Entrypoints.ZesuDecodeRaw.decoderPreserved, platformPreserved])
      (by simp [Entrypoints.ZesuDecodeRaw.decoderPreserved, platformPreserved])
  have inputPointer : after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simpa [after, result, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using pre.inputPointer
  have inputLength : after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    simpa [after, result, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using pre.inputLength
  have stackFrame : after.regs.get? x2 = state.regs.get? x2 := by
    simp [after, result, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have globals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simpa [after, result, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using pre.globalsValue
  have x11 : after.regs.get? x11 = state.regs.get? x11 := by
    simp [after, result, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  exact ⟨after, trace, post, agree,
    afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10390) retired x12 result,
    stackFrame, inputPointer, inputLength, globals, x11, rfl⟩

/-! ## Second child segment: reading and assembling the four-byte prefix -/

theorem hasExactErePrefix_prefix_first_lbu_step (stepNo : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args state)
    (phase : args.phase = .prefixBytes) :
    StepWritesRegister stepNo state 0x10398 x10
      (BitVec.ofNat 64 (args.bytes[1]'(by
        have := pre.prefixExists phase
        omega)).toNat) := by
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10398) := by
    simpa [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs.entryPc, phase] using pre.atEntry
  have pcIn := hasExactErePrefix_body_fetch_classification 0x10398
    (by simp [hasExactErePrefixBodyPcs])
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine (Agree.refl state)
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
    refine ⟨by decide, ?_, ?_⟩
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
    pre.machine.dataAccess.load executeState address 1
      (Agree.weaken (fun _ preserved => preserved.2) executeAgree) allowed
      (by simp [is_aligned_paddr])
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
  have readMemory : Runs (vmem_read (.Regidx 8#5) (sign_extend (m := 64) 1#12) 1
      (MemoryAccessType.Load mem_payload.Data) false false false) executeState executeState
      (.Ok (BitVec.ofNat 8 inputByte.toNat)) := by
    have hread := mem_read_load_run executeState address mstatusBits
      (leBytes 1 (BitVec.ofNat 8 inputByte.toNat)) mstatusAtExecute privilegeAtExecute mprvZero
      memoryByte physAccess loadNoMMIO
    rw [show leWord (leBytes 1 (BitVec.ofNat 8 inputByte.toNat)) = BitVec.ofNat 8 inputByte.toNat
      from by simpa using leWord_leBytes 1 (BitVec.ofNat 8 inputByte.toNat)] at hread
    exact vmem_read_byte_run executeState (.Regidx 8#5) (sign_extend (m := 64) 1#12) address
      mstatusBits (BitVec.ofNat 8 inputByte.toNat) mstatusAtExecute privilegeAtExecute mprvZero
      addressRun (is_aligned_vaddr_one _) hread
  exact decoderLoadStep pre.machine (Agree.refl state) pre.machine.retiredCounter
    (hasExactErePrefix_programImage_of_codeIntact pre.code) stepNo 0x10398 0x03 0x45 0x14 0x00
    1#12 8#5 10#5 true 1 (BitVec.ofNat 8 inputByte.toNat) atPc readMemory
    (by
      have zeroExtend : extend_value true (BitVec.ofNat 8 inputByte.toNat) =
          BitVec.ofNat 64 inputByte.toNat := by
        apply BitVec.eq_of_toNat_eq
        simp [extend_value, zero_extend, Sail.BitVec.zeroExtend]
      rw [zeroExtend]
      exact wX_x10_run executeState (BitVec.ofNat 64 inputByte.toNat))

theorem hasExactErePrefix_prefix_second_lbu_step (stepNo : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (baseState state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args baseState)
    (phase : args.phase = .prefixBytes)
    (agree : Agree platformPreserved baseState state)
    (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1039c))
    (inputPointer : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)) :
    StepWritesRegister stepNo state 0x1039c x12
      (BitVec.ofNat 64 (args.bytes[0]'(by
        have := pre.prefixExists phase
        omega)).toNat) := by
  have pcIn := hasExactErePrefix_body_fetch_classification 0x1039c
    (by simp [hasExactErePrefixBodyPcs])
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
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
    refine ⟨by decide, ?_, ?_⟩
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
    pre.machine.dataAccess.load executeState address 1
      (Agree.weaken (fun _ preserved => preserved.2) executeAgree) allowed
      (by simp [is_aligned_paddr])
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
  have readMemory : Runs (vmem_read (.Regidx 8#5) (sign_extend (m := 64) 0#12) 1
      (MemoryAccessType.Load mem_payload.Data) false false false) executeState executeState
      (.Ok (BitVec.ofNat 8 inputByte.toNat)) := by
    have hread := mem_read_load_run executeState address mstatusBits
      (leBytes 1 (BitVec.ofNat 8 inputByte.toNat)) mstatusAtExecute privilegeAtExecute mprvZero
      memoryByte physAccess loadNoMMIO
    rw [show leWord (leBytes 1 (BitVec.ofNat 8 inputByte.toNat)) = BitVec.ofNat 8 inputByte.toNat
      from by simpa using leWord_leBytes 1 (BitVec.ofNat 8 inputByte.toNat)] at hread
    exact vmem_read_byte_run executeState (.Regidx 8#5) (sign_extend (m := 64) 0#12) address
      mstatusBits (BitVec.ofNat 8 inputByte.toNat) mstatusAtExecute privilegeAtExecute mprvZero
      addressRun (is_aligned_vaddr_one _) hread
  exact decoderLoadStep pre.machine agree retiredPresent code stepNo 0x1039c 0x03 0x46 0x04 0x00
    0#12 8#5 12#5 true 1 (BitVec.ofNat 8 inputByte.toNat) atPc readMemory
    (by
      have zeroExtend : extend_value true (BitVec.ofNat 8 inputByte.toNat) =
          BitVec.ofNat 64 inputByte.toNat := by
        apply BitVec.eq_of_toNat_eq
        simp [extend_value, zero_extend, Sail.BitVec.zeroExtend]
      rw [zeroExtend]
      exact wX_x12_run executeState (BitVec.ofNat 64 inputByte.toNat))

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

theorem hasExactErePrefix_prefix_third_lbu_step (stepNo : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (baseState state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args baseState)
    (phase : args.phase = .prefixBytes)
    (agree : Agree platformPreserved baseState state)
    (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103a0))
    (inputPointer : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)) :
    StepWritesRegister stepNo state 0x103a0 x14
      (BitVec.ofNat 64 (args.bytes[2]'(by
        have := pre.prefixExists phase
        omega)).toNat) := by
  have pcIn := hasExactErePrefix_body_fetch_classification 0x103a0
    (by simp [hasExactErePrefixBodyPcs])
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103a0) 0x03#8 0x47#8 0x24#8 0x00#8 :=
    fetchInstruction state 0x103a0 0x03 0x47 0x24 0x00 code
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  have base : BaseInstructionEncoding 0x03#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x03#8 0x47#8 0x24#8 0x00#8 =
      (0x00244703 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x03#8 0x47#8 0x24#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (2#12, .Regidx 8#5, .Regidx 14#5, true, 1)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103a0)
  have offsetBound : 2 < args.bytes.size := by
    have := pre.prefixExists phase
    omega
  have addressFits : args.inputBase + 2 < 2 ^ 64 := by
    have := pre.inputFits
    omega
  have inputAtExecute : executeState.regs.get? x8 =
      some (BitVec.ofNat 64 args.inputBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, inputPointer]
  have executeAgree : Agree platformPreserved baseState executeState :=
    Agree.trans agree (agree_decoderExecuteState state (BitVec.ofNat 64 0x103a0))
  have executeMemory : executeState.mem = baseState.mem := memory
  let inputByte := args.bytes[2]'offsetBound
  let loadedValue := BitVec.ofNat 64 inputByte.toNat
  have zeroExtend : zero_extend (m := 64) (BitVec.ofNat 8 inputByte.toNat) = loadedValue := by
    apply BitVec.eq_of_toNat_eq
    simp [zero_extend, Sail.BitVec.zeroExtend, loadedValue]
  have write : Runs (wX_bits (.Regidx 14#5)
      (zero_extend (m := 64) (BitVec.ofNat 8 inputByte.toNat))) executeState
      { executeState with regs := executeState.regs.insert x14 loadedValue } () := by
    simpa only [zeroExtend] using
      wX_x14_run executeState (zero_extend (m := 64) (BitVec.ofNat 8 inputByte.toNat))
  have immediateValue : sign_extend (m := 64) 2#12 = BitVec.ofNat 64 2 := by decide
  have execute : Runs (execute (.LOAD (2#12, .Regidx 8#5, .Regidx 14#5, true, 1)))
      executeState { executeState with regs := executeState.regs.insert x14 loadedValue }
      (.Retire_Success ()) := by
    change Runs (execute_LOAD 2#12 (.Regidx 8#5) (.Regidx 14#5) true 1) _ _ _
    exact decoderInputLbuExecute args baseState executeState _ pre 2 offsetBound addressFits 2#12
      immediateValue (.Regidx 14#5) executeAgree executeMemory inputAtExecute write
  exact decoderRegisterWriteStep pre.machine agree retiredPresent stepNo (BitVec.ofNat 64 0x103a0)
    pcIn atPc 0x03#8 0x47#8 0x24#8 0x00#8 (.LOAD (2#12, .Regidx 8#5, .Regidx 14#5, true, 1)) x14
    loadedValue fetchBytes base decode (by decide) (by decide) (by decide) (by decide) execute

theorem hasExactErePrefix_prefix_fourth_lbu_step (stepNo : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (baseState state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args baseState)
    (phase : args.phase = .prefixBytes)
    (agree : Agree platformPreserved baseState state)
    (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103a4))
    (inputPointer : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)) :
    StepWritesRegister stepNo state 0x103a4 x15
      (BitVec.ofNat 64 (args.bytes[3]'(by
        have := pre.prefixExists phase
        omega)).toNat) := by
  have pcIn := hasExactErePrefix_body_fetch_classification 0x103a4
    (by simp [hasExactErePrefixBodyPcs])
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103a4) 0x83#8 0x47#8 0x34#8 0x00#8 :=
    fetchInstruction state 0x103a4 0x83 0x47 0x34 0x00 code
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  have base : BaseInstructionEncoding 0x83#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x83#8 0x47#8 0x34#8 0x00#8 =
      (0x00344783 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0x47#8 0x34#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (3#12, .Regidx 8#5, .Regidx 15#5, true, 1)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103a4)
  have offsetBound : 3 < args.bytes.size := pre.prefixExists phase
  have addressFits : args.inputBase + 3 < 2 ^ 64 := by
    have := pre.inputFits
    omega
  have inputAtExecute : executeState.regs.get? x8 =
      some (BitVec.ofNat 64 args.inputBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, inputPointer]
  have executeAgree : Agree platformPreserved baseState executeState :=
    Agree.trans agree (agree_decoderExecuteState state (BitVec.ofNat 64 0x103a4))
  have executeMemory : executeState.mem = baseState.mem := memory
  let inputByte := args.bytes[3]'offsetBound
  let loadedValue := BitVec.ofNat 64 inputByte.toNat
  have zeroExtend : zero_extend (m := 64) (BitVec.ofNat 8 inputByte.toNat) = loadedValue := by
    apply BitVec.eq_of_toNat_eq
    simp [zero_extend, Sail.BitVec.zeroExtend, loadedValue]
  have write : Runs (wX_bits (.Regidx 15#5)
      (zero_extend (m := 64) (BitVec.ofNat 8 inputByte.toNat))) executeState
      { executeState with regs := executeState.regs.insert x15 loadedValue } () := by
    simpa only [zeroExtend] using
      wX_x15_run executeState (zero_extend (m := 64) (BitVec.ofNat 8 inputByte.toNat))
  have immediateValue : sign_extend (m := 64) 3#12 = BitVec.ofNat 64 3 := by decide
  have execute : Runs (execute (.LOAD (3#12, .Regidx 8#5, .Regidx 15#5, true, 1)))
      executeState { executeState with regs := executeState.regs.insert x15 loadedValue }
      (.Retire_Success ()) := by
    change Runs (execute_LOAD 3#12 (.Regidx 8#5) (.Regidx 15#5) true 1) _ _ _
    exact decoderInputLbuExecute args baseState executeState _ pre 3 offsetBound addressFits 3#12
      immediateValue (.Regidx 15#5) executeAgree executeMemory inputAtExecute write
  exact decoderRegisterWriteStep pre.machine agree retiredPresent stepNo (BitVec.ofNat 64 0x103a4)
    pcIn atPc 0x83#8 0x47#8 0x34#8 0x00#8 (.LOAD (3#12, .Regidx 8#5, .Regidx 15#5, true, 1)) x15
    loadedValue fetchBytes base decode (by decide) (by decide) (by decide) (by decide) execute

theorem hasExactErePrefix_prefix_four_lbu_trace (fromStep : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args state)
    (phase : args.phase = .prefixBytes) :
    ∃ after, Trace fromStep 4 state after := by
  obtain ⟨retired1, first⟩ := hasExactErePrefix_prefix_first_lbu_step fromStep args state pre phase
  let byte1 := args.bytes[1]'(by have := pre.prefixExists phase; omega)
  let after1 := afterRegisterWrite state (BitVec.ofNat 64 0x10398) retired1 x10
    (BitVec.ofNat 64 byte1.toNat)
  have agree1 : Agree platformPreserved state after1 :=
    afterRegisterWrite_agree (by simp [platformPreserved])
  have atSecond : after1.regs.get? PC = some (BitVec.ofNat 64 0x1039c) := by
    simpa [after1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10398) retired1 x10
      (BitVec.ofNat 64 byte1.toNat)
  have input1 : after1.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [after1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      pre.inputPointer]
  obtain ⟨retired2, second⟩ := hasExactErePrefix_prefix_second_lbu_step (fromStep + 1)
    args state after1 pre phase agree1 rfl
    (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10398) retired1 x10
      (BitVec.ofNat 64 byte1.toNat)) atSecond input1
  let byte0 := args.bytes[0]'(by have := pre.prefixExists phase; omega)
  let after2 := afterRegisterWrite after1 (BitVec.ofNat 64 0x1039c) retired2 x12
    (BitVec.ofNat 64 byte0.toNat)
  have agree2 : Agree platformPreserved state after2 :=
    Agree.trans agree1 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have atThird : after2.regs.get? PC = some (BitVec.ofNat 64 0x103a0) := by
    simpa [after2] using afterRegisterWrite_pc after1 (BitVec.ofNat 64 0x1039c) retired2 x12
      (BitVec.ofNat 64 byte0.toNat)
  have input2 : after2.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [after2, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      input1]
  obtain ⟨retired3, third⟩ := hasExactErePrefix_prefix_third_lbu_step (fromStep + 2)
    args state after2 pre phase agree2 rfl
    (afterRegisterWrite_retired_present after1 (BitVec.ofNat 64 0x1039c) retired2 x12
      (BitVec.ofNat 64 byte0.toNat)) atThird input2
  let byte2 := args.bytes[2]'(by have := pre.prefixExists phase; omega)
  let after3 := afterRegisterWrite after2 (BitVec.ofNat 64 0x103a0) retired3 x14
    (BitVec.ofNat 64 byte2.toNat)
  have agree3 : Agree platformPreserved state after3 :=
    Agree.trans agree2 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have atFourth : after3.regs.get? PC = some (BitVec.ofNat 64 0x103a4) := by
    simpa [after3] using afterRegisterWrite_pc after2 (BitVec.ofNat 64 0x103a0) retired3 x14
      (BitVec.ofNat 64 byte2.toNat)
  have input3 : after3.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [after3, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      input2]
  obtain ⟨retired4, fourth⟩ := hasExactErePrefix_prefix_fourth_lbu_step (fromStep + 3)
    args state after3 pre phase agree3 rfl
    (afterRegisterWrite_retired_present after2 (BitVec.ofNat 64 0x103a0) retired3 x14
      (BitVec.ofNat 64 byte2.toNat)) atFourth input3
  let byte3 := args.bytes[3]'(pre.prefixExists phase)
  let after4 := afterRegisterWrite after3 (BitVec.ofNat 64 0x103a4) retired4 x15
    (BitVec.ofNat 64 byte3.toNat)
  refine ⟨after4, ?_⟩
  refine Trace.step fromStep 3 state after1 after4 (by simpa [after1, byte1] using first) ?_
  refine Trace.step (fromStep + 1) 2 after1 after2 after4
    (by simpa [after1, after2, byte0] using second) ?_
  refine Trace.step (fromStep + 2) 1 after2 after3 after4
    (by simpa [after2, after3, byte2] using third) ?_
  exact Trace.one (fromStep + 3) after3 after4 (by simpa [after3, after4, byte3] using fourth)

section AssemblySteps

/- Every step below assembles the four loaded bytes into one word, so they all run against the
same decoder preamble: a `state` agreeing with `baseState` on the platform registers, sharing its
memory, and carrying a retired counter. Declared once here; `include` puts these back into each
signature in exactly this order. -/
variable (stepNo : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (baseState state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args baseState)
    (agree : Agree platformPreserved baseState state)
    (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)

include pre agree memory retiredPresent

theorem hasExactErePrefix_prefix_low_byte_shift_step
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103a8))
    (source : BitVec 64) (sourceRead : state.regs.get? x10 = some source) :
    StepWritesRegister stepNo state 0x103a8 x10
      (Sail.shift_bits_left source
        (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderShiftIopStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x103a8 0x13 0x15 0x85 0x00 8#6 10#5 10#5 .SLLI atPc
    (rX_x10_run _ _ (decoderExecuteState_get? sourceRead)) (wX_x10_run _ _)

theorem hasExactErePrefix_prefix_low_half_or_step
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103ac))
    (highByte lowByte : BitVec 64)
    (highRead : state.regs.get? x10 = some highByte)
    (lowRead : state.regs.get? x12 = some lowByte) :
    StepWritesRegister stepNo state 0x103ac x10 (highByte ||| lowByte) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderRTypeStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x103ac 0x33 0x65 0xc5 0x00 12#5 10#5 10#5 .OR atPc
    (rX_x10_run _ _ (decoderExecuteState_get? highRead))
    (rX_x12_run _ _ (decoderExecuteState_get? lowRead)) (wX_x10_run _ _)

theorem hasExactErePrefix_prefix_length_sub_step
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103b0))
    (length : BitVec 64) (lengthRead : state.regs.get? x9 = some length) :
    StepWritesRegister stepNo state 0x103b0 x13 (iTypeResult .ADDI 0xffc#12 length) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderITypeStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x103b0 0x93 0x86 0xc4 0xff 0xffc#12 9#5 13#5 .ADDI atPc
    (rX_x9_run _ _ (decoderExecuteState_get? lengthRead)) (wX_x13_run _ _)

theorem hasExactErePrefix_prefix_byte2_shift_step
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103b4))
    (source : BitVec 64) (sourceRead : state.regs.get? x14 = some source) :
    StepWritesRegister stepNo state 0x103b4 x14
      (Sail.shift_bits_left source
        (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderShiftIopStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x103b4 0x13 0x17 0x07 0x01 16#6 14#5 14#5 .SLLI atPc
    (rX_x14_run _ _ (decoderExecuteState_get? sourceRead)) (wX_x14_run _ _)

theorem hasExactErePrefix_prefix_byte3_shift_step
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103b8))
    (source : BitVec 64) (sourceRead : state.regs.get? x15 = some source) :
    StepWritesRegister stepNo state 0x103b8 x15
      (Sail.shift_bits_left source
        (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderShiftIopStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x103b8 0x93 0x97 0x87 0x01 24#6 15#5 15#5 .SLLI atPc
    (rX_x15_run _ _ (decoderExecuteState_get? sourceRead)) (wX_x15_run _ _)

theorem hasExactErePrefix_prefix_high_half_or_step
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103bc))
    (highByte2 highByte3 : BitVec 64)
    (byte2Read : state.regs.get? x14 = some highByte2)
    (byte3Read : state.regs.get? x15 = some highByte3) :
    StepWritesRegister stepNo state 0x103bc x14 (highByte3 ||| highByte2) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderRTypeStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x103bc 0x33 0xe7 0xe7 0x00 14#5 15#5 14#5 .OR atPc
    (rX_x15_run _ _ (decoderExecuteState_get? byte3Read))
    (rX_x14_run _ _ (decoderExecuteState_get? byte2Read)) (wX_x14_run _ _)

end AssemblySteps

theorem prefixLowAssemblyValue (byte0 byte1 : BitVec 8) :
    Sail.shift_bits_left (BitVec.ofNat 64 byte1.toNat)
          (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) |||
        BitVec.ofNat 64 byte0.toNat =
      BitVec.ofNat 64 (byte0.toNat + byte1.toNat * 2 ^ 8) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_mul]
  have byte0Value : BitVec.ofNat 64 byte0.toNat = zero_extend (m := 64) byte0 := by
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
    exact BitVec.ofNat_toNat 64 byte0
  have byte1Value : BitVec.ofNat 64 byte1.toNat = zero_extend (m := 64) byte1 := by
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
    exact BitVec.ofNat_toNat 64 byte1
  rw [byte0Value, byte1Value]
  have amount : Sail.BitVec.extractLsb 8#6
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0 = 8#6 := by decide
  rw [amount]
  simp only [Sail.shift_bits_left, zero_extend, Sail.BitVec.zeroExtend]
  bv_decide

theorem prefixHighAssemblyValue (byte2 byte3 : BitVec 8) :
    Sail.shift_bits_left (BitVec.ofNat 64 byte3.toNat)
          (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) |||
        Sail.shift_bits_left (BitVec.ofNat 64 byte2.toNat)
          (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) =
      BitVec.ofNat 64 (byte2.toNat * 2 ^ 16 + byte3.toNat * 2 ^ 24) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_mul]
  have byte2Value : BitVec.ofNat 64 byte2.toNat = zero_extend (m := 64) byte2 := by
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
    exact BitVec.ofNat_toNat 64 byte2
  have byte3Value : BitVec.ofNat 64 byte3.toNat = zero_extend (m := 64) byte3 := by
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
    exact BitVec.ofNat_toNat 64 byte3
  rw [byte2Value, byte3Value]
  have amount16 : Sail.BitVec.extractLsb 16#6
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0 = 16#6 := by decide
  have amount24 : Sail.BitVec.extractLsb 24#6
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0 = 24#6 := by decide
  rw [amount16, amount24]
  simp only [Sail.shift_bits_left, zero_extend, Sail.BitVec.zeroExtend]
  bv_decide

theorem prefixHalvesAssemblyValue (byte0 byte1 byte2 byte3 : BitVec 8) :
    BitVec.ofNat 64 (byte2.toNat * 2 ^ 16 + byte3.toNat * 2 ^ 24) |||
        BitVec.ofNat 64 (byte0.toNat + byte1.toNat * 2 ^ 8) =
      BitVec.ofNat 64 (byte0.toNat + byte1.toNat * 2 ^ 8 +
        byte2.toNat * 2 ^ 16 + byte3.toNat * 2 ^ 24) := by
  simp only [BitVec.ofNat_add, BitVec.ofNat_mul]
  have byte0Value : BitVec.ofNat 64 byte0.toNat = zero_extend (m := 64) byte0 := by
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
    exact BitVec.ofNat_toNat 64 byte0
  have byte1Value : BitVec.ofNat 64 byte1.toNat = zero_extend (m := 64) byte1 := by
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
    exact BitVec.ofNat_toNat 64 byte1
  have byte2Value : BitVec.ofNat 64 byte2.toNat = zero_extend (m := 64) byte2 := by
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
    exact BitVec.ofNat_toNat 64 byte2
  have byte3Value : BitVec.ofNat 64 byte3.toNat = zero_extend (m := 64) byte3 := by
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth]
    exact BitVec.ofNat_toNat 64 byte3
  rw [byte0Value, byte1Value, byte2Value, byte3Value]
  simp only [zero_extend, Sail.BitVec.zeroExtend]
  bv_decide

theorem prefixLengthSubValue (length : Nat) (lower : 4 ≤ length) (upper : length < 2 ^ 64) :
    iTypeResult .ADDI 0xffc#12 (BitVec.ofNat 64 length) =
      BitVec.ofNat 64 (length - 4) := by
  unfold iTypeResult
  have immediate : sign_extend (m := 64) 0xffc#12 = BitVec.ofNat 64 (2 ^ 64 - 4) := by decide
  simp only [immediate]
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem byteArrayGetBang_eq_get (bytes : ByteArray) (index : Nat)
    (inBounds : index < bytes.size) : bytes.get! index = bytes[index] := by
  cases bytes with
  | mk data =>
    exact getElem!_pos data index inBounds

theorem hasExactErePrefix_prefix_segment (fromStep : Nat)
    (args : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs) (state : State)
    (pre : Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePre args state)
    (phase : args.phase = .prefixBytes) :
    ∃ after,
      FunctionTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
        (functionInstanceExitPred
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
        fromStep 10 state after ∧
      Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePost args after ∧
      Agree Entrypoints.ZesuDecodeRaw.decoderPreserved state after ∧
      RetiredCounterPresent after ∧
      after.regs.get? x2 = state.regs.get? x2 ∧
      after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      after.mem = state.mem := by
  have bound0 : 0 < args.bytes.size := by have := pre.prefixExists phase; omega
  have bound1 : 1 < args.bytes.size := by have := pre.prefixExists phase; omega
  have bound2 : 2 < args.bytes.size := by have := pre.prefixExists phase; omega
  have bound3 : 3 < args.bytes.size := pre.prefixExists phase
  let byte0 := args.bytes[0]'bound0
  let byte1 := args.bytes[1]'bound1
  let byte2 := args.bytes[2]'bound2
  let byte3 := args.bytes[3]'bound3
  let value0 := BitVec.ofNat 64 byte0.toNat
  let value1 := BitVec.ofNat 64 byte1.toNat
  let value2 := BitVec.ofNat 64 byte2.toNat
  let value3 := BitVec.ofNat 64 byte3.toNat
  let lowShift := Sail.shift_bits_left value1
    (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let lowHalf := lowShift ||| value0
  let lengthValue := BitVec.ofNat 64 args.bytes.size
  let lengthMinusFour := iTypeResult .ADDI 0xffc#12 lengthValue
  let highShift2 := Sail.shift_bits_left value2
    (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let highShift3 := Sail.shift_bits_left value3
    (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let highHalf := highShift3 ||| highShift2
  obtain ⟨r1, run1⟩ := hasExactErePrefix_prefix_first_lbu_step fromStep args state pre phase
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x10398) r1 x10 value1
  have agree1 : Agree platformPreserved state s1 :=
    afterRegisterWrite_agree (by simp [platformPreserved])
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x1039c) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10398) r1 x10 value1
  have input1 : s1.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [s1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      pre.inputPointer]
  obtain ⟨r2, run2⟩ := hasExactErePrefix_prefix_second_lbu_step (fromStep + 1)
    args state s1 pre phase agree1 rfl
    (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10398) r1 x10 value1) pc1 input1
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x1039c) r2 x12 value0
  have agree2 : Agree platformPreserved state s2 :=
    Agree.trans agree1 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x103a0) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x1039c) r2 x12 value0
  have input2 : s2.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [s2, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, input1]
  obtain ⟨r3, run3⟩ := hasExactErePrefix_prefix_third_lbu_step (fromStep + 2)
    args state s2 pre phase agree2 rfl
    (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x1039c) r2 x12 value0) pc2 input2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x103a0) r3 x14 value2
  have agree3 : Agree platformPreserved state s3 :=
    Agree.trans agree2 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x103a4) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x103a0) r3 x14 value2
  have input3 : s3.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [s3, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, input2]
  obtain ⟨r4, run4⟩ := hasExactErePrefix_prefix_fourth_lbu_step (fromStep + 3)
    args state s3 pre phase agree3 rfl
    (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x103a0) r3 x14 value2) pc3 input3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x103a4) r4 x15 value3
  have agree4 : Agree platformPreserved state s4 :=
    Agree.trans agree3 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x103a8) := by
    simpa [s4] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x103a4) r4 x15 value3
  have value1At4 : s4.regs.get? x10 = some value1 := by
    simp [s4, s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  obtain ⟨r5, run5⟩ := hasExactErePrefix_prefix_low_byte_shift_step (fromStep + 4)
    args state s4 pre agree4 rfl
    (afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x103a4) r4 x15 value3)
    pc4 value1 value1At4
  let s5 := afterRegisterWrite s4 (BitVec.ofNat 64 0x103a8) r5 x10 lowShift
  have agree5 : Agree platformPreserved state s5 :=
    Agree.trans agree4 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc5 : s5.regs.get? PC = some (BitVec.ofNat 64 0x103ac) := by
    simpa [s5] using afterRegisterWrite_pc s4 (BitVec.ofNat 64 0x103a8) r5 x10 lowShift
  have lowShiftAt5 : s5.regs.get? x10 = some lowShift := by
    simp [s5, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have value0At5 : s5.regs.get? x12 = some value0 := by
    simp [s5, s4, s3, s2, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  obtain ⟨r6, run6⟩ := hasExactErePrefix_prefix_low_half_or_step (fromStep + 5)
    args state s5 pre agree5 rfl
    (afterRegisterWrite_retired_present s4 (BitVec.ofNat 64 0x103a8) r5 x10 lowShift)
    pc5 lowShift value0 lowShiftAt5 value0At5
  let s6 := afterRegisterWrite s5 (BitVec.ofNat 64 0x103ac) r6 x10 lowHalf
  have agree6 : Agree platformPreserved state s6 :=
    Agree.trans agree5 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc6 : s6.regs.get? PC = some (BitVec.ofNat 64 0x103b0) := by
    simpa [s6] using afterRegisterWrite_pc s5 (BitVec.ofNat 64 0x103ac) r6 x10 lowHalf
  have lengthAt6 : s6.regs.get? x9 = some lengthValue := by
    simp [s6, s5, s4, s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, lengthValue, pre.inputLength]
  obtain ⟨r7, run7⟩ := hasExactErePrefix_prefix_length_sub_step (fromStep + 6)
    args state s6 pre agree6 rfl
    (afterRegisterWrite_retired_present s5 (BitVec.ofNat 64 0x103ac) r6 x10 lowHalf)
    pc6 lengthValue lengthAt6
  let s7 := afterRegisterWrite s6 (BitVec.ofNat 64 0x103b0) r7 x13 lengthMinusFour
  have agree7 : Agree platformPreserved state s7 :=
    Agree.trans agree6 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc7 : s7.regs.get? PC = some (BitVec.ofNat 64 0x103b4) := by
    simpa [s7] using afterRegisterWrite_pc s6 (BitVec.ofNat 64 0x103b0) r7 x13 lengthMinusFour
  have value2At7 : s7.regs.get? x14 = some value2 := by
    simp [s7, s6, s5, s4, s3, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  obtain ⟨r8, run8⟩ := hasExactErePrefix_prefix_byte2_shift_step (fromStep + 7)
    args state s7 pre agree7 rfl
    (afterRegisterWrite_retired_present s6 (BitVec.ofNat 64 0x103b0) r7 x13 lengthMinusFour)
    pc7 value2 value2At7
  let s8 := afterRegisterWrite s7 (BitVec.ofNat 64 0x103b4) r8 x14 highShift2
  have agree8 : Agree platformPreserved state s8 :=
    Agree.trans agree7 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc8 : s8.regs.get? PC = some (BitVec.ofNat 64 0x103b8) := by
    simpa [s8] using afterRegisterWrite_pc s7 (BitVec.ofNat 64 0x103b4) r8 x14 highShift2
  have value3At8 : s8.regs.get? x15 = some value3 := by
    simp [s8, s7, s6, s5, s4, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  obtain ⟨r9, run9⟩ := hasExactErePrefix_prefix_byte3_shift_step (fromStep + 8)
    args state s8 pre agree8 rfl
    (afterRegisterWrite_retired_present s7 (BitVec.ofNat 64 0x103b4) r8 x14 highShift2)
    pc8 value3 value3At8
  let s9 := afterRegisterWrite s8 (BitVec.ofNat 64 0x103b8) r9 x15 highShift3
  have agree9 : Agree platformPreserved state s9 :=
    Agree.trans agree8 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc9 : s9.regs.get? PC = some (BitVec.ofNat 64 0x103bc) := by
    simpa [s9] using afterRegisterWrite_pc s8 (BitVec.ofNat 64 0x103b8) r9 x15 highShift3
  have high2At9 : s9.regs.get? x14 = some highShift2 := by
    simp [s9, s8, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have high3At9 : s9.regs.get? x15 = some highShift3 := by
    simp [s9, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r10, run10⟩ := hasExactErePrefix_prefix_high_half_or_step (fromStep + 9)
    args state s9 pre agree9 rfl
    (afterRegisterWrite_retired_present s8 (BitVec.ofNat 64 0x103b8) r9 x15 highShift3)
    pc9 highShift2 highShift3 high2At9 high3At9
  let s10 := afterRegisterWrite s9 (BitVec.ofNat 64 0x103bc) r10 x14 highHalf
  have agree10Platform : Agree platformPreserved state s10 :=
    Agree.trans agree9 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have agree10 : Agree Entrypoints.ZesuDecodeRaw.decoderPreserved state s10 :=
    Agree.weaken (fun _ preserved => preserved.2) agree10Platform
  have counter10 := afterRegisterWrite_retired_present s9 (BitVec.ofNat 64 0x103bc)
    r10 x14 highHalf
  have pc10 : s10.regs.get? PC = some (BitVec.ofNat 64 0x103c0) := by
    simpa [s10] using afterRegisterWrite_pc s9 (BitVec.ofNat 64 0x103bc) r10 x14 highHalf
  have trace : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
      (functionInstanceExitPred
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
      fromStep 10 state s10 := by
    have c0 := hasExactErePrefix_body_classification 0x10398 (by simp [hasExactErePrefixBodyPcs])
    have c1 := hasExactErePrefix_body_classification 0x1039c (by simp [hasExactErePrefixBodyPcs])
    have c2 := hasExactErePrefix_body_classification 0x103a0 (by simp [hasExactErePrefixBodyPcs])
    have c3 := hasExactErePrefix_body_classification 0x103a4 (by simp [hasExactErePrefixBodyPcs])
    have c4 := hasExactErePrefix_body_classification 0x103a8 (by simp [hasExactErePrefixBodyPcs])
    have c5 := hasExactErePrefix_body_classification 0x103ac (by simp [hasExactErePrefixBodyPcs])
    have c6 := hasExactErePrefix_body_classification 0x103b0 (by simp [hasExactErePrefixBodyPcs])
    have c7 := hasExactErePrefix_body_classification 0x103b4 (by simp [hasExactErePrefixBodyPcs])
    have c8 := hasExactErePrefix_body_classification 0x103b8 (by simp [hasExactErePrefixBodyPcs])
    have c9 := hasExactErePrefix_body_classification 0x103bc (by simp [hasExactErePrefixBodyPcs])
    have pc0 : state.regs.get? PC = some (BitVec.ofNat 64 0x10398) := by
      simpa [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineArgs.entryPc, phase] using pre.atEntry
    refine .step fromStep 9 _ state s1 s10 pc0 c0.1 c0.2 (by simpa [s1, value1] using run1) ?_
    refine .step (fromStep + 1) 8 _ s1 s2 s10 pc1 c1.1 c1.2
      (by simpa [s2, value0] using run2) ?_
    refine .step (fromStep + 2) 7 _ s2 s3 s10 pc2 c2.1 c2.2
      (by simpa [s3, value2] using run3) ?_
    refine .step (fromStep + 3) 6 _ s3 s4 s10 pc3 c3.1 c3.2
      (by simpa [s4, value3] using run4) ?_
    refine .step (fromStep + 4) 5 _ s4 s5 s10 pc4 c4.1 c4.2
      (by simpa [s5, lowShift] using run5) ?_
    refine .step (fromStep + 5) 4 _ s5 s6 s10 pc5 c5.1 c5.2
      (by simpa [s6, lowHalf] using run6) ?_
    refine .step (fromStep + 6) 3 _ s6 s7 s10 pc6 c6.1 c6.2
      (by simpa [s7, lengthMinusFour] using run7) ?_
    refine .step (fromStep + 7) 2 _ s7 s8 s10 pc7 c7.1 c7.2
      (by simpa [s8, highShift2] using run8) ?_
    refine .step (fromStep + 8) 1 _ s8 s9 s10 pc8 c8.1 c8.2
      (by simpa [s9, highShift3] using run9) ?_
    refine .step (fromStep + 9) 0 _ s9 s10 s10 pc9 c9.1 c9.2
      (by simpa [s10, highHalf] using run10) ?_
    exact .exitAt (fromStep + 10) s10 (BitVec.ofNat 64 0x103c0) pc10
      Entrypoints.ZesuDecodeRaw.hasExactErePrefixInline_prefix_exit
  have inputPointer10 : s10.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, pre.inputPointer]
  have inputLength10 : s10.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, pre.inputLength]
  have stackFrame10 : s10.regs.get? x2 = state.regs.get? x2 := by
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have globals10 : s10.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simpa [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert] using pre.globalsValue
  refine ⟨s10, trace, ?_, agree10, counter10, stackFrame10, inputPointer10, inputLength10,
    globals10, rfl⟩
  simp only [Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlinePost, phase]
  refine ⟨pc10, ?_, ?_, ?_⟩
  · have stored : s10.regs.get? x10 = some lowHalf := by
      simp [s10, s9, s8, s7, s6, afterRegisterWrite, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert]
    have value : lowHalf = BitVec.ofNat 64
        (Entrypoints.ZesuDecodeRaw.prefixLow16 args.bytes) := by
      dsimp [lowHalf, lowShift, value0, value1, byte0, byte1]
      have assembly := prefixLowAssemblyValue
        (BitVec.ofNat 8 (args.bytes[0]'bound0).toNat)
        (BitVec.ofNat 8 (args.bytes[1]'bound1).toNat)
      have assembly' :
          Sail.shift_bits_left (BitVec.ofNat 64 (args.bytes[1]'bound1).toNat)
                (Sail.BitVec.extractLsb 8#6
                  (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) |||
              BitVec.ofNat 64 (args.bytes[0]'bound0).toNat =
            BitVec.ofNat 64
              ((args.bytes[0]'bound0).toNat + (args.bytes[1]'bound1).toNat * 2 ^ 8) := by
        simpa only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (UInt8.toNat_lt _)] using assembly
      rw [assembly']
      apply congrArg (BitVec.ofNat 64)
      rw [Entrypoints.ZesuDecodeRaw.prefixLow16]
      rw [show args.bytes.get! 0 = args.bytes[0] from byteArrayGetBang_eq_get _ _ bound0]
      rw [show args.bytes.get! 1 = args.bytes[1] from byteArrayGetBang_eq_get _ _ bound1]
    exact value ▸ stored
  · have stored : s10.regs.get? x14 = some highHalf := by
      simp [s10, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
    have value : highHalf = BitVec.ofNat 64
        (Entrypoints.ZesuDecodeRaw.prefixHigh16 args.bytes) := by
      dsimp [highHalf, highShift2, highShift3, value2, value3, byte2, byte3]
      have assembly := prefixHighAssemblyValue
        (BitVec.ofNat 8 (args.bytes[2]'bound2).toNat)
        (BitVec.ofNat 8 (args.bytes[3]'bound3).toNat)
      have assembly' :
          Sail.shift_bits_left (BitVec.ofNat 64 (args.bytes[3]'bound3).toNat)
                (Sail.BitVec.extractLsb 24#6
                  (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) |||
              Sail.shift_bits_left (BitVec.ofNat 64 (args.bytes[2]'bound2).toNat)
                (Sail.BitVec.extractLsb 16#6
                  (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) =
            BitVec.ofNat 64
              ((args.bytes[2]'bound2).toNat * 2 ^ 16 +
                (args.bytes[3]'bound3).toNat * 2 ^ 24) := by
        simpa only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (UInt8.toNat_lt _)] using assembly
      rw [assembly']
      apply congrArg (BitVec.ofNat 64)
      rw [Entrypoints.ZesuDecodeRaw.prefixHigh16]
      rw [show args.bytes.get! 2 = args.bytes[2] from byteArrayGetBang_eq_get _ _ bound2]
      rw [show args.bytes.get! 3 = args.bytes[3] from byteArrayGetBang_eq_get _ _ bound3]
    exact value ▸ stored
  · have stored : s10.regs.get? x13 = some lengthMinusFour := by
      simp [s10, s9, s8, s7, afterRegisterWrite, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert]
    have value : lengthMinusFour = BitVec.ofNat 64 (args.bytes.size - 4) := by
      apply prefixLengthSubValue
      · exact pre.prefixExists phase
      · have := pre.rootInputBound
        omega
    exact value ▸ stored

theorem hasExactErePrefixInlineContract_proved :
    Entrypoints.ZesuDecodeRaw.HasExactErePrefixInlineContract := by
  intro args fromStep before pre
  cases phaseEq : args.phase with
  | lengthGate =>
      obtain ⟨after, trace, post, -, -, -, -, -, -⟩ :=
        hasExactErePrefix_length_segment fromStep args before pre phaseEq
      exact ⟨1, after, by simp [Entrypoints.ZesuDecodeRaw.hasExactErePrefixInlineStepBound],
        trace, post⟩
  | prefixBytes =>
      obtain ⟨after, trace, post, -, -, -, -, -, -⟩ :=
        hasExactErePrefix_prefix_segment fromStep args before pre phaseEq
      exact ⟨10, after, by simp [Entrypoints.ZesuDecodeRaw.hasExactErePrefixInlineStepBound],
        trace, post⟩

end BinaryFv.Zesu.MachineExecution
