import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry
import BinaryFv.RiscV.Instruction.Execute.RegisterOp

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

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def decodeInlineImageWord? (address : Nat) : Option Nat := do
  let byte0 ← Artifacts.programImage.readByte? address
  let byte1 ← Artifacts.programImage.readByte? (address + 1)
  let byte2 ← Artifacts.programImage.readByte? (address + 2)
  let byte3 ← Artifacts.programImage.readByte? (address + 3)
  pure (byte0.toNat + byte1.toNat * 2 ^ 8 + byte2.toNat * 2 ^ 16 + byte3.toNat * 2 ^ 24)

/-- Exactly the 31 words attributed directly to the inlined `decode` instance. Child-owned words
and wrapper-owned continuations are deliberately absent. -/
def decodeInlineOwnedInstructionWords : List (Nat × Nat) :=
  [(0x10308, 0x36010513), (0x1030c, 0x01010593),
    (0x10310, 0x00040613), (0x10314, 0x00048693),
    (0x10318, 0x00000097), (0x1031c, 0x12c080e7),
    (0x10320, 0x6a015503), (0x10324, 0x04051c63),
    (0x10328, 0x02010513), (0x1032c, 0x36010593),
    (0x10330, 0x34000613), (0x10334, 0x00004097),
    (0x10338, 0xb84080e7), (0x10380, 0x06b51e63),
    (0x10384, 0xfff00513), (0x10388, 0x02051513),
    (0x1038c, 0xffc50613), (0x103c4, 0x04a69e63),
    (0x103c8, 0x00440613), (0x103cc, 0x6b010513),
    (0x103d0, 0x01010593), (0x103d4, 0x00000097),
    (0x103d8, 0x070080e7), (0x103dc, 0x02010513),
    (0x103e0, 0x6b010593), (0x103e4, 0x34000613),
    (0x103e8, 0x00004097), (0x103ec, 0xad0080e7),
    (0x103f0, 0x00001537), (0x103f4, 0x00a10533),
    (0x103f8, 0x9f055503)]

theorem decodeInline_owned_instruction_words_pinned :
    ∀ entry ∈ decodeInlineOwnedInstructionWords,
      decodeInlineImageWord? entry.1 = some entry.2 := by
  native_decide

theorem decodeInline_owned_instruction_count :
    decodeInlineOwnedInstructionWords.length = 31 := by
  decide

/-- Every listed instruction lies in the generated execution extent of this compiled instance.
This checks completeness against the proof's confinement predicate independently of DWARF labels. -/
theorem decodeInline_owned_in_execution_region :
    ∀ entry ∈ decodeInlineOwnedInstructionWords,
      functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        (BitVec.ofNat 64 entry.1) := by
  intro entry member
  simp only [decodeInlineOwnedInstructionWords, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide

/-! ## First segment: preparing the initial `decodeRaw` call -/

theorem decodeInline_first_result_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10308) retired x10
          (iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10308) := by
    simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x10308) :=
    decodeInline_owned_in_execution_region (0x10308, 0x36010513)
      (by simp [decodeInlineOwnedInstructionWords])
  have code := hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10308) 0x13#8 0x05#8 0x01#8 0x36#8 :=
    fetchFileInstruction state 0x10308 0x13 0x05 0x01 0x36 code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine (Agree.refl state)
    (BitVec.ofNat 64 0x10308) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x05#8 0x01#8 0x36#8 =
      (0x36010513 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x01#8 0x36#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x360#12, .Regidx 2#5, .Regidx 10#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10308)
  have stackAtExecute : executeState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.stackValue]
  let result := iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase)
  have execute : Runs (execute (.ITYPE (0x360#12, .Regidx 2#5, .Regidx 10#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x10 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x360#12 (.Regidx 2#5) (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x360#12 (.Regidx 2#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 args.stackBase)
      (rX_bits_run_x2 executeState _ stackAtExecute) (wX_x10_run executeState result)
  have baseEncoding : BaseInstructionEncoding 0x13#8 := by
    unfold BaseInstructionEncoding
    decide
  exact decoderRegisterWriteStep pre.machine (Agree.refl state) pre.machine.retiredCounter stepNo
    (BitVec.ofNat 64 0x10308) pcIn atPc 0x13#8 0x05#8 0x01#8 0x36#8
    (.ITYPE (0x360#12, .Regidx 2#5, .Regidx 10#5, .ADDI)) x10 result fetchBytes
    baseEncoding decode (by decide) (by decide) (by decide) (by decide) execute

theorem decodeInline_first_allocator_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree platformPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1030c))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x1030c) retired x11
          (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x1030c) :=
    decodeInline_owned_in_execution_region (0x1030c, 0x01010593)
      (by simp [decodeInlineOwnedInstructionWords])
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1030c) 0x93#8 0x05#8 0x01#8 0x01#8 :=
    fetchFileInstruction state 0x1030c 0x93 0x05 0x01 0x01 code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine agree
    (BitVec.ofNat 64 0x1030c) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x93#8 0x05#8 0x01#8 0x01#8 =
      (0x01010593 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x01#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x010#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1030c)
  have stackAtExecute : executeState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  let result := iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase)
  have execute : Runs (execute (.ITYPE (0x010#12, .Regidx 2#5, .Regidx 11#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x11 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x010#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x010#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI
      (BitVec.ofNat 64 args.stackBase)
      (rX_bits_run_x2 executeState _ stackAtExecute) (wX_x11_run executeState result)
  have baseEncoding : BaseInstructionEncoding 0x93#8 := by
    unfold BaseInstructionEncoding
    decide
  exact decoderRegisterWriteStep pre.machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x1030c) pcIn atPc 0x93#8 0x05#8 0x01#8 0x01#8
    (.ITYPE (0x010#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) x11 result fetchBytes
    baseEncoding decode (by decide) (by decide) (by decide) (by decide) execute

theorem decodeInline_first_input_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree platformPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10310))
    (inputRead : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10310) retired x12
          (iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.inputBase))) false := by
  have pcIn := decodeInline_owned_in_execution_region (0x10310, 0x00040613)
    (by simp [decodeInlineOwnedInstructionWords])
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10310) 0x13#8 0x06#8 0x04#8 0x00#8 :=
    fetchFileInstruction state 0x10310 0x13 0x06 0x04 0x00 code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine agree
    (BitVec.ofNat 64 0x10310) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x06#8 0x04#8 0x00#8 =
      (0x00040613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x04#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x000#12, .Regidx 8#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10310)
  have inputAtExecute : executeState.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, inputRead]
  let result := iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.inputBase)
  have execute : Runs (execute (.ITYPE (0x000#12, .Regidx 8#5, .Regidx 12#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x12 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x000#12 (.Regidx 8#5) (.Regidx 12#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x000#12 (.Regidx 8#5) (.Regidx 12#5) .ADDI
      (BitVec.ofNat 64 args.inputBase)
      (rX_x8_run executeState _ inputAtExecute) (wX_x12_run executeState result)
  have baseEncoding : BaseInstructionEncoding 0x13#8 := by
    unfold BaseInstructionEncoding
    decide
  exact decoderRegisterWriteStep pre.machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10310) pcIn atPc 0x13#8 0x06#8 0x04#8 0x00#8
    (.ITYPE (0x000#12, .Regidx 8#5, .Regidx 12#5, .ADDI)) x12 result fetchBytes
    baseEncoding decode (by decide) (by decide) (by decide) (by decide) execute

theorem decodeInline_first_input_length_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree platformPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10314))
    (lengthRead : state.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10314) retired x13
          (iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.bytes.size))) false := by
  have pcIn := decodeInline_owned_in_execution_region (0x10314, 0x00048693)
    (by simp [decodeInlineOwnedInstructionWords])
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10314) 0x93#8 0x86#8 0x04#8 0x00#8 :=
    fetchFileInstruction state 0x10314 0x93 0x86 0x04 0x00 code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine agree
    (BitVec.ofNat 64 0x10314) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x93#8 0x86#8 0x04#8 0x00#8 =
      (0x00048693 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x86#8 0x04#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x000#12, .Regidx 9#5, .Regidx 13#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10314)
  have lengthAtExecute : executeState.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, lengthRead]
  let result := iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.bytes.size)
  have execute : Runs (execute (.ITYPE (0x000#12, .Regidx 9#5, .Regidx 13#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x13 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x000#12 (.Regidx 9#5) (.Regidx 13#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x000#12 (.Regidx 9#5) (.Regidx 13#5) .ADDI
      (BitVec.ofNat 64 args.bytes.size)
      (rX_x9_run executeState _ lengthAtExecute) (wX_x13_run executeState result)
  have baseEncoding : BaseInstructionEncoding 0x93#8 := by
    unfold BaseInstructionEncoding
    decide
  exact decoderRegisterWriteStep pre.machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10314) pcIn atPc 0x93#8 0x86#8 0x04#8 0x00#8
    (.ITYPE (0x000#12, .Regidx 9#5, .Regidx 13#5, .ADDI)) x13 result fetchBytes
    baseEncoding decode (by decide) (by decide) (by decide) (by decide) execute

theorem decodeInline_first_argument_setup (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ after, Trace fromStep 4 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10318) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
      after.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size) ∧
      Agree platformPreserved state after ∧ after.mem = state.mem ∧
      RetiredCounterPresent after := by
  let firstResult := iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired1, run1⟩ := decodeInline_first_result_pointer_step fromStep args state pre phase
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x10308) retired1 x10 firstResult
  have agree1 : Agree platformPreserved state s1 :=
    afterRegisterWrite_agree (by simp [platformPreserved])
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x1030c) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10308) retired1 x10
      firstResult
  have stack1 : s1.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [s1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      pre.stackValue]
  let allocator := iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired2, run2⟩ := decodeInline_first_allocator_pointer_step (fromStep + 1) args
    state s1 pre agree1 rfl
    (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10308) retired1 x10 firstResult)
    pc1 stack1
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x1030c) retired2 x11 allocator
  have agree2 : Agree platformPreserved state s2 :=
    Agree.trans agree1 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10310) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x1030c) retired2 x11 allocator
  have input2 : s2.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.inputValue]
  let input := iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.inputBase)
  obtain ⟨retired3, run3⟩ := decodeInline_first_input_pointer_step (fromStep + 2) args
    state s2 pre agree2 rfl
    (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x1030c) retired2 x11 allocator)
    pc2 input2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10310) retired3 x12 input
  have agree3 : Agree platformPreserved state s3 :=
    Agree.trans agree2 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10314) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10310) retired3 x12 input
  have length3 : s3.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.lengthValue]
  let length := iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.bytes.size)
  obtain ⟨retired4, run4⟩ := decodeInline_first_input_length_step (fromStep + 3) args
    state s3 pre agree3 rfl
    (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10310) retired3 x12 input)
    pc3 length3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x10314) retired4 x13 length
  have agree4 : Agree platformPreserved state s4 :=
    Agree.trans agree3 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x10318) := by
    simpa [s4] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x10314) retired4 x13 length
  have firstResultEq : firstResult =
      BitVec.ofNat 64 args.firstTemporaryResultBase := by
    simp only [firstResult, iTypeResult, DecodeInlineArgs.firstTemporaryResultBase]
    rw [show sign_extend (0x360#12) = (BitVec.ofNat 64 0x360) by decide,
      ← BitVec.ofNat_add]
  have allocatorEq : allocator = BitVec.ofNat 64 args.allocatorBase := by
    simp only [allocator, iTypeResult, DecodeInlineArgs.allocatorBase]
    rw [show sign_extend (0x010#12) = (BitVec.ofNat 64 0x10) by decide,
      ← BitVec.ofNat_add]
  have inputEq : input = BitVec.ofNat 64 args.inputBase := by
    simp [input, iTypeResult]
    decide
  have lengthEq : length = BitVec.ofNat 64 args.bytes.size := by
    simp [length, iTypeResult]
    decide
  have result4 : s4.regs.get? x10 =
      some (BitVec.ofNat 64 args.firstTemporaryResultBase) := by
    simp [s4, s3, s2, s1, firstResultEq, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have allocator4 : s4.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) := by
    simp [s4, s3, s2, allocatorEq, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have input4 : s4.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [s4, s3, inputEq, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have length4 : s4.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [s4, lengthEq, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  refine ⟨s4, ?_, pc4, result4, allocator4, input4, length4, agree4, rfl,
    afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x10314) retired4 x13 length⟩
  · refine Trace.step fromStep 3 state s1 s4 (by simpa [s1, firstResult] using run1) ?_
    refine Trace.step (fromStep + 1) 2 s1 s2 s4 (by simpa [s2, allocator] using run2) ?_
    refine Trace.step (fromStep + 2) 1 s2 s3 s4 (by simpa [s3, input] using run3) ?_
    exact Trace.one (fromStep + 3) s3 s4 (by simpa [s4, length] using run4)

theorem decodeInline_first_call_page_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree platformPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10318)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10318) retired x1
          (BitVec.ofNat 64 0x10318)) false := by
  have pcIn := decodeInline_owned_in_execution_region (0x10318, 0x00000097)
    (by simp [decodeInlineOwnedInstructionWords])
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10318) 0x97#8 0x00#8 0x00#8 0x00#8 :=
    fetchFileInstruction state 0x10318 0x97 0x00 0x00 0x00 code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine agree
    (BitVec.ofNat 64 0x10318) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x97#8 0x00#8 0x00#8 0x00#8 =
      (0x00000097 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x97#8 0x00#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x00000#20, .Regidx 1#5, .AUIPC)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10318)
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x10318) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (0x00000#20, .Regidx 1#5, .AUIPC)))
      executeState
      { executeState with regs := executeState.regs.insert x1 (BitVec.ofNat 64 0x10318) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_auipc_run executeState _ 0x00000#20 (.Regidx 1#5)
      (BitVec.ofNat 64 0x10318)
    · exact readReg_run _ _ _ pcAtExecute
    · simpa using wX_bits_run_x1 executeState (BitVec.ofNat 64 0x10318)
  have baseEncoding : BaseInstructionEncoding 0x97#8 := by
    unfold BaseInstructionEncoding
    decide
  exact decoderRegisterWriteStep pre.machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10318) pcIn atPc 0x97#8 0x00#8 0x00#8 0x00#8
    (.UTYPE (0x00000#20, .Regidx 1#5, .AUIPC)) x1 (BitVec.ofNat 64 0x10318)
    fetchBytes baseEncoding decode (by decide) (by decide) (by decide) (by decide) execute

theorem decodeInline_first_before_decodeRaw_call (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ beforeCall, Trace fromStep 5 state beforeCall ∧
      beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x1031c) ∧
      beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x10318) ∧
      beforeCall.regs.get? x10 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
      beforeCall.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase) ∧
      beforeCall.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size) ∧
      Agree decoderPreserved state beforeCall ∧ beforeCall.mem = state.mem ∧
      RetiredCounterPresent beforeCall := by
  obtain ⟨afterArgs, argsTrace, argsPc, resultArgs, allocatorArgs, inputArgs, lengthArgs,
    argsAgree, argsMemory, argsRetired⟩ :=
    decodeInline_first_argument_setup fromStep args state pre phase
  obtain ⟨retired, callPageStep⟩ := decodeInline_first_call_page_step (fromStep + 4) args
    state afterArgs pre argsAgree argsMemory argsRetired argsPc
  let beforeCall := afterRegisterWrite afterArgs (BitVec.ofNat 64 0x10318) retired x1
    (BitVec.ofNat 64 0x10318)
  have callPc : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x1031c) := by
    simpa [beforeCall] using afterRegisterWrite_pc afterArgs (BitVec.ofNat 64 0x10318)
      retired x1 (BitVec.ofNat 64 0x10318)
  have returnBase : beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x10318) := by
    simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have resultBefore : beforeCall.regs.get? x10 =
      some (BitVec.ofNat 64 args.firstTemporaryResultBase) := by
    simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resultArgs]
  have allocatorBefore : beforeCall.regs.get? x11 =
      some (BitVec.ofNat 64 args.allocatorBase) := by
    simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, allocatorArgs]
  have inputBefore : beforeCall.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, inputArgs]
  have lengthBefore : beforeCall.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, lengthArgs]
  have callPageAgree : Agree decoderPreserved afterArgs beforeCall := by
    apply afterRegisterWrite_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  have memoryUnchanged : beforeCall.mem = state.mem := by
    change (afterRegisterWrite afterArgs (BitVec.ofNat 64 0x10318) retired x1
      (BitVec.ofNat 64 0x10318)).mem = state.mem
    exact (afterRegisterWrite_mem afterArgs (BitVec.ofNat 64 0x10318) retired x1
      (BitVec.ofNat 64 0x10318)).trans argsMemory
  refine ⟨beforeCall, ?_, callPc, returnBase, resultBefore, allocatorBefore, inputBefore,
    lengthBefore,
    Agree.trans (Agree.weaken (fun _ preserved => preserved.2) argsAgree) callPageAgree,
    memoryUnchanged,
    afterRegisterWrite_retired_present afterArgs (BitVec.ofNat 64 0x10318) retired x1
      (BitVec.ofNat 64 0x10318)⟩
  exact Trace.snoc argsTrace (by simpa [beforeCall] using callPageStep)

def decodeInlineFirstCallAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1031c) (BitVec.ofNat 64 0x10444) x1
      (BitVec.ofNat 64 0x10320))
    (BitVec.ofNat 64 0x10444) retired

theorem decodeInline_first_decodeRaw_call_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1031c))
    (callBase : state.regs.get? x1 = some (BitVec.ofNat 64 0x10318))
    (resultPointer : state.regs.get? x10 =
      some (BitVec.ofNat 64 args.firstTemporaryResultBase))
    (allocatorPointer : state.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase))
    (inputPointer : state.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase))
    (inputLength : state.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size)) :
    ∃ retired,
      Runs (try_step stepNo false) state (decodeInlineFirstCallAfter state retired) false ∧
      (decodeInlineFirstCallAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10444) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x1 =
        some (BitVec.ofNat 64 0x10320) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x10 =
        some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x11 =
        some (BitVec.ofNat 64 args.allocatorBase) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x12 =
        some (BitVec.ofNat 64 args.inputBase) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x13 =
        some (BitVec.ofNat 64 args.bytes.size) ∧
      Agree decoderPreserved state (decodeInlineFirstCallAfter state retired) ∧
      (decodeInlineFirstCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (decodeInlineFirstCallAfter state retired) := by
  have pcIn := decodeInline_owned_in_execution_region (0x1031c, 0x12c080e7)
    (by simp [decodeInlineOwnedInstructionWords])
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1031c) 0xe7#8 0x80#8 0xc0#8 0x12#8 :=
    fetchFileInstruction state 0x1031c 0xe7 0x80 0xc0 0x12 code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree pre.machine agree
    (BitVec.ofNat 64 0x1031c) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree pre.machine.normal agree retiredPresent
  have wordEq : fetchWord 0xe7#8 0x80#8 0xc0#8 0x12#8 =
      (0x12c080e7 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xe7#8 0x80#8 0xc0#8 0x12#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0x12c#12, .Regidx 1#5, .Regidx 1#5)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1031c)
  have executeAgree : Agree decoderPreserved baseState executeState :=
    Agree.trans agree
      (Agree.weaken (fun _ preserved => preserved.2)
        (agree_stepPremiseState state (BitVec.ofNat 64 0x1031c)))
  have helpElp : Runs (update_elp_state (.Regidx 1#5)) executeState executeState () :=
    pre.machine.landingPad executeState (.Regidx 1#5) trivial executeAgree
  have linkRead : executeState.regs.get? nextPC = some (BitVec.ofNat 64 0x10320) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x1031c) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp
    decide
  have sourceRead : executeState.regs.get? x1 = some (BitVec.ofNat 64 0x10318) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, callBase]
  have targetEq : Sail.BitVec.update
      ((BitVec.ofNat 64 0x10318) + sign_extend (m := 64) (0x12c#12)) 0 0#1 =
      BitVec.ofNat 64 0x10444 := by decide
  have hwrite : Runs (wX_bits (.Regidx 1#5) (BitVec.ofNat 64 0x10320))
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x1031c) (BitVec.ofNat 64 0x10444))
      (callLinkState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x1031c) (BitVec.ofNat 64 0x10444) x1
        (BitVec.ofNat 64 0x10320)) () := by
    exact wX_bits_run_x1 _ _
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      baseState.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := pre.machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match misaRead : baseState.regs.get? misa with
    | none =>
        simp [misaRead] at normalMisa
    | some misaBits =>
        exact ⟨misaBits, rfl, by
          simpa [misaRead] using normalMisa⟩
  have misaState : state.regs.get? misa = some misaBits :=
    (agree misa (by simp [decoderPreserved, platformPreserved])).trans misaRead
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x1031c)
    misaBits misaState
  have callRun := tryStepJalrCallRetires stepNo state
    (BitVec.ofNat 64 0x1031c) (BitVec.ofNat 64 0x10318) retired
    (BitVec.ofNat 64 0x10320) (0x12c#12) (.Regidx 1#5) (.Regidx 1#5) x1
    (BitVec.ofNat 64 0x10320) inhibit config 0xe7#8 0x80#8 0xc0#8 0x12#8
    (_get_Misa_C misaBits == 1#1)
    (by simpa [targetEq] using hwrite) (by decide) (by decide) (by decide) (by decide)
    fetch noMMIO fetchBytes interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected helpElp
    (get_next_pc_run executeState _ linkRead) (rX_bits_run_x1 executeState _ sourceRead)
    (by decide) zca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  have run : Runs (try_step stepNo false) state
      (decodeInlineFirstCallAfter state retired) false := by
    simpa [decodeInlineFirstCallAfter, targetEq] using callRun
  have pcAfter : (decodeInlineFirstCallAfter state retired).regs.get? PC =
      some (BitVec.ofNat 64 0x10444) := by
    simp [decodeInlineFirstCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  have linkAfter : (decodeInlineFirstCallAfter state retired).regs.get? x1 =
      some (BitVec.ofNat 64 0x10320) := by
    apply tryStepControlFlowAfterRetired_preserves_register
    · exact callLinkState_link _ _ _ x1 (BitVec.ofNat 64 0x10320)
    · decide
    · decide
  have callAgree : Agree decoderPreserved state (decodeInlineFirstCallAfter state retired) := by
    apply jalrCallAfterRetired_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  have callMemory : (decodeInlineFirstCallAfter state retired).mem = state.mem :=
    jalrCallAfterRetired_mem _ _ _ _ _ _
  have preserveGeneral (register : Register) (notLink : register ≠ x1)
      (notPc : register ≠ PC) (notNextPc : register ≠ nextPC)
      (notIncrement : register ≠ minstret_increment) (notRetired : register ≠ minstret) :
      (decodeInlineFirstCallAfter state retired).regs.get? register =
        state.regs.get? register := by
    have singletonAgree : Agree (fun r => r = register) state
        (decodeInlineFirstCallAfter state retired) := by
      apply jalrCallAfterRetired_agree_of
      · simpa using Ne.symm notLink
      · simpa using Ne.symm notPc
      · simpa using Ne.symm notNextPc
      · simpa using Ne.symm notIncrement
      · simpa using Ne.symm notRetired
    exact singletonAgree register rfl
  have resultAfter : (decodeInlineFirstCallAfter state retired).regs.get? x10 =
      some (BitVec.ofNat 64 args.firstTemporaryResultBase) :=
    (preserveGeneral x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      resultPointer
  have allocatorAfter : (decodeInlineFirstCallAfter state retired).regs.get? x11 =
      some (BitVec.ofNat 64 args.allocatorBase) :=
    (preserveGeneral x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      allocatorPointer
  have inputAfter : (decodeInlineFirstCallAfter state retired).regs.get? x12 =
      some (BitVec.ofNat 64 args.inputBase) :=
    (preserveGeneral x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      inputPointer
  have lengthAfter : (decodeInlineFirstCallAfter state retired).regs.get? x13 =
      some (BitVec.ofNat 64 args.bytes.size) :=
    (preserveGeneral x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      inputLength
  refine ⟨retired, run, pcAfter, linkAfter, resultAfter, allocatorAfter, inputAfter, lengthAfter,
    callAgree, callMemory, ?_⟩
  exact ⟨Sail.BitVec.addInt retired 1, by
    simp [decodeInlineFirstCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]⟩

/-- The first six decoder-owned instructions execute through Sail and establish the exact entry
predicate consumed by the selected `decodeRaw` child contract. -/
theorem decodeInline_first_enters_decodeRaw (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ childEntry, Trace fromStep 6 state childEntry ∧
      compiledDecodeRawContract.binding.entry args.firstRawArgs childEntry ∧
      childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x10320) := by
  obtain ⟨beforeCall, beforeTrace, callPc, callBase, resultPointer, allocatorPointer,
    inputPointer, inputLength, beforeAgree, beforeMemory, beforeRetired⟩ :=
    decodeInline_first_before_decodeRaw_call fromStep args state pre phase
  obtain ⟨retired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, callAgree, callMemory, childRetired⟩ :=
    decodeInline_first_decodeRaw_call_step (fromStep + 5) args state beforeCall pre
      beforeAgree beforeMemory beforeRetired callPc callBase resultPointer allocatorPointer
      inputPointer inputLength
  let childEntry := decodeInlineFirstCallAfter beforeCall retired
  have childTrace : Trace fromStep 6 state childEntry :=
    Trace.snoc beforeTrace (by simpa [childEntry] using callRun)
  have childAgree : Agree decoderPreserved state childEntry :=
    Agree.trans beforeAgree callAgree
  have childMemory : childEntry.mem = state.mem := callMemory.trans beforeMemory
  have childMachineAtParentExtent : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono childAgree childRetired
  have childExtentWithinParent : ∀ pc,
      functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw pc →
        functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 pc := by
    intro pc pcIn
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
  have childMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs args.firstRawArgs) childEntry := by
    simpa [DecodeInlineArgs.machineArgs, entryMachineArgs, DecodeInlineArgs.firstRawArgs] using
      childMachineAtParentExtent.restrict childExtentWithinParent
  have sourceEntry :
      (Contracts.contractDecodeRaw Contracts.canonicalContractParams.env
        Contracts.canonicalContractParams.repRawV4).toFunctionInstance.binding.entry
        args.firstRawArgs childEntry := by
    change Contracts.preEntry Contracts.canonicalContractParams.env args.firstRawArgs childEntry
    refine ⟨?_, ?_, childResult, childAllocator, childInput, childLength⟩
    · intro index bound
      rw [childMemory]
      exact pre.inputMemory index bound
    · change Contracts.canonicalContractParams.env.image.fileBytesMatchMemory childEntry.mem
      rw [childMemory]
      exact pre.code
  exact ⟨childEntry, childTrace, ⟨sourceEntry, childPc, childMachine⟩, childLink⟩

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

def decodeRawReturnAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10530) (BitVec.ofNat 64 0x10320))
    (BitVec.ofNat 64 0x10320) retired

/-- Execute the selected emitted child's real `ret` after its strengthened contract establishes the
link and machine frame required by that instruction. -/
theorem decodeRaw_first_return_step (stepNo : Nat) (rawArgs : Contracts.EntryArgs)
    (childEntry childExit : State) {childFrom childUsed : Nat}
    (childPre : compiledDecodeRawContract.binding.entry rawArgs childEntry)
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
      (Contracts.functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
      childFrom childUsed childEntry childExit)
    (entryLink : childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x10320))
    (childPost : compiledDecodeRawContract.binding.exit rawArgs
      (compiledDecodeRawContract.spec.meaning rawArgs) childEntry childExit) :
    ∃ retired,
      Runs (try_step stepNo false) childExit (decodeRawReturnAfter childExit retired) false ∧
      (decodeRawReturnAfter childExit retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10320) := by
  rcases childPost with ⟨sourcePost, childFrame, childRetired⟩
  rcases sourcePost with ⟨-, code, -, -⟩
  have machineAtExit : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs rawArgs) childExit :=
    childPre.2.2.mono (Agree.weaken (fun _ preserved => preserved.2) childFrame) childRetired
  obtain ⟨exitPc, atExit, isExit⟩ := childTrace.trace.final_at_exit
  have exitPcEq : exitPc = BitVec.ofNat 64 0x10530 := by
    apply BitVec.eq_of_toNat_eq
    simpa [functionInstanceExitPred, FunctionInstance.isExit,
      functionInstance_ssz_raw_decodeRaw] using isExit
  subst exitPc
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement childExit)
      (BitVec.ofNat 64 0x10530) 0x67#8 0x80#8 0x00#8 0x00#8 :=
    fetchFileInstruction childExit 0x10530 0x67 0x80 0x00 0x00 code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have pcIn : functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw
      (BitVec.ofNat 64 0x10530) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machineAtExit (Agree.refl childExit)
    (BitVec.ofNat 64 0x10530) atExit pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters machineAtExit.normal (Agree.refl childExit) childRetired
  have wordEq : fetchWord 0x67#8 0x80#8 0x00#8 0x00#8 =
      (0x00008067 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x67#8 0x80#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement childExit)
      (tryStepControlFlowAfterIncrement childExit)
      (.JALR (0#12, .Regidx 1#5, .Regidx 0#5)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement childExit)
    (BitVec.ofNat 64 0x10530)
  have executeAgree : Agree decoderPreserved childExit executeState :=
    Agree.weaken (fun _ preserved => preserved.2)
      (agree_stepPremiseState childExit (BitVec.ofNat 64 0x10530))
  have helpElp : Runs (update_elp_state (.Regidx 1#5)) executeState executeState () :=
    machineAtExit.landingPad executeState (.Regidx 1#5) trivial executeAgree
  have linkRead : executeState.regs.get? nextPC = some (BitVec.ofNat 64 0x10534) := by
    change ((tryStepControlFlowAfterIncrement childExit).regs.insert nextPC
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10530) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp
    decide
  have exitLink : childExit.regs.get? x1 = some (BitVec.ofNat 64 0x10320) :=
    (childFrame x1 (by simp [platformPreserved])).trans entryLink
  have sourceRead : executeState.regs.get? x1 = some (BitVec.ofNat 64 0x10320) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, exitLink]
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      childExit.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := machineAtExit.normal.2.2.2.2.2.2.2.2.2.2.2
    match read : childExit.regs.get? misa with
    | none => simp [read] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [read] using normalMisa⟩
  have zca := currentlyEnabledZca_run_atStepPremise childExit (BitVec.ofNat 64 0x10530)
    misaBits misaRead
  have retRun := tryStepRetRetires stepNo childExit (BitVec.ofNat 64 0x10530) retired
    (.Regidx 1#5) (BitVec.ofNat 64 0x10534) (BitVec.ofNat 64 0x10320) inhibit config
    0x67#8 0x80#8 0x00#8 0x00#8 (_get_Misa_C misaBits == 1#1) fetch noMMIO fetchBytes
    interrupts (by unfold BaseInstructionEncoding; decide) decode notExpected helpElp
    (get_next_pc_run executeState _ linkRead) (rX_bits_run_x1 executeState _ sourceRead)
    (by decide) zca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [decodeRawReturnAfter] using retRun
  · simp [decodeRawReturnAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]

def decodeRawFirstCallTransfer (fromStep used : Nat) (args : DecodeInlineArgs)
    (phase : args.phase = .first) (beforeCall childEntry childExit resumed : State)
    (atCall : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x1031c))
    (callRun : Runs (try_step fromStep false) beforeCall childEntry false)
    (childPre : compiledDecodeRawContract.binding.entry args.firstRawArgs childEntry)
    (bound : used ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs)
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
      (Contracts.functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
      (fromStep + 1) used childEntry childExit)
    (childPost : compiledDecodeRawContract.binding.exit args.firstRawArgs
      (compiledDecodeRawContract.spec.meaning args.firstRawArgs) childEntry childExit)
    (returnRun : Runs (try_step (fromStep + 1 + used) false) childExit resumed false)
    (atResume : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10320)) :
    CallTransfer
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw fromStep used beforeCall resumed := by
  have atRet : childExit.regs.get? PC = some (BitVec.ofNat 64 0x10530) := by
    obtain ⟨retPc, atRet, retIsExit⟩ := childTrace.trace.final_at_exit
    have retPcEq : retPc = BitVec.ofNat 64 0x10530 := by
      apply BitVec.eq_of_toNat_eq
      simpa [functionInstanceExitPred, FunctionInstance.isExit,
        functionInstance_ssz_raw_decodeRaw] using retIsExit
    simpa [retPcEq] using atRet
  have callInRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x1031c) :=
    decodeInline_owned_in_execution_region (0x1031c, 0x12c080e7)
      (by simp [decodeInlineOwnedInstructionWords])
  have returnInRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x10320) :=
    decodeInline_owned_in_execution_region (0x10320, 0x6a015503)
      (by simp [decodeInlineOwnedInstructionWords])
  have retInRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x10530) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have callNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x1031c) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have retNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10530) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have body : Level3ChildSummary functionInstance_ssz_raw_decodeRawId
      (fromStep + 1) used childEntry childExit :=
    Level3ChildSummary.decodeRaw
      ⟨rfl, args.firstRawArgs, childPre, bound, childTrace, childPost⟩
  exact
    { valid := decodeRawFirstAttemptCall_valid
      callPc := BitVec.ofNat 64 0x1031c
      atCall := atCall
      callSource := by decide
      callInRegion := callInRegion
      callNotExit := callNotExit
      sCall := childEntry
      doCall := callRun
      calleeEntryPc := BitVec.ofNat 64 0x10444
      atCalleeEntry := childPre.2.1
      calleeEntryMatches := by decide
      sRet := childExit
      body := body
      retPc := BitVec.ofNat 64 0x10530
      atRet := atRet
      retInRegion := retInRegion
      retNotExit := retNotExit
      doReturn := returnRun
      returnPc := BitVec.ofNat 64 0x10320
      atResume := atResume
      returnMatches := by decide
      resumeInRegion := returnInRegion }

theorem decodeInline_first_call_transfer
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ beforeCall childUsed resumed,
      Trace fromStep 5 state beforeCall ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      Nonempty (CallTransfer
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed) := by
  obtain ⟨beforeCall, parentTrace, callPc, callBase, resultPointer, allocatorPointer,
    inputPointer, inputLength, beforeAgree, beforeMemory, beforeRetired⟩ :=
    decodeInline_first_before_decodeRaw_call fromStep args state pre phase
  obtain ⟨callRetired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, callAgree, callMemory, childRetired⟩ :=
    decodeInline_first_decodeRaw_call_step (fromStep + 5) args state beforeCall pre
      beforeAgree beforeMemory beforeRetired callPc callBase resultPointer allocatorPointer
      inputPointer inputLength
  let childEntry := decodeInlineFirstCallAfter beforeCall callRetired
  have childAgree : Agree decoderPreserved state childEntry :=
    Agree.trans beforeAgree callAgree
  have childMachineAtParentExtent : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono childAgree childRetired
  have childExtentWithinParent : ∀ pc,
      functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw pc →
        functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 pc := by
    intro pc pcIn
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
  have childMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs args.firstRawArgs) childEntry := by
    simpa [DecodeInlineArgs.machineArgs, entryMachineArgs, DecodeInlineArgs.firstRawArgs] using
      childMachineAtParentExtent.restrict childExtentWithinParent
  have childMemory : childEntry.mem = state.mem := callMemory.trans beforeMemory
  have childSourceEntry : Contracts.preEntry Contracts.canonicalContractParams.env
      args.firstRawArgs childEntry := by
    refine ⟨?_, ?_, childResult, childAllocator, childInput, childLength⟩
    · intro index bound
      rw [childMemory]
      exact pre.inputMemory index bound
    · change Contracts.canonicalContractParams.env.image.fileBytesMatchMemory childEntry.mem
      rw [childMemory]
      exact pre.code
  have childPre : compiledDecodeRawContract.binding.entry args.firstRawArgs childEntry :=
    ⟨childSourceEntry, childPc, childMachine⟩
  obtain ⟨childUsed, childExit, bound, childTrace, childPost⟩ :=
    contract args.firstRawArgs (fromStep + 6) childEntry childPre
  obtain ⟨returnRetired, returnRun, atResume⟩ :=
    decodeRaw_first_return_step (fromStep + 6 + childUsed) args.firstRawArgs childEntry
      childExit childPre childTrace childLink childPost
  let resumed := decodeRawReturnAfter childExit returnRetired
  have transfer : CallTransfer
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed := by
    apply decodeRawFirstCallTransfer (fromStep + 5) childUsed args phase beforeCall childEntry
      childExit resumed callPc
    · simpa [childEntry] using callRun
    · exact childPre
    · exact bound
    · simpa only [Nat.add_assoc] using childTrace
    · exact childPost
    · simpa [resumed, Nat.add_assoc] using returnRun
    · simpa [resumed] using atResume
  exact ⟨beforeCall, childUsed, resumed, parentTrace, bound, ⟨transfer⟩⟩

end BinaryFv.Zesu.MachineExecution
