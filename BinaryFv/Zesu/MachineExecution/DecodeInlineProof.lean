import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Elfling.SequentialSplice

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

/-! ## Memory-only transport used across parent-owned register instructions -/

theorem writesOnlyWithinOwnAllocation_of_mem_eq
    (env : Contracts.DecoderEnvironment) (recordBase recordSize : Nat)
    {before after before' after' : State}
    (beforeMemory : before'.mem = before.mem) (afterMemory : after'.mem = after.mem)
    (writes : env.WritesOnlyWithinOwnAllocation recordBase recordSize before after) :
    env.WritesOnlyWithinOwnAllocation recordBase recordSize before' after' := by
  rcases writes with ⟨cursorBefore, cursorAfter, beforeCursor, afterCursor, frame⟩
  refine ⟨cursorBefore, cursorAfter, ?_, ?_, ?_⟩
  · unfold Contracts.DecoderEnvironment.cursor? at beforeCursor ⊢
    unfold BinaryFv.Zesu.MemoryRepresentation.observeWord64? at beforeCursor ⊢
    rw [beforeMemory]
    exact beforeCursor
  · unfold Contracts.DecoderEnvironment.cursor? at afterCursor ⊢
    unfold BinaryFv.Zesu.MemoryRepresentation.observeWord64? at afterCursor ⊢
    rw [afterMemory]
    exact afterCursor
  · intro address outside
    rw [afterMemory, beforeMemory]
    exact frame address outside

theorem rawV4Rep_of_mem_eq {before after : State} {inputBase rootBase : Nat}
    {input : ByteArray} {value : BinaryFv.Specs.SSZ.RawV4}
    (memory : after.mem = before.mem)
    (representation : BinaryFv.Zesu.MemoryRepresentation.RawV4Rep
      before inputBase input rootBase value) :
    BinaryFv.Zesu.MemoryRepresentation.RawV4Rep after inputBase input rootBase value := by
  obtain ⟨_, transport⟩ :=
    Contracts.Footprint.rawV4_footprint_abi inputBase input rootBase value before
      Artifacts.raw_stateless_input_layout.1 representation
  exact transport _ (fun address _ => (congrArg (·.get? address) memory).symm)

/-- A fully allocated fixed-size heap record has a concrete byte snapshot. This supplies the exact
source bytes required by the selected `memcpy` boundary without assuming their contents. -/
theorem memoryBytes_exists_of_heapArrayRep (state : State) (base size : Nat)
    (allocated : BinaryFv.Zesu.MemoryRepresentation.HeapArrayRep state base 1 size) :
    ∃ bytes : ByteArray,
      bytes.size = size ∧ BinaryFv.Zesu.MemoryRepresentation.MemoryBytes state base bytes := by
  let bytes : ByteArray := ⟨Array.ofFn fun index : Fin size =>
    UInt8.ofNat ((state.mem.get? (base + index)).getD 0#8).toNat⟩
  have bytesSize : bytes.size = size := by
    simp [bytes, ByteArray.size, Array.size_ofFn]
  refine ⟨bytes, bytesSize, ?_⟩
  intro index bound
  have indexSize : index < size := by simpa [bytesSize] using bound
  have present := allocated.2 index (by simpa using indexSize)
  obtain ⟨value, valueAt⟩ := Option.isSome_iff_exists.mp present
  have valueRead : (state.mem.get? (base + index)).getD 0#8 = value := by
    rw [valueAt]
    rfl
  have byteAt : bytes[index] = UInt8.ofNat value.toNat := by
    rw [ByteArray.getElem_eq_getElem_data]
    simp only [bytes, Array.getElem_ofFn]
    rw [valueRead]
  rw [byteAt, valueAt]
  simp

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
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10318) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
      after.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size) ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
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
  have stack4 : s4.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [s4, s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.stackValue]
  have region1 := decodeInline_owned_in_execution_region (0x10308, 0x36010513)
    (by simp [decodeInlineOwnedInstructionWords])
  have region2 := decodeInline_owned_in_execution_region (0x1030c, 0x01010593)
    (by simp [decodeInlineOwnedInstructionWords])
  have region3 := decodeInline_owned_in_execution_region (0x10310, 0x00040613)
    (by simp [decodeInlineOwnedInstructionWords])
  have region4 := decodeInline_owned_in_execution_region (0x10314, 0x00048693)
    (by simp [decodeInlineOwnedInstructionWords])
  have notExit1 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10308) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have notExit2 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x1030c) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have notExit3 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10310) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have notExit4 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10314) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have atFirstEntry : state.regs.get? PC = some (BitVec.ofNat 64 0x10308) := by
    simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry
  have prefix1 : ConfinedPrefix _ _ Level3ChildSummary fromStep 1 state s1 :=
    ConfinedPrefix.ownStep
      (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (exit := DecodeInlineExit args) (childSummary := Level3ChildSummary)
      atFirstEntry region1 notExit1 (by simpa [s1, firstResult] using run1)
  have prefix2 : ConfinedPrefix _ _ Level3ChildSummary (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep
      (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (exit := DecodeInlineExit args) (childSummary := Level3ChildSummary)
      pc1 region2 notExit2 (by simpa [s2, allocator] using run2)
  have prefix3 : ConfinedPrefix _ _ Level3ChildSummary (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep
      (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (exit := DecodeInlineExit args) (childSummary := Level3ChildSummary)
      pc2 region3 notExit3 (by simpa [s3, input] using run3)
  have prefix4 : ConfinedPrefix _ _ Level3ChildSummary (fromStep + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep
      (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (exit := DecodeInlineExit args) (childSummary := Level3ChildSummary)
      pc3 region4 notExit4 (by simpa [s4, length] using run4)
  have combinedPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary fromStep 4 state s4 := by
    have p12 := ConfinedPrefix.trans
      (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (exit := DecodeInlineExit args) (childSummary := Level3ChildSummary) prefix1 prefix2
    have p123 := ConfinedPrefix.trans
      (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (exit := DecodeInlineExit args) (childSummary := Level3ChildSummary)
      p12 (by simpa using prefix3)
    have p1234 := ConfinedPrefix.trans
      (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (exit := DecodeInlineExit args) (childSummary := Level3ChildSummary)
      p123 (by simpa using prefix4)
    simpa using p1234
  refine ⟨s4, ?_, combinedPrefix, pc4, result4, allocator4, input4, length4, stack4, agree4, rfl,
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
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall ∧
      beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x1031c) ∧
      beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x10318) ∧
      beforeCall.regs.get? x10 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
      beforeCall.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase) ∧
      beforeCall.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size) ∧
      beforeCall.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      Agree decoderPreserved state beforeCall ∧ beforeCall.mem = state.mem ∧
      RetiredCounterPresent beforeCall := by
  obtain ⟨afterArgs, argsTrace, argsPrefix, argsPc, resultArgs, allocatorArgs, inputArgs,
    lengthArgs, stackArgs, argsAgree, argsMemory, argsRetired⟩ :=
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
  have stackBefore : beforeCall.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackArgs]
  have callPageAgree : Agree decoderPreserved afterArgs beforeCall := by
    apply afterRegisterWrite_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  have memoryUnchanged : beforeCall.mem = state.mem := by
    change (afterRegisterWrite afterArgs (BitVec.ofNat 64 0x10318) retired x1
      (BitVec.ofNat 64 0x10318)).mem = state.mem
    exact (afterRegisterWrite_mem afterArgs (BitVec.ofNat 64 0x10318) retired x1
      (BitVec.ofNat 64 0x10318)).trans argsMemory
  have callPageRegion := decodeInline_owned_in_execution_region (0x10318, 0x00000097)
    (by simp [decodeInlineOwnedInstructionWords])
  have callPageNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10318) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have callPagePrefix : ConfinedPrefix _ _ Level3ChildSummary (fromStep + 4) 1
      afterArgs beforeCall :=
    ConfinedPrefix.ownStep
      (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (exit := DecodeInlineExit args) (childSummary := Level3ChildSummary)
      argsPc callPageRegion callPageNotExit
      (by simpa [beforeCall] using callPageStep)
  have combinedPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall := by
    have combined := ConfinedPrefix.trans
      (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (exit := DecodeInlineExit args) (childSummary := Level3ChildSummary)
      argsPrefix callPagePrefix
    simpa using combined
  refine ⟨beforeCall, ?_, combinedPrefix, callPc, returnBase, resultBefore, allocatorBefore, inputBefore,
    lengthBefore, stackBefore,
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
  obtain ⟨beforeCall, beforeTrace, -, callPc, callBase, resultPointer, allocatorPointer,
    inputPointer, inputLength, -, beforeAgree, beforeMemory, beforeRetired⟩ :=
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

theorem decodeRawReturnAfter_agree (state : State) (retired : BitVec 64) :
    Agree decoderPreserved state (decodeRawReturnAfter state retired) := by
  intro register preserved
  have notPc : register ≠ PC := by
    intro equal
    subst register
    simp [decoderPreserved, platformPreserved] at preserved
  have notNextPc : register ≠ nextPC := by
    intro equal
    subst register
    simp [decoderPreserved, platformPreserved] at preserved
  have notRetired : register ≠ minstret := by
    intro equal
    subst register
    simp [decoderPreserved, platformPreserved] at preserved
  have notIncrement : register ≠ minstret_increment := by
    intro equal
    subst register
    simp [decoderPreserved, platformPreserved] at preserved
  simp [decodeRawReturnAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    controlFlowJumpState, tryStepControlFlowAfterIncrement, coreControlFlowNextState,
    Std.ExtDHashMap.get?_insert, Ne.symm notPc, Ne.symm notNextPc, Ne.symm notRetired,
    Ne.symm notIncrement]

theorem decodeRawReturnAfter_mem (state : State) (retired : BitVec 64) :
    (decodeRawReturnAfter state retired).mem = state.mem := rfl

theorem decodeRawReturnAfter_retired (state : State) (retired : BitVec 64) :
    RetiredCounterPresent (decodeRawReturnAfter state retired) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [decodeRawReturnAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]

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
    childPre.2.2.mono
      (Agree.weaken (fun _ preserved => Or.inl preserved.2) childFrame) childRetired
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
    (childFrame x1 (by simp [decodeRawCallerPreserved, platformPreserved])).trans entryLink
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
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      Nonempty (CallTransfer
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed) ∧
      BinaryFv.Zesu.MemoryRepresentation.ResultStatusLERep resumed
        (args.firstTemporaryResultBase +
          Contracts.canonicalContractParams.env.record.entryResultTagOffset)
        (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)) ∧
      Contracts.canonicalContractParams.env.CodeIntact resumed ∧
      Agree decoderPreserved state resumed ∧
      RetiredCounterPresent resumed ∧
      resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
        Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
        state resumed := by
  obtain ⟨beforeCall, parentTrace, parentPrefix, callPc, callBase, resultPointer, allocatorPointer,
    inputPointer, inputLength, beforeStack, beforeAgree, beforeMemory, beforeRetired⟩ :=
    decodeInline_first_before_decodeRaw_call fromStep args state pre phase
  obtain ⟨callRetired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, callAgree, callMemory, childRetired⟩ :=
    decodeInline_first_decodeRaw_call_step (fromStep + 5) args state beforeCall pre
      beforeAgree beforeMemory beforeRetired callPc callBase resultPointer allocatorPointer
      inputPointer inputLength
  let childEntry := decodeInlineFirstCallAfter beforeCall callRetired
  have childStack : childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [childEntry, decodeInlineFirstCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, callLinkState, controlFlowJumpState,
      tryStepControlFlowAfterIncrement, coreControlFlowNextState, Std.ExtDHashMap.get?_insert,
      beforeStack]
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
  rcases childPost with ⟨sourcePost, childFrame, childCounter⟩
  rcases sourcePost with ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have resumedStatus : BinaryFv.Zesu.MemoryRepresentation.ResultStatusLERep resumed
      (args.firstTemporaryResultBase +
        Contracts.canonicalContractParams.env.record.entryResultTagOffset)
      (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)) := by
    simpa [resumed, DecodeInlineArgs.firstRawArgs] using childStatus
  have resumedCode : Contracts.canonicalContractParams.env.CodeIntact resumed := by
    simpa [resumed, decodeRawReturnAfter] using childCode
  have childFrameDecoder : Agree decoderPreserved childEntry childExit :=
    Agree.weaken (fun _ preserved => Or.inl preserved.2) childFrame
  have resumedAgree : Agree decoderPreserved state resumed :=
    Agree.trans childAgree
      (Agree.trans childFrameDecoder (by
        simpa [resumed] using (decodeRawReturnAfter_agree childExit returnRetired)))
  have exitStack : childExit.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (childFrame x2 (by simp [decodeRawCallerPreserved])).trans childStack
  have resumedStack : resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [resumed, decodeRawReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert, exitStack]
  have resumedPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
      state resumed := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (Contracts.meaningDecodeRaw args.bytes)
      childMemory.symm (decodeRawReturnAfter_mem childExit returnRetired)
    exact ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
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
    · exact ⟨⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩,
        childFrame, childCounter⟩
    · simpa [resumed, Nat.add_assoc] using returnRun
    · simpa [resumed] using atResume
  exact ⟨beforeCall, childUsed, resumed, parentTrace, parentPrefix, bound, ⟨transfer⟩, resumedStatus,
    resumedCode, resumedAgree, by simpa [resumed] using
      decodeRawReturnAfter_retired childExit returnRetired, resumedStack, resumedPost⟩

/-! ## First result dispatch -/

/-- Execute the actual `lhu a0, 0x6a0(sp)` that reads the first `decodeRaw` result tag. The bytes
come from the strengthened child postcondition; no result value is assumed by the machine step. -/
theorem decodeInline_first_result_tag_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (status : BinaryFv.Zesu.MemoryRepresentation.ResultStatusLERep state
      (args.firstTemporaryResultBase +
        Contracts.canonicalContractParams.env.record.entryResultTagOffset)
      (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10320)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10320) retired x10
        (BitVec.ofNat 64
          (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) false := by
  let tag := Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)
  have tagLt : tag < 2 ^ 16 := by
    simp only [tag]
    cases rawResult : Contracts.meaningDecodeRaw args.bytes with
    | ok value => simp [Contracts.decodeInternalResultTag]
    | error error => cases error <;> simp [Contracts.decodeInternalResultTag]
  have tagCases : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 := by
    simp only [tag]
    cases rawResult : Contracts.meaningDecodeRaw args.bytes with
    | ok value => simp [Contracts.decodeInternalResultTag]
    | error error => cases error <;> simp [Contracts.decodeInternalResultTag]
  have tagOffset : Contracts.canonicalContractParams.env.record.entryResultTagOffset = 832 := by
    have pinned := congrArg (fun record => record.entryResultTagOffset)
      Contracts.canonicalRecordSizes_pinned
    simpa [Contracts.canonicalContractParams, Contracts.canonicalEnvironment] using pinned
  let address := BitVec.ofNat 64 (args.stackBase + 0x6a0)
  have addressFits : args.stackBase + 0x6a0 + 2 ≤ 2 ^ 64 := by
    have fit := pre.stackObjectsFit
    omega
  have addressNat : address.toNat = args.stackBase + 0x6a0 := by
    simp [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : args.stackBase + 0x6a0 < 2 ^ 64)]
  have pcIn := decodeInline_owned_in_execution_region (0x10320, 0x6a015503)
    (by simp [decodeInlineOwnedInstructionWords])
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10320) 0x03#8 0x55#8 0x01#8 0x6a#8 :=
    fetchFileInstruction state 0x10320 0x03 0x55 0x01 0x6a image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x10320) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x03#8 0x55#8 0x01#8 0x6a#8 =
      (0x6a015503 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x03#8 0x55#8 0x01#8 0x6a#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0x6a0#12, .Regidx 2#5, .Regidx 10#5, true, 2)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10320)
  have executeAgree : Agree decoderPreserved baseState executeState :=
    Agree.trans agree
      (Agree.weaken (fun _ preserved => preserved.2)
        (agree_stepPremiseState state (BitVec.ofNat 64 0x10320)))
  have stackAtExecute : executeState.regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  obtain ⟨mstatusBits, mstatusReadBase, mprvZero⟩ := pre.machine.mstatus
  obtain ⟨mseccfgBase, mseccfgReadBase, pmmDisabled⟩ := pre.machine.mseccfg
  have mstatusRead : executeState.regs.get? mstatus = some mstatusBits :=
    (executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusReadBase
  have privilegeRead : executeState.regs.get? cur_privilege = some Privilege.Machine :=
    (executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      pre.machine.normal.2.1
  have mseccfgReadExecute : executeState.regs.get? mseccfg = some mseccfgBase :=
    (executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgReadBase
  have addressEq : BitVec.ofNat 64 args.stackBase + sign_extend (m := 64) (0x6a0#12) =
      address := by
    rw [show sign_extend (m := 64) (0x6a0#12) = BitVec.ofNat 64 0x6a0 by decide,
      ← BitVec.ofNat_add]
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 2#5) (sign_extend (m := 64) (0x6a0#12))
        (MemoryAccessType.Load mem_payload.Data) 2)
      executeState executeState (.Ext_DataAddr_OK (virtaddr.Virtaddr address)) := by
    rw [← addressEq]
    exact get_transformed_data_addr_machine_load_run executeState (.Regidx 2#5)
      (BitVec.ofNat 64 args.stackBase) (sign_extend (m := 64) (0x6a0#12)) mstatusBits
      mseccfgBase (rX_bits_run_x2 executeState _ stackAtExecute) mstatusRead privilegeRead
      mprvZero mseccfgReadExecute pmmDisabled
  have allowed : DecoderAccessRange (DecoderReadableByte args.machineArgs) address 2 := by
    refine ⟨by simpa [addressNat] using addressFits, ?_⟩
    intro index indexLt
    right
    right
    left
    rw [addressNat]
    have stackByte := pre.stackObjectsReadable (0x6a0 + index) (by
      have positive : 0 < Contracts.canonicalContractParams.env.record.entryResult := by
        have pinned := congrArg (fun record => record.entryResult)
          Contracts.canonicalRecordSizes_pinned
        have sizeEq : Contracts.canonicalContractParams.env.record.entryResult = 848 := by
          simpa [Contracts.canonicalContractParams, Contracts.canonicalEnvironment] using pinned
        omega
      omega)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stackByte
  obtain ⟨physAccess, loadNoMMIO⟩ :=
    pre.machine.dataAccess.load executeState address 2 executeAgree allowed
  have aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 2 = true := by
    have addressMod : address.toNat % 2 = 0 := by
      rw [addressNat]
      have stackAligned := pre.stackAligned
      omega
    simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, ← Int.ofNat_tmod,
      addressMod]
    rfl
  have statusAtAddress : BinaryFv.Zesu.MemoryRepresentation.ResultStatusLERep state
      address.toNat tag := by
    simpa [addressNat, DecodeInlineArgs.firstTemporaryResultBase, tagOffset, tag,
      Nat.add_assoc] using status
  rcases statusAtAddress with ⟨-, lowByte, highByte⟩
  have memoryBytes : ∀ (index : Nat) (indexLt : index < (leBytes 2 (BitVec.ofNat 16 tag)).length),
      executeState.mem.get? (address.toNat + index) =
        some (leBytes 2 (BitVec.ofNat 16 tag))[index] := by
    intro index indexLt
    rw [leBytes_length] at indexLt
    have executeMemory : executeState.mem = state.mem := rfl
    rw [executeMemory]
    have indexCases : index = 0 ∨ index = 1 := by omega
    rcases indexCases with rfl | rfl
    · rcases tagCases with h | h | h | h <;> simpa [h, leBytes] using lowByte
    · rcases tagCases with h | h | h | h <;> simpa [h, leBytes] using highByte
  have hread := vmem_read_half_from_bytes_run executeState (.Regidx 2#5)
    (sign_extend (m := 64) (0x6a0#12)) address mstatusBits (BitVec.ofNat 16 tag)
    mstatusRead privilegeRead mprvZero addressRun aligned physAccess loadNoMMIO memoryBytes
  have extended : extend_value true (BitVec.ofNat 16 tag) = BitVec.ofNat 64 tag := by
    rcases tagCases with h | h | h | h <;>
      simp [h, extend_value, zero_extend, Sail.BitVec.zeroExtend]
  have write : Runs (wX_bits (.Regidx 10#5) (BitVec.ofNat 64 tag)) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 tag) } () :=
    wX_x10_run executeState (BitVec.ofNat 64 tag)
  have execute : Runs (execute (.LOAD (0x6a0#12, .Regidx 2#5, .Regidx 10#5, true, 2)))
      executeState { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 tag) }
      (.Retire_Success ()) := by
    change Runs (execute_LOAD (0x6a0#12) (.Regidx 2#5) (.Regidx 10#5) true 2) _ _ _
    exact execute_LOAD_lhu_run executeState _ (0x6a0#12) (.Regidx 2#5) (.Regidx 10#5)
      (BitVec.ofNat 16 tag) hread (by simpa [extended] using write)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x10320) pcIn atPc 0x03#8 0x55#8 0x01#8 0x6a#8
    (.LOAD (0x6a0#12, .Regidx 2#5, .Regidx 10#5, true, 2)) x10 (BitVec.ofNat 64 tag)
    fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Consume the first Level 3 `decodeRaw` condition, return from the emitted function, and then
execute the parent-owned result-tag load. This is the first composed path where a child contract
directly enables a following instruction of the inlined parent. -/
theorem decodeInline_first_through_result_tag
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ beforeCall childUsed resumed retired,
      Trace fromStep 5 state beforeCall ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      Nonempty (CallTransfer
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed) ∧
      Runs (try_step (fromStep + 7 + childUsed) false) resumed
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) false ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        PC = some (BitVec.ofNat 64 0x10324) ∧
      Contracts.canonicalContractParams.env.CodeIntact
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      Agree decoderPreserved state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      RetiredCounterPresent
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        x10 = some (BitVec.ofNat 64
          (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes))) ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
        Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes) state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) := by
  obtain ⟨beforeCall, childUsed, resumed, parentTrace, parentPrefix, bound, transfer, status, code,
    resumedAgree, resumedRetired, resumedStack, resumedPost⟩ :=
    decodeInline_first_call_transfer contract fromStep args state pre phase
  obtain ⟨callTransfer⟩ := transfer
  have resumePc : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10320) := by
    have returnPcEq : callTransfer.returnPc = BitVec.ofNat 64 0x10320 := by
      apply BitVec.eq_of_toNat_eq
      simpa [decodeRawFirstAttemptCall] using callTransfer.returnMatches
    simpa [returnPcEq] using callTransfer.atResume
  obtain ⟨retired, tagRun⟩ := decodeInline_first_result_tag_step
    (fromStep + 7 + childUsed) args state resumed pre status code resumedAgree resumedRetired
      resumedStack resumePc
  let tagValue := BitVec.ofNat 64
    (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes))
  let afterTag := afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue
  have tagAgree : Agree decoderPreserved resumed afterTag := by
    apply afterRegisterWrite_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  have afterCode : Contracts.canonicalContractParams.env.CodeIntact afterTag := by
    simpa [afterTag, tagValue, afterRegisterWrite_mem] using code
  have afterX10 : afterTag.regs.get? x10 = some tagValue := by
    simp [afterTag, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have afterStack : afterTag.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [afterTag, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resumedStack]
  have afterPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
      state afterTag := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (Contracts.meaningDecodeRaw args.bytes)
      rfl (afterRegisterWrite_mem resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue)
    exact resumedPost
  refine ⟨beforeCall, childUsed, resumed, retired, parentTrace, parentPrefix, bound, ⟨callTransfer⟩,
    by simpa [afterTag, tagValue] using tagRun, ?_, afterCode,
    Agree.trans resumedAgree tagAgree, ?_, afterStack, afterX10, afterPost⟩
  · simpa [afterTag, tagValue] using
      afterRegisterWrite_pc resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue
  · simpa [afterTag, tagValue] using
      afterRegisterWrite_retired_present resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue

def decodeInlineFirstSuccessBranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10324))
    (BitVec.ofNat 64 0x10328) retired

/-- On a successful first `decodeRaw`, execute the real `bne a0, x0, 0x1037c` at `0x10324` as a
not-taken branch and continue to the success-copy setup at `0x10328`. -/
theorem decodeInline_first_success_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10324))
    (successTag : state.regs.get? x10 = some (0#64)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlineFirstSuccessBranchAfter state retired) false ∧
      (decodeInlineFirstSuccessBranchAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10328) := by
  have pcIn := decodeInline_owned_in_execution_region (0x10324, 0x04051c63)
    (by simp [decodeInlineOwnedInstructionWords])
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10324) 0x63#8 0x1c#8 0x05#8 0x04#8 :=
    fetchFileInstruction state 0x10324 0x63 0x1c 0x05 0x04 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x10324) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal (Agree.refl state) retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have wordEq : fetchWord 0x63#8 0x1c#8 0x05#8 0x04#8 =
      (0x04051c63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x1c#8 0x05#8 0x04#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x58#13, .Regidx 0#5, .Regidx 10#5, .BNE)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10324)
  have x10AtExecute : executeState.regs.get? x10 = some (0#64) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, successTag]
  have condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 10#5) .BNE)
      executeState executeState false := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState (0#64) x10AtExecute) ?_
    refine Runs.bind (rX_x0_run executeState) ?_
    rfl
  have run := tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10324) retired
    (0x58#13) (.Regidx 0#5) (.Regidx 10#5) .BNE inhibit config
    0x63#8 0x1c#8 0x05#8 0x04#8 fetch noMMIO fetchBytes interrupts
    (by unfold BaseInstructionEncoding; decide) decode notExpected condition hartRead inhibitRead
    configRead notInhibited machineEnabled retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [decodeInlineFirstSuccessBranchAfter] using run
  · simp [decodeInlineFirstSuccessBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]

/-- Execute `addi a0, sp, 0x20`, the first argument setup instruction for the successful-result
copy. -/
theorem decodeInline_first_success_copy_destination_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10328))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10328) retired x10
          (iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have pcIn := decodeInline_owned_in_execution_region (0x10328, 0x02010513)
    (by simp [decodeInlineOwnedInstructionWords])
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10328) 0x13#8 0x05#8 0x01#8 0x02#8 :=
    fetchFileInstruction state 0x10328 0x13 0x05 0x01 0x02 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x10328) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x05#8 0x01#8 0x02#8 =
      (0x02010513 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x01#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 10#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10328)
  have stackAtExecute : executeState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  let result := iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase)
  have execute : Runs (execute (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 10#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x10 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x020#12 (.Regidx 2#5) (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x020#12 (.Regidx 2#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 args.stackBase)
      (rX_bits_run_x2 executeState _ stackAtExecute) (wX_x10_run executeState result)
  have baseEncoding : BaseInstructionEncoding 0x13#8 := by
    unfold BaseInstructionEncoding
    decide
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x10328) pcIn atPc 0x13#8 0x05#8 0x01#8 0x02#8
    (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 10#5, .ADDI)) x10 result fetchBytes
    baseEncoding decode (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `addi a1, sp, 0x360`, selecting the successful temporary result as the copy source. -/
theorem decodeInline_first_success_copy_source_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1032c))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x1032c) retired x11
          (iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have pcIn := decodeInline_owned_in_execution_region (0x1032c, 0x36010593)
    (by simp [decodeInlineOwnedInstructionWords])
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1032c) 0x93#8 0x05#8 0x01#8 0x36#8 :=
    fetchFileInstruction state 0x1032c 0x93 0x05 0x01 0x36 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x1032c) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x93#8 0x05#8 0x01#8 0x36#8 =
      (0x36010593 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x01#8 0x36#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x360#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1032c)
  have stackAtExecute : executeState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  let result := iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase)
  have execute : Runs (execute (.ITYPE (0x360#12, .Regidx 2#5, .Regidx 11#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x11 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x360#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x360#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI
      (BitVec.ofNat 64 args.stackBase)
      (rX_bits_run_x2 executeState _ stackAtExecute) (wX_x11_run executeState result)
  have baseEncoding : BaseInstructionEncoding 0x93#8 := by
    unfold BaseInstructionEncoding
    decide
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x1032c) pcIn atPc 0x93#8 0x05#8 0x01#8 0x36#8
    (.ITYPE (0x360#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) x11 result fetchBytes
    baseEncoding decode (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `addi a2, x0, 0x340`, fixing the successful-result copy length at 832 bytes. -/
theorem decodeInline_first_success_copy_length_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10330)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10330) retired x12
          (iTypeResult .ADDI 0x340#12 (0#64))) false := by
  have pcIn := decodeInline_owned_in_execution_region (0x10330, 0x34000613)
    (by simp [decodeInlineOwnedInstructionWords])
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10330) 0x13#8 0x06#8 0x00#8 0x34#8 :=
    fetchFileInstruction state 0x10330 0x13 0x06 0x00 0x34 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x10330) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x06#8 0x00#8 0x34#8 =
      (0x34000613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x00#8 0x34#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10330)
  let result := iTypeResult .ADDI 0x340#12 (0#64)
  have execute : Runs (execute (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x12 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x340#12 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x340#12 (.Regidx 0#5) (.Regidx 12#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x12_run executeState result)
  have baseEncoding : BaseInstructionEncoding 0x13#8 := by
    unfold BaseInstructionEncoding
    decide
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x10330) pcIn atPc 0x13#8 0x06#8 0x00#8 0x34#8
    (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)) x12 result fetchBytes
    baseEncoding decode (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `auipc ra, 4`, the final parent-owned instruction before the emitted `memcpy` call. -/
theorem decodeInline_first_success_copy_call_page_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10334)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10334) retired x1
          (BitVec.ofNat 64 0x14334)) false := by
  have pcIn := decodeInline_owned_in_execution_region (0x10334, 0x00004097)
    (by simp [decodeInlineOwnedInstructionWords])
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10334) 0x97#8 0x40#8 0x00#8 0x00#8 :=
    fetchFileInstruction state 0x10334 0x97 0x40 0x00 0x00 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x10334) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x97#8 0x40#8 0x00#8 0x00#8 =
      (0x00004097 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x97#8 0x40#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10334)
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x10334) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC)))
      executeState
      { executeState with regs := executeState.regs.insert x1 (BitVec.ofNat 64 0x14334) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_auipc_run executeState _ 0x00004#20 (.Regidx 1#5)
      (BitVec.ofNat 64 0x10334)
    · exact readReg_run _ _ _ pcAtExecute
    · simpa using wX_bits_run_x1 executeState (BitVec.ofNat 64 0x14334)
  have baseEncoding : BaseInstructionEncoding 0x97#8 := by
    unfold BaseInstructionEncoding
    decide
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x10334) pcIn atPc 0x97#8 0x40#8 0x00#8 0x00#8
    (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC)) x1 (BitVec.ofNat 64 0x14334) fetchBytes
    baseEncoding decode (by decide) (by decide) (by decide) (by decide) execute

/-- The four successful-result copy arguments are not an assumed ABI boundary. They are the exact
Sail execution of the parent-owned words at `0x10328..0x10334`, stopping on the selected emitted
`memcpy` call instruction at `0x10338`. -/
theorem decodeInline_first_success_copy_setup (fromStep : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (phase : args.phase = .first) (value : BinaryFv.Specs.SSZ.RawV4)
    (success : Contracts.meaningDecodeRaw args.bytes = .ok value)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10328))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (post : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
      baseState state) :
    ∃ after,
      Trace fromStep 4 state after ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10338) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      after.regs.get? x12 = some (BitVec.ofNat 64 832) ∧
      Agree decoderPreserved baseState after ∧
      RetiredCounterPresent after ∧
      Contracts.canonicalContractParams.env.CodeIntact after ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
        Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
        baseState after := by
  let destination := iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired1, run1⟩ := decodeInline_first_success_copy_destination_step fromStep args
    baseState state pre agree retiredPresent code atPc stackRead
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x10328) retired1 x10 destination
  have agree1 : Agree decoderPreserved baseState s1 :=
    Agree.trans agree (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x1032c) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10328) retired1 x10 destination
  have stack1 : s1.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [s1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      stackRead]
  have code1 : Contracts.canonicalContractParams.env.CodeIntact s1 := by
    simpa [s1, afterRegisterWrite_mem] using code
  let source := iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired2, run2⟩ := decodeInline_first_success_copy_source_step (fromStep + 1) args
    baseState s1 pre agree1
    (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10328) retired1 x10 destination)
    code1 pc1 stack1
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x1032c) retired2 x11 source
  have agree2 : Agree decoderPreserved baseState s2 :=
    Agree.trans agree1 (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10330) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x1032c) retired2 x11 source
  have code2 : Contracts.canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, afterRegisterWrite_mem] using code1
  let length := iTypeResult .ADDI 0x340#12 (0#64)
  obtain ⟨retired3, run3⟩ := decodeInline_first_success_copy_length_step (fromStep + 2) args
    baseState s2 pre agree2
    (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x1032c) retired2 x11 source)
    code2 pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10330) retired3 x12 length
  have agree3 : Agree decoderPreserved baseState s3 :=
    Agree.trans agree2 (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10334) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10330) retired3 x12 length
  have code3 : Contracts.canonicalContractParams.env.CodeIntact s3 := by
    simpa [s3, afterRegisterWrite_mem] using code2
  obtain ⟨retired4, run4⟩ := decodeInline_first_success_copy_call_page_step
    (fromStep + 3) args baseState s3 pre agree3
    (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10330) retired3 x12 length)
    code3 pc3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x10334) retired4 x1
    (BitVec.ofNat 64 0x14334)
  have destinationEq : destination = BitVec.ofNat 64 args.finalResultBase := by
    simp only [destination, iTypeResult, DecodeInlineArgs.finalResultBase]
    rw [show sign_extend (0x020#12) = (BitVec.ofNat 64 0x20) by decide,
      ← BitVec.ofNat_add]
  have sourceEq : source = BitVec.ofNat 64 args.firstTemporaryResultBase := by
    simp only [source, iTypeResult, DecodeInlineArgs.firstTemporaryResultBase]
    rw [show sign_extend (0x360#12) = (BitVec.ofNat 64 0x360) by decide,
      ← BitVec.ofNat_add]
  have lengthEq : length = BitVec.ofNat 64 832 := by
    simp [length, iTypeResult]
    decide
  have memory4 : s4.mem = state.mem := by
    simp [s4, s3, s2, s1, afterRegisterWrite_mem]
  have region1 := decodeInline_owned_in_execution_region (0x10328, 0x02010513)
    (by simp [decodeInlineOwnedInstructionWords])
  have region2 := decodeInline_owned_in_execution_region (0x1032c, 0x36010593)
    (by simp [decodeInlineOwnedInstructionWords])
  have region3 := decodeInline_owned_in_execution_region (0x10330, 0x34000613)
    (by simp [decodeInlineOwnedInstructionWords])
  have region4 := decodeInline_owned_in_execution_region (0x10334, 0x00004097)
    (by simp [decodeInlineOwnedInstructionWords])
  have notExit1 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10328) := by
    simp [DecodeInlineExit, phase, success]
  have notExit2 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x1032c) := by
    simp [DecodeInlineExit, phase, success]
  have notExit3 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10330) := by
    simp [DecodeInlineExit, phase, success]
  have notExit4 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10334) := by
    simp [DecodeInlineExit, phase, success]
  have prefix1 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary fromStep 1 state s1 :=
    ConfinedPrefix.ownStep atPc region1 notExit1 (by simpa [s1, destination] using run1)
  have prefix2 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep pc1 region2 notExit2 (by simpa [s2, source] using run2)
  have prefix3 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep pc2 region3 notExit3 (by simpa [s3, length] using run3)
  have prefix4 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep pc3 region4 notExit4 (by simpa [s4] using run4)
  have completePrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary fromStep 4 state s4 := by
    have firstTwo := ConfinedPrefix.trans prefix1 prefix2
    have firstThree := ConfinedPrefix.trans firstTwo (by simpa using prefix3)
    have allFour := ConfinedPrefix.trans firstThree (by simpa using prefix4)
    simpa using allFour
  refine ⟨s4, ?_, completePrefix, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Trace.step fromStep 3 state s1 s4 (by simpa [s1, destination] using run1) ?_
    refine Trace.step (fromStep + 1) 2 s1 s2 s4 (by simpa [s2, source] using run2) ?_
    refine Trace.step (fromStep + 2) 1 s2 s3 s4 (by simpa [s3, length] using run3) ?_
    exact Trace.one (fromStep + 3) s3 s4 (by simpa [s4] using run4)
  · simpa [s4] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x10334) retired4 x1
      (BitVec.ofNat 64 0x14334)
  · simp [s4, s3, s2, s1, destinationEq, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [s4, s3, s2, sourceEq, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [s4, s3, lengthEq, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · exact Agree.trans agree3
      (afterRegisterWrite_agree_of (by simp [decoderPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved]))
  · exact afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x10334) retired4 x1
      (BitVec.ofNat 64 0x14334)
  · simpa [memory4] using code
  · apply canonicalPostEntry_of_mem_eq args.firstRawArgs
      (Contracts.meaningDecodeRaw args.bytes) rfl memory4
    exact post

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
      Nonempty (CallTransfer
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
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
    tagRun, tagPc, tagCode, tagAgree, tagCounter, -, tagValue, -⟩ :=
    decodeInline_first_through_result_tag contract fromStep args state pre phase
  have internalTag : Contracts.decodeInternalResultTag
      (Contracts.meaningDecodeRaw args.bytes) = 0 := by
    simp [success, Contracts.decodeInternalResultTag]
  have tagRunZero : Runs (try_step (fromStep + 7 + childUsed) false) resumed
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64)) false := by
    simpa [internalTag] using tagRun
  have tagPcZero : (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
      (0#64)).regs.get? PC = some (BitVec.ofNat 64 0x10324) := by
    simpa [internalTag] using tagPc
  have tagCodeZero : Contracts.canonicalContractParams.env.CodeIntact
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64)) := by
    simpa [internalTag] using tagCode
  have tagAgreeZero : Agree decoderPreserved state
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64)) := by
    simpa [internalTag] using tagAgree
  have tagCounterZero : RetiredCounterPresent
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64)) := by
    simpa [internalTag] using tagCounter
  have tagValueZero : (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
      (0#64)).regs.get? x10 = some (0#64) := by
    simpa [internalTag] using tagValue
  obtain ⟨branchRetired, branchRun, branchPc⟩ := decodeInline_first_success_branch_step
    (fromStep + 8 + childUsed) args state
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64)) pre
      tagCodeZero tagAgreeZero tagCounterZero tagPcZero tagValueZero
  exact ⟨beforeCall, childUsed, resumed, tagRetired, branchRetired, parentTrace, bound,
    transfer, tagRunZero, branchRun, branchPc⟩

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
      ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep (childUsed + 13) state final := by
  obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, parentPrefix, bound, transfer,
    tagRun, tagPc, tagCode, tagAgree, tagCounter, tagStackRaw, tagValue, tagPost⟩ :=
    decodeInline_first_through_result_tag contract fromStep args state pre phase
  have internalTag : Contracts.decodeInternalResultTag
      (Contracts.meaningDecodeRaw args.bytes) = 0 := by
    simp [success, Contracts.decodeInternalResultTag]
  let tagState := afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64)
  have tagRunZero : Runs (try_step (fromStep + 7 + childUsed) false) resumed tagState false := by
    simpa [tagState, internalTag] using tagRun
  have tagPcZero : tagState.regs.get? PC = some (BitVec.ofNat 64 0x10324) := by
    simpa [tagState, internalTag] using tagPc
  have tagCodeZero : Contracts.canonicalContractParams.env.CodeIntact tagState := by
    simpa [tagState, internalTag] using tagCode
  have tagAgreeZero : Agree decoderPreserved state tagState := by
    simpa [tagState, internalTag] using tagAgree
  have tagCounterZero : RetiredCounterPresent tagState := by
    simpa [tagState, internalTag] using tagCounter
  have tagStack : tagState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simpa [tagState, internalTag] using tagStackRaw
  have tagValueZero : tagState.regs.get? x10 = some (0#64) := by
    simpa [tagState, internalTag] using tagValue
  have tagPostZero : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (.ok value) state tagState := by
    simpa [tagState, success] using tagPost
  obtain ⟨branchRetired, branchRun, branchPc⟩ := decodeInline_first_success_branch_step
    (fromStep + 8 + childUsed) args state tagState pre tagCodeZero tagAgreeZero tagCounterZero
    tagPcZero tagValueZero
  let branchState := decodeInlineFirstSuccessBranchAfter tagState branchRetired
  have branchMemory : branchState.mem = tagState.mem := by
    rfl
  have branchCode : Contracts.canonicalContractParams.env.CodeIntact branchState := by
    simpa [branchMemory] using tagCodeZero
  have branchPreserves : Agree decoderPreserved tagState branchState := by
    intro register preserved
    have notRetired : minstret ≠ register := by
      intro equal
      subst register
      simp [decoderPreserved, platformPreserved] at preserved
    have notPc : PC ≠ register := by
      intro equal
      subst register
      simp [decoderPreserved, platformPreserved] at preserved
    have notNextPc : nextPC ≠ register := by
      intro equal
      subst register
      simp [decoderPreserved, platformPreserved] at preserved
    have notIncrement : minstret_increment ≠ register := by
      intro equal
      subst register
      simp [decoderPreserved, platformPreserved] at preserved
    simp [branchState, decodeInlineFirstSuccessBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, notRetired, notPc, notNextPc, notIncrement]
  have branchAgree : Agree decoderPreserved state branchState :=
    Agree.trans tagAgreeZero branchPreserves
  have branchCounter : RetiredCounterPresent branchState := by
    refine ⟨Sail.BitVec.addInt branchRetired 1, ?_⟩
    simp [branchState, decodeInlineFirstSuccessBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]
  have branchStack : branchState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [branchState, decodeInlineFirstSuccessBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tagStack]
  have branchPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (.ok value) state branchState := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (.ok value) rfl branchMemory
    exact tagPostZero
  obtain ⟨final, setupTrace, setupPrefix, finalPc, finalDestination, finalSource, finalLength,
    finalAgree, finalCounter, finalCode, finalPost⟩ :=
    decodeInline_first_success_copy_setup (fromStep + 9 + childUsed) args state branchState pre
      phase value success branchAgree branchCounter branchCode branchPc branchStack
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
      rootBytes, rootSize, rootMemory⟩
  obtain ⟨callTransfer⟩ := transfer
  have callPrefix := ConfinedPrefix.ofCall callTransfer
  have tagRegion := decodeInline_owned_in_execution_region (0x10320, 0x6a015503)
    (by simp [decodeInlineOwnedInstructionWords])
  have branchRegion := decodeInline_owned_in_execution_region (0x10324, 0x04051c63)
    (by simp [decodeInlineOwnedInstructionWords])
  have tagNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10320) := by
    simp [DecodeInlineExit, phase, success]
  have branchNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10324) := by
    simp [DecodeInlineExit, phase, success]
  have resumePc : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10320) := by
    have returnPcEq : callTransfer.returnPc = BitVec.ofNat 64 0x10320 := by
      apply BitVec.eq_of_toNat_eq
      simpa [decodeRawFirstAttemptCall] using callTransfer.returnMatches
    simpa [returnPcEq] using callTransfer.atResume
  have tagPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 7 + childUsed) 1 resumed tagState :=
    ConfinedPrefix.ownStep resumePc tagRegion tagNotExit tagRunZero
  have branchPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 8 + childUsed) 1 tagState branchState :=
    ConfinedPrefix.ownStep tagPcZero branchRegion branchNotExit
      (by simpa [branchState] using branchRun)
  have finalExit : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
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
  have afterCallCount : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 5) (childUsed + 8)
      beforeCall final := by
    have countEq : 1 + childUsed + 1 + 6 = childUsed + 8 := by omega
    rw [countEq] at afterCall
    exact afterCall
  have complete := parentPrefix (childUsed + 8) final (by
    exact afterCallCount)
  refine ⟨childUsed, final, bound, exit, post, ?_⟩
  have countEq : 5 + (childUsed + 8) = childUsed + 13 := by omega
  rw [countEq] at complete
  exact complete

/-- An unsuccessful first `decodeRaw` stops at the outcome-selected generated exit `0x10324`.
The tag-load instruction is executed; the outgoing branch itself is not part of this path. -/
theorem decodeInline_first_error_reaches_post
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first)
    (error : Contracts.DecodeError)
    (failed : Contracts.meaningDecodeRaw args.bytes = .error error) :
    ∃ beforeCall childUsed resumed tagRetired,
      Trace fromStep 5 state beforeCall ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      Nonempty (CallTransfer
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed) ∧
      Runs (try_step (fromStep + 7 + childUsed) false) resumed
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) false ∧
      DecodeInlineExit args (BitVec.ofNat 64 0x10324) ∧
      DecodeInlineFirstPost args state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) ∧
      ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep (childUsed + 8) state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) := by
  obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, parentPrefix, bound, transfer,
    tagRun, tagPc, -, -, -, -, tagValue, tagPost⟩ :=
    decodeInline_first_through_result_tag contract fromStep args state pre phase
  have tagRunError : Runs (try_step (fromStep + 7 + childUsed) false) resumed
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) false := by
    simpa [failed] using tagRun
  have tagPcError : (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
      (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))).regs.get? PC =
      some (BitVec.ofNat 64 0x10324) := by
    simpa [failed] using tagPc
  have tagValueError : (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
      (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))).regs.get? x10 =
      some (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))) := by
    simpa [failed] using tagValue
  have tagPostError : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (.error error) state
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) := by
    simpa [failed] using tagPost
  have exit : DecodeInlineExit args (BitVec.ofNat 64 0x10324) := by
    simp [DecodeInlineExit, phase, failed]
  have post : DecodeInlineFirstPost args state
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) := by
    simp only [DecodeInlineFirstPost, failed]
    exact ⟨tagPostError, tagPcError, tagValueError⟩
  obtain ⟨callTransfer⟩ := transfer
  have resumePc : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10320) := by
    have returnPcEq : callTransfer.returnPc = BitVec.ofNat 64 0x10320 := by
      apply BitVec.eq_of_toNat_eq
      simpa [decodeRawFirstAttemptCall] using callTransfer.returnMatches
    simpa [returnPcEq] using callTransfer.atResume
  have tagRegion := decodeInline_owned_in_execution_region (0x10320, 0x6a015503)
    (by simp [decodeInlineOwnedInstructionWords])
  have tagNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10320) := by
    simp [DecodeInlineExit, phase, failed]
  let afterTag := afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
    (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))
  have tail : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 7 + childUsed) 1 resumed afterTag := by
    apply ScopedTrace.ownStep (fromStep + 7 + childUsed) 0 (BitVec.ofNat 64 0x10320)
      resumed afterTag afterTag resumePc tagRegion tagNotExit
    · simpa [afterTag] using tagRunError
    · exact ScopedTrace.exitAt (fromStep + 7 + childUsed + 1) afterTag
        (BitVec.ofNat 64 0x10324) (by simpa [afterTag] using tagPcError) exit
  have fromCall : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 5) (childUsed + 3)
      beforeCall afterTag := by
    have shiftedTail : ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary
        (fromStep + 5 + 1 + childUsed + 1) 1 resumed afterTag := by
      have stepEq : fromStep + 5 + 1 + childUsed + 1 = fromStep + 7 + childUsed := by
        omega
      rw [stepEq]
      exact tail
    have callTrace := ScopedTrace.callStep (fromStep + 5) childUsed 1
      decodeRawFirstAttemptCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw beforeCall resumed afterTag callTransfer
      shiftedTail
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using callTrace
  have completeTrace := parentPrefix (childUsed + 3) afterTag fromCall
  have scopedFinal : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary fromStep (childUsed + 8) state afterTag := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completeTrace
  exact ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, bound, ⟨callTransfer⟩,
    tagRunError, exit, post, by simpa [afterTag] using scopedFinal⟩

/-- The complete first-phase arm of the Level 3 contract. This is the single scope showing the
conditional `decodeRaw` summary stitched to all parent-owned Sail execution and the selected semantic
postcondition. No other child condition is used on this phase. -/
theorem decodeInline_first_level3_relation (contract : CompiledDecodeRawInstanceContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) (phase : args.phase = .first) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep used before after ∧
      DecodeInlinePost args before after := by
  cases resultEq : Contracts.meaningDecodeRaw args.bytes with
  | ok value =>
      obtain ⟨childUsed, final, childBound, exit, post, trace⟩ :=
        decodeInline_first_success_reaches_post contract fromStep args before pre phase value resultEq
      refine ⟨childUsed + 13, final, ?_, trace, ?_⟩
      · unfold decodeInlineStepBound
        have rawBound := childBound
        have stepBoundEq : compiledDecodeRawContract.binding.stepBound args.firstRawArgs =
            16384 + 512 * args.bytes.size := rfl
        rw [stepBoundEq] at rawBound
        omega
      · simpa [DecodeInlinePost, phase] using post
  | error error =>
      obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, childBound, transfer,
        tagRun, exit, post, trace⟩ :=
        decodeInline_first_error_reaches_post contract fromStep args before pre phase error resultEq
      refine ⟨childUsed + 8,
        afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))), ?_, trace, ?_⟩
      · unfold decodeInlineStepBound
        have rawBound := childBound
        have stepBoundEq : compiledDecodeRawContract.binding.stepBound args.firstRawArgs =
            16384 + 512 * args.bytes.size := rfl
        rw [stepBoundEq] at rawBound
        omega
      · simpa [DecodeInlinePost, phase] using post

/-! ## Retry phase: mandatory entry branch -/

def decodeInlineRetryEntryAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10380))
    (BitVec.ofNat 64 0x10384) retired

/-- The retry precondition fixes both compared tags to `2`, so the generated
`bne a0, a1, 0x103fc` must fall through into the retry body. -/
theorem decodeInline_retry_entry_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) :
    ∃ retired,
      Runs (try_step stepNo false) state (decodeInlineRetryEntryAfter state retired) false ∧
      (decodeInlineRetryEntryAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10384) := by
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10380) := by
    simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry
  have pcIn := decodeInline_owned_in_execution_region (0x10380, 0x06b51e63)
    (by simp [decodeInlineOwnedInstructionWords])
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10380) 0x63#8 0x1e#8 0xb5#8 0x06#8 :=
    fetchFileInstruction state 0x10380 0x63 0x1e 0xb5 0x06 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine (Agree.refl state)
    (BitVec.ofNat 64 0x10380) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters pre.machine.normal (Agree.refl state) pre.machine.retiredCounter
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have wordEq : fetchWord 0x63#8 0x1e#8 0xb5#8 0x06#8 =
      (0x06b51e63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x1e#8 0xb5#8 0x06#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x7c#13, .Regidx 11#5, .Regidx 10#5, .BNE)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10380)
  obtain ⟨-, tagA0, tagA1⟩ := pre.retryReason phase
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 2) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tagA0]
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 2) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tagA1]
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BNE)
      executeState executeState false := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState (BitVec.ofNat 64 2) x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState (BitVec.ofNat 64 2) x11AtExecute) ?_
    rfl
  have run := tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10380) retired
    (0x7c#13) (.Regidx 11#5) (.Regidx 10#5) .BNE inhibit config
    0x63#8 0x1e#8 0xb5#8 0x06#8 fetch noMMIO fetchBytes interrupts
    (by unfold BaseInstructionEncoding; decide) decode notExpected condition hartRead inhibitRead
    configRead notInhibited machineEnabled retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [decodeInlineRetryEntryAfter] using run
  · simp [decodeInlineRetryEntryAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]

end BinaryFv.Zesu.MachineExecution
