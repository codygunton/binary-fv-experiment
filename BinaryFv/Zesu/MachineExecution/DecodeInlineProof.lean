import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge
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
    (0x1038c, 0xffc50613), (0x103c0, 0x00a76533),
    (0x103c4, 0x04a69e63),
    (0x103c8, 0x00440613), (0x103cc, 0x6b010513),
    (0x103d0, 0x01010593), (0x103d4, 0x00000097),
    (0x103d8, 0x070080e7), (0x103dc, 0x02010513),
    (0x103e0, 0x6b010593), (0x103e4, 0x34000613),
    (0x103e8, 0x00004097), (0x103ec, 0xad0080e7),
    (0x103f0, 0x00001537), (0x103f4, 0x00a10533)]

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

/-- A generated execution member becomes a fetch premise only after its concrete alignment check. -/
theorem decoderFetchPc_of_member {instructionPcs : BitVec 64 → Prop} {pc : BitVec 64}
    (member : instructionPcs pc) (aligned : pc.toNat % 4 = 0) :
    DecoderFetchPc instructionPcs pc := ⟨member, aligned⟩

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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10308, 0x36010513)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have code := hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10308) 0x13#8 0x05#8 0x01#8 0x36#8 :=
    fetchInstruction state 0x10308 0x13 0x05 0x01 0x36 code
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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x1030c, 0x01010593)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1030c) 0x93#8 0x05#8 0x01#8 0x01#8 :=
    fetchInstruction state 0x1030c 0x93 0x05 0x01 0x01 code
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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10310, 0x00040613)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10310) 0x13#8 0x06#8 0x04#8 0x00#8 :=
    fetchInstruction state 0x10310 0x13 0x06 0x04 0x00 code
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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10314, 0x00048693)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10314) 0x93#8 0x86#8 0x04#8 0x00#8 :=
    fetchInstruction state 0x10314 0x93 0x86 0x04 0x00 code
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
      after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
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
  have globals4 : s4.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [s4, s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.globalsValue]
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
  refine ⟨s4, ?_, combinedPrefix, pc4, result4, allocator4, input4, length4, stack4, ?_, ?_, ?_,
    agree4, rfl, afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x10314) retired4 x13 length⟩
  · refine Trace.step fromStep 3 state s1 s4 (by simpa [s1, firstResult] using run1) ?_
    refine Trace.step (fromStep + 1) 2 s1 s2 s4 (by simpa [s2, allocator] using run2) ?_
    refine Trace.step (fromStep + 2) 1 s2 s3 s4 (by simpa [s3, input] using run3) ?_
    exact Trace.one (fromStep + 3) s3 s4 (by simpa [s4, length] using run4)
  · simp [s4, s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.inputValue]
  · simp [s4, s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.lengthValue]
  · exact globals4

theorem decodeInline_first_call_page_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree platformPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10318)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10318) retired x1
          (BitVec.ofNat 64 0x10318)) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10318, 0x00000097)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10318) 0x97#8 0x00#8 0x00#8 0x00#8 :=
    fetchInstruction state 0x10318 0x97 0x00 0x00 0x00 code
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
      beforeCall.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      beforeCall.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Agree decoderPreserved state beforeCall ∧ beforeCall.mem = state.mem ∧
      RetiredCounterPresent beforeCall := by
  obtain ⟨afterArgs, argsTrace, argsPrefix, argsPc, resultArgs, allocatorArgs, inputArgs,
    lengthArgs, stackArgs, inputBaseArgs, inputLengthArgs, globalsArgs, argsAgree, argsMemory, argsRetired⟩ :=
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
  have inputBaseBefore : beforeCall.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, inputBaseArgs]
  have inputLengthBefore : beforeCall.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, inputLengthArgs]
  have globalsBefore : beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, globalsArgs]
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
    lengthBefore, stackBefore, inputBaseBefore, inputLengthBefore, globalsBefore,
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
    (inputLength : state.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size))
    (inputBase : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase))
    (lengthBase : state.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size))
    (globalsBase : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)) :
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
      (decodeInlineFirstCallAfter state retired).regs.get? x8 =
        some (BitVec.ofNat 64 args.inputBase) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x9 =
        some (BitVec.ofNat 64 args.bytes.size) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x18 =
        some (BitVec.ofNat 64 0x4215020) ∧
      Agree decoderPreserved state (decodeInlineFirstCallAfter state retired) ∧
      (decodeInlineFirstCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (decodeInlineFirstCallAfter state retired) := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x1031c, 0x12c080e7)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1031c) 0xe7#8 0x80#8 0xc0#8 0x12#8 :=
    fetchInstruction state 0x1031c 0xe7 0x80 0xc0 0x12 code
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
  have inputBaseAfter : (decodeInlineFirstCallAfter state retired).regs.get? x8 =
      some (BitVec.ofNat 64 args.inputBase) :=
    (preserveGeneral x8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      inputBase
  have inputLengthAfter : (decodeInlineFirstCallAfter state retired).regs.get? x9 =
      some (BitVec.ofNat 64 args.bytes.size) :=
    (preserveGeneral x9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      lengthBase
  have globalsAfter : (decodeInlineFirstCallAfter state retired).regs.get? x18 =
      some (BitVec.ofNat 64 0x4215020) :=
    (preserveGeneral x18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      globalsBase
  refine ⟨retired, run, pcAfter, linkAfter, resultAfter, allocatorAfter, inputAfter, lengthAfter,
    inputBaseAfter, inputLengthAfter, globalsAfter,
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
    inputPointer, inputLength, -, beforeInputBase, beforeInputLength, beforeGlobals, beforeAgree, beforeMemory,
    beforeRetired⟩ :=
    decodeInline_first_before_decodeRaw_call fromStep args state pre phase
  obtain ⟨retired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, -, -, -, callAgree, callMemory, childRetired⟩ :=
    decodeInline_first_decodeRaw_call_step (fromStep + 5) args state beforeCall pre
      beforeAgree beforeMemory beforeRetired callPc callBase resultPointer allocatorPointer
      inputPointer inputLength beforeInputBase beforeInputLength beforeGlobals
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

def decodeRawReturnAfter (returnPc : BitVec 64) (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10530) returnPc)
    returnPc retired

theorem decodeRawReturnAfter_agree (returnPc : BitVec 64) (state : State)
    (retired : BitVec 64) :
    Agree decoderPreserved state (decodeRawReturnAfter returnPc state retired) := by
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

theorem decodeRawReturnAfter_mem (returnPc : BitVec 64) (state : State) (retired : BitVec 64) :
    (decodeRawReturnAfter returnPc state retired).mem = state.mem := rfl

theorem decodeRawReturnAfter_retired (returnPc : BitVec 64) (state : State)
    (retired : BitVec 64) :
    RetiredCounterPresent (decodeRawReturnAfter returnPc state retired) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [decodeRawReturnAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]

/-- Execute the selected emitted child's real `ret` after its strengthened contract establishes the
link and machine frame required by that instruction. -/
theorem decodeRaw_return_step (stepNo : Nat) (rawArgs : Contracts.EntryArgs)
    (returnPc : BitVec 64) (childEntry childExit : State) {childFrom childUsed : Nat}
    (returnTarget : Sail.BitVec.update returnPc 0 0#1 = returnPc)
    (returnBit1 : Sail.BitVec.access returnPc 1 = 0#1)
    (childPre : compiledDecodeRawContract.binding.entry rawArgs childEntry)
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
      (Contracts.functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
      childFrom childUsed childEntry childExit)
    (entryLink : childEntry.regs.get? x1 = some returnPc)
    (childPost : compiledDecodeRawContract.binding.exit rawArgs
      (compiledDecodeRawContract.spec.meaning rawArgs) childEntry childExit) :
    ∃ retired,
      Runs (try_step stepNo false) childExit
        (decodeRawReturnAfter returnPc childExit retired) false ∧
      (decodeRawReturnAfter returnPc childExit retired).regs.get? PC = some returnPc := by
  rcases childPost with ⟨sourcePost, childFrame, childRetired, childPayload, _childSaveArea⟩
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
  have pcIn : DecoderFetchPc (functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decodeRaw) (BitVec.ofNat 64 0x10530) := by
    refine ⟨?_, by native_decide⟩
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
  have exitLink : childExit.regs.get? x1 = some returnPc :=
    (childFrame x1 (by simp [decodeRawCallerPreserved, platformPreserved])).trans entryLink
  have sourceRead : executeState.regs.get? x1 = some returnPc := by
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
    (.Regidx 1#5) (BitVec.ofNat 64 0x10534) returnPc inhibit config
    0x67#8 0x80#8 0x00#8 0x00#8 (_get_Misa_C misaBits == 1#1) fetch noMMIO fetchBytes
    interrupts (by unfold BaseInstructionEncoding; decide) decode notExpected helpElp
    (get_next_pc_run executeState _ linkRead) (rX_bits_run_x1 executeState _ sourceRead)
    returnBit1 zca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [decodeRawReturnAfter, returnTarget] using retRun
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
      resumed.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      resumed.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
        Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
        state resumed ∧
      DecodeInlineCallerSaveArea args state resumed := by
  obtain ⟨beforeCall, parentTrace, parentPrefix, callPc, callBase, resultPointer, allocatorPointer,
    inputPointer, inputLength, beforeStack, beforeInputBase, beforeInputLength, beforeGlobals, beforeAgree,
    beforeMemory, beforeRetired⟩ :=
    decodeInline_first_before_decodeRaw_call fromStep args state pre phase
  obtain ⟨callRetired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, childInputBase, childInputLength, childGlobals, callAgree, callMemory, childRetired⟩ :=
    decodeInline_first_decodeRaw_call_step (fromStep + 5) args state beforeCall pre
      beforeAgree beforeMemory beforeRetired callPc callBase resultPointer allocatorPointer
      inputPointer inputLength beforeInputBase beforeInputLength beforeGlobals
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
    decodeRaw_return_step (fromStep + 6 + childUsed) args.firstRawArgs
      (BitVec.ofNat 64 0x10320) childEntry childExit (by decide) (by decide)
      childPre childTrace childLink childPost
  let resumed := decodeRawReturnAfter (BitVec.ofNat 64 0x10320) childExit returnRetired
  rcases childPost with ⟨sourcePost, childFrame, childCounter, childPayload, childSaveArea⟩
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
        simpa [resumed] using
          (decodeRawReturnAfter_agree (BitVec.ofNat 64 0x10320) childExit returnRetired)))
  have exitStack : childExit.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (childFrame x2 (by simp [decodeRawCallerPreserved])).trans childStack
  have resumedStack : resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [resumed, decodeRawReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert, exitStack]
  have exitInputBase : childExit.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    (childFrame x8 (by simp [decodeRawCallerPreserved])).trans childInputBase
  have exitInputLength : childExit.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    (childFrame x9 (by simp [decodeRawCallerPreserved])).trans childInputLength
  have resumedInputBase : resumed.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [resumed, decodeRawReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert, exitInputBase]
  have resumedInputLength : resumed.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [resumed, decodeRawReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert, exitInputLength]
  have exitGlobals : childExit.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (childFrame x18 (by simp [decodeRawCallerPreserved])).trans childGlobals
  have resumedGlobals : resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [resumed, decodeRawReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert, exitGlobals]
  have resumedPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
      state resumed := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (Contracts.meaningDecodeRaw args.bytes)
      childMemory.symm
        (decodeRawReturnAfter_mem (BitVec.ofNat 64 0x10320) childExit returnRetired)
    exact ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have resumedSaveArea : DecodeInlineCallerSaveArea args state resumed := by
    intro index bound
    rw [decodeRawReturnAfter_mem (BitVec.ofNat 64 0x10320) childExit returnRetired]
    calc
      childExit.mem.get? (args.stackBase + 0xa00 + index) =
          childEntry.mem.get? (args.stackBase + 0xa00 + index) := by
        simpa [DecodeInlineCallerSaveArea, DecodeRawCallerSaveArea,
          DecodeInlineArgs.firstRawArgs, DecodeInlineArgs.allocatorBase, Nat.add_assoc] using
          childSaveArea index bound
      _ = state.mem.get? (args.stackBase + 0xa00 + index) := by rw [childMemory]
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
        childFrame, childCounter, childPayload, childSaveArea⟩
    · simpa [resumed, Nat.add_assoc] using returnRun
    · simpa [resumed] using atResume
  exact ⟨beforeCall, childUsed, resumed, parentTrace, parentPrefix, bound, ⟨transfer⟩, resumedStatus,
    resumedCode, resumedAgree, by simpa [resumed] using
      decodeRawReturnAfter_retired (BitVec.ofNat 64 0x10320) childExit returnRetired,
      resumedStack, resumedInputBase, resumedInputLength, resumedGlobals, resumedPost, resumedSaveArea⟩

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
    (globalsRead : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10320, 0x6a015503)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10320) 0x03#8 0x55#8 0x01#8 0x6a#8 :=
    fetchInstruction state 0x10320 0x03 0x55 0x01 0x6a image
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
    refine ⟨by decide, ?_, ?_⟩
    · simpa [addressNat] using addressFits
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
  have aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 2 = true := by
    have addressMod : address.toNat % 2 = 0 := by
      rw [addressNat]
      have stackAligned := pre.stackAligned
      omega
    simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, ← Int.ofNat_tmod,
      addressMod]
    rfl
  have physicalAligned : is_aligned_paddr (physaddr.Physaddr address) 2 = true := by
    simpa [is_aligned_paddr, is_aligned_vaddr] using aligned
  obtain ⟨physAccess, loadNoMMIO⟩ :=
    pre.machine.dataAccess.load executeState address 2 executeAgree allowed physicalAligned
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
        x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        x10 = some (BitVec.ofNat 64
          (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes))) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
        Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes) state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      DecodeInlineCallerSaveArea args state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) := by
  obtain ⟨beforeCall, childUsed, resumed, parentTrace, parentPrefix, bound, transfer, status, code,
    resumedAgree, resumedRetired, resumedStack, resumedInputBase, resumedInputLength, resumedGlobals,
    resumedPost, resumedSaveArea⟩ :=
    decodeInline_first_call_transfer contract fromStep args state pre phase
  obtain ⟨callTransfer⟩ := transfer
  have resumePc : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10320) := by
    have returnPcEq : callTransfer.returnPc = BitVec.ofNat 64 0x10320 := by
      apply BitVec.eq_of_toNat_eq
      simpa [decodeRawFirstAttemptCall] using callTransfer.returnMatches
    simpa [returnPcEq] using callTransfer.atResume
  obtain ⟨retired, tagRun⟩ := decodeInline_first_result_tag_step
    (fromStep + 7 + childUsed) args state resumed pre status code resumedAgree resumedRetired
      resumedStack resumedGlobals resumePc
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
  have afterInputBase : afterTag.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [afterTag, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resumedInputBase]
  have afterInputLength : afterTag.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [afterTag, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resumedInputLength]
  have afterGlobals : afterTag.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [afterTag, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resumedGlobals]
  have afterPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
      state afterTag := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (Contracts.meaningDecodeRaw args.bytes)
      rfl (afterRegisterWrite_mem resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue)
    exact resumedPost
  have afterSaveArea : DecodeInlineCallerSaveArea args state afterTag := by
    simpa [afterTag, afterRegisterWrite_mem] using resumedSaveArea
  refine ⟨beforeCall, childUsed, resumed, retired, parentTrace, parentPrefix, bound, ⟨callTransfer⟩,
    by simpa [afterTag, tagValue] using tagRun, ?_, afterCode,
    Agree.trans resumedAgree tagAgree, ?_, afterStack, afterInputBase, afterInputLength, afterX10,
    afterGlobals,
    afterPost, afterSaveArea⟩
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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10324, 0x04051c63)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10324) 0x63#8 0x1c#8 0x05#8 0x04#8 :=
    fetchInstruction state 0x10324 0x63 0x1c 0x05 0x04 image
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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10328, 0x02010513)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10328) 0x13#8 0x05#8 0x01#8 0x02#8 :=
    fetchInstruction state 0x10328 0x13 0x05 0x01 0x02 image
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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x1032c, 0x36010593)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1032c) 0x93#8 0x05#8 0x01#8 0x36#8 :=
    fetchInstruction state 0x1032c 0x93 0x05 0x01 0x36 image
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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10330, 0x34000613)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10330) 0x13#8 0x06#8 0x00#8 0x34#8 :=
    fetchInstruction state 0x10330 0x13 0x06 0x00 0x34 image
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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10334, 0x00004097)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10334) 0x97#8 0x40#8 0x00#8 0x00#8 :=
    fetchInstruction state 0x10334 0x97 0x40 0x00 0x00 image
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
    (globals : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
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
      after.regs.get? x1 = some (BitVec.ofNat 64 0x14334) ∧
      after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      Agree decoderPreserved baseState after ∧
      RetiredCounterPresent after ∧
      Contracts.canonicalContractParams.env.CodeIntact after ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
        Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
        baseState after ∧
      after.mem = state.mem := by
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
  have globals4 : s4.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [s4, s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, globals]
  have stack4 : s4.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [s4, s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
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
  refine ⟨s4, ?_, completePrefix, ?_, ?_, ?_, ?_, ?_, ?_, stack4, ?_, ?_, ?_, ?_, ?_⟩
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
  · simp [s4, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  · exact globals4
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
  · simp [s4, s3, s2, s1, afterRegisterWrite_mem]

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
    tagRun, tagPc, tagCode, tagAgree, tagCounter, -, -, -, tagValue, -, -, -⟩ :=
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
  have tagGlobalsZero : tagState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simpa [tagState, internalTag] using tagGlobals
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
  have branchGlobals : branchState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [branchState, decodeInlineFirstSuccessBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tagGlobalsZero]
  have branchPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (.ok value) state branchState := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (.ok value) rfl branchMemory
    exact tagPostZero
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
  refine ⟨childUsed, final, bound, exit, post, ?_,
    ⟨finalAgree, finalCounter, finalCode, finalGlobals.trans pre.globalsValue.symm⟩, finalStack,
    finalSaveArea⟩
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
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) ∧
      DecodeInlineMachinePost state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))).regs.get? x8 =
          some (BitVec.ofNat 64 args.inputBase) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))).regs.get? x9 =
          some (BitVec.ofNat 64 args.bytes.size) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))).regs.get? x2 =
          some (BitVec.ofNat 64 args.stackBase) ∧
      DecodeInlineCallerSaveArea args state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) := by
  obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, parentPrefix, bound, transfer,
    tagRun, tagPc, tagCode, tagAgree, tagCounter, tagStackRaw, tagInputBase, tagInputLength, tagValue,
    tagGlobals, tagPost, tagSaveArea⟩ :=
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
  have tagStackError : (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
      (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))).regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) := by
    simpa [failed] using tagStackRaw
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
    tagRunError, exit, post, by simpa [afterTag] using scopedFinal,
    by simpa [afterTag, failed] using
      (show DecodeInlineMachinePost state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag
          (Contracts.meaningDecodeRaw args.bytes)))) from
        ⟨tagAgree, tagCounter, tagCode, tagGlobals.trans pre.globalsValue.symm⟩),
      by simpa [afterTag, failed] using tagInputBase,
    by simpa [afterTag, failed] using tagInputLength,
    by simpa [afterTag] using tagStackError,
    by simpa [afterTag, afterRegisterWrite_mem] using tagSaveArea⟩

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
      DecodeInlinePost args before after ∧
      DecodeInlineMachinePost before after ∧
      DecodeInlineOutgoingFrame args after := by
  cases resultEq : Contracts.meaningDecodeRaw args.bytes with
  | ok value =>
      obtain ⟨childUsed, final, childBound, exit, post, trace, machinePost, outgoingStack⟩ :=
        decodeInline_first_success_reaches_post contract fromStep args before pre phase value resultEq
      refine ⟨childUsed + 13, final, ?_, trace, ?_, machinePost, ?_⟩
      · unfold decodeInlineStepBound
        have rawBound := childBound
        have stepBoundEq : compiledDecodeRawContract.binding.stepBound args.firstRawArgs =
            16384 + 512 * args.bytes.size := rfl
        rw [stepBoundEq] at rawBound
        omega
      · simpa [DecodeInlinePost, phase] using post
      · simpa [DecodeInlineOutgoingFrame, phase] using outgoingStack.1
  | error error =>
      obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, childBound, transfer,
        tagRun, exit, post, trace, machinePost, -, -, outgoingStack⟩ :=
        decodeInline_first_error_reaches_post contract fromStep args before pre phase error resultEq
      refine ⟨childUsed + 8,
        afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))), ?_, trace, ?_,
          machinePost, by simpa [DecodeInlineOutgoingFrame, phase] using outgoingStack.1⟩
      · unfold decodeInlineStepBound
        have rawBound := childBound
        have stepBoundEq : compiledDecodeRawContract.binding.stepBound args.firstRawArgs =
            16384 + 512 * args.bytes.size := rfl
        rw [stepBoundEq] at rawBound
        omega
      · simpa [DecodeInlinePost, phase] using post

/-- Companion result for the first Level 3 outcome.  It retains the wrapper save frame proved by
the selected `decodeRaw` call while leaving `decodeInline_first_level3_relation`'s existing
semantic interface unchanged. -/
theorem decodeInline_first_level3_save_area (contract : CompiledDecodeRawInstanceContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) (phase : args.phase = .first) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep used before after ∧
      DecodeInlinePost args before after ∧
      DecodeInlineMachinePost before after ∧
      DecodeInlineOutgoingFrame args after ∧
      DecodeInlineCallerSaveArea args before after := by
  cases resultEq : Contracts.meaningDecodeRaw args.bytes with
  | ok value =>
      obtain ⟨childUsed, final, childBound, _, post, trace, machinePost, outgoing⟩ :=
        decodeInline_first_success_reaches_post contract fromStep args before pre phase value resultEq
      refine ⟨childUsed + 13, final, ?_, trace, ?_, machinePost, ?_, outgoing.2⟩
      · unfold decodeInlineStepBound
        have rawBound := childBound
        have stepBoundEq : compiledDecodeRawContract.binding.stepBound args.firstRawArgs =
            16384 + 512 * args.bytes.size := rfl
        rw [stepBoundEq] at rawBound
        omega
      · simpa [DecodeInlinePost, phase] using post
      · simpa [DecodeInlineOutgoingFrame, phase] using outgoing.1
  | error error =>
      obtain ⟨_, childUsed, resumed, tagRetired, _, childBound, _, _, _, post, trace, machinePost,
        _, _, outgoing⟩ :=
        decodeInline_first_error_reaches_post contract fromStep args before pre phase error resultEq
      refine ⟨childUsed + 8,
        afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))), ?_, trace, ?_,
          machinePost, ?_, outgoing.2⟩
      · unfold decodeInlineStepBound
        have rawBound := childBound
        have stepBoundEq : compiledDecodeRawContract.binding.stepBound args.firstRawArgs =
            16384 + 512 * args.bytes.size := rfl
        rw [stepBoundEq] at rawBound
        omega
      · simpa [DecodeInlinePost, phase] using post
      · simpa [DecodeInlineOutgoingFrame, phase] using outgoing.1

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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10380, 0x06b51e63)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10380) 0x63#8 0x1e#8 0xb5#8 0x06#8 :=
    fetchInstruction state 0x10380 0x63 0x1e 0xb5 0x06 image
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

/-- Execute `li a0, -1`, the first parent-owned constant preparation instruction. -/
theorem decodeInline_retry_minus_one_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10384)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10384) retired x10
          (BitVec.ofNat 64 (2 ^ 64 - 1))) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10384, 0xfff00513)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10384) 0x13#8 0x05#8 0xf0#8 0xff#8 :=
    fetchInstruction state 0x10384 0x13 0x05 0xf0 0xff image
  have machine := pre.machine.mono agree retiredPresent
  have privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine :=
    machine.normal.2.1
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  have privilegeAfterIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
    simp [tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, privilegeRead]
  have mseccfgAfterIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits := by
    simp [tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, mseccfgRead]
  have wordEq : fetchWord 0x13#8 0x05#8 0xf0#8 0xff#8 =
      (0xfff00513 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x05#8 0xf0#8 0xff#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0xfff#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10384)
  have execute : Runs (execute (.ITYPE (0xfff#12, .Regidx 0#5, .Regidx 10#5, .ADDI)))
      executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 (2 ^ 64 - 1)) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0xfff#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI) _ _ _
    have resultEq : (0#64 + sign_extend (m := 64) 0xfff#12) =
        BitVec.ofNat 64 (2 ^ 64 - 1) := by native_decide
    rw [← resultEq]
    exact execute_ITYPE_addi_run executeState _ 0xfff#12 (.Regidx 0#5) (.Regidx 10#5)
      0#64 (rX_x0_run executeState) (wX_x10_run executeState _)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x10384) pcIn atPc 0x13#8 0x05#8 0xf0#8 0xff#8
    (.ITYPE (0xfff#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) x10
    (BitVec.ofNat 64 (2 ^ 64 - 1)) fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `slli a0, a0, 32`, producing `2^64 - 2^32`. -/
theorem decodeInline_retry_shift_constant_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10388))
    (constant : state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 1))) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10388) retired x10
          (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x10388, 0x02051513)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10388) 0x13#8 0x15#8 0x05#8 0x02#8 :=
    fetchInstruction state 0x10388 0x13 0x15 0x05 0x02 image
  have machine := pre.machine.mono agree retiredPresent
  have privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine :=
    machine.normal.2.1
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  have privilegeAfterIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
    simp [tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, privilegeRead]
  have mseccfgAfterIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits := by
    simp [tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, mseccfgRead]
  have wordEq : fetchWord 0x13#8 0x15#8 0x05#8 0x02#8 =
      (0x02051513 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x15#8 0x05#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (32#6, .Regidx 10#5, .Regidx 10#5, .SLLI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10388)
  have sourceAtExecute : executeState.regs.get? x10 =
      some (BitVec.ofNat 64 (2 ^ 64 - 1)) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, constant]
  have execute : Runs
      (execute (.SHIFTIOP (32#6, .Regidx 10#5, .Regidx 10#5, .SLLI))) executeState
      { executeState with regs :=
          executeState.regs.insert x10 (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) }
      (.Retire_Success ()) := by
    change Runs (execute_SHIFTIOP 32#6 (.Regidx 10#5) (.Regidx 10#5) .SLLI) _ _ _
    have resultEq : Sail.shift_bits_left (BitVec.ofNat 64 (2 ^ 64 - 1))
        (Sail.BitVec.extractLsb 32#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) =
        BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32) := by native_decide
    rw [← resultEq]
    exact execute_SHIFTIOP_slli_run executeState _ 32#6 (.Regidx 10#5) (.Regidx 10#5)
      (BitVec.ofNat 64 (2 ^ 64 - 1))
      (rX_bits_run_x10 executeState _ sourceAtExecute) (wX_x10_run executeState _)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x10388) pcIn atPc 0x13#8 0x15#8 0x05#8 0x02#8
    (.SHIFTIOP (32#6, .Regidx 10#5, .Regidx 10#5, .SLLI)) x10
    (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `addi a2, a0, -4`, completing the constants consumed by the prefix length gate. -/
theorem decodeInline_retry_minus_four_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1038c))
    (constant : state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x1038c) retired x12
          (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x1038c, 0xffc50613)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1038c) 0x13#8 0x06#8 0xc5#8 0xff#8 :=
    fetchInstruction state 0x1038c 0x13 0x06 0xc5 0xff image
  have machine := pre.machine.mono agree retiredPresent
  have privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine :=
    machine.normal.2.1
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  have privilegeAfterIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
    simp [tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, privilegeRead]
  have mseccfgAfterIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits := by
    simp [tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, mseccfgRead]
  have wordEq : fetchWord 0x13#8 0x06#8 0xc5#8 0xff#8 =
      (0xffc50613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0xc5#8 0xff#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0xffc#12, .Regidx 10#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1038c)
  have sourceAtExecute : executeState.regs.get? x10 =
      some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, constant]
  have execute : Runs (execute (.ITYPE (0xffc#12, .Regidx 10#5, .Regidx 12#5, .ADDI)))
      executeState
      { executeState with regs :=
          executeState.regs.insert x12 (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0xffc#12 (.Regidx 10#5) (.Regidx 12#5) .ADDI) _ _ _
    have resultEq : BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32) + sign_extend (m := 64) 0xffc#12 =
        BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4) := by native_decide
    rw [← resultEq]
    exact execute_ITYPE_addi_run executeState _ 0xffc#12 (.Regidx 10#5) (.Regidx 12#5)
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))
      (rX_bits_run_x10 executeState _ sourceAtExecute) (wX_x12_run executeState _)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x1038c) pcIn atPc 0x13#8 0x06#8 0xc5#8 0xff#8
    (.ITYPE (0xffc#12, .Regidx 10#5, .Regidx 12#5, .ADDI)) x12
    (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)) fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute the retry-entry branch and all three parent-owned constant instructions, stopping at
the selected prefix helper's length-segment entry. -/
theorem decodeInline_retry_reaches_length_gate (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) :
    ∃ after,
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10390) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) ∧
      after.regs.get? x12 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)) ∧
      Agree decoderPreserved state after ∧
      RetiredCounterPresent after ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 2) ∧
      Contracts.canonicalContractParams.env.CodeIntact after ∧
      after.mem = state.mem ∧
      HasExactErePrefixInlinePre
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } after := by
  obtain ⟨branchRetired, branchRun, branchPc⟩ :=
    decodeInline_retry_entry_branch_step fromStep args state pre phase
  let s1 := decodeInlineRetryEntryAfter state branchRetired
  have branchAgree : Agree decoderPreserved state s1 := by
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
    simp [s1, decodeInlineRetryEntryAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, notRetired, notPc, notNextPc, notIncrement]
  have branchCounter : RetiredCounterPresent s1 := by
    refine ⟨Sail.BitVec.addInt branchRetired 1, ?_⟩
    simp [s1, decodeInlineRetryEntryAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]
  have branchMemory : s1.mem = state.mem := rfl
  have branchCode : Contracts.canonicalContractParams.env.CodeIntact s1 := by
    rw [Contracts.DecoderEnvironment.CodeIntact, branchMemory]
    exact pre.code
  obtain ⟨minusOneRetired, minusOneRun⟩ := decodeInline_retry_minus_one_step
    (fromStep + 1) args state s1 pre branchAgree branchCounter branchCode branchPc
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x10384) minusOneRetired x10
    (BitVec.ofNat 64 (2 ^ 64 - 1))
  have agree2 : Agree decoderPreserved state s2 :=
    Agree.trans branchAgree (afterRegisterWrite_agree_of
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10388) := by
    change (afterRegisterWrite s1 (BitVec.ofNat 64 0x10384) minusOneRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 1))).regs.get? PC = _
    rw [afterRegisterWrite_pc]
    decide
  have x10At2 : s2.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 1)) := by
    simp [s2, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have code2 : Contracts.canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, afterRegisterWrite_mem] using branchCode
  obtain ⟨shiftRetired, shiftRun⟩ := decodeInline_retry_shift_constant_step
    (fromStep + 2) args state s2 pre agree2
    (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x10384) minusOneRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 1))) code2 pc2 x10At2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10388) shiftRetired x10
    (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))
  have agree3 : Agree decoderPreserved state s3 :=
    Agree.trans agree2 (afterRegisterWrite_agree_of
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x1038c) := by
    change (afterRegisterWrite s2 (BitVec.ofNat 64 0x10388) shiftRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))).regs.get? PC = _
    rw [afterRegisterWrite_pc]
    decide
  have x10At3 : s3.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) := by
    simp [s3, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have code3 : Contracts.canonicalContractParams.env.CodeIntact s3 := by
    simpa [s3, afterRegisterWrite_mem] using code2
  obtain ⟨minusFourRetired, minusFourRun⟩ := decodeInline_retry_minus_four_step
    (fromStep + 3) args state s3 pre agree3
    (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10388) shiftRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))) code3 pc3 x10At3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x1038c) minusFourRetired x12
    (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))
  have agree4 : Agree decoderPreserved state s4 :=
    Agree.trans agree3 (afterRegisterWrite_agree_of
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x10390) := by
    change (afterRegisterWrite s3 (BitVec.ofNat 64 0x1038c) minusFourRetired x12
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))).regs.get? PC = _
    rw [afterRegisterWrite_pc]
    decide
  have x10At4 : s4.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) := by
    simp [s4, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, x10At3]
  have x12At4 : s4.regs.get? x12 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)) := by
    simp [s4, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have code4 : Contracts.canonicalContractParams.env.CodeIntact s4 := by
    simpa [s4, afterRegisterWrite_mem] using code3
  have counter4 := afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x1038c)
    minusFourRetired x12 (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes }
  have memory4 : s4.mem = state.mem := rfl
  have inputPointer4 : s4.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [s4, s3, s2, s1, afterRegisterWrite, decodeInlineRetryEntryAfter,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, pre.inputValue]
  have inputLength4 : s4.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [s4, s3, s2, s1, afterRegisterWrite, decodeInlineRetryEntryAfter,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, pre.lengthValue]
  have globals4 : s4.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [s4, s3, s2, s1, afterRegisterWrite, decodeInlineRetryEntryAfter,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, pre.globalsValue]
  have stackPointer4 : s4.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [s4, s3, s2, s1, afterRegisterWrite, decodeInlineRetryEntryAfter,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, pre.stackValue]
  have status4 : s4.regs.get? x11 = some (BitVec.ofNat 64 2) := by
    obtain ⟨-, -, statusAtEntry⟩ := pre.retryReason phase
    simp [s4, s3, s2, s1, afterRegisterWrite, decodeInlineRetryEntryAfter,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, statusAtEntry]
  have inputMemory4 : BinaryFv.Zesu.MemoryRepresentation.MemoryBytes s4 args.inputBase args.bytes := by
    intro index bound
    rw [memory4]
    exact pre.inputMemory index bound
  have parentMachine4 : DecodeInlineMachinePre args s4 :=
    pre.machine.mono agree4 counter4
  have childMachine4 : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
      childArgs.machineArgs s4 := by
    simpa [childArgs, HasExactErePrefixInlineArgs.machineArgs, DecodeInlineArgs.machineArgs] using
      parentMachine4.restrict hasExactErePrefix_executionPcs_subset_decode
  have childPre : HasExactErePrefixInlinePre childArgs s4 := by
    refine ⟨?_, inputPointer4, inputLength4, globals4, inputMemory4, code4, pre.inputFits,
      pre.rootInputBound, ?_, ?_, childMachine4⟩
    · simpa [childArgs, HasExactErePrefixInlineArgs.entryPc] using pc4
    · intro _
      exact ⟨x10At4, x12At4⟩
    · simp [childArgs]
  have region1 := decodeInline_owned_in_execution_region (0x10380, 0x06b51e63)
    (by simp [decodeInlineOwnedInstructionWords])
  have region2 := decodeInline_owned_in_execution_region (0x10384, 0xfff00513)
    (by simp [decodeInlineOwnedInstructionWords])
  have region3 := decodeInline_owned_in_execution_region (0x10388, 0x02051513)
    (by simp [decodeInlineOwnedInstructionWords])
  have region4 := decodeInline_owned_in_execution_region (0x1038c, 0xffc50613)
    (by simp [decodeInlineOwnedInstructionWords])
  have notExit1 := decodeInline_retry_entry_not_selected_exit args phase
  have notExit2 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10384) := by
    simp [DecodeInlineExit, phase]
  have notExit3 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10388) := by
    simp [DecodeInlineExit, phase]
  have notExit4 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x1038c) := by
    simp [DecodeInlineExit, phase]
  have p1 : ConfinedPrefix _ (DecodeInlineExit args) Level3ChildSummary fromStep 1 state s1 :=
    ConfinedPrefix.ownStep (by simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry)
      region1 notExit1 (by simpa [s1] using branchRun)
  have p2 : ConfinedPrefix _ (DecodeInlineExit args) Level3ChildSummary (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep branchPc region2 notExit2 (by simpa [s2] using minusOneRun)
  have p3 : ConfinedPrefix _ (DecodeInlineExit args) Level3ChildSummary (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep pc2 region3 notExit3 (by simpa [s3] using shiftRun)
  have p4 : ConfinedPrefix _ (DecodeInlineExit args) Level3ChildSummary (fromStep + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep pc3 region4 notExit4 (by simpa [s4] using minusFourRun)
  have prefix12 := ConfinedPrefix.trans p1 p2
  have prefix123 := ConfinedPrefix.trans prefix12 p3
  have prefix1234 := ConfinedPrefix.trans prefix123 p4
  refine ⟨s4, ?_, pc4, x10At4, x12At4, agree4, counter4, stackPointer4, status4, code4,
    memory4, ?_⟩
  · simpa using prefix1234
  · simpa [childArgs] using childPre

/-- Consume the proved one-instruction prefix length segment after the four parent-owned retry
instructions. The result remains at the outgoing `bltu` for the enclosing `decode` proof to execute. -/
theorem decodeInline_retry_uses_length_gate (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) :
    ∃ childUsed childAfter,
      childUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
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
  have childRun :=
    hasExactErePrefix_length_segment (fromStep + 4) childArgs childEntry childPre' rfl
  let childAfter := Classical.choose childRun
  have childPayload := Classical.choose_spec childRun
  have childTrace := childPayload.1
  have childPost := childPayload.2.1
  have childAgree := childPayload.2.2.1
  have childCounter := childPayload.2.2.2.1
  have childStackFrame := childPayload.2.2.2.2.1
  have childInputPointer := childPayload.2.2.2.2.2.1
  have childInputLength := childPayload.2.2.2.2.2.2.1
  have childGlobals := childPayload.2.2.2.2.2.2.2.1
  have childStatusEq := childPayload.2.2.2.2.2.2.2.2.1
  have childMemory := childPayload.2.2.2.2.2.2.2.2.2
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
  have childPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
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

/-- An input shorter than the four-byte framing word cannot have an exact ERE prefix. -/
theorem meaningHasExactErePrefix_false_of_size_lt_four (bytes : ByteArray)
    (short : bytes.size < 4) : Contracts.meaningHasExactErePrefix bytes = false := by
  simp [Contracts.meaningHasExactErePrefix, BinaryFv.Specs.SSZ.readU32LE?, short]

def decodeInlineRetryLengthBranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10394))
    (BitVec.ofNat 64 0x10398) retired

/-- When four framing bytes exist, execute `bltu a2, a0, 0x10420` at `0x10394` as not taken.
The constants prepared by the parent turn the unsigned comparison into `bytes.size < 4`. -/
theorem decodeInline_retry_length_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10394))
    (constant : state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)))
    (adjustedLength : state.regs.get? x12 = some
      (BitVec.ofNat 64 (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4))))
    (fourBytes : 4 ≤ args.bytes.size) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlineRetryLengthBranchAfter state retired) false ∧
      (decodeInlineRetryLengthBranchAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10398) ∧
      Agree decoderPreserved state (decodeInlineRetryLengthBranchAfter state retired) ∧
      RetiredCounterPresent (decodeInlineRetryLengthBranchAfter state retired) ∧
      (decodeInlineRetryLengthBranchAfter state retired).mem = state.mem := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (BitVec.ofNat 64 0x10394) :=
    decoderFetchPc_of_member (pc := BitVec.ofNat 64 0x10394) (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10394) 0x63#8 0x66#8 0xa6#8 0x08#8 :=
    fetchInstruction state 0x10394 0x63 0x66 0xa6 0x08 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x10394) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal (Agree.refl state) retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have wordEq : fetchWord 0x63#8 0x66#8 0xa6#8 0x08#8 =
      (0x08a66663 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x66#8 0xa6#8 0x08#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x8c#13, .Regidx 10#5, .Regidx 12#5, .BLTU)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10394)
  have x10AtExecute : executeState.regs.get? x10 =
      some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, constant]
  have x12AtExecute : executeState.regs.get? x12 = some
      (BitVec.ofNat 64 (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4))) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, adjustedLength]
  have sizeBound : args.bytes.size < 2 ^ 32 := by
    have := pre.rootInputBound
    omega
  have condition : Runs (bTypeTaken (.Regidx 10#5) (.Regidx 12#5) .BLTU)
      executeState executeState false := by
    unfold bTypeTaken
    have readX12 : Runs (rX_bits (.Regidx 12#5)) executeState executeState
        (BitVec.ofNat 64 (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4))) := by
      have index : (Sail.BitVec.toNatInt (12#5 : BitVec 5)).toNat = 12 := rfl
      unfold Runs
      simp [rX_bits, rX, index, regval_from_reg, PreSail.readReg, EStateM.run, EStateM.bind,
        EStateM.get, EStateM.pure, EStateM.instMonad,
        EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
        x12AtExecute]
    refine Runs.bind readX12 ?_
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    have leftFits : args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4) < 2 ^ 64 := by omega
    have rightFits : 2 ^ 64 - 2 ^ 32 < 2 ^ 64 := by omega
    simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt leftFits, Nat.mod_eq_of_lt rightFits]
    have comparison :
        (Int.ofNat (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4)) <b
          Int.ofNat (2 ^ 64 - 2 ^ 32)) = false := by
      simp only [decide_eq_false_iff_not]
      apply Int.not_lt.mpr
      apply Int.ofNat_le.mpr
      omega
    rw [comparison]
    rfl
  have run := tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10394) retired
    (0x8c#13) (.Regidx 10#5) (.Regidx 12#5) .BLTU inhibit config
    0x63#8 0x66#8 0xa6#8 0x08#8 fetch noMMIO fetchBytes interrupts
    (by unfold BaseInstructionEncoding; decide) decode notExpected condition hartRead inhibitRead
    configRead notInhibited machineEnabled retiredRead
  refine ⟨retired, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [decodeInlineRetryLengthBranchAfter] using run
  · simp [decodeInlineRetryLengthBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  · intro register preserved
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
    simp [decodeInlineRetryLengthBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, notRetired, notPc, notNextPc, notIncrement]
  · refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
    simp [decodeInlineRetryLengthBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]

/-- Splice the proved length child and parent-owned `bltu`, producing the complete machine entry for
the ten-instruction prefix-byte child. -/
theorem decodeInline_retry_reaches_prefix_bytes (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size) :
    ∃ lengthUsed childEntry,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep (5 + lengthUsed) state childEntry ∧
      HasExactErePrefixInlinePre
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } childEntry ∧
      Agree decoderPreserved state childEntry ∧
      RetiredCounterPresent childEntry ∧
      childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Contracts.canonicalContractParams.env.CodeIntact childEntry ∧
      childEntry.mem = state.mem := by
  obtain ⟨lengthUsed, lengthAfter, lengthBound, lengthPrefix, lengthPost, lengthAgree,
    lengthCounter, lengthStackPointer, lengthInputPointer, lengthInputLength, lengthGlobals,
    _lengthStatus, lengthCode, lengthMemory⟩ :=
    decodeInline_retry_uses_length_gate fromStep args state pre phase
  have prefixFalseAtLength : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10394) := by
    simp [DecodeInlineExit, phase, show ¬ args.bytes.size < 4 by omega]
  obtain ⟨branchRetired, branchRun, branchPc, branchPreserves, branchCounter, branchMemory⟩ :=
    decodeInline_retry_length_branch_step (fromStep + (4 + lengthUsed)) args state lengthAfter
      pre lengthAgree lengthCounter lengthCode lengthPost.1 lengthPost.2.1 lengthPost.2.2
      fourBytes
  let childEntry := decodeInlineRetryLengthBranchAfter lengthAfter branchRetired
  have branchPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (4 + lengthUsed)) 1
      lengthAfter childEntry := by
    apply ConfinedPrefix.ownStep lengthPost.1
    · apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide
    · exact prefixFalseAtLength
    · simpa [childEntry] using branchRun
  have completePrefix := ConfinedPrefix.trans lengthPrefix branchPrefix
  have childAgree : Agree decoderPreserved state childEntry :=
    Agree.trans lengthAgree (by simpa [childEntry] using branchPreserves)
  have childMemory : childEntry.mem = state.mem := by
    have branchMemory' : childEntry.mem = lengthAfter.mem := by
      simpa [childEntry] using branchMemory
    exact branchMemory'.trans lengthMemory
  have childCode : Contracts.canonicalContractParams.env.CodeIntact childEntry := by
    rw [Contracts.DecoderEnvironment.CodeIntact, childMemory]
    exact pre.code
  have childStackPointer : childEntry.regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) := by
    simpa [childEntry, decodeInlineRetryLengthBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using lengthStackPointer
  have childGlobals : childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simpa [childEntry, decodeInlineRetryLengthBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using lengthGlobals
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes }
  have parentMachine : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono childAgree (by simpa [childEntry] using branchCounter)
  have childMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
      childArgs.machineArgs childEntry := by
    simpa [childArgs, HasExactErePrefixInlineArgs.machineArgs, DecodeInlineArgs.machineArgs] using
      parentMachine.restrict hasExactErePrefix_executionPcs_subset_decode
  have childPre : HasExactErePrefixInlinePre childArgs childEntry := by
    refine ⟨?_, ?_, ?_, childGlobals, ?_, childCode, pre.inputFits, pre.rootInputBound, ?_, ?_, childMachine⟩
    · simpa [childArgs, HasExactErePrefixInlineArgs.entryPc] using branchPc
    · simpa [childEntry, decodeInlineRetryLengthBranchAfter,
        tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using lengthInputPointer
    · simpa [childEntry, decodeInlineRetryLengthBranchAfter,
        tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using lengthInputLength
    · intro index bound
      rw [childMemory]
      exact pre.inputMemory index bound
    · simp [childArgs]
    · intro _
      exact fourBytes
  refine ⟨lengthUsed, childEntry, lengthBound, ?_, ?_, childAgree, ?_, childStackPointer, childGlobals,
    childCode, childMemory⟩
  · have steps : 4 + lengthUsed + 1 = 5 + lengthUsed := by omega
    rw [← steps]
    exact completePrefix
  · change HasExactErePrefixInlinePre childArgs childEntry
    exact childPre
  · change RetiredCounterPresent childEntry at branchCounter
    exact branchCounter

/-- Consume the proved ten-instruction prefix-byte child after the length branch. The resulting
state is at `0x103c0`, where the parent still owns the final `or`. -/
theorem decodeInline_retry_uses_prefix_bytes (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size) :
    ∃ lengthUsed prefixUsed after,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      prefixUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep
          (5 + lengthUsed + prefixUsed) state after ∧
      HasExactErePrefixInlinePost
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } after ∧
      Agree decoderPreserved state after ∧
      RetiredCounterPresent after ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Contracts.canonicalContractParams.env.CodeIntact after ∧
      after.mem = state.mem := by
  obtain ⟨lengthUsed, childEntry, lengthBound, parentPrefix, childPre, parentAgree, parentCounter,
    parentStackPointer, parentGlobals, parentCode, parentMemory⟩ :=
    decodeInline_retry_reaches_prefix_bytes fromStep args state pre phase fourBytes
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes }
  have childPre' : HasExactErePrefixInlinePre childArgs childEntry := by
    change HasExactErePrefixInlinePre childArgs childEntry at childPre
    exact childPre
  have childRun := hasExactErePrefix_prefix_segment (fromStep + (5 + lengthUsed)) childArgs
    childEntry childPre' rfl
  let after := Classical.choose childRun
  have payload := Classical.choose_spec childRun
  have childTrace := payload.1
  have childPost := payload.2.1
  have childAgree := payload.2.2.1
  have childCounter := payload.2.2.2.1
  have childStackFrame := payload.2.2.2.2.1
  have childInputPointer := payload.2.2.2.2.2.1
  have childInputLength := payload.2.2.2.2.2.2.1
  have childGlobals := payload.2.2.2.2.2.2.2.1
  have childMemory := payload.2.2.2.2.2.2.2.2
  have childStackPointer : after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    childStackFrame.trans parentStackPointer
  let prefixUsed := 10
  have childBound : prefixUsed ≤ hasExactErePrefixInlineStepBound childArgs := by
    simp [prefixUsed, hasExactErePrefixInlineStepBound]
  have exactSummary : hasExactErePrefixInlineSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + (5 + lengthUsed)) prefixUsed childEntry after :=
    ⟨rfl, childArgs, childPre', childBound, childTrace, childPost⟩
  have selectedSummary : Level3ChildSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + (5 + lengthUsed)) prefixUsed childEntry after :=
    .hasExactErePrefix exactSummary
  have childPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (5 + lengthUsed)) prefixUsed
      childEntry after := by
    intro count final rest
    exact ScopedTrace.childBody _ prefixUsed count _ childEntry after final selectedSummary rest
  have completePrefix := ConfinedPrefix.trans parentPrefix childPrefix
  have completeAgree := Agree.trans parentAgree childAgree
  have completeMemory : after.mem = state.mem := childMemory.trans parentMemory
  have completeCode : Contracts.canonicalContractParams.env.CodeIntact after := by
    rw [Contracts.DecoderEnvironment.CodeIntact, completeMemory]
    exact pre.code
  refine ⟨lengthUsed, prefixUsed, after, lengthBound, ?_, ?_, ?_, completeAgree, childCounter,
    childStackPointer, childInputPointer, childInputLength, childGlobals, completeCode, completeMemory⟩
  · simpa [childArgs] using childBound
  · simpa [Nat.add_assoc] using completePrefix
  · simpa [childArgs] using childPost

/-- Execute the parent-owned `or a0, a4, a0` at `0x103c0`, assembling the complete little-endian
prefix value and reaching the result branch at `0x103c4`. -/
theorem decodeInline_retry_prefix_or_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103c0))
    (low high : BitVec 64) (lowRead : state.regs.get? x10 = some low)
    (highRead : state.regs.get? x14 = some high) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) false ∧
      (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10
        (high ||| low)).regs.get? PC = some (BitVec.ofNat 64 0x103c4) ∧
      Agree decoderPreserved state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) ∧
      RetiredCounterPresent
        (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) ∧
      (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10
        (high ||| low)).mem = state.mem := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (BitVec.ofNat 64 0x103c0) :=
    decoderFetchPc_of_member (pc := BitVec.ofNat 64 0x103c0) (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103c0) 0x33#8 0x65#8 0xa7#8 0x00#8 :=
    fetchInstruction state 0x103c0 0x33 0x65 0xa7 0x00 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨decodeMseccfg, decodePlatform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103c0) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ :=
    decodePlatform
  have wordEq : fetchWord 0x33#8 0x65#8 0xa7#8 0x00#8 =
      (0x00a76533 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x65#8 0xa7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 10#5, .Regidx 14#5, .Regidx 10#5, .OR)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103c0)
  have lowAtExecute : executeState.regs.get? x10 = some low := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, lowRead]
  have highAtExecute : executeState.regs.get? x14 = some high := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, highRead]
  have execute : Runs (execute (.RTYPE
      (.Regidx 10#5, .Regidx 14#5, .Regidx 10#5, .OR))) executeState
      { executeState with regs := executeState.regs.insert x10 (high ||| low) }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 10#5) (.Regidx 14#5) (.Regidx 10#5) .OR) _ _ _
    exact execute_RTYPE_run executeState _ (.Regidx 10#5) (.Regidx 14#5)
      (.Regidx 10#5) .OR high low (rX_x14_run executeState high highAtExecute)
      (rX_x10_run executeState low lowAtExecute) (wX_x10_run executeState _)
  obtain ⟨retired, run⟩ := decoderRegisterWriteStep machine (Agree.refl state) retiredPresent
    stepNo (BitVec.ofNat 64 0x103c0) pcIn atPc 0x33#8 0x65#8 0xa7#8 0x00#8
    (.RTYPE (.Regidx 10#5, .Regidx 14#5, .Regidx 10#5, .OR)) x10 (high ||| low)
    fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute
  refine ⟨retired, run, ?_, ?_, ?_, rfl⟩
  · simpa using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103c0) retired x10
      (high ||| low)
  · exact afterRegisterWrite_agree_of
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
  · exact afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103c0) retired x10
      (high ||| low)

/-- The two child-produced halves are exactly the framing reader's little-endian `u32`. -/
theorem prefix_halves_or_eq_readU32LE (bytes : ByteArray) (fourBytes : 4 ≤ bytes.size) :
    ∃ declared,
      BinaryFv.Specs.SSZ.readU32LE? bytes 0 = some declared ∧
      BitVec.ofNat 64 (prefixHigh16 bytes) ||| BitVec.ofNat 64 (prefixLow16 bytes) =
        BitVec.ofNat 64 declared ∧
      declared < 2 ^ 32 := by
  let byte0 := bytes.get! 0
  let byte1 := bytes.get! 1
  let byte2 := bytes.get! 2
  let byte3 := bytes.get! 3
  let declared := byte0.toNat + byte1.toNat * 2 ^ 8 +
    byte2.toNat * 2 ^ 16 + byte3.toNat * 2 ^ 24
  refine ⟨declared, ?_, ?_, ?_⟩
  · rw [BinaryFv.Specs.SSZ.readU32LE?, if_neg (by omega)]
  · have assembly := prefixHalvesAssemblyValue
      (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
      (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
    dsimp [prefixLow16, prefixHigh16, declared, byte0, byte1, byte2, byte3]
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)] using assembly
  · have bound0 := UInt8.toNat_lt byte0
    have bound1 := UInt8.toNat_lt byte1
    have bound2 := UInt8.toNat_lt byte2
    have bound3 := UInt8.toNat_lt byte3
    dsimp [declared]
    omega

theorem prefix_declared_eq_of_meaning_true (bytes : ByteArray) (declared : Nat)
    (read : BinaryFv.Specs.SSZ.readU32LE? bytes 0 = some declared)
    (exactPrefix : Contracts.meaningHasExactErePrefix bytes = true) :
    declared = bytes.size - 4 := by
  rw [Contracts.meaningHasExactErePrefix, read] at exactPrefix
  simp only [Bool.and_eq_true, decide_eq_true_eq] at exactPrefix
  exact beq_iff_eq.mp exactPrefix.2

theorem prefix_declared_ne_of_meaning_false (bytes : ByteArray) (declared : Nat)
    (fourBytes : 4 ≤ bytes.size)
    (read : BinaryFv.Specs.SSZ.readU32LE? bytes 0 = some declared)
    (notExact : Contracts.meaningHasExactErePrefix bytes = false) :
    declared ≠ bytes.size - 4 := by
  intro equal
  rw [Contracts.meaningHasExactErePrefix, read] at notExact
  simp [fourBytes, equal] at notExact

def decodeInlineRetryPrefixBranchFallThrough (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103c4))
    (BitVec.ofNat 64 0x103c8) retired

/-- Execute `bne a3, a0, 0x10420` as not taken when the framing word equals `bytes.size - 4`. -/
theorem decodeInline_retry_prefix_branch_not_taken (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103c4))
    (declared : Nat) (declaredRead : state.regs.get? x10 = some (BitVec.ofNat 64 declared))
    (lengthRead : state.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4)))
    (equal : declared = args.bytes.size - 4) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlineRetryPrefixBranchFallThrough state retired) false ∧
      (decodeInlineRetryPrefixBranchFallThrough state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x103c8) ∧
      Agree decoderPreserved state (decodeInlineRetryPrefixBranchFallThrough state retired) ∧
      RetiredCounterPresent (decodeInlineRetryPrefixBranchFallThrough state retired) ∧
      (decodeInlineRetryPrefixBranchFallThrough state retired).mem = state.mem := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103c4, 0x04a69e63)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103c4) 0x63#8 0x9e#8 0xa6#8 0x04#8 :=
    fetchInstruction state 0x103c4 0x63 0x9e 0xa6 0x04 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103c4) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal (Agree.refl state) retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have wordEq : fetchWord 0x63#8 0x9e#8 0xa6#8 0x04#8 =
      (0x04a69e63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x9e#8 0xa6#8 0x04#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x5c#13, .Regidx 10#5, .Regidx 13#5, .BNE)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103c4)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 declared) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, declaredRead]
  have x13AtExecute : executeState.regs.get? x13 =
      some (BitVec.ofNat 64 (args.bytes.size - 4)) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, lengthRead]
  have condition : Runs (bTypeTaken (.Regidx 10#5) (.Regidx 13#5) .BNE)
      executeState executeState false := by
    unfold bTypeTaken
    refine Runs.bind (rX_x13_run executeState _ x13AtExecute) ?_
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    simp [equal]
    rfl
  have run := tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x103c4) retired
    (0x5c#13) (.Regidx 10#5) (.Regidx 13#5) .BNE inhibit config
    0x63#8 0x9e#8 0xa6#8 0x04#8 fetch noMMIO fetchBytes interrupts
    (by unfold BaseInstructionEncoding; decide) decode notExpected condition hartRead inhibitRead
    configRead notInhibited machineEnabled retiredRead
  refine ⟨retired, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [decodeInlineRetryPrefixBranchFallThrough] using run
  · simp [decodeInlineRetryPrefixBranchFallThrough, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  · intro register preserved
    have notRetired : minstret ≠ register := by
      intro h; subst register; simp [decoderPreserved, platformPreserved] at preserved
    have notPc : PC ≠ register := by
      intro h; subst register; simp [decoderPreserved, platformPreserved] at preserved
    have notNextPc : nextPC ≠ register := by
      intro h; subst register; simp [decoderPreserved, platformPreserved] at preserved
    have notIncrement : minstret_increment ≠ register := by
      intro h; subst register; simp [decoderPreserved, platformPreserved] at preserved
    simp [decodeInlineRetryPrefixBranchFallThrough, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, notRetired, notPc, notNextPc, notIncrement]
  · refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
    simp [decodeInlineRetryPrefixBranchFallThrough, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]

def decodeInlineRetryPrefixBranchTaken (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103c4) (BitVec.ofNat 64 0x10420))
    (BitVec.ofNat 64 0x10420) retired

/-- Execute `bne a3, a0, 0x10420` as taken when the framing word differs from `bytes.size - 4`. -/
theorem decodeInline_retry_prefix_branch_taken (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103c4))
    (declared : Nat) (declaredBound : declared < 2 ^ 32)
    (declaredRead : state.regs.get? x10 = some (BitVec.ofNat 64 declared))
    (lengthRead : state.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4)))
    (different : declared ≠ args.bytes.size - 4) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlineRetryPrefixBranchTaken state retired) false ∧
      (decodeInlineRetryPrefixBranchTaken state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10420) ∧
      Agree decoderPreserved state (decodeInlineRetryPrefixBranchTaken state retired) ∧
      RetiredCounterPresent (decodeInlineRetryPrefixBranchTaken state retired) ∧
      (decodeInlineRetryPrefixBranchTaken state retired).mem = state.mem := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103c4, 0x04a69e63)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103c4) 0x63#8 0x9e#8 0xa6#8 0x04#8 :=
    fetchInstruction state 0x103c4 0x63 0x9e 0xa6 0x04 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103c4) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal (Agree.refl state) retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have wordEq : fetchWord 0x63#8 0x9e#8 0xa6#8 0x04#8 =
      (0x04a69e63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x9e#8 0xa6#8 0x04#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x5c#13, .Regidx 10#5, .Regidx 13#5, .BNE)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103c4)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 declared) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, declaredRead]
  have x13AtExecute : executeState.regs.get? x13 =
      some (BitVec.ofNat 64 (args.bytes.size - 4)) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, lengthRead]
  have lengthBound : args.bytes.size - 4 < 2 ^ 64 := by
    have := pre.rootInputBound
    omega
  have bitsDifferent : BitVec.ofNat 64 (args.bytes.size - 4) ≠
      BitVec.ofNat 64 declared := by
    intro equalBits
    apply different
    have declaredBound64 : declared < 2 ^ 64 := by omega
    have equalNat : args.bytes.size - 4 = declared := by
      rw [← Nat.mod_eq_of_lt lengthBound, ← Nat.mod_eq_of_lt declaredBound64]
      exact congrArg BitVec.toNat equalBits
    exact equalNat.symm
  have condition : Runs (bTypeTaken (.Regidx 10#5) (.Regidx 13#5) .BNE)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_x13_run executeState _ x13AtExecute) ?_
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    have comparison : (BitVec.ofNat 64 (args.bytes.size - 4) !=
        BitVec.ofNat 64 declared) = true := bne_iff_ne.mpr bitsDifferent
    rw [comparison]
    rfl
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x103c4) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have targetEq : BitVec.ofNat 64 0x103c4 + sign_extend (m := 64) (0x5c#13) =
      BitVec.ofNat 64 0x10420 := by decide
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      state.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match read : state.regs.get? misa with
    | none => simp [read] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [read] using normalMisa⟩
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x103c4)
    misaBits misaRead
  have run := tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x103c4)
    (BitVec.ofNat 64 0x103c4) retired (0x5c#13) (.Regidx 10#5) (.Regidx 13#5) .BNE
    inhibit config 0x63#8 0x9e#8 0xa6#8 0x04#8 (_get_Misa_C misaBits == 1#1)
    fetch noMMIO fetchBytes interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected condition (readReg_run executeState PC _ pcAtExecute)
    (by decide) (by decide) zca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead
  refine ⟨retired, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [decodeInlineRetryPrefixBranchTaken, targetEq] using run
  · simp [decodeInlineRetryPrefixBranchTaken, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · intro register preserved
    have notRetired : minstret ≠ register := by
      intro h; subst register; simp [decoderPreserved, platformPreserved] at preserved
    have notPc : PC ≠ register := by
      intro h; subst register; simp [decoderPreserved, platformPreserved] at preserved
    have notNextPc : nextPC ≠ register := by
      intro h; subst register; simp [decoderPreserved, platformPreserved] at preserved
    have notIncrement : minstret_increment ≠ register := by
      intro h; subst register; simp [decoderPreserved, platformPreserved] at preserved
    simp [decodeInlineRetryPrefixBranchTaken, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, notRetired, notPc,
      notNextPc, notIncrement]
  · refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
    simp [decodeInlineRetryPrefixBranchTaken, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]

/-- Close the four-or-more-byte prefix-mismatch arm at the selected outgoing branch source. The
branch itself transfers to wrapper code and is therefore executed by the Level 2 proof. -/
theorem decodeInline_retry_prefix_mismatch_reaches_post (fromStep : Nat)
    (args : DecodeInlineArgs) (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size)
    (notExact : Contracts.meaningHasExactErePrefix args.bytes = false) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧
      DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after := by
  obtain ⟨lengthUsed, prefixUsed, beforeOr, lengthBound, prefixBound, parentPrefix, prefixPost,
    beforeAgree, beforeCounter, _beforeStack, inputPointer, inputLength, beforeGlobals,
    beforeCode, beforeMemory⟩ :=
    decodeInline_retry_uses_prefix_bytes fromStep args state pre phase fourBytes
  obtain ⟨orRetired, orRun, orPc, orPreserves, orCounter, orMemory⟩ :=
    decodeInline_retry_prefix_or_step (fromStep + (5 + lengthUsed + prefixUsed)) args state
      beforeOr pre beforeAgree beforeCounter beforeCode prefixPost.1
      (BitVec.ofNat 64 (prefixLow16 args.bytes))
      (BitVec.ofNat 64 (prefixHigh16 args.bytes)) prefixPost.2.1 prefixPost.2.2.1
  let after := afterRegisterWrite beforeOr (BitVec.ofNat 64 0x103c0) orRetired x10
    (BitVec.ofNat 64 (prefixHigh16 args.bytes) |||
      BitVec.ofNat 64 (prefixLow16 args.bytes))
  have orNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x103c0) := by
    simp [DecodeInlineExit, phase, notExact, show ¬ args.bytes.size < 4 by omega]
  have orRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x103c0) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have orPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (5 + lengthUsed + prefixUsed)) 1
      beforeOr after :=
    ConfinedPrefix.ownStep prefixPost.1 orRegion orNotExit (by simpa [after] using orRun)
  have completePrefix := ConfinedPrefix.trans parentPrefix orPrefix
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x103c4) := by
    simp [DecodeInlineExit, phase, notExact, show ¬ args.bytes.size < 4 by omega]
  have tail : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (5 + lengthUsed + prefixUsed + 1)) 0 after after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x103c4) (by simpa [after] using orPc)
      selectedExit
  have trace := completePrefix 0 after tail
  have rawInvalid : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz :=
    (pre.retryReason phase).1
  have resultInvalid : Contracts.meaningDecode args.bytes = .error .invalidSsz := by
    simp [Contracts.meaningDecode, rawInvalid, notExact]
  have afterAgree : Agree decoderPreserved state after := beforeAgree.trans orPreserves
  have afterCode : Contracts.canonicalContractParams.env.CodeIntact after := by
    rw [Contracts.DecoderEnvironment.CodeIntact, orMemory, beforeMemory]
    exact pre.code
  have afterGlobals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    exact (afterRegisterWrite_register beforeOr (BitVec.ofNat 64 0x103c0) orRetired x10 x18
      (BitVec.ofNat 64 (prefixHigh16 args.bytes) |||
        BitVec.ofNat 64 (prefixLow16 args.bytes))
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans beforeGlobals
  refine ⟨6 + lengthUsed + prefixUsed, after, ?_, ?_, ?_,
    ⟨afterAgree, orCounter, afterCode, afterGlobals.trans pre.globalsValue.symm⟩, ?_⟩
  · unfold decodeInlineStepBound
    have prefixBoundValue : prefixUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using prefixBound
    have lengthBoundValue : lengthUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using lengthBound
    omega
  · have countEq : 5 + lengthUsed + prefixUsed + 1 = 6 + lengthUsed + prefixUsed := by omega
    rw [← countEq]
    simpa using trace
  · simp [DecodeInlinePost, phase, DecodeInlineRetryPost, notExact, resultInvalid,
      show ¬ args.bytes.size < 4 by omega, after, orPc]
  · simp only [DecodeInlineOutgoingFrame, phase, notExact, Bool.false_eq_true, ↓reduceIte,
      show ¬ args.bytes.size < 4 by omega]
    constructor
    · simp [after, afterRegisterWrite, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
    · simpa [after, afterRegisterWrite, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using prefixPost.2.2.2

/-! ## Exact-prefix second-call setup -/

/-- Execute `addi a2, s0, 4`, selecting the tail after the framing word. -/
theorem decodeInline_retry_tail_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103c8))
    (inputRead : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103c8) retired x12
          (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103c8, 0x00440613)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103c8) 0x13#8 0x06#8 0x44#8 0x00#8 :=
    fetchInstruction state 0x103c8 0x13 0x06 0x44 0x00 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103c8) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x06#8 0x44#8 0x00#8 =
      (0x00440613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x44#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x004#12, .Regidx 8#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103c8)
  have inputAtExecute : executeState.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, inputRead]
  let result := iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase)
  have execute : Runs (execute (.ITYPE (0x004#12, .Regidx 8#5, .Regidx 12#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x12 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x004#12 (.Regidx 8#5) (.Regidx 12#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x004#12 (.Regidx 8#5) (.Regidx 12#5) .ADDI
      (BitVec.ofNat 64 args.inputBase) (rX_x8_run executeState _ inputAtExecute)
      (wX_x12_run executeState result)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x103c8) pcIn atPc 0x13#8 0x06#8 0x44#8 0x00#8
    (.ITYPE (0x004#12, .Regidx 8#5, .Regidx 12#5, .ADDI)) x12 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `addi a0, sp, 0x6b0`, selecting the retry result object. -/
theorem decodeInline_retry_result_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103cc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103cc) retired x10
          (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103cc, 0x6b010513)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103cc) 0x13#8 0x05#8 0x01#8 0x6b#8 :=
    fetchInstruction state 0x103cc 0x13 0x05 0x01 0x6b image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103cc) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x05#8 0x01#8 0x6b#8 =
      (0x6b010513 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x01#8 0x6b#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x6b0#12, .Regidx 2#5, .Regidx 10#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103cc)
  have stackAtExecute : executeState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  let result := iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase)
  have execute : Runs (execute (.ITYPE (0x6b0#12, .Regidx 2#5, .Regidx 10#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x10 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x6b0#12 (.Regidx 2#5) (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x6b0#12 (.Regidx 2#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 args.stackBase) (rX_bits_run_x2 executeState _ stackAtExecute)
      (wX_x10_run executeState result)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x103cc) pcIn atPc 0x13#8 0x05#8 0x01#8 0x6b#8
    (.ITYPE (0x6b0#12, .Regidx 2#5, .Regidx 10#5, .ADDI)) x10 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `addi a1, sp, 0x10`, selecting the existing allocator object. -/
theorem decodeInline_retry_allocator_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103d0))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103d0) retired x11
          (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103d0, 0x01010593)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103d0) 0x93#8 0x05#8 0x01#8 0x01#8 :=
    fetchInstruction state 0x103d0 0x93 0x05 0x01 0x01 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103d0) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x93#8 0x05#8 0x01#8 0x01#8 =
      (0x01010593 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x01#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x010#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103d0)
  have stackAtExecute : executeState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  let result := iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase)
  have execute : Runs (execute (.ITYPE (0x010#12, .Regidx 2#5, .Regidx 11#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x11 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x010#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x010#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI
      (BitVec.ofNat 64 args.stackBase) (rX_bits_run_x2 executeState _ stackAtExecute)
      (wX_x11_run executeState result)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x103d0) pcIn atPc 0x93#8 0x05#8 0x01#8 0x01#8
    (.ITYPE (0x010#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) x11 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `auipc ra, 0`, preparing the retry call's PC-relative base. -/
theorem decodeInline_retry_call_page_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103d4)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103d4) retired x1
          (BitVec.ofNat 64 0x103d4)) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103d4, 0x00000097)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103d4) 0x97#8 0x00#8 0x00#8 0x00#8 :=
    fetchInstruction state 0x103d4 0x97 0x00 0x00 0x00 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103d4) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x97#8 0x00#8 0x00#8 0x00#8 =
      (0x00000097 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x97#8 0x00#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x00000#20, .Regidx 1#5, .AUIPC)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103d4)
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x103d4) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (0x00000#20, .Regidx 1#5, .AUIPC))) executeState
      { executeState with regs := executeState.regs.insert x1 (BitVec.ofNat 64 0x103d4) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_auipc_run executeState _ 0x00000#20 (.Regidx 1#5)
      (BitVec.ofNat 64 0x103d4)
    · exact readReg_run _ _ _ pcAtExecute
    · simpa using wX_bits_run_x1 executeState (BitVec.ofNat 64 0x103d4)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x103d4) pcIn atPc 0x97#8 0x00#8 0x00#8 0x00#8
    (.UTYPE (0x00000#20, .Regidx 1#5, .AUIPC)) x1 (BitVec.ofNat 64 0x103d4)
    fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

set_option maxHeartbeats 8000000 in
/-- Execute every `decode`-owned instruction from retry entry through the second `decodeRaw` call
site. The two prefix-helper segments are consumed as child summaries; the branch, framing-word
assembly, and four call-argument instructions are executed directly through Sail. -/
theorem decodeInline_retry_before_second_decodeRaw_call (fromStep : Nat)
    (args : DecodeInlineArgs) (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true) :
    ∃ lengthUsed prefixUsed beforeCall,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      prefixUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep
          (11 + lengthUsed + prefixUsed) state beforeCall ∧
      beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103d8) ∧
      beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x103d4) ∧
      beforeCall.regs.get? x10 = some (BitVec.ofNat 64 (args.stackBase + 0x6b0)) ∧
      beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
      beforeCall.regs.get? x12 = some (BitVec.ofNat 64 (args.inputBase + 4)) ∧
      beforeCall.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4)) ∧
      beforeCall.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Agree decoderPreserved state beforeCall ∧
      RetiredCounterPresent beforeCall ∧
      Contracts.canonicalContractParams.env.CodeIntact beforeCall ∧
      beforeCall.mem = state.mem := by
  have fourBytes : 4 ≤ args.bytes.size := by
    rw [Contracts.meaningHasExactErePrefix] at exactPrefix
    split at exactPrefix <;> simp_all
  obtain ⟨lengthUsed, prefixUsed, beforeOr, lengthBound, prefixBound, prefixTrace,
    prefixPost, agreeBeforeOr, counterBeforeOr, stackBeforeOr, inputBeforeOr, lengthBeforeOr,
    globalsBeforeOr, codeBeforeOr, memoryBeforeOr⟩ :=
    decodeInline_retry_uses_prefix_bytes fromStep args state pre phase fourBytes
  obtain ⟨declared, declaredRead, assembled, declaredBound⟩ :=
    prefix_halves_or_eq_readU32LE args.bytes fourBytes
  have declaredEq := prefix_declared_eq_of_meaning_true args.bytes declared declaredRead exactPrefix
  obtain ⟨orRetired, orRun, orPc, orAgree, orCounter, orMemory⟩ :=
    decodeInline_retry_prefix_or_step (fromStep + (5 + lengthUsed + prefixUsed)) args state
      beforeOr pre agreeBeforeOr counterBeforeOr codeBeforeOr prefixPost.1
      (BitVec.ofNat 64 (prefixLow16 args.bytes))
      (BitVec.ofNat 64 (prefixHigh16 args.bytes)) prefixPost.2.1 prefixPost.2.2.1
  let sOr := afterRegisterWrite beforeOr (BitVec.ofNat 64 0x103c0) orRetired x10
    (BitVec.ofNat 64 (prefixHigh16 args.bytes) |||
      BitVec.ofNat 64 (prefixLow16 args.bytes))
  have declaredAtOr : sOr.regs.get? x10 = some (BitVec.ofNat 64 declared) := by
    simp [sOr, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      assembled]
  have lengthAtOr : sOr.regs.get? x13 =
      some (BitVec.ofNat 64 (args.bytes.size - 4)) := by
    simp [sOr, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      prefixPost.2.2.2]
  have agreeOr := Agree.trans agreeBeforeOr orAgree
  have codeOr : Contracts.canonicalContractParams.env.CodeIntact sOr := by
    rw [Contracts.DecoderEnvironment.CodeIntact, orMemory, memoryBeforeOr]
    exact pre.code
  obtain ⟨branchRetired, branchRun, branchPc, branchAgree, branchCounter, branchMemory⟩ :=
    decodeInline_retry_prefix_branch_not_taken
      (fromStep + (6 + lengthUsed + prefixUsed)) args state sOr pre agreeOr orCounter codeOr
      orPc declared declaredAtOr lengthAtOr declaredEq
  let sBranch := decodeInlineRetryPrefixBranchFallThrough sOr branchRetired
  have agreeBranch : Agree decoderPreserved state sBranch :=
    Agree.trans agreeOr (by simpa [sBranch] using branchAgree)
  have memoryBranch : sBranch.mem = state.mem := by
    calc
      sBranch.mem = sOr.mem := by simpa [sBranch] using branchMemory
      _ = beforeOr.mem := orMemory
      _ = state.mem := memoryBeforeOr
  have codeBranch : Contracts.canonicalContractParams.env.CodeIntact sBranch := by
    rw [Contracts.DecoderEnvironment.CodeIntact, memoryBranch]
    exact pre.code
  have inputAtBranch : sBranch.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simpa [sBranch, decodeInlineRetryPrefixBranchFallThrough, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, sOr, afterRegisterWrite] using inputBeforeOr
  have stackAtBranch : sBranch.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simpa [sBranch, decodeInlineRetryPrefixBranchFallThrough, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, sOr, afterRegisterWrite] using stackBeforeOr
  obtain ⟨tailRetired, tailRun⟩ := decodeInline_retry_tail_pointer_step
    (fromStep + (7 + lengthUsed + prefixUsed)) args state sBranch pre agreeBranch
      (by simpa [sBranch] using branchCounter) codeBranch branchPc inputAtBranch
  let sTail := afterRegisterWrite sBranch (BitVec.ofNat 64 0x103c8) tailRetired x12
    (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))
  have agreeTail : Agree decoderPreserved state sTail := Agree.trans agreeBranch
    (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have counterTail := afterRegisterWrite_retired_present sBranch
    (BitVec.ofNat 64 0x103c8) tailRetired x12
      (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))
  have pcTail : sTail.regs.get? PC = some (BitVec.ofNat 64 0x103cc) := by
    simpa [sTail] using afterRegisterWrite_pc sBranch (BitVec.ofNat 64 0x103c8) tailRetired
      x12 (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))
  have stackTail : sTail.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [sTail, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      stackAtBranch]
  have codeTail : Contracts.canonicalContractParams.env.CodeIntact sTail := by
    simpa [sTail, afterRegisterWrite_mem] using codeBranch
  obtain ⟨resultRetired, resultRun⟩ := decodeInline_retry_result_pointer_step
    (fromStep + (8 + lengthUsed + prefixUsed)) args state sTail pre agreeTail counterTail codeTail
      pcTail stackTail
  let sResult := afterRegisterWrite sTail (BitVec.ofNat 64 0x103cc) resultRetired x10
    (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))
  have agreeResult : Agree decoderPreserved state sResult := Agree.trans agreeTail
    (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have counterResult := afterRegisterWrite_retired_present sTail
    (BitVec.ofNat 64 0x103cc) resultRetired x10
      (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))
  have pcResult : sResult.regs.get? PC = some (BitVec.ofNat 64 0x103d0) := by
    simpa [sResult] using afterRegisterWrite_pc sTail (BitVec.ofNat 64 0x103cc) resultRetired
      x10 (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))
  have stackResult : sResult.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [sResult, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      stackTail]
  have codeResult : Contracts.canonicalContractParams.env.CodeIntact sResult := by
    simpa [sResult, afterRegisterWrite_mem] using codeTail
  obtain ⟨allocatorRetired, allocatorRun⟩ := decodeInline_retry_allocator_pointer_step
    (fromStep + (9 + lengthUsed + prefixUsed)) args state sResult pre agreeResult counterResult
      codeResult pcResult stackResult
  let sAllocator := afterRegisterWrite sResult (BitVec.ofNat 64 0x103d0) allocatorRetired x11
    (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))
  have agreeAllocator : Agree decoderPreserved state sAllocator := Agree.trans agreeResult
    (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have counterAllocator := afterRegisterWrite_retired_present sResult
    (BitVec.ofNat 64 0x103d0) allocatorRetired x11
      (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))
  have pcAllocator : sAllocator.regs.get? PC = some (BitVec.ofNat 64 0x103d4) := by
    simpa [sAllocator] using afterRegisterWrite_pc sResult (BitVec.ofNat 64 0x103d0)
      allocatorRetired x11 (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))
  have codeAllocator : Contracts.canonicalContractParams.env.CodeIntact sAllocator := by
    simpa [sAllocator, afterRegisterWrite_mem] using codeResult
  obtain ⟨pageRetired, pageRun⟩ := decodeInline_retry_call_page_step
    (fromStep + (10 + lengthUsed + prefixUsed)) args state sAllocator pre agreeAllocator
      counterAllocator codeAllocator pcAllocator
  let beforeCall := afterRegisterWrite sAllocator (BitVec.ofNat 64 0x103d4) pageRetired x1
    (BitVec.ofNat 64 0x103d4)
  have agreeBeforeCall : Agree decoderPreserved state beforeCall := Agree.trans agreeAllocator
    (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have counterBeforeCall := afterRegisterWrite_retired_present sAllocator
    (BitVec.ofNat 64 0x103d4) pageRetired x1 (BitVec.ofNat 64 0x103d4)
  have codeBeforeCall : Contracts.canonicalContractParams.env.CodeIntact beforeCall := by
    simpa [beforeCall, afterRegisterWrite_mem] using codeAllocator
  have memoryBeforeCall : beforeCall.mem = state.mem := by
    simpa [beforeCall, sAllocator, sResult, sTail, afterRegisterWrite_mem] using memoryBranch
  have notExit (pc : Nat) (pcFits : pc < 2 ^ 64) (notFinal : pc ≠ 0x103f8) :
      ¬ DecodeInlineExit args (BitVec.ofNat 64 pc) := by
    simp only [DecodeInlineExit, phase, exactPrefix, ↓reduceIte]
    intro equal
    apply notFinal
    have sameNat := congrArg BitVec.toNat equal
    simpa [Nat.mod_eq_of_lt pcFits] using sameNat
  have own (pc word : Nat) (member : (pc, word) ∈ decodeInlineOwnedInstructionWords) :
      functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        (BitVec.ofNat 64 pc) := decodeInline_owned_in_execution_region (pc, word) member
  have pOr : ConfinedPrefix _ _ Level3ChildSummary
      (fromStep + (5 + lengthUsed + prefixUsed)) 1 beforeOr sOr :=
    ConfinedPrefix.ownStep prefixPost.1 (own 0x103c0 0x00a76533 (by simp
      [decodeInlineOwnedInstructionWords])) (notExit 0x103c0 (by decide) (by decide))
      (by simpa [sOr] using orRun)
  have pBranch : ConfinedPrefix _ _ Level3ChildSummary
      (fromStep + (6 + lengthUsed + prefixUsed)) 1 sOr sBranch :=
    ConfinedPrefix.ownStep orPc (own 0x103c4 0x04a69e63 (by simp
      [decodeInlineOwnedInstructionWords])) (notExit 0x103c4 (by decide) (by decide))
      (by simpa [sBranch] using branchRun)
  have pTail : ConfinedPrefix _ _ Level3ChildSummary
      (fromStep + (7 + lengthUsed + prefixUsed)) 1 sBranch sTail :=
    ConfinedPrefix.ownStep branchPc (own 0x103c8 0x00440613 (by simp
      [decodeInlineOwnedInstructionWords])) (notExit 0x103c8 (by decide) (by decide))
      (by simpa [sTail] using tailRun)
  have pResult : ConfinedPrefix _ _ Level3ChildSummary
      (fromStep + (8 + lengthUsed + prefixUsed)) 1 sTail sResult :=
    ConfinedPrefix.ownStep pcTail (own 0x103cc 0x6b010513 (by simp
      [decodeInlineOwnedInstructionWords])) (notExit 0x103cc (by decide) (by decide))
      (by simpa [sResult] using resultRun)
  have pAllocator : ConfinedPrefix _ _ Level3ChildSummary
      (fromStep + (9 + lengthUsed + prefixUsed)) 1 sResult sAllocator :=
    ConfinedPrefix.ownStep pcResult (own 0x103d0 0x01010593 (by simp
      [decodeInlineOwnedInstructionWords])) (notExit 0x103d0 (by decide) (by decide))
      (by simpa [sAllocator] using allocatorRun)
  have pPage : ConfinedPrefix _ _ Level3ChildSummary
      (fromStep + (10 + lengthUsed + prefixUsed)) 1 sAllocator beforeCall :=
    ConfinedPrefix.ownStep pcAllocator (own 0x103d4 0x00000097 (by simp
      [decodeInlineOwnedInstructionWords])) (notExit 0x103d4 (by decide) (by decide))
      (by simpa [beforeCall] using pageRun)
  have prefixOr := ConfinedPrefix.trans prefixTrace pOr
  have pBranchAt : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + ((5 + lengthUsed + prefixUsed) + 1)) 1 sOr sBranch := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pBranch
  have prefixBranch := ConfinedPrefix.trans prefixOr pBranchAt
  have pTailAt : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (((5 + lengthUsed + prefixUsed) + 1) + 1)) 1 sBranch sTail := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pTail
  have prefixTail := ConfinedPrefix.trans prefixBranch pTailAt
  have pResultAt : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + ((((5 + lengthUsed + prefixUsed) + 1) + 1) + 1)) 1 sTail sResult := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pResult
  have prefixResult := ConfinedPrefix.trans prefixTail pResultAt
  have pAllocatorAt : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (((((5 + lengthUsed + prefixUsed) + 1) + 1) + 1) + 1)) 1
      sResult sAllocator := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pAllocator
  have prefixAllocator := ConfinedPrefix.trans prefixResult pAllocatorAt
  have pPageAt : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + ((((((5 + lengthUsed + prefixUsed) + 1) + 1) + 1) + 1) + 1)) 1
      sAllocator beforeCall := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pPage
  have complete := ConfinedPrefix.trans prefixAllocator pPageAt
  have completeLength :
      5 + lengthUsed + prefixUsed + 1 + 1 + 1 + 1 + 1 + 1 = 11 + lengthUsed + prefixUsed := by
    omega
  have resultValue : iTypeResult .ADDI (0x6b0#12) (BitVec.ofNat 64 args.stackBase) =
      BitVec.ofNat 64 (args.stackBase + 0x6b0) := by
    simp only [iTypeResult]
    rw [show sign_extend (0x6b0#12) = (BitVec.ofNat 64 0x6b0) by decide,
      ← BitVec.ofNat_add]
  have allocatorValue : iTypeResult .ADDI (0x010#12) (BitVec.ofNat 64 args.stackBase) =
      BitVec.ofNat 64 args.allocatorBase := by
    simp only [iTypeResult, DecodeInlineArgs.allocatorBase]
    rw [show sign_extend (0x010#12) = (BitVec.ofNat 64 0x10) by decide,
      ← BitVec.ofNat_add]
  have inputValue : iTypeResult .ADDI (0x004#12) (BitVec.ofNat 64 args.inputBase) =
      BitVec.ofNat 64 (args.inputBase + 4) := by
    simp only [iTypeResult]
    rw [show sign_extend (0x004#12) = (BitVec.ofNat 64 4) by decide,
      ← BitVec.ofNat_add]
  have lengthAtBranch : sBranch.regs.get? x13 =
      some (BitVec.ofNat 64 (args.bytes.size - 4)) := by
    simp [sBranch, decodeInlineRetryPrefixBranchFallThrough, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, lengthAtOr]
  have globalsBeforeCall : beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [beforeCall, sAllocator, sResult, sTail, sBranch, sOr, afterRegisterWrite,
      decodeInlineRetryPrefixBranchFallThrough, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, globalsBeforeOr]
  refine ⟨lengthUsed, prefixUsed, beforeCall, lengthBound, prefixBound, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, globalsBeforeCall, agreeBeforeCall, counterBeforeCall, codeBeforeCall, memoryBeforeCall⟩
  · rw [← completeLength]
    exact complete
  · simpa [beforeCall] using afterRegisterWrite_pc sAllocator (BitVec.ofNat 64 0x103d4)
      pageRetired x1 (BitVec.ofNat 64 0x103d4)
  · simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [beforeCall, sAllocator, sResult, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resultValue]
  · simp [beforeCall, sAllocator, sResult, sTail, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, allocatorValue]
  · simp [beforeCall, sAllocator, sResult, sTail, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, inputValue]
  · simp [beforeCall, sAllocator, sResult, sTail, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, lengthAtBranch]
  · simp [beforeCall, sAllocator, sResult, sTail, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, stackAtBranch]

def decodeInlineRetryCallAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103d8) (BitVec.ofNat 64 0x10444) x1
      (BitVec.ofNat 64 0x103dc))
    (BitVec.ofNat 64 0x10444) retired

/-- Execute the second emitted `decodeRaw` call at `0x103d8` through Sail. -/
theorem decodeInline_retry_decodeRaw_call_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103d8))
    (callBase : state.regs.get? x1 = some (BitVec.ofNat 64 0x103d4))
    (resultPointer : state.regs.get? x10 = some (BitVec.ofNat 64 (args.stackBase + 0x6b0)))
    (allocatorPointer : state.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase))
    (inputPointer : state.regs.get? x12 = some (BitVec.ofNat 64 (args.inputBase + 4)))
    (inputLength : state.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4))) :
    ∃ retired,
      Runs (try_step stepNo false) state (decodeInlineRetryCallAfter state retired) false ∧
      (decodeInlineRetryCallAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10444) ∧
      (decodeInlineRetryCallAfter state retired).regs.get? x1 =
        some (BitVec.ofNat 64 0x103dc) ∧
      (decodeInlineRetryCallAfter state retired).regs.get? x10 =
        some (BitVec.ofNat 64 (args.stackBase + 0x6b0)) ∧
      (decodeInlineRetryCallAfter state retired).regs.get? x11 =
        some (BitVec.ofNat 64 args.allocatorBase) ∧
      (decodeInlineRetryCallAfter state retired).regs.get? x12 =
        some (BitVec.ofNat 64 (args.inputBase + 4)) ∧
      (decodeInlineRetryCallAfter state retired).regs.get? x13 =
        some (BitVec.ofNat 64 (args.bytes.size - 4)) ∧
      Agree decoderPreserved state (decodeInlineRetryCallAfter state retired) ∧
      (decodeInlineRetryCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (decodeInlineRetryCallAfter state retired) := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103d8, 0x070080e7)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have code : Artifacts.programImage.fileBytesMatchMemory state.mem := by
    rw [memory]
    exact hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103d8) 0xe7#8 0x80#8 0x00#8 0x07#8 :=
    fetchInstruction state 0x103d8 0xe7 0x80 0x00 0x07 code
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree pre.machine agree
    (BitVec.ofNat 64 0x103d8) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree pre.machine.normal agree retiredPresent
  have wordEq : fetchWord 0xe7#8 0x80#8 0x00#8 0x07#8 =
      (0x070080e7 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xe7#8 0x80#8 0x00#8 0x07#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0x070#12, .Regidx 1#5, .Regidx 1#5)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103d8)
  have executeAgree : Agree decoderPreserved baseState executeState :=
    Agree.trans agree (Agree.weaken (fun _ preserved => preserved.2)
      (agree_stepPremiseState state (BitVec.ofNat 64 0x103d8)))
  have helpElp : Runs (update_elp_state (.Regidx 1#5)) executeState executeState () :=
    pre.machine.landingPad executeState (.Regidx 1#5) trivial executeAgree
  have linkRead : executeState.regs.get? nextPC = some (BitVec.ofNat 64 0x103dc) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x103d8) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp
    decide
  have sourceRead : executeState.regs.get? x1 = some (BitVec.ofNat 64 0x103d4) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, callBase]
  have targetEq : Sail.BitVec.update
      ((BitVec.ofNat 64 0x103d4) + sign_extend (m := 64) (0x070#12)) 0 0#1 =
      BitVec.ofNat 64 0x10444 := by decide
  have hwrite : Runs (wX_bits (.Regidx 1#5) (BitVec.ofNat 64 0x103dc))
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x103d8) (BitVec.ofNat 64 0x10444))
      (callLinkState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x103d8) (BitVec.ofNat 64 0x10444) x1
        (BitVec.ofNat 64 0x103dc)) () := wX_bits_run_x1 _ _
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      baseState.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := pre.machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match misaRead : baseState.regs.get? misa with
    | none => simp [misaRead] at normalMisa
    | some misaBits => exact ⟨misaBits, rfl, by simpa [misaRead] using normalMisa⟩
  have misaState : state.regs.get? misa = some misaBits :=
    (agree misa (by simp [decoderPreserved, platformPreserved])).trans misaRead
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x103d8)
    misaBits misaState
  have callRun := tryStepJalrCallRetires stepNo state
    (BitVec.ofNat 64 0x103d8) (BitVec.ofNat 64 0x103d4) retired
    (BitVec.ofNat 64 0x103dc) (0x070#12) (.Regidx 1#5) (.Regidx 1#5) x1
    (BitVec.ofNat 64 0x103dc) inhibit config 0xe7#8 0x80#8 0x00#8 0x07#8
    (_get_Misa_C misaBits == 1#1)
    (by simpa [targetEq] using hwrite) (by decide) (by decide) (by decide) (by decide)
    fetch noMMIO fetchBytes interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected helpElp (get_next_pc_run executeState _ linkRead)
    (rX_bits_run_x1 executeState _ sourceRead) (by decide) zca hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead
  have run : Runs (try_step stepNo false) state
      (decodeInlineRetryCallAfter state retired) false := by
    simpa [decodeInlineRetryCallAfter, targetEq] using callRun
  have pcAfter : (decodeInlineRetryCallAfter state retired).regs.get? PC =
      some (BitVec.ofNat 64 0x10444) := by
    simp [decodeInlineRetryCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  have linkAfter : (decodeInlineRetryCallAfter state retired).regs.get? x1 =
      some (BitVec.ofNat 64 0x103dc) := by
    apply tryStepControlFlowAfterRetired_preserves_register
    · exact callLinkState_link _ _ _ x1 (BitVec.ofNat 64 0x103dc)
    · decide
    · decide
  have callAgree : Agree decoderPreserved state (decodeInlineRetryCallAfter state retired) := by
    apply jalrCallAfterRetired_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  have preserveGeneral (register : Register) (notLink : register ≠ x1)
      (notPc : register ≠ PC) (notNextPc : register ≠ nextPC)
      (notIncrement : register ≠ minstret_increment) (notRetired : register ≠ minstret) :
      (decodeInlineRetryCallAfter state retired).regs.get? register = state.regs.get? register := by
    have preserved := jalrCallAfterRetired_agree_of
      (P := fun candidate => candidate = register) state (BitVec.ofNat 64 0x103d8)
      (BitVec.ofNat 64 0x10444) retired x1 (BitVec.ofNat 64 0x103dc)
      (Ne.symm notLink) (Ne.symm notPc) (Ne.symm notNextPc)
      (Ne.symm notIncrement) (Ne.symm notRetired)
    exact preserved register rfl
  refine ⟨retired, run, pcAfter, linkAfter,
    (preserveGeneral x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      resultPointer,
    (preserveGeneral x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      allocatorPointer,
    (preserveGeneral x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      inputPointer,
    (preserveGeneral x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      inputLength,
    callAgree, jalrCallAfterRetired_mem _ _ _ _ _ _, ?_⟩
  exact ⟨Sail.BitVec.addInt retired 1, by
    simp [decodeInlineRetryCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]⟩

def decodeRawRetryCallTransfer (fromStep used : Nat) (args : DecodeInlineArgs)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true)
    (beforeCall childEntry childExit resumed : State)
    (atCall : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103d8))
    (callRun : Runs (try_step fromStep false) beforeCall childEntry false)
    (childPre : compiledDecodeRawContract.binding.entry args.retryRawArgs childEntry)
    (bound : used ≤ compiledDecodeRawContract.binding.stepBound args.retryRawArgs)
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
      (Contracts.functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
      (fromStep + 1) used childEntry childExit)
    (childPost : compiledDecodeRawContract.binding.exit args.retryRawArgs
      (compiledDecodeRawContract.spec.meaning args.retryRawArgs) childEntry childExit)
    (returnRun : Runs (try_step (fromStep + 1 + used) false) childExit resumed false)
    (atResume : resumed.regs.get? PC = some (BitVec.ofNat 64 0x103dc)) :
    CallTransfer
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary decodeRawRetryCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw fromStep used beforeCall resumed := by
  have atRet : childExit.regs.get? PC = some (BitVec.ofNat 64 0x10530) := by
    obtain ⟨retPc, atRet, retIsExit⟩ := childTrace.trace.final_at_exit
    have retPcEq : retPc = BitVec.ofNat 64 0x10530 := by
      apply BitVec.eq_of_toNat_eq
      simpa [functionInstanceExitPred, FunctionInstance.isExit,
        functionInstance_ssz_raw_decodeRaw] using retIsExit
    simpa [retPcEq] using atRet
  have callInRegion := decodeInline_owned_in_execution_region (0x103d8, 0x070080e7)
    (by simp [decodeInlineOwnedInstructionWords])
  have returnInRegion := decodeInline_owned_in_execution_region (0x103dc, 0x02010513)
    (by simp [decodeInlineOwnedInstructionWords])
  have retInRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x10530) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have callNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x103d8) := by
    simp [DecodeInlineExit, phase, exactPrefix]
  have retNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10530) := by
    simp [DecodeInlineExit, phase, exactPrefix]
  have body : Level3ChildSummary functionInstance_ssz_raw_decodeRawId
      (fromStep + 1) used childEntry childExit :=
    Level3ChildSummary.decodeRaw
      ⟨rfl, args.retryRawArgs, childPre, bound, childTrace, childPost⟩
  exact
    { valid := decodeRawRetryCall_valid
      callPc := BitVec.ofNat 64 0x103d8
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
      returnPc := BitVec.ofNat 64 0x103dc
      atResume := atResume
      returnMatches := by decide
      resumeInRegion := returnInRegion }

/-- Consume the second `decodeRaw` contract only after the exact-prefix path has executed the real
call setup. The child receives the four-byte-stripped input region, then its real `ret` returns to
`0x103dc`. -/
theorem decodeInline_retry_call_transfer
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true) :
    ∃ lengthUsed prefixUsed childUsed beforeCall resumed,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      prefixUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.retryRawArgs ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep
          (11 + lengthUsed + prefixUsed) state beforeCall ∧
      Nonempty (CallTransfer
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary decodeRawRetryCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + (11 + lengthUsed + prefixUsed))
          childUsed beforeCall resumed) ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.retryRawArgs
        Contracts.canonicalContractParams.repRawV4
        (Contracts.meaningDecodeRaw args.retryRawArgs.bytes) state resumed ∧
      Agree decoderPreserved state resumed ∧
      RetiredCounterPresent resumed ∧
      resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      DecodeRawResultPayloadInitialized args.retryRawArgs resumed ∧
      Contracts.canonicalContractParams.env.CodeIntact resumed ∧
      DecodeInlineCallerSaveArea args state resumed := by
  obtain ⟨lengthUsed, prefixUsed, beforeCall, lengthBound, prefixBound, parentPrefix, callPc,
    callBase, resultPointer, allocatorPointer, inputPointer, inputLength, beforeStack,
    beforeGlobals, beforeAgree, beforeCounter, beforeCode, beforeMemory⟩ :=
    decodeInline_retry_before_second_decodeRaw_call fromStep args state pre phase exactPrefix
  obtain ⟨callRetired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, callAgree, callMemory, childCounter⟩ :=
    decodeInline_retry_decodeRaw_call_step
      (fromStep + (11 + lengthUsed + prefixUsed)) args state beforeCall pre beforeAgree
      beforeMemory beforeCounter callPc callBase resultPointer allocatorPointer inputPointer
      inputLength
  let childEntry := decodeInlineRetryCallAfter beforeCall callRetired
  have childAgree : Agree decoderPreserved state childEntry := Agree.trans beforeAgree callAgree
  have childMemory : childEntry.mem = state.mem := callMemory.trans beforeMemory
  have childStack : childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [childEntry, decodeInlineRetryCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, callLinkState, controlFlowJumpState,
      tryStepControlFlowAfterIncrement, coreControlFlowNextState, Std.ExtDHashMap.get?_insert,
      beforeStack]
  have childGlobals : childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [childEntry, decodeInlineRetryCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, callLinkState, controlFlowJumpState,
      tryStepControlFlowAfterIncrement, coreControlFlowNextState, Std.ExtDHashMap.get?_insert,
      beforeGlobals]
  have fourBytes : 4 ≤ args.bytes.size := by
    rw [Contracts.meaningHasExactErePrefix] at exactPrefix
    split at exactPrefix <;> simp_all
  have tailSize : args.retryRawArgs.bytes.size = args.bytes.size - 4 := by
    simp [DecodeInlineArgs.retryRawArgs, ByteArray.size_extract]
  have childMachineAtParentExtent : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono childAgree childCounter
  have readableSubset : ∀ address,
      DecoderReadableByte (entryMachineArgs args.retryRawArgs) address →
        DecoderReadableByte args.machineArgs address := by
    intro address readable
    rcases readable with image | input | stack | allocator | arena
    · exact Or.inl image
    · exact Or.inr (Or.inl ⟨by
        simp only [entryMachineArgs, DecodeInlineArgs.retryRawArgs] at input
        simp only [DecodeInlineArgs.machineArgs]
        omega, by
        simp only [entryMachineArgs, DecodeInlineArgs.retryRawArgs] at input
        simp only [DecodeInlineArgs.machineArgs]
        have right := input.2
        simp only [ByteArray.size_extract] at right
        omega⟩)
    · exact Or.inr (Or.inr (Or.inl stack))
    · exact Or.inr (Or.inr (Or.inr (Or.inl allocator)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr arena)))
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
      (entryMachineArgs args.retryRawArgs) childEntry :=
    (childMachineAtParentExtent.narrowInput readableSubset).restrict childExtentWithinParent
  have childSourceEntry : Contracts.preEntry Contracts.canonicalContractParams.env
      args.retryRawArgs childEntry := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro index bound
      have originalBound : 4 + index < args.bytes.size := by
        rw [tailSize] at bound
        omega
      rw [childMemory]
      have original := pre.inputMemory (4 + index) originalBound
      simpa [DecodeInlineArgs.retryRawArgs, Nat.add_assoc,
        ByteArray.getElem_extract] using original
    · change Contracts.canonicalContractParams.env.image.fileBytesMatchMemory childEntry.mem
      rw [childMemory]
      exact pre.code
    · simpa [DecodeInlineArgs.retryRawArgs] using childResult
    · simpa [DecodeInlineArgs.retryRawArgs] using childAllocator
    · simpa [DecodeInlineArgs.retryRawArgs] using childInput
    · simpa [DecodeInlineArgs.retryRawArgs, tailSize] using childLength
  have childPre : compiledDecodeRawContract.binding.entry args.retryRawArgs childEntry :=
    ⟨childSourceEntry, childPc, childMachine⟩
  obtain ⟨childUsed, childExit, childBound, childTrace, childPost⟩ :=
    contract args.retryRawArgs (fromStep + (12 + lengthUsed + prefixUsed)) childEntry childPre
  obtain ⟨returnRetired, returnRun, atResume⟩ :=
    decodeRaw_return_step (fromStep + (12 + lengthUsed + prefixUsed + childUsed))
      args.retryRawArgs (BitVec.ofNat 64 0x103dc) childEntry childExit (by decide) (by decide)
      childPre childTrace childLink childPost
  let resumed := decodeRawReturnAfter (BitVec.ofNat 64 0x103dc) childExit returnRetired
  rcases childPost with ⟨sourcePost, childFrame, childExitCounter, childPayload, childSaveArea⟩
  rcases sourcePost with ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have childFrameDecoder : Agree decoderPreserved childEntry childExit :=
    Agree.weaken (fun _ preserved => Or.inl preserved.2) childFrame
  have resumedAgree : Agree decoderPreserved state resumed := Agree.trans childAgree
    (Agree.trans childFrameDecoder (by
      simpa [resumed] using
        decodeRawReturnAfter_agree (BitVec.ofNat 64 0x103dc) childExit returnRetired))
  have exitStack : childExit.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (childFrame x2 (by simp [decodeRawCallerPreserved])).trans childStack
  have resumedStack : resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [resumed, decodeRawReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert, exitStack]
  have exitGlobals : childExit.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (childFrame x18 (by simp [decodeRawCallerPreserved])).trans childGlobals
  have resumedGlobals : resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [resumed, decodeRawReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert, exitGlobals]
  have resumedPost : Contracts.postEntry Contracts.canonicalContractParams.env args.retryRawArgs
      Contracts.canonicalContractParams.repRawV4
      (Contracts.meaningDecodeRaw args.retryRawArgs.bytes) state resumed := by
    apply canonicalPostEntry_of_mem_eq args.retryRawArgs
      (Contracts.meaningDecodeRaw args.retryRawArgs.bytes) childMemory.symm
      (decodeRawReturnAfter_mem (BitVec.ofNat 64 0x103dc) childExit returnRetired)
    exact ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have transfer := decodeRawRetryCallTransfer
    (fromStep + (11 + lengthUsed + prefixUsed)) childUsed args phase exactPrefix beforeCall
      childEntry childExit resumed callPc (by simpa [childEntry] using callRun) childPre childBound
      (by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using childTrace)
      ⟨⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩,
        childFrame, childExitCounter, childPayload, childSaveArea⟩
      (by simpa [resumed, Nat.add_assoc] using returnRun) (by simpa [resumed] using atResume)
  have resumedCode : Contracts.canonicalContractParams.env.CodeIntact resumed := by
    simpa [resumed, decodeRawReturnAfter] using childCode
  have resumedPayload : DecodeRawResultPayloadInitialized args.retryRawArgs resumed := by
    obtain ⟨contents, contentsSize, contentsMemory⟩ := childPayload
    exact ⟨contents, contentsSize, by
      intro index bound
      rw [decodeRawReturnAfter_mem (BitVec.ofNat 64 0x103dc) childExit returnRetired]
      exact contentsMemory index bound⟩
  have resumedSaveArea : DecodeInlineCallerSaveArea args state resumed := by
    intro index bound
    rw [decodeRawReturnAfter_mem (BitVec.ofNat 64 0x103dc) childExit returnRetired]
    calc
      childExit.mem.get? (args.stackBase + 0xa00 + index) =
          childEntry.mem.get? (args.stackBase + 0xa00 + index) := by
        simpa [DecodeInlineCallerSaveArea, DecodeRawCallerSaveArea,
          DecodeInlineArgs.retryRawArgs, DecodeInlineArgs.allocatorBase, Nat.add_assoc] using
          childSaveArea index bound
      _ = state.mem.get? (args.stackBase + 0xa00 + index) := by rw [childMemory]
  exact ⟨lengthUsed, prefixUsed, childUsed, beforeCall, resumed, lengthBound, prefixBound,
    childBound, parentPrefix, ⟨transfer⟩, resumedPost, resumedAgree,
    decodeRawReturnAfter_retired (BitVec.ofNat 64 0x103dc) childExit returnRetired,
    resumedStack, resumedGlobals, resumedPayload, resumedCode, resumedSaveArea⟩

/-! ## Retry payload copy -/

/-- Execute `addi a0, sp, 0x20`, selecting the final result payload destination. -/
theorem decodeInline_retry_copy_destination_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103dc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103dc) retired x10
        (iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103dc, 0x02010513)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103dc) 0x13#8 0x05#8 0x01#8 0x02#8 :=
    fetchInstruction state 0x103dc 0x13 0x05 0x01 0x02 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103dc) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x05#8 0x01#8 0x02#8 =
      (0x02010513 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x01#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 10#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103dc)
  have stackAtExecute : executeState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  let result := iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase)
  have execute : Runs (execute (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 10#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x10 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x020#12 (.Regidx 2#5) (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x020#12 (.Regidx 2#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 args.stackBase) (rX_bits_run_x2 executeState _ stackAtExecute)
      (wX_x10_run executeState result)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x103dc) pcIn atPc 0x13#8 0x05#8 0x01#8 0x02#8
    (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 10#5, .ADDI)) x10 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `addi a1, sp, 0x6b0`, selecting the retry result payload source. -/
theorem decodeInline_retry_copy_source_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103e0))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103e0) retired x11
        (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103e0, 0x6b010593)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103e0) 0x93#8 0x05#8 0x01#8 0x6b#8 :=
    fetchInstruction state 0x103e0 0x93 0x05 0x01 0x6b image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103e0) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x93#8 0x05#8 0x01#8 0x6b#8 =
      (0x6b010593 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x01#8 0x6b#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x6b0#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103e0)
  have stackAtExecute : executeState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  let result := iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase)
  have execute : Runs (execute (.ITYPE (0x6b0#12, .Regidx 2#5, .Regidx 11#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x11 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x6b0#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x6b0#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI
      (BitVec.ofNat 64 args.stackBase) (rX_bits_run_x2 executeState _ stackAtExecute)
      (wX_x11_run executeState result)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x103e0) pcIn atPc 0x93#8 0x05#8 0x01#8 0x6b#8
    (.ITYPE (0x6b0#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) x11 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `addi a2, x0, 0x340`, fixing the payload copy length at 832 bytes. -/
theorem decodeInline_retry_copy_length_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103e4)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103e4) retired x12
        (iTypeResult .ADDI 0x340#12 (0#64))) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103e4, 0x34000613)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103e4) 0x13#8 0x06#8 0x00#8 0x34#8 :=
    fetchInstruction state 0x103e4 0x13 0x06 0x00 0x34 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103e4) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x06#8 0x00#8 0x34#8 =
      (0x34000613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x00#8 0x34#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103e4)
  let result := iTypeResult .ADDI 0x340#12 (0#64)
  have execute : Runs (execute (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x12 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x340#12 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x340#12 (.Regidx 0#5) (.Regidx 12#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x12_run executeState result)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x103e4) pcIn atPc 0x13#8 0x06#8 0x00#8 0x34#8
    (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)) x12 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `auipc ra, 4`, preparing the retry `memcpy` call base. -/
theorem decodeInline_retry_copy_call_page_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103e8)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103e8) retired x1
        (BitVec.ofNat 64 0x143e8)) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103e8, 0x00004097)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103e8) 0x97#8 0x40#8 0x00#8 0x00#8 :=
    fetchInstruction state 0x103e8 0x97 0x40 0x00 0x00 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103e8) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x97#8 0x40#8 0x00#8 0x00#8 =
      (0x00004097 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x97#8 0x40#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103e8)
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x103e8) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC))) executeState
      { executeState with regs := executeState.regs.insert x1 (BitVec.ofNat 64 0x143e8) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_auipc_run executeState _ 0x00004#20 (.Regidx 1#5)
      (BitVec.ofNat 64 0x103e8)
    · exact readReg_run _ _ _ pcAtExecute
    · simpa using wX_bits_run_x1 executeState (BitVec.ofNat 64 0x143e8)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x103e8) pcIn atPc 0x97#8 0x40#8 0x00#8 0x00#8
    (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC)) x1 (BitVec.ofNat 64 0x143e8) fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute the four retry-copy setup words and establish the exact compiled `memcpy` arguments. -/
theorem decodeInline_retry_copy_setup (fromStep : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (globalsRead : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103dc))
    (payload : DecodeRawResultPayloadInitialized args.retryRawArgs state) :
    ∃ contents beforeCall,
      contents.size = 832 ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state beforeCall ∧
      beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103ec) ∧
      beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x143e8) ∧
      beforeCall.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase) ∧
      beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.retryRawArgs.resultBase) ∧
      beforeCall.regs.get? x12 = some (BitVec.ofNat 64 832) ∧
      beforeCall.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      MemoryRepresentation.MemoryBytes beforeCall args.retryRawArgs.resultBase contents ∧
      Agree decoderPreserved baseState beforeCall ∧
      RetiredCounterPresent beforeCall ∧
      Contracts.canonicalContractParams.env.CodeIntact beforeCall ∧
      beforeCall.mem = state.mem := by
  obtain ⟨contents, contentsSize, contentsMemory⟩ := payload
  let destination := iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired1, run1⟩ := decodeInline_retry_copy_destination_step fromStep args
    baseState state pre agree retiredPresent code atPc stackRead
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103dc) retired1 x10 destination
  have agree1 : Agree decoderPreserved baseState s1 := Agree.trans agree
    (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x103e0) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103dc) retired1 x10 destination
  have stack1 : s1.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [s1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      stackRead]
  have code1 : Contracts.canonicalContractParams.env.CodeIntact s1 := by
    simpa [s1, afterRegisterWrite_mem] using code
  let source := iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired2, run2⟩ := decodeInline_retry_copy_source_step (fromStep + 1) args
    baseState s1 pre agree1
      (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103dc) retired1 x10 destination)
      code1 pc1 stack1
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x103e0) retired2 x11 source
  have agree2 : Agree decoderPreserved baseState s2 := Agree.trans agree1
    (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x103e4) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x103e0) retired2 x11 source
  have code2 : Contracts.canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, afterRegisterWrite_mem] using code1
  let length := iTypeResult .ADDI 0x340#12 (0#64)
  obtain ⟨retired3, run3⟩ := decodeInline_retry_copy_length_step (fromStep + 2) args
    baseState s2 pre agree2
      (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x103e0) retired2 x11 source)
      code2 pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x103e4) retired3 x12 length
  have agree3 : Agree decoderPreserved baseState s3 := Agree.trans agree2
    (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x103e8) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x103e4) retired3 x12 length
  have code3 : Contracts.canonicalContractParams.env.CodeIntact s3 := by
    simpa [s3, afterRegisterWrite_mem] using code2
  obtain ⟨retired4, run4⟩ := decodeInline_retry_copy_call_page_step (fromStep + 3) args
    baseState s3 pre agree3
      (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x103e4) retired3 x12 length)
      code3 pc3
  let beforeCall := afterRegisterWrite s3 (BitVec.ofNat 64 0x103e8) retired4 x1
    (BitVec.ofNat 64 0x143e8)
  have notExit (pc : Nat) (pcFits : pc < 2 ^ 64) (different : pc ≠ 0x103f8) :
      ¬ DecodeInlineExit args (BitVec.ofNat 64 pc) := by
    simp only [DecodeInlineExit, phase, exactPrefix, ↓reduceIte]
    intro equal
    apply different
    have sameNat := congrArg BitVec.toNat equal
    simpa [Nat.mod_eq_of_lt pcFits] using sameNat
  have p1 : ConfinedPrefix _ _ Level3ChildSummary fromStep 1 state s1 :=
    ConfinedPrefix.ownStep atPc
      (decodeInline_owned_in_execution_region (0x103dc, 0x02010513)
        (by simp [decodeInlineOwnedInstructionWords])) (notExit 0x103dc (by decide) (by decide))
      (by simpa [s1, destination] using run1)
  have p2 : ConfinedPrefix _ _ Level3ChildSummary (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep pc1
      (decodeInline_owned_in_execution_region (0x103e0, 0x6b010593)
        (by simp [decodeInlineOwnedInstructionWords])) (notExit 0x103e0 (by decide) (by decide))
      (by simpa [s2, source] using run2)
  have p3 : ConfinedPrefix _ _ Level3ChildSummary (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep pc2
      (decodeInline_owned_in_execution_region (0x103e4, 0x34000613)
        (by simp [decodeInlineOwnedInstructionWords])) (notExit 0x103e4 (by decide) (by decide))
      (by simpa [s3, length] using run3)
  have p4 : ConfinedPrefix _ _ Level3ChildSummary (fromStep + 3) 1 s3 beforeCall :=
    ConfinedPrefix.ownStep pc3
      (decodeInline_owned_in_execution_region (0x103e8, 0x00004097)
        (by simp [decodeInlineOwnedInstructionWords])) (notExit 0x103e8 (by decide) (by decide))
      (by simpa [beforeCall] using run4)
  have complete := ConfinedPrefix.trans (ConfinedPrefix.trans (ConfinedPrefix.trans p1 p2) p3) p4
  have destinationEq : destination = BitVec.ofNat 64 args.finalResultBase := by
    simp only [destination, iTypeResult, DecodeInlineArgs.finalResultBase]
    rw [show sign_extend (0x020#12) = (BitVec.ofNat 64 0x20) by decide,
      ← BitVec.ofNat_add]
  have sourceEq : source = BitVec.ofNat 64 args.retryRawArgs.resultBase := by
    simp only [source, iTypeResult, DecodeInlineArgs.retryRawArgs]
    rw [show sign_extend (0x6b0#12) = (BitVec.ofNat 64 0x6b0) by decide,
      ← BitVec.ofNat_add]
  have lengthEq : length = BitVec.ofNat 64 832 := by simp [length, iTypeResult]; decide
  have globalsBeforeCall : beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [beforeCall, s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, globalsRead]
  refine ⟨contents, beforeCall, contentsSize, by simpa using complete, ?_, ?_, ?_, ?_, ?_, ?_,
    globalsBeforeCall, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [beforeCall] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x103e8) retired4 x1
      (BitVec.ofNat 64 0x143e8)
  · simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [beforeCall, s3, s2, s1, destinationEq, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [beforeCall, s3, s2, sourceEq, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [beforeCall, s3, lengthEq, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [beforeCall, s3, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  · intro index bound
    have memoryEq : beforeCall.mem = state.mem := by
      simp [beforeCall, s3, s2, s1, afterRegisterWrite_mem]
    rw [memoryEq]
    exact contentsMemory index bound
  · exact Agree.trans agree3 (afterRegisterWrite_agree_of
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  · exact afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x103e8) retired4 x1
      (BitVec.ofNat 64 0x143e8)
  · simpa [beforeCall, afterRegisterWrite_mem] using code3
  · simp [beforeCall, s3, s2, s1, afterRegisterWrite_mem]

def decodeInlineMemcpyCallAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103ec) (BitVec.ofNat 64 0x13eb8) x1
      (BitVec.ofNat 64 0x103f0))
    (BitVec.ofNat 64 0x13eb8) retired

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
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103ec, 0xad0080e7)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103ec) 0xe7#8 0x80#8 0x00#8 0xad#8 :=
    fetchInstruction state 0x103ec 0xe7 0x80 0x00 0xad image
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree pre.machine agree
    (BitVec.ofNat 64 0x103ec) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree pre.machine.normal agree retiredPresent
  have wordEq : fetchWord 0xe7#8 0x80#8 0x00#8 0xad#8 =
      (0xad0080e7 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xe7#8 0x80#8 0x00#8 0xad#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0xad0#12, .Regidx 1#5, .Regidx 1#5)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103ec)
  have executeAgree : Agree decoderPreserved baseState executeState := Agree.trans agree
    (Agree.weaken (fun _ preserved => preserved.2)
      (agree_stepPremiseState state (BitVec.ofNat 64 0x103ec)))
  have helpElp : Runs (update_elp_state (.Regidx 1#5)) executeState executeState () :=
    pre.machine.landingPad executeState (.Regidx 1#5) trivial executeAgree
  have linkRead : executeState.regs.get? nextPC = some (BitVec.ofNat 64 0x103f0) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x103ec) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp
    decide
  have sourceRead : executeState.regs.get? x1 = some (BitVec.ofNat 64 0x143e8) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, callBase]
  have targetEq : Sail.BitVec.update
      ((BitVec.ofNat 64 0x143e8) + sign_extend (m := 64) (0xad0#12)) 0 0#1 =
      BitVec.ofNat 64 0x13eb8 := by decide
  have hwrite : Runs (wX_bits (.Regidx 1#5) (BitVec.ofNat 64 0x103f0))
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x103ec) (BitVec.ofNat 64 0x13eb8))
      (callLinkState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x103ec) (BitVec.ofNat 64 0x13eb8) x1
        (BitVec.ofNat 64 0x103f0)) () := wX_bits_run_x1 _ _
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      baseState.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := pre.machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match misaRead : baseState.regs.get? misa with
    | none => simp [misaRead] at normalMisa
    | some misaBits => exact ⟨misaBits, rfl, by simpa [misaRead] using normalMisa⟩
  have misaState : state.regs.get? misa = some misaBits :=
    (agree misa (by simp [decoderPreserved, platformPreserved])).trans misaRead
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x103ec)
    misaBits misaState
  have callRun := tryStepJalrCallRetires stepNo state
    (BitVec.ofNat 64 0x103ec) (BitVec.ofNat 64 0x143e8) retired
    (BitVec.ofNat 64 0x103f0) (0xad0#12) (.Regidx 1#5) (.Regidx 1#5) x1
    (BitVec.ofNat 64 0x103f0) inhibit config 0xe7#8 0x80#8 0x00#8 0xad#8
    (_get_Misa_C misaBits == 1#1)
    (by simpa [targetEq] using hwrite) (by decide) (by decide) (by decide) (by decide)
    fetch noMMIO fetchBytes interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected helpElp (get_next_pc_run executeState _ linkRead)
    (rX_bits_run_x1 executeState _ sourceRead) (by decide) zca hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead
  have run : Runs (try_step stepNo false) state
      (decodeInlineMemcpyCallAfter state retired) false := by
    simpa [decodeInlineMemcpyCallAfter, targetEq] using callRun
  have preserveGeneral (register : Register) (notLink : register ≠ x1)
      (notPc : register ≠ PC) (notNextPc : register ≠ nextPC)
      (notIncrement : register ≠ minstret_increment) (notRetired : register ≠ minstret) :
      (decodeInlineMemcpyCallAfter state retired).regs.get? register =
        state.regs.get? register := by
    have preserved := jalrCallAfterRetired_agree_of
      (P := fun candidate => candidate = register) state (BitVec.ofNat 64 0x103ec)
      (BitVec.ofNat 64 0x13eb8) retired x1 (BitVec.ofNat 64 0x103f0)
      (Ne.symm notLink) (Ne.symm notPc) (Ne.symm notNextPc)
      (Ne.symm notIncrement) (Ne.symm notRetired)
    exact preserved register rfl
  refine ⟨retired, run, ?_, ?_, preserveGeneral x10 (by decide) (by decide) (by decide)
    (by decide) (by decide), preserveGeneral x11 (by decide) (by decide) (by decide)
    (by decide) (by decide), preserveGeneral x12 (by decide) (by decide) (by decide)
    (by decide) (by decide), preserveGeneral x2 (by decide) (by decide) (by decide)
    (by decide) (by decide), ?_, jalrCallAfterRetired_mem _ _ _ _ _ _, ?_⟩
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

def decodeInlineRetryCopyArgs (args : DecodeInlineArgs) (contents : ByteArray) :
    Contracts.CopyArgs where
  destination := args.finalResultBase
  source := args.retryRawArgs.resultBase
  length := 832
  contents := contents

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

/-- Execute the retry call and consume the already-proved compiled `memcpy` contract on the exact
832-byte payload retained from the second `decodeRaw` result. -/
theorem decodeInline_retry_uses_memcpy (fromStep : Nat) (args : DecodeInlineArgs)
    (contents : ByteArray) (baseState beforeCall : State) (pre : DecodeInlinePre args baseState)
    (contentsSize : contents.size = 832)
    (sourceMemory : MemoryRepresentation.MemoryBytes beforeCall
      args.retryRawArgs.resultBase contents)
    (agree : Agree decoderPreserved baseState beforeCall)
    (counter : RetiredCounterPresent beforeCall)
    (code : Contracts.canonicalContractParams.env.CodeIntact beforeCall)
    (atCall : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103ec))
    (callBase : beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x143e8))
    (destination : beforeCall.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase))
    (source : beforeCall.regs.get? x11 = some
      (BitVec.ofNat 64 args.retryRawArgs.resultBase))
    (length : beforeCall.regs.get? x12 = some (BitVec.ofNat 64 832)) :
    ∃ callRetired childUsed childEntry childExit,
      childEntry = decodeInlineMemcpyCallAfter beforeCall callRetired ∧
      childEntry.regs.get? x18 = beforeCall.regs.get? x18 ∧
      Runs (try_step fromStep false) beforeCall childEntry false ∧
      (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.entry
        (decodeInlineRetryCopyArgs args contents) childEntry ∧
      childUsed ≤ (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.stepBound
        (decodeInlineRetryCopyArgs args contents) ∧
      EnteredFunctionTrace
        (functionInstanceExecutionPcs generatedProgram functionInstance_memcpy)
        (functionInstanceExitPred functionInstance_memcpy)
        (Contracts.functionInstanceEntryWord functionInstance_memcpy)
        (fromStep + 1) childUsed childEntry childExit ∧
      (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.exit
        (decodeInlineRetryCopyArgs args contents)
        ((compiledMemcpyContract Contracts.canonicalContractParams.env).spec.meaning
          (decodeInlineRetryCopyArgs args contents)) childEntry childExit := by
  obtain ⟨callRetired, callRun, childPc, childLink, childDestination, childSource,
    childLength, childStack, callAgree, callMemory, childCounter⟩ :=
    decodeInline_retry_memcpy_call_step fromStep args baseState beforeCall pre agree
      code counter atCall callBase
  let childEntry := decodeInlineMemcpyCallAfter beforeCall callRetired
  let copyArgs := decodeInlineRetryCopyArgs args contents
  have childAgree : Agree decoderPreserved baseState childEntry := Agree.trans agree callAgree
  have childCode : Contracts.canonicalContractParams.env.CodeIntact childEntry := by
    rw [Contracts.DecoderEnvironment.CodeIntact, show childEntry.mem = beforeCall.mem by
      simpa [childEntry] using callMemory]
    exact code
  have childSourceMemory : MemoryRepresentation.MemoryBytes childEntry
      args.retryRawArgs.resultBase contents := by
    intro index bound
    rw [show childEntry.mem = beforeCall.mem by simpa [childEntry] using callMemory]
    exact sourceMemory index bound
  have machinePre : MemcpyMachinePre Contracts.canonicalContractParams.env copyArgs childEntry := by
    apply decodeInline_retry_memcpy_machine_pre args contents baseState childEntry pre childAgree
      childCounter
    · simpa [childEntry] using childPc
    · simpa [childEntry] using childLink
  have sourcePre : (Contracts.contractMemcpy Contracts.canonicalContractParams.env).pre
      copyArgs childEntry := by
    constructor
    · refine ⟨childSourceMemory, ?_, childCode, ?_, ?_, ?_⟩
      · simpa [copyArgs, decodeInlineRetryCopyArgs] using contentsSize
      · simpa [copyArgs, decodeInlineRetryCopyArgs, childEntry] using childDestination.trans destination
      · simpa [copyArgs, decodeInlineRetryCopyArgs, childEntry] using childSource.trans source
      · simpa [copyArgs, decodeInlineRetryCopyArgs, childEntry] using childLength.trans length
    · left
      dsimp [copyArgs, decodeInlineRetryCopyArgs, DecodeInlineArgs.finalResultBase,
        DecodeInlineArgs.retryRawArgs]
      omega
  have compiledEntry :
      (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.entry
        copyArgs childEntry := ⟨sourcePre, machinePre⟩
  obtain ⟨childUsed, childExit, childBound, childTrace, childPost⟩ :=
    compiledMemcpyInstanceContract_proved copyArgs (fromStep + 1) childEntry compiledEntry
  exact ⟨callRetired, childUsed, childEntry, childExit, rfl, by
    simp [childEntry, decodeInlineMemcpyCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, callLinkState, controlFlowJumpState,
      tryStepControlFlowAfterIncrement, coreControlFlowNextState, Std.ExtDHashMap.get?_insert],
    by simpa [childEntry] using callRun,
    compiledEntry, childBound, childTrace, childPost⟩

/-- Package the retry `memcpy` call, proved child execution, and real return as the checked call
boundary consumed by the enclosing Level 3 trace. -/
def memcpyRetryCallTransfer (fromStep used : Nat) (args : DecodeInlineArgs)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true)
    (contents : ByteArray) (beforeCall childEntry childExit resumed : State)
    (atCall : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103ec))
    (callRun : Runs (try_step fromStep false) beforeCall childEntry false)
    (childPre : (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.entry
      (decodeInlineRetryCopyArgs args contents) childEntry)
    (bound : used ≤ (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.stepBound
      (decodeInlineRetryCopyArgs args contents))
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_memcpy)
      (functionInstanceExitPred functionInstance_memcpy)
      (Contracts.functionInstanceEntryWord functionInstance_memcpy)
      (fromStep + 1) used childEntry childExit)
    (childPost : (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.exit
      (decodeInlineRetryCopyArgs args contents)
      ((compiledMemcpyContract Contracts.canonicalContractParams.env).spec.meaning
        (decodeInlineRetryCopyArgs args contents)) childEntry childExit)
    (returnRun : Runs (try_step (fromStep + 1 + used) false) childExit resumed false)
    (atResume : resumed.regs.get? PC = some (BitVec.ofNat 64 0x103f0)) :
    CallTransfer
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary memcpyRetryCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_memcpy fromStep used beforeCall resumed := by
  have atRet : childExit.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) := by
    obtain ⟨retPc, atRet, retIsExit⟩ := childTrace.trace.final_at_exit
    have retPcEq : retPc = BitVec.ofNat 64 0x13ec0 := by
      apply BitVec.eq_of_toNat_eq
      simpa [functionInstanceExitPred, FunctionInstance.isExit, functionInstance_memcpy] using retIsExit
    simpa [retPcEq] using atRet
  have callInRegion := decodeInline_owned_in_execution_region (0x103ec, 0xad0080e7)
    (by simp [decodeInlineOwnedInstructionWords])
  have resumeInRegion := decodeInline_owned_in_execution_region (0x103f0, 0x00001537)
    (by simp [decodeInlineOwnedInstructionWords])
  have retInRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x13ec0) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have callNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x103ec) := by
    simp [DecodeInlineExit, phase, exactPrefix]
  have retNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x13ec0) := by
    simp [DecodeInlineExit, phase, exactPrefix]
  have body : Level3ChildSummary functionInstance_memcpyId
      (fromStep + 1) used childEntry childExit :=
    Level3ChildSummary.memcpy
      ⟨rfl, decodeInlineRetryCopyArgs args contents, childPre, bound, childTrace, childPost⟩
  exact
    { valid := memcpyRetryCall_valid
      callPc := BitVec.ofNat 64 0x103ec
      atCall
      callSource := by decide
      callInRegion
      callNotExit
      sCall := childEntry
      doCall := callRun
      calleeEntryPc := BitVec.ofNat 64 0x13eb8
      atCalleeEntry := childPre.2.entry
      calleeEntryMatches := by decide
      sRet := childExit
      body
      retPc := BitVec.ofNat 64 0x13ec0
      atRet
      retInRegion
      retNotExit
      doReturn := returnRun
      returnPc := BitVec.ofNat 64 0x103f0
      atResume
      returnMatches := by decide
      resumeInRegion }

/-- Execute the decoder-owned `lui a0, 1` after the retry `memcpy` returns. -/
theorem decodeInline_retry_final_page_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103f0)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103f0) retired x10
          (BitVec.ofNat 64 0x1000)) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103f0, 0x00001537)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103f0) 0x37#8 0x15#8 0x00#8 0x00#8 :=
    fetchInstruction state 0x103f0 0x37 0x15 0x00 0x00 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103f0) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x37#8 0x15#8 0x00#8 0x00#8 =
      (0x00001537 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x37#8 0x15#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x00001#20, .Regidx 10#5, .LUI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103f0)
  have valueEq : sign_extend (m := 64) (0x00001#20 ++ 0x000#12) =
      (BitVec.ofNat 64 0x1000) := by decide
  have execute : Runs (execute (.UTYPE (0x00001#20, .Regidx 10#5, .LUI))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0x1000) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_lui_run executeState _ 0x00001#20 (.Regidx 10#5)
    simpa [valueEq] using wX_x10_run executeState (BitVec.ofNat 64 0x1000)
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x103f0) pcIn atPc 0x37#8 0x15#8 0x00#8 0x00#8
    (.UTYPE (0x00001#20, .Regidx 10#5, .LUI)) x10 (BitVec.ofNat 64 0x1000)
    fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute the decoder-owned `add a0, sp, a0`, reaching the outgoing result-tag load. -/
theorem decodeInline_retry_final_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103f4))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (pageRead : state.regs.get? x10 = some (BitVec.ofNat 64 0x1000)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103f4) retired x10
          (BitVec.ofNat 64 (args.stackBase + 0x1000))) false := by
  have pcIn := decoderFetchPc_of_member
    (decodeInline_owned_in_execution_region (0x103f4, 0x00a10533)
      (by simp [decodeInlineOwnedInstructionWords])) (by native_decide)
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103f4) 0x33#8 0x05#8 0xa1#8 0x00#8 :=
    fetchInstruction state 0x103f4 0x33 0x05 0xa1 0x00 image
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x103f4) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x33#8 0x05#8 0xa1#8 0x00#8 =
      (0x00a10533 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x05#8 0xa1#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 10#5, .Regidx 2#5, .Regidx 10#5, .ADD)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103f4)
  have stackAtExecute : executeState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  have pageAtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 0x1000) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pageRead]
  let finalValue : BitVec 64 := BitVec.ofNat 64 (args.stackBase + 0x1000)
  have resultEq : BitVec.ofNat 64 args.stackBase + BitVec.ofNat 64 0x1000 = finalValue := by
    dsimp [finalValue]
    rw [← BitVec.ofNat_add]
  have execute : Runs
      (execute (.RTYPE (.Regidx 10#5, .Regidx 2#5, .Regidx 10#5, .ADD))) executeState
      { executeState with
        regs := executeState.regs.insert x10 finalValue } (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 10#5) (.Regidx 2#5) (.Regidx 10#5) .ADD) _ _ _
    have hwrite : Runs (wX_bits (.Regidx 10#5)
        (BitVec.ofNat 64 args.stackBase + BitVec.ofNat 64 0x1000)) executeState
        { executeState with regs := executeState.regs.insert x10 finalValue } () := by
      rw [resultEq]
      exact wX_x10_run executeState finalValue
    exact execute_RTYPE_add_run executeState _ (.Regidx 10#5)
      (.Regidx 2#5) (.Regidx 10#5) (BitVec.ofNat 64 args.stackBase)
      (BitVec.ofNat 64 0x1000) (rX_bits_run_x2 executeState _ stackAtExecute)
      (rX_bits_run_x10 executeState _ pageAtExecute)
      hwrite
  exact decoderRegisterWriteStep machine (Agree.refl state) retiredPresent stepNo
    (BitVec.ofNat 64 0x103f4) pcIn atPc 0x33#8 0x05#8 0xa1#8 0x00#8
    (.RTYPE (.Regidx 10#5, .Regidx 2#5, .Regidx 10#5, .ADD)) x10
    finalValue fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Close the short-input retry arm at the selected `0x10394` exit. The outgoing branch belongs to
the Level 2 wrapper, so this Level 3 trace stops before executing it. -/
theorem decodeInline_retry_short_reaches_post (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (short : args.bytes.size < 4) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧
      DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after := by
  obtain ⟨childUsed, childAfter, childBound, parentPrefix, childPost, agree, counter, -, -, -,
    childGlobals, _childStatus, code, memory⟩ :=
    decodeInline_retry_uses_length_gate fromStep args state pre phase
  have prefixFalse : Contracts.meaningHasExactErePrefix args.bytes = false :=
    meaningHasExactErePrefix_false_of_size_lt_four args.bytes short
  have atExit : childAfter.regs.get? PC = some (BitVec.ofNat 64 0x10394) := by
    simpa [HasExactErePrefixInlinePost] using childPost.1
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x10394) := by
    simp [DecodeInlineExit, phase, prefixFalse, short]
  have tail : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (4 + childUsed)) 0
      childAfter childAfter :=
    ScopedTrace.exitAt _ childAfter (BitVec.ofNat 64 0x10394) atExit selectedExit
  have trace := parentPrefix 0 childAfter tail
  have rawInvalid : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz :=
    (pre.retryReason phase).1
  have resultInvalid : Contracts.meaningDecode args.bytes = .error .invalidSsz := by
    simp [Contracts.meaningDecode, rawInvalid, prefixFalse]
  refine ⟨4 + childUsed, childAfter, ?_, ?_, ?_,
    ⟨agree, counter, code, childGlobals.trans pre.globalsValue.symm⟩, ?_⟩
  · unfold decodeInlineStepBound
    have lengthBound : hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } = 12 := rfl
    rw [lengthBound] at childBound
    omega
  · simpa using trace
  · simp [DecodeInlinePost, phase, DecodeInlineRetryPost, prefixFalse, resultInvalid, atExit,
      short]
  · simp [DecodeInlineOutgoingFrame, phase, prefixFalse, short]
    exact ⟨childPost.2.1, childPost.2.2⟩

end BinaryFv.Zesu.MachineExecution
