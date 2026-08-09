import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryPrefix
import BinaryFv.Zesu.MachineExecution.GeneratedWordStep
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge
import BinaryFv.RiscV.Elfling.ProgramGeometry
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.Zesu.MachineExecution.OwnedPc

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

private theorem decodeInlineCallerSaveArea_of_mem_eq {args : DecodeInlineArgs} {before s t : State}
    (hmem : t.mem = s.mem) (h : DecodeInlineCallerSaveArea args before s) :
    DecodeInlineCallerSaveArea args before t := by
  intro index bound
  rw [hmem]
  exact h index bound

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The inlined `decode` instance's own execution scope, named once for the whole module.

Spelled out, this occupied a line to itself at 73 sites here, and it is the `own` half of the
`(own, exit, childSummary)` triple every `ConfinedPrefix`, `ScopedTrace` and `CallTransfer` in this
file carries; the other two halves are `DecodeInlineExit args` and `Level3ChildSummary`, which are
already short. As an `abbrev` it is reducible, so it *is* the spelled-out application: a proof or a
downstream module written against the long form elaborates unchanged, and `owned_pc` still sees the
`functionInstanceExecutionPcs` it decides. -/
abbrev decodeInlineOwnPcs : BitVec 64 → Prop :=
  functionInstanceExecutionPcs generatedProgram
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31

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
    ∀ entry ∈ decodeInlineOwnedInstructionWords, decodeInlineOwnPcs (BitVec.ofNat 64 entry.1) := by
  intro entry member
  simp only [decodeInlineOwnedInstructionWords, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals owned_pc

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
    unfold BinaryFv.Zesu.DecodedValue.observeWord64? at beforeCursor ⊢
    rw [beforeMemory]
    exact beforeCursor
  · unfold Contracts.DecoderEnvironment.cursor? at afterCursor ⊢
    unfold BinaryFv.Zesu.DecodedValue.observeWord64? at afterCursor ⊢
    rw [afterMemory]
    exact afterCursor
  · intro address outside
    rw [afterMemory, beforeMemory]
    exact frame address outside

/-- The complete `StatelessInput` representation survives a memory-preserving machine segment. -/
theorem statelessInputRep_of_mem_eq {before after : State} {inputBase rootBase : Nat}
    {input : ByteArray} {value : BinaryFv.Specs.SSZ.StatelessInput}
    (memory : after.mem = before.mem)
    (representation : BinaryFv.Zesu.DecodedValue.StatelessInputRep
      before inputBase input rootBase value) :
    BinaryFv.Zesu.DecodedValue.StatelessInputRep after inputBase input rootBase value := by
  obtain ⟨_, transport⟩ :=
    Contracts.Footprint.statelessInput_footprint_abi inputBase input rootBase value before
      Artifacts.raw_stateless_input_layout.1 representation
  exact transport _ (fun address _ => (congrArg (·.get? address) memory).symm)

/-- A fully allocated fixed-size heap record has a concrete byte snapshot. This supplies the exact
source bytes required by the selected `memcpy` boundary without assuming their contents. -/
theorem memoryBytes_exists_of_heapArrayRep (state : State) (base size : Nat)
    (allocated : BinaryFv.Zesu.DecodedValue.HeapArrayRep state base 1 size) :
    ∃ bytes : ByteArray,
      bytes.size = size ∧ BinaryFv.Zesu.DecodedValue.MemoryBytes state base bytes := by
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

/-- `postEntry` is memory-only at the canonical `StatelessInput` representation. This rebases its relative
write frame and transports its result representation when surrounding instructions change only
registers. -/
theorem canonicalPostEntry_of_mem_eq (args : Contracts.EntryArgs)
    (result : Except Contracts.DecodeError BinaryFv.Specs.SSZ.StatelessInput)
    {before after before' after' : State}
    (beforeMemory : before'.mem = before.mem) (afterMemory : after'.mem = after.mem)
    (post : Contracts.postEntry Contracts.canonicalContractParams.env args
      Contracts.canonicalContractParams.repStatelessInput result before after) :
    Contracts.postEntry Contracts.canonicalContractParams.env args
      Contracts.canonicalContractParams.repStatelessInput result before' after' := by
  rcases post with ⟨input, code, writes, status, outcome⟩
  refine ⟨?_, ?_, writesOnlyWithinOwnAllocation_of_mem_eq _ _ _ beforeMemory afterMemory writes,
    ?_, ?_⟩
  · intro index bound
    rw [afterMemory]
    exact input index bound
  · change Contracts.canonicalContractParams.env.image.fileBytesLoadedFaithfully after'.mem
    rw [afterMemory]
    exact code
  · rcases status with ⟨tagBound, low, high⟩
    exact ⟨tagBound, by simpa [afterMemory] using low, by simpa [afterMemory] using high⟩
  · cases result with
    | ok value =>
        exact statelessInputRep_of_mem_eq afterMemory outcome
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
  exact GeneratedWordStep.generatedRegisterWriteStep pre.machine (Agree.refl state)
    pre.machine.retiredCounter (hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10308 0x36010513 atPc
    (decoded := .ITYPE (0x360#12, .Regidx 2#5, .Regidx 10#5, .ADDI))
    (decoderDecode pre.machine (Agree.refl state) (by decoder_decode))
    (execute_ITYPE_run _ _ 0x360#12 (.Regidx 2#5) (.Regidx 10#5) .ADDI _
      (rX_bits_run_x2 _ _ (decoderExecuteState_get? pre.stackValue)) (wX_x10_run _ _))

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
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderITypeStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x1030c 0x93 0x05 0x01 0x01 0x010#12 2#5 11#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x11_run _ _)

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
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderITypeStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10310 0x13 0x06 0x04 0x00 0x000#12 8#5 12#5 .ADDI atPc
    (rX_x8_run _ _ (decoderExecuteState_get? inputRead)) (wX_x12_run _ _)

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
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderITypeStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10314 0x93 0x86 0x04 0x00 0x000#12 9#5 13#5 .ADDI atPc
    (rX_x9_run _ _ (decoderExecuteState_get? lengthRead)) (wX_x13_run _ _)

theorem decodeInline_first_argument_setup (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ after, Trace fromStep 4 state after ∧
      ConfinedPrefix decodeInlineOwnPcs
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
      Agree platformPreserved state after ∧ Agree decodeRawCalleeSaved state after ∧
      after.mem = state.mem ∧
      RetiredCounterPresent after := by
  let firstResult := iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired1, run1⟩ := decodeInline_first_result_pointer_step fromStep args state pre phase
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x10308) retired1 x10 firstResult
  have w1 : WritesOnlyRegs _ state s1 := afterRegisterWrite_writes _ _ _ _ _
  have preStack := pre.stackValue
  have preInput := pre.inputValue
  have preLength := pre.lengthValue
  have preGlobals := pre.globalsValue
  have agree1 : Agree platformPreserved state s1 :=
    afterRegisterWrite_agree (by simp [platformPreserved])
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x1030c) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10308) retired1 x10
      firstResult
  have stack1 : s1.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  let allocator := iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired2, run2⟩ := decodeInline_first_allocator_pointer_step (fromStep + 1) args
    state s1 pre agree1 rfl
    (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10308) retired1 x10 firstResult)
    pc1 stack1
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x1030c) retired2 x11 allocator
  have w2 : WritesOnlyRegs _ s1 s2 := afterRegisterWrite_writes _ _ _ _ _
  have agree2 : Agree platformPreserved state s2 :=
    Agree.trans agree1 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10310) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x1030c) retired2 x11 allocator
  have input2 : s2.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  let input := iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.inputBase)
  obtain ⟨retired3, run3⟩ := decodeInline_first_input_pointer_step (fromStep + 2) args
    state s2 pre agree2 rfl
    (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x1030c) retired2 x11 allocator)
    pc2 input2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10310) retired3 x12 input
  have w3 : WritesOnlyRegs _ s2 s3 := afterRegisterWrite_writes _ _ _ _ _
  have agree3 : Agree platformPreserved state s3 :=
    Agree.trans agree2 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10314) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10310) retired3 x12 input
  have length3 : s3.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  let length := iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.bytes.size)
  obtain ⟨retired4, run4⟩ := decodeInline_first_input_length_step (fromStep + 3) args
    state s3 pre agree3 rfl
    (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10310) retired3 x12 input)
    pc3 length3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x10314) retired4 x13 length
  have w4 : WritesOnlyRegs _ s3 s4 := afterRegisterWrite_writes _ _ _ _ _
  have agree4 : Agree platformPreserved state s4 :=
    Agree.trans agree3 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have calleeSaved1 : Agree decodeRawCalleeSaved state s1 :=
    afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved])
  have calleeSaved2 : Agree decodeRawCalleeSaved state s2 :=
    calleeSaved1.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have calleeSaved3 : Agree decodeRawCalleeSaved state s3 :=
    calleeSaved2.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have calleeSaved4 : Agree decodeRawCalleeSaved state s4 :=
    calleeSaved3.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
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
  have stack4 : s4.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have globals4 : s4.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
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
  have prefix1 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep 1 state s1 :=
    ConfinedPrefix.ownStep' atFirstEntry (by simpa [s1, firstResult] using run1)
      (notExit := notExit1)
  have prefix2 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep' pc1 (by simpa [s2, allocator] using run2) (notExit := notExit2)
  have prefix3 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep' pc2 (by simpa [s3, input] using run3) (notExit := notExit3)
  have prefix4 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep' pc3 (by simpa [s4, length] using run4) (notExit := notExit4)
  have combinedPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep 4 state s4 := by
    confined_steps [prefix1, prefix2, prefix3, prefix4]
  refine ⟨s4, ?_, combinedPrefix, pc4, result4, allocator4, input4, length4, stack4, ?_, ?_, ?_,
    agree4, calleeSaved4, rfl,
    afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x10314) retired4 x13 length⟩
  · refine Trace.step fromStep 3 state s1 s4 (by simpa [s1, firstResult] using run1) ?_
    refine Trace.step (fromStep + 1) 2 s1 s2 s4 (by simpa [s2, allocator] using run2) ?_
    refine Trace.step (fromStep + 2) 1 s2 s3 s4 (by simpa [s3, input] using run3) ?_
    exact Trace.one (fromStep + 3) s3 s4 (by simpa [s4, length] using run4)
  · grind
  · grind
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
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext pre.machine agree
  exact decoderAuipcStep pre.machine agree retiredPresent
    (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10318 0x97 0x00 0x00 0x00 0x00000#20 1#5 atPc
    (by simpa using wX_bits_run_x1 _ (BitVec.ofNat 64 0x10318))

theorem decodeInline_first_before_decodeRaw_call (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ beforeCall, Trace fromStep 5 state beforeCall ∧
      ConfinedPrefix decodeInlineOwnPcs
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
      Agree decoderPreserved state beforeCall ∧ Agree decodeRawCalleeSaved state beforeCall ∧
      beforeCall.mem = state.mem ∧
      RetiredCounterPresent beforeCall := by
  obtain ⟨afterArgs, argsTrace, argsPrefix, argsPc, resultArgs, allocatorArgs, inputArgs,
    lengthArgs, stackArgs, inputBaseArgs, inputLengthArgs, globalsArgs, argsAgree, argsCalleeSaved,
    argsMemory, argsRetired⟩ :=
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
  have callPageWrites : WritesOnlyRegs _ afterArgs beforeCall := afterRegisterWrite_writes _ _ _ _ _
  have callPageAgree : Agree decoderPreserved afterArgs beforeCall := by
    apply afterRegisterWrite_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  have memoryUnchanged : beforeCall.mem = state.mem := by
    change (afterRegisterWrite afterArgs (BitVec.ofNat 64 0x10318) retired x1
      (BitVec.ofNat 64 0x10318)).mem = state.mem
    exact (afterRegisterWrite_mem afterArgs (BitVec.ofNat 64 0x10318) retired x1
      (BitVec.ofNat 64 0x10318)).trans argsMemory
  have callPageNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10318) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have callPagePrefix : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args)
      Level3ChildSummary (fromStep + 4) 1 afterArgs beforeCall :=
    ConfinedPrefix.ownStep' argsPc (by simpa [beforeCall] using callPageStep)
      (notExit := callPageNotExit)
  have combinedPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall := by
    confined_steps [argsPrefix, callPagePrefix]
  refine ⟨beforeCall, ?_, combinedPrefix, callPc, returnBase, by grind, by grind, by grind,
    by grind, by grind, by grind, by grind, by grind,
    Agree.trans (Agree.weaken (fun _ preserved => preserved.2) argsAgree) callPageAgree,
    argsCalleeSaved.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved])), memoryUnchanged,
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
      Agree decodeRawCalleeSaved state (decodeInlineFirstCallAfter state retired) ∧
      (decodeInlineFirstCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (decodeInlineFirstCallAfter state retired) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContextOfDecoderAgree pre.machine agree
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) state
      (decodeInlineFirstCallAfter state retired) false :=
    decoderJalrCallStep pre.machine agree retiredPresent
      (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
      stepNo 0x1031c 0xe7 0x80 0xc0 0x12 0x12c#12 1#5 1#5 (BitVec.ofNat 64 0x10318)
      (BitVec.ofNat 64 0x10320) (BitVec.ofNat 64 0x10444) atPc
      (rX_bits_run_x1 _ _ (decoderExecuteState_get? callBase)) (wX_bits_run_x1 _ _)
  have callWrites : WritesOnlyRegs _ state (decodeInlineFirstCallAfter state retired) :=
    callRetirement_writes _ _ _ _ _ _
  -- Regression for the seven carries below: `grind` must refuse what the call writes.
  fail_if_success (have : (decodeInlineFirstCallAfter state retired).regs.get? x1 =
    state.regs.get? x1 := by grind)
  fail_if_success (have : (decodeInlineFirstCallAfter state retired).regs.get? PC =
    state.regs.get? PC := by grind)
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
  have callCalleeSavedAgree : Agree decodeRawCalleeSaved state
      (decodeInlineFirstCallAfter state retired) := by
    apply jalrCallAfterRetired_agree_of
    all_goals simp [decodeRawCalleeSaved]
  have callMemory : (decodeInlineFirstCallAfter state retired).mem = state.mem :=
    jalrCallAfterRetired_mem _ _ _ _ _ _
  refine ⟨retired, run, pcAfter, linkAfter, by grind, by grind, by grind, by grind, by grind,
    by grind, by grind, callAgree, callCalleeSavedAgree, callMemory, ?_⟩
  exact ⟨Sail.BitVec.addInt retired 1, by
    simp [decodeInlineFirstCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]⟩

/-- The selected emitted `decodeRaw` region is contained in its enclosing inlined `decode` region.
This is checked from the generated call relation, not handwritten address bounds. -/
private theorem decodeRaw_executionPcs_subset_decodeInline (pc : BitVec 64)
    (pcIn : functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw pc) :
    decodeInlineOwnPcs pc := by
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
  exact (programGeometry_of_check (program := generatedProgram) (by native_decide)).calleeWithinExecution
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
    parentMember functionInstance_ssz_raw_decodeRaw childIsCallee pc pcIn

/-- Read off the generated exit address of the selected emitted `decodeRaw` from its own trace. -/
private theorem decodeRaw_trace_exit_pc {childFrom childUsed : Nat} {childEntry childExit : State}
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
      (Contracts.functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
      childFrom childUsed childEntry childExit) :
    childExit.regs.get? PC = some (BitVec.ofNat 64 0x10530) := by
  obtain ⟨retPc, atRet, retIsExit⟩ := childTrace.trace.final_at_exit
  have retPcEq : retPc = BitVec.ofNat 64 0x10530 := by
    apply BitVec.eq_of_toNat_eq
    simpa [functionInstanceExitPred, FunctionInstance.isExit,
      functionInstance_ssz_raw_decodeRaw] using retIsExit
  simpa [retPcEq] using atRet

/-- The declared `decode` budget leaves room for the selected `decodeRaw` budget plus the thirteen
parent-owned instructions of the first phase. -/
private theorem decodeInline_first_stepBound_le {args : DecodeInlineArgs} {childUsed own : Nat}
    (childBound : childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs)
    (ownBound : own ≤ 13) : childUsed + own ≤ decodeInlineStepBound args := by
  unfold decodeInlineStepBound
  have stepBoundEq : compiledDecodeRawContract.binding.stepBound args.firstRawArgs =
      16384 + 512 * args.bytes.size := rfl
  rw [stepBoundEq] at childBound
  omega

/-- The first six decoder-owned instructions execute through Sail and establish the exact entry
predicate consumed by the selected `decodeRaw` child contract. -/
theorem decodeInline_first_enters_decodeRaw (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ childEntry, Trace fromStep 6 state childEntry ∧
      compiledDecodeRawContract.binding.entry args.firstRawArgs childEntry ∧
      childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x10320) := by
  obtain ⟨beforeCall, beforeTrace, -, callPc, callBase, resultPointer, allocatorPointer,
    inputPointer, inputLength, beforeStack, beforeInputBase, beforeInputLength, beforeGlobals, beforeAgree,
    beforeCalleeSaved, beforeMemory, beforeRetired⟩ :=
    decodeInline_first_before_decodeRaw_call fromStep args state pre phase
  obtain ⟨retired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, childInputBase, childInputLength, childGlobals, callAgree, callCalleeSaved, callMemory,
    childRetired⟩ :=
    decodeInline_first_decodeRaw_call_step (fromStep + 5) args state beforeCall pre
      beforeAgree beforeMemory beforeRetired callPc callBase resultPointer allocatorPointer
      inputPointer inputLength beforeInputBase beforeInputLength beforeGlobals
  let childEntry := decodeInlineFirstCallAfter beforeCall retired
  have childTrace : Trace fromStep 6 state childEntry :=
    Trace.snoc beforeTrace (by simpa [childEntry] using callRun)
  have childAgree : Agree decoderPreserved state childEntry :=
    Agree.trans beforeAgree callAgree
  have childCalleeSaved : Agree decodeRawCalleeSaved state childEntry :=
    beforeCalleeSaved.trans callCalleeSaved
  have entryFrame : DecodeRawEntryFrame state := by
    simpa [DecodeInlineRawCallFrame, phase] using pre.rawCallFrame
  have childStack : childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    ((callRetirement_writes _ _ _ _ _ _).get x2 (by decide)).trans beforeStack
  have childMemory : childEntry.mem = state.mem := callMemory.trans beforeMemory
  have childMachineAtParentExtent : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono childAgree childRetired
  have childMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs args.firstRawArgs) childEntry := by
    simpa [DecodeInlineArgs.machineArgs, entryMachineArgs, DecodeInlineArgs.firstRawArgs] using
      childMachineAtParentExtent.restrict decodeRaw_executionPcs_subset_decodeInline
  have sourceEntry :
      (Contracts.contractDecodeRaw Contracts.canonicalContractParams.env
        Contracts.canonicalContractParams.repStatelessInput).toFunctionInstance.binding.entry
        args.firstRawArgs childEntry := by
    change Contracts.preEntry Contracts.canonicalContractParams.env args.firstRawArgs childEntry
    refine ⟨?_, ?_, childResult, childAllocator, childInput, childLength⟩
    · intro index bound
      rw [childMemory]
      exact pre.inputMemory index bound
    · change Contracts.canonicalContractParams.env.image.fileBytesLoadedFaithfully childEntry.mem
      rw [childMemory]
      exact pre.code
  have childFrame : DecodeRawEntryFrame childEntry :=
    DecodeRawEntryFrame.of_calleeSaved_agree entryFrame childCalleeSaved
      (by simpa [childEntry] using childStack)
      (by simpa [childEntry] using childInputBase) (by simpa [childEntry] using childInputLength)
      (by simpa [childEntry] using childGlobals)
  exact ⟨childEntry, childTrace, ⟨sourceEntry, childPc, childFrame, childMachine⟩, childLink⟩

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
    Agree decoderPreserved state (decodeRawReturnAfter returnPc state retired) :=
  Agree.weaken (fun _ preserved => preserved.2)
    ((jumpRetirement_writes _ _ _ _).agree platformPreserved_disjoint)

theorem decodeRawReturnAfter_calleeSaved (returnPc : BitVec 64) (state : State)
    (retired : BitVec 64) :
    Agree decodeRawCalleeSaved state (decodeRawReturnAfter returnPc state retired) :=
  (jumpRetirement_writes _ _ _ _).agree decodeRawCalleeSaved_disjoint

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
  rcases childPost with ⟨sourcePost, childFrame, childRetired, childPayload, _childSaveArea,
    _childProvenance, _childAllocation⟩
  rcases sourcePost with ⟨-, code, -, -⟩
  have machineAtExit : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs rawArgs) childExit :=
    childPre.2.2.2.mono
      (Agree.weaken (fun _ preserved => Or.inl preserved.2) childFrame) childRetired
  have atExit := decodeRaw_trace_exit_pc childTrace
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContextOfDecoderAgree machineAtExit (Agree.refl childExit)
  have exitLink : childExit.regs.get? x1 = some returnPc :=
    (childFrame x1 (by simp [decodeRawCallerPreserved, platformPreserved])).trans entryLink
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) childExit
      (decodeRawReturnAfter returnPc childExit retired) false :=
    decoderRetStep machineAtExit (Agree.refl childExit) childRetired code
      stepNo 0x10530 0x67 0x80 0x00 0x00 1#5 returnPc returnPc atExit
      (rX_bits_run_x1 _ _ (decoderExecuteState_get? exitLink))
  refine ⟨retired, run, ?_⟩
  simp [decodeRawReturnAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
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
    CallTransfer decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw fromStep used beforeCall resumed := by
  have atRet := decodeRaw_trace_exit_pc childTrace
  have callInRegion : decodeInlineOwnPcs (BitVec.ofNat 64 0x1031c) :=
    decodeInline_owned_in_execution_region (0x1031c, 0x12c080e7)
      (by simp [decodeInlineOwnedInstructionWords])
  have returnInRegion : decodeInlineOwnPcs (BitVec.ofNat 64 0x10320) :=
    decodeInline_owned_in_execution_region (0x10320, 0x6a015503)
      (by simp [decodeInlineOwnedInstructionWords])
  have retInRegion : decodeInlineOwnPcs (BitVec.ofNat 64 0x10530) := by owned_pc
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
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      childUsed ≤ 16384 + 512 * args.bytes.size ∧
      Nonempty (CallTransfer decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed) ∧
      BinaryFv.Zesu.DecodedValue.ResultStatusLERep resumed
        (args.firstTemporaryResultBase +
          Contracts.canonicalContractParams.env.record.entryResultTagOffset)
        (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)) ∧
      Contracts.canonicalContractParams.env.CodeIntact resumed ∧
      Agree decoderPreserved state resumed ∧
      Agree decodeRawCalleeSaved state resumed ∧
      RetiredCounterPresent resumed ∧
      resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      resumed.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      resumed.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repStatelessInput (Contracts.meaningDecodeRaw args.bytes)
      state resumed ∧
      DecodeRawSuccessAllocationProvenance args.firstRawArgs
        (Contracts.meaningDecodeRaw args.bytes) state resumed ∧
      DecodeInlineCallerSaveArea args state resumed ∧
      DecodeRawAllocationWithinCanonicalArena state resumed := by
  obtain ⟨beforeCall, parentTrace, parentPrefix, callPc, callBase, resultPointer, allocatorPointer,
    inputPointer, inputLength, beforeStack, beforeInputBase, beforeInputLength, beforeGlobals, beforeAgree,
    beforeCalleeSaved, beforeMemory, beforeRetired⟩ :=
    decodeInline_first_before_decodeRaw_call fromStep args state pre phase
  obtain ⟨callRetired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, childInputBase, childInputLength, childGlobals, callAgree, callCalleeSaved, callMemory,
    childRetired⟩ :=
    decodeInline_first_decodeRaw_call_step (fromStep + 5) args state beforeCall pre
      beforeAgree beforeMemory beforeRetired callPc callBase resultPointer allocatorPointer
      inputPointer inputLength beforeInputBase beforeInputLength beforeGlobals
  let childEntry := decodeInlineFirstCallAfter beforeCall callRetired
  have childStack : childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    ((callRetirement_writes _ _ _ _ _ _).get x2 (by decide)).trans beforeStack
  have childAgree : Agree decoderPreserved state childEntry :=
    Agree.trans beforeAgree callAgree
  have childCalleeSaved : Agree decodeRawCalleeSaved state childEntry :=
    beforeCalleeSaved.trans callCalleeSaved
  have entryFrame : DecodeRawEntryFrame state := by
    simpa [DecodeInlineRawCallFrame, phase] using pre.rawCallFrame
  have childMachineAtParentExtent : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono childAgree childRetired
  have childMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs args.firstRawArgs) childEntry := by
    simpa [DecodeInlineArgs.machineArgs, entryMachineArgs, DecodeInlineArgs.firstRawArgs] using
      childMachineAtParentExtent.restrict decodeRaw_executionPcs_subset_decodeInline
  have childMemory : childEntry.mem = state.mem := callMemory.trans beforeMemory
  have childSourceEntry : Contracts.preEntry Contracts.canonicalContractParams.env
      args.firstRawArgs childEntry := by
    refine ⟨?_, ?_, childResult, childAllocator, childInput, childLength⟩
    · intro index bound
      rw [childMemory]
      exact pre.inputMemory index bound
    · change Contracts.canonicalContractParams.env.image.fileBytesLoadedFaithfully childEntry.mem
      rw [childMemory]
      exact pre.code
  have childFrame : DecodeRawEntryFrame childEntry :=
    DecodeRawEntryFrame.of_calleeSaved_agree entryFrame childCalleeSaved childStack
      childInputBase childInputLength childGlobals
  have childPre : compiledDecodeRawContract.binding.entry args.firstRawArgs childEntry :=
    ⟨childSourceEntry, childPc, childFrame, childMachine⟩
  obtain ⟨childUsed, childExit, bound, childTrace, childPost⟩ :=
    contract args.firstRawArgs (fromStep + 6) childEntry childPre
  have firstInvalidBound : childUsed ≤ 16384 + 512 * args.bytes.size := by
    simpa [compiledDecodeRawContract, Contracts.contractDecodeRaw,
      DecodeInlineArgs.firstRawArgs] using bound
  obtain ⟨returnRetired, returnRun, atResume⟩ :=
    decodeRaw_return_step (fromStep + 6 + childUsed) args.firstRawArgs
      (BitVec.ofNat 64 0x10320) childEntry childExit (by decide) (by decide)
      childPre childTrace childLink childPost
  let resumed := decodeRawReturnAfter (BitVec.ofNat 64 0x10320) childExit returnRetired
  rcases childPost with ⟨sourcePost, childFrame, childCounter, childPayload, childSaveArea,
    childProvenance, childAllocation⟩
  rcases sourcePost with ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have resumedStatus : BinaryFv.Zesu.DecodedValue.ResultStatusLERep resumed
      (args.firstTemporaryResultBase +
        Contracts.canonicalContractParams.env.record.entryResultTagOffset)
      (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)) := by
    simpa [resumed, DecodeInlineArgs.firstRawArgs] using childStatus
  have resumedCode : Contracts.canonicalContractParams.env.CodeIntact resumed := by
    exact Contracts.codeIntact_of_mem_eq
      (decodeRawReturnAfter_mem (BitVec.ofNat 64 0x10320) childExit returnRetired) childCode
  have childFrameDecoder : Agree decoderPreserved childEntry childExit :=
    Agree.weaken (fun _ preserved => Or.inl preserved.2) childFrame
  have childFrameCalleeSaved : Agree decodeRawCalleeSaved childEntry childExit :=
    Agree.weaken (fun _ preserved => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr preserved))))) childFrame
  have resumedAgree : Agree decoderPreserved state resumed :=
    Agree.trans childAgree
      (Agree.trans childFrameDecoder (by
        simpa [resumed] using
          (decodeRawReturnAfter_agree (BitVec.ofNat 64 0x10320) childExit returnRetired)))
  have resumedCalleeSaved : Agree decodeRawCalleeSaved state resumed :=
    childCalleeSaved.trans (childFrameCalleeSaved.trans
      (decodeRawReturnAfter_calleeSaved (BitVec.ofNat 64 0x10320) childExit returnRetired))
  have wReturn : WritesOnlyRegs _ childExit resumed := jumpRetirement_writes _ _ _ _
  have exitStack : childExit.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (childFrame x2 (by simp [decodeRawCallerPreserved])).trans childStack
  have exitInputBase : childExit.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    (childFrame x8 (by simp [decodeRawCallerPreserved])).trans childInputBase
  have exitInputLength : childExit.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    (childFrame x9 (by simp [decodeRawCallerPreserved])).trans childInputLength
  have exitGlobals : childExit.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (childFrame x18 (by simp [decodeRawCallerPreserved])).trans childGlobals
  have resumedStack : resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have resumedInputBase : resumed.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  have resumedInputLength : resumed.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  have resumedGlobals : resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have resumedPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repStatelessInput (Contracts.meaningDecodeRaw args.bytes)
      state resumed := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (Contracts.meaningDecodeRaw args.bytes)
      childMemory.symm
        (decodeRawReturnAfter_mem (BitVec.ofNat 64 0x10320) childExit returnRetired)
    exact ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have resumedProvenance : DecodeRawSuccessAllocationProvenance args.firstRawArgs
      (Contracts.meaningDecodeRaw args.bytes) state resumed := by
    apply decodeRawSuccessAllocationProvenance_of_mem_eq childMemory.symm
      (decodeRawReturnAfter_mem (BitVec.ofNat 64 0x10320) childExit returnRetired)
    exact childProvenance
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
  have resumedAllocation : DecodeRawAllocationWithinCanonicalArena state resumed := by
    rcases childAllocation with ⟨cursorBefore, cursorAfter, beforeCursor, afterCursor,
      arenaBase, cursorOrder, cursorBound⟩
    refine ⟨cursorBefore, cursorAfter, ?_, ?_, arenaBase, cursorOrder, cursorBound⟩
    · unfold Contracts.DecoderEnvironment.cursor? at beforeCursor ⊢
      unfold BinaryFv.Zesu.DecodedValue.observeWord64? at beforeCursor ⊢
      rw [← childMemory]
      exact beforeCursor
    · unfold Contracts.DecoderEnvironment.cursor? at afterCursor ⊢
      unfold BinaryFv.Zesu.DecodedValue.observeWord64? at afterCursor ⊢
      rw [decodeRawReturnAfter_mem]
      exact afterCursor
  have transfer : CallTransfer decodeInlineOwnPcs
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
        childFrame, childCounter, childPayload, childSaveArea, childProvenance, childAllocation⟩
    · simpa [resumed, Nat.add_assoc] using returnRun
    · simpa [resumed] using atResume
  exact ⟨beforeCall, childUsed, resumed, parentTrace, parentPrefix, bound, firstInvalidBound,
    ⟨transfer⟩, resumedStatus,
    resumedCode, resumedAgree, resumedCalleeSaved,
    (by simpa [resumed] using
      (decodeRawReturnAfter_retired (BitVec.ofNat 64 0x10320) childExit returnRetired)),
      resumedStack, resumedInputBase, resumedInputLength, resumedGlobals, resumedPost,
      resumedProvenance, resumedSaveArea, resumedAllocation⟩

/-! ## First result dispatch -/

/-- Execute the actual `lhu a0, 0x6a0(sp)` that reads the first `decodeRaw` result tag. The bytes
come from the strengthened child postcondition; no result value is assumed by the machine step. -/
theorem decodeInline_first_result_tag_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (status : BinaryFv.Zesu.DecodedValue.ResultStatusLERep state
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
  have machine := pre.machine.mono agree retiredPresent
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10320)
  have executeAgree : Agree decoderPreserved baseState executeState :=
    Agree.trans agree
      (Agree.weaken (fun _ preserved => preserved.2)
        (agree_stepPremiseState state (BitVec.ofNat 64 0x10320)))
  have stackAtExecute : executeState.regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) := decoderExecuteState_get? stackRead
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
  have statusAtAddress : BinaryFv.Zesu.DecodedValue.ResultStatusLERep state
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
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderLhuStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10320 0x03 0x55 0x01 0x6a 0x6a0#12 2#5 10#5 atPc hread
    (by simpa [extended] using wX_x10_run executeState (BitVec.ofNat 64 tag))

/-- Consume the first Level 3 `decodeRaw` condition, return from the emitted function, and then
execute the parent-owned result-tag load. This is the first composed path where a child contract
directly enables a following instruction of the inlined parent. -/
theorem decodeInline_first_through_result_tag
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ beforeCall childUsed resumed retired,
      Trace fromStep 5 state beforeCall ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      childUsed ≤ 16384 + 512 * args.bytes.size ∧
      Nonempty (CallTransfer decodeInlineOwnPcs
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
      Agree decodeRawCalleeSaved state
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
      Contracts.canonicalContractParams.repStatelessInput (Contracts.meaningDecodeRaw args.bytes) state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      DecodeRawSuccessAllocationProvenance args.firstRawArgs
        (Contracts.meaningDecodeRaw args.bytes) state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      DecodeInlineCallerSaveArea args state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      DecodeRawAllocationWithinCanonicalArena state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) := by
  obtain ⟨beforeCall, childUsed, resumed, parentTrace, parentPrefix, bound, firstInvalidBound,
    transfer, status, code,
    resumedAgree, resumedCalleeSaved, resumedRetired, resumedStack, resumedInputBase,
    resumedInputLength, resumedGlobals, resumedPost, resumedProvenance, resumedSaveArea,
    resumedAllocation⟩ :=
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
  have tagCalleeSaved : Agree decodeRawCalleeSaved resumed afterTag := by
    apply afterRegisterWrite_agree_of
    all_goals simp [decodeRawCalleeSaved]
  have afterCode : Contracts.canonicalContractParams.env.CodeIntact afterTag := by
    exact Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem _ _ _ _ _) code
  have afterX10 : afterTag.regs.get? x10 = some tagValue := by
    simp [afterTag, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have wTag : WritesOnlyRegs _ resumed afterTag := afterRegisterWrite_writes _ _ _ _ _
  have afterStack : afterTag.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have afterInputBase : afterTag.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  have afterInputLength : afterTag.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  have afterGlobals : afterTag.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have afterPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repStatelessInput (Contracts.meaningDecodeRaw args.bytes)
      state afterTag := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (Contracts.meaningDecodeRaw args.bytes)
      rfl (afterRegisterWrite_mem resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue)
    exact resumedPost
  have afterProvenance : DecodeRawSuccessAllocationProvenance args.firstRawArgs
      (Contracts.meaningDecodeRaw args.bytes) state afterTag := by
    apply decodeRawSuccessAllocationProvenance_of_mem_eq rfl
      (afterRegisterWrite_mem resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue)
    exact resumedProvenance
  have afterSaveArea : DecodeInlineCallerSaveArea args state afterTag := by
    exact decodeInlineCallerSaveArea_of_mem_eq (afterRegisterWrite_mem _ _ _ _ _) resumedSaveArea
  have afterAllocation : DecodeRawAllocationWithinCanonicalArena state afterTag := by
    rcases resumedAllocation with ⟨cursorBefore, cursorAfter, beforeCursor, afterCursor,
      arenaBase, cursorOrder, cursorBound⟩
    refine ⟨cursorBefore, cursorAfter, beforeCursor, ?_, arenaBase, cursorOrder, cursorBound⟩
    unfold Contracts.DecoderEnvironment.cursor? at afterCursor ⊢
    unfold BinaryFv.Zesu.DecodedValue.observeWord64? at afterCursor ⊢
    rw [afterRegisterWrite_mem]
    exact afterCursor
  refine ⟨beforeCall, childUsed, resumed, retired, parentTrace, parentPrefix, bound,
    firstInvalidBound, ⟨callTransfer⟩,
    by simpa [afterTag, tagValue] using tagRun, ?_, afterCode,
    Agree.trans resumedAgree tagAgree, resumedCalleeSaved.trans tagCalleeSaved, ?_, afterStack,
    afterInputBase, afterInputLength, afterX10,
    afterGlobals,
    afterPost, afterProvenance, afterSaveArea, afterAllocation⟩
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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  obtain ⟨retired, run⟩ := decoderBranchNotTakenStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10324 0x63 0x1c 0x05 0x04 0x58#13 0#5 10#5 .BNE atPc
    (by unfold bTypeTaken
        refine Runs.bind (rX_bits_run_x10 _ (0#64) (decoderExecuteState_get? successTag)) ?_
        refine Runs.bind (rX_x0_run _) ?_
        rfl)
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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10328 0x13 0x05 0x01 0x02 0x020#12 2#5 10#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x10_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x1032c 0x93 0x05 0x01 0x36 0x360#12 2#5 11#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x11_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10330 0x13 0x06 0x00 0x34 0x340#12 0#5 12#5 .ADDI atPc
    (rX_x0_run _) (wX_x12_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderAuipcStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10334 0x97 0x40 0x00 0x00 0x00004#20 1#5 atPc
    (by simpa using wX_bits_run_x1 _ (BitVec.ofNat 64 0x14334))

/-- The four successful-result copy arguments are not an assumed ABI boundary. They are the exact
Sail execution of the parent-owned words at `0x10328..0x10334`, stopping on the selected emitted
`memcpy` call instruction at `0x10338`. -/
theorem decodeInline_first_success_copy_setup (fromStep : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (phase : args.phase = .first) (value : BinaryFv.Specs.SSZ.RawV4)
    (success : Contracts.meaningDecodeRaw args.bytes = .ok value)
    (agree : Agree decoderPreserved baseState state)
    (calleeSaved : Agree decodeRawCalleeSaved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10328))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (globals : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (post : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repStatelessInput (Contracts.meaningDecodeRaw args.bytes)
      baseState state) :
    ∃ after,
      Trace fromStep 4 state after ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10338) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      after.regs.get? x12 = some (BitVec.ofNat 64 832) ∧
      after.regs.get? x1 = some (BitVec.ofNat 64 0x14334) ∧
      after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      Agree decoderPreserved baseState after ∧
      Agree decodeRawCalleeSaved baseState after ∧
      RetiredCounterPresent after ∧
      Contracts.canonicalContractParams.env.CodeIntact after ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
        Contracts.canonicalContractParams.repStatelessInput (Contracts.meaningDecodeRaw args.bytes)
        baseState after ∧
      after.mem = state.mem := by
  let destination := iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired1, run1⟩ := decodeInline_first_success_copy_destination_step fromStep args
    baseState state pre agree retiredPresent code atPc stackRead
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x10328) retired1 x10 destination
  have w1 : WritesOnlyRegs _ state s1 := afterRegisterWrite_writes _ _ _ _ _
  have agree1 : Agree decoderPreserved baseState s1 :=
    Agree.trans agree (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have calleeSaved1 : Agree decodeRawCalleeSaved baseState s1 :=
    calleeSaved.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x1032c) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10328) retired1 x10 destination
  have stack1 : s1.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have code1 : Contracts.canonicalContractParams.env.CodeIntact s1 := by
    exact Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem _ _ _ _ _) code
  let source := iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired2, run2⟩ := decodeInline_first_success_copy_source_step (fromStep + 1) args
    baseState s1 pre agree1
    (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10328) retired1 x10 destination)
    code1 pc1 stack1
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x1032c) retired2 x11 source
  have w2 : WritesOnlyRegs _ s1 s2 := afterRegisterWrite_writes _ _ _ _ _
  have agree2 : Agree decoderPreserved baseState s2 :=
    Agree.trans agree1 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have calleeSaved2 : Agree decodeRawCalleeSaved baseState s2 :=
    calleeSaved1.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10330) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x1032c) retired2 x11 source
  have code2 : Contracts.canonicalContractParams.env.CodeIntact s2 := by
    exact Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem _ _ _ _ _) code1
  let length := iTypeResult .ADDI 0x340#12 (0#64)
  obtain ⟨retired3, run3⟩ := decodeInline_first_success_copy_length_step (fromStep + 2) args
    baseState s2 pre agree2
    (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x1032c) retired2 x11 source)
    code2 pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10330) retired3 x12 length
  have w3 : WritesOnlyRegs _ s2 s3 := afterRegisterWrite_writes _ _ _ _ _
  have agree3 : Agree decoderPreserved baseState s3 :=
    Agree.trans agree2 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have calleeSaved3 : Agree decodeRawCalleeSaved baseState s3 :=
    calleeSaved2.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10334) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10330) retired3 x12 length
  have code3 : Contracts.canonicalContractParams.env.CodeIntact s3 := by
    exact Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem _ _ _ _ _) code2
  obtain ⟨retired4, run4⟩ := decodeInline_first_success_copy_call_page_step
    (fromStep + 3) args baseState s3 pre agree3
    (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10330) retired3 x12 length)
    code3 pc3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x10334) retired4 x1
    (BitVec.ofNat 64 0x14334)
  have w4 : WritesOnlyRegs _ s3 s4 := afterRegisterWrite_writes _ _ _ _ _
  have calleeSaved4 : Agree decodeRawCalleeSaved baseState s4 :=
    calleeSaved3.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
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
  have globals4 : s4.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have stack4 : s4.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have notExit1 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10328) := by
    simp [DecodeInlineExit, phase, success]
  have notExit2 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x1032c) := by
    simp [DecodeInlineExit, phase, success]
  have notExit3 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10330) := by
    simp [DecodeInlineExit, phase, success]
  have notExit4 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10334) := by
    simp [DecodeInlineExit, phase, success]
  have prefix1 : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep 1 state s1 :=
    ConfinedPrefix.ownStep' atPc (by simpa [s1, destination] using run1) (notExit := notExit1)
  have prefix2 : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep' pc1 (by simpa [s2, source] using run2) (notExit := notExit2)
  have prefix3 : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep' pc2 (by simpa [s3, length] using run3) (notExit := notExit3)
  have prefix4 : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep' pc3 (by simpa [s4] using run4) (notExit := notExit4)
  have completePrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep 4 state s4 := by
    confined_steps [prefix1, prefix2, prefix3, prefix4]
  refine ⟨s4, ?_, completePrefix, ?_, ?_, ?_, ?_, ?_, ?_, stack4, ?_, calleeSaved4, ?_, ?_, ?_, ?_⟩
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
  · exact Contracts.codeIntact_of_mem_eq memory4 code
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
  obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, -, bound, -, transfer,
    tagRun, tagPc, tagCode, tagAgree, -, tagCounter, -, -, -, tagValue, -, -, -⟩ :=
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
      DecodeInlineCallerSaveArea args state final ∧
      DecodeRawAllocationWithinCanonicalArena state final := by
  obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, parentPrefix, bound, -, transfer,
    tagRun, tagPc, tagCode, tagAgree, tagCalleeSaved, tagCounter, tagStackRaw, -, -, tagValue, tagGlobals, tagPost,
    tagProvenance, tagSaveArea, tagAllocation⟩ :=
    decodeInline_first_through_result_tag contract fromStep args state pre phase
  have internalTag : Contracts.decodeInternalResultTag
      (Contracts.meaningDecodeRaw args.bytes) = 0 := by
    simp [success, Contracts.decodeInternalResultTag]
  -- The tag written on this path is the literal `0#64`, so one rewrite retypes every retained
  -- fact about the tagged state; a second selects the outcome inside the source postcondition.
  rw [internalTag] at tagRun tagPc tagCode tagAgree tagCalleeSaved tagCounter tagStackRaw
  rw [internalTag] at tagGlobals tagValue tagPost tagProvenance tagSaveArea
  rw [success] at tagPost tagProvenance
  let tagState := afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10 (0#64)
  obtain ⟨branchRetired, branchRun, branchPc⟩ := decodeInline_first_success_branch_step
    (fromStep + 8 + childUsed) args state tagState pre tagCode tagAgree tagCounter
    tagPc tagValue
  let branchState := decodeInlineFirstSuccessBranchAfter tagState branchRetired
  have branchMemory : branchState.mem = tagState.mem := by
    rfl
  have branchCode : Contracts.canonicalContractParams.env.CodeIntact branchState := by
    exact Contracts.codeIntact_of_mem_eq branchMemory tagCode
  have branchPreserves : Agree decoderPreserved tagState branchState :=
    Agree.weaken (fun _ preserved => preserved.2)
      ((fallThroughRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
  have branchAgree : Agree decoderPreserved state branchState :=
    Agree.trans tagAgree branchPreserves
  have branchCalleeSaved : Agree decodeRawCalleeSaved state branchState :=
    tagCalleeSaved.trans (by
      simpa [branchState] using
        ((fallThroughRetirement_writes tagState (BitVec.ofNat 64 0x10324)
          (BitVec.ofNat 64 0x10328) branchRetired).agree decodeRawCalleeSaved_disjoint))
  have branchCounter : RetiredCounterPresent branchState := by
    refine ⟨Sail.BitVec.addInt branchRetired 1, ?_⟩
    simp [branchState, decodeInlineFirstSuccessBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]
  have branchStack : branchState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    ((fallThroughRetirement_writes _ _ _ _).get x2 (by decide)).trans tagStackRaw
  have branchGlobals : branchState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    ((fallThroughRetirement_writes _ _ _ _).get x18 (by decide)).trans tagGlobals
  have branchPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repStatelessInput (.ok value) state branchState := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (.ok value) rfl branchMemory
    exact tagPost
  have branchProvenance : DecodeRawSuccessAllocationProvenance args.firstRawArgs (.ok value)
      state branchState := by
    apply decodeRawSuccessAllocationProvenance_of_mem_eq rfl branchMemory
    exact tagProvenance
  have branchSaveArea : DecodeInlineCallerSaveArea args state branchState := by
    simpa [branchMemory] using tagSaveArea
  obtain ⟨final, setupTrace, setupPrefix, finalPc, finalDestination, finalSource, finalLength,
    finalLink, finalGlobals, finalStack, finalAgree, finalCalleeSaved, finalCounter, finalCode,
    finalPost, finalMemory⟩ :=
    decodeInline_first_success_copy_setup (fromStep + 9 + childUsed) args state branchState pre
      phase value success branchAgree branchCalleeSaved branchCounter branchCode branchPc branchStack branchGlobals
      (by simpa [success] using branchPost)
  have representation : BinaryFv.Zesu.DecodedValue.StatelessInputRep final args.inputBase args.bytes
      args.firstTemporaryResultBase value := by
    simpa [success] using finalPost.2.2.2.2
  obtain ⟨bases, allocation, descriptors, inputSlices⟩ := representation.layout
  have rootAllocated := BinaryFv.Zesu.DecodedValue.stateless_input_allocation_root_size final
    args.firstTemporaryResultBase value bases allocation
  obtain ⟨rootBytes, rootSize, rootMemory⟩ :=
    memoryBytes_exists_of_heapArrayRep final args.firstTemporaryResultBase 832 rootAllocated
  have exit : DecodeInlineExit args (BitVec.ofNat 64 0x10338) := by
    simp [DecodeInlineExit, phase, success]
  have post : DecodeInlineFirstPost args state final := by
    simp only [DecodeInlineFirstPost, success]
    have finalProvenance : DecodeRawSuccessAllocationProvenance args.firstRawArgs (.ok value)
        state final := by
      apply decodeRawSuccessAllocationProvenance_of_mem_eq rfl finalMemory
      exact branchProvenance
    exact ⟨by simpa [success] using finalPost, finalProvenance, finalPc, finalDestination, finalSource, finalLength,
      finalLink, rootBytes, rootSize, rootMemory⟩
  have finalSaveArea : DecodeInlineCallerSaveArea args state final := by
    unfold DecodeInlineCallerSaveArea
    rw [finalMemory]
    exact branchSaveArea
  have finalAllocation : DecodeRawAllocationWithinCanonicalArena state final := by
    rcases tagAllocation with ⟨cursorBefore, cursorAfter, beforeCursor, afterCursor, arenaBase,
      cursorOrder, cursorBound⟩
    refine ⟨cursorBefore, cursorAfter, beforeCursor, ?_, arenaBase, cursorOrder, cursorBound⟩
    unfold Contracts.DecoderEnvironment.cursor? at afterCursor ⊢
    unfold BinaryFv.Zesu.DecodedValue.observeWord64? at afterCursor ⊢
    rw [finalMemory, branchMemory]
    exact afterCursor
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
    ⟨finalAgree, finalCalleeSaved, finalCounter, finalCode, finalGlobals.trans pre.globalsValue.symm⟩,
    finalStack,
    finalSaveArea, finalAllocation⟩
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
      childUsed ≤ 16384 + 512 * args.bytes.size ∧
      Nonempty (CallTransfer decodeInlineOwnPcs
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
      ScopedTrace decodeInlineOwnPcs
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
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) ∧
      DecodeRawAllocationWithinCanonicalArena state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) := by
  obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, parentPrefix, bound,
    firstInvalidBound, transfer,
    tagRun, tagPc, tagCode, tagAgree, tagCalleeSaved, tagCounter, tagStackRaw, tagInputBase, tagInputLength, tagValue,
    tagGlobals, tagPost, tagProvenance, tagSaveArea, tagAllocation⟩ :=
    decodeInline_first_through_result_tag contract fromStep args state pre phase
  -- Select the error outcome once. Every retained fact is stated about the tagged state, so a
  -- single rewrite puts all twelve into the exact form this theorem's conclusion asks for.
  rw [failed] at tagRun tagPc tagCode tagAgree tagCounter tagStackRaw
  rw [failed] at tagInputBase tagInputLength tagValue tagGlobals tagPost tagProvenance tagSaveArea
  have exit : DecodeInlineExit args (BitVec.ofNat 64 0x10324) := by
    simp [DecodeInlineExit, phase, failed]
  have post : DecodeInlineFirstPost args state
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) := by
    simp only [DecodeInlineFirstPost, failed]
    refine ⟨tagPost, ?_, tagPc, tagValue⟩
    apply decodeRawSuccessAllocationProvenance_of_mem_eq rfl
      (afterRegisterWrite_mem resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))))
    exact tagProvenance
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
  have tail : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 7 + childUsed) 1 resumed afterTag := by
    apply ScopedTrace.ownStep (fromStep + 7 + childUsed) 0 (BitVec.ofNat 64 0x10320)
      resumed afterTag afterTag resumePc tagRegion tagNotExit
    · simpa [afterTag] using tagRun
    · exact ScopedTrace.exitAt (fromStep + 7 + childUsed + 1) afterTag
        (BitVec.ofNat 64 0x10324) (by simpa [afterTag] using tagPc) exit
  have fromCall : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 5) (childUsed + 3)
      beforeCall afterTag := by
    have shiftedTail : ScopedTrace decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
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
  have scopedFinal : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep (childUsed + 8) state afterTag := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completeTrace
  exact ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, bound, firstInvalidBound,
    ⟨callTransfer⟩,
    tagRun, exit, post, by simpa [afterTag] using scopedFinal,
    ⟨tagAgree, by simpa [afterTag, failed] using tagCalleeSaved,
      tagCounter, tagCode, tagGlobals.trans pre.globalsValue.symm⟩,
    tagInputBase, tagInputLength, tagStackRaw, tagSaveArea, tagAllocation⟩

/-- The first `invalidSsz` exit retains the two wrapper arguments consumed by the retry entry.
This is deliberately narrower than `DecodeInlineOutgoingFrame`: only the retry edge needs these
values, and the concrete error proof already establishes them at `0x10324`. -/
theorem decodeInline_first_invalidSsz_level3_save_area
    (contract : CompiledDecodeRawInstanceContract) (args : DecodeInlineArgs) (fromStep : Nat)
    (before : State) (pre : DecodeInlinePre args before) (phase : args.phase = .first)
    (invalid : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
        fromStep used before after ∧
      DecodeInlinePost args before after ∧
      DecodeInlineMachinePost before after ∧
      DecodeInlineOutgoingFrame args after ∧
      DecodeInlineCallerSaveArea args before after ∧
      after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      DecodeRawAllocationWithinCanonicalArena before after ∧
      used ≤ 16392 + 512 * args.bytes.size := by
  obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, childBound, firstInvalidBound,
    transfer,
    tagRun, exit, firstPost, trace, machinePost, inputBase, inputLength, outgoingStack, saveArea,
    allocation⟩ :=
    decodeInline_first_error_reaches_post contract fromStep args before pre phase .invalidSsz invalid
  let after := afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
    (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error .invalidSsz)))
  have rawBound : childUsed ≤ 16384 + 512 * args.bytes.size := firstInvalidBound
  refine ⟨childUsed + 8, after, decodeInline_first_stepBound_le childBound (by omega), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [after] using trace
  · simpa [DecodeInlinePost, phase, after] using firstPost
  · simpa [after] using machinePost
  · simpa [DecodeInlineOutgoingFrame, phase, after] using outgoingStack
  · simpa [after] using saveArea
  · simpa [after] using inputBase
  · simpa [after] using inputLength
  · simpa [after] using allocation
  · omega

/-- The complete first-phase arm of the Level 3 contract. This is the single scope showing the
conditional `decodeRaw` summary stitched to all parent-owned Sail execution and the selected semantic
postcondition. No other child condition is used on this phase. -/
theorem decodeInline_first_level3_relation (contract : CompiledDecodeRawInstanceContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) (phase : args.phase = .first) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep used before after ∧
      DecodeInlinePost args before after ∧
      DecodeInlineMachinePost before after ∧
      DecodeInlineOutgoingFrame args after := by
  cases resultEq : Contracts.meaningDecodeRaw args.bytes with
  | ok value =>
      obtain ⟨childUsed, final, childBound, exit, post, trace, machinePost, outgoingStack⟩ :=
        decodeInline_first_success_reaches_post contract fromStep args before pre phase value resultEq
      refine ⟨childUsed + 13, final, ?_, trace, ?_, machinePost, ?_⟩
      · exact decodeInline_first_stepBound_le childBound (by omega)
      · simpa [DecodeInlinePost, phase] using post
      · simpa [DecodeInlineOutgoingFrame, phase] using outgoingStack.1
  | error error =>
      obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, childBound, -, transfer,
        tagRun, exit, post, trace, machinePost, -, -, outgoingStack, -, -⟩ :=
        decodeInline_first_error_reaches_post contract fromStep args before pre phase error resultEq
      refine ⟨childUsed + 8,
        afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))), ?_, trace, ?_,
          machinePost, by simpa [DecodeInlineOutgoingFrame, phase] using outgoingStack⟩
      · exact decodeInline_first_stepBound_le childBound (by omega)
      · simpa [DecodeInlinePost, phase] using post

/-- Companion result for the first Level 3 outcome.  It retains the wrapper save frame proved by
the selected `decodeRaw` call while leaving `decodeInline_first_level3_relation`'s existing
semantic interface unchanged. -/
theorem decodeInline_first_level3_save_area (contract : CompiledDecodeRawInstanceContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) (phase : args.phase = .first) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep used before after ∧
      DecodeInlinePost args before after ∧
      DecodeInlineMachinePost before after ∧
      DecodeInlineOutgoingFrame args after ∧
      DecodeInlineCallerSaveArea args before after ∧
      DecodeRawAllocationWithinCanonicalArena before after := by
  cases resultEq : Contracts.meaningDecodeRaw args.bytes with
  | ok value =>
      obtain ⟨childUsed, final, childBound, _, post, trace, machinePost, stack, saveArea, allocation⟩ :=
        decodeInline_first_success_reaches_post contract fromStep args before pre phase value resultEq
      refine ⟨childUsed + 13, final, ?_, trace, ?_, machinePost, ?_, saveArea, allocation⟩
      · exact decodeInline_first_stepBound_le childBound (by omega)
      · simpa [DecodeInlinePost, phase] using post
      · simpa [DecodeInlineOutgoingFrame, phase] using stack
  | error error =>
      obtain ⟨_, childUsed, resumed, tagRetired, _, childBound, -, _, _, _, post, trace, machinePost,
        _, _, outgoing, saveArea, allocation⟩ :=
        decodeInline_first_error_reaches_post contract fromStep args before pre phase error resultEq
      refine ⟨childUsed + 8,
        afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))), ?_, trace, ?_,
          machinePost, ?_, saveArea, allocation⟩
      · exact decodeInline_first_stepBound_le childBound (by omega)
      · simpa [DecodeInlinePost, phase] using post
      · simpa [DecodeInlineOutgoingFrame, phase] using outgoing

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
  obtain ⟨-, tagA0, tagA1⟩ := pre.retryReason phase
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContext pre.machine (Agree.refl state)
  obtain ⟨retired, run⟩ := decoderBranchNotTakenStep pre.machine (Agree.refl state)
    pre.machine.retiredCounter (hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10380 0x63 0x1e 0xb5 0x06 0x7c#13 11#5 10#5 .BNE atPc
    (by unfold bTypeTaken
        refine Runs.bind
          (rX_bits_run_x10 _ (BitVec.ofNat 64 2) (decoderExecuteState_get? tagA0)) ?_
        refine Runs.bind
          (rX_bits_run_x11 _ (BitVec.ofNat 64 2) (decoderExecuteState_get? tagA1)) ?_
        rfl)
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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10384 0x13 0x05 0xf0 0xff 0xfff#12 0#5 10#5 .ADDI atPc (rX_x0_run _)
    (by rw [show iTypeResult .ADDI 0xfff#12 (0#64) = BitVec.ofNat 64 (2 ^ 64 - 1) from by
          native_decide]
        exact wX_x10_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderShiftIopStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10388 0x13 0x15 0x05 0x02 32#6 10#5 10#5 .SLLI atPc
    (rX_bits_run_x10 _ _ (decoderExecuteState_get? constant))
    (by rw [show shiftIopResult .SLLI 32#6 (BitVec.ofNat 64 (2 ^ 64 - 1)) =
              BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32) from by native_decide]
        exact wX_x10_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x1038c 0x13 0x06 0xc5 0xff 0xffc#12 10#5 12#5 .ADDI atPc
    (rX_bits_run_x10 _ _ (decoderExecuteState_get? constant))
    (by rw [show iTypeResult .ADDI 0xffc#12 (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) =
              BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4) from by native_decide]
        exact wX_x12_run _ _)

/-- Execute the retry-entry branch and all three parent-owned constant instructions, stopping at
the selected prefix helper's length-segment entry. -/
theorem decodeInline_retry_reaches_length_gate (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) :
    ∃ after,
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10390) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) ∧
      after.regs.get? x12 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)) ∧
      Agree decoderPreserved state after ∧
      Agree decodeRawCalleeSaved state after ∧
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
  have w1 : WritesOnlyRegs _ state s1 := fallThroughRetirement_writes _ _ _ _
  have preStack := pre.stackValue
  have preInput := pre.inputValue
  have preLength := pre.lengthValue
  have preGlobals := pre.globalsValue
  have branchAgree : Agree decoderPreserved state s1 :=
    Agree.weaken (fun _ preserved => preserved.2)
      ((fallThroughRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
  have callerFrame1 : Agree decodeRawCalleeSaved state s1 :=
    (fallThroughRetirement_writes _ _ _ _).agree decodeRawCalleeSaved_disjoint
  have branchCounter : RetiredCounterPresent s1 := by
    refine ⟨Sail.BitVec.addInt branchRetired 1, ?_⟩
    simp [s1, decodeInlineRetryEntryAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]
  have branchMemory : s1.mem = state.mem := rfl
  have branchCode : Contracts.canonicalContractParams.env.CodeIntact s1 := by
    exact Contracts.codeIntact_of_mem_eq branchMemory pre.code
  obtain ⟨minusOneRetired, minusOneRun⟩ := decodeInline_retry_minus_one_step
    (fromStep + 1) args state s1 pre branchAgree branchCounter branchCode branchPc
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x10384) minusOneRetired x10
    (BitVec.ofNat 64 (2 ^ 64 - 1))
  have w2 : WritesOnlyRegs _ s1 s2 := afterRegisterWrite_writes _ _ _ _ _
  -- Regression for the write-set carry below: `grind` must refuse the register this step writes.
  fail_if_success (have : s2.regs.get? x10 = s1.regs.get? x10 := by grind)
  have agree2 : Agree decoderPreserved state s2 :=
    Agree.trans branchAgree (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have callerFrame2 : Agree decodeRawCalleeSaved state s2 :=
    callerFrame1.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10388) := by
    change (afterRegisterWrite s1 (BitVec.ofNat 64 0x10384) minusOneRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 1))).regs.get? PC = _
    rw [afterRegisterWrite_pc]
    decide
  have x10At2 : s2.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 1)) := by
    simp [s2, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have code2 : Contracts.canonicalContractParams.env.CodeIntact s2 := by
    exact Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem _ _ _ _ _) branchCode
  obtain ⟨shiftRetired, shiftRun⟩ := decodeInline_retry_shift_constant_step
    (fromStep + 2) args state s2 pre agree2
    (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x10384) minusOneRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 1))) code2 pc2 x10At2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10388) shiftRetired x10
    (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))
  have w3 : WritesOnlyRegs _ s2 s3 := afterRegisterWrite_writes _ _ _ _ _
  have agree3 : Agree decoderPreserved state s3 :=
    Agree.trans agree2 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have callerFrame3 : Agree decodeRawCalleeSaved state s3 :=
    callerFrame2.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x1038c) := by
    change (afterRegisterWrite s2 (BitVec.ofNat 64 0x10388) shiftRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))).regs.get? PC = _
    rw [afterRegisterWrite_pc]
    decide
  have x10At3 : s3.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) := by
    simp [s3, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have code3 : Contracts.canonicalContractParams.env.CodeIntact s3 := by
    exact Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem _ _ _ _ _) code2
  obtain ⟨minusFourRetired, minusFourRun⟩ := decodeInline_retry_minus_four_step
    (fromStep + 3) args state s3 pre agree3
    (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10388) shiftRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))) code3 pc3 x10At3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x1038c) minusFourRetired x12
    (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))
  have w4 : WritesOnlyRegs _ s3 s4 := afterRegisterWrite_writes _ _ _ _ _
  fail_if_success (have : s4.regs.get? x12 = s3.regs.get? x12 := by grind)
  have agree4 : Agree decoderPreserved state s4 :=
    Agree.trans agree3 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have callerFrame4 : Agree decodeRawCalleeSaved state s4 :=
    callerFrame3.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x10390) := by
    change (afterRegisterWrite s3 (BitVec.ofNat 64 0x1038c) minusFourRetired x12
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))).regs.get? PC = _
    rw [afterRegisterWrite_pc]
    decide
  have x10At4 : s4.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) := by grind
  have x12At4 : s4.regs.get? x12 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)) := by
    simp [s4, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have code4 : Contracts.canonicalContractParams.env.CodeIntact s4 :=
    Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem s3 (BitVec.ofNat 64 0x1038c) minusFourRetired x12
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))) code3
  have counter4 := afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x1038c)
    minusFourRetired x12 (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes }
  have memory4 : s4.mem = state.mem := rfl
  have inputPointer4 : s4.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  have inputLength4 : s4.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  have globals4 : s4.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have stackPointer4 : s4.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have status4 : s4.regs.get? x11 = some (BitVec.ofNat 64 2) := by
    obtain ⟨-, -, statusAtEntry⟩ := pre.retryReason phase
    grind
  have inputMemory4 : BinaryFv.Zesu.DecodedValue.MemoryBytes s4 args.inputBase args.bytes := by
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
  have notExit1 := decodeInline_retry_entry_not_selected_exit args phase
  have notExit2 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10384) := by
    simp [DecodeInlineExit, phase]
  have notExit3 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10388) := by
    simp [DecodeInlineExit, phase]
  have notExit4 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x1038c) := by
    simp [DecodeInlineExit, phase]
  have p1 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep 1 state s1 :=
    ConfinedPrefix.ownStep' (by simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry)
      (by simpa [s1] using branchRun) (notExit := notExit1)
  have p2 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep' branchPc (by simpa [s2] using minusOneRun) (notExit := notExit2)
  have p3 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep' pc2 (by simpa [s3] using shiftRun) (notExit := notExit3)
  have p4 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep' pc3 (by simpa [s4] using minusFourRun) (notExit := notExit4)
  refine ⟨s4, ?_, pc4, x10At4, x12At4, agree4, callerFrame4, counter4, stackPointer4, status4, code4,
    memory4, ?_⟩
  · confined_steps [p1, p2, p3, p4]
  · simpa [childArgs] using childPre

/-- Consume the proved one-instruction prefix length segment after the four parent-owned retry
instructions. The result remains at the outgoing `bltu` for the enclosing `decode` proof to execute. -/
theorem decodeInline_retry_uses_length_gate (prefixContract : HasExactErePrefixInlineContract)
    (fromStep : Nat) (args : DecodeInlineArgs)
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
      Agree decodeRawCalleeSaved state childAfter ∧
      RetiredCounterPresent childAfter ∧
      childAfter.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      childAfter.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      childAfter.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      childAfter.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      childAfter.regs.get? x11 = some (BitVec.ofNat 64 2) ∧
      Contracts.canonicalContractParams.env.CodeIntact childAfter ∧
      childAfter.mem = state.mem := by
  obtain ⟨childEntry, parentPrefix, entryPc, x10Constant, x12Constant, parentAgree,
    parentCallerFrame, parentCounter, parentStackPointer, parentStatus, parentCode, parentMemory, childPre⟩ :=
    decodeInline_retry_reaches_length_gate fromStep args state pre phase
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes }
  have childPre' : HasExactErePrefixInlinePre childArgs childEntry := by
    simpa [childArgs] using childPre
  obtain ⟨childUsed, childAfter, childBound, childTrace, childPost, childFrame⟩ :=
    prefixContract childArgs (fromStep + 4) childEntry childPre'
  have childStatus : childAfter.regs.get? x11 = some (BitVec.ofNat 64 2) :=
    childFrame.status.trans parentStatus
  have childStackPointer : childAfter.regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) := childFrame.stackPointer.trans parentStackPointer
  have exactSummary : hasExactErePrefixInlineSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + 4) childUsed childEntry childAfter :=
    ⟨rfl, childArgs, childPre', childBound, childTrace, childPost, childFrame⟩
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
    Agree.trans parentAgree childFrame.agree
  have completeCallerFrame : Agree decodeRawCalleeSaved state childAfter :=
    Agree.trans parentCallerFrame childFrame.callerFrame
  have childCode : Contracts.canonicalContractParams.env.CodeIntact childAfter := by
    exact Contracts.codeIntact_of_mem_eq childFrame.memory parentCode
  refine ⟨childUsed, childAfter, ?_, ?_, ?_, completeAgree, completeCallerFrame, childFrame.retiredCounter,
    childStackPointer, childFrame.inputPointer, childFrame.inputLength, childFrame.globals,
    childStatus, childCode, childFrame.memory.trans parentMemory⟩
  · simpa [childArgs] using childBound
  · simpa [Nat.add_assoc] using completePrefix
  · simpa [childArgs] using childPost

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
  have machine := pre.machine.mono agree retiredPresent
  have sizeBound : args.bytes.size < 2 ^ 32 := by
    have := pre.rootInputBound
    omega
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  obtain ⟨retired, run⟩ := decoderBranchNotTakenStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10394 0x63 0x66 0xa6 0x08 0x8c#13 10#5 12#5 .BLTU atPc
    (by unfold bTypeTaken
        refine Runs.bind (rX_x12_run _ _ (decoderExecuteState_get? adjustedLength)) ?_
        refine Runs.bind (rX_bits_run_x10 _ _ (decoderExecuteState_get? constant)) ?_
        have leftFits : args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4) < 2 ^ 64 := by omega
        have rightFits : 2 ^ 64 - 2 ^ 32 < 2 ^ 64 := by omega
        simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt leftFits, Nat.mod_eq_of_lt rightFits]
        rw [show (Int.ofNat (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4)) <b
            Int.ofNat (2 ^ 64 - 2 ^ 32)) = false from by
          simp only [decide_eq_false_iff_not]
          exact Int.not_lt.mpr (Int.ofNat_le.mpr (by omega))]
        rfl)
  refine ⟨retired, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [decodeInlineRetryLengthBranchAfter] using run
  · simp [decodeInlineRetryLengthBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  · exact Agree.weaken (fun _ preserved => preserved.2)
      ((fallThroughRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
  · refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
    simp [decodeInlineRetryLengthBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]

/-- Splice the proved length child and parent-owned `bltu`, producing the complete machine entry for
the ten-instruction prefix-byte child. -/
theorem decodeInline_retry_reaches_prefix_bytes
    (prefixContract : HasExactErePrefixInlineContract)
    (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size) :
    ∃ lengthUsed childEntry,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep (5 + lengthUsed) state childEntry ∧
      HasExactErePrefixInlinePre
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } childEntry ∧
      Agree decoderPreserved state childEntry ∧
      Agree decodeRawCalleeSaved state childEntry ∧
      RetiredCounterPresent childEntry ∧
      childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      childEntry.regs.get? x11 = some (BitVec.ofNat 64 2) ∧
      Contracts.canonicalContractParams.env.CodeIntact childEntry ∧
      childEntry.mem = state.mem := by
  obtain ⟨lengthUsed, lengthAfter, lengthBound, lengthPrefix, lengthPost, lengthAgree, lengthCallerFrame,
    lengthCounter, lengthStackPointer, lengthInputPointer, lengthInputLength, lengthGlobals,
    lengthStatus, lengthCode, lengthMemory⟩ :=
    decodeInline_retry_uses_length_gate prefixContract fromStep args state pre phase
  have prefixFalseAtLength : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10394) := by
    simp [DecodeInlineExit, phase, show ¬ args.bytes.size < 4 by omega]
  obtain ⟨branchRetired, branchRun, branchPc, branchPreserves, branchCounter, branchMemory⟩ :=
    decodeInline_retry_length_branch_step (fromStep + (4 + lengthUsed)) args state lengthAfter
      pre lengthAgree lengthCounter lengthCode lengthPost.1 lengthPost.2.1 lengthPost.2.2
      fourBytes
  let childEntry := decodeInlineRetryLengthBranchAfter lengthAfter branchRetired
  have branchPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (4 + lengthUsed)) 1
      lengthAfter childEntry :=
    ConfinedPrefix.ownStep' lengthPost.1 (by simpa [childEntry] using branchRun)
      (notExit := prefixFalseAtLength)
  have completePrefix := ConfinedPrefix.trans lengthPrefix branchPrefix
  have childAgree : Agree decoderPreserved state childEntry :=
    Agree.trans lengthAgree (by simpa [childEntry] using branchPreserves)
  have childCallerFrame : Agree decodeRawCalleeSaved state childEntry :=
    lengthCallerFrame.trans
      ((fallThroughRetirement_writes _ _ _ _).agree decodeRawCalleeSaved_disjoint)
  have childMemory : childEntry.mem = state.mem := by
    have branchMemory' : childEntry.mem = lengthAfter.mem := by
      simpa [childEntry] using branchMemory
    exact branchMemory'.trans lengthMemory
  have childCode : Contracts.canonicalContractParams.env.CodeIntact childEntry := by
    exact Contracts.codeIntact_of_mem_eq childMemory pre.code
  have childStackPointer : childEntry.regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) :=
    ((fallThroughRetirement_writes _ _ _ _).get x2 (by decide)).trans lengthStackPointer
  have childGlobals : childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    ((fallThroughRetirement_writes _ _ _ _).get x18 (by decide)).trans lengthGlobals
  have childStatus : childEntry.regs.get? x11 = some (BitVec.ofNat 64 2) :=
    ((fallThroughRetirement_writes _ _ _ _).get x11 (by decide)).trans lengthStatus
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
    · exact ((fallThroughRetirement_writes _ _ _ _).get x8 (by decide)).trans lengthInputPointer
    · exact ((fallThroughRetirement_writes _ _ _ _).get x9 (by decide)).trans lengthInputLength
    · intro index bound
      rw [childMemory]
      exact pre.inputMemory index bound
    · simp [childArgs]
    · intro _
      exact fourBytes
  refine ⟨lengthUsed, childEntry, lengthBound, ?_, ?_, childAgree, childCallerFrame, ?_, childStackPointer, childGlobals,
    childStatus, childCode, childMemory⟩
  · have steps : 4 + lengthUsed + 1 = 5 + lengthUsed := by omega
    rw [← steps]
    exact completePrefix
  · change HasExactErePrefixInlinePre childArgs childEntry
    exact childPre
  · change RetiredCounterPresent childEntry at branchCounter
    exact branchCounter

/-- Consume the proved ten-instruction prefix-byte child after the length branch. The resulting
state is at `0x103c0`, where the parent still owns the final `or`. -/
theorem decodeInline_retry_uses_prefix_bytes (prefixContract : HasExactErePrefixInlineContract)
    (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size) :
    ∃ lengthUsed prefixUsed after,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      prefixUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary fromStep
          (5 + lengthUsed + prefixUsed) state after ∧
      HasExactErePrefixInlinePost
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } after ∧
      Agree decoderPreserved state after ∧
      Agree decodeRawCalleeSaved state after ∧
      RetiredCounterPresent after ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 2) ∧
      Contracts.canonicalContractParams.env.CodeIntact after ∧
      after.mem = state.mem := by
  obtain ⟨lengthUsed, childEntry, lengthBound, parentPrefix, childPre, parentAgree, parentCallerFrame, parentCounter,
    parentStackPointer, parentGlobals, parentStatus, parentCode, parentMemory⟩ :=
    decodeInline_retry_reaches_prefix_bytes prefixContract fromStep args state pre phase fourBytes
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes }
  have childPre' : HasExactErePrefixInlinePre childArgs childEntry := by
    change HasExactErePrefixInlinePre childArgs childEntry at childPre
    exact childPre
  obtain ⟨prefixUsed, after, childBound, childTrace, childPost, childFrame⟩ :=
    prefixContract childArgs (fromStep + (5 + lengthUsed)) childEntry childPre'
  have childStackPointer : after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    childFrame.stackPointer.trans parentStackPointer
  have exactSummary : hasExactErePrefixInlineSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + (5 + lengthUsed)) prefixUsed childEntry after :=
    ⟨rfl, childArgs, childPre', childBound, childTrace, childPost, childFrame⟩
  have selectedSummary : Level3ChildSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + (5 + lengthUsed)) prefixUsed childEntry after :=
    .hasExactErePrefix exactSummary
  have childPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (5 + lengthUsed)) prefixUsed
      childEntry after := by
    intro count final rest
    exact ScopedTrace.childBody _ prefixUsed count _ childEntry after final selectedSummary rest
  have completePrefix := ConfinedPrefix.trans parentPrefix childPrefix
  have completeAgree := Agree.trans parentAgree childFrame.agree
  have completeCallerFrame := Agree.trans parentCallerFrame childFrame.callerFrame
  have completeMemory : after.mem = state.mem := childFrame.memory.trans parentMemory
  have completeCode : Contracts.canonicalContractParams.env.CodeIntact after := by
    exact Contracts.codeIntact_of_mem_eq completeMemory pre.code
  have completeStatus : after.regs.get? x11 = some (BitVec.ofNat 64 2) :=
    childFrame.status.trans parentStatus
  refine ⟨lengthUsed, prefixUsed, after, lengthBound, ?_, ?_, ?_, completeAgree, completeCallerFrame,
    childFrame.retiredCounter, childStackPointer, childFrame.inputPointer, childFrame.inputLength,
    childFrame.globals, completeStatus, completeCode, completeMemory⟩
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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) false :=
    decoderRTypeStep machine (Agree.refl state) retiredPresent
      (hasExactErePrefix_programImage_of_codeIntact code)
      stepNo 0x103c0 0x33 0x65 0xa7 0x00 10#5 14#5 10#5 .OR atPc
      (rX_x14_run _ _ (decoderExecuteState_get? highRead))
      (rX_x10_run _ _ (decoderExecuteState_get? lowRead)) (wX_x10_run _ _)
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

/-- Close the four-or-more-byte prefix-mismatch arm at the selected outgoing branch source. The
branch itself transfers to wrapper code and is therefore executed by the Level 2 proof. -/
theorem decodeInline_retry_prefix_mismatch_reaches_post
    (prefixContract : HasExactErePrefixInlineContract) (fromStep : Nat)
    (args : DecodeInlineArgs) (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size)
    (notExact : Contracts.meaningHasExactErePrefix args.bytes = false) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧
      DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after ∧
      DecodeInlineCallerSaveArea args state after ∧
      used ≤ 30 := by
  obtain ⟨lengthUsed, prefixUsed, beforeOr, lengthBound, prefixBound, parentPrefix, prefixPost,
    beforeAgree, beforeCallerFrame, beforeCounter, _beforeStack, inputPointer, inputLength, beforeGlobals,
    _beforeStatus, beforeCode, beforeMemory⟩ :=
    decodeInline_retry_uses_prefix_bytes prefixContract fromStep args state pre phase fourBytes
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
  have orPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (5 + lengthUsed + prefixUsed)) 1
      beforeOr after :=
    ConfinedPrefix.ownStep' prefixPost.1 (by simpa [after] using orRun) (notExit := orNotExit)
  have completePrefix := ConfinedPrefix.trans parentPrefix orPrefix
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x103c4) := by
    simp [DecodeInlineExit, phase, notExact, show ¬ args.bytes.size < 4 by omega]
  have tail : ScopedTrace decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (5 + lengthUsed + prefixUsed + 1)) 0 after after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x103c4) (by simpa [after] using orPc)
      selectedExit
  have trace := completePrefix 0 after tail
  have rawInvalid : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz :=
    (pre.retryReason phase).1
  have resultInvalid : Contracts.meaningDecode args.bytes = .error .invalidSsz := by
    simp [Contracts.meaningDecode, rawInvalid, notExact]
  have afterAgree : Agree decoderPreserved state after := beforeAgree.trans orPreserves
  have afterCallerFrame : Agree decodeRawCalleeSaved state after :=
    beforeCallerFrame.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have afterCode : Contracts.canonicalContractParams.env.CodeIntact after := by
    exact Contracts.codeIntact_of_mem_eq (orMemory.trans beforeMemory) pre.code
  have wOr : WritesOnlyRegs _ beforeOr after := afterRegisterWrite_writes _ _ _ _ _
  have afterGlobals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  refine ⟨6 + lengthUsed + prefixUsed, after, ?_, ?_, ?_,
    ⟨afterAgree, afterCallerFrame, orCounter, afterCode, afterGlobals.trans pre.globalsValue.symm⟩, ?_, ?_, ?_⟩
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
  · intro index bound
    simpa [after, afterRegisterWrite_mem] using
      congrArg (fun mem => mem.get? (args.stackBase + 0xa00 + index))
        (orMemory.trans beforeMemory)
  · have prefixBoundValue : prefixUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using prefixBound
    have lengthBoundValue : lengthUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using lengthBound
    omega

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103c8 0x13 0x06 0x44 0x00 0x004#12 8#5 12#5 .ADDI atPc
    (rX_x8_run _ _ (decoderExecuteState_get? inputRead)) (wX_x12_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103cc 0x13 0x05 0x01 0x6b 0x6b0#12 2#5 10#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x10_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103d0 0x93 0x05 0x01 0x01 0x010#12 2#5 11#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x11_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderAuipcStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103d4 0x97 0x00 0x00 0x00 0x00000#20 1#5 atPc
    (by simpa using wX_bits_run_x1 _ (BitVec.ofNat 64 0x103d4))

set_option maxHeartbeats 8000000 in
/-- Execute every `decode`-owned instruction from retry entry through the second `decodeRaw` call
site. The two prefix-helper segments are consumed as child summaries; the branch, framing-word
assembly, and four call-argument instructions are executed directly through Sail. -/
theorem decodeInline_retry_before_second_decodeRaw_call
    (prefixContract : HasExactErePrefixInlineContract) (fromStep : Nat)
    (args : DecodeInlineArgs) (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true) :
    ∃ lengthUsed prefixUsed beforeCall,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      prefixUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary fromStep
          (11 + lengthUsed + prefixUsed) state beforeCall ∧
      beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103d8) ∧
      beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x103d4) ∧
      beforeCall.regs.get? x10 = some (BitVec.ofNat 64 (args.stackBase + 0x6b0)) ∧
      beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
      beforeCall.regs.get? x12 = some (BitVec.ofNat 64 (args.inputBase + 4)) ∧
      beforeCall.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4)) ∧
      beforeCall.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      beforeCall.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      beforeCall.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Agree decoderPreserved state beforeCall ∧
      Agree decodeRawCalleeSaved state beforeCall ∧
      RetiredCounterPresent beforeCall ∧
      Contracts.canonicalContractParams.env.CodeIntact beforeCall ∧
      beforeCall.mem = state.mem := by
  have fourBytes : 4 ≤ args.bytes.size := by
    rw [Contracts.meaningHasExactErePrefix] at exactPrefix
    split at exactPrefix <;> simp_all
  obtain ⟨lengthUsed, prefixUsed, beforeOr, lengthBound, prefixBound, prefixTrace,
    prefixPost, agreeBeforeOr, callerFrameBeforeOr, counterBeforeOr, stackBeforeOr, inputBeforeOr, lengthBeforeOr,
    globalsBeforeOr, _statusBeforeOr, codeBeforeOr, memoryBeforeOr⟩ :=
    decodeInline_retry_uses_prefix_bytes prefixContract fromStep args state pre phase fourBytes
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
  have wOr : WritesOnlyRegs _ beforeOr sOr := afterRegisterWrite_writes _ _ _ _ _
  have lengthAtOr : sOr.regs.get? x13 =
      some (BitVec.ofNat 64 (args.bytes.size - 4)) :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x13 (by decide)).trans prefixPost.2.2.2
  have agreeOr := Agree.trans agreeBeforeOr orAgree
  have callerFrameOr : Agree decodeRawCalleeSaved state sOr :=
    callerFrameBeforeOr.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have codeOr : Contracts.canonicalContractParams.env.CodeIntact sOr := by
    exact Contracts.codeIntact_of_mem_eq (orMemory.trans memoryBeforeOr) pre.code
  obtain ⟨branchRetired, branchRun, branchPc, branchAgree, branchCounter, branchMemory⟩ :=
    decodeInline_retry_prefix_branch_not_taken
      (fromStep + (6 + lengthUsed + prefixUsed)) args state sOr pre agreeOr orCounter codeOr
      orPc declared declaredAtOr lengthAtOr declaredEq
  let sBranch := decodeInlineRetryPrefixBranchFallThrough sOr branchRetired
  have wBranch : WritesOnlyRegs _ sOr sBranch := fallThroughRetirement_writes _ _ _ _
  have agreeBranch : Agree decoderPreserved state sBranch :=
    Agree.trans agreeOr (by simpa [sBranch] using branchAgree)
  have callerFrameBranch : Agree decodeRawCalleeSaved state sBranch :=
    callerFrameOr.trans ((fallThroughRetirement_writes _ _ _ _).agree decodeRawCalleeSaved_disjoint)
  have memoryBranch : sBranch.mem = state.mem := by
    calc
      sBranch.mem = sOr.mem := by simpa [sBranch] using branchMemory
      _ = beforeOr.mem := orMemory
      _ = state.mem := memoryBeforeOr
  have codeBranch : Contracts.canonicalContractParams.env.CodeIntact sBranch := by
    exact Contracts.codeIntact_of_mem_eq memoryBranch pre.code
  have inputAtBranch : sBranch.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  have stackAtBranch : sBranch.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  obtain ⟨tailRetired, tailRun⟩ := decodeInline_retry_tail_pointer_step
    (fromStep + (7 + lengthUsed + prefixUsed)) args state sBranch pre agreeBranch
      (by simpa [sBranch] using branchCounter) codeBranch branchPc inputAtBranch
  let sTail := afterRegisterWrite sBranch (BitVec.ofNat 64 0x103c8) tailRetired x12
    (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))
  have wTail : WritesOnlyRegs _ sBranch sTail := afterRegisterWrite_writes _ _ _ _ _
  have agreeTail : Agree decoderPreserved state sTail := Agree.trans agreeBranch (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have callerFrameTail : Agree decodeRawCalleeSaved state sTail :=
    callerFrameBranch.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have counterTail := afterRegisterWrite_retired_present sBranch
    (BitVec.ofNat 64 0x103c8) tailRetired x12
      (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))
  have pcTail : sTail.regs.get? PC = some (BitVec.ofNat 64 0x103cc) := by
    simpa [sTail] using afterRegisterWrite_pc sBranch (BitVec.ofNat 64 0x103c8) tailRetired
      x12 (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))
  have stackTail : sTail.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have codeTail : Contracts.canonicalContractParams.env.CodeIntact sTail :=
    Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem sBranch (BitVec.ofNat 64 0x103c8) tailRetired x12
      (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))) codeBranch
  obtain ⟨resultRetired, resultRun⟩ := decodeInline_retry_result_pointer_step
    (fromStep + (8 + lengthUsed + prefixUsed)) args state sTail pre agreeTail counterTail codeTail
      pcTail stackTail
  let sResult := afterRegisterWrite sTail (BitVec.ofNat 64 0x103cc) resultRetired x10
    (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))
  have wResult : WritesOnlyRegs _ sTail sResult := afterRegisterWrite_writes _ _ _ _ _
  have agreeResult : Agree decoderPreserved state sResult := Agree.trans agreeTail (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have callerFrameResult : Agree decodeRawCalleeSaved state sResult :=
    callerFrameTail.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have counterResult := afterRegisterWrite_retired_present sTail
    (BitVec.ofNat 64 0x103cc) resultRetired x10
      (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))
  have pcResult : sResult.regs.get? PC = some (BitVec.ofNat 64 0x103d0) := by
    simpa [sResult] using afterRegisterWrite_pc sTail (BitVec.ofNat 64 0x103cc) resultRetired
      x10 (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))
  have stackResult : sResult.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have codeResult : Contracts.canonicalContractParams.env.CodeIntact sResult :=
    Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem sTail (BitVec.ofNat 64 0x103cc) resultRetired x10
      (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))) codeTail
  obtain ⟨allocatorRetired, allocatorRun⟩ := decodeInline_retry_allocator_pointer_step
    (fromStep + (9 + lengthUsed + prefixUsed)) args state sResult pre agreeResult counterResult
      codeResult pcResult stackResult
  let sAllocator := afterRegisterWrite sResult (BitVec.ofNat 64 0x103d0) allocatorRetired x11
    (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))
  have wAllocator : WritesOnlyRegs _ sResult sAllocator := afterRegisterWrite_writes _ _ _ _ _
  have agreeAllocator : Agree decoderPreserved state sAllocator := Agree.trans agreeResult (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have callerFrameAllocator : Agree decodeRawCalleeSaved state sAllocator :=
    callerFrameResult.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have counterAllocator := afterRegisterWrite_retired_present sResult
    (BitVec.ofNat 64 0x103d0) allocatorRetired x11
      (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))
  have pcAllocator : sAllocator.regs.get? PC = some (BitVec.ofNat 64 0x103d4) := by
    simpa [sAllocator] using afterRegisterWrite_pc sResult (BitVec.ofNat 64 0x103d0)
      allocatorRetired x11 (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))
  have codeAllocator : Contracts.canonicalContractParams.env.CodeIntact sAllocator :=
    Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem sResult (BitVec.ofNat 64 0x103d0) allocatorRetired
      x11 (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))) codeResult
  obtain ⟨pageRetired, pageRun⟩ := decodeInline_retry_call_page_step
    (fromStep + (10 + lengthUsed + prefixUsed)) args state sAllocator pre agreeAllocator
      counterAllocator codeAllocator pcAllocator
  let beforeCall := afterRegisterWrite sAllocator (BitVec.ofNat 64 0x103d4) pageRetired x1
    (BitVec.ofNat 64 0x103d4)
  have wPage : WritesOnlyRegs _ sAllocator beforeCall := afterRegisterWrite_writes _ _ _ _ _
  have agreeBeforeCall : Agree decoderPreserved state beforeCall := Agree.trans agreeAllocator (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have callerFrameBeforeCall : Agree decodeRawCalleeSaved state beforeCall :=
    callerFrameAllocator.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have counterBeforeCall := afterRegisterWrite_retired_present sAllocator
    (BitVec.ofNat 64 0x103d4) pageRetired x1 (BitVec.ofNat 64 0x103d4)
  have codeBeforeCall : Contracts.canonicalContractParams.env.CodeIntact beforeCall :=
    Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem sAllocator (BitVec.ofNat 64 0x103d4) pageRetired x1
      (BitVec.ofNat 64 0x103d4)) codeAllocator
  have memoryBeforeCall : beforeCall.mem = state.mem := by
    exact memoryBranch
  have notExit (pc : Nat) (pcFits : pc < 2 ^ 64) (notFinal : pc ≠ 0x103f8) :
      ¬ DecodeInlineExit args (BitVec.ofNat 64 pc) := by
    simp only [DecodeInlineExit, phase, exactPrefix, ↓reduceIte]
    intro equal
    apply notFinal
    have sameNat := congrArg BitVec.toNat equal
    simpa [Nat.mod_eq_of_lt pcFits] using sameNat
  have pOr : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (5 + lengthUsed + prefixUsed)) 1 beforeOr sOr :=
    ConfinedPrefix.ownStep' prefixPost.1 (by simpa [sOr] using orRun)
      (notExit := notExit 0x103c0 (by decide) (by decide))
  have pBranch : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (6 + lengthUsed + prefixUsed)) 1 sOr sBranch :=
    ConfinedPrefix.ownStep' orPc (by simpa [sBranch] using branchRun)
      (notExit := notExit 0x103c4 (by decide) (by decide))
  have pTail : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (7 + lengthUsed + prefixUsed)) 1 sBranch sTail :=
    ConfinedPrefix.ownStep' branchPc (by simpa [sTail] using tailRun)
      (notExit := notExit 0x103c8 (by decide) (by decide))
  have pResult : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (8 + lengthUsed + prefixUsed)) 1 sTail sResult :=
    ConfinedPrefix.ownStep' pcTail (by simpa [sResult] using resultRun)
      (notExit := notExit 0x103cc (by decide) (by decide))
  have pAllocator : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (9 + lengthUsed + prefixUsed)) 1 sResult sAllocator :=
    ConfinedPrefix.ownStep' pcResult (by simpa [sAllocator] using allocatorRun)
      (notExit := notExit 0x103d0 (by decide) (by decide))
  have pPage : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (10 + lengthUsed + prefixUsed)) 1 sAllocator beforeCall :=
    ConfinedPrefix.ownStep' pcAllocator (by simpa [beforeCall] using pageRun)
      (notExit := notExit 0x103d4 (by decide) (by decide))
  have prefixOr : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep (6 + lengthUsed + prefixUsed) state sOr :=
    ConfinedPrefix.trans' _ prefixTrace pOr
  have prefixBranch : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep (7 + lengthUsed + prefixUsed) state sBranch :=
    ConfinedPrefix.trans' _ prefixOr pBranch
  have prefixTail : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep (8 + lengthUsed + prefixUsed) state sTail :=
    ConfinedPrefix.trans' _ prefixBranch pTail
  have prefixResult : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep (9 + lengthUsed + prefixUsed) state sResult :=
    ConfinedPrefix.trans' _ prefixTail pResult
  have prefixAllocator : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args)
      Level3ChildSummary fromStep (10 + lengthUsed + prefixUsed) state sAllocator :=
    ConfinedPrefix.trans' _ prefixResult pAllocator
  have complete : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep (11 + lengthUsed + prefixUsed) state beforeCall :=
    ConfinedPrefix.trans' _ prefixAllocator pPage
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
      some (BitVec.ofNat 64 (args.bytes.size - 4)) := by grind
  have inputBeforeCall : beforeCall.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  have lengthBeforeCall : beforeCall.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  have globalsBeforeCall : beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  refine ⟨lengthUsed, prefixUsed, beforeCall, lengthBound, prefixBound, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, inputBeforeCall, lengthBeforeCall, globalsBeforeCall, agreeBeforeCall,
    callerFrameBeforeCall, counterBeforeCall, codeBeforeCall, memoryBeforeCall⟩
  · exact complete
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
  · grind
  · grind

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
      Agree decodeRawCalleeSaved state (decodeInlineRetryCallAfter state retired) ∧
      (decodeInlineRetryCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (decodeInlineRetryCallAfter state retired) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContextOfDecoderAgree pre.machine agree
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) state
      (decodeInlineRetryCallAfter state retired) false :=
    decoderJalrCallStep pre.machine agree retiredPresent
      (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
      stepNo 0x103d8 0xe7 0x80 0x00 0x07 0x070#12 1#5 1#5 (BitVec.ofNat 64 0x103d4)
      (BitVec.ofNat 64 0x103dc) (BitVec.ofNat 64 0x10444) atPc
      (rX_bits_run_x1 _ _ (decoderExecuteState_get? callBase)) (wX_bits_run_x1 _ _)
  have callWrites : WritesOnlyRegs _ state (decodeInlineRetryCallAfter state retired) :=
    callRetirement_writes _ _ _ _ _ _
  fail_if_success (have : (decodeInlineRetryCallAfter state retired).regs.get? x1 =
    state.regs.get? x1 := by grind)
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
  have callCallerFrame : Agree decodeRawCalleeSaved state
      (decodeInlineRetryCallAfter state retired) := by
    apply jalrCallAfterRetired_agree_of
    all_goals simp [decodeRawCalleeSaved]
  refine ⟨retired, run, pcAfter, linkAfter, by grind, by grind, by grind, by grind,
    callAgree, callCallerFrame, jalrCallAfterRetired_mem _ _ _ _ _ _, ?_⟩
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
    CallTransfer decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary decodeRawRetryCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw fromStep used beforeCall resumed := by
  have atRet := decodeRaw_trace_exit_pc childTrace
  have callInRegion := decodeInline_owned_in_execution_region (0x103d8, 0x070080e7)
    (by simp [decodeInlineOwnedInstructionWords])
  have returnInRegion := decodeInline_owned_in_execution_region (0x103dc, 0x02010513)
    (by simp [decodeInlineOwnedInstructionWords])
  have retInRegion : decodeInlineOwnPcs (BitVec.ofNat 64 0x10530) := by owned_pc
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
    (contract : CompiledDecodeRawInstanceContract)
    (prefixContract : HasExactErePrefixInlineContract)
    (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true) :
    ∃ lengthUsed prefixUsed childUsed beforeCall resumed,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      prefixUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.retryRawArgs ∧
      ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary fromStep
          (11 + lengthUsed + prefixUsed) state beforeCall ∧
      Nonempty (CallTransfer decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary decodeRawRetryCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + (11 + lengthUsed + prefixUsed))
          childUsed beforeCall resumed) ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.retryRawArgs
        Contracts.canonicalContractParams.repStatelessInput
        (Contracts.meaningDecodeRaw args.retryRawArgs.bytes) state resumed ∧
      Agree decoderPreserved state resumed ∧
      Agree decodeRawCalleeSaved state resumed ∧
      RetiredCounterPresent resumed ∧
      resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      resumed.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      resumed.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      DecodeRawResultPayloadInitialized args.retryRawArgs resumed ∧
      Contracts.canonicalContractParams.env.CodeIntact resumed ∧
      DecodeInlineCallerSaveArea args state resumed ∧
      DecodeRawAllocationWithinCanonicalArena state resumed ∧
      DecodeRawSuccessAllocationProvenance args.retryRawArgs
        (Contracts.meaningDecode args.bytes) state resumed := by
  obtain ⟨lengthUsed, prefixUsed, beforeCall, lengthBound, prefixBound, parentPrefix, callPc,
    callBase, resultPointer, allocatorPointer, inputPointer, inputLength, beforeStack,
    beforeInputBase, beforeInputLength, beforeGlobals, beforeAgree, beforeCallerFrame,
    beforeCounter, beforeCode, beforeMemory⟩ :=
    decodeInline_retry_before_second_decodeRaw_call prefixContract fromStep args state pre phase
      exactPrefix
  obtain ⟨callRetired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, callAgree, callCallerFrame, callMemory, childCounter⟩ :=
    decodeInline_retry_decodeRaw_call_step
      (fromStep + (11 + lengthUsed + prefixUsed)) args state beforeCall pre beforeAgree
      beforeMemory beforeCounter callPc callBase resultPointer allocatorPointer inputPointer
      inputLength
  let childEntry := decodeInlineRetryCallAfter beforeCall callRetired
  have childAgree : Agree decoderPreserved state childEntry := Agree.trans beforeAgree callAgree
  have childCalleeSaved : Agree decodeRawCalleeSaved state childEntry :=
    beforeCallerFrame.trans callCallerFrame
  have childMemory : childEntry.mem = state.mem := callMemory.trans beforeMemory
  have childStack : childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    ((callRetirement_writes _ _ _ _ _ _).get x2 (by decide)).trans beforeStack
  have childInputBase : childEntry.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    ((callRetirement_writes _ _ _ _ _ _).get x8 (by decide)).trans beforeInputBase
  have childInputLength : childEntry.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    ((callRetirement_writes _ _ _ _ _ _).get x9 (by decide)).trans beforeInputLength
  have childGlobals : childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    ((callRetirement_writes _ _ _ _ _ _).get x18 (by decide)).trans beforeGlobals
  have entryFrame : DecodeRawEntryFrame state := by
    simpa [DecodeInlineRawCallFrame, phase] using pre.rawCallFrame
  have childFrame : DecodeRawEntryFrame childEntry :=
    DecodeRawEntryFrame.of_calleeSaved_agree entryFrame childCalleeSaved childStack
      childInputBase childInputLength childGlobals
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
  have childMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs args.retryRawArgs) childEntry :=
    (childMachineAtParentExtent.narrowInput readableSubset).restrict
      decodeRaw_executionPcs_subset_decodeInline
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
    · change Contracts.canonicalContractParams.env.image.fileBytesLoadedFaithfully childEntry.mem
      rw [childMemory]
      exact pre.code
    · simpa [DecodeInlineArgs.retryRawArgs] using childResult
    · simpa [DecodeInlineArgs.retryRawArgs] using childAllocator
    · simpa [DecodeInlineArgs.retryRawArgs] using childInput
    · simpa [DecodeInlineArgs.retryRawArgs, tailSize] using childLength
  have childPre : compiledDecodeRawContract.binding.entry args.retryRawArgs childEntry :=
    ⟨childSourceEntry, childPc, childFrame, childMachine⟩
  obtain ⟨childUsed, childExit, childBound, childTrace, childPost⟩ :=
    contract args.retryRawArgs (fromStep + (12 + lengthUsed + prefixUsed)) childEntry childPre
  obtain ⟨returnRetired, returnRun, atResume⟩ :=
    decodeRaw_return_step (fromStep + (12 + lengthUsed + prefixUsed + childUsed))
      args.retryRawArgs (BitVec.ofNat 64 0x103dc) childEntry childExit (by decide) (by decide)
      childPre childTrace childLink childPost
  let resumed := decodeRawReturnAfter (BitVec.ofNat 64 0x103dc) childExit returnRetired
  rcases childPost with ⟨sourcePost, childFrame, childExitCounter, childPayload, childSaveArea,
    childProvenance, childAllocation⟩
  rcases sourcePost with ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have childFrameDecoder : Agree decoderPreserved childEntry childExit :=
    Agree.weaken (fun _ preserved => Or.inl preserved.2) childFrame
  have resumedAgree : Agree decoderPreserved state resumed := Agree.trans childAgree
    (Agree.trans childFrameDecoder (by
      simpa [resumed] using
        decodeRawReturnAfter_agree (BitVec.ofNat 64 0x103dc) childExit returnRetired))
  have childFrameCalleeSaved : Agree decodeRawCalleeSaved childEntry childExit :=
    Agree.weaken
      (fun _ preserved => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr preserved))))) childFrame
  have resumedCallerFrame : Agree decodeRawCalleeSaved state resumed :=
    childCalleeSaved.trans
      (childFrameCalleeSaved.trans
        (decodeRawReturnAfter_calleeSaved (BitVec.ofNat 64 0x103dc) childExit returnRetired))
  have wReturn : WritesOnlyRegs _ childExit resumed := jumpRetirement_writes _ _ _ _
  have exitStack : childExit.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (childFrame x2 (by simp [decodeRawCallerPreserved])).trans childStack
  have exitGlobals : childExit.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (childFrame x18 (by simp [decodeRawCallerPreserved])).trans childGlobals
  have resumedStack : resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have exitInputBase : childExit.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    (childFrame x8 (by simp [decodeRawCallerPreserved])).trans childInputBase
  have exitInputLength : childExit.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    (childFrame x9 (by simp [decodeRawCallerPreserved])).trans childInputLength
  have resumedInputBase : resumed.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  have resumedInputLength : resumed.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  have resumedGlobals : resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have resumedPost : Contracts.postEntry Contracts.canonicalContractParams.env args.retryRawArgs
      Contracts.canonicalContractParams.repStatelessInput
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
        childFrame, childExitCounter, childPayload, childSaveArea, childProvenance, childAllocation⟩
      (by simpa [resumed, Nat.add_assoc] using returnRun) (by simpa [resumed] using atResume)
  have resumedCode : Contracts.canonicalContractParams.env.CodeIntact resumed := by
    exact Contracts.codeIntact_of_mem_eq
      (decodeRawReturnAfter_mem (BitVec.ofNat 64 0x103dc) childExit returnRetired) childCode
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
  have resumedAllocation : DecodeRawAllocationWithinCanonicalArena state resumed := by
    rcases childAllocation with ⟨cursorBefore, cursorAfter, beforeCursor, afterCursor, arenaBase,
      cursorOrder, cursorBound⟩
    refine ⟨cursorBefore, cursorAfter, ?_, ?_, arenaBase, cursorOrder, cursorBound⟩
    · unfold Contracts.DecoderEnvironment.cursor? at beforeCursor ⊢
      unfold BinaryFv.Zesu.DecodedValue.observeWord64? at beforeCursor ⊢
      rw [← childMemory]
      exact beforeCursor
    · unfold Contracts.DecoderEnvironment.cursor? at afterCursor ⊢
      unfold BinaryFv.Zesu.DecodedValue.observeWord64? at afterCursor ⊢
      rw [decodeRawReturnAfter_mem]
      exact afterCursor
  have resumedProvenance : DecodeRawSuccessAllocationProvenance args.retryRawArgs
      (Contracts.meaningDecode args.bytes) state resumed := by
    simpa [Contracts.meaningDecode, (pre.retryReason phase).1, exactPrefix,
      DecodeInlineArgs.retryRawArgs] using
      decodeRawSuccessAllocationProvenance_of_mem_eq childMemory.symm
        (decodeRawReturnAfter_mem (BitVec.ofNat 64 0x103dc) childExit returnRetired) childProvenance
  exact ⟨lengthUsed, prefixUsed, childUsed, beforeCall, resumed, lengthBound, prefixBound,
    childBound, parentPrefix, ⟨transfer⟩, resumedPost, resumedAgree, resumedCallerFrame,
    decodeRawReturnAfter_retired (BitVec.ofNat 64 0x103dc) childExit returnRetired,
    resumedStack, resumedInputBase, resumedInputLength, resumedGlobals, resumedPayload, resumedCode, resumedSaveArea, resumedAllocation,
    resumedProvenance⟩

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103dc 0x13 0x05 0x01 0x02 0x020#12 2#5 10#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x10_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103e0 0x93 0x05 0x01 0x6b 0x6b0#12 2#5 11#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x11_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103e4 0x13 0x06 0x00 0x34 0x340#12 0#5 12#5 .ADDI atPc
    (rX_x0_run _) (wX_x12_run _ _)

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderAuipcStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103e8 0x97 0x40 0x00 0x00 0x00004#20 1#5 atPc
    (by simpa using wX_bits_run_x1 _ (BitVec.ofNat 64 0x143e8))

/-- Execute the four retry-copy setup words and establish the exact compiled `memcpy` arguments. -/
theorem decodeInline_retry_copy_setup (fromStep : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true)
    (agree : Agree decoderPreserved baseState state)
    (callerFrame : Agree decodeRawCalleeSaved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (globalsRead : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103dc))
    (payload : DecodeRawResultPayloadInitialized args.retryRawArgs state) :
    ∃ contents beforeCall,
      contents.size = 832 ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state beforeCall ∧
      beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103ec) ∧
      beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x143e8) ∧
      beforeCall.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase) ∧
      beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.retryRawArgs.resultBase) ∧
      beforeCall.regs.get? x12 = some (BitVec.ofNat 64 832) ∧
      beforeCall.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      DecodedValue.MemoryBytes beforeCall args.retryRawArgs.resultBase contents ∧
      Agree decoderPreserved baseState beforeCall ∧
      Agree decodeRawCalleeSaved baseState beforeCall ∧
      RetiredCounterPresent beforeCall ∧
      Contracts.canonicalContractParams.env.CodeIntact beforeCall ∧
      beforeCall.mem = state.mem := by
  obtain ⟨contents, contentsSize, contentsMemory⟩ := payload
  let destination := iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired1, run1⟩ := decodeInline_retry_copy_destination_step fromStep args
    baseState state pre agree retiredPresent code atPc stackRead
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103dc) retired1 x10 destination
  have w1 : WritesOnlyRegs _ state s1 := afterRegisterWrite_writes _ _ _ _ _
  have agree1 : Agree decoderPreserved baseState s1 := Agree.trans agree (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have callerFrame1 : Agree decodeRawCalleeSaved baseState s1 := callerFrame.trans
    (afterRegisterWrite_agree_of (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]))
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x103e0) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103dc) retired1 x10 destination
  have stack1 : s1.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have code1 : Contracts.canonicalContractParams.env.CodeIntact s1 := by
    exact Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem _ _ _ _ _) code
  let source := iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired2, run2⟩ := decodeInline_retry_copy_source_step (fromStep + 1) args
    baseState s1 pre agree1
      (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103dc) retired1 x10 destination)
      code1 pc1 stack1
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x103e0) retired2 x11 source
  have w2 : WritesOnlyRegs _ s1 s2 := afterRegisterWrite_writes _ _ _ _ _
  have agree2 : Agree decoderPreserved baseState s2 := Agree.trans agree1 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have callerFrame2 : Agree decodeRawCalleeSaved baseState s2 := callerFrame1.trans
    (afterRegisterWrite_agree_of (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]))
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x103e4) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x103e0) retired2 x11 source
  have code2 : Contracts.canonicalContractParams.env.CodeIntact s2 := by
    exact Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem _ _ _ _ _) code1
  let length := iTypeResult .ADDI 0x340#12 (0#64)
  obtain ⟨retired3, run3⟩ := decodeInline_retry_copy_length_step (fromStep + 2) args
    baseState s2 pre agree2
      (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x103e0) retired2 x11 source)
      code2 pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x103e4) retired3 x12 length
  have w3 : WritesOnlyRegs _ s2 s3 := afterRegisterWrite_writes _ _ _ _ _
  have agree3 : Agree decoderPreserved baseState s3 := Agree.trans agree2 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have callerFrame3 : Agree decodeRawCalleeSaved baseState s3 := callerFrame2.trans
    (afterRegisterWrite_agree_of (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]))
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x103e8) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x103e4) retired3 x12 length
  have code3 : Contracts.canonicalContractParams.env.CodeIntact s3 := by
    exact Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem _ _ _ _ _) code2
  obtain ⟨retired4, run4⟩ := decodeInline_retry_copy_call_page_step (fromStep + 3) args
    baseState s3 pre agree3
      (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x103e4) retired3 x12 length)
      code3 pc3
  let beforeCall := afterRegisterWrite s3 (BitVec.ofNat 64 0x103e8) retired4 x1
    (BitVec.ofNat 64 0x143e8)
  have w4 : WritesOnlyRegs _ s3 beforeCall := afterRegisterWrite_writes _ _ _ _ _
  have agree4 : Agree decoderPreserved baseState beforeCall := agree3.trans
    (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have callerFrame4 : Agree decodeRawCalleeSaved baseState beforeCall := callerFrame3.trans
    (afterRegisterWrite_agree_of (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]))
  have notExit (pc : Nat) (pcFits : pc < 2 ^ 64) (different : pc ≠ 0x103f8) :
      ¬ DecodeInlineExit args (BitVec.ofNat 64 pc) := by
    simp only [DecodeInlineExit, phase, exactPrefix, ↓reduceIte]
    intro equal
    apply different
    have sameNat := congrArg BitVec.toNat equal
    simpa [Nat.mod_eq_of_lt pcFits] using sameNat
  have p1 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep 1 state s1 :=
    ConfinedPrefix.ownStep' atPc (by simpa [s1, destination] using run1)
      (notExit := notExit 0x103dc (by decide) (by decide))
  have p2 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep' pc1 (by simpa [s2, source] using run2)
      (notExit := notExit 0x103e0 (by decide) (by decide))
  have p3 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep' pc2 (by simpa [s3, length] using run3)
      (notExit := notExit 0x103e4 (by decide) (by decide))
  have p4 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 3) 1 s3 beforeCall :=
    ConfinedPrefix.ownStep' pc3 (by simpa [beforeCall] using run4)
      (notExit := notExit 0x103e8 (by decide) (by decide))
  have complete : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep 4 state beforeCall := by
    confined_steps [p1, p2, p3, p4]
  have destinationEq : destination = BitVec.ofNat 64 args.finalResultBase := by
    simp only [destination, iTypeResult, DecodeInlineArgs.finalResultBase]
    rw [show sign_extend (0x020#12) = (BitVec.ofNat 64 0x20) by decide,
      ← BitVec.ofNat_add]
  have sourceEq : source = BitVec.ofNat 64 args.retryRawArgs.resultBase := by
    simp only [source, iTypeResult, DecodeInlineArgs.retryRawArgs]
    rw [show sign_extend (0x6b0#12) = (BitVec.ofNat 64 0x6b0) by decide,
      ← BitVec.ofNat_add]
  have lengthEq : length = BitVec.ofNat 64 832 := by simp [length, iTypeResult]; decide
  have globalsBeforeCall : beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  refine ⟨contents, beforeCall, contentsSize, complete, ?_, ?_, ?_, ?_, ?_, ?_,
    globalsBeforeCall, ?_, agree4, callerFrame4, ?_, ?_, ?_⟩
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
  · grind
  · intro index bound
    have memoryEq : beforeCall.mem = state.mem := by
      simp [beforeCall, s3, s2, s1, afterRegisterWrite_mem]
    rw [memoryEq]
    exact contentsMemory index bound
  · exact afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x103e8) retired4 x1
      (BitVec.ofNat 64 0x143e8)
  · exact Contracts.codeIntact_of_mem_eq (afterRegisterWrite_mem s3 (BitVec.ofNat 64 0x103e8) retired4 x1
      (BitVec.ofNat 64 0x143e8)) code3
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
theorem decodeInline_retry_uses_memcpy (memcpy : CompiledMemcpyInstanceContract)
    (fromStep : Nat) (args : DecodeInlineArgs)
    (contents : ByteArray) (baseState beforeCall : State) (pre : DecodeInlinePre args baseState)
    (contentsSize : contents.size = 832)
    (sourceMemory : DecodedValue.MemoryBytes beforeCall
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
  have callWrites : WritesOnlyRegs _ beforeCall childEntry := callRetirement_writes _ _ _ _ _ _
  let copyArgs := decodeInlineRetryCopyArgs args contents
  have childAgree : Agree decoderPreserved baseState childEntry := Agree.trans agree callAgree
  have childCode : Contracts.canonicalContractParams.env.CodeIntact childEntry := by
    exact Contracts.codeIntact_of_mem_eq (by simpa [childEntry] using callMemory) code
  have childSourceMemory : DecodedValue.MemoryBytes childEntry
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
    memcpy copyArgs (fromStep + 1) childEntry compiledEntry
  exact ⟨callRetired, childUsed, childEntry, childExit, rfl, by grind,
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
    CallTransfer decodeInlineOwnPcs
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
  have retInRegion : decodeInlineOwnPcs (BitVec.ofNat 64 0x13ec0) := by owned_pc
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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderLuiStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103f0 0x37 0x15 0x00 0x00 0x00001#20 10#5 atPc
    (by simpa [show sign_extend (m := 64) (0x00001#20 ++ 0x000#12) = BitVec.ofNat 64 0x1000 from by
          decide] using wX_x10_run _ (BitVec.ofNat 64 0x1000))

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
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderRTypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103f4 0x33 0x05 0xa1 0x00 10#5 2#5 10#5 .ADD atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead))
    (rX_bits_run_x10 _ _ (decoderExecuteState_get? pageRead))
    (by rw [show rTypeResult .ADD (BitVec.ofNat 64 args.stackBase) (BitVec.ofNat 64 0x1000) =
              BitVec.ofNat 64 (args.stackBase + 0x1000) from by
            show BitVec.ofNat 64 args.stackBase + BitVec.ofNat 64 0x1000 = _
            rw [← BitVec.ofNat_add]]
        exact wX_x10_run _ _)

/-- Close the short-input retry arm at the selected `0x10394` exit. The outgoing branch belongs to
the Level 2 wrapper, so this Level 3 trace stops before executing it. -/
theorem decodeInline_retry_short_reaches_post (prefixContract : HasExactErePrefixInlineContract)
    (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (short : args.bytes.size < 4) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧
      DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after ∧
      DecodeInlineCallerSaveArea args state after ∧
      used ≤ 16 := by
  obtain ⟨childUsed, childAfter, childBound, parentPrefix, childPost, agree, callerFrame, counter, -, -, -,
    childGlobals, _childStatus, code, memory⟩ :=
    decodeInline_retry_uses_length_gate prefixContract fromStep args state pre phase
  have prefixFalse : Contracts.meaningHasExactErePrefix args.bytes = false :=
    meaningHasExactErePrefix_false_of_size_lt_four args.bytes short
  have atExit : childAfter.regs.get? PC = some (BitVec.ofNat 64 0x10394) := by
    simpa [HasExactErePrefixInlinePost] using childPost.1
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x10394) := by
    simp [DecodeInlineExit, phase, prefixFalse, short]
  have tail : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (4 + childUsed)) 0
      childAfter childAfter :=
    ScopedTrace.exitAt _ childAfter (BitVec.ofNat 64 0x10394) atExit selectedExit
  have trace := parentPrefix 0 childAfter tail
  have rawInvalid : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz :=
    (pre.retryReason phase).1
  have resultInvalid : Contracts.meaningDecode args.bytes = .error .invalidSsz := by
    simp [Contracts.meaningDecode, rawInvalid, prefixFalse]
  refine ⟨4 + childUsed, childAfter, ?_, ?_, ?_,
    ⟨agree, callerFrame, counter, code, childGlobals.trans pre.globalsValue.symm⟩, ?_, ?_, ?_⟩
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
  · intro index bound
    rw [memory]
  · have lengthBound : hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } = 12 := rfl
    rw [lengthBound] at childBound
    omega

end BinaryFv.Zesu.MachineExecution
