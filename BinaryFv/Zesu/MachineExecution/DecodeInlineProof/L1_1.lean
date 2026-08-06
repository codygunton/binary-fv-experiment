import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryPrefix
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry
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

theorem decodeInline_first_result_pointer_step (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10308) retired x10
          (iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10308) := by
    simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContext pre.machine (Agree.refl state)
  exact decoderITypeStep pre.machine (Agree.refl state) pre.machine.retiredCounter
    (hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10308 0x13 0x05 0x01 0x36 0x360#12 2#5 10#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? pre.stackValue)) (wX_x10_run _ _)

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

def decodeInlineFirstCallAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1031c) (BitVec.ofNat 64 0x10444) x1
      (BitVec.ofNat 64 0x10320))
    (BitVec.ofNat 64 0x10444) retired

/-- Read off the generated exit address of the selected emitted `decodeRaw` from its own trace. -/
theorem decodeRaw_trace_exit_pc {childFrom childUsed : Nat} {childEntry childExit : State}
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

end BinaryFv.Zesu.MachineExecution
