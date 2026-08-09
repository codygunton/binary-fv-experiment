import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.Contracts.StatelessInputRelocation
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.OwnedPc

/-!
# The first `memcpy` transfer in `zesu_decode_raw`

This module owns the real `jalr` at `0x10338`, the emitted `memcpy` summary, and its `ret` back
to `0x1033c`.  The call is attributed to the first inlined `decode` segment, but the enclosing
Level 2 wrapper trace owns the call boundary.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/--
The one call boundary this module proves, named once: the wrapper's scope, the wrapper and `memcpy`
function instances, and the `memcpyFirstDecodeResult` binding, with only the trace offset, the
retired child length, and the two states left to vary.

This is an `abbrev`, so it is the same type as the spelled-out `CallTransfer` application and unifies
with it in either direction. The child's retired step count stays an explicit argument, because it is
what the child-summary interface consumes.
-/
abbrev FirstMemcpyCallTransfer (fromStep childUsed : Nat) (before resumed : State) : Type :=
  CallTransfer decodeRawExecutionPcs decodeRawExit
    Level2ChildSummary memcpyFirstDecodeResult generatedProgram
    functionInstance_raw_decoder_root_zesu_decode_raw functionInstance_memcpy
    fromStep childUsed before resumed

/-- State immediately after the real `jalr x1, -0x47c(x1)` at `0x10338`. -/
def firstMemcpyCallAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10338) (BitVec.ofNat 64 0x13eb8) x1
      (BitVec.ofNat 64 0x1033c))
    (BitVec.ofNat 64 0x13eb8) retired

/-- Sail execution of the first emitted-`memcpy` call.  Its inputs are the registers established
by the preceding four proved `decode` instructions; no callable source ABI is assumed. -/
theorem first_memcpy_call_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (code : canonicalContractParams.env.CodeIntact state)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10338))
    (callBase : state.regs.get? x1 = some (BitVec.ofNat 64 0x14334)) :
    ∃ retired,
      Runs (try_step stepNo false) state (firstMemcpyCallAfter state retired) false ∧
      (firstMemcpyCallAfter state retired).regs.get? PC = some (BitVec.ofNat 64 0x13eb8) ∧
      (firstMemcpyCallAfter state retired).regs.get? x1 = some (BitVec.ofNat 64 0x1033c) ∧
      (firstMemcpyCallAfter state retired).regs.get? x10 = state.regs.get? x10 ∧
      (firstMemcpyCallAfter state retired).regs.get? x11 = state.regs.get? x11 ∧
      (firstMemcpyCallAfter state retired).regs.get? x12 = state.regs.get? x12 ∧
      (firstMemcpyCallAfter state retired).regs.get? x2 = state.regs.get? x2 ∧
      Agree decoderPreserved state (firstMemcpyCallAfter state retired) ∧
      (firstMemcpyCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (firstMemcpyCallAfter state retired) := by
  obtain ⟨retired, run⟩ := decoderJalrCallStep (linkReg := x1) (linkValue := BitVec.ofNat 64 0x1033c)
    pre.machine agree retiredPresent (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10338 0xe7 0x80 0x40 0xb8 0xb84#12 1#5 1#5 (BitVec.ofNat 64 0x14334)
    (BitVec.ofNat 64 0x1033c) (BitVec.ofNat 64 0x13eb8) atPc
    (rX_bits_run_x1 _ _ (decoderExecuteState_get? callBase)) (wX_bits_run_x1 _ _)
  have run' : Runs (try_step stepNo false) state (firstMemcpyCallAfter state retired) false := by
    simpa [firstMemcpyCallAfter] using run
  have callWrites : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x1)) state
      (firstMemcpyCallAfter state retired) :=
    callRetirement_writes state (BitVec.ofNat 64 0x10338) (BitVec.ofNat 64 0x13eb8) retired x1
      (BitVec.ofNat 64 0x1033c)
  refine ⟨retired, run', ?_, ?_, callWrites.get x10 (by decide), callWrites.get x11 (by decide),
    callWrites.get x12 (by decide), callWrites.get x2 (by decide), ?_,
    jalrCallAfterRetired_mem _ _ _ _ _ _, ?_⟩
  · exact tryStepControlFlowAfterRetired_pc _ (BitVec.ofNat 64 0x13eb8) retired
  · apply tryStepControlFlowAfterRetired_preserves_register
    · exact callLinkState_link _ _ _ x1 (BitVec.ofNat 64 0x1033c)
    · decide
    · decide
  · apply jalrCallAfterRetired_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  · exact tryStepControlFlowAfterRetired_retired_present _ (BitVec.ofNat 64 0x13eb8) retired

/-- The first successful `decodeRaw` payload copy has the same emitted body as the retry copy,
but reads the first temporary record at `sp + 0x360`. -/
def firstMemcpyCopyArgs (args : DecodeInlineArgs) (contents : ByteArray) : CopyArgs where
  destination := args.finalResultBase
  source := args.firstTemporaryResultBase
  length := 832
  contents := contents

/-- The enclosing decoder's checked machine facts provide the emitted `memcpy` entry for the first
success path.  Both copy ranges are explicit stack subranges, not a function ABI. -/
theorem first_memcpy_machine_pre (args : DecodeInlineArgs) (contents : ByteArray)
    (baseState childEntry : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState childEntry)
    (counter : RetiredCounterPresent childEntry)
    (atEntry : childEntry.regs.get? PC = some (BitVec.ofNat 64 0x13eb8))
    (returnAddress : childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x1033c)) :
    MemcpyMachinePre canonicalContractParams.env (firstMemcpyCopyArgs args contents) childEntry := by
  let copyArgs := firstMemcpyCopyArgs args contents
  change MemcpyMachinePre canonicalContractParams.env copyArgs childEntry
  have machineAtEntry : DecodeInlineMachinePre args childEntry := pre.machine.mono agree counter
  have resultSize : canonicalContractParams.env.record.entryResult = 848 := by
    have pinned := congrArg (fun record => record.entryResult) canonicalRecordSizes_pinned
    simpa [canonicalContractParams, canonicalEnvironment] using pinned
  have sourceFits : copyArgs.source + copyArgs.length ≤ 2 ^ 64 := by
    dsimp [copyArgs, firstMemcpyCopyArgs, DecodeInlineArgs.firstTemporaryResultBase]
    have stackFit := pre.stackObjectsFit
    rw [resultSize] at stackFit
    omega
  have destinationFits : copyArgs.destination + copyArgs.length ≤ 2 ^ 64 := by
    dsimp [copyArgs, firstMemcpyCopyArgs, DecodeInlineArgs.finalResultBase]
    have stackFit := pre.stackObjectsFit
    rw [resultSize] at stackFit
    omega
  have sourceReadable : ∀ index, index < copyArgs.length →
      DecoderReadableByte args.machineArgs (copyArgs.source + index) := by
    intro index bound
    right; right; left
    dsimp [copyArgs, firstMemcpyCopyArgs, DecodeInlineArgs.firstTemporaryResultBase] at bound ⊢
    have stack := pre.stackObjectsReadable (0x360 + index) (by rw [resultSize]; omega)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stack
  have destinationWritable : ∀ index, index < copyArgs.length →
      DecoderWritableByte (copyArgs.destination + index) := by
    intro index bound
    left
    dsimp [copyArgs, firstMemcpyCopyArgs, DecodeInlineArgs.finalResultBase] at bound ⊢
    have stack := pre.stackObjectsReadable (0x20 + index) (by rw [resultSize]; omega)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stack
  have destinationNotFile : ∀ index, index < copyArgs.length →
      canonicalContractParams.env.image.readFileByte? (copyArgs.destination + index) = none := by
    intro index bound
    cases read : canonicalContractParams.env.image.readFileByte? (copyArgs.destination + index) with
    | none => rfl
    | some byte =>
        have segmentInfo := BinaryFv.Binary.ProgramImage.readFileByte?_mem_segment read
        obtain ⟨segment, member, -, addressHigh⟩ := segmentInfo
        have fileSegmentsBelow : Artifacts.programImage.segments.toList.all
            (fun segment => decide
              (segment.initialEndAddress ≤ Entrypoints.ZesuDecodeRaw.loadedCeiling)) = true := by
          native_decide
        have segmentHigh : segment.initialEndAddress ≤ Entrypoints.ZesuDecodeRaw.loadedCeiling :=
          of_decide_eq_true (List.all_eq_true.mp fileSegmentsBelow segment (by
            simpa [canonicalContractParams, canonicalEnvironment] using member))
        have stackByte : canonicalContractParams.env.stack (copyArgs.destination + index) := by
          dsimp [copyArgs, firstMemcpyCopyArgs, DecodeInlineArgs.finalResultBase] at bound ⊢
          have stack := pre.stackObjectsReadable (0x20 + index) (by rw [resultSize]; omega)
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stack
        have below : copyArgs.destination + index < Entrypoints.ZesuDecodeRaw.loadedCeiling :=
          Nat.lt_of_lt_of_le addressHigh segmentHigh
        exact absurd stackByte (canonicalStack_above_loaded _ below)
  have destinationNotAllocator : ∀ address, canonicalContractParams.env.allocatorState address →
      address < copyArgs.destination ∨ copyArgs.destination + copyArgs.length ≤ address := by
    intro address allocator
    by_cases before : address < copyArgs.destination
    · exact Or.inl before
    right
    by_cases after : copyArgs.destination + copyArgs.length ≤ address
    · exact after
    exfalso
    have indexBound : address - copyArgs.destination < copyArgs.length := by omega
    have stackByte : canonicalContractParams.env.stack
        (copyArgs.destination + (address - copyArgs.destination)) := by
      dsimp [copyArgs, firstMemcpyCopyArgs, DecodeInlineArgs.finalResultBase] at indexBound ⊢
      have stack := pre.stackObjectsReadable (0x20 + (address - (args.stackBase + 0x20)))
        (by rw [resultSize]; omega)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stack
    have addressEq : copyArgs.destination + (address - copyArgs.destination) = address := by omega
    exact canonicalStack_disjoint_from_allocatorState address allocator (by simpa [addressEq] using stackByte)
  apply memcpyMachinePre_of_decoder copyArgs childEntry machineAtEntry
  · intro pc bodyPc
    rcases bodyPc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> owned_pc
  · exact atEntry
  · exact ⟨BitVec.ofNat 64 0x1033c, returnAddress, by decide⟩
  · rfl
  · simp [copyArgs, firstMemcpyCopyArgs]
  · dsimp [copyArgs, firstMemcpyCopyArgs, DecodeInlineArgs.firstTemporaryResultBase]
    have stackFit := pre.stackObjectsFit
    rw [resultSize] at stackFit
    omega
  · dsimp [copyArgs, firstMemcpyCopyArgs, DecodeInlineArgs.finalResultBase]
    have stackFit := pre.stackObjectsFit
    rw [resultSize] at stackFit
    omega
  · exact sourceFits
  · exact destinationFits
  · exact destinationNotFile
  · exact destinationNotAllocator
  · exact sourceReadable
  · exact destinationWritable

/-- Execute the first call and consume the selected emitted-`memcpy` contract on the exact 832 bytes
produced by the first `decodeRaw` result. -/
theorem first_memcpy_uses_contract (memcpy : CompiledMemcpyInstanceContract)
    (fromStep : Nat) (args : DecodeInlineArgs)
    (contents : ByteArray) (baseState beforeCall : State) (pre : DecodeInlinePre args baseState)
    (contentsSize : contents.size = 832)
    (sourceMemory : DecodedValue.MemoryBytes beforeCall args.firstTemporaryResultBase contents)
    (agree : Agree decoderPreserved baseState beforeCall)
    (counter : RetiredCounterPresent beforeCall)
    (code : canonicalContractParams.env.CodeIntact beforeCall)
    (atCall : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x10338))
    (callBase : beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x14334))
    (destination : beforeCall.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase))
    (source : beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.firstTemporaryResultBase))
    (length : beforeCall.regs.get? x12 = some (BitVec.ofNat 64 832)) :
    ∃ callRetired childUsed childEntry childExit,
      childEntry = firstMemcpyCallAfter beforeCall callRetired ∧
      Runs (try_step fromStep false) beforeCall childEntry false ∧
      Agree decoderPreserved beforeCall childEntry ∧
      (compiledMemcpyContract canonicalContractParams.env).binding.entry
        (firstMemcpyCopyArgs args contents) childEntry ∧
      childUsed ≤ (compiledMemcpyContract canonicalContractParams.env).binding.stepBound
        (firstMemcpyCopyArgs args contents) ∧
      EnteredFunctionTrace
        (functionInstanceExecutionPcs generatedProgram functionInstance_memcpy)
        (functionInstanceExitPred functionInstance_memcpy)
        (functionInstanceEntryWord functionInstance_memcpy)
        (fromStep + 1) childUsed childEntry childExit ∧
      (compiledMemcpyContract canonicalContractParams.env).binding.exit
        (firstMemcpyCopyArgs args contents)
        ((compiledMemcpyContract canonicalContractParams.env).spec.meaning
          (firstMemcpyCopyArgs args contents)) childEntry childExit := by
  obtain ⟨callRetired, callRun, childPc, childLink, childDestination, childSource, childLength,
    -, callAgree, callMemory, childCounter⟩ :=
    first_memcpy_call_step fromStep args baseState beforeCall pre agree code counter atCall callBase
  let childEntry := firstMemcpyCallAfter beforeCall callRetired
  let copyArgs := firstMemcpyCopyArgs args contents
  have childAgree : Agree decoderPreserved baseState childEntry := Agree.trans agree callAgree
  have childCode : canonicalContractParams.env.CodeIntact childEntry := by
    rw [DecoderEnvironment.CodeIntact, show childEntry.mem = beforeCall.mem by
      simpa [childEntry] using callMemory]
    exact code
  have childSourceMemory : DecodedValue.MemoryBytes childEntry
      args.firstTemporaryResultBase contents := by
    intro index bound
    rw [show childEntry.mem = beforeCall.mem by simpa [childEntry] using callMemory]
    exact sourceMemory index bound
  have machinePre : MemcpyMachinePre canonicalContractParams.env copyArgs childEntry := by
    apply first_memcpy_machine_pre args contents baseState childEntry pre childAgree childCounter
    · simpa [childEntry] using childPc
    · simpa [childEntry] using childLink
  have sourcePre : (contractMemcpy canonicalContractParams.env).pre copyArgs childEntry := by
    constructor
    · refine ⟨childSourceMemory, ?_, childCode, ?_, ?_, ?_⟩
      · simpa [copyArgs, firstMemcpyCopyArgs] using contentsSize
      · simpa [copyArgs, firstMemcpyCopyArgs, childEntry] using childDestination.trans destination
      · simpa [copyArgs, firstMemcpyCopyArgs, childEntry] using childSource.trans source
      · simpa [copyArgs, firstMemcpyCopyArgs, childEntry] using childLength.trans length
    · left
      change args.stackBase + 0x20 + 832 ≤ args.stackBase + 0x360
      omega
  have compiledEntry : (compiledMemcpyContract canonicalContractParams.env).binding.entry
      copyArgs childEntry := ⟨sourcePre, machinePre⟩
  obtain ⟨childUsed, childExit, childBound, childTrace, childPost⟩ :=
    memcpy copyArgs (fromStep + 1) childEntry compiledEntry
  exact ⟨callRetired, childUsed, childEntry, childExit, rfl,
    by simpa [childEntry] using callRun, by simpa [childEntry] using callAgree, compiledEntry,
    childBound, childTrace, childPost⟩

/-- The complete checked call phase: the Sail-proved call at `0x10338`, the closed emitted
`memcpy` summary, and the Sail-proved `ret` to `0x1033c`. -/
theorem first_memcpy_call_transfer (memcpy : CompiledMemcpyInstanceContract)
    (fromStep : Nat) (args : DecodeInlineArgs)
    (contents : ByteArray) (baseState beforeCall : State) (pre : DecodeInlinePre args baseState)
    (contentsSize : contents.size = 832)
    (sourceMemory : DecodedValue.MemoryBytes beforeCall args.firstTemporaryResultBase contents)
    (agree : Agree decoderPreserved baseState beforeCall)
    (counter : RetiredCounterPresent beforeCall)
    (code : canonicalContractParams.env.CodeIntact beforeCall)
    (atCall : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x10338))
    (callBase : beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x14334))
    (destination : beforeCall.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase))
    (source : beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.firstTemporaryResultBase))
    (length : beforeCall.regs.get? x12 = some (BitVec.ofNat 64 832)) :
    ∃ childUsed resumed,
      Nonempty (FirstMemcpyCallTransfer fromStep childUsed beforeCall resumed) ∧
      resumed.regs.get? PC = some (BitVec.ofNat 64 0x1033c) := by
  obtain ⟨callRetired, bodyUsed, childEntry, childExit, childEntryEq, callRun, -, childPre,
    bodyBound, childTrace, childPost⟩ :=
    first_memcpy_uses_contract memcpy fromStep args contents baseState beforeCall pre contentsSize
      sourceMemory agree counter code atCall callBase destination source length
  have childLink : childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x1033c) := by
    rw [childEntryEq]
    simp [firstMemcpyCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, callLinkState, Std.ExtDHashMap.get?_insert]
  obtain ⟨returnRetired, returnRun, returnedPc⟩ :=
    memcpy_return_step (fromStep + 1 + bodyUsed) (firstMemcpyCopyArgs args contents)
      (BitVec.ofNat 64 0x1033c) childEntry childExit (by decide) (by decide) childPre childTrace
      childLink childPost
  let resumed := memcpyReturnAfter (BitVec.ofNat 64 0x1033c) childExit returnRetired
  have atRet : childExit.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) := by
    obtain ⟨exitPc, atExit, isExit⟩ := childTrace.trace.final_at_exit
    have exitPcEq : exitPc = BitVec.ofNat 64 0x13ec0 := by
      apply BitVec.eq_of_toNat_eq
      simpa [functionInstanceExitPred, FunctionInstance.isExit, functionInstance_memcpy] using isExit
    simpa [exitPcEq] using atExit
  have body : Level2ChildSummary functionInstance_memcpyId (fromStep + 1) bodyUsed childEntry childExit :=
    .memcpy ⟨rfl, firstMemcpyCopyArgs args contents, childPre, bodyBound, childTrace, childPost⟩
  refine ⟨bodyUsed, resumed, ⟨?_⟩, by simpa [resumed] using returnedPc⟩
  exact
    { valid := memcpyFirstDecodeResult_valid
      callPc := BitVec.ofNat 64 0x10338
      atCall
      callSource := by decide
      callInRegion := by owned_pc
      callNotExit := by owned_pc
      sCall := childEntry
      doCall := callRun
      calleeEntryPc := BitVec.ofNat 64 0x13eb8
      atCalleeEntry := childPre.2.entry
      calleeEntryMatches := by decide
      sRet := childExit
      body
      retPc := BitVec.ofNat 64 0x13ec0
      atRet
      retInRegion := by owned_pc
      retNotExit := by owned_pc
      doReturn := by simpa [resumed, Nat.add_assoc] using returnRun
      returnPc := BitVec.ofNat 64 0x1033c
      atResume := by simpa [resumed] using returnedPc
      returnMatches := by decide
      resumeInRegion := by owned_pc }

/-- The real first-copy call/return together with the facts consumed by the following tag-zero
store.  These are consequences of the compiled `memcpy` proof, not a callable ABI. -/
structure FirstMemcpyTransferFrame (fromStep : Nat) (args : DecodeInlineArgs) (contents : ByteArray)
    (before atCall : State) (childUsed : Nat) (resumed : State) : Prop where
  transfer : Nonempty (FirstMemcpyCallTransfer fromStep childUsed atCall resumed)
  atResume : resumed.regs.get? PC = some (BitVec.ofNat 64 0x1033c)
  contentsSize : contents.size = 832
  copyBound : childUsed ≤ 64 + 8 * 832
  destinationMemory : DecodedValue.MemoryBytes resumed args.finalResultBase contents
  sourceRepresentation : ∃ value, meaningDecodeRaw args.bytes = .ok value ∧
    DecodedValue.StatelessInputRep atCall args.inputBase args.bytes args.firstTemporaryResultBase value
  destinationRepresentation : ∃ value cursorBefore cursorAfter,
    meaningDecodeRaw args.bytes = .ok value ∧
      StatelessInputRepInHeapInterval resumed args.inputBase args.bytes args.finalResultBase value
        cursorBefore cursorAfter ∧ cursorAfter ≤ Elflings.canonicalHeapLimit
  inputAtCall : DecodedValue.MemoryBytes atCall args.inputBase args.bytes
  copyFrame : CopyDestinationFrame (firstMemcpyCopyArgs args contents) atCall resumed
  code : canonicalContractParams.env.CodeIntact resumed
  retiredCounter : RetiredCounterPresent resumed
  globalsValue : resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  stackValue : resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)
  decoder : Agree decoderPreserved before resumed
  callerSaveArea : DecodeInlineCallerSaveArea args before resumed

/-- Discharge every first-call input from the first `decodeRaw` success frame.  In particular,
the link value comes from the proved `auipc` at `0x10334`; it is not a source ABI premise. -/
theorem first_memcpy_transfer_of_first_post (memcpy : CompiledMemcpyInstanceContract)
    (fromStep : Nat) (args : DecodeInlineArgs)
    (before atCall : State) (pre : DecodeInlinePre args before)
    (value : BinaryFv.Specs.SSZ.StatelessInput)
    (success : meaningDecodeRaw args.bytes = .ok value)
    (post : DecodeInlineFirstPost args before atCall)
    (frame : DecodeInlineMachinePost before atCall) :
    ∃ used resumed,
      Nonempty (FirstMemcpyCallTransfer fromStep used atCall resumed) ∧
      resumed.regs.get? PC = some (BitVec.ofNat 64 0x1033c) := by
  simp only [DecodeInlineFirstPost, success] at post
  obtain ⟨-, -, atPc, destination, source, length, callBase, contents, contentsSize, sourceMemory⟩ := post
  exact first_memcpy_call_transfer memcpy fromStep args contents before atCall pre contentsSize sourceMemory
    frame.agree frame.retiredCounter frame.code atPc callBase destination source length

/-- At an arbitrary trace offset, retain the first-copy payload and machine frame for the tag-zero
continuation. -/
theorem first_memcpy_transfer_frame_of_first_post (memcpy : CompiledMemcpyInstanceContract)
    (fromStep : Nat) (args : DecodeInlineArgs)
    (before atCall : State) (pre : DecodeInlinePre args before)
    (value : BinaryFv.Specs.SSZ.StatelessInput)
    (success : meaningDecodeRaw args.bytes = .ok value)
    (post : DecodeInlineFirstPost args before atCall)
    (frame : DecodeInlineMachinePost before atCall) (phase : args.phase = .first)
    (outgoing : DecodeInlineOutgoingFrame args atCall)
    (saveArea : DecodeInlineCallerSaveArea args before atCall)
    (allocationFrame : DecodeInlineFirstAllocationFrame args before atCall) :
    ∃ contents childUsed resumed,
      FirstMemcpyTransferFrame fromStep args contents before atCall childUsed resumed := by
  simp only [DecodeInlineFirstPost, success] at post
  obtain ⟨entryPost, provenance, atPc, destination, source, length, callBase, contents, contentsSize,
    sourceMemory⟩ := post
  obtain ⟨callRetired, bodyUsed, childEntry, childExit, childEntryEq, callRun, callAgree, childPre,
    bodyBound, childTrace, childPost⟩ :=
    first_memcpy_uses_contract memcpy fromStep args contents before atCall pre contentsSize sourceMemory
      frame.agree frame.retiredCounter frame.code atPc callBase destination source length
  have childLink : childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x1033c) := by
    rw [childEntryEq]
    simp [firstMemcpyCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, callLinkState, Std.ExtDHashMap.get?_insert]
  rcases childPost with ⟨sourcePost, machinePost⟩
  rcases sourcePost with ⟨exitCode, noAllocation, writesOnly, copyFrame, sourceAfter,
    destinationMemory⟩
  obtain ⟨returnRetired, returnRun, returnedPc⟩ :=
    memcpy_return_step (fromStep + 1 + bodyUsed) (firstMemcpyCopyArgs args contents)
      (BitVec.ofNat 64 0x1033c) childEntry childExit (by decide) (by decide) childPre childTrace
      childLink ⟨⟨exitCode, noAllocation, writesOnly, copyFrame, sourceAfter, destinationMemory⟩,
        machinePost⟩
  let resumed := memcpyReturnAfter (BitVec.ofNat 64 0x1033c) childExit returnRetired
  have atCallGlobals : atCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    frame.globalsValue.trans pre.globalsValue
  have callWrites : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x1)) atCall
      (firstMemcpyCallAfter atCall callRetired) :=
    callRetirement_writes atCall (BitVec.ofNat 64 0x10338) (BitVec.ofNat 64 0x13eb8) callRetired x1
      (BitVec.ofNat 64 0x1033c)
  have childGlobals : childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    rw [childEntryEq]
    exact (callWrites.get x18 (by decide)).trans atCallGlobals
  have atCallStack : atCall.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simpa [DecodeInlineOutgoingFrame, phase] using outgoing
  have childEntryStack : childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    rw [childEntryEq]
    exact (callWrites.get x2 (by decide)).trans atCallStack
  have childExitStack : childExit.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (machinePost.frame x2 (by simp [NonW])).trans childEntryStack
  have returnWrites : WritesOnlyRegs stepBookkeeping childExit resumed :=
    jumpRetirement_writes childExit (BitVec.ofNat 64 0x13ec0) (BitVec.ofNat 64 0x1033c) returnRetired
  have resumedStack : resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (returnWrites.get x2 (by decide)).trans childExitStack
  have childEntryAgree : Agree decoderPreserved before childEntry := frame.agree.trans callAgree
  have childExitAgree : Agree decoderPreserved before childExit := childEntryAgree.trans
    (Agree.weaken (fun register preserved => by
      rcases preserved with ⟨notLink, platform⟩
      rcases platform with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [NonW]) machinePost.frame)
  have resumedAgree : Agree decoderPreserved before resumed :=
    childExitAgree.trans
      (returnWrites.agree (platformPreserved_disjoint.weaken (fun _ preserved => preserved.2)))
  have childEntryMemory : childEntry.mem = atCall.mem := by
    rw [childEntryEq]
    rfl
  have resumedMemory : resumed.mem = childExit.mem := by rfl
  have returnedCopyFrame : CopyDestinationFrame (firstMemcpyCopyArgs args contents) atCall resumed := by
    intro address outside
    rw [resumedMemory, copyFrame address outside, childEntryMemory]
  have sourceRepresentation : DecodedValue.StatelessInputRep atCall args.inputBase args.bytes
      args.firstTemporaryResultBase value := by
    simpa [DecodeInlineArgs.firstRawArgs] using entryPost.2.2.2.2
  obtain ⟨cursorBefore, cursorAfter, beforeCursor, afterCursor, allocated⟩ := provenance
  obtain allocationBound := allocationFrame phase
  obtain ⟨boundBefore, boundAfter, boundBeforeCursor, boundAfterCursor, -, -, cursorBound⟩ :=
    allocationBound
  have afterEq : boundAfter = cursorAfter :=
    Option.some.inj (boundAfterCursor.symm.trans afterCursor)
  have representationAfter : StatelessInputRepInHeapInterval resumed args.inputBase args.bytes
      args.firstTemporaryResultBase value cursorBefore cursorAfter :=
    allocated.survives_copy (firstMemcpyCopyArgs args contents) returnedCopyFrame
      (by
        intro address root
        dsimp [range, DecodeInlineArgs.firstTemporaryResultBase] at root
        right
        simp [firstMemcpyCopyArgs, DecodeInlineArgs.finalResultBase,
          DecodeInlineArgs.firstTemporaryResultBase]
        omega)
      (by
        intro address interval
        dsimp [Contracts.interval] at interval
        left
        have stackAddress := pre.stackObjectsReadable 0x20 (by omega)
        have notBelow : ¬ args.stackBase + 0x20 < Elflings.canonicalHeapLimit := by
          intro below
          exact canonicalArena_not_in_stack (args.stackBase + 0x20) below
            (by simpa [canonicalContractParams, canonicalEnvironment] using stackAddress)
        have heapLimitBelowStack : Elflings.canonicalHeapLimit ≤ args.stackBase + 0x20 := by omega
        dsimp [firstMemcpyCopyArgs, DecodeInlineArgs.finalResultBase]
        omega)
  have destinationRepresentation : StatelessInputRepInHeapInterval resumed args.inputBase args.bytes
      args.finalResultBase value cursorBefore cursorAfter :=
    representationAfter.rebase_root (by
      have resultSize : canonicalContractParams.env.record.entryResult = 848 := by
        have pinned := congrArg (fun record => record.entryResult) canonicalRecordSizes_pinned
        simpa [canonicalContractParams, canonicalEnvironment] using pinned
      have fits := pre.stackObjectsFit
      rw [resultSize] at fits
      simp [DecodeInlineArgs.finalResultBase]
      omega)
      (by
        intro index bound
        rw [resumedMemory]
        have destinationMemory' : DecodedValue.MemoryBytes childExit args.finalResultBase contents := by
          simpa [firstMemcpyCopyArgs, meaningCopy] using destinationMemory
        exact (destinationMemory' index (by simpa [contentsSize] using bound)).trans
          (sourceAfter index (by simpa [firstMemcpyCopyArgs, contentsSize] using bound)).symm)
  have resumedSaveArea : DecodeInlineCallerSaveArea args before resumed := by
    intro index bound
    rw [resumedMemory]
    rw [copyFrame (args.stackBase + 0xa00 + index) (Or.inr (by
      simp [firstMemcpyCopyArgs, DecodeInlineArgs.finalResultBase]
      omega))]
    rw [childEntryMemory]
    exact saveArea index bound
  have atRet : childExit.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) := by
    obtain ⟨exitPc, atExit, isExit⟩ := childTrace.trace.final_at_exit
    have exitPcEq : exitPc = BitVec.ofNat 64 0x13ec0 := by
      apply BitVec.eq_of_toNat_eq
      simpa [functionInstanceExitPred, FunctionInstance.isExit, functionInstance_memcpy] using isExit
    simpa [exitPcEq] using atExit
  have body : Level2ChildSummary functionInstance_memcpyId (fromStep + 1) bodyUsed childEntry childExit :=
    .memcpy ⟨rfl, firstMemcpyCopyArgs args contents, childPre, bodyBound, childTrace,
      ⟨⟨exitCode, noAllocation, writesOnly, copyFrame, sourceAfter, destinationMemory⟩, machinePost⟩⟩
  refine ⟨contents, bodyUsed, resumed, ⟨⟨?_⟩, ?_, contentsSize, ?_, ?_, ⟨value, success,
    sourceRepresentation⟩, ⟨value, cursorBefore, cursorAfter, success, destinationRepresentation,
      afterEq ▸ cursorBound⟩,
    entryPost.1,
    returnedCopyFrame, ?_, ?_, ?_, resumedStack,
    resumedAgree, resumedSaveArea⟩⟩
  exact
    { valid := memcpyFirstDecodeResult_valid
      callPc := BitVec.ofNat 64 0x10338
      atCall := atPc
      callSource := by decide
      callInRegion := by owned_pc
      callNotExit := by owned_pc
      sCall := childEntry
      doCall := callRun
      calleeEntryPc := BitVec.ofNat 64 0x13eb8
      atCalleeEntry := childPre.2.entry
      calleeEntryMatches := by decide
      sRet := childExit
      body
      retPc := BitVec.ofNat 64 0x13ec0
      atRet
      retInRegion := by owned_pc
      retNotExit := by owned_pc
      doReturn := by simpa [resumed, Nat.add_assoc] using returnRun
      returnPc := BitVec.ofNat 64 0x1033c
      atResume := by simpa [resumed] using returnedPc
      returnMatches := by decide
      resumeInRegion := by owned_pc }
  · simpa [resumed] using returnedPc
  · simpa [compiledMemcpyContract, Contracts.contractMemcpy, firstMemcpyCopyArgs] using bodyBound
  · simpa [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState] using destinationMemory
  · rw [DecoderEnvironment.CodeIntact]
    simpa [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState] using exitCode
  · exact tryStepControlFlowAfterRetired_retired_present _ (BitVec.ofNat 64 0x1033c) returnRetired
  · exact (returnWrites.get x18 (by decide)).trans
      ((machinePost.frame x18 (by simp [NonW])).trans childGlobals)

end BinaryFv.Zesu.MachineExecution
