import BinaryFv.Zesu.MachineExecution.DecodeInlineProof
import BinaryFv.Zesu.MachineExecution.Level2WrapperProof
import BinaryFv.RiscV.Elfling.ProgramGeometry

/-!
# The wrapper prefix that consumes the Level 3 first-phase decode theorem

`Level2WrapperProof` executes every wrapper-owned instruction without depending on the proved
inlined-`decode` machine execution. Exactly one of its results consumes
`decodeInline_first_level3_save_area`, so that result lives here instead: it keeps the wrapper
execution module — the largest single elaboration segment in the build — off `DecodeInlineProof`'s
import closure, so the two elaborate concurrently rather than in series.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.ProgramImage BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.RiscV.Sep
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep GeneratedWordStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The selected inlined `decode` region is contained in its enclosing wrapper's generated
execution region. This is checked from the generated call relation, not handwritten address bounds. -/
private theorem decodeInline_executionPcs_subset_wrapper (pc : BitVec 64)
    (inside : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 pc) :
    functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw pc := by
  have parentMember : functionInstance_raw_decoder_root_zesu_decode_raw ∈
      generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨1, by native_decide, rfl⟩
  have childMember :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨3, by native_decide, rfl⟩
  have childIsCallee :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        BinaryFv.RiscV.Elfling.calleeFunctionInstances generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw := by
    apply Array.mem_filter.mpr
    exact ⟨childMember, by native_decide⟩
  exact (programGeometry_of_check (program := generatedProgram) (by native_decide)).calleeWithinExecution
    functionInstance_raw_decoder_root_zesu_decode_raw parentMember
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 childIsCallee
    pc inside

/-- A first `decodeRaw` call may write its temporary stack result, allocation interval, allocator
state, and the canonical machine stack.  None of those four permissions contains a decoder-global
byte.  The concrete temporary result occupies the wrapper stack objects; the generated BSS and
allocator bounds discharge the other three alternatives. -/
private theorem firstRawOwnedRegion_outside_decoderGlobals (args : DecodeInlineArgs)
    {entry : State} (machine : ZesuDecodeRawMachinePre
      { inputBase := args.inputBase, bytes := args.bytes } args.stackBase entry)
    {cursorBefore cursorAfter address : Nat}
    (cursorBound : cursorAfter ≤ Elflings.canonicalHeapLimit)
    (global : DecoderGlobalsByte address) :
    ¬ canonicalContractParams.env.ownedRegion args.firstRawArgs.resultBase
      canonicalContractParams.env.record.entryResult cursorBefore cursorAfter address := by
  have globalBelow : address < Entrypoints.ZesuDecodeRaw.globalsCeiling := by
    simpa [DecoderGlobalsByte, Entrypoints.ZesuDecodeRaw.globalsCeiling] using global.2
  intro owned
  change
    (Contracts.allocatedRegion args.firstRawArgs.resultBase
      canonicalContractParams.env.record.entryResult cursorBefore cursorAfter address ∨
      (canonicalContractParams.env.allocatorState address ∨ canonicalContractParams.env.stack address))
      at owned
  rcases owned with (record | allocation) | allocator | stack
  · have recordIndex : address - args.firstRawArgs.resultBase <
      canonicalContractParams.env.record.entryResult := by
      dsimp [Contracts.range, DecodeInlineArgs.firstRawArgs,
        DecodeInlineArgs.firstTemporaryResultBase] at record
      change address - (args.stackBase + 0x360) < canonicalContractParams.env.record.entryResult
      omega
    have resultBase : args.firstRawArgs.resultBase = args.stackBase + 0x360 := rfl
    have recordAddress : args.stackBase + (0x360 + (address - args.firstRawArgs.resultBase)) = address := by
      rw [resultBase]
      dsimp [Contracts.range, DecodeInlineArgs.firstRawArgs,
        DecodeInlineArgs.firstTemporaryResultBase] at record
      omega
    have recordInStack : canonicalContractParams.env.stack address := by
      rw [← recordAddress]
      exact machine.stackObjectsReadable _ (by
        have := recordIndex
        omega)
    exact (canonicalStack_disjoint_from_globals address globalBelow)
      (by simpa [canonicalContractParams, canonicalEnvironment] using recordInStack)
  · exact decodeRawAllocationInterval_outside_decoderGlobals cursorBound global allocation
  · have heapTopBelowGlobals : Elflings.canonicalHeapTopAddr + 8 ≤
      Elflings.GeneratedDecoderGlobals.bssBase := by native_decide
    have heapPosBelowGlobals : Elflings.canonicalHeapPosAddr + 8 ≤
      Elflings.GeneratedDecoderGlobals.bssBase := by
      native_decide
    change Elflings.canonicalAllocatorState address at allocator
    rcases global with ⟨globalBase, _⟩
    rcases allocator with allocator | allocator <;> omega
  · exact (canonicalStack_disjoint_from_globals address globalBelow)
      (by simpa [canonicalContractParams, canonicalEnvironment] using stack)

/-- The wrapper's concrete setup reaches the inline `decode` boundary with every value required by
the emitted `decodeRaw` call. The `s3`–`s11` equations come from their dedicated frame agreement;
`sp`, `s0`, `s1`, and `s2` are the wrapper values materialized by the setup itself. -/
private theorem decodeRawEntryFrame_of_wrapper {args : ZesuDecodeRawArgs} {stackBase : Nat}
    {entry state : State} (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackBase))
    (input : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase))
    (length : state.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size))
    (globals : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (calleeSaved : Agree decodeRawCalleeSaved entry state) :
    DecodeRawEntryFrame state := by
  obtain ⟨savedS3, savedS3AtEntry⟩ := machine.savedS3AtEntry
  obtain ⟨savedS4, savedS4AtEntry⟩ := machine.savedS4AtEntry
  obtain ⟨savedS5, savedS5AtEntry⟩ := machine.savedS5AtEntry
  obtain ⟨savedS6, savedS6AtEntry⟩ := machine.savedS6AtEntry
  obtain ⟨savedS7, savedS7AtEntry⟩ := machine.savedS7AtEntry
  obtain ⟨savedS8, savedS8AtEntry⟩ := machine.savedS8AtEntry
  obtain ⟨savedS9, savedS9AtEntry⟩ := machine.savedS9AtEntry
  obtain ⟨savedS10, savedS10AtEntry⟩ := machine.savedS10AtEntry
  obtain ⟨savedS11, savedS11AtEntry⟩ := machine.savedS11AtEntry
  refine ⟨BitVec.ofNat 64 stackBase, BitVec.ofNat 64 args.inputBase,
    BitVec.ofNat 64 args.bytes.size, BitVec.ofNat 64 0x4215020, savedS3, savedS4, savedS5,
    savedS6, savedS7, savedS8, savedS9, savedS10, savedS11, stack,
    input, length, globals, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (calleeSaved x19 (by simp [decodeRawCalleeSaved])).trans savedS3AtEntry
  · exact (calleeSaved x20 (by simp [decodeRawCalleeSaved])).trans savedS4AtEntry
  · exact (calleeSaved x21 (by simp [decodeRawCalleeSaved])).trans savedS5AtEntry
  · exact (calleeSaved x22 (by simp [decodeRawCalleeSaved])).trans savedS6AtEntry
  · exact (calleeSaved x23 (by simp [decodeRawCalleeSaved])).trans savedS7AtEntry
  · exact (calleeSaved x24 (by simp [decodeRawCalleeSaved])).trans savedS8AtEntry
  · exact (calleeSaved x25 (by simp [decodeRawCalleeSaved])).trans savedS9AtEntry
  · exact (calleeSaved x26 (by simp [decodeRawCalleeSaved])).trans savedS10AtEntry
  · exact (calleeSaved x27 (by simp [decodeRawCalleeSaved])).trans savedS11AtEntry

/-- The nineteen-step wrapper prefix establishes the complete first-phase `decode` entry and then
visibly consumes the Level 3 conditional theorem. It retains that theorem's bound, scoped trace,
and semantic postcondition alongside the Level 2 child summary, so the wrapper proof can dispatch
the actual result without recovering facts from an opaque existential. -/
theorem wrapper_reaches_decode_first_contract
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    (fromStep : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ atDecode, Trace fromStep 19 entry atDecode ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 19 entry atDecode ∧
      ∃ decodeArgs : DecodeInlineArgs,
        decodeArgs =
            { phase := .first
              stackBase := stackBase
              inputBase := args.inputBase
              bytes := args.bytes } ∧
          DecodeInlinePre decodeArgs atDecode ∧
          Agree decoderPreserved entry atDecode ∧
          atDecode.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted = some (1#8) ∧
          atDecode.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
            Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) =
            entry.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
              Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) ∧
          ∃ used after,
            Level2ChildSummary
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
              (fromStep + 19) used atDecode after ∧
            level3DecodeChildSummary
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
              (fromStep + 19) used atDecode after ∧
            used ≤ decodeInlineStepBound decodeArgs ∧
            (∀ value, meaningDecodeRaw decodeArgs.bytes = .ok value →
              used ≤ 16384 + 512 * decodeArgs.bytes.size + 13) ∧
            ScopedTrace
              (functionInstanceExecutionPcs generatedProgram
                functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
              (DecodeInlineExit decodeArgs) Level3ChildSummary
              (fromStep + 19) used atDecode after ∧
            FunctionTrace
              (functionInstanceExecutionPcs generatedProgram
                functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
              (DecodeInlineExit decodeArgs) (fromStep + 19) used atDecode after ∧
            DecodeInlinePost decodeArgs atDecode after ∧
            DecodeInlineMachinePost atDecode after ∧
            DecodeInlineOutgoingFrame decodeArgs after ∧
            DecodeInlineCallerSaveArea decodeArgs atDecode after ∧
            DecodeInlineFirstAllocationFrame decodeArgs atDecode after ∧
            DecodeInlineFirstErrorInputFrame decodeArgs after ∧
            DecoderGlobalsBoundaryFrame atDecode after ∧
            ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
              entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
              WrapperSavedRegisterFrame stackBase link s0 s1 s2 atDecode := by
  obtain ⟨atDecode, trace, confined, pc, stack, savedInput, length, globals, attempted, stored, inputMemory,
    _, agree, calleeSaved, retired, code, savedFrame⟩ :=
    wrapper_through_allocator_setup allocator fromStep args stackBase entry source machine
  let decodeArgs : DecodeInlineArgs :=
    { phase := .first
      stackBase := stackBase
      inputBase := args.inputBase
      bytes := args.bytes }
  have parentMachine := machine.machine.mono agree retired
  have decodeMachine : DecodeInlineMachinePre decodeArgs atDecode := by
    simpa [DecodeInlineArgs.machineArgs, decodeArgs, zesuDecodeRawMachineArgs] using
      parentMachine.restrict decodeInline_executionPcs_subset_wrapper
  let pre : DecodeInlinePre decodeArgs atDecode :=
    { atEntry := by simpa [decodeArgs, DecodeInlineArgs.entryPc] using pc
      stackValue := by simpa [decodeArgs] using stack
      inputValue := by simpa [decodeArgs] using savedInput
      lengthValue := by simpa [decodeArgs] using length
      globalsValue := globals
      rawCallFrame := by
        simpa [DecodeInlineRawCallFrame, DecodeInlineArgs.phase] using
          decodeRawEntryFrame_of_wrapper machine stack savedInput length globals calleeSaved
      inputMemory := by simpa [decodeArgs] using inputMemory
      code := code
      inputFits := machine.inputFits
      rootInputBound := machine.inputBound
      stackAligned := machine.stackAligned
      stackObjectsFit := machine.stackObjectsFit
      stackObjectsReadable := machine.stackObjectsReadable
      inputAvoidsCanonicalStack := machine.inputAvoidsCanonicalStack
      stackFrameWritable := machine.stackFrameWritable
      rawFrameWritable := machine.rawFrameWritable
      rawPrologueFrameWritable := machine.rawPrologueFrameWritable
      decodeRawMachine := by
        simpa [decodeArgs, DecodeInlineArgs.machineArgs, zesuDecodeRawMachineArgs] using parentMachine
      machine := decodeMachine
      retryReason := by simp [decodeArgs]
      propagateReason := by
        intro error phase
        simp [decodeArgs] at phase }
  obtain ⟨used, after, bound, childTrace, flat, post, machinePost, outgoing, saveArea, _, firstError,
    firstAllocation, firstSuccessProvenance, _, firstSuccessBound, _, _⟩ :=
    decode decodeArgs (fromStep + 19) atDecode pre
  have firstPhase : decodeArgs.phase = .first := by simp [decodeArgs]
  have firstPost : Contracts.postEntry canonicalContractParams.env decodeArgs.firstRawArgs
      canonicalContractParams.repStatelessInput (meaningDecodeRaw decodeArgs.bytes) atDecode after := by
    have details := post
    simp only [DecodeInlinePost, firstPhase, DecodeInlineFirstPost] at details
    exact details.1
  have firstWrites := firstPost.2.2.1
  have globalsFrame : DecoderGlobalsBoundaryFrame atDecode after := by
    obtain allocation := firstAllocation firstPhase
    have preservesGlobal (address : Nat) (global : DecoderGlobalsByte address) :
        after.mem.get? address = atDecode.mem.get? address := by
      apply writesOnlyWithinOwnAllocation_preserves_byte firstWrites
      intro cursorBefore cursorAfter beforeCursor afterCursor
      rcases allocation with ⟨allocationBefore, allocationAfter, beforeAllocation, afterAllocation,
        _arenaBase, _cursorOrder, cursorBound⟩
      have beforeEq : cursorBefore = allocationBefore :=
        Option.some.inj (beforeCursor.symm.trans beforeAllocation)
      have afterEq : cursorAfter = allocationAfter :=
        Option.some.inj (afterCursor.symm.trans afterAllocation)
      subst cursorBefore
      subst cursorAfter
      exact firstRawOwnedRegion_outside_decoderGlobals decodeArgs (by simpa [decodeArgs] using machine)
        cursorBound global
    constructor
    · apply preservesGlobal
      unfold DecoderGlobalsByte
      simp only [Elflings.canonicalDecoderGlobalsLayout, Elflings.decoderGlobalAddr?,
        Elflings.GeneratedDecoderGlobals.bssBase, Elflings.GeneratedDecoderGlobals.bssSize]
      native_decide
    · apply preservesGlobal
      unfold DecoderGlobalsByte
      simp only [Elflings.canonicalDecoderGlobalsLayout, Elflings.canonicalStoredResultObjectLayout,
        Elflings.decoderGlobalAddr?, Elflings.GeneratedDecoderGlobals.bssBase,
        Elflings.GeneratedDecoderGlobals.bssSize, Artifacts.storedResultSize,
        Artifacts.storedResultTagOffset, Artifacts.storedResultPayloadOffset]
      native_decide
  have level3 : level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      (fromStep + 19) used atDecode after :=
    ⟨rfl, decodeArgs, pre, bound, childTrace, flat, post, machinePost, outgoing⟩
  exact ⟨atDecode, trace, confined, decodeArgs, rfl, pre, agree, attempted, stored, used, after, .decode level3,
    level3, bound, firstSuccessBound firstPhase, childTrace, flat, post, machinePost, outgoing, saveArea,
    firstAllocation, firstError, globalsFrame, savedFrame⟩

/-- The first `invalidSsz` boundary retains the live input registers required by the wrapper's
retry entry.  This consumes the same selected Level 3 `decode` child as the generic first-entry
edge, but preserves the two concrete facts established by its error arm. -/
theorem wrapper_reaches_decode_first_invalid_contract
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    (fromStep : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (invalid : meaningDecodeRaw args.bytes = .error .invalidSsz) :
    ∃ atDecode, Trace fromStep 19 entry atDecode ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 19 entry atDecode ∧
      ∃ decodeArgs : DecodeInlineArgs,
        decodeArgs =
            { phase := .first, stackBase := stackBase, inputBase := args.inputBase,
              bytes := args.bytes } ∧
          DecodeInlinePre decodeArgs atDecode ∧
          Agree decoderPreserved entry atDecode ∧
          atDecode.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted = some (1#8) ∧
          ∃ used after,
            Level2ChildSummary
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
              (fromStep + 19) used atDecode after ∧
            level3DecodeChildSummary
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
              (fromStep + 19) used atDecode after ∧
            used ≤ decodeInlineStepBound decodeArgs ∧
            used ≤ 16392 + 512 * decodeArgs.bytes.size ∧
            ScopedTrace decodeInlineOwnPcs (DecodeInlineExit decodeArgs) Level3ChildSummary
              (fromStep + 19) used atDecode after ∧
            FunctionTrace
              (functionInstanceExecutionPcs generatedProgram
                functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
              (DecodeInlineExit decodeArgs) (fromStep + 19) used atDecode after ∧
            DecodeInlinePost decodeArgs atDecode after ∧
            DecodeInlineMachinePost atDecode after ∧
            DecodeInlineOutgoingFrame decodeArgs after ∧
            DecodeInlineCallerSaveArea decodeArgs atDecode after ∧
            after.regs.get? x8 = some (BitVec.ofNat 64 decodeArgs.inputBase) ∧
            after.regs.get? x9 = some (BitVec.ofNat 64 decodeArgs.bytes.size) ∧
            after.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted = some (1#8) ∧
            after.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
              Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) =
              entry.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
                Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) ∧
            ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
              entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
              WrapperSavedRegisterFrame stackBase link s0 s1 s2 atDecode := by
  obtain ⟨atDecode, trace, confined, pc, stack, savedInput, length, globals, attempted, storedAtDecode,
    inputMemory, _, agree, calleeSaved, retired, code, savedFrame⟩ :=
    wrapper_through_allocator_setup allocator fromStep args stackBase entry source machine
  let decodeArgs : DecodeInlineArgs :=
    { phase := .first, stackBase := stackBase, inputBase := args.inputBase, bytes := args.bytes }
  have parentMachine := machine.machine.mono agree retired
  have decodeMachine : DecodeInlineMachinePre decodeArgs atDecode := by
    simpa [DecodeInlineArgs.machineArgs, decodeArgs, zesuDecodeRawMachineArgs] using
      parentMachine.restrict decodeInline_executionPcs_subset_wrapper
  let pre : DecodeInlinePre decodeArgs atDecode :=
    { atEntry := by simpa [decodeArgs, DecodeInlineArgs.entryPc] using pc
      stackValue := by simpa [decodeArgs] using stack
      inputValue := by simpa [decodeArgs] using savedInput
      lengthValue := by simpa [decodeArgs] using length
      globalsValue := globals
      rawCallFrame := by
        simpa [DecodeInlineRawCallFrame, DecodeInlineArgs.phase] using
          decodeRawEntryFrame_of_wrapper machine stack savedInput length globals calleeSaved
      inputMemory := by simpa [decodeArgs] using inputMemory
      code := code
      inputFits := machine.inputFits
      rootInputBound := machine.inputBound
      stackAligned := machine.stackAligned
      stackObjectsFit := machine.stackObjectsFit
      stackObjectsReadable := machine.stackObjectsReadable
      inputAvoidsCanonicalStack := machine.inputAvoidsCanonicalStack
      stackFrameWritable := machine.stackFrameWritable
      rawFrameWritable := machine.rawFrameWritable
      rawPrologueFrameWritable := machine.rawPrologueFrameWritable
      decodeRawMachine := by
        simpa [decodeArgs, DecodeInlineArgs.machineArgs, zesuDecodeRawMachineArgs] using parentMachine
      machine := decodeMachine
      retryReason := by simp [decodeArgs]
      propagateReason := by
        intro error phase
        simp [decodeArgs] at phase }
  obtain ⟨used, after, bound, childTrace, flat, post, machinePost, outgoing, saveArea,
    firstFrames⟩ :=
    decode decodeArgs (fromStep + 19) atDecode pre
  obtain ⟨inputFrame, _, firstAllocation, _, _, _, firstInvalidBound, _⟩ := firstFrames
  obtain ⟨inputValue, lengthValue⟩ := inputFrame (by simp [decodeArgs])
    (by simpa [decodeArgs] using invalid)
  have firstPhase : decodeArgs.phase = .first := by simp [decodeArgs]
  have firstPost : Contracts.postEntry canonicalContractParams.env decodeArgs.firstRawArgs
      canonicalContractParams.repStatelessInput (meaningDecodeRaw decodeArgs.bytes) atDecode after := by
    have details := post
    simp only [DecodeInlinePost, firstPhase, DecodeInlineFirstPost] at details
    exact details.1
  have allocation : DecodeRawAllocationWithinCanonicalArena atDecode after :=
    firstAllocation firstPhase
  have firstWrites := firstPost.2.2.1
  have preservesGlobal (address : Nat) (global : DecoderGlobalsByte address) :
      after.mem.get? address = atDecode.mem.get? address := by
    apply writesOnlyWithinOwnAllocation_preserves_byte firstWrites
    intro cursorBefore cursorAfter beforeCursor afterCursor
    rcases allocation with ⟨allocationBefore, allocationAfter, beforeAllocation, afterAllocation,
      _arenaBase, _cursorOrder, cursorBound⟩
    have beforeEq : cursorBefore = allocationBefore :=
      Option.some.inj (beforeCursor.symm.trans beforeAllocation)
    have afterEq : cursorAfter = allocationAfter :=
      Option.some.inj (afterCursor.symm.trans afterAllocation)
    subst cursorBefore
    subst cursorAfter
    exact firstRawOwnedRegion_outside_decoderGlobals decodeArgs (by simpa [decodeArgs] using machine)
      cursorBound global
  have attemptedGlobal : DecoderGlobalsByte Elflings.canonicalDecoderGlobalsLayout.attempted := by
    unfold DecoderGlobalsByte
    simp only [Elflings.canonicalDecoderGlobalsLayout, Elflings.decoderGlobalAddr?,
      Elflings.GeneratedDecoderGlobals.bssBase, Elflings.GeneratedDecoderGlobals.bssSize]
    native_decide
  have storedGlobal : DecoderGlobalsByte (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) := by
    unfold DecoderGlobalsByte
    simp only [Elflings.canonicalDecoderGlobalsLayout, Elflings.canonicalStoredResultObjectLayout,
      Elflings.decoderGlobalAddr?, Elflings.GeneratedDecoderGlobals.bssBase,
      Elflings.GeneratedDecoderGlobals.bssSize, Artifacts.storedResultSize,
      Artifacts.storedResultTagOffset, Artifacts.storedResultPayloadOffset]
    native_decide
  have attemptedAfter : after.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted = some (1#8) :=
    (preservesGlobal _ attemptedGlobal).trans attempted
  have storedAfter : after.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) =
      entry.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) :=
    (preservesGlobal _ storedGlobal).trans storedAtDecode
  have level3 : level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      (fromStep + 19) used atDecode after :=
    ⟨rfl, decodeArgs, pre, bound, childTrace, flat, post, machinePost, outgoing⟩
  exact ⟨atDecode, trace, confined, decodeArgs, rfl, pre, agree, attempted, used, after, .decode level3,
    level3, bound, firstInvalidBound firstPhase (by simpa [decodeArgs] using invalid), childTrace, flat, post, machinePost, outgoing, saveArea, inputValue, lengthValue,
    attemptedAfter, storedAfter, savedFrame⟩

end BinaryFv.Zesu.MachineExecution
