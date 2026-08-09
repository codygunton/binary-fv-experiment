import BinaryFv.Zesu.MachineExecution.Level4DecodeRawTerminalStatusSteps
import BinaryFv.Zesu.MachineExecution.Level4RawNewPayloadRequestDeinitSteps
import BinaryFv.Zesu.MachineExecution.Level4DecodeRawEpilogueSteps
import BinaryFv.Zesu.MachineExecution.Level4DecodeRawParentInvariant
import BinaryFv.RiscV.Elfling.ProgramGeometry

/-! # Terminal status-route carriers for `ssz_raw.decodeRaw`

The four final status stores all reach the same emitted 16-word epilogue.  This internal carrier
records only the concrete route state needed to execute a store and its following `jal`; providers
must derive it from their real interface exits, rather than adding it to `hLevel4`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register RegisterWriteStep

inductive Level4TerminalStatusRoute where
  | s7 | a0S5 | s1 | s6
deriving DecidableEq

def Level4TerminalStatusRoute.storePc : Level4TerminalStatusRoute → Nat
  | .s7 => 0x10738 | .a0S5 => 0x11ba4 | .s1 => 0x129f0 | .s6 => 0x12ff4

def Level4TerminalStatusRoute.jumpPc : Level4TerminalStatusRoute → Nat
  | .s7 => 0x1073c | .a0S5 => 0x11ba8 | .s1 => 0x129f4 | .s6 => 0x12ff8

set_option genInjectivity false in
/-- A real parent route has reached one terminal status store.  `targetAvoidsSaved` is the exact
two-byte non-overlap needed to retain the prologue's thirteen saved words.  The companion
`targetAvoidsInput` retains the borrowed decoder input.  Providers discharge both route-local
facts from their real interface exits, rather than exposing either as a refinement assumption. -/
structure Level4TerminalStatusReady (route : Level4TerminalStatusRoute)
    (margs : DecoderMachineArgs) (origin state : State) where
  frame : Level4DecodeRawParentFrame margs origin state
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 route.storePc)
  statusBase : BitVec 64
  status : BitVec 64
  target : BitVec 64
  baseValue : match route with
    | .s7 | .a0S5 => state.regs.get? x21 = some statusBase
    | .s1 | .s6 => state.regs.get? x10 = some statusBase
  statusValue : match route with
    | .s7 => state.regs.get? x23 = some status
    | .a0S5 => state.regs.get? x10 = some status
    | .s1 => state.regs.get? x9 = some status
    | .s6 => state.regs.get? x22 = some status
  targetEq : statusBase + sign_extend (m := 64) 0x340#12 = target
  aligned : is_aligned_vaddr (virtaddr.Virtaddr target) 2 = true
  allowed : DecoderAccessRange DecoderWritableByte target 2
  targetAvoidsSaved : ∀ address, frame.stack + 0x788 ≤ address → address < frame.stack + 0x7f0 →
    address < target.toNat ∨ target.toNat + 2 ≤ address
  targetAvoidsInput : ∀ address, margs.inputBase ≤ address → address < margs.inputBase + margs.bytes.size →
    address < target.toNat ∨ target.toNat + 2 ≤ address

/-- The status-copy and epilogue PCs belong to the concrete `decodeRaw` instance, then to its
inline decoder and exported wrapper.  This is the machine transport used before and after each
terminal instruction; it is not a contract premise. -/
private theorem level4_terminal_status_phase_subset (pc : BitVec 64)
    (hpc : pc.toNat ∈ decodeRawRejectionCleanupStatusCopyEpiloguePcs) :
    RegisterWriteStep.decodeRawExecutionPcs pc := by
  have rawIn : functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw pc := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    rw [show functionInstanceExecutionRanges generatedProgram functionInstance_ssz_raw_decodeRaw =
      functionInstance_ssz_raw_decodeRaw.regions ++
        Program.extentRanges generatedProgram functionInstance_ssz_raw_decodeRaw from rfl]
    apply RegionPcs.append_iff.mpr
    left
    simp only [decodeRawRejectionCleanupStatusCopyEpiloguePcs, List.mem_filter] at hpc
    rcases hpc with ⟨hpc, _⟩
    simp only [decodeRawDirectPcs, List.mem_filter] at hpc
    rcases hpc with ⟨hpc, _⟩
    simp only [instructionPcs, List.mem_flatMap, List.mem_map, List.mem_range] at hpc
    obtain ⟨range, rangeMem, index, indexBound, pcEq⟩ := hpc
    refine ⟨range, ?_, ?_, ?_⟩
    · simpa using rangeMem
    · rw [← pcEq]
      omega
    · rw [← pcEq]
      change range.start + 4 * index < range.start + range.size
      omega
  have rawMember : functionInstance_ssz_raw_decodeRaw ∈ generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨6, by native_decide, rfl⟩
  have decodeMember :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨3, by native_decide, rfl⟩
  have rootMember : functionInstance_raw_decoder_root_zesu_decode_raw ∈
      generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨1, by native_decide, rfl⟩
  have rawCallee : functionInstance_ssz_raw_decodeRaw ∈
      calleeFunctionInstances generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 := by
    apply Array.mem_filter.mpr
    exact ⟨rawMember, by native_decide⟩
  have decodeCallee :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        calleeFunctionInstances generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw := by
    apply Array.mem_filter.mpr
    exact ⟨decodeMember, by native_decide⟩
  let geometry := programGeometry_of_check (program := generatedProgram) (by native_decide)
  have decodeIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 pc :=
    geometry.calleeWithinExecution
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      decodeMember functionInstance_ssz_raw_decodeRaw rawCallee pc rawIn
  exact geometry.calleeWithinExecution functionInstance_raw_decoder_root_zesu_decode_raw rootMember
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 decodeCallee pc
    decodeIn

/-- A writable terminal-status destination cannot be an ELF-backed instruction byte. -/
private theorem level4_terminal_status_writable_not_file {address : Nat}
    (writable : DecoderWritableByte address) :
    Artifacts.programImage.readFileByte? address = none := by
  cases read : Artifacts.programImage.readFileByte? address with
  | none => rfl
  | some byte =>
    exfalso
    have below := file_addr_lt read
    rcases writable with stack | globals | allocator | arena
    · simp only [canonicalContractParams, canonicalEnvironment, canonicalStack, range] at stack
      have stackBase : 86028 ≤ canonicalRunnerLayout.stackBase := by native_decide
      omega
    · unfold DecoderGlobalsByte at globals
      have bssBase : 86028 ≤ Elflings.GeneratedDecoderGlobals.bssBase := by native_decide
      omega
    · simp only [canonicalContractParams, canonicalEnvironment, Elflings.canonicalAllocatorState] at allocator
      rcases allocator with cursor | limit
      · have cursorBase : 86028 ≤ Elflings.canonicalHeapPosAddr := by native_decide
        omega
      · have limitBase : 86028 ≤ Elflings.canonicalHeapTopAddr := by native_decide
        omega
    · have heapBase : 86028 ≤ Elflings.canonicalHeapBase := by native_decide
      have arenaBase : Elflings.canonicalHeapBase ≤ address := by
        simpa [canonicalContractParams, canonicalEnvironment] using arena.1
      omega

/-- The two-byte status store leaves code bytes intact, so its literal `jal` can execute from the
same production image. -/
private theorem level4_terminal_status_store_code (state : State) (pc retired target status : BitVec 64)
    (allowed : DecoderAccessRange DecoderWritableByte target 2)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    Artifacts.programImage.fileBytesLoadedFaithfully
      (afterMemoryWrite state pc retired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0)).mem := by
  have executeCode : Artifacts.programImage.fileBytesLoadedFaithfully
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).mem := by
    simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code
  apply fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage
  · intro index
    exact level4_terminal_status_writable_not_file (allowed.2.2 index.val index.isLt)
  simpa [afterMemoryWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using executeCode

private theorem level4_terminal_status_store_step {route : Level4TerminalStatusRoute}
    {margs : DecoderMachineArgs} {origin state : State}
    (ready : Level4TerminalStatusReady route margs origin state)
    (machine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs state)
    (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (fromStep : Nat) :
    ∃ nextRetired, Runs (try_step fromStep false) state
      (afterMemoryWrite state (BitVec.ofNat 64 route.storePc) nextRetired ready.target.toNat
        (width := 2) (Sail.BitVec.extractLsb ready.status 15 0)) false := by
  cases route with
  | s7 =>
    exact level4_status_store_s7_step machine (Agree.refl state) retired code fromStep ready.atPc
      ready.statusBase ready.status ready.target ready.baseValue ready.statusValue ready.targetEq
      ready.aligned ready.allowed
  | a0S5 =>
    exact level4_status_store_a0_s5_step machine (Agree.refl state) retired code fromStep ready.atPc
      ready.statusBase ready.status ready.target ready.baseValue ready.statusValue ready.targetEq
      ready.aligned ready.allowed
  | s1 =>
    exact level4_status_store_s1_step machine (Agree.refl state) retired code fromStep ready.atPc
      ready.statusBase ready.status ready.target ready.baseValue ready.statusValue ready.targetEq
      ready.aligned ready.allowed
  | s6 =>
    exact level4_status_store_s6_step machine (Agree.refl state) retired code fromStep ready.atPc
      ready.statusBase ready.status ready.target ready.baseValue ready.statusValue ready.targetEq
      ready.aligned ready.allowed

private theorem level4_terminal_status_jump_step {route : Level4TerminalStatusRoute}
    {margs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (fromStep : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 route.jumpPc)) :
    ∃ nextRetired, Runs (try_step fromStep false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 route.jumpPc) (BitVec.ofNat 64 0x104f4))
        (BitVec.ofNat 64 0x104f4) nextRetired) false := by
  cases route with
  | s7 => exact level4_terminal_jump_1073c machine agree retired code fromStep atPc
  | a0S5 => exact level4_terminal_jump_11ba8 machine agree retired code fromStep atPc
  | s1 => exact level4_terminal_jump_129f4 machine agree retired code fromStep atPc
  | s6 => exact level4_terminal_jump_12ff8 machine agree retired code fromStep atPc

private theorem level4_terminal_status_next_pc (route : Level4TerminalStatusRoute) :
    Sail.BitVec.addInt (BitVec.ofNat 64 route.storePc) 4 = BitVec.ofNat 64 route.jumpPc := by
  cases route <;> native_decide

private theorem level4_terminal_status_store_saved_frame (state : State) (pc retired target status : BitVec 64)
    (stack : Nat) (avoids : ∀ address, stack + 0x788 ≤ address → address < stack + 0x7f0 →
      address < target.toNat ∨ target.toNat + 2 ≤ address)
    {ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64}
    (saved : Level4DecodeRawSavedFrame state stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) :
    Level4DecodeRawSavedFrame
      (afterMemoryWrite state pc retired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0))
      stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 := by
  rw [Level4DecodeRawSavedFrame] at saved ⊢
  rcases saved with ⟨raSaved, s0Saved, s1Saved, s2Saved, s3Saved, s4Saved, s5Saved, s6Saved,
    s7Saved, s8Saved, s9Saved, s10Saved, s11Saved⟩
  have preserve (offset : Nat) (lower : 0x788 ≤ offset) (upper : offset + 8 ≤ 0x7f0)
      (value : BitVec 64) (word : SavedWordBytes state (stack + offset) value) :
      SavedWordBytes
        (afterMemoryWrite state pc retired target.toNat
          (width := 2) (Sail.BitVec.extractLsb status 15 0))
        (stack + offset) value := by
    intro index indexBound
    have indexLt : index < 8 := by
      rw [BinaryFv.RiscV.Sep.leBytes_length] at indexBound
      exact indexBound
    have unchanged := storeRetirement_mem_writes state pc (Sail.BitVec.addInt pc 4) retired
      target.toNat (width := 2) (Sail.BitVec.extractLsb status 15 0) (stack + offset + index) (by
        rintro ⟨writeLower, writeUpper⟩
        rcases avoids (stack + offset + index) (by omega) (by omega) with before | after <;> omega)
    simpa [afterMemoryWrite] using unchanged.trans (word index indexBound)
  exact ⟨preserve 0x7e8 (by omega) (by omega) ra raSaved,
    preserve 0x7e0 (by omega) (by omega) s0 s0Saved,
    preserve 0x7d8 (by omega) (by omega) s1 s1Saved,
    preserve 0x7d0 (by omega) (by omega) s2 s2Saved,
    preserve 0x7c8 (by omega) (by omega) s3 s3Saved,
    preserve 0x7c0 (by omega) (by omega) s4 s4Saved,
    preserve 0x7b8 (by omega) (by omega) s5 s5Saved,
    preserve 0x7b0 (by omega) (by omega) s6 s6Saved,
    preserve 0x7a8 (by omega) (by omega) s7 s7Saved,
    preserve 0x7a0 (by omega) (by omega) s8 s8Saved,
    preserve 0x798 (by omega) (by omega) s9 s9Saved,
    preserve 0x790 (by omega) (by omega) s10 s10Saved,
    preserve 0x788 (by omega) (by omega) s11 s11Saved⟩

private theorem level4_terminal_status_store_input (state : State) (pc retired target status : BitVec 64)
    (inputBase : Nat) (bytes : ByteArray)
    (avoids : ∀ address, inputBase ≤ address → address < inputBase + bytes.size →
      address < target.toNat ∨ target.toNat + 2 ≤ address)
    (input : DecodedValue.MemoryBytes state inputBase bytes) :
    DecodedValue.MemoryBytes
      (afterMemoryWrite state pc retired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0)) inputBase bytes := by
  apply input.of_mem_eq
  intro index indexBound
  have unchanged := storeRetirement_mem_writes state pc (Sail.BitVec.addInt pc 4) retired
    target.toNat (width := 2) (Sail.BitVec.extractLsb status 15 0) (inputBase + index) (by
      rintro ⟨writeLower, writeUpper⟩
      rcases avoids (inputBase + index) (by omega) (by omega) with before | after <;> omega)
  simpa [afterMemoryWrite] using unchanged

private theorem level4_terminal_status_store_writes (state : State) (pc retired target status : BitVec 64) :
    WritesOnlyRegs stepBookkeeping state
      (afterMemoryWrite state pc retired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0)) := by
  simpa [afterMemoryWrite] using
    (storeRetirement_writes state pc (Sail.BitVec.addInt pc 4) retired target.toNat
      (width := 2) (Sail.BitVec.extractLsb status 15 0))

private theorem level4_terminal_status_store_retired (state : State) (pc retired target status : BitVec 64) :
    RetiredCounterPresent
      (afterMemoryWrite state pc retired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0)) := by
  simpa [afterMemoryWrite] using
    (tryStepControlFlowAfterRetired_retired_present
      (afterWriteBytes (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
        target.toNat (Sail.BitVec.extractLsb status 15 0))
      (Sail.BitVec.addInt pc 4) retired)

/-- The exact terminal store preserves every component of the parent frame once its concrete
two-byte destination avoids both the saved frame and borrowed input. -/
private theorem level4_terminal_status_store_parent_frame {margs : DecoderMachineArgs}
    {origin state : State} (frame : Level4DecodeRawParentFrame margs origin state)
    (pc retired target status : BitVec 64)
    (avoidsSaved : ∀ address, frame.stack + 0x788 ≤ address → address < frame.stack + 0x7f0 →
      address < target.toNat ∨ target.toNat + 2 ≤ address)
    (avoidsInput : ∀ address, margs.inputBase ≤ address → address < margs.inputBase + margs.bytes.size →
      address < target.toNat ∨ target.toNat + 2 ≤ address)
    (codeAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterMemoryWrite state pc retired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0)).mem) :
    frame.PreservedTo
      (afterMemoryWrite state pc retired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0)) := by
  rcases frame.invariant with ⟨entry, entryStack, entryRa, saved, stackValue, input, inputSeparated,
    stackWritable, rawFrameWritable, rawFrameInputSeparated, postStackAligned, code, machine, -⟩
  let after := afterMemoryWrite state pc retired target.toNat
    (width := 2) (Sail.BitVec.extractLsb status 15 0)
  have writes : WritesOnlyRegs stepBookkeeping state after :=
    level4_terminal_status_store_writes state pc retired target status
  have agree : Agree decoderPreserved state after :=
    writes.agree (platformPreserved_disjoint.weaken (fun _ preserved => preserved.2))
  have retiredAfter : RetiredCounterPresent after :=
    level4_terminal_status_store_retired state pc retired target status
  have epilogueSaved : Level4DecodeRawSavedFrame state frame.stack frame.savedRa frame.savedS0
      frame.savedS1 frame.savedS2 frame.savedS3 frame.savedS4 frame.savedS5 frame.savedS6 frame.savedS7
      frame.savedS8 frame.savedS9 frame.savedS10 frame.savedS11 := by
    simpa only [Level4DecodeRawSavedFrame, Level4DecodeRawPrologueSavedFrame] using saved
  have savedAfter : Level4DecodeRawPrologueSavedFrame after frame.stack frame.savedRa frame.savedS0
      frame.savedS1 frame.savedS2 frame.savedS3 frame.savedS4 frame.savedS5 frame.savedS6 frame.savedS7
      frame.savedS8 frame.savedS9 frame.savedS10 frame.savedS11 := by
    simpa only [Level4DecodeRawSavedFrame, Level4DecodeRawPrologueSavedFrame] using
      level4_terminal_status_store_saved_frame state pc retired target status frame.stack avoidsSaved
        epilogueSaved
  have inputAfter : DecodedValue.MemoryBytes after margs.inputBase margs.bytes :=
    level4_terminal_status_store_input state pc retired target status margs.inputBase margs.bytes avoidsInput
      input
  exact ⟨entry, entryStack, entryRa, savedAfter, (writes.get x2 (by decide)).trans stackValue,
    inputAfter, inputSeparated, stackWritable, rawFrameWritable, rawFrameInputSeparated, postStackAligned, codeAfter,
    machine.mono agree retiredAfter, retiredAfter⟩

/-- The literal terminal `jal` is register-only and therefore retains the complete parent frame
already preserved across its preceding status store. -/
private theorem level4_terminal_status_jump_parent_frame {margs : DecoderMachineArgs}
    {origin state : State} (frame : Level4DecodeRawParentFrame margs origin state)
    (pc target retired : BitVec 64) :
    frame.PreservedTo
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) := by
  rcases frame.invariant with ⟨entry, entryStack, entryRa, saved, stackValue, input, inputSeparated,
    stackWritable, rawFrameWritable, rawFrameInputSeparated, postStackAligned, code, machine, -⟩
  let after := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired
  have writes : WritesOnlyRegs stepBookkeeping state after := jumpRetirement_writes state pc target retired
  have memory : after.mem = state.mem := jumpRetirement_mem state pc target retired
  have agree : Agree decoderPreserved state after :=
    writes.agree (platformPreserved_disjoint.weaken (fun _ preserved => preserved.2))
  have retiredAfter : RetiredCounterPresent after := jumpRetirement_retired_present state pc target retired
  have epilogueSaved : Level4DecodeRawSavedFrame state frame.stack frame.savedRa frame.savedS0
      frame.savedS1 frame.savedS2 frame.savedS3 frame.savedS4 frame.savedS5 frame.savedS6 frame.savedS7
      frame.savedS8 frame.savedS9 frame.savedS10 frame.savedS11 := by
    simpa only [Level4DecodeRawSavedFrame, Level4DecodeRawPrologueSavedFrame] using saved
  have savedAfter : Level4DecodeRawPrologueSavedFrame after frame.stack frame.savedRa frame.savedS0
      frame.savedS1 frame.savedS2 frame.savedS3 frame.savedS4 frame.savedS5 frame.savedS6 frame.savedS7
      frame.savedS8 frame.savedS9 frame.savedS10 frame.savedS11 := by
    simpa only [Level4DecodeRawSavedFrame, Level4DecodeRawPrologueSavedFrame] using
      epilogueSaved.of_mem_eq memory
  exact ⟨entry, entryStack, entryRa, savedAfter,
    (writes.get x2 (by decide)).trans stackValue,
    input.of_mem_eq (fun index bound => by rw [memory]), inputSeparated, stackWritable, rawFrameWritable,
    rawFrameInputSeparated, postStackAligned,
    (by rw [memory]; exact code), machine.mono agree retiredAfter, retiredAfter⟩

private theorem level4_terminal_status_epilogue_subset (pc : BitVec 64)
    (hpc : Level4DecodeRawEpiloguePcs pc) :
    pc.toNat ∈ decodeRawRejectionCleanupStatusCopyEpiloguePcs := by
  have checked := List.all_eq_true.mp
    level4DecodeRawEpiloguePcs_subset_rejectionCleanupStatusCopyEpilogue pc.toNat hpc
  simpa using checked

private theorem level4_terminal_status_save_area_readable {margs : DecoderMachineArgs}
    (entry : Level4DecodeRawEntryProloguePre margs origin) (stack : Nat)
    (stackEq : entry.stack = stack) :
    DecoderAccessRange (DecoderReadableByte margs) (BitVec.ofNat 64 (stack + 0x788)) 104 := by
  have stackFits : stack + 0x7f0 < 2 ^ 64 := by
    rw [← stackEq]
    exact entry.stackFits
  have readBaseFits : stack + 0x788 < 2 ^ 64 := by omega
  refine ⟨by decide, ?_, ?_⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt readBaseFits]
    omega
  · intro index indexBound
    refine Or.inr (Or.inr (Or.inl ?_))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt readBaseFits, ← stackEq]
    exact entry.saveAreaWritable index indexBound

/-- A terminal status route consists of its exact store and literal jump followed by the existing
16-step epilogue.  It retains the source parent frame, its full preservation at the epilogue
handoff, and the combined 18-step execution trace. -/
structure Level4TerminalStatusRouteResult (route : Level4TerminalStatusRoute)
    {margs : DecoderMachineArgs} {origin state : State}
    (ready : Level4TerminalStatusReady route margs origin state) (fromStep : Nat) (handoffState : State)
    (handoff : Level4RejectionCleanupStatusEpilogueHandoff margs handoffState handoffState)
    (after : State) : Prop where
  framePreserved : ready.frame.PreservedTo handoffState
  storeJumpTrace : Trace fromStep 2 state handoffState
  epilogue : Level4DecodeRawEpilogueResult (fromStep + 2) handoffState after
    (level4DecodeRawEpiloguePre_of_rejectionCleanupStatusHandoff handoff)
  trace : Trace fromStep 18 state after

/-- Execute any concrete terminal status route into the shared raw-decoder epilogue.  The only
route-local input is `Level4TerminalStatusReady`; its two non-overlap facts are consumed here to
retain the complete parent frame, rather than becoming a Level 4 contract assumption. -/
theorem level4_terminal_status_route_to_epilogue {route : Level4TerminalStatusRoute}
    {margs : DecoderMachineArgs} {origin state : State}
    (ready : Level4TerminalStatusReady route margs origin state) (fromStep : Nat) :
    ∃ handoffState handoff after,
      Level4TerminalStatusRouteResult route ready fromStep handoffState handoff after := by
  rcases ready.frame.invariant with
    ⟨entry0, -, -, -, -, -, -, -, -, -, -, code, outerMachine, retiredPresent⟩
  let phaseMachine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs state :=
    DecoderMachinePre.restrict (fun pc hpc => level4_terminal_status_phase_subset pc hpc) outerMachine
  obtain ⟨storeRetired, storeRun⟩ :=
    level4_terminal_status_store_step ready phaseMachine retiredPresent code fromStep
  let afterStore := afterMemoryWrite state (BitVec.ofNat 64 route.storePc) storeRetired ready.target.toNat
    (width := 2) (Sail.BitVec.extractLsb ready.status 15 0)
  have storeTrace : Trace fromStep 1 state afterStore :=
    Trace.one fromStep state afterStore (by simpa [afterStore] using storeRun)
  have storeCode : Artifacts.programImage.fileBytesLoadedFaithfully afterStore.mem :=
    level4_terminal_status_store_code state (BitVec.ofNat 64 route.storePc) storeRetired ready.target
      ready.status ready.allowed code
  have storeWrites : WritesOnlyRegs stepBookkeeping state afterStore :=
    level4_terminal_status_store_writes state (BitVec.ofNat 64 route.storePc) storeRetired ready.target
      ready.status
  have storeAgree : Agree decoderPreserved state afterStore :=
    storeWrites.agree (platformPreserved_disjoint.weaken (fun _ preserved => preserved.2))
  have storeRetiredPresent : RetiredCounterPresent afterStore :=
    level4_terminal_status_store_retired state (BitVec.ofNat 64 route.storePc) storeRetired ready.target
      ready.status
  have storeAtJump : afterStore.regs.get? PC = some (BitVec.ofNat 64 route.jumpPc) := by
    have pcAfter := tryStepControlFlowAfterRetired_pc
      (afterWriteBytes
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 route.storePc))
        ready.target.toNat (width := 2) (Sail.BitVec.extractLsb ready.status 15 0))
      (Sail.BitVec.addInt (BitVec.ofNat 64 route.storePc) 4) storeRetired
    simpa [afterStore, afterMemoryWrite, level4_terminal_status_next_pc] using pcAfter
  have storeParent : ready.frame.PreservedTo afterStore :=
    level4_terminal_status_store_parent_frame ready.frame (BitVec.ofNat 64 route.storePc) storeRetired
      ready.target ready.status ready.targetAvoidsSaved ready.targetAvoidsInput storeCode
  let storeFrame := ready.frame.toState storeParent
  let storeMachine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs afterStore :=
    phaseMachine.mono storeAgree storeRetiredPresent
  obtain ⟨jumpRetired, jumpRun⟩ := level4_terminal_status_jump_step storeMachine (Agree.refl afterStore)
    storeRetiredPresent storeCode (fromStep + 1) storeAtJump
  let handoffState := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement afterStore)
      (BitVec.ofNat 64 route.jumpPc) (BitVec.ofNat 64 0x104f4))
    (BitVec.ofNat 64 0x104f4) jumpRetired
  have jumpTrace : Trace (fromStep + 1) 1 afterStore handoffState :=
    Trace.one (fromStep + 1) afterStore handoffState (by simpa [handoffState] using jumpRun)
  have storeJumpTrace : Trace fromStep 2 state handoffState := by
    simpa using Trace.append storeTrace jumpTrace
  have handoffParentFromStore : storeFrame.PreservedTo handoffState :=
    level4_terminal_status_jump_parent_frame storeFrame (BitVec.ofNat 64 route.jumpPc)
      (BitVec.ofNat 64 0x104f4) jumpRetired
  have handoffParent : ready.frame.PreservedTo handoffState := by
    simpa [storeFrame] using handoffParentFromStore
  let handoffFrame := ready.frame.toState handoffParent
  rcases handoffFrame.invariant with ⟨entry, entryStack, entryRa, saved, stackValue, -, -, -, -, -, -, handoffCode,
    handoffOuterMachine, handoffRetired⟩
  have handoffPc : handoffState.regs.get? PC = some (BitVec.ofNat 64 0x104f4) :=
    jumpRetirement_pc afterStore (BitVec.ofNat 64 route.jumpPc) (BitVec.ofNat 64 0x104f4) jumpRetired
  let epilogueMachine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs handoffState :=
    DecoderMachinePre.restrict
      (fun pc hpc => level4_terminal_status_phase_subset pc (level4_terminal_status_epilogue_subset pc hpc))
      handoffOuterMachine
  have epilogueSaved : Level4DecodeRawSavedFrame handoffState handoffFrame.stack handoffFrame.savedRa
      handoffFrame.savedS0 handoffFrame.savedS1 handoffFrame.savedS2 handoffFrame.savedS3
      handoffFrame.savedS4 handoffFrame.savedS5 handoffFrame.savedS6 handoffFrame.savedS7
      handoffFrame.savedS8 handoffFrame.savedS9 handoffFrame.savedS10 handoffFrame.savedS11 := by
    simpa only [Level4DecodeRawSavedFrame, Level4DecodeRawPrologueSavedFrame] using saved
  let handoff : Level4RejectionCleanupStatusEpilogueHandoff margs handoffState handoffState := {
    phase := decodeRawCfgPhaseInterface .rejectionCleanupStatusCopyEpilogue
    phaseIsRejectionCleanupStatusCopyEpilogue := rfl
    machine := epilogueMachine
    agree := Agree.refl handoffState
    retired := handoffRetired
    code := handoffCode
    atPc := handoffPc
    stackBase := handoffFrame.stack
    stackBefore := BitVec.ofNat 64 entry.postStack
    stackValue := stackValue
    stackRestore := by
      rw [show sign_extend (m := 64) 0x690#12 = BitVec.ofNat 64 0x690 by decide,
        ← BitVec.ofNat_add, ← entryStack]
      exact congrArg (BitVec.ofNat 64) entry.postStackEq.symm
    stackFits := by
      rw [← entryStack]
      exact entry.stackFits
    saveAreaReadable := level4_terminal_status_save_area_readable entry handoffFrame.stack entryStack
    slotAligned := by
      intro offset lower upper aligned
      rw [← entryStack]
      exact entry.slotAligned offset lower upper aligned
    ra := handoffFrame.savedRa
    s0 := handoffFrame.savedS0
    s1 := handoffFrame.savedS1
    s2 := handoffFrame.savedS2
    s3 := handoffFrame.savedS3
    s4 := handoffFrame.savedS4
    s5 := handoffFrame.savedS5
    s6 := handoffFrame.savedS6
    s7 := handoffFrame.savedS7
    s8 := handoffFrame.savedS8
    s9 := handoffFrame.savedS9
    s10 := handoffFrame.savedS10
    s11 := handoffFrame.savedS11
    saved := epilogueSaved
    returnTarget := by
      rw [← entryRa]
      exact entry.return_target
    returnBit1 := by
      rw [← entryRa]
      exact entry.return_bit_one_zero }
  obtain ⟨after, epilogue⟩ :=
    level4_decode_raw_epilogue_of_rejectionCleanupStatusHandoff handoff (fromStep + 2)
  refine ⟨handoffState, handoff, after, handoffParent, storeJumpTrace, epilogue, ?_⟩
  simpa only [Nat.add_assoc] using Trace.append storeJumpTrace epilogue.trace

end BinaryFv.Zesu.MachineExecution
