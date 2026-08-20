import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Elfling.Seg
import BinaryFv.ProofProgress.OwnedPc

/-!
# Exact Level 3 execution-request slice steps

The five inlined source calls share one stack-access context. This module starts with the second
call at `0x130b0`, whose six instructions select request type one or reject invalid bounds.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

def checkedSliceFrame (stackPointer : Nat) : Region :=
  byteRange stackPointer 0x510

structure CheckedSliceMachineAccess (stackPointer : Nat) (state : State) : Prop where
  configured : ConfiguredMachinePre EndpointMachinePc state
  stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer)
  stackFits : stackPointer + 0x510 ≤ 2 ^ 64
  stackAligned : stackPointer % 16 = 0
  loadPma : ∀ offset, offset + 8 ≤ 0x510 →
    LoadPmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 8
  storePma : ∀ offset, offset + 8 ≤ 0x510 →
    StorePmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 8
  loadNoMMIO : ∀ offset, offset + 8 ≤ 0x510 →
    LoadMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 8
  storeNoMMIO : ∀ offset, offset + 8 ≤ 0x510 →
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 8
  frameNotCode : ∀ address, checkedSliceFrame stackPointer address →
    Artifacts.programImage.readFileByte? address = none

def checkedSlice351cOwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x130b0, 0x130b4, 0x130b8, 0x130bc, 0x130c0, 0x130c4] pc

def checkedSlice351cExitPc (pc : BitVec 64) : Prop :=
  pcInList [0x130c8, 0x13db0] pc

def checkedSlice351cWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x12 ∨ register = x13

def checkedSlice351cMemory (stackPointer : Nat) : Region :=
  byteRange (stackPointer + 0x198) 8

private theorem instructionPreserved_disjoint_checkedSlice351cWrites :
    RegSet.Disjoint instructionPreserved checkedSlice351cWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem platformPreserved_disjoint_checkedSlice351cWrites :
    RegSet.Disjoint platformPreserved checkedSlice351cWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved bookkeeping
  all_goals simp [platformPreserved] at preserved

private theorem checkedSlice351cMemory_in_frame {stackPointer address : Nat}
    (inside : checkedSlice351cMemory stackPointer address) :
    checkedSliceFrame stackPointer address := by
  change stackPointer + 0x198 ≤ address ∧ address < stackPointer + 0x198 + 8 at inside
  change stackPointer ≤ address ∧ address < stackPointer + 0x510
  omega

theorem checkedSlice351cAccessOfSeg {stackPointer : Nat} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (seg : Seg checkedSlice351cOwnPc checkedSlice351cExitPc
      (fun _ _ _ _ _ => False) checkedSlice351cWrites
      (checkedSlice351cMemory stackPointer) kv fromStep count before after pc) :
    CheckedSliceMachineAccess stackPointer after := by
  have instructionAgree := seg.agree instructionPreserved_disjoint_checkedSlice351cWrites
  have platformAgree := seg.agree platformPreserved_disjoint_checkedSlice351cWrites
  refine
    { configured := access.configured.mono instructionAgree seg.retired
      stackRead := (seg.get x2 (by
        intro written
        simp [checkedSlice351cWrites, stepBookkeeping] at written)).trans access.stackRead
      stackFits := access.stackFits
      stackAligned := access.stackAligned
      loadPma := fun offset bound =>
        loadPmaAllows_of_agree platformAgree (access.loadPma offset bound)
      storePma := fun offset bound =>
        storePmaAllows_of_agree platformAgree (access.storePma offset bound)
      loadNoMMIO := access.loadNoMMIO
      storeNoMMIO := access.storeNoMMIO
      frameNotCode := access.frameNotCode }

theorem checkedSlice351cCodeOfSeg {stackPointer : Nat} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg checkedSlice351cOwnPc checkedSlice351cExitPc
      (fun _ _ _ _ _ => False) checkedSlice351cWrites
      (checkedSlice351cMemory stackPointer) kv fromStep count before after pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
  intro address byte fileByte
  have unchanged := seg.mem address (by
    intro inside
    have notCode := access.frameNotCode address (checkedSlice351cMemory_in_frame inside)
    rw [fileByte] at notCode
    cases notCode)
  exact unchanged.trans (loaded address byte fileByte)

/-- Exact `0x130b0: ld a3,0x4f8(sp)`. -/
theorem checkedSlice351cLoadEndStep (stepNo stackPointer endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130b0)
    (rep : UIntRep 8 state.mem (stackPointer + 0x4f8) endOffset)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130b0 retired x13 (BitVec.ofNat 64 endOffset)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x130b0 stackPointer 0x4f8 endOffset state
    0x4f8 (.Regidx 13#5) x13 (BitVec.ofNat 64 endOffset) 0x83 0x36 0x81 0x4f
    access.configured atPc access.stackRead rep (access.loadPma 0x4f8 (by omega))
    (access.loadNoMMIO 0x4f8 (by omega)) (by omega) (by omega) loaded
    (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x4f8#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x13_run premise (BitVec.ofNat 64 endOffset)
  · configured_decode access.configured

/-- Exact `0x130b4: ld a2,0x1a0(sp)`. -/
theorem checkedSlice351cLoadStartStep (stepNo stackPointer startOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130b4)
    (rep : UIntRep 8 state.mem (stackPointer + 0x1a0) startOffset)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130b4 retired x12 (BitVec.ofNat 64 startOffset)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x130b4 stackPointer 0x1a0 startOffset state
    0x1a0 (.Regidx 12#5) x12 (BitVec.ofNat 64 startOffset) 0x03 0x36 0x01 0x1a
    access.configured atPc access.stackRead rep (access.loadPma 0x1a0 (by omega))
    (access.loadNoMMIO 0x1a0 (by omega)) (by omega) (by omega) loaded
    (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x1a0#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x12_run premise (BitVec.ofNat 64 startOffset)
  · configured_decode access.configured

/-- Exact `0x130b8: sd a3,0x198(sp)`. -/
theorem checkedSlice351cStoreEndStep (stepNo stackPointer endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130b8)
    (endAt : state.regs.get? x13 = some (BitVec.ofNat 64 endOffset))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x130b8)
          (stackPointer + 0x198) (BitVec.ofNat 64 endOffset))
        0x130b8 retired) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordStoreStep stepNo 0x130b8 stackPointer 0x198 state
    (BitVec.ofNat 64 endOffset) 0x198 (.Regidx 13#5) 0x23 0x3c 0xd1 0x18
    access.configured atPc access.stackRead (access.storePma 0x198 (by omega))
    (access.storeNoMMIO 0x198 (by omega)) (by omega) (by omega) loaded
    (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x198#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := access.configured.storeDecodeContext
    decode_run
  · intro premise writes
    exact rX_x13_run premise _ ((writes.get x13 (by decide)).trans endAt)

private theorem checkedSlice351cBltuRun (state : State) (right left : BitVec 64)
    (rightAt : state.regs.get? x13 = some right)
    (leftAt : state.regs.get? x12 = some left) :
    Runs (bTypeTaken (.Regidx 12#5) (.Regidx 13#5) .BLTU) state state
      (zopz0zI_u right left) :=
  bltuConditionRun state (.Regidx 13#5) (.Regidx 12#5) right left
    (rX_x13_run state right rightAt) (rX_x12_run state left leftAt)

/-- Exact taken or not-taken `0x130bc: bltu a3,a2,0x13db0`. -/
theorem checkedSlice351cStartEndBranchStep (stepNo stackPointer : Nat) (state : State)
    (startOffset endOffset : Nat)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130bc)
    (startAt : state.regs.get? x12 = some (BitVec.ofNat 64 startOffset))
    (endAt : state.regs.get? x13 = some (BitVec.ofNat 64 endOffset))
    (comparison : zopz0zI_u (BitVec.ofNat 64 endOffset) (BitVec.ofNat 64 startOffset) = taken)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if taken then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x130bc 0x13db0)
          0x13db0 retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130bc)
          0x130c0 retired) false := by
  cases taken
  · apply configuredBranchNotTakenStep stepNo 0x130bc state 0xcf4 (.Regidx 12#5)
      (.Regidx 13#5) .BLTU 0xe3 0xea 0xc6 0x4e access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice351cBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130bc)
        (BitVec.ofNat 64 endOffset) (BitVec.ofNat 64 startOffset)
        ((stepPremiseState_writes state 0x130bc).get x13 (by decide) |>.trans endAt)
        ((stepPremiseState_writes state 0x130bc).get x12 (by decide) |>.trans startAt)
  · apply configuredBranchTakenStep stepNo 0x130bc 0x13db0 state 0xcf4
      (.Regidx 12#5) (.Regidx 13#5) .BLTU 0xe3 0xea 0xc6 0x4e
      access.configured atPc loaded (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice351cBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130bc)
        (BitVec.ofNat 64 endOffset) (BitVec.ofNat 64 startOffset)
        ((stepPremiseState_writes state 0x130bc).get x13 (by decide) |>.trans endAt)
        ((stepPremiseState_writes state 0x130bc).get x12 (by decide) |>.trans startAt)
    all_goals native_decide

/-- Exact `0x130c0: ld a2,0x198(sp)`. -/
theorem checkedSlice351cReloadEndStep (stepNo stackPointer endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130c0)
    (rep : UIntRep 8 state.mem (stackPointer + 0x198) endOffset)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130c0 retired x12 (BitVec.ofNat 64 endOffset)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x130c0 stackPointer 0x198 endOffset state
    0x198 (.Regidx 12#5) x12 (BitVec.ofNat 64 endOffset) 0x03 0x36 0x81 0x19
    access.configured atPc access.stackRead rep (access.loadPma 0x198 (by omega))
    (access.loadNoMMIO 0x198 (by omega)) (by omega) (by omega) loaded
    (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x198#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x12_run premise (BitVec.ofNat 64 endOffset)
  · configured_decode access.configured

private theorem checkedSlice351cLengthEndBltuRun (state : State) (length endOffset : BitVec 64)
    (lengthAt : state.regs.get? x10 = some length)
    (endAt : state.regs.get? x12 = some endOffset) :
    Runs (bTypeTaken (.Regidx 12#5) (.Regidx 10#5) .BLTU) state state
      (zopz0zI_u length endOffset) :=
  bltuConditionRun state (.Regidx 10#5) (.Regidx 12#5) length endOffset
    (rX_x10_run state length lengthAt) (rX_x12_run state endOffset endAt)

/-- Exact taken or not-taken `0x130c4: bltu a0,a2,0x13db0`. -/
theorem checkedSlice351cLengthEndBranchStep (stepNo stackPointer : Nat) (state : State)
    (length endOffset : Nat)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130c4)
    (lengthAt : state.regs.get? x10 = some (BitVec.ofNat 64 length))
    (endAt : state.regs.get? x12 = some (BitVec.ofNat 64 endOffset))
    (comparison : zopz0zI_u (BitVec.ofNat 64 length) (BitVec.ofNat 64 endOffset) = taken)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if taken then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x130c4 0x13db0)
          0x13db0 retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130c4)
          0x130c8 retired) false := by
  cases taken
  · apply configuredBranchNotTakenStep stepNo 0x130c4 state 0xcec (.Regidx 12#5)
      (.Regidx 10#5) .BLTU 0xe3 0x66 0xc5 0x4e access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice351cLengthEndBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130c4)
        (BitVec.ofNat 64 length) (BitVec.ofNat 64 endOffset)
        ((stepPremiseState_writes state 0x130c4).get x10 (by decide) |>.trans lengthAt)
        ((stepPremiseState_writes state 0x130c4).get x12 (by decide) |>.trans endAt)
  · apply configuredBranchTakenStep stepNo 0x130c4 0x13db0 state 0xcec
      (.Regidx 12#5) (.Regidx 10#5) .BLTU 0xe3 0x66 0xc5 0x4e
      access.configured atPc loaded (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice351cLengthEndBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130c4)
        (BitVec.ofNat 64 length) (BitVec.ofNat 64 endOffset)
        ((stepPremiseState_writes state 0x130c4).get x10 (by decide) |>.trans lengthAt)
        ((stepPremiseState_writes state 0x130c4).get x12 (by decide) |>.trans endAt)
    all_goals native_decide

/-- The three stack operations shared by every outcome of the second checked-slice instance. -/
theorem checkedSlice351cPrefix (fromStep stackPointer startOffset endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130b0)
    (startRep : UIntRep 8 state.mem (stackPointer + 0x1a0) startOffset)
    (endRep : UIntRep 8 state.mem (stackPointer + 0x4f8) endOffset)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after,
      Seg checkedSlice351cOwnPc checkedSlice351cExitPc (fun _ _ _ _ _ => False)
        checkedSlice351cWrites (checkedSlice351cMemory stackPointer)
        [⟨x12, BitVec.ofNat 64 startOffset⟩, ⟨x13, BitVec.ofNat 64 endOffset⟩]
        fromStep 3 state after 0x130bc ∧
      UIntRep 8 after.mem (stackPointer + 0x198) endOffset := by
  obtain ⟨retired, retiredRead⟩ := access.configured.retiredCounter
  have seg0 := Seg.nil checkedSlice351cOwnPc checkedSlice351cExitPc
    (fun _ _ _ _ _ => False) checkedSlice351cWrites
    (checkedSlice351cMemory stackPointer) fromStep ⟨retired, retiredRead⟩ atPc
  obtain ⟨s1, seg1⟩ := seg0.step
    (by owned_pc [checkedSlice351cOwnPc, pcInList])
    (by owned_pc [checkedSlice351cExitPc, pcInList]) x13
    (BitVec.ofNat 64 endOffset) 0x130b4
    (checkedSlice351cLoadEndStep fromStep stackPointer endOffset state access atPc endRep loaded)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr rfl)) (by decide) (by decide)
    (by simp [RegsOutside])
  have startRep1 : UIntRep 8 s1.mem (stackPointer + 0x1a0) startOffset :=
    startRep.of_writesOnlyWithin seg1.mem (by
      intro index indexBound inside
      unfold checkedSlice351cMemory byteRange at inside
      omega)
  obtain ⟨s2, seg2⟩ := seg1.step
    (by owned_pc [checkedSlice351cOwnPc, pcInList])
    (by owned_pc [checkedSlice351cExitPc, pcInList]) x12
    (BitVec.ofNat 64 startOffset) 0x130b8
    (checkedSlice351cLoadStartStep (fromStep + 1) stackPointer startOffset s1
      (checkedSlice351cAccessOfSeg access seg1) seg1.atPc startRep1
      (checkedSlice351cCodeOfSeg access loaded seg1))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inl rfl)) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have endAt2 := seg2.reg x13 (BitVec.ofNat 64 endOffset) (by simp)
  obtain ⟨retired3, s3, s3Eq, seg3⟩ := seg2.stepStoreWitness
    (width := 8) (stackPointer + 0x198) (BitVec.ofNat 64 endOffset) 0x130bc
    (by owned_pc [checkedSlice351cOwnPc, pcInList])
    (by owned_pc [checkedSlice351cExitPc, pcInList])
    (checkedSlice351cStoreEndStep (fromStep + 2) stackPointer endOffset s2
      (checkedSlice351cAccessOfSeg access seg2) seg2.atPc endAt2
      (checkedSlice351cCodeOfSeg access loaded seg2))
    (by native_decide)
    (by intro address lower upper; unfold checkedSlice351cMemory byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  refine ⟨s3, by simpa only [Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seg3,
    ?_⟩
  rw [s3Eq]
  simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
    uintRep_afterWriteBytes_eight
      (coreStoreNextState (tryStepStoreAfterIncrement s2) 0x130b8)
      (stackPointer + 0x198) endOffset endRep.1 (by
        have stackFits := access.stackFits
        omega)

/-- The checked-slice instance rejects an end offset that precedes its start offset. -/
theorem checkedSlice351cInvalidStartEndRun
    (fromStep stackPointer startOffset endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130b0)
    (startRep : UIntRep 8 state.mem (stackPointer + 0x1a0) startOffset)
    (endRep : UIntRep 8 state.mem (stackPointer + 0x4f8) endOffset)
    (invalid : zopz0zI_u (BitVec.ofNat 64 endOffset) (BitVec.ofNat 64 startOffset) = true)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after,
      Seg checkedSlice351cOwnPc checkedSlice351cExitPc (fun _ _ _ _ _ => False)
        checkedSlice351cWrites (checkedSlice351cMemory stackPointer)
        [⟨x12, BitVec.ofNat 64 startOffset⟩, ⟨x13, BitVec.ofNat 64 endOffset⟩]
        fromStep 4 state after 0x13db0 := by
  obtain ⟨prefixState, seg3, _⟩ := checkedSlice351cPrefix fromStep stackPointer
    startOffset endOffset state access atPc startRep endRep loaded
  obtain ⟨after, seg4⟩ := seg3.stepJump 0x13db0
    (by owned_pc [checkedSlice351cOwnPc, pcInList])
    (by owned_pc [checkedSlice351cExitPc, pcInList])
    (checkedSlice351cStartEndBranchStep (fromStep + 3) stackPointer prefixState
      startOffset endOffset (checkedSlice351cAccessOfSeg access seg3) seg3.atPc
      (seg3.reg x12 (BitVec.ofNat 64 startOffset) (by simp))
      (seg3.reg x13 (BitVec.ofNat 64 endOffset) (by simp)) invalid
      (checkedSlice351cCodeOfSeg access loaded seg3))
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seg4⟩

/-- The first bounds check accepts the slice and preserves the stored end offset. -/
theorem checkedSlice351cValidStartEndPrefix
    (fromStep stackPointer startOffset endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130b0)
    (startRep : UIntRep 8 state.mem (stackPointer + 0x1a0) startOffset)
    (endRep : UIntRep 8 state.mem (stackPointer + 0x4f8) endOffset)
    (valid : zopz0zI_u (BitVec.ofNat 64 endOffset) (BitVec.ofNat 64 startOffset) = false)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after,
      Seg checkedSlice351cOwnPc checkedSlice351cExitPc (fun _ _ _ _ _ => False)
        checkedSlice351cWrites (checkedSlice351cMemory stackPointer)
        [⟨x12, BitVec.ofNat 64 startOffset⟩, ⟨x13, BitVec.ofNat 64 endOffset⟩]
        fromStep 4 state after 0x130c0 ∧
      UIntRep 8 after.mem (stackPointer + 0x198) endOffset := by
  obtain ⟨prefixState, seg3, stored⟩ := checkedSlice351cPrefix fromStep stackPointer
    startOffset endOffset state access atPc startRep endRep loaded
  obtain ⟨retired4, after, afterEq, seg4⟩ := seg3.stepFallThroughWitness 0x130c0
    (by owned_pc [checkedSlice351cOwnPc, pcInList])
    (by owned_pc [checkedSlice351cExitPc, pcInList])
    (checkedSlice351cStartEndBranchStep (fromStep + 3) stackPointer prefixState
      startOffset endOffset (checkedSlice351cAccessOfSeg access seg3) seg3.atPc
      (seg3.reg x12 (BitVec.ofNat 64 startOffset) (by simp))
      (seg3.reg x13 (BitVec.ofNat 64 endOffset) (by simp)) valid
      (checkedSlice351cCodeOfSeg access loaded seg3))
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  refine ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seg4, ?_⟩
  rw [afterEq]
  exact stored.of_mem_eq (fallThroughRetirement_mem prefixState 0x130bc 0x130c0 retired4)

/-- After the first check succeeds, the second check rejects an oversized end or reaches success. -/
theorem checkedSlice351cLengthCheckedRun
    (fromStep stackPointer length startOffset endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130b0)
    (lengthAt : state.regs.get? x10 = some (BitVec.ofNat 64 length))
    (startRep : UIntRep 8 state.mem (stackPointer + 0x1a0) startOffset)
    (endRep : UIntRep 8 state.mem (stackPointer + 0x4f8) endOffset)
    (startEndValid :
      zopz0zI_u (BitVec.ofNat 64 endOffset) (BitVec.ofNat 64 startOffset) = false)
    (lengthComparison :
      zopz0zI_u (BitVec.ofNat 64 length) (BitVec.ofNat 64 endOffset) = rejected)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after,
      Seg checkedSlice351cOwnPc checkedSlice351cExitPc (fun _ _ _ _ _ => False)
        checkedSlice351cWrites (checkedSlice351cMemory stackPointer)
        [⟨x12, BitVec.ofNat 64 endOffset⟩, ⟨x13, BitVec.ofNat 64 endOffset⟩]
        fromStep 6 state after (if rejected then 0x13db0 else 0x130c8) := by
  obtain ⟨checked, seg4, stored⟩ := checkedSlice351cValidStartEndPrefix fromStep stackPointer
    startOffset endOffset state access atPc startRep endRep startEndValid loaded
  have seg4' := seg4.forget (kv' := [⟨x13, BitVec.ofNat 64 endOffset⟩]) (by simp)
  obtain ⟨reloaded, seg5⟩ := seg4'.step
    (by owned_pc [checkedSlice351cOwnPc, pcInList])
    (by owned_pc [checkedSlice351cExitPc, pcInList]) x12
    (BitVec.ofNat 64 endOffset) 0x130c4
    (checkedSlice351cReloadEndStep (fromStep + 4) stackPointer endOffset checked
      (checkedSlice351cAccessOfSeg access seg4) seg4.atPc stored
      (checkedSlice351cCodeOfSeg access loaded seg4))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inl rfl)) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have lengthAt5 : reloaded.regs.get? x10 = some (BitVec.ofNat 64 length) :=
    (seg5.get x10 (by simp [checkedSlice351cWrites, stepBookkeeping])).trans lengthAt
  cases rejected
  · obtain ⟨after, seg6⟩ := seg5.stepFallThrough 0x130c8
      (by owned_pc [checkedSlice351cOwnPc, pcInList])
      (by owned_pc [checkedSlice351cExitPc, pcInList])
      (checkedSlice351cLengthEndBranchStep (fromStep + 5) stackPointer reloaded
        length endOffset (checkedSlice351cAccessOfSeg access seg5) seg5.atPc lengthAt5
        (seg5.reg x12 (BitVec.ofNat 64 endOffset) (by simp)) lengthComparison
        (checkedSlice351cCodeOfSeg access loaded seg5))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seg6⟩
  · obtain ⟨after, seg6⟩ := seg5.stepJump 0x13db0
      (by owned_pc [checkedSlice351cOwnPc, pcInList])
      (by owned_pc [checkedSlice351cExitPc, pcInList])
      (checkedSlice351cLengthEndBranchStep (fromStep + 5) stackPointer reloaded
        length endOffset (checkedSlice351cAccessOfSeg access seg5) seg5.atPc lengthAt5
        (seg5.reg x12 (BitVec.ofNat 64 endOffset) (by simp)) lengthComparison
        (checkedSlice351cCodeOfSeg access loaded seg5))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seg6⟩

end BinaryFv.Zesu.MachineExecution
