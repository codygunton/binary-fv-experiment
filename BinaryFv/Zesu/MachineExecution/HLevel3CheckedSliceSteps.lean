import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Instruction.Execute.Arithmetic
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

/-- Transport the shared checked-slice access facts through an exact `Seg` frame. -/
theorem CheckedSliceMachineAccess.ofSeg {stackPointer : Nat} {own exit : BitVec 64 → Prop}
    {W : RegSet} {M : Region} {kv : List RegVal} {fromStep count : Nat}
    {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (instructionDisjoint : RegSet.Disjoint instructionPreserved W)
    (platformDisjoint : RegSet.Disjoint platformPreserved W)
    (spNotWritten : ¬W x2)
    (seg : Seg own exit (fun _ _ _ _ _ => False) W M kv fromStep count before after pc) :
    CheckedSliceMachineAccess stackPointer after := by
  have instructionAgree := seg.agree instructionDisjoint
  have platformAgree := seg.agree platformDisjoint
  refine
    { configured := access.configured.mono instructionAgree seg.retired
      stackRead := (seg.get x2 spNotWritten).trans access.stackRead
      stackFits := access.stackFits
      stackAligned := access.stackAligned
      loadPma := fun offset bound =>
        loadPmaAllows_of_agree platformAgree (access.loadPma offset bound)
      storePma := fun offset bound =>
        storePmaAllows_of_agree platformAgree (access.storePma offset bound)
      loadNoMMIO := access.loadNoMMIO
      storeNoMMIO := access.storeNoMMIO
      frameNotCode := access.frameNotCode }

/-- Preserve the linked program image through writes inside the checked-slice stack frame. -/
theorem checkedSliceCodeOfSeg {stackPointer : Nat} {own exit : BitVec 64 → Prop}
    {W : RegSet} {M : Region} {kv : List RegVal} {fromStep count : Nat}
    {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (memoryInFrame : ∀ {address}, M address → checkedSliceFrame stackPointer address)
    (seg : Seg own exit (fun _ _ _ _ _ => False) W M kv fromStep count before after pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
  intro address byte fileByte
  have unchanged := seg.mem address (by
    intro inside
    have notCode := access.frameNotCode address (memoryInFrame inside)
    rw [fileByte] at notCode
    cases notCode)
  exact unchanged.trans (loaded address byte fileByte)

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
    CheckedSliceMachineAccess stackPointer after :=
  access.ofSeg instructionPreserved_disjoint_checkedSlice351cWrites
    platformPreserved_disjoint_checkedSlice351cWrites
    (by intro written; simp [checkedSlice351cWrites, stepBookkeeping] at written) seg

theorem checkedSlice351cCodeOfSeg {stackPointer : Nat} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg checkedSlice351cOwnPc checkedSlice351cExitPc
      (fun _ _ _ _ _ => False) checkedSlice351cWrites
      (checkedSlice351cMemory stackPointer) kv fromStep count before after pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully after.mem :=
  checkedSliceCodeOfSeg access loaded checkedSlice351cMemory_in_frame seg

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

/-! ## Request-type-zero checked slice at `0x13098` -/

def checkedSlice34fdOwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x13098, 0x1309c, 0x130a0, 0x130a4, 0x130a8, 0x130ac] pc

def checkedSlice34fdExitPc (pc : BitVec 64) : Prop :=
  pcInList [0x130b0, 0x13db0] pc

def checkedSlice34fdWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x12 ∨ register = x13

def checkedSlice34fdMemory (stackPointer : Nat) : Region := fun address =>
  byteRange (stackPointer + 0x188) 8 address ∨
  byteRange (stackPointer + 0x1a0) 8 address

private theorem instructionPreserved_disjoint_checkedSlice34fdWrites :
    RegSet.Disjoint instructionPreserved checkedSlice34fdWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem platformPreserved_disjoint_checkedSlice34fdWrites :
    RegSet.Disjoint platformPreserved checkedSlice34fdWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved bookkeeping
  all_goals simp [platformPreserved] at preserved

private theorem checkedSlice34fdMemory_in_frame {stackPointer address : Nat}
    (inside : checkedSlice34fdMemory stackPointer address) :
    checkedSliceFrame stackPointer address := by
  rcases inside with inside | inside
  · change stackPointer + 0x188 ≤ address ∧ address < stackPointer + 0x188 + 8 at inside
    unfold checkedSliceFrame byteRange
    omega
  · change stackPointer + 0x1a0 ≤ address ∧ address < stackPointer + 0x1a0 + 8 at inside
    unfold checkedSliceFrame byteRange
    omega

theorem checkedSlice34fdAccessOfSeg {stackPointer : Nat} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (seg : Seg checkedSlice34fdOwnPc checkedSlice34fdExitPc
      (fun _ _ _ _ _ => False) checkedSlice34fdWrites
      (checkedSlice34fdMemory stackPointer) kv fromStep count before after pc) :
    CheckedSliceMachineAccess stackPointer after :=
  access.ofSeg instructionPreserved_disjoint_checkedSlice34fdWrites
    platformPreserved_disjoint_checkedSlice34fdWrites
    (by intro written; simp [checkedSlice34fdWrites, stepBookkeeping] at written) seg

theorem checkedSlice34fdCodeOfSeg {stackPointer : Nat} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg checkedSlice34fdOwnPc checkedSlice34fdExitPc
      (fun _ _ _ _ _ => False) checkedSlice34fdWrites
      (checkedSlice34fdMemory stackPointer) kv fromStep count before after pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully after.mem :=
  checkedSliceCodeOfSeg access loaded checkedSlice34fdMemory_in_frame seg

private theorem checkedSlice34fdLoadStartStep
    (stepNo stackPointer startOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x13098)
    (rep : UIntRep 8 state.mem (stackPointer + 0x4e8) startOffset)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x13098 retired x13 (BitVec.ofNat 64 startOffset)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x13098 stackPointer 0x4e8 startOffset state
    0x4e8 (.Regidx 13#5) x13 (BitVec.ofNat 64 startOffset) 0x83 0x36 0x81 0x4e
    access.configured atPc access.stackRead rep (access.loadPma 0x4e8 (by omega))
    (access.loadNoMMIO 0x4e8 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x4e8#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x13_run premise (BitVec.ofNat 64 startOffset)
  · configured_decode access.configured

private theorem checkedSlice34fdLoadEndStep
    (stepNo stackPointer endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x1309c)
    (rep : UIntRep 8 state.mem (stackPointer + 0x4f0) endOffset)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1309c retired x12 (BitVec.ofNat 64 endOffset)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x1309c stackPointer 0x4f0 endOffset state
    0x4f0 (.Regidx 12#5) x12 (BitVec.ofNat 64 endOffset) 0x03 0x36 0x01 0x4f
    access.configured atPc access.stackRead rep (access.loadPma 0x4f0 (by omega))
    (access.loadNoMMIO 0x4f0 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x4f0#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x12_run premise (BitVec.ofNat 64 endOffset)
  · configured_decode access.configured

private theorem checkedSlice34fdStoreStartStep
    (stepNo stackPointer startOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130a0)
    (startAt : state.regs.get? x13 = some (BitVec.ofNat 64 startOffset))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x130a0)
          (stackPointer + 0x188) (BitVec.ofNat 64 startOffset))
        0x130a0 retired) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordStoreStep stepNo 0x130a0 stackPointer 0x188 state
    (BitVec.ofNat 64 startOffset) 0x188 (.Regidx 13#5) 0x23 0x34 0xd1 0x18
    access.configured atPc access.stackRead (access.storePma 0x188 (by omega))
    (access.storeNoMMIO 0x188 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x188#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := access.configured.storeDecodeContext
    configured_decode access.configured
  · intro premise writes
    exact rX_x13_run premise _ ((writes.get x13 (by decide)).trans startAt)

private theorem checkedSlice34fdStoreEndStep
    (stepNo stackPointer endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130a8)
    (endAt : state.regs.get? x12 = some (BitVec.ofNat 64 endOffset))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x130a8)
          (stackPointer + 0x1a0) (BitVec.ofNat 64 endOffset))
        0x130a8 retired) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordStoreStep stepNo 0x130a8 stackPointer 0x1a0 state
    (BitVec.ofNat 64 endOffset) 0x1a0 (.Regidx 12#5) 0x23 0x30 0xc1 0x1a
    access.configured atPc access.stackRead (access.storePma 0x1a0 (by omega))
    (access.storeNoMMIO 0x1a0 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x1a0#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := access.configured.storeDecodeContext
    configured_decode access.configured
  · intro premise writes
    exact rX_x12_run premise _ ((writes.get x12 (by decide)).trans endAt)

private theorem checkedSlice34fdBltuRun (state : State) (left right : BitVec 64)
    (leftAt : state.regs.get? x12 = some left)
    (rightAt : state.regs.get? x13 = some right) :
    Runs (bTypeTaken (.Regidx 13#5) (.Regidx 12#5) .BLTU) state state
      (zopz0zI_u left right) :=
  bltuConditionRun state (.Regidx 12#5) (.Regidx 13#5) left right
    (rX_x12_run state left leftAt) (rX_x13_run state right rightAt)

private theorem checkedSlice34fdStartEndBranchStep
    (stepNo stackPointer startOffset endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130a4)
    (startAt : state.regs.get? x13 = some (BitVec.ofNat 64 startOffset))
    (endAt : state.regs.get? x12 = some (BitVec.ofNat 64 endOffset))
    (comparison : zopz0zI_u (BitVec.ofNat 64 endOffset)
      (BitVec.ofNat 64 startOffset) = taken)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if taken then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x130a4 0x13db0)
          0x13db0 retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130a4)
          0x130a8 retired) false := by
  cases taken
  · apply configuredBranchNotTakenStep stepNo 0x130a4 state 0xd0c (.Regidx 13#5)
      (.Regidx 12#5) .BLTU 0xe3 0x66 0xd6 0x50 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice34fdBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130a4)
        (BitVec.ofNat 64 endOffset) (BitVec.ofNat 64 startOffset)
        ((stepPremiseState_writes state 0x130a4).get x12 (by decide) |>.trans endAt)
        ((stepPremiseState_writes state 0x130a4).get x13 (by decide) |>.trans startAt)
  · apply configuredBranchTakenStep stepNo 0x130a4 0x13db0 state 0xd0c
      (.Regidx 13#5) (.Regidx 12#5) .BLTU 0xe3 0x66 0xd6 0x50
      access.configured atPc loaded (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice34fdBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130a4)
        (BitVec.ofNat 64 endOffset) (BitVec.ofNat 64 startOffset)
        ((stepPremiseState_writes state 0x130a4).get x12 (by decide) |>.trans endAt)
        ((stepPremiseState_writes state 0x130a4).get x13 (by decide) |>.trans startAt)
    all_goals native_decide

private theorem checkedSlice34fdLengthEndBltuRun (state : State)
    (length endOffset : BitVec 64)
    (lengthAt : state.regs.get? x10 = some length)
    (endAt : state.regs.get? x12 = some endOffset) :
    Runs (bTypeTaken (.Regidx 12#5) (.Regidx 10#5) .BLTU) state state
      (zopz0zI_u length endOffset) :=
  bltuConditionRun state (.Regidx 10#5) (.Regidx 12#5) length endOffset
    (rX_x10_run state length lengthAt) (rX_x12_run state endOffset endAt)

private theorem checkedSlice34fdLengthEndBranchStep
    (stepNo stackPointer length endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130ac)
    (lengthAt : state.regs.get? x10 = some (BitVec.ofNat 64 length))
    (endAt : state.regs.get? x12 = some (BitVec.ofNat 64 endOffset))
    (comparison : zopz0zI_u (BitVec.ofNat 64 length)
      (BitVec.ofNat 64 endOffset) = taken)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if taken then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x130ac 0x13db0)
          0x13db0 retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130ac)
          0x130b0 retired) false := by
  cases taken
  · apply configuredBranchNotTakenStep stepNo 0x130ac state 0xd04 (.Regidx 12#5)
      (.Regidx 10#5) .BLTU 0xe3 0x62 0xc5 0x50 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice34fdLengthEndBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130ac)
        (BitVec.ofNat 64 length) (BitVec.ofNat 64 endOffset)
        ((stepPremiseState_writes state 0x130ac).get x10 (by decide) |>.trans lengthAt)
        ((stepPremiseState_writes state 0x130ac).get x12 (by decide) |>.trans endAt)
  · apply configuredBranchTakenStep stepNo 0x130ac 0x13db0 state 0xd04
      (.Regidx 12#5) (.Regidx 10#5) .BLTU 0xe3 0x62 0xc5 0x50
      access.configured atPc loaded (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice34fdLengthEndBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130ac)
        (BitVec.ofNat 64 length) (BitVec.ofNat 64 endOffset)
        ((stepPremiseState_writes state 0x130ac).get x10 (by decide) |>.trans lengthAt)
        ((stepPremiseState_writes state 0x130ac).get x12 (by decide) |>.trans endAt)
    all_goals native_decide

/-- Exact trace for request type zero, including both bounds checks. -/
theorem checkedSlice34fdRun (fromStep stackPointer length startOffset endOffset : Nat)
    (state : State) (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x13098)
    (lengthAt : state.regs.get? x10 = some (BitVec.ofNat 64 length))
    (startRep : UIntRep 8 state.mem (stackPointer + 0x4e8) startOffset)
    (endRep : UIntRep 8 state.mem (stackPointer + 0x4f0) endOffset)
    (startEndComparison : zopz0zI_u (BitVec.ofNat 64 endOffset)
      (BitVec.ofNat 64 startOffset) = reversed)
    (lengthComparison : zopz0zI_u (BitVec.ofNat 64 length)
      (BitVec.ofNat 64 endOffset) = oversized)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after,
      Seg checkedSlice34fdOwnPc checkedSlice34fdExitPc (fun _ _ _ _ _ => False)
        checkedSlice34fdWrites (checkedSlice34fdMemory stackPointer)
        [⟨x12, BitVec.ofNat 64 endOffset⟩, ⟨x13, BitVec.ofNat 64 startOffset⟩]
        fromStep (if reversed then 4 else 6) state after
          (if reversed || oversized then 0x13db0 else 0x130b0) := by
  obtain ⟨retired, retiredRead⟩ := access.configured.retiredCounter
  have seg0 := Seg.nil checkedSlice34fdOwnPc checkedSlice34fdExitPc
    (fun _ _ _ _ _ => False) checkedSlice34fdWrites
    (checkedSlice34fdMemory stackPointer) fromStep ⟨retired, retiredRead⟩ atPc
  obtain ⟨s1, seg1⟩ := seg0.step
    (by owned_pc [checkedSlice34fdOwnPc, pcInList])
    (by owned_pc [checkedSlice34fdExitPc, pcInList]) x13
    (BitVec.ofNat 64 startOffset) 0x1309c
    (checkedSlice34fdLoadStartStep fromStep stackPointer startOffset state access atPc
      startRep loaded)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr rfl)) (by decide) (by decide) (by simp [RegsOutside])
  have endRep1 : UIntRep 8 s1.mem (stackPointer + 0x4f0) endOffset := by
    exact endRep.of_writesOnlyWithin seg1.mem (by
      intro index indexBound inside
      rcases inside with inside | inside
      · unfold byteRange at inside
        omega
      · unfold byteRange at inside
        omega)
  obtain ⟨s2, seg2⟩ := seg1.step
    (by owned_pc [checkedSlice34fdOwnPc, pcInList])
    (by owned_pc [checkedSlice34fdExitPc, pcInList]) x12
    (BitVec.ofNat 64 endOffset) 0x130a0
    (checkedSlice34fdLoadEndStep (fromStep + 1) stackPointer endOffset s1
      (checkedSlice34fdAccessOfSeg access seg1) seg1.atPc endRep1
      (checkedSlice34fdCodeOfSeg access loaded seg1))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inl rfl)) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨_, s3, _, seg3⟩ := seg2.stepStoreWitness (width := 8)
    (stackPointer + 0x188) (BitVec.ofNat 64 startOffset) 0x130a4
    (by owned_pc [checkedSlice34fdOwnPc, pcInList])
    (by owned_pc [checkedSlice34fdExitPc, pcInList])
    (checkedSlice34fdStoreStartStep (fromStep + 2) stackPointer startOffset s2
      (checkedSlice34fdAccessOfSeg access seg2) seg2.atPc
      (seg2.reg x13 (BitVec.ofNat 64 startOffset) (by simp))
      (checkedSlice34fdCodeOfSeg access loaded seg2))
    (by native_decide)
    (by intro address lower upper; exact Or.inl ⟨lower, upper⟩)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  cases reversed
  · obtain ⟨s4, seg4⟩ := seg3.stepFallThrough 0x130a8
      (by owned_pc [checkedSlice34fdOwnPc, pcInList])
      (by owned_pc [checkedSlice34fdExitPc, pcInList])
      (checkedSlice34fdStartEndBranchStep (fromStep + 3) stackPointer startOffset
        endOffset s3 (checkedSlice34fdAccessOfSeg access seg3) seg3.atPc
        (seg3.reg x13 (BitVec.ofNat 64 startOffset) (by simp))
        (seg3.reg x12 (BitVec.ofNat 64 endOffset) (by simp)) startEndComparison
        (checkedSlice34fdCodeOfSeg access loaded seg3))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨_, s5, _, seg5⟩ := seg4.stepStoreWitness (width := 8)
      (stackPointer + 0x1a0) (BitVec.ofNat 64 endOffset) 0x130ac
      (by owned_pc [checkedSlice34fdOwnPc, pcInList])
      (by owned_pc [checkedSlice34fdExitPc, pcInList])
      (checkedSlice34fdStoreEndStep (fromStep + 4) stackPointer endOffset s4
        (checkedSlice34fdAccessOfSeg access seg4) seg4.atPc
        (seg4.reg x12 (BitVec.ofNat 64 endOffset) (by simp))
        (checkedSlice34fdCodeOfSeg access loaded seg4))
      (by native_decide)
      (by intro address lower upper; exact Or.inr ⟨lower, upper⟩)
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    have lengthAt5 : s5.regs.get? x10 = some (BitVec.ofNat 64 length) :=
      (seg5.get x10 (by simp [checkedSlice34fdWrites, stepBookkeeping])).trans lengthAt
    cases oversized
    · obtain ⟨after, seg6⟩ := seg5.stepFallThrough 0x130b0
        (by owned_pc [checkedSlice34fdOwnPc, pcInList])
        (by owned_pc [checkedSlice34fdExitPc, pcInList])
        (checkedSlice34fdLengthEndBranchStep (fromStep + 5) stackPointer length
          endOffset s5 (checkedSlice34fdAccessOfSeg access seg5) seg5.atPc lengthAt5
          (seg5.reg x12 (BitVec.ofNat 64 endOffset) (by simp)) lengthComparison
          (checkedSlice34fdCodeOfSeg access loaded seg5))
        (by intro register bookkeeping; exact Or.inl bookkeeping)
        (by simp [RegsOutside, stepBookkeeping])
      exact ⟨after, by simpa only [Bool.false_eq, Bool.false_or, if_false, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using seg6⟩
    · obtain ⟨after, seg6⟩ := seg5.stepJump 0x13db0
        (by owned_pc [checkedSlice34fdOwnPc, pcInList])
        (by owned_pc [checkedSlice34fdExitPc, pcInList])
        (checkedSlice34fdLengthEndBranchStep (fromStep + 5) stackPointer length
          endOffset s5 (checkedSlice34fdAccessOfSeg access seg5) seg5.atPc lengthAt5
          (seg5.reg x12 (BitVec.ofNat 64 endOffset) (by simp)) lengthComparison
          (checkedSlice34fdCodeOfSeg access loaded seg5))
        (by intro register bookkeeping; exact Or.inl bookkeeping)
        (by simp [RegsOutside, stepBookkeeping])
      refine ⟨after, ?_⟩
      exact seg6
  · obtain ⟨after, seg4⟩ := seg3.stepJump 0x13db0
      (by owned_pc [checkedSlice34fdOwnPc, pcInList])
      (by owned_pc [checkedSlice34fdExitPc, pcInList])
      (checkedSlice34fdStartEndBranchStep (fromStep + 3) stackPointer startOffset
        endOffset s3 (checkedSlice34fdAccessOfSeg access seg3) seg3.atPc
        (seg3.reg x13 (BitVec.ofNat 64 startOffset) (by simp))
        (seg3.reg x12 (BitVec.ofNat 64 endOffset) (by simp)) startEndComparison
        (checkedSlice34fdCodeOfSeg access loaded seg3))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa only [Bool.true_eq, Bool.true_or, if_true, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using seg4⟩

/-! ## Request type two -/

def checkedSlice3541OwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x130c8, 0x130cc, 0x130d0, 0x130d4, 0x130d8, 0x130dc, 0x130e0,
    0x130e4, 0x130e8, 0x130ec, 0x130f0, 0x130f4, 0x130f8] pc

def checkedSlice3541ExitPc (pc : BitVec 64) : Prop :=
  pcInList [0x1230c, 0x130fc, 0x13db0] pc

def checkedSlice3541Writes : RegSet := fun register =>
  stepBookkeeping register ∨ register = x12 ∨ register = x13 ∨ register = x14 ∨
    register = x22 ∨ register = x24 ∨ register = x27

def checkedSlice3541Memory (stackPointer : Nat) : Region :=
  byteRange (stackPointer + 0x170) 8

private theorem instructionPreserved_disjoint_checkedSlice3541Writes :
    RegSet.Disjoint instructionPreserved checkedSlice3541Writes := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem platformPreserved_disjoint_checkedSlice3541Writes :
    RegSet.Disjoint platformPreserved checkedSlice3541Writes := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved bookkeeping
  all_goals simp [platformPreserved] at preserved

private theorem checkedSlice3541Memory_in_frame {stackPointer address : Nat}
    (inside : checkedSlice3541Memory stackPointer address) :
    checkedSliceFrame stackPointer address := by
  change stackPointer + 0x170 ≤ address ∧ address < stackPointer + 0x170 + 8 at inside
  unfold checkedSliceFrame byteRange
  omega

theorem checkedSlice3541AccessOfSeg {stackPointer : Nat} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (seg : Seg checkedSlice3541OwnPc checkedSlice3541ExitPc
      (fun _ _ _ _ _ => False) checkedSlice3541Writes
      (checkedSlice3541Memory stackPointer) kv fromStep count before after pc) :
    CheckedSliceMachineAccess stackPointer after :=
  access.ofSeg instructionPreserved_disjoint_checkedSlice3541Writes
    platformPreserved_disjoint_checkedSlice3541Writes
    (by intro written; simp [checkedSlice3541Writes, stepBookkeeping] at written) seg

theorem checkedSlice3541CodeOfSeg {stackPointer : Nat} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg checkedSlice3541OwnPc checkedSlice3541ExitPc
      (fun _ _ _ _ _ => False) checkedSlice3541Writes
      (checkedSlice3541Memory stackPointer) kv fromStep count before after pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully after.mem :=
  checkedSliceCodeOfSeg access loaded checkedSlice3541Memory_in_frame seg

/-- Exact `0x130c8: ld a3,0x500(sp)`. -/
theorem checkedSlice3541LoadCandidateEndStep
    (stepNo stackPointer candidateEnd : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130c8)
    (rep : UIntRep 8 state.mem (stackPointer + 0x500) candidateEnd)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130c8 retired x13 (BitVec.ofNat 64 candidateEnd)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x130c8 stackPointer 0x500 candidateEnd state
    0x500 (.Regidx 13#5) x13 (BitVec.ofNat 64 candidateEnd) 0x83 0x36 0x01 0x50
    access.configured atPc access.stackRead rep (access.loadPma 0x500 (by omega))
    (access.loadNoMMIO 0x500 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x500#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x13_run premise (BitVec.ofNat 64 candidateEnd)
  · configured_decode access.configured

/-- Exact `0x130cc: li a2,12`. -/
theorem checkedSlice3541LoadThresholdStep (stepNo : Nat) (state : State)
    (access : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x130cc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130cc retired x12 12) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130cc
  have execute : Runs (execute (.ITYPE (12, .Regidx 0#5, .Regidx 12#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x12 12 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 12 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 12 0 = 12#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 12 (.Regidx 0#5)
      (.Regidx 12#5) .ADDI 0 (rX_x0_run premise) (wX_x12_run premise _)
  exact configuredRegisterWriteStep stepNo 0x130cc state x12 12
    (.ITYPE (12, .Regidx 0#5, .Regidx 12#5, .ADDI)) 0x13 0x06 0xc0 0x00
    access atPc loaded (by configured_decode access) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x130d0: sd a3,0x170(sp)`. -/
theorem checkedSlice3541StoreCandidateEndStep
    (stepNo stackPointer candidateEnd : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130d0)
    (endAt : state.regs.get? x13 = some (BitVec.ofNat 64 candidateEnd))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x130d0)
          (stackPointer + 0x170) (BitVec.ofNat 64 candidateEnd))
        0x130d0 retired) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordStoreStep stepNo 0x130d0 stackPointer 0x170 state
    (BitVec.ofNat 64 candidateEnd) 0x170 (.Regidx 13#5) 0x23 0x38 0xd1 0x16
    access.configured atPc access.stackRead (access.storePma 0x170 (by omega))
    (access.storeNoMMIO 0x170 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x170#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := access.configured.storeDecodeContext
    configured_decode access.configured
  · intro premise writes
    exact rX_x13_run premise _ ((writes.get x13 (by decide)).trans endAt)

private theorem checkedSlice3541HasNextRun (state : State) (tableBytes : BitVec 64)
    (tableAt : state.regs.get? x11 = some tableBytes)
    (thresholdAt : state.regs.get? x12 = some 12) :
    Runs (bTypeTaken (.Regidx 11#5) (.Regidx 12#5) .BLTU) state state
      (zopz0zI_u 12 tableBytes) :=
  bltuConditionRun state (.Regidx 12#5) (.Regidx 11#5) 12 tableBytes
    (rX_x12_run state 12 thresholdAt) (rX_x11_run state tableBytes tableAt)

/-- Exact `0x130d4: bltu a2,a1,0x130dc`. -/
theorem checkedSlice3541HasNextBranchStep
    (stepNo stackPointer tableBytes : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130d4)
    (tableAt : state.regs.get? x11 = some (BitVec.ofNat 64 tableBytes))
    (thresholdAt : state.regs.get? x12 = some 12)
    (comparison : zopz0zI_u 12 (BitVec.ofNat 64 tableBytes) = taken)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if taken then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x130d4 0x130dc)
          0x130dc retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130d4)
          0x130d8 retired) false := by
  cases taken
  · apply configuredBranchNotTakenStep stepNo 0x130d4 state 8 (.Regidx 11#5)
      (.Regidx 12#5) .BLTU 0x63 0x64 0xb6 0x00 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice3541HasNextRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130d4)
        (BitVec.ofNat 64 tableBytes)
        ((stepPremiseState_writes state 0x130d4).get x11 (by decide) |>.trans tableAt)
        ((stepPremiseState_writes state 0x130d4).get x12 (by decide) |>.trans thresholdAt)
  · apply configuredBranchTakenStep stepNo 0x130d4 0x130dc state 8 (.Regidx 11#5)
      (.Regidx 12#5) .BLTU 0x63 0x64 0xb6 0x00 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice3541HasNextRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130d4)
        (BitVec.ofNat 64 tableBytes)
        ((stepPremiseState_writes state 0x130d4).get x11 (by decide) |>.trans tableAt)
        ((stepPremiseState_writes state 0x130d4).get x12 (by decide) |>.trans thresholdAt)
    all_goals native_decide

/-- Exact `0x130d8: sd a0,0x170(sp)`. -/
theorem checkedSlice3541StoreLengthStep (stepNo stackPointer length : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130d8)
    (lengthAt : state.regs.get? x10 = some (BitVec.ofNat 64 length))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x130d8)
          (stackPointer + 0x170) (BitVec.ofNat 64 length))
        0x130d8 retired) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordStoreStep stepNo 0x130d8 stackPointer 0x170 state
    (BitVec.ofNat 64 length) 0x170 (.Regidx 10#5) 0x23 0x38 0xa1 0x16
    access.configured atPc access.stackRead (access.storePma 0x170 (by omega))
    (access.storeNoMMIO 0x170 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x170#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := access.configured.storeDecodeContext
    configured_decode access.configured
  · intro premise writes
    exact rX_x10_run premise _ ((writes.get x10 (by decide)).trans lengthAt)

/-- Select and store the type-two end offset, including the last-entry fallback to input length. -/
theorem checkedSlice3541EndPrefix
    (fromStep stackPointer length tableBytes candidateEnd : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130c8)
    (lengthAt : state.regs.get? x10 = some (BitVec.ofNat 64 length))
    (lengthFits : length < 2 ^ 64)
    (tableAt : state.regs.get? x11 = some (BitVec.ofNat 64 tableBytes))
    (candidateRep : UIntRep 8 state.mem (stackPointer + 0x500) candidateEnd)
    (comparison : zopz0zI_u 12 (BitVec.ofNat 64 tableBytes) = hasNext)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after,
      Seg checkedSlice3541OwnPc checkedSlice3541ExitPc (fun _ _ _ _ _ => False)
        checkedSlice3541Writes (checkedSlice3541Memory stackPointer)
        [⟨x12, 12⟩, ⟨x13, BitVec.ofNat 64 candidateEnd⟩]
        fromStep (if hasNext then 4 else 5) state after 0x130dc ∧
      UIntRep 8 after.mem (stackPointer + 0x170) (if hasNext then candidateEnd else length) := by
  obtain ⟨retired, retiredRead⟩ := access.configured.retiredCounter
  have seg0 := Seg.nil checkedSlice3541OwnPc checkedSlice3541ExitPc
    (fun _ _ _ _ _ => False) checkedSlice3541Writes
    (checkedSlice3541Memory stackPointer) fromStep ⟨retired, retiredRead⟩ atPc
  obtain ⟨s1, seg1⟩ := seg0.step
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList]) x13
    (BitVec.ofNat 64 candidateEnd) 0x130cc
    (checkedSlice3541LoadCandidateEndStep fromStep stackPointer candidateEnd state access atPc
      candidateRep loaded)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [checkedSlice3541Writes]) (by decide) (by decide) (by simp [RegsOutside])
  obtain ⟨s2, seg2⟩ := seg1.step
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList]) x12 12 0x130d0
    (checkedSlice3541LoadThresholdStep (fromStep + 1) s1
      (checkedSlice3541AccessOfSeg access seg1).configured seg1.atPc
      (checkedSlice3541CodeOfSeg access loaded seg1))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [checkedSlice3541Writes]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨retired3, s3, s3Eq, seg3⟩ := seg2.stepStoreWitness
    (width := 8) (stackPointer + 0x170) (BitVec.ofNat 64 candidateEnd) 0x130d4
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList])
    (checkedSlice3541StoreCandidateEndStep (fromStep + 2) stackPointer candidateEnd s2
      (checkedSlice3541AccessOfSeg access seg2) seg2.atPc
      (seg2.reg x13 (BitVec.ofNat 64 candidateEnd) (by simp))
      (checkedSlice3541CodeOfSeg access loaded seg2))
    (by native_decide)
    (by intro address lower upper; exact ⟨lower, upper⟩)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have storedCandidate : UIntRep 8 s3.mem (stackPointer + 0x170) candidateEnd := by
    rw [s3Eq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement s2) 0x130d0)
        (stackPointer + 0x170) candidateEnd candidateRep.1 (by
          have stackFits := access.stackFits
          omega)
  have tableAt3 : s3.regs.get? x11 = some (BitVec.ofNat 64 tableBytes) :=
    (seg3.get x11 (by simp [checkedSlice3541Writes, stepBookkeeping])).trans tableAt
  cases hasNext
  · obtain ⟨s4, seg4⟩ := seg3.stepFallThrough 0x130d8
      (by owned_pc [checkedSlice3541OwnPc, pcInList])
      (by owned_pc [checkedSlice3541ExitPc, pcInList])
      (checkedSlice3541HasNextBranchStep (fromStep + 3) stackPointer tableBytes s3
        (checkedSlice3541AccessOfSeg access seg3) seg3.atPc tableAt3
        (seg3.reg x12 12 (by simp)) comparison
        (checkedSlice3541CodeOfSeg access loaded seg3))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    have lengthAt4 : s4.regs.get? x10 = some (BitVec.ofNat 64 length) :=
      (seg4.get x10 (by simp [checkedSlice3541Writes, stepBookkeeping])).trans lengthAt
    obtain ⟨retired5, s5, s5Eq, seg5⟩ := seg4.stepStoreWitness
      (width := 8) (stackPointer + 0x170) (BitVec.ofNat 64 length) 0x130dc
      (by owned_pc [checkedSlice3541OwnPc, pcInList])
      (by owned_pc [checkedSlice3541ExitPc, pcInList])
      (checkedSlice3541StoreLengthStep (fromStep + 4) stackPointer length s4
        (checkedSlice3541AccessOfSeg access seg4) seg4.atPc lengthAt4
        (checkedSlice3541CodeOfSeg access loaded seg4))
      (by native_decide)
      (by intro address lower upper; exact ⟨lower, upper⟩)
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    refine ⟨s5, ?_, ?_⟩
    · simpa only [if_false, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seg5
    · rw [s5Eq]
      simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
        uintRep_afterWriteBytes_eight
          (coreStoreNextState (tryStepStoreAfterIncrement s4) 0x130d8)
          (stackPointer + 0x170) length lengthFits (by
            have stackFits := access.stackFits
            omega)
  · obtain ⟨retired4, s4, s4Eq, seg4⟩ := seg3.stepJumpWitness 0x130dc
      (by owned_pc [checkedSlice3541OwnPc, pcInList])
      (by owned_pc [checkedSlice3541ExitPc, pcInList])
      (checkedSlice3541HasNextBranchStep (fromStep + 3) stackPointer tableBytes s3
        (checkedSlice3541AccessOfSeg access seg3) seg3.atPc tableAt3
        (seg3.reg x12 12 (by simp)) comparison
        (checkedSlice3541CodeOfSeg access loaded seg3))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    refine ⟨s4, ?_, ?_⟩
    · simpa only [if_true, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seg4
    · rw [s4Eq]
      simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using storedCandidate

/-- Exact `0x130dc: ld a2,0x198(sp)`. -/
theorem checkedSlice3541LoadStartStep (stepNo stackPointer startOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130dc)
    (rep : UIntRep 8 state.mem (stackPointer + 0x198) startOffset)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130dc retired x12 (BitVec.ofNat 64 startOffset)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x130dc stackPointer 0x198 startOffset state
    0x198 (.Regidx 12#5) x12 (BitVec.ofNat 64 startOffset) 0x03 0x36 0x81 0x19
    access.configured atPc access.stackRead rep (access.loadPma 0x198 (by omega))
    (access.loadNoMMIO 0x198 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x198#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x12_run premise (BitVec.ofNat 64 startOffset)
  · configured_decode access.configured

/-- Exact `0x130e0: ld a4,0x170(sp)`. -/
theorem checkedSlice3541LoadEndStep (stepNo stackPointer endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130e0)
    (rep : UIntRep 8 state.mem (stackPointer + 0x170) endOffset)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130e0 retired x14 (BitVec.ofNat 64 endOffset)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x130e0 stackPointer 0x170 endOffset state
    0x170 (.Regidx 14#5) x14 (BitVec.ofNat 64 endOffset) 0x03 0x37 0x01 0x17
    access.configured atPc access.stackRead rep (access.loadPma 0x170 (by omega))
    (access.loadNoMMIO 0x170 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x170#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x14_run premise (BitVec.ofNat 64 endOffset)
  · configured_decode access.configured

private theorem checkedSlice3541ReversedRun (state : State) (startOffset endOffset : BitVec 64)
    (startAt : state.regs.get? x12 = some startOffset)
    (endAt : state.regs.get? x14 = some endOffset) :
    Runs (bTypeTaken (.Regidx 12#5) (.Regidx 14#5) .BLTU) state state
      (zopz0zI_u endOffset startOffset) :=
  bltuConditionRun state (.Regidx 14#5) (.Regidx 12#5) endOffset startOffset
    (rX_x14_run state endOffset endAt) (rX_x12_run state startOffset startAt)

/-- Exact `0x130e4: bltu a4,a2,0x13db0`. -/
theorem checkedSlice3541ReversedBranchStep
    (stepNo stackPointer startOffset endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130e4)
    (startAt : state.regs.get? x12 = some (BitVec.ofNat 64 startOffset))
    (endAt : state.regs.get? x14 = some (BitVec.ofNat 64 endOffset))
    (comparison : zopz0zI_u (BitVec.ofNat 64 endOffset)
      (BitVec.ofNat 64 startOffset) = taken)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if taken then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x130e4 0x13db0)
          0x13db0 retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130e4)
          0x130e8 retired) false := by
  cases taken
  · apply configuredBranchNotTakenStep stepNo 0x130e4 state 0xccc (.Regidx 12#5)
      (.Regidx 14#5) .BLTU 0xe3 0x66 0xc7 0x4c access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice3541ReversedRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130e4)
        (BitVec.ofNat 64 startOffset) (BitVec.ofNat 64 endOffset)
        ((stepPremiseState_writes state 0x130e4).get x12 (by decide) |>.trans startAt)
        ((stepPremiseState_writes state 0x130e4).get x14 (by decide) |>.trans endAt)
  · apply configuredBranchTakenStep stepNo 0x130e4 0x13db0 state 0xccc (.Regidx 12#5)
      (.Regidx 14#5) .BLTU 0xe3 0x66 0xc7 0x4c access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice3541ReversedRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130e4)
        (BitVec.ofNat 64 startOffset) (BitVec.ofNat 64 endOffset)
        ((stepPremiseState_writes state 0x130e4).get x12 (by decide) |>.trans startAt)
        ((stepPremiseState_writes state 0x130e4).get x14 (by decide) |>.trans endAt)
    all_goals native_decide

/-- Exact `0x130e8: ld s8,0x1b0(sp)`. -/
theorem checkedSlice3541LoadS8Step (stepNo stackPointer value : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130e8)
    (rep : UIntRep 8 state.mem (stackPointer + 0x1b0) value)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130e8 retired x24 (BitVec.ofNat 64 value)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x130e8 stackPointer 0x1b0 value state
    0x1b0 (.Regidx 24#5) x24 (BitVec.ofNat 64 value) 0x03 0x3c 0x01 0x1b
    access.configured atPc access.stackRead rep (access.loadPma 0x1b0 (by omega))
    (access.loadNoMMIO 0x1b0 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x1b0#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x24_run premise (BitVec.ofNat 64 value)
  · configured_decode access.configured

/-- Exact `0x130ec: ld s11,0x1a8(sp)`. -/
theorem checkedSlice3541LoadS11Step (stepNo stackPointer value : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130ec)
    (rep : UIntRep 8 state.mem (stackPointer + 0x1a8) value)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130ec retired x27 (BitVec.ofNat 64 value)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x130ec stackPointer 0x1a8 value state
    0x1a8 (.Regidx 27#5) x27 (BitVec.ofNat 64 value) 0x83 0x3d 0x81 0x1a
    access.configured atPc access.stackRead rep (access.loadPma 0x1a8 (by omega))
    (access.loadNoMMIO 0x1a8 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x1a8#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x27_run premise (BitVec.ofNat 64 value)
  · configured_decode access.configured

/-- Exact `0x130f0: li s6,1`. -/
theorem checkedSlice3541LoadSuccessTagStep (stepNo : Nat) (state : State)
    (access : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x130f0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130f0 retired x22 1) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130f0
  have execute : Runs (execute (.ITYPE (1, .Regidx 0#5, .Regidx 22#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x22 1 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 1 (.Regidx 0#5) (.Regidx 22#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 1 0 = 1#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 1 (.Regidx 0#5)
      (.Regidx 22#5) .ADDI 0 (rX_x0_run premise) (wX_x22_run premise _)
  exact configuredRegisterWriteStep stepNo 0x130f0 state x22 1
    (.ITYPE (1, .Regidx 0#5, .Regidx 22#5, .ADDI)) 0x13 0x0b 0x10 0x00
    access atPc loaded (by configured_decode access) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x130f4: ld a2,0x170(sp)`. -/
theorem checkedSlice3541ReloadEndStep (stepNo stackPointer endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130f4)
    (rep : UIntRep 8 state.mem (stackPointer + 0x170) endOffset)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x130f4 retired x12 (BitVec.ofNat 64 endOffset)) false := by
  have stackFits := access.stackFits
  have stackAligned := access.stackAligned
  apply configuredStackDwordLoadStep stepNo 0x130f4 stackPointer 0x170 endOffset state
    0x170 (.Regidx 12#5) x12 (BitVec.ofNat 64 endOffset) 0x03 0x36 0x01 0x17
    access.configured atPc access.stackRead rep (access.loadPma 0x170 (by omega))
    (access.loadNoMMIO 0x170 (by omega)) (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x170#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x12_run premise (BitVec.ofNat 64 endOffset)
  · configured_decode access.configured

private theorem checkedSlice3541OversizedRun (state : State) (length endOffset : BitVec 64)
    (lengthAt : state.regs.get? x10 = some length)
    (endAt : state.regs.get? x12 = some endOffset) :
    Runs (bTypeTaken (.Regidx 12#5) (.Regidx 10#5) .BLTU) state state
      (zopz0zI_u length endOffset) :=
  bltuConditionRun state (.Regidx 10#5) (.Regidx 12#5) length endOffset
    (rX_x10_run state length lengthAt) (rX_x12_run state endOffset endAt)

/-- Exact `0x130f8: bltu a0,a2,0x1230c`. -/
theorem checkedSlice3541OversizedBranchStep
    (stepNo stackPointer length endOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130f8)
    (lengthAt : state.regs.get? x10 = some (BitVec.ofNat 64 length))
    (endAt : state.regs.get? x12 = some (BitVec.ofNat 64 endOffset))
    (comparison : zopz0zI_u (BitVec.ofNat 64 length)
      (BitVec.ofNat 64 endOffset) = taken)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if taken then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x130f8 0x1230c)
          0x1230c retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130f8)
          0x130fc retired) false := by
  cases taken
  · apply configuredBranchNotTakenStep stepNo 0x130f8 state 0x1214 (.Regidx 12#5)
      (.Regidx 10#5) .BLTU 0x63 0x6a 0xc5 0xa0 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice3541OversizedRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130f8)
        (BitVec.ofNat 64 length) (BitVec.ofNat 64 endOffset)
        ((stepPremiseState_writes state 0x130f8).get x10 (by decide) |>.trans lengthAt)
        ((stepPremiseState_writes state 0x130f8).get x12 (by decide) |>.trans endAt)
  · apply configuredBranchTakenStep stepNo 0x130f8 0x1230c state 0x1214 (.Regidx 12#5)
      (.Regidx 10#5) .BLTU 0x63 0x6a 0xc5 0xa0 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice3541OversizedRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x130f8)
        (BitVec.ofNat 64 length) (BitVec.ofNat 64 endOffset)
        ((stepPremiseState_writes state 0x130f8).get x10 (by decide) |>.trans lengthAt)
        ((stepPremiseState_writes state 0x130f8).get x12 (by decide) |>.trans endAt)
    all_goals native_decide

/-- Extend a type-two end-selection prefix through the reversed-bounds rejection. -/
private theorem checkedSlice3541InvalidFromJoin
    (fromStep prefixCount stackPointer candidateEnd startOffset endOffset : Nat)
    (base join : State) (access : CheckedSliceMachineAccess stackPointer base)
    (prefixSeg : Seg checkedSlice3541OwnPc checkedSlice3541ExitPc
      (fun _ _ _ _ _ => False) checkedSlice3541Writes
      (checkedSlice3541Memory stackPointer)
      [⟨x12, 12⟩, ⟨x13, BitVec.ofNat 64 candidateEnd⟩]
      fromStep prefixCount base join 0x130dc)
    (startRep : UIntRep 8 join.mem (stackPointer + 0x198) startOffset)
    (endRep : UIntRep 8 join.mem (stackPointer + 0x170) endOffset)
    (invalid : zopz0zI_u (BitVec.ofNat 64 endOffset)
      (BitVec.ofNat 64 startOffset) = true)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem) :
    ∃ after,
      Seg checkedSlice3541OwnPc checkedSlice3541ExitPc (fun _ _ _ _ _ => False)
        checkedSlice3541Writes (checkedSlice3541Memory stackPointer)
        [⟨x14, BitVec.ofNat 64 endOffset⟩, ⟨x12, BitVec.ofNat 64 startOffset⟩,
          ⟨x13, BitVec.ofNat 64 candidateEnd⟩]
        fromStep (prefixCount + 3) base after 0x13db0 := by
  have prefixSeg' := prefixSeg.forget
    (kv' := [⟨x13, BitVec.ofNat 64 candidateEnd⟩]) (by simp)
  obtain ⟨startRetired, started, startedEq, startSeg⟩ := prefixSeg'.stepWitness
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList]) x12
    (BitVec.ofNat 64 startOffset) 0x130e0
    (checkedSlice3541LoadStartStep
      (fromStep + prefixCount) stackPointer startOffset join
      (checkedSlice3541AccessOfSeg access prefixSeg) prefixSeg.atPc startRep
      (checkedSlice3541CodeOfSeg access loaded prefixSeg))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [checkedSlice3541Writes]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have endRepStarted : UIntRep 8 started.mem (stackPointer + 0x170) endOffset := by
    rw [startedEq]
    exact endRep.of_mem_eq
      (afterRegisterWrite_mem join 0x130dc startRetired x12
        (BitVec.ofNat 64 startOffset))
  obtain ⟨ended, endSeg⟩ := startSeg.step
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList]) x14
    (BitVec.ofNat 64 endOffset) 0x130e4
    (checkedSlice3541LoadEndStep
      (fromStep + prefixCount + 1) stackPointer endOffset started
      (checkedSlice3541AccessOfSeg access startSeg) startSeg.atPc endRepStarted
      (checkedSlice3541CodeOfSeg access loaded startSeg))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [checkedSlice3541Writes]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨after, finalSeg⟩ := endSeg.stepJump 0x13db0
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList])
    (checkedSlice3541ReversedBranchStep
      (fromStep + prefixCount + 2) stackPointer startOffset endOffset ended
      (checkedSlice3541AccessOfSeg access endSeg) endSeg.atPc
      (endSeg.reg x12 (BitVec.ofNat 64 startOffset) (by simp))
      (endSeg.reg x14 (BitVec.ofNat 64 endOffset) (by simp))
      invalid (checkedSlice3541CodeOfSeg access loaded endSeg))
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  exact ⟨after, by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalSeg⟩

/-- The type-two instance rejects a selected end offset that precedes its start offset. -/
theorem checkedSlice3541InvalidStartEndRun
    (fromStep stackPointer length tableBytes candidateEnd startOffset : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130c8)
    (lengthAt : state.regs.get? x10 = some (BitVec.ofNat 64 length))
    (lengthFits : length < 2 ^ 64)
    (tableAt : state.regs.get? x11 = some (BitVec.ofNat 64 tableBytes))
    (candidateRep : UIntRep 8 state.mem (stackPointer + 0x500) candidateEnd)
    (startRep : UIntRep 8 state.mem (stackPointer + 0x198) startOffset)
    (comparison : zopz0zI_u 12 (BitVec.ofNat 64 tableBytes) = hasNext)
    (invalid : zopz0zI_u
      (BitVec.ofNat 64 (if hasNext then candidateEnd else length))
      (BitVec.ofNat 64 startOffset) = true)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after,
      Seg checkedSlice3541OwnPc checkedSlice3541ExitPc (fun _ _ _ _ _ => False)
        checkedSlice3541Writes (checkedSlice3541Memory stackPointer)
        [⟨x14, BitVec.ofNat 64 (if hasNext then candidateEnd else length)⟩,
          ⟨x12, BitVec.ofNat 64 startOffset⟩,
          ⟨x13, BitVec.ofNat 64 candidateEnd⟩]
        fromStep (if hasNext then 7 else 8) state after 0x13db0 := by
  obtain ⟨join, prefixSeg, endRep⟩ := checkedSlice3541EndPrefix fromStep stackPointer
    length tableBytes candidateEnd state access atPc lengthAt lengthFits tableAt candidateRep
    comparison loaded
  have startRepJoin : UIntRep 8 join.mem (stackPointer + 0x198) startOffset :=
    startRep.of_writesOnlyWithin prefixSeg.mem (by
      intro index indexBound inside
      unfold checkedSlice3541Memory byteRange at inside
      omega)
  obtain ⟨after, finalSeg⟩ := checkedSlice3541InvalidFromJoin fromStep
    (if hasNext then 4 else 5) stackPointer candidateEnd startOffset
    (if hasNext then candidateEnd else length) state join access prefixSeg startRepJoin endRep
    invalid loaded
  refine ⟨after, ?_⟩
  cases hasNext <;>
    simpa only [if_false, if_true, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalSeg

/-- Extend a type-two end-selection prefix through the valid-start and length checks. -/
private theorem checkedSlice3541LengthCheckedFromJoin
    (fromStep prefixCount stackPointer candidateEnd startOffset endOffset savedS8 savedS11 length : Nat)
    (base join : State) (access : CheckedSliceMachineAccess stackPointer base)
    (lengthAt : base.regs.get? x10 = some (BitVec.ofNat 64 length))
    (prefixSeg : Seg checkedSlice3541OwnPc checkedSlice3541ExitPc
      (fun _ _ _ _ _ => False) checkedSlice3541Writes
      (checkedSlice3541Memory stackPointer)
      [⟨x12, 12⟩, ⟨x13, BitVec.ofNat 64 candidateEnd⟩]
      fromStep prefixCount base join 0x130dc)
    (startRep : UIntRep 8 base.mem (stackPointer + 0x198) startOffset)
    (endRep : UIntRep 8 join.mem (stackPointer + 0x170) endOffset)
    (savedS8Rep : UIntRep 8 base.mem (stackPointer + 0x1b0) savedS8)
    (savedS11Rep : UIntRep 8 base.mem (stackPointer + 0x1a8) savedS11)
    (startEndValid : zopz0zI_u (BitVec.ofNat 64 endOffset)
      (BitVec.ofNat 64 startOffset) = false)
    (lengthComparison : zopz0zI_u (BitVec.ofNat 64 length)
      (BitVec.ofNat 64 endOffset) = rejected)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem) :
    ∃ after,
      Seg checkedSlice3541OwnPc checkedSlice3541ExitPc (fun _ _ _ _ _ => False)
        checkedSlice3541Writes (checkedSlice3541Memory stackPointer)
        [⟨x12, BitVec.ofNat 64 endOffset⟩, ⟨x22, 1⟩,
          ⟨x27, BitVec.ofNat 64 savedS11⟩, ⟨x24, BitVec.ofNat 64 savedS8⟩,
          ⟨x14, BitVec.ofNat 64 endOffset⟩, ⟨x13, BitVec.ofNat 64 candidateEnd⟩]
        fromStep (prefixCount + 8) base after (if rejected then 0x1230c else 0x130fc) := by
  have startRepJoin : UIntRep 8 join.mem (stackPointer + 0x198) startOffset :=
    startRep.of_writesOnlyWithin prefixSeg.mem (by
      intro index indexBound inside
      unfold checkedSlice3541Memory byteRange at inside
      omega)
  have prefixSeg' := prefixSeg.forget
    (kv' := [⟨x13, BitVec.ofNat 64 candidateEnd⟩]) (by simp)
  obtain ⟨startRetired, started, startedEq, startSeg⟩ := prefixSeg'.stepWitness
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList]) x12
    (BitVec.ofNat 64 startOffset) 0x130e0
    (checkedSlice3541LoadStartStep (fromStep + prefixCount) stackPointer startOffset join
      (checkedSlice3541AccessOfSeg access prefixSeg) prefixSeg.atPc startRepJoin
      (checkedSlice3541CodeOfSeg access loaded prefixSeg))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [checkedSlice3541Writes]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have endRepStarted : UIntRep 8 started.mem (stackPointer + 0x170) endOffset := by
    rw [startedEq]
    exact endRep.of_mem_eq
      (afterRegisterWrite_mem join 0x130dc startRetired x12 (BitVec.ofNat 64 startOffset))
  obtain ⟨endRetired, ended, endedEq, endSeg⟩ := startSeg.stepWitness
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList]) x14
    (BitVec.ofNat 64 endOffset) 0x130e4
    (checkedSlice3541LoadEndStep (fromStep + prefixCount + 1) stackPointer endOffset started
      (checkedSlice3541AccessOfSeg access startSeg) startSeg.atPc endRepStarted
      (checkedSlice3541CodeOfSeg access loaded startSeg))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [checkedSlice3541Writes]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have endRepEnded : UIntRep 8 ended.mem (stackPointer + 0x170) endOffset := by
    rw [endedEq]
    exact endRepStarted.of_mem_eq
      (afterRegisterWrite_mem started 0x130e0 endRetired x14 (BitVec.ofNat 64 endOffset))
  obtain ⟨branchRetired, checked, checkedEq, checkedSeg⟩ := endSeg.stepFallThroughWitness 0x130e8
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList])
    (checkedSlice3541ReversedBranchStep (fromStep + prefixCount + 2) stackPointer
      startOffset endOffset ended (checkedSlice3541AccessOfSeg access endSeg) endSeg.atPc
      (endSeg.reg x12 (BitVec.ofNat 64 startOffset) (by simp))
      (endSeg.reg x14 (BitVec.ofNat 64 endOffset) (by simp)) startEndValid
      (checkedSlice3541CodeOfSeg access loaded endSeg))
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have endRepChecked : UIntRep 8 checked.mem (stackPointer + 0x170) endOffset := by
    rw [checkedEq]
    exact endRepEnded.of_mem_eq
      (fallThroughRetirement_mem ended 0x130e4 0x130e8 branchRetired)
  have savedS8Checked : UIntRep 8 checked.mem (stackPointer + 0x1b0) savedS8 :=
    savedS8Rep.of_writesOnlyWithin checkedSeg.mem (by
      intro index indexBound inside
      unfold checkedSlice3541Memory byteRange at inside
      omega)
  obtain ⟨s8Retired, loadedS8, loadedS8Eq, s8Seg⟩ := checkedSeg.stepWitness
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList]) x24
    (BitVec.ofNat 64 savedS8) 0x130ec
    (checkedSlice3541LoadS8Step (fromStep + prefixCount + 3) stackPointer savedS8 checked
      (checkedSlice3541AccessOfSeg access checkedSeg) checkedSeg.atPc savedS8Checked
      (checkedSlice3541CodeOfSeg access loaded checkedSeg))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [checkedSlice3541Writes]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have endRepS8 : UIntRep 8 loadedS8.mem (stackPointer + 0x170) endOffset := by
    rw [loadedS8Eq]
    exact endRepChecked.of_mem_eq
      (afterRegisterWrite_mem checked 0x130e8 s8Retired x24 (BitVec.ofNat 64 savedS8))
  have savedS11S8 : UIntRep 8 loadedS8.mem (stackPointer + 0x1a8) savedS11 :=
    savedS11Rep.of_writesOnlyWithin s8Seg.mem (by
      intro index indexBound inside
      unfold checkedSlice3541Memory byteRange at inside
      omega)
  obtain ⟨s11Retired, loadedS11, loadedS11Eq, s11Seg⟩ := s8Seg.stepWitness
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList]) x27
    (BitVec.ofNat 64 savedS11) 0x130f0
    (checkedSlice3541LoadS11Step (fromStep + prefixCount + 4) stackPointer savedS11 loadedS8
      (checkedSlice3541AccessOfSeg access s8Seg) s8Seg.atPc savedS11S8
      (checkedSlice3541CodeOfSeg access loaded s8Seg))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [checkedSlice3541Writes]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have endRepS11 : UIntRep 8 loadedS11.mem (stackPointer + 0x170) endOffset := by
    rw [loadedS11Eq]
    exact endRepS8.of_mem_eq
      (afterRegisterWrite_mem loadedS8 0x130ec s11Retired x27 (BitVec.ofNat 64 savedS11))
  obtain ⟨tagRetired, tagged, taggedEq, tagSeg⟩ := s11Seg.stepWitness
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList]) x22 1 0x130f4
    (checkedSlice3541LoadSuccessTagStep (fromStep + prefixCount + 5) loadedS11
      (checkedSlice3541AccessOfSeg access s11Seg).configured s11Seg.atPc
      (checkedSlice3541CodeOfSeg access loaded s11Seg))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [checkedSlice3541Writes]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have endRepTagged : UIntRep 8 tagged.mem (stackPointer + 0x170) endOffset := by
    rw [taggedEq]
    exact endRepS11.of_mem_eq
      (afterRegisterWrite_mem loadedS11 0x130f0 tagRetired x22 1)
  have tagSeg' := tagSeg.forget
    (kv' := [⟨x22, 1⟩, ⟨x27, BitVec.ofNat 64 savedS11⟩,
      ⟨x24, BitVec.ofNat 64 savedS8⟩, ⟨x14, BitVec.ofNat 64 endOffset⟩,
      ⟨x13, BitVec.ofNat 64 candidateEnd⟩]) (by simp)
  obtain ⟨reloaded, reloadSeg⟩ := tagSeg'.step
    (by owned_pc [checkedSlice3541OwnPc, pcInList])
    (by owned_pc [checkedSlice3541ExitPc, pcInList]) x12
    (BitVec.ofNat 64 endOffset) 0x130f8
    (checkedSlice3541ReloadEndStep (fromStep + prefixCount + 6) stackPointer endOffset tagged
      (checkedSlice3541AccessOfSeg access tagSeg) tagSeg.atPc endRepTagged
      (checkedSlice3541CodeOfSeg access loaded tagSeg))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [checkedSlice3541Writes]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have lengthAtReloaded : reloaded.regs.get? x10 = some (BitVec.ofNat 64 length) :=
    (reloadSeg.get x10 (by simp [checkedSlice3541Writes, stepBookkeeping])).trans lengthAt
  cases rejected
  · obtain ⟨after, finalSeg⟩ := reloadSeg.stepFallThrough 0x130fc
      (by owned_pc [checkedSlice3541OwnPc, pcInList])
      (by owned_pc [checkedSlice3541ExitPc, pcInList])
      (checkedSlice3541OversizedBranchStep (fromStep + prefixCount + 7) stackPointer
        length endOffset reloaded (checkedSlice3541AccessOfSeg access reloadSeg) reloadSeg.atPc
        lengthAtReloaded (reloadSeg.reg x12 (BitVec.ofNat 64 endOffset) (by simp))
        lengthComparison (checkedSlice3541CodeOfSeg access loaded reloadSeg))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by
      simpa only [if_false, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalSeg⟩
  · obtain ⟨after, finalSeg⟩ := reloadSeg.stepJump 0x1230c
      (by owned_pc [checkedSlice3541OwnPc, pcInList])
      (by owned_pc [checkedSlice3541ExitPc, pcInList])
      (checkedSlice3541OversizedBranchStep (fromStep + prefixCount + 7) stackPointer
        length endOffset reloaded (checkedSlice3541AccessOfSeg access reloadSeg) reloadSeg.atPc
        lengthAtReloaded (reloadSeg.reg x12 (BitVec.ofNat 64 endOffset) (by simp))
        lengthComparison (checkedSlice3541CodeOfSeg access loaded reloadSeg))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by
      simpa only [if_true, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalSeg⟩

/-- The type-two instance accepts its start and then checks the selected end against the length. -/
theorem checkedSlice3541LengthCheckedRun
    (fromStep stackPointer length tableBytes candidateEnd startOffset savedS8 savedS11 : Nat)
    (state : State) (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x130c8)
    (lengthAt : state.regs.get? x10 = some (BitVec.ofNat 64 length))
    (lengthFits : length < 2 ^ 64)
    (tableAt : state.regs.get? x11 = some (BitVec.ofNat 64 tableBytes))
    (candidateRep : UIntRep 8 state.mem (stackPointer + 0x500) candidateEnd)
    (startRep : UIntRep 8 state.mem (stackPointer + 0x198) startOffset)
    (savedS8Rep : UIntRep 8 state.mem (stackPointer + 0x1b0) savedS8)
    (savedS11Rep : UIntRep 8 state.mem (stackPointer + 0x1a8) savedS11)
    (hasNextComparison : zopz0zI_u 12 (BitVec.ofNat 64 tableBytes) = hasNext)
    (startEndValid : zopz0zI_u
      (BitVec.ofNat 64 (if hasNext then candidateEnd else length))
      (BitVec.ofNat 64 startOffset) = false)
    (lengthComparison : zopz0zI_u (BitVec.ofNat 64 length)
      (BitVec.ofNat 64 (if hasNext then candidateEnd else length)) = rejected)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after,
      Seg checkedSlice3541OwnPc checkedSlice3541ExitPc (fun _ _ _ _ _ => False)
        checkedSlice3541Writes (checkedSlice3541Memory stackPointer)
        [⟨x12, BitVec.ofNat 64 (if hasNext then candidateEnd else length)⟩, ⟨x22, 1⟩,
          ⟨x27, BitVec.ofNat 64 savedS11⟩, ⟨x24, BitVec.ofNat 64 savedS8⟩,
          ⟨x14, BitVec.ofNat 64 (if hasNext then candidateEnd else length)⟩,
          ⟨x13, BitVec.ofNat 64 candidateEnd⟩]
        fromStep (if hasNext then 12 else 13) state after
          (if rejected then 0x1230c else 0x130fc) := by
  obtain ⟨join, prefixSeg, endRep⟩ := checkedSlice3541EndPrefix fromStep stackPointer
    length tableBytes candidateEnd state access atPc lengthAt lengthFits tableAt candidateRep
    hasNextComparison loaded
  obtain ⟨after, finalSeg⟩ := checkedSlice3541LengthCheckedFromJoin fromStep
    (if hasNext then 4 else 5) stackPointer candidateEnd startOffset
    (if hasNext then candidateEnd else length) savedS8 savedS11 length state join access lengthAt
    prefixSeg startRep endRep savedS8Rep savedS11Rep startEndValid lengthComparison loaded
  refine ⟨after, ?_⟩
  cases hasNext <;>
    simpa only [if_false, if_true, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalSeg

/-! ## Request-type-three checked slice at `0x13100` -/

def checkedSlice3566OwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x13100, 0x13104, 0x13108, 0x1310c, 0x13110, 0x13114, 0x13118,
    0x1311c, 0x13120, 0x13124, 0x13128, 0x1312c, 0x13130, 0x13134, 0x13138,
    0x1313c, 0x13140] pc

def checkedSlice3566ExitPc (pc : BitVec 64) : Prop :=
  pcInList [0x1230c, 0x13144, 0x13198, 0x13db0] pc

def checkedSlice3566Writes : RegSet := fun register =>
  stepBookkeeping register ∨ register = x12 ∨ register = x13 ∨ register = x14 ∨
    register = x15 ∨ register = x22 ∨ register = x24 ∨ register = x27

def checkedSlice3566Memory (stackPointer : Nat) : Region := fun address =>
  byteRange (stackPointer + 0x278) 16 address

private theorem instructionPreserved_disjoint_checkedSlice3566Writes :
    RegSet.Disjoint instructionPreserved checkedSlice3566Writes := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem platformPreserved_disjoint_checkedSlice3566Writes :
    RegSet.Disjoint platformPreserved checkedSlice3566Writes := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved bookkeeping
  all_goals simp [platformPreserved] at preserved

private theorem checkedSlice3566Memory_in_frame {stackPointer address : Nat}
    (inside : checkedSlice3566Memory stackPointer address) :
    checkedSliceFrame stackPointer address := by
  change stackPointer + 0x278 ≤ address ∧ address < stackPointer + 0x278 + 16 at inside
  unfold checkedSliceFrame byteRange
  omega

theorem checkedSlice3566AccessOfSeg {stackPointer : Nat} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (seg : Seg checkedSlice3566OwnPc checkedSlice3566ExitPc
      (fun _ _ _ _ _ => False) checkedSlice3566Writes
      (checkedSlice3566Memory stackPointer) kv fromStep count before after pc) :
    CheckedSliceMachineAccess stackPointer after :=
  access.ofSeg instructionPreserved_disjoint_checkedSlice3566Writes
    platformPreserved_disjoint_checkedSlice3566Writes
    (by intro written; simp [checkedSlice3566Writes, stepBookkeeping] at written) seg

theorem checkedSlice3566CodeOfSeg {stackPointer : Nat} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (access : CheckedSliceMachineAccess stackPointer before)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg checkedSlice3566OwnPc checkedSlice3566ExitPc
      (fun _ _ _ _ _ => False) checkedSlice3566Writes
      (checkedSlice3566Memory stackPointer) kv fromStep count before after pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully after.mem :=
  checkedSliceCodeOfSeg access loaded checkedSlice3566Memory_in_frame seg

private theorem checkedSlice3566PresentRun (state : State) (tableBytes : BitVec 64)
    (tableAt : state.regs.get? x11 = some tableBytes)
    (thresholdAt : state.regs.get? x12 = some 13) :
    Runs (bTypeTaken (.Regidx 12#5) (.Regidx 11#5) .BLTU) state state
      (zopz0zI_u tableBytes 13) :=
  bltuConditionRun state (.Regidx 11#5) (.Regidx 12#5) tableBytes 13
    (rX_x11_run state tableBytes tableAt) (rX_x12_run state 13 thresholdAt)

/-- Exact `0x13100: bltu a1,a2,0x13198`. -/
theorem checkedSlice3566PresentBranchStep
    (stepNo stackPointer tableBytes : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x13100)
    (tableAt : state.regs.get? x11 = some (BitVec.ofNat 64 tableBytes))
    (thresholdAt : state.regs.get? x12 = some 13)
    (comparison : zopz0zI_u (BitVec.ofNat 64 tableBytes) 13 = absent)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if absent then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x13100 0x13198)
          0x13198 retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x13100)
          0x13104 retired) false := by
  cases absent
  · apply configuredBranchNotTakenStep stepNo 0x13100 state 0x98 (.Regidx 12#5)
      (.Regidx 11#5) .BLTU 0x63 0xec 0xc5 0x08 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice3566PresentRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x13100)
        (BitVec.ofNat 64 tableBytes)
        ((stepPremiseState_writes state 0x13100).get x11 (by decide) |>.trans tableAt)
        ((stepPremiseState_writes state 0x13100).get x12 (by decide) |>.trans thresholdAt)
  · apply configuredBranchTakenStep stepNo 0x13100 0x13198 state 0x98 (.Regidx 12#5)
      (.Regidx 11#5) .BLTU 0x63 0xec 0xc5 0x08 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using checkedSlice3566PresentRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x13100)
        (BitVec.ofNat 64 tableBytes)
        ((stepPremiseState_writes state 0x13100).get x11 (by decide) |>.trans tableAt)
        ((stepPremiseState_writes state 0x13100).get x12 (by decide) |>.trans thresholdAt)
    all_goals native_decide

/-- The missing type-three entry returns the source-level empty slice in one instruction. -/
theorem checkedSlice3566EmptyRun
    (fromStep stackPointer tableBytes : Nat) (state : State)
    (access : CheckedSliceMachineAccess stackPointer state)
    (atPc : state.regs.get? PC = some 0x13100)
    (tableAt : state.regs.get? x11 = some (BitVec.ofNat 64 tableBytes))
    (thresholdAt : state.regs.get? x12 = some 13)
    (absent : zopz0zI_u (BitVec.ofNat 64 tableBytes) 13 = true)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after,
      Seg checkedSlice3566OwnPc checkedSlice3566ExitPc (fun _ _ _ _ _ => False)
        checkedSlice3566Writes (checkedSlice3566Memory stackPointer) []
        fromStep 1 state after 0x13198 := by
  obtain ⟨retired, retiredRead⟩ := access.configured.retiredCounter
  have seg0 := Seg.nil checkedSlice3566OwnPc checkedSlice3566ExitPc
    (fun _ _ _ _ _ => False) checkedSlice3566Writes
    (checkedSlice3566Memory stackPointer) fromStep ⟨retired, retiredRead⟩ atPc
  obtain ⟨after, seg1⟩ := seg0.stepJump 0x13198
    (by owned_pc [checkedSlice3566OwnPc, pcInList])
    (by owned_pc [checkedSlice3566ExitPc, pcInList])
    (checkedSlice3566PresentBranchStep fromStep stackPointer tableBytes state access atPc tableAt
      thresholdAt absent loaded)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  exact ⟨after, by simpa only [Nat.zero_add] using seg1⟩

end BinaryFv.Zesu.MachineExecution
