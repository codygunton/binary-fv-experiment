import BinaryFv.Zesu.MachineExecution.HLevel3RawEncoderSteps

/-!
# Shared called-encoder prologue

The Boolean encoder and the Level 2 integer-output parent use the same two instructions:
`addi sp,sp,-16` and `sd ra,8(sp)`. This module proves that instruction sequence once.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

def encoderCallPrologue16Writes (register : Register) : Prop :=
  stepBookkeeping register ∨ register = x2

private theorem instructionPreserved_disjoint_encoderCallPrologue16Writes :
    RegSet.Disjoint instructionPreserved encoderCallPrologue16Writes := by
  intro register preserved written
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  · simp [instructionPreserved, platformPreserved] at preserved

/-- Retire an exact `addi sp,sp,-16` site. -/
theorem encoderCallSubtract16Step (stepNo pc stackPointer : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (lower : 16 ≤ stackPointer) (upper : stackPointer < 2 ^ 64)
    (site : ExactInstructionSite pc 0x13 0x01 0x01 0xff) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x2
        (BitVec.ofNat 64 (stackPointer - 16))) false := by
  exact configuredAddiX2Step stepNo pc state 0xff0
    (BitVec.ofNat 64 stackPointer) (BitVec.ofNat 64 (stackPointer - 16))
    0x13 0x01 0x01 0xff configured atPc stack loaded
    (stackSubtractResult stackPointer 16 0xff0 lower upper (by native_decide))
    (by configured_decode configured) site (by rfl)

/-- Retire the matching exact `sd ra,8(sp)` site. -/
theorem encoderCallSaveReturn16Step (stepNo pc stackPointer returnAddress : Nat) (state : State)
    (access : EncoderCallMachineAccess 16
      { returnAddress := returnAddress, callerStack := stackPointer,
        inputSize := inputSize, value := value } state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (stackPointer - 16)))
    (link : state.regs.get? x1 = some (BitVec.ofNat 64 returnAddress))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (lower : 16 ≤ stackPointer) (upper : stackPointer < 2 ^ 64)
    (site : ExactInstructionSite pc 0x23 0x34 0x11 0x00) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc))
          (stackPointer - 16 + 8) (BitVec.ofNat 64 returnAddress))
        (BitVec.ofNat 64 pc) retired) false := by
  exact configuredStackDwordStoreStep stepNo pc (stackPointer - 16) 8 state
    (BitVec.ofNat 64 returnAddress) 8 (.Regidx 1#5) 0x23 0x34 0x11 0x00
    access.output.configured atPc stack (access.frameStore 8 8 (by omega))
    (access.frameStoreNoMMIO 8 8 (by omega))
    (by
      rcases Nat.dvd_of_mod_eq_zero access.stackAligned with ⟨factor, rfl⟩
      omega)
    (by omega) loaded
    (by
      rw [show sign_extend (m := 64) (8 : BitVec 12) = BitVec.ofNat 64 8 by native_decide]
      change BitVec.ofNat 64 (stackPointer - 16) + BitVec.ofNat 64 8 = _
      rw [← BitVec.ofNat_add])
    (by configured_store_decode access.output.configured)
    (by
      intro premise writes
      exact rX_x1_run premise (BitVec.ofNat 64 returnAddress)
        ((writes.get x1 (by decide)).trans link)) site (by rfl)

private theorem encoderCallPrologue16LoadedOfSeg
    {args : EncoderCallArgs Value} {owned exit kv fromStep count before after pc}
    (access : EncoderCallMachineAccess 16 args before)
    (lower : 16 ≤ args.callerStack)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg owned exit (fun _ _ _ _ _ => False) encoderCallPrologue16Writes
      (byteRange (args.callerStack - 16) 16) kv fromStep count before after pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
  intro address byte fileByte
  have unchanged := seg.mem address (by
    intro inside
    unfold byteRange at inside
    have none := access.frameNotCode address (by omega) (by omega)
    rw [fileByte] at none
    cases none)
  exact unchanged.trans (loaded address byte fileByte)

def EncoderCallPrologue16Handoff (owned exit : BitVec 64 → Prop)
    (entryPc fromStep : Nat) (args : EncoderCallArgs Value) (valueBits : BitVec 64)
    (before after : State) : Prop :=
  Seg owned exit (fun _ _ _ _ _ => False) encoderCallPrologue16Writes
    (byteRange (args.callerStack - 16) 16)
    [⟨x2, BitVec.ofNat 64 (args.callerStack - 16)⟩,
      ⟨x10, valueBits⟩, ⟨x1, BitVec.ofNat 64 args.returnAddress⟩]
    fromStep 2 before after (BitVec.ofNat 64 (entryPc + 8)) ∧
  EncoderCallMachineAccess 16 args after ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.mem ∧
  UIntRep 8 after.mem (args.callerStack - 16 + 8) args.returnAddress

/-- Compose the common 16-byte called-encoder prologue before either concrete parent uses it. -/
theorem encoderCallPrologue16Seg
    {owned exit : BitVec 64 → Prop} (entryPc fromStep : Nat)
    (args : EncoderCallArgs Value) (valueBits : BitVec 64) (before : State)
    (lower : 16 ≤ args.callerStack) (stackFits : args.callerStack < 2 ^ 64)
    (returnFits : args.returnAddress < 2 ^ 64)
    (atPc : before.regs.get? PC = some (BitVec.ofNat 64 entryPc))
    (link : before.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress))
    (stack : before.regs.get? x2 = some (BitVec.ofNat 64 args.callerStack))
    (valueReg : before.regs.get? x10 = some valueBits)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (access : EncoderCallMachineAccess 16 args before)
    (subtractSite : ExactInstructionSite entryPc 0x13 0x01 0x01 0xff)
    (saveSite : ExactInstructionSite (entryPc + 4) 0x23 0x34 0x11 0x00)
    (subtractInside : owned (BitVec.ofNat 64 entryPc))
    (saveInside : owned (BitVec.ofNat 64 (entryPc + 4)))
    (subtractNotExit : ¬exit (BitVec.ofNat 64 entryPc))
    (saveNotExit : ¬exit (BitVec.ofNat 64 (entryPc + 4))) :
    ∃ after, EncoderCallPrologue16Handoff owned exit entryPc fromStep args valueBits before after := by
  let frameBase := args.callerStack - 16
  have seg0 := (((Seg.nil owned exit (fun _ _ _ _ _ => False) encoderCallPrologue16Writes
    (byteRange frameBase 16) fromStep access.output.configured.retiredCounter atPc).know
      x1 (BitVec.ofNat 64 args.returnAddress) link).know
      x2 (BitVec.ofNat 64 args.callerStack) stack).know x10 valueBits valueReg
  obtain ⟨retired0, run0⟩ := encoderCallSubtract16Step fromStep entryPc args.callerStack
    before access.output.configured atPc stack loaded lower stackFits subtractSite
  have seg0' := seg0.forget
    (kv' := [⟨x10, valueBits⟩, ⟨x1, BitVec.ofNat 64 args.returnAddress⟩]) (by simp)
  obtain ⟨retired0', machine1, machine1Eq, seg1⟩ := seg0'.stepWitness
    subtractInside subtractNotExit x2 (BitVec.ofNat 64 frameBase)
    (BitVec.ofNat 64 (entryPc + 4)) ⟨retired0, by simpa [frameBase] using run0⟩
    subtractSite.advance (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [encoderCallPrologue16Writes]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have configured1 := access.output.configured.mono
    (seg1.agree instructionPreserved_disjoint_encoderCallPrologue16Writes) seg1.retired
  have access1 := access.ofWrites seg1.writes
    (by simp [encoderCallPrologue16Writes, stepBookkeeping]) configured1
  have loaded1 := encoderCallPrologue16LoadedOfSeg access lower loaded seg1
  obtain ⟨retired1, run1⟩ := encoderCallSaveReturn16Step (fromStep + 1) (entryPc + 4)
    args.callerStack args.returnAddress machine1 access1 seg1.atPc
    (by simpa [frameBase] using seg1.reg x2 (BitVec.ofNat 64 frameBase) (by simp))
    (seg1.reg x1 _ (by simp)) loaded1 lower stackFits saveSite
  obtain ⟨retired1', machine2, machine2Eq, seg2⟩ := seg1.stepStoreWitness
    (width := 8) (frameBase + 8) (BitVec.ofNat 64 args.returnAddress)
    (BitVec.ofNat 64 (entryPc + 8)) saveInside saveNotExit
    ⟨retired1, by simpa [frameBase] using run1⟩ saveSite.advance
    (by intro address lower' upper; unfold frameBase byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have saved : UIntRep 8 machine2.mem (frameBase + 8) args.returnAddress := by
    rw [machine2Eq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement machine1)
          (BitVec.ofNat 64 (entryPc + 4)))
        (frameBase + 8) args.returnAddress returnFits (by omega)
  refine ⟨machine2, ?_, ?_, ?_, ?_⟩
  · simpa [EncoderCallPrologue16Handoff, frameBase, Nat.add_assoc] using seg2
  · exact access.ofWrites seg2.writes
      (by simp [encoderCallPrologue16Writes, stepBookkeeping])
      (access.output.configured.mono
        (seg2.agree instructionPreserved_disjoint_encoderCallPrologue16Writes) seg2.retired)
  · exact encoderCallPrologue16LoadedOfSeg access lower loaded seg2
  · simpa [frameBase] using saved

end BinaryFv.Zesu.MachineExecution
