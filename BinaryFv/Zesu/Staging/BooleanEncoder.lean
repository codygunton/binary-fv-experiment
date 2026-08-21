import BinaryFv.Zesu.MachineExecution.EncoderCallFinish
import BinaryFv.Zesu.Staging.RawEncoder

/-!
# The Level 3 Boolean encoder proof

The production Boolean encoder writes one stack byte, reuses the proved `Encoder.raw` child, and
uses the shared called-encoder return theorem.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

def booleanEncoderPrefixWrites (register : Register) : Prop :=
  stepBookkeeping register ∨ register = x2 ∨ register = x10

private theorem instructionPreserved_disjoint_booleanEncoderPrefixWrites :
    RegSet.Disjoint instructionPreserved booleanEncoderPrefixWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem abiCalleePreserved_booleanEncoder_cases {register : Register}
    (preserved : abiCalleePreserved register) :
    register = x1 ∨ register = x2 ∨
      (¬booleanEncoderPrefixWrites register ∧ encoderInlinePreserved register ∧
        ¬encoderCallFinishWrites register) := by
  simp [abiCalleePreserved, booleanEncoderPrefixWrites, encoderInlinePreserved,
    encoderCallFinishWrites, instructionPreserved, platformPreserved, stepBookkeeping] at preserved ⊢
  grind

private theorem EncoderCallMachineAccess.ofBooleanSeg
    {args : EncoderCallArgs Bool} {owned exit kv fromStep count before after pc}
    (access : EncoderCallMachineAccess 16 args before)
    (seg : Seg owned exit (fun _ _ _ _ _ => False) booleanEncoderPrefixWrites
      (byteRange (args.callerStack - 16) 16) kv fromStep count before after pc) :
    EncoderCallMachineAccess 16 args after := by
  have pmaEq := seg.writes.get pma_regions (by
    simp [booleanEncoderPrefixWrites, stepBookkeeping])
  exact
    { output :=
        { configured := access.output.configured.mono
            (seg.agree instructionPreserved_disjoint_booleanEncoderPrefixWrites) seg.retired
          outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputBufferStore
          outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputLengthStore
          outputBufferNoMMIO := access.output.outputBufferNoMMIO
          outputLengthNoMMIO := access.output.outputLengthNoMMIO }
      stackAligned := access.stackAligned
      frameOutputDisjoint := access.frameOutputDisjoint
      frameLoad := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameLoad offset width bound)
      frameStore := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameStore offset width bound)
      frameLoadNoMMIO := access.frameLoadNoMMIO
      frameStoreNoMMIO := access.frameStoreNoMMIO
      frameNotCode := access.frameNotCode }

private theorem EncoderCallMachineAccess.ofEncoderInlineFrame
    {args : EncoderCallArgs Bool} {before after : State}
    (access : EncoderCallMachineAccess 16 args before)
    (agree : Agree encoderInlinePreserved before after)
    (retired : RetiredCounterPresent after) : EncoderCallMachineAccess 16 args after := by
  have instructionAgree : Agree instructionPreserved before after :=
    agree.weaken (fun _ preserved => Or.inl preserved)
  have pmaEq := instructionAgree pma_regions
    (by simp [instructionPreserved, platformPreserved])
  exact
    { output :=
        { configured := access.output.configured.mono instructionAgree retired
          outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputBufferStore
          outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputLengthStore
          outputBufferNoMMIO := access.output.outputBufferNoMMIO
          outputLengthNoMMIO := access.output.outputLengthNoMMIO }
      stackAligned := access.stackAligned
      frameOutputDisjoint := access.frameOutputDisjoint
      frameLoad := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameLoad offset width bound)
      frameStore := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameStore offset width bound)
      frameLoadNoMMIO := access.frameLoadNoMMIO
      frameStoreNoMMIO := access.frameStoreNoMMIO
      frameNotCode := access.frameNotCode }

private theorem booleanEncoderLoadedOfSeg
    {args : EncoderCallArgs Bool} {owned exit kv fromStep count before after pc}
    (access : EncoderCallMachineAccess 16 args before)
    (frameLower : 16 ≤ args.callerStack)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg owned exit (fun _ _ _ _ _ => False) booleanEncoderPrefixWrites
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

private def booleanEncoderFinishSite : EncoderCallFinishSite 16 0x15bbc
    Elflings.writeSuccessBooleanExecutionPcRanges Elflings.writeSuccessBooleanExitPcs where
  loadPc := 0x15bbc
  restorePc := 0x15bc0
  retPc := 0x15bc4
  returnOffset := 8
  loadImm := 8
  restoreImm := 16
  loadByte0 := 0x83
  loadByte1 := 0x30
  loadByte2 := 0x81
  loadByte3 := 0x00
  restoreByte0 := 0x13
  restoreByte1 := 0x01
  restoreByte2 := 0x01
  restoreByte3 := 0x01
  pcs := by decide
  loadStarts := rfl
  frameLarge := by decide
  returnSlot := by decide
  loadSign := by native_decide
  restoreSign := by native_decide
  loadSite := by native_decide
  restoreSite := by native_decide
  retSite := by native_decide
  loadBase := by rfl
  restoreBase := by rfl
  loadDecode := by intro state configured; write_success_decode configured
  restoreDecode := by intro state configured; write_success_decode configured
  loadInside := by owned_pc [pcInRanges, Elflings.writeSuccessBooleanExecutionPcRanges]
  restoreInside := by owned_pc [pcInRanges, Elflings.writeSuccessBooleanExecutionPcRanges]
  retInside := by owned_pc [pcInRanges, Elflings.writeSuccessBooleanExecutionPcRanges]
  loadLocal := by owned_pc [pcInRanges]
  restoreLocal := by owned_pc [pcInRanges]
  retLocal := by owned_pc [pcInRanges]
  localInside := by
    intro pc inside
    unfold pcInRanges at inside ⊢
    rcases inside with ⟨range, member, lower, upper⟩
    simp at member
    rcases member with rfl
    exact ⟨(0x15b9c, 0x15bc8), by simp [Elflings.writeSuccessBooleanExecutionPcRanges],
      by omega, upper⟩
  loadNotExit := by simp [pcInList, Elflings.writeSuccessBooleanExitPcs]
  restoreNotExit := by simp [pcInList, Elflings.writeSuccessBooleanExitPcs]
  retNotExit := by simp [pcInList, Elflings.writeSuccessBooleanExitPcs]
  localAfterHost := by native_decide
  returnFacts := by
    intro returnPc fits listed
    simp [pcInList, Elflings.writeSuccessBooleanExitPcs, Nat.mod_eq_of_lt fits] at listed
    rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals native_decide

/-- The shared machine composition for the production Boolean encoder. -/
theorem writeSuccessBooleanContract_implements :
    (encoderCallContract Elflings.writeSuccessBooleanEntry
      Elflings.writeSuccessBooleanExitPcs 16
      (fun value => #[if value then 1 else 0]) BooleanEncoderBinding
      (fun _ => 16)).Implements EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessBooleanExecutionPcRanges)
      (pcInList Elflings.writeSuccessBooleanExitPcs) := by
  intro args fromStep before entry
  rcases entry with ⟨returnListed, frameLower, stackFits, atPc, link, stack, valueReg,
    loaded, access⟩
  have returnFits : args.returnAddress < 2 ^ 64 := by
    simp [Elflings.writeSuccessBooleanExitPcs] at returnListed
    omega
  let frameBase := args.callerStack - 16
  let valueBits := booleanEncoderWord args.value
  have frameBaseEq : frameBase = args.callerStack - 16 := rfl
  have valueBitsDef : valueBits = booleanEncoderWord args.value := rfl
  have valueBitsEq : valueBits = (if args.value then 1 else 0) := rfl
  have seg00 := Seg.nil (pcInRanges [(0x15b9c, 0x15bac)])
    (pcInList [0x15bac]) (fun _ _ _ _ _ => False)
    booleanEncoderPrefixWrites (byteRange frameBase 16) fromStep
    access.output.configured.retiredCounter (by
      simpa [Elflings.writeSuccessBooleanEntry] using atPc)
  have seg01 := seg00.know x1 (BitVec.ofNat 64 args.returnAddress) link
  have seg02 := seg01.know x2 (BitVec.ofNat 64 args.callerStack) stack
  have seg0 := seg02.know x10 valueBits (by simpa [valueBits, booleanEncoderWord] using valueReg)
  obtain ⟨retired0, run0⟩ := booleanEncoderSubtractStep fromStep args.callerStack
    before.machine access.output.configured
      (by simpa [Elflings.writeSuccessBooleanEntry] using atPc)
      stack loaded frameLower stackFits
  have seg0' := seg0.forget
    (kv' := [⟨x10, valueBits⟩, ⟨x1, BitVec.ofNat 64 args.returnAddress⟩]) (by simp)
  obtain ⟨retired0', machine1, machine1Eq, seg1⟩ := seg0'.stepWitness
    (by owned_pc [pcInRanges])
    (by simp [pcInList]) x2
    (BitVec.ofNat 64 frameBase) 0x15ba0 ⟨retired0, by simpa [frameBase] using run0⟩
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [booleanEncoderPrefixWrites]) (by decide) (by decide)
    (by simp [RegsOutside, booleanEncoderPrefixWrites, stepBookkeeping])
  have access1 := EncoderCallMachineAccess.ofBooleanSeg access seg1
  have loaded1 := booleanEncoderLoadedOfSeg access frameLower loaded seg1
  obtain ⟨retired1, run1⟩ := booleanEncoderSaveReturnStep (fromStep + 1)
    args.callerStack args.returnAddress machine1 access1 seg1.atPc
    (by
      have h := seg1.reg x2 (BitVec.ofNat 64 frameBase) (by simp)
      rw [frameBaseEq] at h
      exact h)
    (seg1.reg x1 _ (by simp)) loaded1 frameLower stackFits
  obtain ⟨retired1', machine2, machine2Eq, seg2⟩ := seg1.stepStoreWitness
    (width := 8) (frameBase + 8) (BitVec.ofNat 64 args.returnAddress) 0x15ba4
    (by owned_pc [pcInRanges])
    (by simp [pcInList]) ⟨retired1, by simpa [frameBase] using run1⟩
    (by native_decide) (by intro address lower upper; unfold frameBase byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, booleanEncoderPrefixWrites, stepBookkeeping])
  have access2 := EncoderCallMachineAccess.ofBooleanSeg access seg2
  have loaded2 := booleanEncoderLoadedOfSeg access frameLower loaded seg2
  have saved2 : UIntRep 8 machine2.mem (frameBase + 8) args.returnAddress := by
    rw [machine2Eq]
    simpa [tryStepStoreAfterRetired, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement machine1) 0x15ba0)
        (frameBase + 8) args.returnAddress returnFits (by omega)
  have seg2' := seg2.forget (kv' := [⟨x1, BitVec.ofNat 64 args.returnAddress⟩,
    ⟨x2, BitVec.ofNat 64 frameBase⟩]) (by simp)
  obtain ⟨retired2, run2⟩ := booleanEncoderMaskStep (fromStep + 2) args.value machine2
    access2.output.configured seg2'.atPc
    (by
      have h := seg2.reg x10 valueBits (by simp)
      rw [valueBitsDef] at h
      exact h) loaded2
  obtain ⟨retired2', machine3, machine3Eq, seg3⟩ := seg2'.stepWitness
    (by owned_pc [pcInRanges])
    (by simp [pcInList]) x10 valueBits 0x15ba8
    ⟨retired2, by simpa [valueBits] using run2⟩ (by native_decide)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [booleanEncoderPrefixWrites]) (by decide) (by decide)
    (by simp [RegsOutside, booleanEncoderPrefixWrites, stepBookkeeping])
  have access3 := EncoderCallMachineAccess.ofBooleanSeg access seg3
  have loaded3 := booleanEncoderLoadedOfSeg access frameLower loaded seg3
  have saved3 : UIntRep 8 machine3.mem (frameBase + 8) args.returnAddress := by
    apply saved2.of_mem_eq
    rw [machine3Eq]
    exact afterRegisterWrite_mem _ _ _ _ _
  obtain ⟨retired3, run3⟩ := booleanEncoderStoreStep (fromStep + 3) args.callerStack
    args.value machine3 access3 seg3.atPc
    (by
      have h := seg3.reg x2 (BitVec.ofNat 64 frameBase) (by simp)
      rw [frameBaseEq] at h
      exact h)
    (by
      have h := seg3.reg x10 valueBits (by simp)
      rw [valueBitsDef] at h
      exact h) loaded3 frameLower stackFits
  obtain ⟨retired3', machine4, machine4Eq, seg4⟩ := seg3.stepStoreWitness
    (width := 1) (frameBase + 7) valueBits 0x15bac
    (by owned_pc [pcInRanges])
    (by simp [pcInList])
    ⟨retired3, by simpa [frameBase, valueBits] using run3⟩ (by native_decide)
    (by intro address lower upper; unfold frameBase byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, booleanEncoderPrefixWrites, stepBookkeeping])
  have access4 := EncoderCallMachineAccess.ofBooleanSeg access seg4
  have loaded4 := booleanEncoderLoadedOfSeg access frameLower loaded seg4
  have byteRep4 : UIntRep 1 machine4.mem (frameBase + 7) (if args.value then 1 else 0) := by
    rw [machine4Eq]
    have valueByteEq : BitVec.setWidth 8 valueBits =
        BitVec.ofNat 8 (if args.value then 1 else 0) := by
      unfold valueBits booleanEncoderWord
      cases args.value <;> native_decide
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, valueByteEq] using
      uintRep_afterWriteBytes_one
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement machine3) 0x15ba8)
        (frameBase + 7) (if args.value then 1 else 0) (by cases args.value <;> decide) (by omega)
  have saved4 : UIntRep 8 machine4.mem (frameBase + 8) args.returnAddress := by
    have writes : WritesOnlyWithin (byteRange (frameBase + 7) 1) machine3 machine4 := by
      intro address outside
      rw [machine4Eq]
      exact storeRetirement_mem_writes machine3 0x15ba8 0x15bac retired3'
        (frameBase + 7) valueBits address outside
    exact saved3.of_writesOnlyWithin writes (by
      intro index bound
      unfold byteRange
      omega)
  let prepared : EndpointState := { before with machine := machine4 }
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := frameBase + 7, bytes := #[if args.value then 1 else 0] }
  have childEntry : RawEncoderSetupEntry 0x15bac 1 (RawEncoderStackSource 7)
      rawArgs prepared := by
    refine ⟨by simpa [prepared] using seg4.atPc, ?_, by simp [rawArgs], ?_, ?_,
      by simpa [prepared] using loaded4, by simpa [prepared] using access4.output⟩
    · refine ⟨frameBase, by simpa [prepared] using seg4.reg x2 _ (by simp), rfl, ?_⟩
      omega
    · have bytesEq : (#[if args.value then 1 else 0] : Array UInt8) =
          #[UInt8.ofNat (if args.value then 1 else 0)] := by
        cases args.value <;> decide
      change BytesRep machine4.mem (frameBase + 7) #[if args.value then 1 else 0]
      rw [bytesEq]
      exact byteRep4.bytesRepSingleton
    · intro index bound
      have indexZero : index = 0 := by simpa [rawArgs] using bound
      subst index
      apply access.frameOutputDisjoint (frameBase + 7)
      unfold frameBase byteRange
      omega
  obtain ⟨childUsed, childAfter, childOutcome, childPositive, childBound, childTrace, childExitAt,
    _, childExit⟩ := proposed_rawEncoder_42a2_proved rawArgs (fromStep + 4) prepared childEntry
  cases childOutcome
  rcases childExit with ⟨childPc, childStdout, childStdin, childCursor, childCode,
    childMem, childFrame⟩
  rcases childFrame with ⟨childAgree, childRetired, childLoaded, childAux⟩
  have childTrace' : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessBooleanExecutionPcRanges) (fromStep + 4) childUsed
      prepared childAfter := childTrace.weaken (by
    intro pc inside
    unfold pcInRanges at inside ⊢
    rcases inside with ⟨range, member, lower, upper⟩
    simp [rawEncoder42a2ExecutionPcs] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨(0x15b9c, 0x15bc8), by simp [Elflings.writeSuccessBooleanExecutionPcRanges],
        by omega, by omega⟩
    · exact ⟨(0x15b9c, 0x15bc8), by simp [Elflings.writeSuccessBooleanExecutionPcRanges],
        by omega, by omega⟩
    · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessBooleanExecutionPcRanges],
        lower, upper⟩)
  have childAccess := EncoderCallMachineAccess.ofEncoderInlineFrame access4 childAgree childRetired
  have childStack : childAfter.machine.regs.get? x2 = some (BitVec.ofNat 64 frameBase) :=
    (childAgree x2 (by simp [encoderInlinePreserved])).trans (seg4.reg x2 _ (by simp))
  have savedChild : UIntRep 8 childAfter.machine.mem (frameBase + 8) args.returnAddress :=
    saved4.of_writesOnlyWithin childMem (by
      intro index bound
      apply access.frameOutputDisjoint (frameBase + 8 + index)
      unfold frameBase byteRange
      omega)
  have frameAligned : frameBase % 16 = 0 := by
    rcases Nat.dvd_of_mod_eq_zero access.stackAligned with ⟨factor, equality⟩
    unfold frameBase
    omega
  have returnPcListed : pcInList Elflings.writeSuccessBooleanExitPcs
      (BitVec.ofNat 64 args.returnAddress) := by
    simpa [pcInList, Nat.mod_eq_of_lt returnFits] using returnListed
  obtain ⟨machine5, seg5⟩ := encoderCallFinishSeg booleanEncoderFinishSite
    (fromStep + 4 + childUsed) args.callerStack args.returnAddress childAfter.machine
    frameLower stackFits returnFits returnPcListed childAccess.output.configured childPc
    childStack savedChild (childAccess.frameLoad 8 8 (by omega))
    (childAccess.frameLoadNoMMIO 8 8 (by omega)) frameAligned childLoaded
  let after : EndpointState := { childAfter with machine := machine5 }
  have suffixMachineTrace : ScopedTrace (pcInRanges [(0x15bbc, 0x15bc8)])
      (pcInList Elflings.writeSuccessBooleanExitPcs) (fun _ _ _ _ _ => False)
      (fromStep + 4 + childUsed) 3 childAfter.machine machine5 := by
    exact seg5.confined 0 machine5
      (ScopedTrace.exitAt (fromStep + 4 + childUsed + 3) machine5
        (BitVec.ofNat 64 args.returnAddress) seg5.atPc returnPcListed)
  have suffixTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessBooleanExecutionPcRanges)
      (fromStep + 4 + childUsed) 3 childAfter after := by
    have lifted := liftSailSegToEndpointTrace childAfter (executionPcs := [(0x15bbc, 0x15bc8)])
      (by intro range member; simp at member; rcases member with rfl; native_decide)
      suffixMachineTrace
    exact lifted.weaken booleanEncoderFinishSite.localInside
  have prefixTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessBooleanExecutionPcRanges) fromStep 4 before prepared := by
    have scopedTrace := seg4.confined 0 machine4
      (ScopedTrace.exitAt (fromStep + 4) machine4 0x15bac seg4.atPc (by simp [pcInList]))
    have localTrace := liftSailSegToEndpointTrace before (executionPcs := [(0x15b9c, 0x15bac)])
      (by intro range member; simp at member; rcases member with rfl; native_decide) scopedTrace
    exact localTrace.weaken (by
      intro pc inside
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lower, upper⟩
      simp at member
      rcases member with rfl
      exact ⟨(0x15b9c, 0x15bc8), by simp [Elflings.writeSuccessBooleanExecutionPcRanges],
        lower, by omega⟩)
  have wholeTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessBooleanExecutionPcRanges) fromStep
      (4 + childUsed + 3) before after := by
    simpa [Nat.add_assoc] using prefixTrace.append (childTrace'.append suffixTrace)
  have childUsedBound : childUsed ≤ 9 := by
    simpa [rawEncoderSetupContract] using childBound
  have totalBound : 4 + childUsed + 3 ≤ 16 := by omega
  refine ⟨4 + childUsed + 3, after, (), by omega, totalBound, wholeTrace,
    ⟨BitVec.ofNat 64 args.returnAddress, by simpa [after] using seg5.atPc, returnPcListed⟩,
    trivial, ?_⟩
  refine ⟨by simpa [after] using seg5.atPc, ?_, ?_, ?_, ?_, frameLower, ?_, ?_⟩
  · simpa [after, prepared, rawArgs, childStdout, valueBits] using rfl
  · simpa [after, prepared] using childStdin
  · simpa [after, prepared] using childCursor
  · simpa [after, prepared] using childCode
  · have prefixMem : WritesOnlyWithin (encoderCallMemoryRegion 16 args)
        before.machine prepared.machine := WritesOnlyWithin.mono
          (fun address inside => Or.inl inside) seg4.mem
    have outputMem : WritesOnlyWithin (encoderCallMemoryRegion 16 args)
        prepared.machine childAfter.machine := WritesOnlyWithin.mono
          (fun address inside => Or.inr inside) childMem
    have suffixMem : WritesOnlyWithin (encoderCallMemoryRegion 16 args)
        childAfter.machine machine5 := WritesOnlyWithin.mono (by simp) seg5.mem
    simpa [after] using prefixMem.trans_same outputMem |>.trans_same suffixMem
  · refine ⟨?_, seg5.retired, ?_, ?_⟩
    · intro register preserved
      rcases abiCalleePreserved_booleanEncoder_cases preserved with rfl | rfl | rest
      · exact (seg5.reg x1 _ (by simp)).trans link.symm
      · exact (seg5.reg x2 _ (by simp)).trans stack.symm
      · have prefixEq := seg4.writes register rest.1
        have childEq := childAgree register rest.2.1
        have suffixEq := seg5.writes register rest.2.2
        exact suffixEq.trans (childEq.trans prefixEq)
    · have memoryEq := seg5.memEq (by simp)
      simpa [after, memoryEq] using childLoaded
    · exact ⟨seg5.aux.1.trans (childAux.1.trans seg4.aux.1),
        seg5.aux.2.1.trans (childAux.2.1.trans seg4.aux.2.1),
        seg5.aux.2.2.trans (childAux.2.2.trans seg4.aux.2.2)⟩

/-- `fi:1:4276` is a thin use of the shared Boolean machine theorem. -/
theorem proposed_booleanEncoder_4276_proved : WriteSuccessBooleanInstanceContract :=
  ⟨fun _ => 16, by intro _ _; simp [level2ContractFuel],
    writeSuccessBooleanContract_implements⟩

end BinaryFv.Zesu.Staging
