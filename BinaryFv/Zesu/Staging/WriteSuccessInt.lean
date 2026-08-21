import BinaryFv.Zesu.MachineExecution.EncoderCallFinish
import BinaryFv.Zesu.MachineExecution.EncoderCallPrologue
import BinaryFv.Zesu.Staging.MemWriteInt
import BinaryFv.Zesu.Staging.IntegerEncoder
import BinaryFv.Zesu.Staging.RawEncoder

/-!
# The Level 2 fixed-width integer output proof

This parent composes the shared 16-byte prologue, the proved `mem.writeInt` store, the proved
`Encoder.raw` child, and the shared called-encoder return sequence.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

private def writeSuccessIntSubtractSite : ExactInstructionSite 0x15d10 0x13 0x01 0x01 0xff :=
  by native_decide

private def writeSuccessIntSaveReturnSite : ExactInstructionSite 0x15d14 0x23 0x34 0x11 0x00 :=
  by native_decide

private def writeSuccessIntFinishSite : EncoderCallFinishSite 16 0x15d2c
    Elflings.writeSuccessIntExecutionPcRanges Elflings.writeSuccessIntExitPcs where
  loadPc := 0x15d2c
  restorePc := 0x15d30
  retPc := 0x15d34
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
  loadDecode := by intro state configured; configured_decode configured
  restoreDecode := by intro state configured; configured_decode configured
  loadInside := by owned_pc [pcInRanges, Elflings.writeSuccessIntExecutionPcRanges]
  restoreInside := by owned_pc [pcInRanges, Elflings.writeSuccessIntExecutionPcRanges]
  retInside := by owned_pc [pcInRanges, Elflings.writeSuccessIntExecutionPcRanges]
  loadLocal := by owned_pc [pcInRanges]
  restoreLocal := by owned_pc [pcInRanges]
  retLocal := by owned_pc [pcInRanges]
  localInside := by
    intro pc inside
    unfold pcInRanges at inside ⊢
    rcases inside with ⟨range, member, lower, upper⟩
    simp at member
    rcases member with rfl
    exact ⟨(0x15d10, 0x15d38), by simp [Elflings.writeSuccessIntExecutionPcRanges],
      by omega, upper⟩
  loadNotExit := by simp [pcInList, Elflings.writeSuccessIntExitPcs]
  restoreNotExit := by simp [pcInList, Elflings.writeSuccessIntExitPcs]
  retNotExit := by simp [pcInList, Elflings.writeSuccessIntExitPcs]
  localAfterHost := by native_decide
  returnFacts := by
    intro returnPc fits listed
    simp [pcInList, Elflings.writeSuccessIntExitPcs, Nat.mod_eq_of_lt fits] at listed
    rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals native_decide

private theorem abiCalleePreserved_writeSuccessInt_cases {register : Register}
    (preserved : abiCalleePreserved register) :
    register = x1 ∨ register = x2 ∨
      (¬encoderCallPrologue16Writes register ∧ memWriteIntPreserved register ∧
        encoderInlinePreserved register ∧ ¬encoderCallFinishWrites register) := by
  simp [abiCalleePreserved] at preserved
  rcases preserved with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [encoderCallPrologue16Writes, memWriteIntPreserved, encoderInlinePreserved,
    encoderCallFinishWrites, instructionPreserved, platformPreserved,
    stepBookkeeping]

/-- The fixed-width integer output parent satisfies its complete Level 2 contract. -/
theorem writeSuccessIntContract_implements :
    (encoderCallContract Elflings.writeSuccessIntEntry Elflings.writeSuccessIntExitPcs 16
      (encodeNatLE 8) UInt64EncoderBinding (fun _ => 15)).Implements
      EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessIntExecutionPcRanges)
      (pcInList Elflings.writeSuccessIntExitPcs) := by
  intro args fromStep before entry
  rcases entry with ⟨returnListed, frameLower, stackFits, atPc, link, stack,
    ⟨valueFits, valueReg⟩, loaded, access⟩
  have returnFits : args.returnAddress < 2 ^ 64 := by
    simp [Elflings.writeSuccessIntExitPcs] at returnListed
    omega
  let frameBase := args.callerStack - 16
  let valueBits := BitVec.ofNat 64 args.value
  obtain ⟨machine2, prefixSeg, access2, loaded2, saved2⟩ :=
    encoderCallPrologue16Seg
      (owned := pcInRanges [(0x15d10, 0x15d18)]) (exit := pcInList [0x15d18])
      0x15d10 fromStep args valueBits before.machine frameLower stackFits returnFits
      (by simpa [Elflings.writeSuccessIntEntry] using atPc) link stack
      (by simpa [valueBits] using valueReg) loaded access
      writeSuccessIntSubtractSite writeSuccessIntSaveReturnSite
      (by owned_pc [pcInRanges]) (by owned_pc [pcInRanges])
      (by simp [pcInList]) (by simp [pcInList])
  let prepared : EndpointState := { before with machine := machine2 }
  let storeArgs : MemWriteIntArgs :=
    { address := frameBase, value := args.value
      addressFits := by unfold frameBase; omega
      valueFits }
  have frameAligned : frameBase % 8 = 0 := by
    rcases Nat.dvd_of_mod_eq_zero access.stackAligned with ⟨factor, equality⟩
    unfold frameBase
    omega
  have preparedConfigured : ConfiguredMachinePre EndpointMachinePc prepared.machine := by
    simpa [prepared] using access2.output.configured
  have storeEntry : memWriteIntEntry storeArgs prepared := by
    refine ⟨by simpa [prepared] using prefixSeg.atPc, ?_, ?_,
      preparedConfigured,
      by simpa [prepared] using loaded2, ?_⟩
    · simpa [prepared, storeArgs, frameBase] using
        (prefixSeg.reg x2 (BitVec.ofNat 64 (args.callerStack - 16)) (by simp))
    · simpa [prepared, storeArgs, valueBits] using
        (prefixSeg.reg x10 valueBits (by simp))
    · refine ⟨0x23, 0x30, 0xa1, 0x00, by rfl, by native_decide, by native_decide,
        by native_decide, by native_decide, ?_, ?_⟩
      · configured_store_decode preparedConfigured
      · exact
          { nonwrap := storeArgs.addressFits
            aligned := by simpa [storeArgs] using frameAligned
            pma := by simpa [storeArgs, frameBase] using access2.frameStore 0 8 (by omega)
            noMMIO := by
              simpa [storeArgs, frameBase] using access2.frameStoreNoMMIO 0 8 (by omega)
            codeDisjoint := by
              intro index
              apply access2.frameNotCode (frameBase + index.val)
              · omega
              · omega }
  obtain ⟨storeUsed, stored, storeOutcome, storePositive, storeBound, storeTrace,
    storeExitAt, _, storeExit⟩ :=
    memWriteIntContract_implements storeArgs (fromStep + 2) prepared storeEntry
  cases storeOutcome
  rcases storeExit with ⟨storedPc, storedValue, storedStdin, storedCursor, storedStdout,
    storedCode, storedMem, storedAgree, storedRetired, storedLoaded, storedAux⟩
  have storedInlineAgree : Agree encoderInlinePreserved machine2 stored.machine := storedAgree
  have storedAccess := access2.ofEncoderInlineFrame storedInlineAgree storedRetired
  have storedStack : stored.machine.regs.get? x2 = some (BitVec.ofNat 64 frameBase) :=
    (storedAgree x2 (by simp [memWriteIntPreserved, encoderInlinePreserved])).trans (by
      simpa [frameBase] using
        (prefixSeg.reg x2 (BitVec.ofNat 64 (args.callerStack - 16)) (by simp)))
  have savedStored : UIntRep 8 stored.machine.mem (frameBase + 8) args.returnAddress :=
    saved2.of_writesOnlyWithin storedMem (by
      intro index bound inside
      unfold byteRange at inside
      simp [storeArgs, frameBase] at inside
      omega)
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := frameBase, bytes := encodeNatLE 8 args.value }
  have rawEntry : RawEncoderSetupEntry 0x15d1c 8 (RawEncoderStackSource 0)
      rawArgs stored := by
    refine ⟨storedPc, ?_, by simp [rawArgs, encodeNatLE_size], ?_, ?_, storedLoaded,
      storedAccess.output⟩
    · exact ⟨frameBase, storedStack, by simp [rawArgs], by unfold frameBase; omega⟩
    · simpa [rawArgs, storeArgs] using UIntRep.bytesRepEncodeNatLEEight storedValue
    · intro index bound
      apply access.frameOutputDisjoint (frameBase + index)
      simp only [rawArgs] at bound
      unfold byteRange
      unfold frameBase
      simp [encodeNatLE_size] at bound
      omega
  obtain ⟨rawUsed, rawAfter, rawOutcome, rawPositive, rawBound, rawTrace, rawExitAt,
    _, rawExit⟩ := proposed_rawEncoder_45f6_proved rawArgs (fromStep + 2 + storeUsed)
      stored rawEntry
  cases rawOutcome
  rcases rawExit with ⟨rawPc, rawStdout, rawStdin, rawCursor, rawCode, rawMem, rawFrame⟩
  rcases rawFrame with ⟨rawAgree, rawRetired, rawLoaded, rawAux⟩
  have rawAccess := storedAccess.ofEncoderInlineFrame rawAgree rawRetired
  have rawStack : rawAfter.machine.regs.get? x2 = some (BitVec.ofNat 64 frameBase) :=
    (rawAgree x2 (by simp [encoderInlinePreserved])).trans storedStack
  have savedRaw : UIntRep 8 rawAfter.machine.mem (frameBase + 8) args.returnAddress :=
    savedStored.of_writesOnlyWithin rawMem (by
      intro index bound
      apply access.frameOutputDisjoint (frameBase + 8 + index)
      unfold frameBase byteRange
      omega)
  have returnPcListed : pcInList Elflings.writeSuccessIntExitPcs
      (BitVec.ofNat 64 args.returnAddress) := by
    simpa [pcInList, Nat.mod_eq_of_lt returnFits] using returnListed
  obtain ⟨machine5, suffixSeg⟩ := encoderCallFinishSeg writeSuccessIntFinishSite
    (fromStep + 2 + storeUsed + rawUsed) args.callerStack args.returnAddress rawAfter.machine
    frameLower stackFits returnFits returnPcListed rawAccess.output.configured rawPc rawStack
    savedRaw (rawAccess.frameLoad 8 8 (by omega))
    (rawAccess.frameLoadNoMMIO 8 8 (by omega))
    (by
      rcases Nat.dvd_of_mod_eq_zero access.stackAligned with ⟨factor, equality⟩
      omega)
    rawLoaded
  let after : EndpointState := { rawAfter with machine := machine5 }
  have prefixTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessIntExecutionPcRanges) fromStep 2 before prepared := by
    have scopedTrace := prefixSeg.confined 0 machine2
      (ScopedTrace.exitAt (fromStep + 2) machine2 0x15d18 prefixSeg.atPc
        (by simp [pcInList]))
    have lifted := liftSailSegToEndpointTrace before (executionPcs := [(0x15d10, 0x15d18)])
      (by intro range member; simp at member; rcases member with rfl; native_decide) scopedTrace
    exact lifted.weaken (by
      intro pc inside
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lower, upper⟩
      simp at member
      rcases member with rfl
      exact ⟨(0x15d10, 0x15d38), by simp [Elflings.writeSuccessIntExecutionPcRanges],
        lower, by omega⟩)
  have storeTrace' : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessIntExecutionPcRanges) (fromStep + 2)
      storeUsed prepared stored := storeTrace.weaken (by
    intro pc inside
    unfold pcInList at inside
    simp at inside
    exact ⟨(0x15d10, 0x15d38), by simp [Elflings.writeSuccessIntExecutionPcRanges],
      by omega, by omega⟩)
  have rawTrace' : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessIntExecutionPcRanges) (fromStep + 2 + storeUsed)
      rawUsed stored rawAfter := rawTrace.weaken (by
    intro pc inside
    unfold pcInRanges at inside ⊢
    rcases inside with ⟨range, member, lower, upper⟩
    simp [rawEncoder45f6ExecutionPcs] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨(0x15d10, 0x15d38), by simp [Elflings.writeSuccessIntExecutionPcRanges],
        by omega, by omega⟩
    · exact ⟨(0x15d10, 0x15d38), by simp [Elflings.writeSuccessIntExecutionPcRanges],
        by omega, by omega⟩
    · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessIntExecutionPcRanges],
        lower, upper⟩)
  have suffixMachineTrace : ScopedTrace (pcInRanges [(0x15d2c, 0x15d38)])
      (pcInList Elflings.writeSuccessIntExitPcs) (fun _ _ _ _ _ => False)
      (fromStep + 2 + storeUsed + rawUsed) 3 rawAfter.machine machine5 := by
    exact suffixSeg.confined 0 machine5
      (ScopedTrace.exitAt (fromStep + 2 + storeUsed + rawUsed + 3) machine5
        (BitVec.ofNat 64 args.returnAddress) suffixSeg.atPc returnPcListed)
  have suffixTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessIntExecutionPcRanges)
      (fromStep + 2 + storeUsed + rawUsed) 3 rawAfter after := by
    have lifted := liftSailSegToEndpointTrace rawAfter (executionPcs := [(0x15d2c, 0x15d38)])
      (by intro range member; simp at member; rcases member with rfl; native_decide)
      suffixMachineTrace
    exact lifted.weaken writeSuccessIntFinishSite.localInside
  have wholeTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessIntExecutionPcRanges) fromStep
      (2 + storeUsed + rawUsed + 3) before after := by
    simpa [Nat.add_assoc] using
      prefixTrace.append (storeTrace'.append (rawTrace'.append suffixTrace))
  have totalBound : 2 + storeUsed + rawUsed + 3 ≤ 15 := by
    have storeOne : storeUsed ≤ 1 := by simpa [memWriteIntContract] using storeBound
    have rawNine : rawUsed ≤ 9 := by simpa [rawEncoderSetupContract] using rawBound
    omega
  refine ⟨2 + storeUsed + rawUsed + 3, after, (), by omega, totalBound, wholeTrace,
    ⟨BitVec.ofNat 64 args.returnAddress, by simpa [after] using suffixSeg.atPc,
      returnPcListed⟩, trivial, ?_⟩
  refine ⟨by simpa [after] using suffixSeg.atPc, ?_, ?_, ?_, ?_, frameLower, ?_, ?_⟩
  · simpa [after, prepared, rawArgs, rawStdout, storedStdout] using rfl
  · simpa [after, prepared, storedStdin] using rawStdin
  · simpa [after, prepared, storedCursor] using rawCursor
  · simpa [after, prepared, storedCode] using rawCode
  · have prefixMem : WritesOnlyWithin (encoderCallMemoryRegion 16 args)
        before.machine prepared.machine := WritesOnlyWithin.mono
          (fun address inside => Or.inl inside) prefixSeg.mem
    have storeMem' : WritesOnlyWithin (encoderCallMemoryRegion 16 args)
        prepared.machine stored.machine := WritesOnlyWithin.mono
          (fun address inside => Or.inl (by
            unfold byteRange at inside ⊢
            simp [storeArgs, frameBase] at inside ⊢
            omega)) storedMem
    have rawMem' : WritesOnlyWithin (encoderCallMemoryRegion 16 args)
        stored.machine rawAfter.machine := WritesOnlyWithin.mono
          (fun address inside => Or.inr inside) rawMem
    have suffixMem : WritesOnlyWithin (encoderCallMemoryRegion 16 args)
        rawAfter.machine machine5 := WritesOnlyWithin.mono (by simp) suffixSeg.mem
    simpa [after] using prefixMem.trans_same storeMem' |>.trans_same rawMem' |>.trans_same suffixMem
  · refine ⟨?_, suffixSeg.retired, ?_, ?_⟩
    · intro register preserved
      rcases abiCalleePreserved_writeSuccessInt_cases preserved with rfl | rfl | rest
      · exact (suffixSeg.reg x1 _ (by simp)).trans link.symm
      · exact (suffixSeg.reg x2 _ (by simp)).trans stack.symm
      · exact (suffixSeg.writes register rest.2.2.2).trans
          ((rawAgree register rest.2.2.1).trans
            ((storedAgree register rest.2.1).trans (prefixSeg.writes register rest.1)))
    · have memoryEq := suffixSeg.memEq (by simp)
      simpa [after, memoryEq] using rawLoaded
    · exact ⟨suffixSeg.aux.1.trans (rawAux.1.trans (storedAux.1.trans prefixSeg.aux.1)),
        suffixSeg.aux.2.1.trans
          (rawAux.2.1.trans (storedAux.2.1.trans prefixSeg.aux.2.1)),
        suffixSeg.aux.2.2.trans
          (rawAux.2.2.trans (storedAux.2.2.trans prefixSeg.aux.2.2))⟩

/-- `fi:1:4578` is a thin Level 2 wrapper around the shared composition theorem. -/
theorem writeSuccessInt_proved : WriteSuccessIntInstanceContract :=
  ⟨fun _ => 15, by intro _ _; simp [level2ContractFuel], writeSuccessIntContract_implements⟩

end BinaryFv.Zesu.Staging
