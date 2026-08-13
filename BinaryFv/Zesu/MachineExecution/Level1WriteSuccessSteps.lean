import BinaryFv.Zesu.MachineExecution.Level1DecodeInputSteps

/-!
# Parent-owned `writeSuccess` steps

This module composes the optimized observation writer around the selected Level-2 encoder regions.
The ABI prologue reuses the shared configured `addi`/dword-store instruction adapters and `Seg`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

def writeSuccessParentPc (pc : BitVec 64) : Prop :=
  pcInRanges Elflings.writeSuccessOwnedPcRanges pc

def writeSuccessParentWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x1 ∨ register = x2 ∨ register = x8 ∨
    register = x9 ∨ register = x10 ∨ register = x11 ∨ register = x12 ∨
    register = x13 ∨ register = x14 ∨ register = x15 ∨ register = x16 ∨
    register = x17 ∨ register = x18 ∨ register = x19 ∨ register = x20 ∨
    register = x21 ∨ register = x22 ∨ register = x23 ∨ register = x24 ∨
    register = x25 ∨ register = x26 ∨ register = x27 ∨ register = x28 ∨
    register = x29 ∨ register = x30 ∨ register = x31

def writeSuccessPrologueWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x2 ∨ register = x8

def writeSuccessFrameMemory (args : WriteSuccessArgs) : Region :=
  byteRange (args.stackPointer - 0x7d0) 0x7d0

def writeSuccessIncomingRegs (args : WriteSuccessArgs) (values : DecodeCalleeSavedValues) :
    List RegVal :=
  [⟨x1, BitVec.ofNat 64 args.returnAddress⟩,
   ⟨x8, values.s0⟩, ⟨x9, values.s1⟩, ⟨x18, values.s2⟩, ⟨x19, values.s3⟩,
   ⟨x20, values.s4⟩, ⟨x21, values.s5⟩, ⟨x22, values.s6⟩, ⟨x23, values.s7⟩,
   ⟨x24, values.s8⟩, ⟨x25, values.s9⟩, ⟨x26, values.s10⟩, ⟨x27, values.s11⟩,
   ⟨x10, BitVec.ofNat 64 args.decodedAddress⟩]

private theorem writeSuccessIncomingRegs_hold (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state)
    (values : DecodeCalleeSavedValues) (saved : DecodeCalleeSavedAtRegisters values state) :
    RegsHold state.machine (writeSuccessIncomingRegs args values) := by
  rcases entry with ⟨_, _, _, _, _, link, _, decoded, _, _, _, _⟩
  rcases saved with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
  intro pair member
  simp only [writeSuccessIncomingRegs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> assumption

private theorem writeSuccessStackResult (stackPointer : Nat) (lower : 0x7d0 ≤ stackPointer)
    (fits : stackPointer < 2 ^ 64) :
    BitVec.ofNat 64 (stackPointer - 0x7d0) =
      iTypeResult .ADDI 0x830 (BitVec.ofNat 64 stackPointer) := by
  have sign : sign_extend (m := 64) (0x830#12) =
      BitVec.ofNat 64 (2 ^ 64 - 0x7d0) := by native_decide
  unfold iTypeResult
  change BitVec.ofNat 64 (stackPointer - 0x7d0) =
    BitVec.ofNat 64 stackPointer + sign_extend (m := 64) (0x830#12)
  rw [sign, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have sum : stackPointer + (2 ^ 64 - 0x7d0) =
      (stackPointer - 0x7d0) + 2 ^ 64 := by omega
  rw [sum, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

/-- Exact first writer instruction, `0x14d30: addi sp,sp,-2000`, as a one-step `Seg`. -/
theorem writeSuccessAllocateFrame (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state)
    (values : DecodeCalleeSavedValues) (saved : DecodeCalleeSavedAtRegisters values state) :
    ∃ next,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 1 state.machine next 0x14d34 ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  rcases entry with ⟨_return, lower, _aligned, fits, atPc, _link, stack, _decoded, _rep,
    loaded, _saved, access⟩
  let kv := writeSuccessIncomingRegs args values
  have seg0 : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      kv fromStep 0 state.machine state.machine 0x14d30 := {
    trace := Trace.refl fromStep state.machine
    confined := .nil
    writes := WritesOnlyRegs.refl writeSuccessPrologueWrites state.machine
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := writeSuccessIncomingRegs_hold args state
      ⟨_return, lower, _aligned, fits, atPc, _link, stack, _decoded, _rep, loaded, _saved, access⟩
      values saved }
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x01 : BitVec 8) (0x01 : BitVec 8)
        (0x83 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state.machine)
      (tryStepControlFlowAfterIncrement state.machine)
      (.ITYPE (0x830, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := access.configured.seccfgPresent
    have privilegeAfter :
        (tryStepControlFlowAfterIncrement state.machine).regs.get? cur_privilege =
          some Privilege.Machine := by
      calc
        _ = state.machine.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged
            state.machine minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := access.configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state.machine).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.machine.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged
            state.machine minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    decode_run
  obtain ⟨retired, run⟩ := decodeInputAddiX2Step fromStep 0x14d30 state.machine 0x830
    (BitVec.ofNat 64 args.stackPointer) (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
    0x13 0x01 0x01 0x83 access.configured atPc stack loaded
    (writeSuccessStackResult args.stackPointer lower fits) decode (base := by rfl)
  obtain ⟨retired', next, nextEq, seg1⟩ := seg0.stepWitness
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
    (by unfold pcInList; native_decide) x2
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) 0x14d34 ⟨retired, run⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (Or.inr (Or.inl rfl)) (by decide) (by decide) (by
      simpa [kv, writeSuccessIncomingRegs, RegsOutside, RegSet.union, RegSet.only,
        stepBookkeeping] using
        (show RegsOutside (RegSet.union stepBookkeeping (RegSet.only x2)) kv by decide))
  have disjoint : RegSet.Disjoint instructionPreserved writeSuccessPrologueWrites := by
    intro register preserved written
    rcases written with bookkeeping | rfl | rfl
    · exact platformPreserved_disjoint register preserved.1 bookkeeping
    all_goals simp [instructionPreserved, platformPreserved] at preserved
  exact ⟨next, seg1, access.configured.mono (seg1.agree disjoint) seg1.retired⟩

private theorem instructionPreserved_disjoint_bookkeeping :
    RegSet.Disjoint instructionPreserved stepBookkeeping :=
  platformPreserved_disjoint.weaken (fun _ preserved => preserved.1)

private theorem writeSuccessStoreDecodeReads {state : State}
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    ∃ seccfgBits,
      (tryStepStoreAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine ∧
      (tryStepStoreAfterIncrement state).regs.get? mseccfg = some seccfgBits := by
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  refine ⟨seccfgBits, ?_, ?_⟩
  · calc
      _ = state.regs.get? cur_privilege := by
        simpa [tryStepStoreAfterIncrement] using writeReg_read_unchanged state
          minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := configured.normal.2.1
  · calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepStoreAfterIncrement] using writeReg_read_unchanged state
          minstret_increment mseccfg true (by decide)
      _ = some seccfgBits := seccfgRead

private theorem writeSuccessCodeOfSeg {args : WriteSuccessArgs} {W kv a n base cur pc}
    (access : WriteSuccessMachineAccess args base)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (stackLower : 0x7d0 ≤ args.stackPointer)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) W (writeSuccessFrameMemory args) kv a n base cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  intro address byte fileByte
  have unchanged := seg.mem address (by
    intro inside
    unfold writeSuccessFrameMemory byteRange at inside
    have none := access.frameNotCode address inside.1 (by omega)
    rw [fileByte] at none
    cases none)
  exact unchanged.trans (loaded address byte fileByte)

/-- Extend the writer prologue by one exact dword save, preserving all previously saved words. -/
theorem writeSuccessSaveStep {args : WriteSuccessArgs} {base : State}
    {kv : List RegVal} {a n : Nat} {cur : State} {pc : BitVec 64}
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      kv a n base cur pc)
    (access : WriteSuccessMachineAccess args base)
    (configured : ConfiguredMachinePre EndpointMachinePc cur)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (stackLower : 0x7d0 ≤ args.stackPointer) (stackFits : args.stackPointer < 2 ^ 64)
    (words : List (Nat × Nat)) (wordsRep : SavedWordReps cur words)
    (storePc offset : Nat) (source : BitVec 64) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (stackRead : cur.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping cur premise →
      Runs (rX_bits rs2) premise premise source)
    (belowWords : ∀ word ∈ words,
      args.stackPointer - 0x7d0 + offset + 8 ≤ word.1)
    (frameBound : offset + 8 ≤ 0x7d0)
    (aligned : (args.stackPointer - 0x7d0 + offset) % 8 = 0)
    (pcEq : pc = BitVec.ofNat 64 storePc)
    (inRegion : writeSuccessParentPc (BitVec.ofNat 64 storePc))
    (notExit : ¬pcInList Elflings.writeSuccessExitPcs (BitVec.ofNat 64 storePc))
    (decodeOfConfigured : ConfiguredMachinePre EndpointMachinePc cur →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
        (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
        (BitVec.ofNat 8 byte3.toNat)))
        (tryStepStoreAfterIncrement cur) (tryStepStoreAfterIncrement cur)
        (.STORE (imm, rs2, .Regidx 2#5, 8)))
    (addressEq : BitVec.ofNat 64 (args.stackPointer - 0x7d0) + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (args.stackPointer - 0x7d0 + offset))
    (keep : RegsOutside stepBookkeeping kv)
    (pcFits : storePc < 2 ^ 64) (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? storePc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (storePc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (storePc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (storePc + 3) = some byte3)
    (advance : Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4 = BitVec.ofNat 64 (storePc + 4)) :
    ∃ next,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        kv a (n + 1) base next (BitVec.ofNat 64 (storePc + 4)) ∧
      SavedWordReps next
        ((args.stackPointer - 0x7d0 + offset, source.toNat) :: words) ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  subst pc
  have code := writeSuccessCodeOfSeg access loaded stackLower seg
  have pma := dataPmaAllows_of_pma_regions_eq
    (seg.writes.get pma_regions (by simp [writeSuccessPrologueWrites, stepBookkeeping]))
    (access.frameStore offset 8 frameBound)
  have noMMIO := access.frameNoMMIO offset 8 frameBound
  have fits : args.stackPointer - 0x7d0 + offset + 8 ≤ 2 ^ 64 := by omega
  obtain ⟨retired, run⟩ := decodeInputStoreStep (a + n) storePc offset cur
    (args.stackPointer - 0x7d0) source imm rs2 byte0 byte1 byte2 byte3 configured seg.atPc
    stackRead pma noMMIO aligned fits code addressEq (decodeOfConfigured configured) dataRun
    (pcFits := pcFits) (base := baseEncoding) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3)
  obtain ⟨retired', next, nextEq, nextSeg⟩ := seg.stepStoreWitness
    (width := 8) (args.stackPointer - 0x7d0 + offset) source
    (BitVec.ofNat 64 (storePc + 4))
    inRegion notExit ⟨retired, run⟩ advance
    (by intro address lower upper; unfold writeSuccessFrameMemory byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping) keep
  have stepWrites : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 + offset) 8) cur next := by
    intro address outside
    rw [nextEq]
    exact storeRetirement_mem_writes cur (BitVec.ofNat 64 storePc)
      (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) retired'
      (args.stackPointer - 0x7d0 + offset) source address outside
  have oldReps : SavedWordReps next words := by
    intro word member
    exact (wordsRep word member).of_writesOnlyWithin stepWrites (by
      intro index indexBound inside
      unfold byteRange at inside
      have := belowWords word member
      omega)
  have currentRep : UIntRep 8 next.mem
      (args.stackPointer - 0x7d0 + offset) source.toNat := by
    have sourceFits : source.toNat < 2 ^ 64 := source.isLt
    rw [nextEq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement cur) (BitVec.ofNat 64 storePc))
        (args.stackPointer - 0x7d0 + offset) source.toNat sourceFits fits
  refine ⟨next, nextSeg, ?_, ?_⟩
  · intro word member
    simp only [List.mem_cons] at member
    rcases member with rfl | tail
    · simpa using currentRep
    · exact oldReps word tail
  · have stepAgree : Agree instructionPreserved cur next := by
      rw [nextEq]
      exact (storeRetirement_writes cur (BitVec.ofNat 64 storePc)
        (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) retired'
        (args.stackPointer - 0x7d0 + offset) source).agree
        instructionPreserved_disjoint_bookkeeping
    exact configured.mono stepAgree nextSeg.retired

/-- Exact first save, `0x14d34: sd ra,1992(sp)`. -/
theorem writeSuccessSaveRa {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 1 state.machine cur 0x14d34)
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ next,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 2 state.machine next 0x14d38 ∧
      SavedWordReps next
        [(args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits [] (by
    intro word member; simp at member) 0x14d34 0x7c8
    (BitVec.ofNat 64 args.returnAddress) 0x7c8 (.Regidx 1#5) 0x23 0x34 0x11 0x7c
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x1_run premise (BitVec.ofNat 64 args.returnAddress)
      ((writes.get x1 (by decide)).trans
        (seg.reg x1 (BitVec.ofNat 64 args.returnAddress) (by
          simp [writeSuccessIncomingRegs])))
  · intro word member; simp at member
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7c8#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Exact second save, `0x14d38: sd s0,1984(sp)`. -/
theorem writeSuccessSaveS0 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 2 state.machine cur 0x14d38)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7c8,
        (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ next,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 3 state.machine next 0x14d3c ∧
      SavedWordReps next
        [(args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d38 0x7c0 values.s0 0x7c0 (.Regidx 8#5) 0x23 0x30 0x81 0x7c
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x8_run premise values.s0
      ((writes.get x8 (by decide)).trans
        (seg.reg x8 values.s0 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7c0#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d3c: sd s1,1976(sp)`. -/
theorem writeSuccessSaveS1 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 3 state.machine cur 0x14d3c)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 4 state.machine nextState 0x14d40 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d3c 0x7b8 values.s1 0x7b8 (.Regidx 9#5) 0x23 0x3c 0x91 0x7a
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x9_run premise values.s1
      ((writes.get x9 (by decide)).trans
        (seg.reg x9 values.s1 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7b8#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d40: sd s2,1968(sp)`. -/
theorem writeSuccessSaveS2 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 4 state.machine cur 0x14d40)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 5 state.machine nextState 0x14d44 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d40 0x7b0 values.s2 0x7b0 (.Regidx 18#5) 0x23 0x38 0x21 0x7b
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x18_run premise values.s2
      ((writes.get x18 (by decide)).trans
        (seg.reg x18 values.s2 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7b0#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d44: sd s3,1960(sp)`. -/
theorem writeSuccessSaveS3 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 5 state.machine cur 0x14d44)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 6 state.machine nextState 0x14d48 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d44 0x7a8 values.s3 0x7a8 (.Regidx 19#5) 0x23 0x34 0x31 0x7b
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x19_run premise values.s3
      ((writes.get x19 (by decide)).trans
        (seg.reg x19 values.s3 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7a8#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d48: sd s4,1952(sp)`. -/
theorem writeSuccessSaveS4 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 6 state.machine cur 0x14d48)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 7 state.machine nextState 0x14d4c ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d48 0x7a0 values.s4 0x7a0 (.Regidx 20#5) 0x23 0x30 0x41 0x7b
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x20_run premise values.s4
      ((writes.get x20 (by decide)).trans
        (seg.reg x20 values.s4 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7a0#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d4c: sd s5,1944(sp)`. -/
theorem writeSuccessSaveS5 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 7 state.machine cur 0x14d4c)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 8 state.machine nextState 0x14d50 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d4c 0x798 values.s5 0x798 (.Regidx 21#5) 0x23 0x3c 0x51 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x21_run premise values.s5
      ((writes.get x21 (by decide)).trans
        (seg.reg x21 values.s5 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x798#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d50: sd s6,1936(sp)`. -/
theorem writeSuccessSaveS6 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 8 state.machine cur 0x14d50)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 9 state.machine nextState 0x14d54 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d50 0x790 values.s6 0x790 (.Regidx 22#5) 0x23 0x38 0x61 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x22_run premise values.s6
      ((writes.get x22 (by decide)).trans
        (seg.reg x22 values.s6 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x790#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d54: sd s7,1928(sp)`. -/
theorem writeSuccessSaveS7 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 9 state.machine cur 0x14d54)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 10 state.machine nextState 0x14d58 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d54 0x788 values.s7 0x788 (.Regidx 23#5) 0x23 0x34 0x71 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x23_run premise values.s7
      ((writes.get x23 (by decide)).trans
        (seg.reg x23 values.s7 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x788#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d58: sd s8,1920(sp)`. -/
theorem writeSuccessSaveS8 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 10 state.machine cur 0x14d58)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 11 state.machine nextState 0x14d5c ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d58 0x780 values.s8 0x780 (.Regidx 24#5) 0x23 0x30 0x81 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x24_run premise values.s8
      ((writes.get x24 (by decide)).trans
        (seg.reg x24 values.s8 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x780#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d5c: sd s9,1912(sp)`. -/
theorem writeSuccessSaveS9 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 11 state.machine cur 0x14d5c)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 12 state.machine nextState 0x14d60 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
         (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d5c 0x778 values.s9 0x778 (.Regidx 25#5) 0x23 0x3c 0x91 0x77
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x25_run premise values.s9
      ((writes.get x25 (by decide)).trans
        (seg.reg x25 values.s9 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x778#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d60: sd s10,1904(sp)`. -/
theorem writeSuccessSaveS10 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 12 state.machine cur 0x14d60)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
         (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 13 state.machine nextState 0x14d64 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x770, values.s10.toNat),
         (args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
         (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d60 0x770 values.s10 0x770 (.Regidx 26#5) 0x23 0x38 0xa1 0x77
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x26_run premise values.s10
      ((writes.get x26 (by decide)).trans
        (seg.reg x26 values.s10 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x770#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d64: sd s11,1896(sp)`. -/
theorem writeSuccessSaveS11 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 13 state.machine cur 0x14d64)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x770, values.s10.toNat),
         (args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
         (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 14 state.machine nextState 0x14d68 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x768, values.s11.toNat),
         (args.stackPointer - 0x7d0 + 0x770, values.s10.toNat),
         (args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
         (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, loaded, _, access⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d64 0x768 values.s11 0x768 (.Regidx 27#5) 0x23 0x34 0xb1 0x77
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x27_run premise values.s11
      ((writes.get x27 (by decide)).trans
        (seg.reg x27 values.s11 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold pcInList; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x768#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def writeSuccessSavedWords (args : WriteSuccessArgs) (values : DecodeCalleeSavedValues) :
    List (Nat × Nat) :=
  [(args.stackPointer - 0x7d0 + 0x768, values.s11.toNat),
   (args.stackPointer - 0x7d0 + 0x770, values.s10.toNat),
   (args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
   (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
   (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
   (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
   (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
   (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
   (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
   (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
   (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
   (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
   (args.stackPointer - 0x7d0 + 0x7c8,
    (BitVec.ofNat 64 args.returnAddress).toNat)]

/-- The exact stack allocation and thirteen ABI saves, ending before `mv s0,a0`. -/
theorem writeSuccessSavePrologue (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values next,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 14 state.machine next 0x14d68 ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  rcases entry with ⟨ret, lower, aligned, fits, atPc, link, stack, decoded, rep, loaded,
    ⟨values, saved⟩, access⟩
  have entry' : WriteSuccessEntry args state :=
    ⟨ret, lower, aligned, fits, atPc, link, stack, decoded, rep, loaded, ⟨values, saved⟩, access⟩
  obtain ⟨s1, seg1, cfg1⟩ := writeSuccessAllocateFrame fromStep args state entry' values saved
  obtain ⟨s2, seg2, words2, cfg2⟩ := writeSuccessSaveRa entry' seg1 cfg1
  obtain ⟨s3, seg3, words3, cfg3⟩ := writeSuccessSaveS0 entry' seg2 words2 cfg2
  obtain ⟨s4, seg4, words4, cfg4⟩ := writeSuccessSaveS1 entry' seg3 words3 cfg3
  obtain ⟨s5, seg5, words5, cfg5⟩ := writeSuccessSaveS2 entry' seg4 words4 cfg4
  obtain ⟨s6, seg6, words6, cfg6⟩ := writeSuccessSaveS3 entry' seg5 words5 cfg5
  obtain ⟨s7, seg7, words7, cfg7⟩ := writeSuccessSaveS4 entry' seg6 words6 cfg6
  obtain ⟨s8, seg8, words8, cfg8⟩ := writeSuccessSaveS5 entry' seg7 words7 cfg7
  obtain ⟨s9, seg9, words9, cfg9⟩ := writeSuccessSaveS6 entry' seg8 words8 cfg8
  obtain ⟨s10, seg10, words10, cfg10⟩ := writeSuccessSaveS7 entry' seg9 words9 cfg9
  obtain ⟨s11, seg11, words11, cfg11⟩ := writeSuccessSaveS8 entry' seg10 words10 cfg10
  obtain ⟨s12, seg12, words12, cfg12⟩ := writeSuccessSaveS9 entry' seg11 words11 cfg11
  obtain ⟨s13, seg13, words13, cfg13⟩ := writeSuccessSaveS10 entry' seg12 words12 cfg12
  obtain ⟨s14, seg14, words14, cfg14⟩ := writeSuccessSaveS11 entry' seg13 words13 cfg13
  exact ⟨values, s14, seg14, by simpa [writeSuccessSavedWords] using words14, cfg14⟩

/-- Production `0x14d68: mv s0,a0`. -/
theorem writeSuccessBindDecodedStep (stepNo : Nat) (state : State) (value : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d68)
    (source : state.regs.get? x10 = some value)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14d68 retired x8 value) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d68
  have source' := (stepPremiseState_writes state 0x14d68).get x10 (by decide) |>.trans source
  have execute : Runs (execute (.ITYPE (0, .Regidx 10#5, .Regidx 8#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x8 value } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 10#5) (.Regidx 8#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 0 value = value := by
      simp [iTypeResult, show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
    simpa only [resultEq] using
      execute_ITYPE_run premise _ 0 (.Regidx 10#5) (.Regidx 8#5) .ADDI value
        (rX_x10_run premise value source') (wX_x8_run premise (iTypeResult .ADDI 0 value))
  exact configuredRegisterWriteStep stepNo 0x14d68 state x8 value
    (.ITYPE (0, .Regidx 10#5, .Regidx 8#5, .ADDI)) 0x13 0x04 0x05 0x00
    configured atPc loaded (by
      obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
      have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
          some Privilege.Machine := by
        calc
          _ = state.regs.get? cur_privilege := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
          _ = some Privilege.Machine := configured.normal.2.1
      have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
          some seccfgBits := by
        calc
          _ = state.regs.get? mseccfg := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
          _ = some seccfgBits := seccfgRead
      decode_run) execute (base := by rfl)

/-- Complete the writer ABI prologue at the first parent-owned payload setup instruction. -/
theorem writeSuccessPrologueHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values next,
      Seg writeSuccessParentPc (pcInList Elflings.writeSuccessExitPcs)
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        [⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
        fromStep 15 state.machine next 0x14d6c ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  obtain ⟨values, savedState, seg, words, configured⟩ :=
    writeSuccessSavePrologue fromStep args state entry
  rcases entry with ⟨_, lower, _, _, _, _, _, _, _, loaded, _, access⟩
  have seg0 := seg.forget (kv' := []) (by simp)
  have code := writeSuccessCodeOfSeg access loaded lower seg0
  have source := seg.reg x10 (BitVec.ofNat 64 args.decodedAddress)
    (by simp [writeSuccessIncomingRegs])
  obtain ⟨retired, run⟩ := writeSuccessBindDecodedStep (fromStep + 14) savedState
    (BitVec.ofNat 64 args.decodedAddress) configured seg.atPc source code
  obtain ⟨retired', next, nextEq, seg1⟩ := seg0.stepWitness
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
    (by unfold pcInList; native_decide) x8 (BitVec.ofNat 64 args.decodedAddress) 0x14d6c
    ⟨retired, run⟩ (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (Or.inr (Or.inr rfl)) (by decide) (by decide) (by simp [RegsOutside])
  have wordsNext : SavedWordReps next (writeSuccessSavedWords args values) := by
    rw [nextEq]
    simpa only [afterRegisterWrite_mem] using words
  have configuredNext : ConfiguredMachinePre EndpointMachinePc next := by
    rw [nextEq]
    exact ConfiguredMachinePre.afterRegisterWrite 0x14d68 retired' x8
      (BitVec.ofNat 64 args.decodedAddress) configured (by
        intro preserved
        rcases preserved.1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
          h | h | h
        all_goals cases h)
  exact ⟨values, next, seg1, wordsNext, configuredNext⟩

end BinaryFv.Zesu.MachineExecution
