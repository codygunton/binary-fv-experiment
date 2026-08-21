import BinaryFv.Zesu.MachineExecution.HLevel3BooleanEncoderSteps

/-!
# Shared called-encoder return sequence

Called encoders restore `ra`, restore `sp`, and return. This module proves that machine sequence
once. Boolean and fixed-width integer encoders supply only their exact instruction sites.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

def encoderCallFinishWrites (register : Register) : Prop :=
  stepBookkeeping register ∨ register = x1 ∨ register = x2

theorem instructionPreserved_disjoint_encoderCallFinishWrites :
    RegSet.Disjoint instructionPreserved encoderCallFinishWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

/-- Lift a Sail-only `Seg` trace into the endpoint state when all owned PCs follow host code. -/
theorem liftSailSegToEndpointTrace (template : EndpointState)
    {executionPcs : List Elflings.PcRange} {exit : BitVec 64 → Prop}
    {fromStep count : Nat} {before after : State}
    (afterHost : ∀ range ∈ executionPcs, 0x101d4 ≤ range.1)
    (trace : ScopedTrace (pcInRanges executionPcs) exit (fun _ _ _ _ _ => False)
      fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs) fromStep count
      { template with machine := before } { template with machine := after } := by
  have notObserved : ∀ pc, pcInRanges executionPcs pc → ¬BareMetalHostTransitionPc pc := by
    intro pc inside observed
    unfold pcInRanges at inside
    rcases inside with ⟨range, member, lower, upper⟩
    have after := afterHost range member
    unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
      at observed
    rcases observed with observed | observed | observed <;> omega
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } atPc inside ?_ (by simpa using ih)
      exact endpointStep_sail fromStep { template with machine := before } middle
        (fun observed observedPc => by
          change before.regs.get? PC = some observed at observedPc
          rw [atPc] at observedPc
          cases Option.some.inj observedPc
          exact notObserved pc inside)
        machineStep
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count callSite program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

/-- Exact instruction data for the common `ld ra; addi sp; ret` sequence. -/
structure EncoderCallFinishSite (frameSize callReturn : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat) where
  loadPc : Nat
  restorePc : Nat
  retPc : Nat
  returnOffset : Nat
  loadImm : BitVec 12
  restoreImm : BitVec 12
  loadByte0 : UInt8
  loadByte1 : UInt8
  loadByte2 : UInt8
  loadByte3 : UInt8
  restoreByte0 : UInt8
  restoreByte1 : UInt8
  restoreByte2 : UInt8
  restoreByte3 : UInt8
  pcs : restorePc = loadPc + 4 ∧ retPc = restorePc + 4
  loadStarts : loadPc = callReturn
  frameLarge : 8 ≤ frameSize
  returnSlot : returnOffset = frameSize - 8 ∧ returnOffset + 8 ≤ frameSize ∧
    returnOffset % 8 = 0
  loadSign : sign_extend (m := 64) loadImm = BitVec.ofNat 64 returnOffset
  restoreSign : sign_extend (m := 64) restoreImm = BitVec.ofNat 64 frameSize
  loadSite : ExactInstructionSite loadPc loadByte0 loadByte1 loadByte2 loadByte3
  restoreSite : ExactInstructionSite restorePc restoreByte0 restoreByte1 restoreByte2 restoreByte3
  retSite : ExactInstructionSite retPc 0x67 0x80 0x00 0x00
  loadBase : BaseInstructionEncoding (BitVec.ofNat 8 loadByte0.toNat)
  restoreBase : BaseInstructionEncoding (BitVec.ofNat 8 restoreByte0.toNat)
  loadDecode : ∀ state, ConfiguredMachinePre EndpointMachinePc state →
    Runs (ext_decode (fetchWord (BitVec.ofNat 8 loadByte0.toNat)
      (BitVec.ofNat 8 loadByte1.toNat) (BitVec.ofNat 8 loadByte2.toNat)
      (BitVec.ofNat 8 loadByte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (loadImm, .Regidx 2#5, .Regidx 1#5, false, 8))
  restoreDecode : ∀ state, ConfiguredMachinePre EndpointMachinePc state →
    Runs (ext_decode (fetchWord (BitVec.ofNat 8 restoreByte0.toNat)
      (BitVec.ofNat 8 restoreByte1.toNat) (BitVec.ofNat 8 restoreByte2.toNat)
      (BitVec.ofNat 8 restoreByte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (restoreImm, .Regidx 2#5, .Regidx 2#5, .ADDI))
  loadInside : pcInRanges executionPcs (BitVec.ofNat 64 loadPc)
  restoreInside : pcInRanges executionPcs (BitVec.ofNat 64 restorePc)
  retInside : pcInRanges executionPcs (BitVec.ofNat 64 retPc)
  loadLocal : pcInRanges [(loadPc, retPc + 4)] (BitVec.ofNat 64 loadPc)
  restoreLocal : pcInRanges [(loadPc, retPc + 4)] (BitVec.ofNat 64 restorePc)
  retLocal : pcInRanges [(loadPc, retPc + 4)] (BitVec.ofNat 64 retPc)
  localInside : ∀ pc, pcInRanges [(loadPc, retPc + 4)] pc → pcInRanges executionPcs pc
  loadNotExit : ¬pcInList exitPcs (BitVec.ofNat 64 loadPc)
  restoreNotExit : ¬pcInList exitPcs (BitVec.ofNat 64 restorePc)
  retNotExit : ¬pcInList exitPcs (BitVec.ofNat 64 retPc)
  localAfterHost : 0x101d4 ≤ loadPc
  returnFacts : ∀ returnPc, returnPc < 2 ^ 64 →
    pcInList exitPcs (BitVec.ofNat 64 returnPc) →
    Sail.BitVec.access (BitVec.ofNat 64 returnPc) 1 = 0#1 ∧
    Sail.BitVec.update (BitVec.ofNat 64 returnPc) 0 0#1 = BitVec.ofNat 64 returnPc

/-- The shared machine result of `ld ra; addi sp; ret`. -/
theorem encoderCallFinishSeg
    (site : EncoderCallFinishSite frameSize callReturn executionPcs exitPcs)
    (fromStep stackPointer returnPc : Nat) (state : State)
    (frameLower : frameSize ≤ stackPointer) (stackFits : stackPointer < 2 ^ 64)
    (returnFits : returnPc < 2 ^ 64)
    (returnInside : pcInList exitPcs (BitVec.ofNat 64 returnPc))
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 callReturn))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (stackPointer - frameSize)))
    (savedReturn : UIntRep 8 state.mem
      (stackPointer - frameSize + site.returnOffset) returnPc)
    (loadPma : LoadPmaAllows state
      (BitVec.ofNat 64 (stackPointer - frameSize + site.returnOffset)) 8)
    (loadNoMMIO : LoadMMIOAddressExcluded
      (BitVec.ofNat 64 (stackPointer - frameSize + site.returnOffset)) 8)
    (frameAligned : (stackPointer - frameSize) % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg (pcInRanges [(site.loadPc, site.retPc + 4)]) (pcInList exitPcs)
      (fun _ _ _ _ _ => False) encoderCallFinishWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 stackPointer⟩, ⟨x1, BitVec.ofNat 64 returnPc⟩]
      fromStep 3 state after (BitVec.ofNat 64 returnPc) := by
  let frameBase := stackPointer - frameSize
  have atLoad : state.regs.get? PC = some (BitVec.ofNat 64 site.loadPc) := by
    simpa [site.loadStarts] using atPc
  have loadAddress : BitVec.ofNat 64 frameBase + sign_extend (m := 64) site.loadImm =
      BitVec.ofNat 64 (frameBase + site.returnOffset) := by
    rw [site.loadSign, ← BitVec.ofNat_add]
  obtain ⟨retired0, loadRun⟩ := configuredStackDwordLoadStep fromStep site.loadPc frameBase
    site.returnOffset returnPc state site.loadImm (.Regidx 1#5) x1
    (BitVec.ofNat 64 returnPc) site.loadByte0 site.loadByte1 site.loadByte2 site.loadByte3
    configured atLoad stack savedReturn loadPma loadNoMMIO
    (by
      have slot := site.returnSlot.2.1
      omega)
    (by
      have base16 : 16 ∣ frameBase := Nat.dvd_of_mod_eq_zero frameAligned
      have base8 : 8 ∣ frameBase := by
        rcases base16 with ⟨factor, equality⟩
        refine ⟨2 * factor, ?_⟩
        omega
      have offset8 : 8 ∣ site.returnOffset :=
        Nat.dvd_of_mod_eq_zero site.returnSlot.2.2
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add base8 offset8)) loaded loadAddress
    (by intro premise; exact wX_x1_run premise (BitVec.ofNat 64 returnPc))
    (site.loadDecode state configured) (site := site.loadSite) (base := site.loadBase)
  have seg00 := Seg.nil (pcInRanges [(site.loadPc, site.retPc + 4)]) (pcInList exitPcs)
    (fun _ _ _ _ _ => False) encoderCallFinishWrites (fun _ => False) fromStep
    configured.retiredCounter atLoad
  have seg0 := seg00.know x2 (BitVec.ofNat 64 frameBase) stack
  obtain ⟨retired0', machine1, machine1Eq, seg1⟩ := seg0.stepWitness site.loadLocal
    site.loadNotExit x1 (BitVec.ofNat 64 returnPc) (BitVec.ofNat 64 site.restorePc)
    ⟨retired0, loadRun⟩ (by simpa [site.pcs.1] using site.loadSite.advance)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [encoderCallFinishWrites]) (by decide) (by decide)
    (by simp [RegsOutside, encoderCallFinishWrites, stepBookkeeping])
  have seg1' := seg1.forget (kv' := [⟨x1, BitVec.ofNat 64 returnPc⟩]) (by simp)
  have configured1 : ConfiguredMachinePre EndpointMachinePc machine1 := by
    rw [machine1Eq]
    exact configured.afterRegisterWrite (BitVec.ofNat 64 site.loadPc) retired0' x1
      (BitVec.ofNat 64 returnPc) (by simp [instructionPreserved, platformPreserved])
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
    rw [machine1Eq]
    simpa using fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage state
      (BitVec.ofNat 64 site.loadPc) retired0' x1 (BitVec.ofNat 64 returnPc) loaded
  have stackResult : BitVec.ofNat 64 stackPointer =
      iTypeResult .ADDI site.restoreImm (BitVec.ofNat 64 frameBase) := by
    simpa [frameBase] using stackRestoreResult stackPointer frameSize site.restoreImm
      frameLower stackFits site.restoreSign
  obtain ⟨retired1, restoreRun⟩ := configuredAddiX2Step (fromStep + 1) site.restorePc
    machine1 site.restoreImm (BitVec.ofNat 64 frameBase) (BitVec.ofNat 64 stackPointer)
    site.restoreByte0 site.restoreByte1 site.restoreByte2 site.restoreByte3 configured1
    seg1'.atPc (seg1.reg x2 _ (by simp)) loaded1 stackResult
    (site.restoreDecode machine1 configured1) (site := site.restoreSite)
    (base := site.restoreBase)
  obtain ⟨retired1', machine2, machine2Eq, seg2⟩ := seg1'.stepWitness site.restoreLocal
    site.restoreNotExit x2 (BitVec.ofNat 64 stackPointer) (BitVec.ofNat 64 site.retPc)
    ⟨retired1, restoreRun⟩ (by simpa [site.pcs.2] using site.restoreSite.advance)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [encoderCallFinishWrites]) (by decide) (by decide)
    (by simp [RegsOutside, encoderCallFinishWrites, stepBookkeeping])
  have configured2 := configured.mono
    (seg2.agree instructionPreserved_disjoint_encoderCallFinishWrites) seg2.retired
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully machine2.mem := by
    have memoryEq := seg2.memEq (by simp)
    simpa [memoryEq] using loaded
  obtain ⟨retired2, retRun⟩ := configuredRetStep (fromStep + 2) site.retPc machine2
    (BitVec.ofNat 64 returnPc) configured2 seg2.atPc (seg2.reg x1 _ (by simp))
    (site.returnFacts returnPc returnFits returnInside).1 loaded2
    (read0 := site.retSite.read0) (read1 := site.retSite.read1)
    (read2 := site.retSite.read2) (read3 := site.retSite.read3)
    (pcFits := site.retSite.pcFits) (pcAligned := site.retSite.pcAligned)
  have canonicalReturn := (site.returnFacts returnPc returnFits returnInside).2
  have retRun' : Runs (try_step (fromStep + 2) false) machine2
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement machine2)
          (BitVec.ofNat 64 site.retPc) (BitVec.ofNat 64 returnPc))
        (BitVec.ofNat 64 returnPc) retired2) false := by
    simpa only [canonicalReturn] using retRun
  obtain ⟨machine3, seg3⟩ := seg2.stepJump (BitVec.ofNat 64 returnPc) site.retLocal
    site.retNotExit ⟨retired2, retRun'⟩
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, encoderCallFinishWrites, stepBookkeeping])
  exact ⟨machine3, by simpa using seg3⟩

end BinaryFv.Zesu.MachineExecution
