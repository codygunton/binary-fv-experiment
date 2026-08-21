import BinaryFv.Zesu.MachineExecution.Level1WriteSuccessSteps

/-!
# Shared Level 3 `extern_io.write_output` wrapper

Seven inlined source instances execute the same three instructions: `li a1`, `auipc ra`, and a
direct `jalr` to the exact bare-metal `write_output` leaf. This module proves that composition once.
Each concrete instance supplies only its three instruction runs and generated range facts.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

def rawWriteOutputParentPc (entry : Nat) (pc : BitVec 64) : Prop :=
  pcInRanges [(entry, entry + 12)] pc

def rawWriteOutputParentWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x1 ∨ register = x11

/-- Execute one exact `li a1, size` site for the shared output wrapper. -/
theorem configuredRawWriteOutputLengthStep (stepNo pc size : Nat) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (resultEq : iTypeResult .ADDI imm 0 = BitVec.ofNat 64 size)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (imm, .Regidx 0#5, .Regidx 11#5, .ADDI))) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x11 (BitVec.ofNat 64 size)) false :=
  writeSuccessAddiX11FromZeroStep stepNo pc size imm byte0 byte1 byte2 byte3 state configured
    atPc loaded resultEq decode site.pcFits base site.read0 site.read1 site.read2 site.read3
    site.pcAligned

/-- Execute one exact `auipc ra` site for the shared output wrapper. -/
theorem configuredRawWriteOutputCallBaseStep (stepNo pc : Nat) (imm : BitVec 20)
    (callBase : BitVec 64) (byte0 byte1 byte2 byte3 : UInt8) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (resultEq : BitVec.ofNat 64 pc + sign_extend (m := 64) (imm ++ 0x000#12) = callBase)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (imm, .Regidx 1#5, .AUIPC))) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x1 callBase) false := by
  simpa [resultEq] using configuredAuipcStep stepNo state pc imm byte0 byte1 byte2 byte3
    configured atPc loaded site.pcFits site.read0 site.read1 site.read2 site.read3 site.pcAligned
    base decode

/-- Execute one exact `jalr` site for the shared output wrapper. -/
theorem configuredRawWriteOutputCallStep (stepNo pc : Nat) (callBase : BitVec 64)
    (imm : BitVec 12) (returnPc : BitVec 64) (byte0 byte1 byte2 byte3 : UInt8) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (baseRead : state.regs.get? x1 = some callBase)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (imm, .Regidx 1#5, .Regidx 1#5)))
    (targetEq : Sail.BitVec.update (callBase + sign_extend (m := 64) imm) 0 0#1 = 0x10190)
    (returnEq : Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = returnPc)
    (targetBit1 : Sail.BitVec.access (callBase + sign_extend (m := 64) imm) 1 = 0#1) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
          0x10190 x1 returnPc) 0x10190 retired) false :=
  configuredJalrCallStep stepNo state pc callBase imm 0x10190 returnPc
    byte0 byte1 byte2 byte3 configured atPc baseRead loaded site.pcFits site.read0 site.read1
    site.read2 site.read3 site.pcAligned base decode targetEq returnEq targetBit1

private theorem encoderInlinePreserved_disjoint_rawWriteOutputParentWrites :
    RegSet.Disjoint encoderInlinePreserved rawWriteOutputParentWrites := by
  intro register preserved written
  simp [encoderInlinePreserved, rawWriteOutputParentWrites, instructionPreserved,
    platformPreserved, stepBookkeeping] at preserved written
  grind

private theorem instructionPreserved_disjoint_rawWriteOutputParentWrites :
    RegSet.Disjoint instructionPreserved rawWriteOutputParentWrites := by
  intro register preserved written
  exact encoderInlinePreserved_disjoint_rawWriteOutputParentWrites register (Or.inl preserved)
    written

/-- Exact site data needed by the shared three-instruction wrapper proof. -/
structure RawWriteOutputSite (entry expectedSize successPc : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat) where
  callBaseValue : BitVec 64
  entryFits : entry + 12 < 2 ^ 64
  expectedSizePositive : 0 < expectedSize
  expectedSizeFits : expectedSize < 2 ^ 64
  successFits : successPc < 2 ^ 64
  afterHostTransitions : 0x101d4 < entry
  returnAligned : Sail.BitVec.access (BitVec.ofNat 64 successPc) 1 = 0#1
  returnCanonical : Sail.BitVec.update (BitVec.ofNat 64 successPc) 0 0#1 =
    BitVec.ofNat 64 successPc
  advanceLength : Sail.BitVec.addInt (BitVec.ofNat 64 entry) 4 =
    BitVec.ofNat 64 (entry + 4)
  advanceBase : Sail.BitVec.addInt (BitVec.ofNat 64 (entry + 4)) 4 =
    BitVec.ofNat 64 (entry + 8)
  lengthStep : ∀ stepNo state,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 entry) →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 entry) retired x11
        (BitVec.ofNat 64 expectedSize)) false
  callBaseStep : ∀ stepNo state,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 (entry + 4)) →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 (entry + 4)) retired x1 callBaseValue) false
  callStep : ∀ stepNo state,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 (entry + 8)) →
    state.regs.get? x1 = some callBaseValue →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 (entry + 8)) 0x10190 x1 (BitVec.ofNat 64 successPc))
        0x10190 retired) false
  parentRangeMember : (entry, entry + 12) ∈ executionPcs
  outputRangeMember : (0x10190, 0x101c4) ∈ executionPcs
  exitInExitPcs : successPc ∈ exitPcs

private theorem RawWriteOutputSite.parentInside
    (site : RawWriteOutputSite entry expectedSize successPc executionPcs exitPcs)
    (offset : Nat) (offsetBound : offset < 12) :
    rawWriteOutputParentPc entry (BitVec.ofNat 64 (entry + offset)) := by
  have fits := site.entryFits
  have sumFits : entry + offset < 2 ^ 64 := by omega
  unfold rawWriteOutputParentPc
  exact ⟨(entry, entry + 12), by simp,
    by simp [Nat.mod_eq_of_lt sumFits],
    by simp [Nat.mod_eq_of_lt sumFits]; omega⟩

private theorem RawWriteOutputSite.parentNotExit
    (site : RawWriteOutputSite entry expectedSize successPc executionPcs exitPcs)
    (offset : Nat) (offsetBound : offset < 12) :
    BitVec.ofNat 64 (entry + offset) ≠ (0x10190 : BitVec 64) := by
  intro equal
  have fits := site.entryFits
  have afterHost := site.afterHostTransitions
  have sumFits : entry + offset < 2 ^ 64 := by omega
  have same := congrArg BitVec.toNat equal
  simp [Nat.mod_eq_of_lt sumFits] at same
  omega

private theorem RawWriteOutputSite.parentNotHost
    (site : RawWriteOutputSite entry expectedSize successPc executionPcs exitPcs)
    {pc : BitVec 64} (inside : rawWriteOutputParentPc entry pc) :
    ¬BareMetalHostTransitionPc pc := by
  intro observed
  have afterHost := site.afterHostTransitions
  unfold rawWriteOutputParentPc pcInRanges at inside
  rcases inside with ⟨range, member, lower, upper⟩
  simp at member
  subst range
  unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc at observed
  rcases observed with equal | equal | equal <;>
    rw [equal] at lower upper <;> simp at lower upper <;> omega

private theorem RawWriteOutputSite.parentInExecution
    (site : RawWriteOutputSite entry expectedSize successPc executionPcs exitPcs)
    {pc : BitVec 64} (inside : rawWriteOutputParentPc entry pc) :
    pcInRanges executionPcs pc := by
  unfold rawWriteOutputParentPc at inside
  unfold pcInRanges at inside ⊢
  rcases inside with ⟨range, member, lower, upper⟩
  simp at member
  subst range
  exact ⟨(entry, entry + 12), site.parentRangeMember, lower, upper⟩

private theorem RawWriteOutputSite.outputInExecution
    (site : RawWriteOutputSite entry expectedSize successPc executionPcs exitPcs)
    {pc : BitVec 64} (inside : writeOutputTracePc pc) : pcInRanges executionPcs pc := by
  unfold writeOutputTracePc writeOutputPc at inside
  rcases inside with (rfl | rfl | rfl | rfl) | rfl <;>
    exact ⟨(0x10190, 0x101c4), site.outputRangeMember, by native_decide, by native_decide⟩

private theorem liftRawWriteOutputTrace
    (site : RawWriteOutputSite entry expectedSize successPc executionPcs exitPcs)
    {exit : BitVec 64 → Prop} (template : EndpointState)
    {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace (rawWriteOutputParentPc entry) exit
      (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep count { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } atPc (site.parentInExecution inside) ?_ (by simpa using ih)
      exact endpointStep_sail fromStep { template with machine := before } middle
        (fun observed observedPc => by
          change before.regs.get? PC = some observed at observedPc
          rw [atPc] at observedPc
          cases Option.some.inj observedPc
          exact site.parentNotHost inside)
        machineStep
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count call program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

/-- One proof of every three-instruction raw encoder that calls the exact bare-metal output leaf. -/
theorem rawEncoderInstanceContract_of_writeOutputSite
    (site : RawWriteOutputSite entry expectedSize successPc executionPcs exitPcs) :
    RawEncoderInstanceContract entry expectedSize executionPcs exitPcs successPc := by
  refine ⟨fun _ => 8, (by intro _; simp [level2ContractFuel]), ?_⟩
  intro args fromStep before entryPre
  rcases entryPre with ⟨atPc, source, size, bytes, outside, loaded, access⟩
  have seg0 := (Seg.nil (rawWriteOutputParentPc entry) (fun pc => pc = 0x10190)
    rawWriteOutputParentWrites (fun _ => False) fromStep
    (childSummary := fun _ _ _ _ _ => False) access.configured.retiredCounter atPc).know
      x10 (BitVec.ofNat 64 args.sourceAddress) source
  obtain ⟨r0, run0⟩ := site.lengthStep fromStep before.machine access.configured atPc loaded
  have seg1 := seg0.stepKnown
    (site.parentInside 0 (by omega)) (site.parentNotExit 0 (by omega))
    x11 (BitVec.ofNat 64 expectedSize) (BitVec.ofNat 64 (entry + 4)) r0 run0
    site.advanceLength (by intro r h; exact Or.inl h) (Or.inr (Or.inr rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have cfg1 := access.configured.mono
    (seg1.agree instructionPreserved_disjoint_rawWriteOutputParentWrites) seg1.retired
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0 x11
        (BitVec.ofNat 64 expectedSize)).mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨r1, run1⟩ := site.callBaseStep (fromStep + 1)
    (afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0 x11
      (BitVec.ofNat 64 expectedSize)) cfg1 seg1.atPc loaded1
  have seg2 := seg1.stepKnown
    (site.parentInside 4 (by omega)) (site.parentNotExit 4 (by omega))
    x1 site.callBaseValue (BitVec.ofNat 64 (entry + 8)) r1 run1
    site.advanceBase (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have cfg2 := access.configured.mono
    (seg2.agree instructionPreserved_disjoint_rawWriteOutputParentWrites) seg2.retired
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite
        (afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0 x11
          (BitVec.ofNat 64 expectedSize))
        (BitVec.ofNat 64 (entry + 4)) r1 x1 site.callBaseValue).mem := by
    simpa [seg2.memEq (by simp)] using loaded
  obtain ⟨r2, callRun⟩ := site.callStep (fromStep + 2)
    (afterRegisterWrite
      (afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0 x11
        (BitVec.ofNat 64 expectedSize))
      (BitVec.ofNat 64 (entry + 4)) r1 x1 site.callBaseValue)
    cfg2 seg2.atPc (seg2.reg x1 site.callBaseValue (by simp)) loaded2
  let parentMachine := afterRegisterWrite
    (afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0 x11
      (BitVec.ofNat 64 expectedSize))
    (BitVec.ofNat 64 (entry + 4)) r1 x1 site.callBaseValue
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement parentMachine)
      (BitVec.ofNat 64 (entry + 8)) 0x10190 x1 (BitVec.ofNat 64 successPc))
    0x10190 r2
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes parentMachine (BitVec.ofNat 64 (entry + 8))
    0x10190 r2 x1 (BitVec.ofNat 64 successPc)
  have callAtPc : callMachine.regs.get? PC = some 0x10190 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      callLinkState, Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    have base : callMachine.mem = parentMachine.mem := rfl
    exact base.trans (seg2.memEq (by simp))
  have callPrefix : ConfinedPrefix (rawWriteOutputParentPc entry) (fun pc => pc = 0x10190)
      (fun _ _ _ _ _ => False) (fromStep + 2) 1 parentMachine callMachine :=
    ConfinedPrefix.ownStep seg2.atPc
      (site.parentInside 8 (by omega)) (site.parentNotExit 8 (by omega)) callRun
  have parentMachineTrace := seg2.confined.trans callPrefix 0 callMachine
    (.exitAt _ _ 0x10190 callAtPc rfl)
  have parentTrace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep 3 before callState := by
    simpa [callState] using liftRawWriteOutputTrace site before parentMachineTrace
  have callConfigured : ConfiguredMachinePre EndpointMachinePc callMachine :=
    configuredAfterWriteSuccessCall (BitVec.ofNat 64 (entry + 8)) 0x10190
      (BitVec.ofNat 64 successPc) r2 cfg2
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have fullPmaEq : callMachine.regs.get? pma_regions = before.machine.regs.get? pma_regions :=
    callPmaEq.trans (seg2.writes.get pma_regions (by
      simp [rawWriteOutputParentWrites, stepBookkeeping]))
  obtain ⟨after, output⟩ := writeOutputHandoff (fromStep + 3) args.sourceAddress args.bytes
    (BitVec.ofNat 64 successPc) callState (by simpa [callState] using callAtPc)
    (by simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert])
    (by change callMachine.regs.get? x10 = some (BitVec.ofNat 64 args.sourceAddress)
        exact (callWrites.get x10 (by decide)).trans
          (seg2.reg x10 (BitVec.ofNat 64 args.sourceAddress) (by simp)))
    (by change callMachine.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size)
        rw [size]
        exact (callWrites.get x11 (by decide)).trans
          (seg2.reg x11 (BitVec.ofNat 64 expectedSize) (by simp)))
    (by
      have bound := bytes.1
      have positive := site.expectedSizePositive
      rw [size] at bound
      omega)
    (by rw [size]; exact site.expectedSizeFits)
    (by simpa [callState, callMemEq] using bytes) outside
    (dataPmaAllows_of_pma_regions_eq fullPmaEq access.outputBufferStore)
    (dataPmaAllows_of_pma_regions_eq fullPmaEq access.outputLengthStore)
    site.returnAligned callConfigured (by simpa [callState, callMemEq] using loaded)
  have outputTrace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      (fromStep + 3) 5 callState after := output.trace.weaken (fun _ h => site.outputInExecution h)
  have outputAtPc : EndpointPc after = some (BitVec.ofNat 64 successPc) := by
    simpa [EndpointPc, site.returnCanonical] using output.atPc
  have wholeTrace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep 8 before after := by
    simpa [Nat.add_assoc] using parentTrace.append outputTrace
  have parentAgree : Agree encoderInlinePreserved before.machine callMachine :=
    (seg2.writes.agree encoderInlinePreserved_disjoint_rawWriteOutputParentWrites).trans
      (callWrites.agree (by
        intro register preserved written
        apply encoderInlinePreserved_disjoint_rawWriteOutputParentWrites register preserved
        rcases written with bookkeeping | rfl
        · exact Or.inl bookkeeping
        · exact Or.inr (Or.inl rfl)))
  have outputAgree : Agree encoderInlinePreserved callMachine after.machine := by
    intro register preserved
    rcases preserved with instruction | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact output.preserved register instruction
    all_goals
      apply output.writes.get
      simp [writeOutputWrites, stepBookkeeping]
  refine ⟨8, after, (), by omega, Nat.le_refl 8, wholeTrace,
    ⟨BitVec.ofNat 64 successPc, outputAtPc, ?_⟩, trivial, ?_⟩
  · unfold pcInList
    simpa [Nat.mod_eq_of_lt site.successFits] using site.exitInExitPcs
  · refine ⟨outputAtPc, ?_, ?_, ?_, ?_, ?_, parentAgree.trans outputAgree,
      output.configured.retiredCounter, output.loaded, ?_⟩
    · simpa [callState] using output.stdout
    · simpa [callState] using output.stdin
    · simpa [callState] using output.cursor
    · simpa [callState] using output.exitCode
    · intro address outsideMemory
      exact (output.memory address outsideMemory).trans
        (congrArg (fun mem => mem.get? address) callMemEq)
    · exact (seg2.aux.trans
        (AuxStateAgree.callRetirement parentMachine (BitVec.ofNat 64 (entry + 8))
          0x10190 r2 x1 (BitVec.ofNat 64 successPc))).trans output.aux

/-- Build a shared output site from literal instruction data. Every default is checked at the
concrete call site, where all bytes, immediates, addresses, and generated ranges are known. -/
def rawWriteOutputSiteOfLiterals (entry expectedSize successPc : Nat)
    (callBaseValue : BitVec 64) (lengthImm : BitVec 12) (callBaseImm : BitVec 20)
    (callImm : BitVec 12)
    (lengthByte0 lengthByte1 lengthByte2 lengthByte3 : UInt8)
    (baseByte0 baseByte1 baseByte2 baseByte3 : UInt8)
    (callByte0 callByte1 callByte2 callByte3 : UInt8)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat)
    (lengthSite : ExactInstructionSite entry lengthByte0 lengthByte1 lengthByte2 lengthByte3 := by
      native_decide)
    (baseSite : ExactInstructionSite (entry + 4) baseByte0 baseByte1 baseByte2 baseByte3 := by
      native_decide)
    (callSite : ExactInstructionSite (entry + 8) callByte0 callByte1 callByte2 callByte3 := by
      native_decide)
    (lengthBase : BaseInstructionEncoding (BitVec.ofNat 8 lengthByte0.toNat) := by rfl)
    (baseBase : BaseInstructionEncoding (BitVec.ofNat 8 baseByte0.toNat) := by rfl)
    (callBase : BaseInstructionEncoding (BitVec.ofNat 8 callByte0.toNat) := by rfl)
    (lengthResult : iTypeResult .ADDI lengthImm 0 = BitVec.ofNat 64 expectedSize := by
      native_decide)
    (baseResult : BitVec.ofNat 64 (entry + 4) +
        sign_extend (m := 64) (callBaseImm ++ 0x000#12) = callBaseValue := by native_decide)
    (lengthDecode : ∀ state, ConfiguredMachinePre EndpointMachinePc state →
        Runs (ext_decode (fetchWord (BitVec.ofNat 8 lengthByte0.toNat)
          (BitVec.ofNat 8 lengthByte1.toNat) (BitVec.ofNat 8 lengthByte2.toNat)
          (BitVec.ofNat 8 lengthByte3.toNat)))
          (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
          (.ITYPE (lengthImm, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
      intro state configured; write_success_decode configured)
    (baseDecode : ∀ state, ConfiguredMachinePre EndpointMachinePc state →
        Runs (ext_decode (fetchWord (BitVec.ofNat 8 baseByte0.toNat)
          (BitVec.ofNat 8 baseByte1.toNat) (BitVec.ofNat 8 baseByte2.toNat)
          (BitVec.ofNat 8 baseByte3.toNat)))
          (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
          (.UTYPE (callBaseImm, .Regidx 1#5, .AUIPC)) := by
      intro state configured; write_success_decode configured)
    (callDecode : ∀ state, ConfiguredMachinePre EndpointMachinePc state →
        Runs (ext_decode (fetchWord (BitVec.ofNat 8 callByte0.toNat)
          (BitVec.ofNat 8 callByte1.toNat) (BitVec.ofNat 8 callByte2.toNat)
          (BitVec.ofNat 8 callByte3.toNat)))
          (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
          (.JALR (callImm, .Regidx 1#5, .Regidx 1#5)) := by
      intro state configured; write_success_decode configured)
    (targetEq : Sail.BitVec.update (callBaseValue + sign_extend (m := 64) callImm) 0 0#1 =
        0x10190 := by native_decide)
    (returnEq : Sail.BitVec.addInt (BitVec.ofNat 64 (entry + 8)) 4 =
        BitVec.ofNat 64 successPc := by native_decide)
    (targetBit1 : Sail.BitVec.access (callBaseValue + sign_extend (m := 64) callImm) 1 = 0#1 := by
      native_decide)
    (entryFits : entry + 12 < 2 ^ 64 := by native_decide)
    (expectedSizePositive : 0 < expectedSize := by native_decide)
    (expectedSizeFits : expectedSize < 2 ^ 64 := by native_decide)
    (successFits : successPc < 2 ^ 64 := by native_decide)
    (afterHostTransitions : 0x101d4 < entry := by native_decide)
    (returnAligned : Sail.BitVec.access (BitVec.ofNat 64 successPc) 1 = 0#1 := by native_decide)
    (returnCanonical : Sail.BitVec.update (BitVec.ofNat 64 successPc) 0 0#1 =
      BitVec.ofNat 64 successPc := by native_decide)
    (parentRangeMember : (entry, entry + 12) ∈ executionPcs := by native_decide)
    (outputRangeMember : (0x10190, 0x101c4) ∈ executionPcs := by native_decide)
    (exitInExitPcs : successPc ∈ exitPcs := by native_decide) :
    RawWriteOutputSite entry expectedSize successPc executionPcs exitPcs := {
  callBaseValue
  entryFits
  expectedSizePositive
  expectedSizeFits
  successFits
  afterHostTransitions
  returnAligned
  returnCanonical
  advanceLength := lengthSite.advance
  advanceBase := baseSite.advance
  lengthStep := by
    intro stepNo state configured atPc loaded
    exact configuredRawWriteOutputLengthStep stepNo entry expectedSize lengthImm
      lengthByte0 lengthByte1 lengthByte2 lengthByte3 state configured atPc loaded lengthSite
      lengthBase lengthResult (lengthDecode state configured)
  callBaseStep := by
    intro stepNo state configured atPc loaded
    exact configuredRawWriteOutputCallBaseStep stepNo (entry + 4) callBaseImm callBaseValue
      baseByte0 baseByte1 baseByte2 baseByte3 state configured atPc loaded baseSite baseBase
      baseResult (baseDecode state configured)
  callStep := by
    intro stepNo state configured atPc baseRead loaded
    exact configuredRawWriteOutputCallStep stepNo (entry + 8) callBaseValue callImm
      (BitVec.ofNat 64 successPc) callByte0 callByte1 callByte2 callByte3 state configured atPc
      baseRead loaded callSite callBase (callDecode state configured) targetEq returnEq targetBit1
  parentRangeMember
  outputRangeMember
  exitInExitPcs
}

/-- Production `0x161c0: auipc a0,1` for the constant failure record. -/
theorem writeFailureRecordAddressHighStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x161c0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x161c0 retired x10 0x171c0) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x161c0
  have pcRead : Runs (readReg PC) premise premise 0x161c0 := by
    apply readReg_run
    simp [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (1, .Regidx 10#5, .AUIPC))) premise
      { premise with regs := premise.regs.insert x10 0x171c0 } (.Retire_Success ()) := by
    change Runs (execute_UTYPE 1 (.Regidx 10#5) .AUIPC) _ _ _
    simpa using execute_UTYPE_auipc_run premise _ 1 (.Regidx 10#5) 0x161c0 pcRead
      (wX_x10_run premise 0x171c0)
  exact configuredRegisterWriteStep stepNo 0x161c0 state x10 0x171c0
    (.UTYPE (1, .Regidx 10#5, .AUIPC)) 0x17 0x15 0x00 0x00 configured atPc loaded
    (by decode_run) execute (base := by rfl)

/-- Production `0x161c4: addi a0,a0,1544` for the constant failure record. -/
theorem writeFailureRecordAddressLowStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x161c4)
    (source : state.regs.get? x10 = some 0x171c0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x161c4 retired x10 0x177c8) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x161c4
  have sourceAtPremise : premise.regs.get? x10 = some 0x171c0 :=
    (stepPremiseState_writes state 0x161c4).get x10 (by decide) |>.trans source
  have execute : Runs (execute (.ITYPE (0x608, .Regidx 10#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 0x177c8 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x608 (.Regidx 10#5) (.Regidx 10#5) .ADDI) _ _ _
    simpa using execute_ITYPE_run premise _ 0x608 (.Regidx 10#5) (.Regidx 10#5) .ADDI
      0x171c0 (rX_x10_run premise 0x171c0 sourceAtPremise)
      (wX_x10_run premise 0x177c8)
  exact configuredRegisterWriteStep stepNo 0x161c4 state x10 0x177c8
    (.ITYPE (0x608, .Regidx 10#5, .Regidx 10#5, .ADDI)) 0x13 0x05 0x85 0x60
    configured atPc loaded (by decode_run) execute (base := by rfl)

/-- Production `0x161c8: li a1,6` for the constant failure record. -/
theorem writeFailureRecordLengthStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x161c8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x161c8 retired x11 6) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  exact configuredRawWriteOutputLengthStep stepNo 0x161c8 6 6
    0x93 0x05 0x60 0x00 state configured atPc loaded (by native_decide) (by rfl)
    (by native_decide) (by decode_run)

/-- Production `0x161cc: auipc t1,-6` for the constant failure tail jump. -/
theorem writeFailureRecordJumpBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x161cc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x161cc retired x6 0x101cc) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x161cc
  have pcRead : Runs (readReg PC) premise premise 0x161cc := by
    apply readReg_run
    simp [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (0xffffa, .Regidx 6#5, .AUIPC))) premise
      { premise with regs := premise.regs.insert x6 0x101cc } (.Retire_Success ()) := by
    change Runs (execute_UTYPE 0xffffa (.Regidx 6#5) .AUIPC) _ _ _
    simpa using execute_UTYPE_auipc_run premise _ 0xffffa (.Regidx 6#5) 0x161cc pcRead
      (wX_x6_run premise 0x101cc)
  exact configuredRegisterWriteStep stepNo 0x161cc state x6 0x101cc
    (.UTYPE (0xffffa, .Regidx 6#5, .AUIPC)) 0x17 0xa3 0xff 0xff configured atPc loaded
    (by decode_run) execute (base := by rfl)

/-- Production `0x161d0: jr -60(t1)` tail-jumps to `write_output`. -/
theorem writeFailureRecordTailJumpStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x161d0)
    (source : state.regs.get? x6 = some 0x101cc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x161d0 0x10190)
        0x10190 retired) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x161d0
  have sourceAtPremise : premise.regs.get? x6 = some 0x101cc :=
    (stepPremiseState_writes state 0x161d0).get x6 (by decide) |>.trans source
  exact configuredJrOffsetStep stepNo 0x161d0 state 0xfc4 (.Regidx 6#5) 0x101cc 0x10190
    0x67 0x00 0x43 0xfc configured atPc loaded (by decode_run)
    (by simpa using rX_x6_run premise 0x101cc sourceAtPremise) (by native_decide)
    (by native_decide) (by native_decide) (by rfl)

def writeFailureTailPc (pc : BitVec 64) : Prop :=
  pcInRanges [(0x161c0, 0x161d4)] pc

def writeFailureTailWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x6 ∨ register = x10 ∨ register = x11

private theorem instructionPreserved_disjoint_writeFailureTailWrites :
    RegSet.Disjoint instructionPreserved writeFailureTailWrites := by
  intro register preserved written
  simp [instructionPreserved, platformPreserved, writeFailureTailWrites,
    stepBookkeeping] at preserved written
  grind

set_option genInjectivity false in
/-- The shared five-step failure-record tail schedule, before the output leaf executes. -/
structure WriteFailureTailHandoff (fromStep : Nat) (before after : State) : Prop where
  trace : ConfinedPrefix writeFailureTailPc (fun pc => pc = 0x10190)
    (fun _ _ _ _ _ => False) fromStep 5 before after
  atPc : after.regs.get? PC = some 0x10190
  link : after.regs.get? x1 = some 0x14d24
  buffer : after.regs.get? x10 = some 0x177c8
  count : after.regs.get? x11 = some 6
  writes : WritesOnlyRegs writeFailureTailWrites before after
  memEq : after.mem = before.mem
  aux : AuxStateAgree before after
  retired : RetiredCounterPresent after
  configured : ConfiguredMachinePre EndpointMachinePc after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.mem

/-- Compose the constant failure address, length, and tail jump once for the failure family. -/
theorem writeFailureTailHandoff (fromStep : Nat) (before : State)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (atPc : before.regs.get? PC = some 0x161c0)
    (link : before.regs.get? x1 = some 0x14d24)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after, WriteFailureTailHandoff fromStep before after := by
  have seg0 := (Seg.nil writeFailureTailPc (fun pc => pc = 0x10190)
    writeFailureTailWrites (fun _ => False) fromStep
    (childSummary := fun _ _ _ _ _ => False) configured.retiredCounter atPc).know
      x1 0x14d24 link
  obtain ⟨r0, run0⟩ := writeFailureRecordAddressHighStep fromStep before configured atPc loaded
  obtain ⟨s1, seg1⟩ := seg0.step (by
      unfold writeFailureTailPc pcInRanges
      exact ⟨(0x161c0, 0x161d4), by simp, by native_decide, by native_decide⟩)
    (by native_decide) x10 0x171c0 0x161c4 ⟨r0, run0⟩
    (by native_decide) (by intro r h; exact Or.inl h)
    (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have cfg1 := configured.mono
    (seg1.agree instructionPreserved_disjoint_writeFailureTailWrites) seg1.retired
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully s1.mem := by
    simpa [seg1.memEq (by simp)] using loaded
  have seg1' := seg1.forget (kv' := [⟨x1, 0x14d24⟩]) (by simp)
  obtain ⟨r1, run1⟩ := writeFailureRecordAddressLowStep (fromStep + 1) s1 cfg1 seg1.atPc
    (seg1.reg x10 0x171c0 (by simp)) loaded1
  obtain ⟨s2, seg2⟩ := seg1'.step (by
      unfold writeFailureTailPc pcInRanges
      exact ⟨(0x161c0, 0x161d4), by simp, by native_decide, by native_decide⟩)
    (by native_decide) x10 0x177c8 0x161c8 ⟨r1, run1⟩
    (by native_decide) (by intro r h; exact Or.inl h)
    (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have cfg2 := configured.mono
    (seg2.agree instructionPreserved_disjoint_writeFailureTailWrites) seg2.retired
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully s2.mem := by
    simpa [seg2.memEq (by simp)] using loaded
  obtain ⟨r2, run2⟩ := writeFailureRecordLengthStep (fromStep + 2) s2 cfg2 seg2.atPc loaded2
  obtain ⟨s3, seg3⟩ := seg2.step (by
      unfold writeFailureTailPc pcInRanges
      exact ⟨(0x161c0, 0x161d4), by simp, by native_decide, by native_decide⟩)
    (by native_decide) x11 6 0x161cc ⟨r2, run2⟩
    (by native_decide) (by intro r h; exact Or.inl h)
    (Or.inr (Or.inr (Or.inr rfl))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have cfg3 := configured.mono
    (seg3.agree instructionPreserved_disjoint_writeFailureTailWrites) seg3.retired
  have loaded3 : Artifacts.programImage.fileBytesLoadedFaithfully s3.mem := by
    simpa [seg3.memEq (by simp)] using loaded
  obtain ⟨r3, run3⟩ := writeFailureRecordJumpBaseStep (fromStep + 3) s3 cfg3 seg3.atPc loaded3
  obtain ⟨s4, seg4⟩ := seg3.step (by
      unfold writeFailureTailPc pcInRanges
      exact ⟨(0x161c0, 0x161d4), by simp, by native_decide, by native_decide⟩)
    (by native_decide) x6 0x101cc 0x161d0 ⟨r3, run3⟩
    (by native_decide) (by intro r h; exact Or.inl h)
    (Or.inr (Or.inl rfl)) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have cfg4 := configured.mono
    (seg4.agree instructionPreserved_disjoint_writeFailureTailWrites) seg4.retired
  have loaded4 : Artifacts.programImage.fileBytesLoadedFaithfully s4.mem := by
    simpa [seg4.memEq (by simp)] using loaded
  obtain ⟨s5, seg5⟩ := seg4.stepJump 0x10190
    (by
      unfold writeFailureTailPc pcInRanges
      exact ⟨(0x161c0, 0x161d4), by simp, by native_decide, by native_decide⟩)
    (by native_decide)
    (writeFailureRecordTailJumpStep (fromStep + 4) s4 cfg4 seg4.atPc
      (seg4.reg x6 0x101cc (by simp)) loaded4)
    (by intro r h; exact Or.inl h) (by simp [RegsOutside, stepBookkeeping])
  refine ⟨s5, (by simpa using seg5.confined), seg5.atPc, seg5.reg x1 0x14d24 (by simp),
    seg5.reg x10 0x177c8 (by simp), seg5.reg x11 6 (by simp), seg5.writes,
    seg5.memEq (by simp), seg5.aux, seg5.retired, ?_, ?_⟩
  · exact configured.mono
      (seg5.agree instructionPreserved_disjoint_writeFailureTailWrites) seg5.retired
  · simpa [seg5.memEq (by simp)] using loaded

private theorem encoderInlinePreserved_disjoint_writeFailureTailWrites :
    RegSet.Disjoint encoderInlinePreserved writeFailureTailWrites := by
  intro register preserved written
  simp [encoderInlinePreserved, instructionPreserved, platformPreserved,
    writeFailureTailWrites, stepBookkeeping] at preserved written
  grind

private theorem abiCalleePreserved_disjoint_writeFailureTailWrites :
    RegSet.Disjoint abiCalleePreserved writeFailureTailWrites := by
  intro register preserved written
  simp [abiCalleePreserved, writeFailureTailWrites, stepBookkeeping] at preserved written
  grind

private theorem encoderInlinePreserved_disjoint_writeOutputWrites :
    RegSet.Disjoint encoderInlinePreserved writeOutputWrites := by
  intro register preserved written
  simp [encoderInlinePreserved, instructionPreserved, platformPreserved, writeOutputWrites]
    at preserved written
  grind

private theorem abiCalleePreserved_disjoint_writeOutputWrites :
    RegSet.Disjoint abiCalleePreserved writeOutputWrites := by
  intro register preserved written
  simp [abiCalleePreserved, writeOutputWrites] at preserved written
  grind

private theorem writeFailureTailPc_in_execution {pc : BitVec 64}
    (inside : writeFailureTailPc pc) :
    pcInRanges Elflings.writeFailureRawLine127ExecutionPcRanges pc := by
  unfold writeFailureTailPc at inside
  unfold pcInRanges at inside ⊢
  rcases inside with ⟨range, member, lower, upper⟩
  simp at member
  subst range
  exact ⟨(0x161c0, 0x161d4), by
    simp [Elflings.writeFailureRawLine127ExecutionPcRanges], lower, upper⟩

private theorem writeFailureTailPc_not_host {pc : BitVec 64}
    (inside : writeFailureTailPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro host
  unfold writeFailureTailPc pcInRanges at inside
  rcases inside with ⟨range, member, lower, upper⟩
  simp at member
  subst range
  unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc
    exitContextStorePc at host
  rcases host with equal | equal | equal <;>
    rw [equal] at lower upper <;> simp at lower upper

private theorem writeFailureOutputPc_in_execution {pc : BitVec 64}
    (inside : writeOutputTracePc pc) :
    pcInRanges Elflings.writeFailureRawLine127ExecutionPcRanges pc := by
  unfold writeOutputTracePc writeOutputPc at inside
  rcases inside with (rfl | rfl | rfl | rfl) | rfl <;>
    exact ⟨(0x10190, 0x101c4), by
      simp [Elflings.writeFailureRawLine127ExecutionPcRanges],
      by native_decide, by native_decide⟩

private theorem liftWriteFailureTailTrace (template : EndpointState)
    {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace writeFailureTailPc (fun pc => pc = 0x10190)
      (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeFailureRawLine127ExecutionPcRanges)
      fromStep count { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } atPc (writeFailureTailPc_in_execution inside)
        ?_ (by simpa using ih)
      exact endpointStep_sail fromStep { template with machine := before } middle
        (fun observed observedPc => by
          change before.regs.get? PC = some observed at observedPc
          rw [atPc] at observedPc
          cases Option.some.inj observedPc
          exact writeFailureTailPc_not_host inside)
        machineStep
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count call program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

/-- Prove the failure writer from one shared tail schedule and the exact output leaf. -/
theorem writeFailureRecordInstanceContract_of_tailSchedule :
    WriteFailureRecordInstanceContract := by
  refine ⟨10, (by simp [level2ContractFuel]), ?_⟩
  intro args fromStep before entry
  rcases entry with ⟨⟨atPc, loaded, access⟩, link⟩
  obtain ⟨callMachine, tail⟩ :=
    writeFailureTailHandoff fromStep before.machine access.configured atPc link loaded
  let callState : EndpointState := { before with machine := callMachine }
  have parentScoped : ScopedTrace writeFailureTailPc (fun pc => pc = 0x10190)
      (fun _ _ _ _ _ => False) fromStep 5 before.machine callMachine := by
    simpa using tail.trace 0 callMachine
      (ScopedTrace.exitAt (fromStep + 5) callMachine 0x10190 tail.atPc rfl)
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeFailureRawLine127ExecutionPcRanges)
      fromStep 5 before callState := by
    simpa [callState] using liftWriteFailureTailTrace before parentScoped
  have staticRep : BytesRep callMachine.mem 0x177c8 failureRecordBytes := by
    refine ⟨by native_decide, ?_⟩
    intro index inBounds
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
        index = 5 := by
      simp [failureRecordBytes] at inBounds
      omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [failureRecordBytes] using tail.loaded _ _ (by native_decide)
  have outside : ∀ index, index < failureRecordBytes.size →
      ¬writeOutputMemory (0x177c8 + index) := by
    intro index inBounds inside
    unfold writeOutputMemory Region.union byteRange at inside
    simp [failureRecordBytes] at inBounds
    simp [Elflings.ioContextAddress] at inside
    rcases inside with inside | inside <;> omega
  have pmaEq := tail.writes.get pma_regions (by
    simp [writeFailureTailWrites, stepBookkeeping])
  obtain ⟨after, output⟩ := writeOutputHandoff (fromStep + 5) 0x177c8 failureRecordBytes
    0x14d24 callState (by simpa [callState] using tail.atPc)
    (by simpa [callState] using tail.link) (by simpa [callState] using tail.buffer)
    (by simpa [callState, failureRecordBytes] using tail.count)
    (by native_decide) (by native_decide) (by simpa [callState] using staticRep) outside
    (dataPmaAllows_of_pma_regions_eq pmaEq access.outputBufferStore)
    (dataPmaAllows_of_pma_regions_eq pmaEq access.outputLengthStore)
    (by native_decide) tail.configured tail.loaded
  have outputTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeFailureRawLine127ExecutionPcRanges)
      (fromStep + 5) 5 callState after :=
    output.trace.weaken (fun _ h => writeFailureOutputPc_in_execution h)
  have wholeTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeFailureRawLine127ExecutionPcRanges)
      fromStep 10 before after := by
    simpa [Nat.add_assoc] using parentTrace.append outputTrace
  have parentInlineAgree : Agree encoderInlinePreserved before.machine callMachine :=
    tail.writes.agree encoderInlinePreserved_disjoint_writeFailureTailWrites
  have outputInlineAgree : Agree encoderInlinePreserved callMachine after.machine :=
    output.writes.agree encoderInlinePreserved_disjoint_writeOutputWrites
  have parentCallAgree : Agree abiCalleePreserved before.machine callMachine :=
    tail.writes.agree abiCalleePreserved_disjoint_writeFailureTailWrites
  have outputCallAgree : Agree abiCalleePreserved callMachine after.machine :=
    output.writes.agree abiCalleePreserved_disjoint_writeOutputWrites
  have outputAtPc : EndpointPc after = some 0x14d24 := by
    simpa [EndpointPc] using output.atPc
  refine ⟨10, after, (), by omega, Nat.le_refl 10, wholeTrace,
    ⟨0x14d24, outputAtPc, ?_⟩, trivial, ?_⟩
  · unfold pcInList
    simpa [Elflings.writeFailureRawLine127ExitPcs]
  · refine ⟨⟨outputAtPc, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [callState] using output.stdout
    · simpa [callState] using output.stdin
    · simpa [callState] using output.cursor
    · simpa [callState] using output.exitCode
    · intro address outsideMemory
      exact (output.memory address outsideMemory).trans
        (congrArg (fun mem => mem.get? address) tail.memEq)
    · exact ⟨parentInlineAgree.trans outputInlineAgree, output.configured.retiredCounter,
        output.loaded, tail.aux.trans output.aux⟩
    · exact ⟨parentCallAgree.trans outputCallAgree, output.configured.retiredCounter,
        output.loaded, (tail.aux.trans output.aux).1, (tail.aux.trans output.aux).2.1,
        (tail.aux.trans output.aux).2.2⟩

private def parentHashWriteOutputSite : RawWriteOutputSite 0x14e2c 32 0x14e38
    Elflings.writeSuccessRawLine135ExecutionPcRanges Elflings.writeSuccessRawLine135ExitPcs :=
  rawWriteOutputSiteOfLiterals 0x14e2c 32 0x14e38 0xfe30 32 0xffffb 0x360
    0x93 0x05 0x00 0x02 0x97 0xb0 0xff 0xff 0xe7 0x80 0x00 0x36
    Elflings.writeSuccessRawLine135ExecutionPcRanges Elflings.writeSuccessRawLine135ExitPcs

/-- The parent-hash output wrapper is a thin application of the shared output theorem. -/
theorem writeSuccessParentHashInstanceContract : WriteSuccessParentHashInstanceContract :=
  rawEncoderInstanceContract_of_writeOutputSite parentHashWriteOutputSite

private def feeRecipientWriteOutputSite : RawWriteOutputSite 0x14e3c 20 0x14e48
    Elflings.writeSuccessRawLine136ExecutionPcRanges Elflings.writeSuccessRawLine136ExitPcs :=
  rawWriteOutputSiteOfLiterals 0x14e3c 20 0x14e48 0xfe40 20 0xffffb 0x350
    0x93 0x05 0x40 0x01 0x97 0xb0 0xff 0xff 0xe7 0x80 0x00 0x35
    Elflings.writeSuccessRawLine136ExecutionPcRanges Elflings.writeSuccessRawLine136ExitPcs

/-- The fee-recipient output wrapper uses the shared output theorem. -/
theorem writeSuccessFeeRecipientInstanceContract : WriteSuccessFeeRecipientInstanceContract :=
  rawEncoderInstanceContract_of_writeOutputSite feeRecipientWriteOutputSite

private def stateRootWriteOutputSite : RawWriteOutputSite 0x14e4c 32 0x14e58
    Elflings.writeSuccessRawLine137ExecutionPcRanges Elflings.writeSuccessRawLine137ExitPcs :=
  rawWriteOutputSiteOfLiterals 0x14e4c 32 0x14e58 0xfe50 32 0xffffb 0x340
    0x93 0x05 0x00 0x02 0x97 0xb0 0xff 0xff 0xe7 0x80 0x00 0x34
    Elflings.writeSuccessRawLine137ExecutionPcRanges Elflings.writeSuccessRawLine137ExitPcs

/-- The state-root output wrapper uses the shared output theorem. -/
theorem writeSuccessStateRootInstanceContract : WriteSuccessStateRootInstanceContract :=
  rawEncoderInstanceContract_of_writeOutputSite stateRootWriteOutputSite

private def receiptsRootWriteOutputSite : RawWriteOutputSite 0x14e5c 32 0x14e68
    Elflings.writeSuccessRawLine138ExecutionPcRanges Elflings.writeSuccessRawLine138ExitPcs :=
  rawWriteOutputSiteOfLiterals 0x14e5c 32 0x14e68 0xfe60 32 0xffffb 0x330
    0x93 0x05 0x00 0x02 0x97 0xb0 0xff 0xff 0xe7 0x80 0x00 0x33
    Elflings.writeSuccessRawLine138ExecutionPcRanges Elflings.writeSuccessRawLine138ExitPcs

/-- The receipts-root output wrapper uses the shared output theorem. -/
theorem writeSuccessReceiptsRootInstanceContract : WriteSuccessReceiptsRootInstanceContract :=
  rawEncoderInstanceContract_of_writeOutputSite receiptsRootWriteOutputSite

private def logsBloomWriteOutputSite : RawWriteOutputSite 0x14e6c 256 0x14e78
    Elflings.writeSuccessRawLine139ExecutionPcRanges Elflings.writeSuccessRawLine139ExitPcs :=
  rawWriteOutputSiteOfLiterals 0x14e6c 256 0x14e78 0xfe70 0x100 0xffffb 0x320
    0x93 0x05 0x00 0x10 0x97 0xb0 0xff 0xff 0xe7 0x80 0x00 0x32
    Elflings.writeSuccessRawLine139ExecutionPcRanges Elflings.writeSuccessRawLine139ExitPcs

/-- The logs-bloom output wrapper uses the shared output theorem. -/
theorem writeSuccessLogsBloomInstanceContract : WriteSuccessLogsBloomInstanceContract :=
  rawEncoderInstanceContract_of_writeOutputSite logsBloomWriteOutputSite

private def blockHashWriteOutputSite : RawWriteOutputSite 0x14ed8 32 0x14ee4
    Elflings.writeSuccessRawLine147ExecutionPcRanges Elflings.writeSuccessRawLine147ExitPcs :=
  rawWriteOutputSiteOfLiterals 0x14ed8 32 0x14ee4 0xfedc 32 0xffffb 0x2b4
    0x93 0x05 0x00 0x02 0x97 0xb0 0xff 0xff 0xe7 0x80 0x40 0x2b
    Elflings.writeSuccessRawLine147ExecutionPcRanges Elflings.writeSuccessRawLine147ExitPcs

/-- The block-hash output wrapper uses the shared output theorem. -/
theorem writeSuccessBlockHashInstanceContract : WriteSuccessBlockHashInstanceContract :=
  rawEncoderInstanceContract_of_writeOutputSite blockHashWriteOutputSite

private def parentBeaconRootWriteOutputSite : RawWriteOutputSite 0x15730 32 0x1573c
    Elflings.writeSuccessRawLine156ExecutionPcRanges Elflings.writeSuccessRawLine156ExitPcs :=
  rawWriteOutputSiteOfLiterals 0x15730 32 0x1573c 0x10734 32 0xffffb 0xa5c
    0x93 0x05 0x00 0x02 0x97 0xb0 0xff 0xff 0xe7 0x80 0xc0 0xa5
    Elflings.writeSuccessRawLine156ExecutionPcRanges Elflings.writeSuccessRawLine156ExitPcs

/-- The parent-beacon-root output wrapper uses the shared output theorem. -/
theorem writeSuccessParentBeaconRootInstanceContract :
    WriteSuccessParentBeaconRootInstanceContract :=
  rawEncoderInstanceContract_of_writeOutputSite parentBeaconRootWriteOutputSite

end BinaryFv.Zesu.MachineExecution
