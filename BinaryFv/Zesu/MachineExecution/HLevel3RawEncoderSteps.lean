import BinaryFv.Zesu.MachineExecution.HLevel3WriteOutputSteps

/-!
# Shared Level 3 raw encoder wrapper

The returning raw encoders use two setup instructions in either order. Both orders reach the same
`auipc; jalr; write_output` suffix. This module proves the semantic composition once. Concrete
instances must supply only an exact two-step setup site.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

def rawEncoderSetupWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x10 ∨ register = x11

/-- The raw source starts at a fixed offset from the live stack pointer. -/
def RawEncoderStackSource (offset : Nat) (args : RawEncoderArgs) (state : EndpointState) : Prop :=
  ∃ stackPointer,
    state.machine.regs.get? x2 = some (BitVec.ofNat 64 stackPointer) ∧
    args.sourceAddress = stackPointer + offset ∧
    stackPointer + offset < 2 ^ 64

/-- The raw source is already in `s2`. -/
def RawEncoderX18Source (args : RawEncoderArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? x18 = some (BitVec.ofNat 64 args.sourceAddress)

/-- Execute one exact `addi a0, sp, offset` raw-encoder setup instruction. -/
theorem configuredRawEncoderStackSourceStep (stepNo pc offset : Nat) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8) (state : State) (stackPointer : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (resultEq : iTypeResult .ADDI imm (BitVec.ofNat 64 stackPointer) =
      BitVec.ofNat 64 (stackPointer + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (imm, .Regidx 2#5, .Regidx 10#5, .ADDI))) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10
        (BitVec.ofNat 64 (stackPointer + offset))) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have source := (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x2
    (by decide) |>.trans stack
  have execute : Runs (execute (.ITYPE (imm, .Regidx 2#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 (BitVec.ofNat 64 (stackPointer + offset)) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE imm (.Regidx 2#5) (.Regidx 10#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ imm (.Regidx 2#5)
      (.Regidx 10#5) .ADDI (BitVec.ofNat 64 stackPointer)
      (rX_x2_run premise (BitVec.ofNat 64 stackPointer) source)
      (wX_x10_run premise (iTypeResult .ADDI imm (BitVec.ofNat 64 stackPointer)))
  exact configuredRegisterWriteStep stepNo pc state x10
    (BitVec.ofNat 64 (stackPointer + offset))
    (.ITYPE (imm, .Regidx 2#5, .Regidx 10#5, .ADDI)) byte0 byte1 byte2 byte3
    configured atPc loaded decode execute (pcFits := site.pcFits) (base := base)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)
    (pcAligned := site.pcAligned)

/-- Execute one exact `mv a0, s2` raw-encoder setup instruction. -/
theorem configuredRawEncoderX18SourceStep (stepNo pc : Nat)
    (byte0 byte1 byte2 byte3 : UInt8) (state : State) (sourceAddress : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (source : state.regs.get? x18 = some (BitVec.ofNat 64 sourceAddress))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0, .Regidx 18#5, .Regidx 10#5, .ADDI))) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10
        (BitVec.ofNat 64 sourceAddress)) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have source' := (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x18
    (by decide) |>.trans source
  have resultEq : iTypeResult .ADDI 0 (BitVec.ofNat 64 sourceAddress) =
      BitVec.ofNat 64 sourceAddress := by
    simp [iTypeResult, show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
  have execute : Runs (execute (.ITYPE (0, .Regidx 18#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 (BitVec.ofNat 64 sourceAddress) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 18#5) (.Regidx 10#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ 0 (.Regidx 18#5)
      (.Regidx 10#5) .ADDI (BitVec.ofNat 64 sourceAddress)
      (rX_x18_run premise (BitVec.ofNat 64 sourceAddress) source')
      (wX_x10_run premise (iTypeResult .ADDI 0 (BitVec.ofNat 64 sourceAddress)))
  exact configuredRegisterWriteStep stepNo pc state x10 (BitVec.ofNat 64 sourceAddress)
    (.ITYPE (0, .Regidx 18#5, .Regidx 10#5, .ADDI)) byte0 byte1 byte2 byte3
    configured atPc loaded decode execute (pcFits := site.pcFits) (base := base)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)
    (pcAligned := site.pcAligned)

private theorem encoderInlinePreserved_disjoint_rawEncoderSetupWrites :
    RegSet.Disjoint encoderInlinePreserved rawEncoderSetupWrites := by
  intro register preserved written
  simp [encoderInlinePreserved, rawEncoderSetupWrites, instructionPreserved,
    platformPreserved, stepBookkeeping] at preserved written
  grind

private theorem instructionPreserved_disjoint_rawEncoderSetupWrites :
    RegSet.Disjoint instructionPreserved rawEncoderSetupWrites :=
  fun register preserved written =>
    encoderInlinePreserved_disjoint_rawEncoderSetupWrites register (Or.inl preserved) written

/-- The real inlined raw-encoder boundary. The first two instructions create `a0` and `a1`. -/
def RawEncoderSetupEntry (entry expectedSize : Nat)
    (bindSource : RawEncoderArgs → EndpointState → Prop)
    (args : RawEncoderArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  bindSource args state ∧
  args.bytes.size = expectedSize ∧
  BytesRep state.machine.mem args.sourceAddress args.bytes ∧
  (∀ index, index < args.bytes.size → ¬writeOutputMemory (args.sourceAddress + index)) ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  EncoderOutputMachineAccess state.machine

/-- The raw-encoder contract before its two optimized argument-setup instructions. -/
def rawEncoderSetupContract (entry expectedSize successPc : Nat)
    (bindSource : RawEncoderArgs → EndpointState → Prop) :
    RelationalMachineContract EndpointState RawEncoderArgs Unit :=
  { allows := fun _ _ => True
    entry := RawEncoderSetupEntry entry expectedSize bindSource
    exit := RawEncoderExit successPc
    stepBound := fun _ => 9 }

set_option genInjectivity false in
/-- Facts shared by both source-first and length-first two-instruction setup schedules. -/
structure RawEncoderSetupHandoff (executionPcs : List Elflings.PcRange)
    (entry expectedSize fromStep : Nat)
    (args : RawEncoderArgs) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges executionPcs) fromStep 2 before after
  atPc : after.machine.regs.get? PC = some (BitVec.ofNat 64 (entry + 8))
  source : after.machine.regs.get? x10 = some (BitVec.ofNat 64 args.sourceAddress)
  length : after.machine.regs.get? x11 = some (BitVec.ofNat 64 expectedSize)
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  stdout : after.stdout = before.stdout
  exitCode : after.exitCode = before.exitCode
  memory : after.machine.mem = before.machine.mem
  agree : Agree encoderInlinePreserved before.machine after.machine
  aux : EndpointMachineAuxAgree before.machine after.machine
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : EncoderOutputMachineAccess after.machine

/-- Compose any exact two-register setup once its two Sail instruction runs are available. -/
theorem rawEncoderSetupHandoff_of_two_steps
    (entry expectedSize fromStep : Nat) (args : RawEncoderArgs) (before : EndpointState)
    (firstDestination secondDestination : Register)
    (firstValue : RegisterType firstDestination)
    (secondValue : RegisterType secondDestination)
    (r0 r1 : BitVec 64)
    (firstRun : Runs (try_step fromStep false) before.machine
      (afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0
        firstDestination firstValue) false)
    (secondRun : Runs (try_step (fromStep + 1) false)
      (afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0
        firstDestination firstValue)
      (afterRegisterWrite
        (afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0
          firstDestination firstValue)
        (BitVec.ofNat 64 (entry + 4)) r1 secondDestination secondValue) false)
    (atPc : before.machine.regs.get? PC = some (BitVec.ofNat 64 entry))
    (firstInside : pcInRanges executionPcs (BitVec.ofNat 64 entry))
    (secondInside : pcInRanges executionPcs (BitVec.ofNat 64 (entry + 4)))
    (firstAdvance : Sail.BitVec.addInt (BitVec.ofNat 64 entry) 4 =
      BitVec.ofNat 64 (entry + 4))
    (secondAdvance : Sail.BitVec.addInt (BitVec.ofNat 64 (entry + 4)) 4 =
      BitVec.ofNat 64 (entry + 8))
    (firstNotHost : ¬BareMetalHostTransitionPc (BitVec.ofNat 64 entry))
    (secondNotHost : ¬BareMetalHostTransitionPc (BitVec.ofNat 64 (entry + 4)))
    (sourceAfter : (afterRegisterWrite
      (afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0
        firstDestination firstValue)
      (BitVec.ofNat 64 (entry + 4)) r1 secondDestination secondValue).regs.get? x10 =
        some (BitVec.ofNat 64 args.sourceAddress))
    (lengthAfter : (afterRegisterWrite
      (afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0
        firstDestination firstValue)
      (BitVec.ofNat 64 (entry + 4)) r1 secondDestination secondValue).regs.get? x11 =
        some (BitVec.ofNat 64 expectedSize))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (access : EncoderOutputMachineAccess before.machine)
    (firstMember : firstDestination = x10 ∨ firstDestination = x11)
    (secondMember : secondDestination = x10 ∨ secondDestination = x11)
    (distinct : firstDestination ≠ secondDestination) :
    ∃ after, RawEncoderSetupHandoff executionPcs entry expectedSize fromStep args before after := by
  let after0 := afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0
    firstDestination firstValue
  let after1 := afterRegisterWrite after0 (BitVec.ofNat 64 (entry + 4)) r1
    secondDestination secondValue
  let prepared : EndpointState := { before with machine := after1 }
  have seg0 := Seg.nil (pcInRanges executionPcs) (fun _ => False) rawEncoderSetupWrites
    (fun _ => False) fromStep (childSummary := fun _ _ _ _ _ => False)
    access.configured.retiredCounter atPc
  have firstNotPc : firstDestination ≠ PC := by
    rcases firstMember with rfl | rfl <;> decide
  have firstNotRetired : firstDestination ≠ minstret := by
    rcases firstMember with rfl | rfl <;> decide
  have secondNotPc : secondDestination ≠ PC := by
    rcases secondMember with rfl | rfl <;> decide
  have secondNotRetired : secondDestination ≠ minstret := by
    rcases secondMember with rfl | rfl <;> decide
  have seg1 := seg0.stepKnown firstInside (by simp) firstDestination firstValue
    (BitVec.ofNat 64 (entry + 4)) r0 firstRun firstAdvance
    (by intro register written; exact Or.inl written)
    (Or.inr firstMember)
    firstNotPc firstNotRetired (by simp [RegsOutside])
  have keepFirst : RegsOutside
      (RegSet.union stepBookkeeping (RegSet.only secondDestination))
      [⟨firstDestination, firstValue⟩] := by
    simp [RegsOutside, stepBookkeeping, distinct]
    rcases firstMember with rfl | rfl <;> decide
  have seg2 := seg1.stepKnown secondInside (by simp) secondDestination secondValue
    (BitVec.ofNat 64 (entry + 8)) r1 (by simpa [after0] using secondRun) secondAdvance
    (by intro register written; exact Or.inl written)
    (Or.inr secondMember)
    secondNotPc secondNotRetired keepFirst
  have configured : ConfiguredMachinePre EndpointMachinePc after1 :=
    access.configured.mono
      (seg2.agree instructionPreserved_disjoint_rawEncoderSetupWrites) seg2.retired
  have pmaEq : after1.regs.get? pma_regions = before.machine.regs.get? pma_regions := by
    simpa [after1, after0] using seg2.writes.get pma_regions (by
      simp [rawEncoderSetupWrites, stepBookkeeping])
  have preparedAccess : EncoderOutputMachineAccess after1 := {
    configured := configured
    outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq access.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq access.outputLengthStore
    outputBufferNoMMIO := access.outputBufferNoMMIO
    outputLengthNoMMIO := access.outputLengthNoMMIO
  }
  have trace0 : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep 1 before { before with machine := after0 } :=
    .step fromStep 0 (BitVec.ofNat 64 entry) before { before with machine := after0 }
      { before with machine := after0 } (by simpa [EndpointPc] using atPc) firstInside
      (endpointStep_sail fromStep before after0
        (fun observed observedPc => by
          change before.machine.regs.get? PC = some observed at observedPc
          rw [atPc] at observedPc
          cases Option.some.inj observedPc
          exact firstNotHost) firstRun)
      (.refl (fromStep + 1) { before with machine := after0 })
  have secondAtPc : after0.regs.get? PC = some (BitVec.ofNat 64 (entry + 4)) := by
    simpa [after0] using seg1.atPc
  have trace1 : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      (fromStep + 1) 1 { before with machine := after0 } prepared :=
    .step (fromStep + 1) 0 (BitVec.ofNat 64 (entry + 4))
      { before with machine := after0 } prepared prepared
      (by simpa [EndpointPc] using secondAtPc) secondInside
      (endpointStep_sail (fromStep + 1) { before with machine := after0 } after1
        (fun observed observedPc => by
          change after0.regs.get? PC = some observed at observedPc
          rw [secondAtPc] at observedPc
          cases Option.some.inj observedPc
          exact secondNotHost) (by simpa [after0] using secondRun))
      (.refl (fromStep + 2) prepared)
  refine ⟨prepared, {
    trace := by simpa [prepared, Nat.add_assoc] using trace0.append trace1
    atPc := by simpa [prepared, after1, after0] using seg2.atPc
    source := by simpa [prepared, after1, after0] using sourceAfter
    length := by simpa [prepared, after1, after0] using lengthAfter
    stdin := rfl
    cursor := rfl
    stdout := rfl
    exitCode := rfl
    memory := by simpa [prepared, after1, after0] using seg2.memEq (by simp)
    agree := by simpa [prepared, after1, after0] using
      seg2.writes.agree encoderInlinePreserved_disjoint_rawEncoderSetupWrites
    aux := by simpa [prepared, after1, after0] using seg2.aux
    loaded := by simpa [prepared, after1, after0, seg2.memEq (by simp)] using loaded
    access := by simpa [prepared] using preparedAccess }⟩

/-- A site supplies only the two setup steps. The shared output site supplies the remaining steps. -/
structure RawEncoderSetupSite (entry expectedSize successPc : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat)
    (bindSource : RawEncoderArgs → EndpointState → Prop) where
  output : RawWriteOutputPreparedSite (entry + 4) expectedSize successPc executionPcs exitPcs
  setup : ∀ fromStep args before,
    RawEncoderSetupEntry entry expectedSize bindSource args before →
      ∃ after, RawEncoderSetupHandoff executionPcs entry expectedSize fromStep args before after

/-- Build every source-first setup site from one exact source step and the shared output suffix. -/
def rawEncoderStackSourceFirstSetupSite
    (entry offset expectedSize successPc : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat)
    (output : RawWriteOutputPreparedSite (entry + 4) expectedSize successPc executionPcs exitPcs)
    (firstInside : pcInRanges executionPcs (BitVec.ofNat 64 entry))
    (secondInside : pcInRanges executionPcs (BitVec.ofNat 64 (entry + 4)))
    (firstAdvance : Sail.BitVec.addInt (BitVec.ofNat 64 entry) 4 =
      BitVec.ofNat 64 (entry + 4))
    (secondAdvance : Sail.BitVec.addInt (BitVec.ofNat 64 (entry + 4)) 4 =
      BitVec.ofNat 64 (entry + 8))
    (firstNotHost : ¬BareMetalHostTransitionPc (BitVec.ofNat 64 entry))
    (secondNotHost : ¬BareMetalHostTransitionPc (BitVec.ofNat 64 (entry + 4)))
    (sourceStep : ∀ stepNo state stackPointer,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 entry) →
      state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 entry) retired x10
          (BitVec.ofNat 64 (stackPointer + offset))) false)
    (lengthStep : ∀ stepNo state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 (entry + 4)) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 (entry + 4)) retired x11
          (BitVec.ofNat 64 expectedSize)) false) :
    RawEncoderSetupSite entry expectedSize successPc executionPcs exitPcs
      (RawEncoderStackSource offset) := {
  output
  setup := by
    intro fromStep args before entryPre
    rcases entryPre with ⟨atPc, ⟨stackPointer, stack, sourceEq, sourceFits⟩, size, bytes,
      outside, loaded, access⟩
    obtain ⟨r0, run0⟩ := sourceStep fromStep before.machine stackPointer
      access.configured atPc stack loaded
    let after0 := afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0 x10
      (BitVec.ofNat 64 (stackPointer + offset))
    have writes0 := afterRegisterWrite_writes before.machine (BitVec.ofNat 64 entry) r0 x10
      (BitVec.ofNat 64 (stackPointer + offset))
    have configured0 : ConfiguredMachinePre EndpointMachinePc after0 := by
      apply ConfiguredMachinePre.afterRegisterWrite (BitVec.ofNat 64 entry) r0 x10
        (BitVec.ofNat 64 (stackPointer + offset)) access.configured
      intro preserved
      exact instructionPreserved_disjoint_rawEncoderSetupWrites x10 preserved
        (Or.inr (Or.inl rfl))
    have atPc0 : after0.regs.get? PC = some (BitVec.ofNat 64 (entry + 4)) := by
      simpa [after0, firstAdvance] using
        afterRegisterWrite_pc before.machine (BitVec.ofNat 64 entry) r0 x10
          (BitVec.ofNat 64 (stackPointer + offset))
    have loaded0 : Artifacts.programImage.fileBytesLoadedFaithfully after0.mem := by
      simpa [after0, afterRegisterWrite_mem] using loaded
    obtain ⟨r1, run1⟩ := lengthStep (fromStep + 1) after0 configured0 atPc0 loaded0
    apply rawEncoderSetupHandoff_of_two_steps entry expectedSize fromStep args before
      x10 x11 (BitVec.ofNat 64 (stackPointer + offset)) (BitVec.ofNat 64 expectedSize) r0 r1
      run0 (by simpa [after0] using run1) atPc firstInside secondInside firstAdvance
      secondAdvance firstNotHost secondNotHost
    · have source0 : after0.regs.get? x10 =
          some (BitVec.ofNat 64 (stackPointer + offset)) := by
        simpa [after0] using afterRegisterWrite_destination before.machine
          (BitVec.ofNat 64 entry) r0 x10 (BitVec.ofNat 64 (stackPointer + offset))
          (by decide) (by decide)
      rw [sourceEq]
      exact (afterRegisterWrite_writes after0 (BitVec.ofNat 64 (entry + 4)) r1 x11
        (BitVec.ofNat 64 expectedSize)).get x10 (by decide) |>.trans source0
    · exact afterRegisterWrite_destination after0 (BitVec.ofNat 64 (entry + 4)) r1 x11
        (BitVec.ofNat 64 expectedSize) (by decide) (by decide)
    · exact loaded
    · exact access
    · exact Or.inl rfl
    · exact Or.inr rfl
    · decide
}

/-- Build every length-first setup site from exact length and `mv a0, s2` steps. -/
def rawEncoderX18LengthFirstSetupSite
    (entry expectedSize successPc : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat)
    (output : RawWriteOutputPreparedSite (entry + 4) expectedSize successPc executionPcs exitPcs)
    (firstInside : pcInRanges executionPcs (BitVec.ofNat 64 entry))
    (secondInside : pcInRanges executionPcs (BitVec.ofNat 64 (entry + 4)))
    (firstAdvance : Sail.BitVec.addInt (BitVec.ofNat 64 entry) 4 =
      BitVec.ofNat 64 (entry + 4))
    (secondAdvance : Sail.BitVec.addInt (BitVec.ofNat 64 (entry + 4)) 4 =
      BitVec.ofNat 64 (entry + 8))
    (firstNotHost : ¬BareMetalHostTransitionPc (BitVec.ofNat 64 entry))
    (secondNotHost : ¬BareMetalHostTransitionPc (BitVec.ofNat 64 (entry + 4)))
    (lengthStep : ∀ stepNo state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 entry) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 entry) retired x11
          (BitVec.ofNat 64 expectedSize)) false)
    (sourceStep : ∀ stepNo state sourceAddress,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 (entry + 4)) →
      state.regs.get? x18 = some (BitVec.ofNat 64 sourceAddress) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 (entry + 4)) retired x10
          (BitVec.ofNat 64 sourceAddress)) false) :
    RawEncoderSetupSite entry expectedSize successPc executionPcs exitPcs RawEncoderX18Source := {
  output
  setup := by
    intro fromStep args before entryPre
    rcases entryPre with ⟨atPc, source, size, bytes, outside, loaded, access⟩
    obtain ⟨r0, run0⟩ := lengthStep fromStep before.machine access.configured atPc loaded
    let after0 := afterRegisterWrite before.machine (BitVec.ofNat 64 entry) r0 x11
      (BitVec.ofNat 64 expectedSize)
    have configured0 : ConfiguredMachinePre EndpointMachinePc after0 := by
      apply ConfiguredMachinePre.afterRegisterWrite (BitVec.ofNat 64 entry) r0 x11
        (BitVec.ofNat 64 expectedSize) access.configured
      intro preserved
      exact instructionPreserved_disjoint_rawEncoderSetupWrites x11 preserved
        (Or.inr (Or.inr rfl))
    have atPc0 : after0.regs.get? PC = some (BitVec.ofNat 64 (entry + 4)) := by
      simpa [after0, firstAdvance] using
        afterRegisterWrite_pc before.machine (BitVec.ofNat 64 entry) r0 x11
          (BitVec.ofNat 64 expectedSize)
    have source0 : after0.regs.get? x18 = some (BitVec.ofNat 64 args.sourceAddress) := by
      exact (afterRegisterWrite_writes before.machine (BitVec.ofNat 64 entry) r0 x11
        (BitVec.ofNat 64 expectedSize)).get x18 (by decide) |>.trans source
    have loaded0 : Artifacts.programImage.fileBytesLoadedFaithfully after0.mem := by
      simpa [after0, afterRegisterWrite_mem] using loaded
    obtain ⟨r1, run1⟩ := sourceStep (fromStep + 1) after0 args.sourceAddress configured0
      atPc0 source0 loaded0
    apply rawEncoderSetupHandoff_of_two_steps entry expectedSize fromStep args before
      x11 x10 (BitVec.ofNat 64 expectedSize) (BitVec.ofNat 64 args.sourceAddress) r0 r1
      run0 (by simpa [after0] using run1) atPc firstInside secondInside firstAdvance
      secondAdvance firstNotHost secondNotHost
    · exact afterRegisterWrite_destination after0 (BitVec.ofNat 64 (entry + 4)) r1 x10
        (BitVec.ofNat 64 args.sourceAddress) (by decide) (by decide)
    · have length0 : after0.regs.get? x11 = some (BitVec.ofNat 64 expectedSize) := by
        simpa [after0] using afterRegisterWrite_destination before.machine
          (BitVec.ofNat 64 entry) r0 x11 (BitVec.ofNat 64 expectedSize)
          (by decide) (by decide)
      exact (afterRegisterWrite_writes after0 (BitVec.ofNat 64 (entry + 4)) r1 x10
        (BitVec.ofNat 64 args.sourceAddress)).get x11 (by decide) |>.trans length0
    · exact loaded
    · exact access
    · exact Or.inr rfl
    · exact Or.inl rfl
    · decide
}

/-- Build a source-first setup site from exact instruction data. Concrete instances only list
addresses, immediates, bytes, ranges, and exits. -/
def rawEncoderStackSourceFirstSetupSiteOfLiterals
    (entry offset expectedSize successPc : Nat)
    (callBaseValue : BitVec 64) (sourceImm lengthImm : BitVec 12)
    (callBaseImm : BitVec 20) (callImm : BitVec 12)
    (sourceByte0 sourceByte1 sourceByte2 sourceByte3 : UInt8)
    (lengthByte0 lengthByte1 lengthByte2 lengthByte3 : UInt8)
    (baseByte0 baseByte1 baseByte2 baseByte3 : UInt8)
    (callByte0 callByte1 callByte2 callByte3 : UInt8)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat)
    (sourceSite : ExactInstructionSite entry sourceByte0 sourceByte1 sourceByte2 sourceByte3 := by
      native_decide)
    (lengthSite : ExactInstructionSite (entry + 4)
      lengthByte0 lengthByte1 lengthByte2 lengthByte3 := by native_decide)
    (sourceBase : BaseInstructionEncoding (BitVec.ofNat 8 sourceByte0.toNat) := by rfl)
    (lengthBase : BaseInstructionEncoding (BitVec.ofNat 8 lengthByte0.toNat) := by rfl)
    (sourceExtend : sign_extend (m := 64) sourceImm = BitVec.ofNat 64 offset := by native_decide)
    (lengthResult : iTypeResult .ADDI lengthImm 0 = BitVec.ofNat 64 expectedSize := by
      native_decide)
    (sourceDecode : ∀ state, ConfiguredMachinePre EndpointMachinePc state →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 sourceByte0.toNat)
        (BitVec.ofNat 8 sourceByte1.toNat) (BitVec.ofNat 8 sourceByte2.toNat)
        (BitVec.ofNat 8 sourceByte3.toNat)))
        (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
        (.ITYPE (sourceImm, .Regidx 2#5, .Regidx 10#5, .ADDI)) := by
      intro state configured; write_success_decode configured)
    (lengthDecode : ∀ state, ConfiguredMachinePre EndpointMachinePc state →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 lengthByte0.toNat)
        (BitVec.ofNat 8 lengthByte1.toNat) (BitVec.ofNat 8 lengthByte2.toNat)
        (BitVec.ofNat 8 lengthByte3.toNat)))
        (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
        (.ITYPE (lengthImm, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
      intro state configured; write_success_decode configured)
    (baseSite : ExactInstructionSite (entry + 8) baseByte0 baseByte1 baseByte2 baseByte3 := by
      native_decide)
    (callSite : ExactInstructionSite (entry + 12) callByte0 callByte1 callByte2 callByte3 := by
      native_decide)
    (baseBase : BaseInstructionEncoding (BitVec.ofNat 8 baseByte0.toNat) := by rfl)
    (callBase : BaseInstructionEncoding (BitVec.ofNat 8 callByte0.toNat) := by rfl)
    (baseResult : BitVec.ofNat 64 (entry + 8) +
        sign_extend (m := 64) (callBaseImm ++ 0x000#12) = callBaseValue := by native_decide)
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
    (returnEq : Sail.BitVec.addInt (BitVec.ofNat 64 (entry + 12)) 4 =
      BitVec.ofNat 64 successPc := by native_decide)
    (targetBit1 : Sail.BitVec.access (callBaseValue + sign_extend (m := 64) callImm) 1 = 0#1 := by
      native_decide)
    (expectedSizePositive : 0 < expectedSize := by native_decide)
    (expectedSizeFits : expectedSize < 2 ^ 64 := by native_decide)
    (successFits : successPc < 2 ^ 64 := by native_decide)
    (returnAligned : Sail.BitVec.access (BitVec.ofNat 64 successPc) 1 = 0#1 := by native_decide)
    (returnCanonical : Sail.BitVec.update (BitVec.ofNat 64 successPc) 0 0#1 =
      BitVec.ofNat 64 successPc := by native_decide)
    (setupRangeMember : (entry, entry + 8) ∈ executionPcs := by native_decide)
    (suffixRangeMember : (entry + 4, entry + 16) ∈ executionPcs := by native_decide)
    (outputRangeMember : (0x10190, 0x101c4) ∈ executionPcs := by native_decide)
    (exitInExitPcs : successPc ∈ exitPcs := by native_decide)
    (entryFits : entry + 16 < 2 ^ 64 := by native_decide)
    (afterHost : 0x101d4 < entry := by native_decide) :
    RawEncoderSetupSite entry expectedSize successPc executionPcs exitPcs
      (RawEncoderStackSource offset) :=
  rawEncoderStackSourceFirstSetupSite entry offset expectedSize successPc executionPcs exitPcs
    (rawWriteOutputPreparedSiteOfLiterals (entry + 4) expectedSize successPc callBaseValue
      callBaseImm callImm baseByte0 baseByte1 baseByte2 baseByte3
      callByte0 callByte1 callByte2 callByte3 executionPcs exitPcs
      baseSite callSite baseBase callBase baseResult baseDecode callDecode targetEq returnEq
      targetBit1 (by omega) expectedSizePositive expectedSizeFits successFits (by omega)
      returnAligned returnCanonical suffixRangeMember outputRangeMember exitInExitPcs)
    (by
      have entryFit : entry < 2 ^ 64 := by omega
      exact ⟨(entry, entry + 8), setupRangeMember,
        by simp [Nat.mod_eq_of_lt entryFit],
        by simp [Nat.mod_eq_of_lt entryFit]⟩)
    (by
      have nextFit : entry + 4 < 2 ^ 64 := by omega
      exact ⟨(entry, entry + 8), setupRangeMember,
        (by simp [Nat.mod_eq_of_lt nextFit]),
        (by simp [Nat.mod_eq_of_lt nextFit])⟩)
    sourceSite.advance lengthSite.advance
    (by
      intro observed
      unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
        at observed
      rcases observed with observed | observed | observed <;>
        simp [Nat.mod_eq_of_lt (by omega : entry < 2 ^ 64)] at observed <;> omega)
    (by
      intro observed
      unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
        at observed
      rcases observed with observed | observed | observed <;>
        simp [Nat.mod_eq_of_lt (by omega : entry + 4 < 2 ^ 64)] at observed <;> omega)
    (by
      intro stepNo state stackPointer configured atPc stack loaded
      exact configuredRawEncoderStackSourceStep stepNo entry offset sourceImm
        sourceByte0 sourceByte1 sourceByte2 sourceByte3 state stackPointer configured atPc stack
        loaded sourceSite sourceBase (by
          rw [BitVec.ofNat_add]
          simp [iTypeResult, sourceExtend]) (sourceDecode state configured))
    (by
      intro stepNo state configured atPc loaded
      exact configuredRawWriteOutputLengthStep stepNo (entry + 4) expectedSize lengthImm
        lengthByte0 lengthByte1 lengthByte2 lengthByte3 state configured atPc loaded lengthSite
        lengthBase lengthResult (lengthDecode state configured))

/-- One proof covers every returning raw encoder, independent of its two setup-instruction order. -/
theorem rawEncoderSetupContract_of_site
    (site : RawEncoderSetupSite entry expectedSize successPc executionPcs exitPcs bindSource) :
    (rawEncoderSetupContract entry expectedSize successPc bindSource).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs) := by
  intro args fromStep before entryPre
  rcases entryPre with ⟨atPc, sourceBinding, size, bytes, outside, loaded, access⟩
  obtain ⟨prepared, setup⟩ := site.setup fromStep args before
    ⟨atPc, sourceBinding, size, bytes, outside, loaded, access⟩
  obtain ⟨after, outputTrace, outputExit⟩ := rawWriteOutputPreparedHandoff site.output
    (fromStep + 2) args prepared setup.atPc setup.source setup.length size
    (by simpa [setup.memory] using bytes) outside setup.loaded setup.access
  rcases outputExit with ⟨afterPc, stdout, stdin, cursor, exitCode, memory, agree, retired,
    outputLoaded, aux⟩
  have trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep 9 before after := by
    simpa [Nat.add_assoc] using setup.trace.append outputTrace
  refine ⟨9, after, (), by omega, Nat.le_refl 9, trace,
    ⟨BitVec.ofNat 64 successPc, afterPc, ?_⟩, trivial, ?_⟩
  · unfold pcInList
    simpa [Nat.mod_eq_of_lt site.output.successFits] using site.output.exitInExitPcs
  · refine ⟨afterPc, ?_, ?_, ?_, ?_, ?_, setup.agree.trans agree, retired,
      outputLoaded, ⟨aux.1.trans setup.aux.1, aux.2.1.trans setup.aux.2.1,
        aux.2.2.trans setup.aux.2.2⟩⟩
    · simpa [setup.stdout] using stdout
    · simpa [setup.stdin] using stdin
    · simpa [setup.cursor] using cursor
    · simpa [setup.exitCode] using exitCode
    · intro address outsideMemory
      exact (memory address outsideMemory).trans
        (congrArg (fun mem => mem.get? address) setup.memory)

/-! ## Exact returning `Encoder.raw` instances -/

def rawEncoder4045ExecutionPcs : List Elflings.PcRange :=
  [(0x15548, 0x15550), (0x1554c, 0x15558), (0x10190, 0x101c4)]

def rawEncoder4045ExitPcs : List Nat := [0x14d10, 0x15558]

private def rawEncoder4045Site : RawEncoderSetupSite 0x15548 32 0x15558
    rawEncoder4045ExecutionPcs rawEncoder4045ExitPcs (RawEncoderStackSource 0x690) :=
  rawEncoderStackSourceFirstSetupSiteOfLiterals
    0x15548 0x690 32 0x15558 0x10550 0x690 32 0xffffb 0xc40
    0x13 0x05 0x01 0x69 0x93 0x05 0x00 0x02
    0x97 0xb0 0xff 0xff 0xe7 0x80 0x00 0xc4
    rawEncoder4045ExecutionPcs rawEncoder4045ExitPcs

/-- `fi:1:4045` is a thin use of the shared stack-source raw-encoder theorem. -/
theorem rawEncoder4045Contract_implements :
    (rawEncoderSetupContract 0x15548 32 0x15558 (RawEncoderStackSource 0x690)).Implements
      EndpointStep EndpointPc (pcInRanges rawEncoder4045ExecutionPcs)
      (pcInList rawEncoder4045ExitPcs) :=
  rawEncoderSetupContract_of_site rawEncoder4045Site

def rawEncoder40c3ExecutionPcs : List Elflings.PcRange :=
  [(0x156c0, 0x156c8), (0x156c4, 0x156d0), (0x10190, 0x101c4)]

def rawEncoder40c3ExitPcs : List Nat := [0x14d10, 0x156d0]

private def rawEncoder40c3Site : RawEncoderSetupSite 0x156c0 20 0x156d0
    rawEncoder40c3ExecutionPcs rawEncoder40c3ExitPcs RawEncoderX18Source :=
  rawEncoderX18LengthFirstSetupSite 0x156c0 20 0x156d0
    rawEncoder40c3ExecutionPcs rawEncoder40c3ExitPcs
    (rawWriteOutputPreparedSiteOfLiterals 0x156c4 20 0x156d0 0x106c8 0xffffb 0xac8
      0x97 0xb0 0xff 0xff 0xe7 0x80 0x80 0xac
      rawEncoder40c3ExecutionPcs rawEncoder40c3ExitPcs)
    (by unfold rawEncoder40c3ExecutionPcs pcInRanges; native_decide)
    (by unfold rawEncoder40c3ExecutionPcs pcInRanges; native_decide)
    (by native_decide) (by native_decide)
    (by unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc;
        native_decide)
    (by unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc;
        native_decide)
    (by
      intro stepNo state configured atPc loaded
      exact configuredRawWriteOutputLengthStep stepNo 0x156c0 20 20
        0x93 0x05 0x40 0x01 state configured atPc loaded (by native_decide) (by rfl)
        (by native_decide) (by write_success_decode configured))
    (by
      intro stepNo state sourceAddress configured atPc source loaded
      exact configuredRawEncoderX18SourceStep stepNo 0x156c4
        0x13 0x05 0x09 0x00 state sourceAddress configured atPc source loaded
        (by native_decide) (by rfl) (by write_success_decode configured))

/-- `fi:1:40c3` uses the shared length-first setup theorem. -/
theorem rawEncoder40c3Contract_implements :
    (rawEncoderSetupContract 0x156c0 20 0x156d0 RawEncoderX18Source).Implements
      EndpointStep EndpointPc (pcInRanges rawEncoder40c3ExecutionPcs)
      (pcInList rawEncoder40c3ExitPcs) :=
  rawEncoderSetupContract_of_site rawEncoder40c3Site

def rawEncoder412aExecutionPcs : List Elflings.PcRange :=
  [(0x158c4, 0x158cc), (0x158c8, 0x158d4), (0x10190, 0x101c4)]

def rawEncoder412aExitPcs : List Nat := [0x14d10, 0x158d4]

private def rawEncoder412aSite : RawEncoderSetupSite 0x158c4 32 0x158d4
    rawEncoder412aExecutionPcs rawEncoder412aExitPcs (RawEncoderStackSource 0x6d0) :=
  rawEncoderStackSourceFirstSetupSiteOfLiterals
    0x158c4 0x6d0 32 0x158d4 0x108cc 0x6d0 32 0xffffb 0x8c4
    0x13 0x05 0x01 0x6d 0x93 0x05 0x00 0x02
    0x97 0xb0 0xff 0xff 0xe7 0x80 0x40 0x8c
    rawEncoder412aExecutionPcs rawEncoder412aExitPcs

/-- `fi:1:412a` uses the same shared stack-source raw-encoder theorem. -/
theorem rawEncoder412aContract_implements :
    (rawEncoderSetupContract 0x158c4 32 0x158d4 (RawEncoderStackSource 0x6d0)).Implements
      EndpointStep EndpointPc (pcInRanges rawEncoder412aExecutionPcs)
      (pcInList rawEncoder412aExitPcs) :=
  rawEncoderSetupContract_of_site rawEncoder412aSite

def rawEncoder42a2ExecutionPcs : List Elflings.PcRange :=
  [(0x15bac, 0x15bb4), (0x15bb0, 0x15bbc), (0x10190, 0x101c4)]

def rawEncoder42a2ExitPcs : List Nat :=
  [0x150fc, 0x15128, 0x15148, 0x15180, 0x1519c, 0x1571c,
    0x15980, 0x159a0, 0x159bc, 0x159c8, 0x15bbc, 0x15bec]

private def rawEncoder42a2Site : RawEncoderSetupSite 0x15bac 1 0x15bbc
    rawEncoder42a2ExecutionPcs rawEncoder42a2ExitPcs (RawEncoderStackSource 7) :=
  rawEncoderStackSourceFirstSetupSiteOfLiterals
    0x15bac 7 1 0x15bbc 0xfbb4 7 1 0xffffa 0x5dc
    0x13 0x05 0x71 0x00 0x93 0x05 0x10 0x00
    0x97 0xa0 0xff 0xff 0xe7 0x80 0xc0 0x5d
    rawEncoder42a2ExecutionPcs rawEncoder42a2ExitPcs

/-- `fi:1:42a2` uses the shared theorem with a one-byte stack source. -/
theorem rawEncoder42a2Contract_implements :
    (rawEncoderSetupContract 0x15bac 1 0x15bbc (RawEncoderStackSource 7)).Implements
      EndpointStep EndpointPc (pcInRanges rawEncoder42a2ExecutionPcs)
      (pcInList rawEncoder42a2ExitPcs) :=
  rawEncoderSetupContract_of_site rawEncoder42a2Site

def rawEncoder45f6ExecutionPcs : List Elflings.PcRange :=
  [(0x15d1c, 0x15d24), (0x15d20, 0x15d2c), (0x10190, 0x101c4)]

def rawEncoder45f6ExitPcs : List Nat :=
  [0x14e94, 0x14ea0, 0x14eac, 0x14eb8, 0x14ed4, 0x14efc, 0x150fc, 0x15108,
    0x15154, 0x151d0, 0x1521c, 0x153d0, 0x15584, 0x155d8, 0x155e4, 0x1562c,
    0x1568c, 0x156b4, 0x156c0, 0x156dc, 0x156f4, 0x15700, 0x1571c, 0x15750,
    0x1596c, 0x159b0, 0x159bc, 0x159c8, 0x15c34, 0x15c90, 0x15d2c]

private def rawEncoder45f6Site : RawEncoderSetupSite 0x15d1c 8 0x15d2c
    rawEncoder45f6ExecutionPcs rawEncoder45f6ExitPcs (RawEncoderStackSource 0) :=
  rawEncoderStackSourceFirstSetupSiteOfLiterals
    0x15d1c 0 8 0x15d2c 0xfd24 0 8 0xffffa 0x46c
    0x13 0x05 0x01 0x00 0x93 0x05 0x80 0x00
    0x97 0xa0 0xff 0xff 0xe7 0x80 0xc0 0x46
    rawEncoder45f6ExecutionPcs rawEncoder45f6ExitPcs

/-- `fi:1:45f6` uses the shared theorem with the stack pointer as its source. -/
theorem rawEncoder45f6Contract_implements :
    (rawEncoderSetupContract 0x15d1c 8 0x15d2c (RawEncoderStackSource 0)).Implements
      EndpointStep EndpointPc (pcInRanges rawEncoder45f6ExecutionPcs)
      (pcInList rawEncoder45f6ExitPcs) :=
  rawEncoderSetupContract_of_site rawEncoder45f6Site

end BinaryFv.Zesu.MachineExecution
