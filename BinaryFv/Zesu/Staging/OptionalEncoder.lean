import BinaryFv.Zesu.Staging.IntegerEncoder
import BinaryFv.Zesu.Staging.RawEncoder

/-!
# Shared optional encoder boundary

`Encoder.optionalU128` and `Encoder.optionalAddress` use the same output protocol. Both emit one
Boolean tag. A present value then emits one payload. The register and stack payload bindings differ,
so this file keeps those bindings separate and shares the route and exit proof.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

structure OptionalEncoderArgs (Value : Type) where
  stackPointer : Nat
  inputSize : Nat
  value : Option Value
  stackFits : stackPointer < 2 ^ 64

def optionalEncoderMemory (localFrameSize scratchOffset scratchSize : Nat)
    (stackPointer : Nat) : Region :=
  Region.union (byteRange (stackPointer - localFrameSize) localFrameSize)
    (Region.union (byteRange (stackPointer + scratchOffset) scratchSize) writeOutputMemory)

set_option genInjectivity false in
/-- Machine permissions shared by both optional encoders. A zero scratch size disables that range. -/
structure OptionalEncoderMachineAccess (localFrameSize scratchOffset scratchSize : Nat)
    (args : OptionalEncoderArgs Value) (state : State) : Prop where
  output : EncoderOutputMachineAccess state
  stackAligned : args.stackPointer % 16 = 0
  frameFits : localFrameSize ≤ args.stackPointer
  scratchFits : args.stackPointer + scratchOffset + scratchSize ≤ 2 ^ 64
  frameLoad : ∀ offset width, offset + width ≤ localFrameSize →
    LoadPmaAllows state (BitVec.ofNat 64 (args.stackPointer - localFrameSize + offset)) width
  frameStore : ∀ offset width, offset + width ≤ localFrameSize →
    StorePmaAllows state (BitVec.ofNat 64 (args.stackPointer - localFrameSize + offset)) width
  frameLoadNoMMIO : ∀ offset width, offset + width ≤ localFrameSize →
    LoadMMIOAddressExcluded
      (BitVec.ofNat 64 (args.stackPointer - localFrameSize + offset)) width
  frameStoreNoMMIO : ∀ offset width, offset + width ≤ localFrameSize →
    StoreMMIOAddressExcluded
      (BitVec.ofNat 64 (args.stackPointer - localFrameSize + offset)) width
  scratchLoad : ∀ offset width, offset + width ≤ scratchSize →
    LoadPmaAllows state (BitVec.ofNat 64 (args.stackPointer + scratchOffset + offset)) width
  scratchStore : ∀ offset width, offset + width ≤ scratchSize →
    StorePmaAllows state (BitVec.ofNat 64 (args.stackPointer + scratchOffset + offset)) width
  scratchLoadNoMMIO : ∀ offset width, offset + width ≤ scratchSize →
    LoadMMIOAddressExcluded
      (BitVec.ofNat 64 (args.stackPointer + scratchOffset + offset)) width
  scratchStoreNoMMIO : ∀ offset width, offset + width ≤ scratchSize →
    StoreMMIOAddressExcluded
      (BitVec.ofNat 64 (args.stackPointer + scratchOffset + offset)) width
  frameOutputDisjoint : RegionsDoNotOverlap
    (byteRange (args.stackPointer - localFrameSize) localFrameSize) writeOutputMemory
  scratchOutputDisjoint : RegionsDoNotOverlap
    (byteRange (args.stackPointer + scratchOffset) scratchSize) writeOutputMemory
  frameNotCode : ∀ address, args.stackPointer - localFrameSize ≤ address →
    address < args.stackPointer → Artifacts.programImage.readFileByte? address = none
  scratchNotCode : ∀ address, args.stackPointer + scratchOffset ≤ address →
    address < args.stackPointer + scratchOffset + scratchSize →
      Artifacts.programImage.readFileByte? address = none

def optionalBooleanCallWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x1 ∨ register = x10

private theorem encoderInlinePreserved_disjoint_optionalBooleanCallWrites :
    RegSet.Disjoint encoderInlinePreserved optionalBooleanCallWrites := by
  intro register preserved written
  simp [encoderInlinePreserved, optionalBooleanCallWrites, instructionPreserved,
    platformPreserved, stepBookkeeping] at preserved written
  grind

private theorem instructionPreserved_disjoint_optionalBooleanCallWrites :
    RegSet.Disjoint instructionPreserved optionalBooleanCallWrites := by
  intro register preserved written
  exact encoderInlinePreserved_disjoint_optionalBooleanCallWrites register (Or.inl preserved)
    written

private theorem OptionalEncoderMachineAccess.ofWrites
    {writes : RegSet}
    (access : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args before)
    (frame : WritesOnlyRegs writes before after) (pmaOutside : ¬writes pma_regions)
    (configured : ConfiguredMachinePre EndpointMachinePc after) :
    OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args after := by
  have pmaEq := frame.get pma_regions pmaOutside
  exact
    { output :=
        { configured := configured
          outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputBufferStore
          outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputLengthStore
          outputBufferNoMMIO := access.output.outputBufferNoMMIO
          outputLengthNoMMIO := access.output.outputLengthNoMMIO }
      stackAligned := access.stackAligned
      frameFits := access.frameFits
      scratchFits := access.scratchFits
      frameLoad := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameLoad offset width bound)
      frameStore := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameStore offset width bound)
      frameLoadNoMMIO := access.frameLoadNoMMIO
      frameStoreNoMMIO := access.frameStoreNoMMIO
      scratchLoad := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.scratchLoad offset width bound)
      scratchStore := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.scratchStore offset width bound)
      scratchLoadNoMMIO := access.scratchLoadNoMMIO
      scratchStoreNoMMIO := access.scratchStoreNoMMIO
      frameOutputDisjoint := access.frameOutputDisjoint
      scratchOutputDisjoint := access.scratchOutputDisjoint
      frameNotCode := access.frameNotCode
      scratchNotCode := access.scratchNotCode }

private theorem OptionalEncoderMachineAccess.encoderCall
    (access : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args state)
    (frameLower : 16 ≤ localFrameSize) (tag : Bool) :
    EncoderCallMachineAccess 16
      { returnAddress := returnPc
        callerStack := args.stackPointer
        inputSize := args.inputSize
        value := tag }
      state := by
  let childArgs : EncoderCallArgs Bool :=
    { returnAddress := returnPc
      callerStack := args.stackPointer
      inputSize := args.inputSize
      value := tag }
  have frameFits := access.frameFits
  refine
    { output := access.output
      stackAligned := access.stackAligned
      frameOutputDisjoint := ?_
      frameLoad := ?_
      frameStore := ?_
      frameLoadNoMMIO := ?_
      frameStoreNoMMIO := ?_
      frameNotCode := ?_ }
  · intro address inside output
    apply access.frameOutputDisjoint address
    · change byteRange (args.stackPointer - 16) 16 address at inside
      unfold byteRange at inside ⊢
      omega
    · exact output
  · intro offset width bound
    have addressEq : args.stackPointer - 16 + offset =
        args.stackPointer - localFrameSize + (localFrameSize - 16 + offset) := by
      omega
    rw [addressEq]
    exact access.frameLoad (localFrameSize - 16 + offset) width (by omega)
  · intro offset width bound
    have addressEq : args.stackPointer - 16 + offset =
        args.stackPointer - localFrameSize + (localFrameSize - 16 + offset) := by
      omega
    rw [addressEq]
    exact access.frameStore (localFrameSize - 16 + offset) width (by omega)
  · intro offset width bound
    have addressEq : args.stackPointer - 16 + offset =
        args.stackPointer - localFrameSize + (localFrameSize - 16 + offset) := by
      omega
    rw [addressEq]
    exact access.frameLoadNoMMIO (localFrameSize - 16 + offset) width (by omega)
  · intro offset width bound
    have addressEq : args.stackPointer - 16 + offset =
        args.stackPointer - localFrameSize + (localFrameSize - 16 + offset) := by
      omega
    rw [addressEq]
    exact access.frameStoreNoMMIO (localFrameSize - 16 + offset) width (by omega)
  · intro address lower upper
    change args.stackPointer - 16 ≤ address at lower
    exact access.frameNotCode address (by omega) upper

/-- Reuse an optional encoder's local-frame permissions for one nested integer encoder. -/
theorem OptionalEncoderMachineAccess.integerEncoder
    (access : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args state)
    (childFrameSize : Nat) (childInside : childFrameSize ≤ localFrameSize)
    (childAligned : childFrameSize % 16 = 0) :
    IntegerEncoderMachineAccess (args.stackPointer - childFrameSize) childFrameSize state := by
  have localInside : localFrameSize ≤ args.stackPointer := access.frameFits
  have childFits : childFrameSize ≤ args.stackPointer := by omega
  have stackFits := args.stackFits
  have baseEq : args.stackPointer - childFrameSize =
      args.stackPointer - localFrameSize + (localFrameSize - childFrameSize) := by omega
  refine {
    output := access.output
    frameFits := by omega
    frameAligned := by
      rcases Nat.dvd_of_mod_eq_zero access.stackAligned with ⟨stackFactor, stackEq⟩
      rcases Nat.dvd_of_mod_eq_zero childAligned with ⟨childFactor, childEq⟩
      have difference : args.stackPointer - childFrameSize =
          16 * (stackFactor - childFactor) := by omega
      simp [difference]
    storePma := ?_
    storeNoMMIO := ?_
    loadPma := ?_
    loadNoMMIO := ?_
    codeDisjoint := ?_
    outputDisjoint := ?_ }
  · intro offset bound aligned
    simpa [baseEq, Nat.add_assoc] using
      access.frameStore (localFrameSize - childFrameSize + offset) 8 (by omega)
  · intro offset bound aligned
    simpa [baseEq, Nat.add_assoc] using
      access.frameStoreNoMMIO (localFrameSize - childFrameSize + offset) 8 (by omega)
  · intro offset bound aligned
    simpa [baseEq, Nat.add_assoc] using
      access.frameLoad (localFrameSize - childFrameSize + offset) 8 (by omega)
  · intro offset bound aligned
    simpa [baseEq, Nat.add_assoc] using
      access.frameLoadNoMMIO (localFrameSize - childFrameSize + offset) 8 (by omega)
  · intro offset bound
    apply access.frameNotCode (args.stackPointer - childFrameSize + offset)
    · omega
    · omega
  · intro offset bound inside
    apply access.frameOutputDisjoint (args.stackPointer - childFrameSize + offset)
    · unfold byteRange
      omega
    · exact inside

private theorem instructionPreserved_abiCalleePreserved_optional (register : Register)
    (preserved : instructionPreserved register) : abiCalleePreserved register := by
  rcases preserved with ⟨platform, notLink⟩
  rcases platform with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact (notLink rfl).elim
  all_goals simp [abiCalleePreserved]

private theorem OptionalEncoderMachineAccess.ofEncoderFrame
    (template : EndpointState)
    (access : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args before)
    (frame : EncoderInlineFrame { template with machine := before }
      { template with machine := after }) :
    OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args after := by
  have instructionAgree : Agree instructionPreserved before after :=
    frame.1.weaken (fun _ preserved => Or.inl preserved)
  have pmaEq := instructionAgree pma_regions
    (by simp [instructionPreserved, platformPreserved])
  exact
    { output :=
        { configured := access.output.configured.mono instructionAgree frame.2.1
          outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputBufferStore
          outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputLengthStore
          outputBufferNoMMIO := access.output.outputBufferNoMMIO
          outputLengthNoMMIO := access.output.outputLengthNoMMIO }
      stackAligned := access.stackAligned
      frameFits := access.frameFits
      scratchFits := access.scratchFits
      frameLoad := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameLoad offset width bound)
      frameStore := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameStore offset width bound)
      frameLoadNoMMIO := access.frameLoadNoMMIO
      frameStoreNoMMIO := access.frameStoreNoMMIO
      scratchLoad := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.scratchLoad offset width bound)
      scratchStore := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.scratchStore offset width bound)
      scratchLoadNoMMIO := access.scratchLoadNoMMIO
      scratchStoreNoMMIO := access.scratchStoreNoMMIO
      frameOutputDisjoint := access.frameOutputDisjoint
      scratchOutputDisjoint := access.scratchOutputDisjoint
      frameNotCode := access.frameNotCode
      scratchNotCode := access.scratchNotCode }

private theorem liftOptionalParentTrace (template : EndpointState)
    {owned exit : BitVec 64 → Prop} {fromStep count : Nat} {before after : State}
    (notHost : ∀ pc, owned pc → ¬BareMetalHostTransitionPc pc)
    (trace : ScopedTrace owned exit (fun _ _ _ _ _ => False)
      fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc owned fromStep count
      { template with machine := before } { template with machine := after } := by
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
          exact notHost pc inside)
        machineStep
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count callSite program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

/-- The exact three parent instructions that prepare and enter one shared Boolean encoder call. -/
def optionalBooleanParentPc (pc : Nat) (parentPc : BitVec 64) : Prop :=
  parentPc = BitVec.ofNat 64 pc ∨ parentPc = BitVec.ofNat 64 (pc + 4)

structure OptionalBooleanCallSite (pc returnPc callBase : Nat)
    (executionPcs : List Elflings.PcRange) where
  baseStep : ∀ stepNo state,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 pc) →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x1
        (BitVec.ofNat 64 callBase)) false
  callStep : ∀ stepNo state,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 (pc + 4)) →
    state.regs.get? x1 = some (BitVec.ofNat 64 callBase) →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 (pc + 4)) 0x15b9c x1 (BitVec.ofNat 64 returnPc))
        0x15b9c retired) false
  owned0 : pcInRanges executionPcs (BitVec.ofNat 64 pc)
  owned1 : pcInRanges executionPcs (BitVec.ofNat 64 (pc + 4))
  notExit0 : BitVec.ofNat 64 pc ≠ 0x15b9c
  notExit1 : BitVec.ofNat 64 (pc + 4) ≠ 0x15b9c
  next0 : Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 (pc + 4)
  returnListed : returnPc ∈ Elflings.writeSuccessBooleanExitPcs
  childInside : ∀ {childPc},
    pcInRanges Elflings.writeSuccessBooleanExecutionPcRanges childPc →
    pcInRanges executionPcs childPc
  notHost0 : ¬BareMetalHostTransitionPc (BitVec.ofNat 64 pc)
  notHost1 : ¬BareMetalHostTransitionPc (BitVec.ofNat 64 (pc + 4))

/-- Build the shared Boolean call site from exact `auipc; jalr` instruction data. -/
def optionalBooleanCallSiteOfLiterals (pc returnPc callBase : Nat)
    (baseImm : BitVec 20) (callImm : BitVec 12)
    (baseByte0 baseByte1 baseByte2 baseByte3 : UInt8)
    (callByte0 callByte1 callByte2 callByte3 : UInt8)
    (executionPcs : List Elflings.PcRange) (parentRange : Elflings.PcRange)
    (baseSite : ExactInstructionSite pc baseByte0 baseByte1 baseByte2 baseByte3 := by
      native_decide)
    (callSite : ExactInstructionSite (pc + 4) callByte0 callByte1 callByte2 callByte3 := by
      native_decide)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 baseByte0.toNat) := by rfl)
    (callEncoding : BaseInstructionEncoding (BitVec.ofNat 8 callByte0.toNat) := by rfl)
    (baseResult : BitVec.ofNat 64 pc + sign_extend (m := 64) (baseImm ++ 0x000#12) =
      BitVec.ofNat 64 callBase := by native_decide)
    (baseDecode : ∀ state, ConfiguredMachinePre EndpointMachinePc state →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 baseByte0.toNat)
        (BitVec.ofNat 8 baseByte1.toNat) (BitVec.ofNat 8 baseByte2.toNat)
        (BitVec.ofNat 8 baseByte3.toNat)))
        (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
        (.UTYPE (baseImm, .Regidx 1#5, .AUIPC)) := by
      intro state configured; write_success_decode configured)
    (callDecode : ∀ state, ConfiguredMachinePre EndpointMachinePc state →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 callByte0.toNat)
        (BitVec.ofNat 8 callByte1.toNat) (BitVec.ofNat 8 callByte2.toNat)
        (BitVec.ofNat 8 callByte3.toNat)))
        (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
        (.JALR (callImm, .Regidx 1#5, .Regidx 1#5)) := by
      intro state configured; write_success_decode configured)
    (targetEq : Sail.BitVec.update
      (BitVec.ofNat 64 callBase + sign_extend (m := 64) callImm) 0 0#1 = 0x15b9c := by
      native_decide)
    (returnEq : Sail.BitVec.addInt (BitVec.ofNat 64 (pc + 4)) 4 =
      BitVec.ofNat 64 returnPc := by native_decide)
    (targetBit1 : Sail.BitVec.access
      (BitVec.ofNat 64 callBase + sign_extend (m := 64) callImm) 1 = 0#1 := by native_decide)
    (parentRangeMember : parentRange ∈ executionPcs := by native_decide)
    (parentLower : parentRange.1 ≤ pc := by native_decide)
    (parentUpper : pc + 8 ≤ parentRange.2 := by native_decide)
    (returnListed : returnPc ∈ Elflings.writeSuccessBooleanExitPcs := by native_decide)
    (outputRangeMember : (0x10190, 0x101c4) ∈ executionPcs := by native_decide)
    (booleanRangeMember : (0x15b9c, 0x15bc8) ∈ executionPcs := by native_decide)
    (pcAfterHost : 0x101d4 < pc := by native_decide)
    (notExit0 : BitVec.ofNat 64 pc ≠ 0x15b9c := by native_decide)
    (notExit1 : BitVec.ofNat 64 (pc + 4) ≠ 0x15b9c := by native_decide) :
    OptionalBooleanCallSite pc returnPc callBase executionPcs := {
  baseStep := by
    intro stepNo state configured atPc loaded
    obtain ⟨retired, run⟩ := configuredAuipcStep stepNo state pc baseImm
      baseByte0 baseByte1 baseByte2 baseByte3
      configured atPc loaded baseSite.pcFits baseSite.read0 baseSite.read1 baseSite.read2
      baseSite.read3 baseSite.pcAligned baseEncoding (baseDecode state configured)
    exact ⟨retired, by simpa [afterRegisterWrite, baseResult] using run⟩
  callStep := by
    intro stepNo state configured atPc baseRead loaded
    exact configuredJalrCallStep stepNo state (pc + 4) (BitVec.ofNat 64 callBase) callImm
      0x15b9c (BitVec.ofNat 64 returnPc) callByte0 callByte1 callByte2 callByte3 configured
      atPc baseRead loaded callSite.pcFits callSite.read0 callSite.read1 callSite.read2
      callSite.read3 callSite.pcAligned callEncoding (callDecode state configured) targetEq
      returnEq targetBit1
  owned0 := by
    unfold pcInRanges
    exact ⟨parentRange, parentRangeMember,
      by simp [Nat.mod_eq_of_lt baseSite.pcFits, parentLower],
      by simp [Nat.mod_eq_of_lt baseSite.pcFits]; omega⟩
  owned1 := by
    unfold pcInRanges
    exact ⟨parentRange, parentRangeMember,
      by simp [Nat.mod_eq_of_lt callSite.pcFits]; omega,
      by simp [Nat.mod_eq_of_lt callSite.pcFits]; omega⟩
  notExit0
  notExit1
  next0 := baseSite.advance
  returnListed
  childInside := by
    intro childPc inside
    unfold pcInRanges at inside ⊢
    rcases inside with ⟨range, member, lower, upper⟩
    simp [Elflings.writeSuccessBooleanExecutionPcRanges] at member
    rcases member with rfl | rfl
    · exact ⟨(0x10190, 0x101c4), outputRangeMember, lower, upper⟩
    · exact ⟨(0x15b9c, 0x15bc8), booleanRangeMember, lower, upper⟩
  notHost0 := by
    intro observed
    unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
      at observed
    rcases observed with equal | equal | equal
    all_goals
      simp [Nat.mod_eq_of_lt baseSite.pcFits] at equal
      omega
  notHost1 := by
    intro observed
    unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
      at observed
    rcases observed with equal | equal | equal
    all_goals
      simp [Nat.mod_eq_of_lt callSite.pcFits] at equal
      omega
}

set_option genInjectivity false in
/-- Shared result of the Boolean tag call used by both optional encoders. -/
structure OptionalBooleanCallHandoff (localFrameSize scratchOffset scratchSize fromStep : Nat)
    (childUsed returnPc : Nat) (executionPcs : List Elflings.PcRange)
    (args : OptionalEncoderArgs Value)
    (tag : Bool) (before after : EndpointState) where
  trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
    fromStep (2 + childUsed) before after
  atPc : after.machine.regs.get? PC = some (BitVec.ofNat 64 returnPc)
  stack : after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer)
  stdout : after.stdout = before.stdout ++ #[if tag then 1 else 0]
  stdin : after.stdin = before.stdin
  stdinCursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : WritesOnlyWithin
    (optionalEncoderMemory localFrameSize scratchOffset scratchSize args.stackPointer)
    before.machine after.machine
  frame : EncoderInlineFrame before after
  access : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args after.machine

private theorem encoderInlinePreserved_abiCalleePreserved_optional (register : Register)
    (preserved : encoderInlinePreserved register) : abiCalleePreserved register := by
  rcases preserved with instruction | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact instructionPreserved_abiCalleePreserved_optional register instruction
  all_goals simp [abiCalleePreserved]

/-- Compose the one Boolean-tag call shared by both optional encoder instances. -/
theorem optionalBooleanCallHandoff
    (child : WriteSuccessBooleanInstanceContract)
    (site : OptionalBooleanCallSite pc returnPc callBase executionPcs)
    (frameLower : 16 ≤ localFrameSize) (fromStep : Nat)
    (args : OptionalEncoderArgs Value) (tag : Bool) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer))
    (tagReg : before.machine.regs.get? x10 = some (if tag then 1 else 0))
    (access : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args
      before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem) :
    ∃ childUsed after, OptionalBooleanCallHandoff localFrameSize scratchOffset scratchSize fromStep
      childUsed returnPc executionPcs args tag before after := by
  let tagBits : BitVec 64 := if tag then 1 else 0
  have seg0 : Seg (optionalBooleanParentPc pc) (fun target => target = 0x15b9c)
      (fun _ _ _ _ _ => False) optionalBooleanCallWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 args.stackPointer⟩, ⟨x10, tagBits⟩]
      fromStep 0 before.machine before.machine (BitVec.ofNat 64 pc) := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    aux := AuxStateAgree.refl _
    retired := access.output.configured.retiredCounter
    atPc
    regs := by
      intro pair member
      simp at member
      rcases member with rfl | rfl
      · exact stack
      · simpa [tagBits] using tagReg }
  obtain ⟨baseMachine, seg1⟩ := seg0.step (by simp [optionalBooleanParentPc]) site.notExit0 x1
    (BitVec.ofNat 64 callBase) (BitVec.ofNat 64 (pc + 4))
    (site.baseStep fromStep _ access.output.configured atPc loaded)
    site.next0 (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [optionalBooleanCallWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have configured1 := access.output.configured.mono
    (seg1.agree instructionPreserved_disjoint_optionalBooleanCallWrites) seg1.retired
  have access1 := access.ofWrites seg1.writes
    (by simp [optionalBooleanCallWrites, stepBookkeeping]) configured1
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully baseMachine.mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨retired2, callRun⟩ := site.callStep (fromStep + 1) baseMachine configured1
    seg1.atPc (seg1.reg x1 (BitVec.ofNat 64 callBase) (by simp)) loaded2
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement baseMachine)
      (BitVec.ofNat 64 (pc + 4)) 0x15b9c x1 (BitVec.ofNat 64 returnPc)) 0x15b9c retired2
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes baseMachine (BitVec.ofNat 64 (pc + 4))
    0x15b9c retired2 x1 (BitVec.ofNat 64 returnPc)
  have callAtPc : callMachine.regs.get? PC = some 0x15b9c := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    have one : callMachine.mem = baseMachine.mem := by
      change
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement baseMachine)
            (BitVec.ofNat 64 (pc + 4)) 0x15b9c x1 (BitVec.ofNat 64 returnPc))
          0x15b9c retired2).mem = baseMachine.mem
      rw [tryStepControlFlowAfterRetired_mem]
      change (controlFlowJumpState (tryStepControlFlowAfterIncrement baseMachine)
        (BitVec.ofNat 64 (pc + 4)) 0x15b9c).mem = baseMachine.mem
      rw [controlFlowJumpState_mem]
      rfl
    exact one.trans (seg1.memEq (by simp))
  let childArgs : EncoderCallArgs Bool :=
    { returnAddress := returnPc
      callerStack := args.stackPointer
      inputSize := args.inputSize
      value := tag }
  have callConfigured := configuredAfterWriteSuccessCall (BitVec.ofNat 64 (pc + 4)) 0x15b9c
    (BitVec.ofNat 64 returnPc) retired2 configured1
  have callAccess : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args
      callMachine := access1.ofWrites callWrites (by simp [stepBookkeeping]) callConfigured
  have childEntry : EncoderCallEntry Elflings.writeSuccessBooleanEntry
      Elflings.writeSuccessBooleanExitPcs 16 BooleanEncoderBinding childArgs callState := by
    have localFrameFits : localFrameSize ≤ args.stackPointer := access.frameFits
    refine ⟨site.returnListed, ?_, args.stackFits, ?_, ?_, ?_, ?_, ?_⟩
    · change 16 ≤ args.stackPointer
      omega
    · simpa [callState] using callAtPc
    · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, childArgs]
    · exact (callWrites.get x2 (by decide)).trans
        (seg1.reg x2 (BitVec.ofNat 64 args.stackPointer) (by simp))
    · exact (callWrites.get x10 (by decide)).trans
        (seg1.reg x10 tagBits (by simp [tagBits]))
    · exact ⟨by simpa [callState, callMemEq] using loaded,
        callAccess.encoderCall frameLower tag⟩
  have callPrefix : ConfinedPrefix (optionalBooleanParentPc pc)
      (fun target => target = 0x15b9c) (fun _ _ _ _ _ => False)
      (fromStep + 1) 1 baseMachine callMachine :=
    ConfinedPrefix.ownStep seg1.atPc (by simp [optionalBooleanParentPc]) site.notExit1 callRun
  have callEnd : ScopedTrace (optionalBooleanParentPc pc) (fun target => target = 0x15b9c)
      (fun _ _ _ _ _ => False) (fromStep + 2) 0 callMachine callMachine :=
    .exitAt _ _ 0x15b9c callAtPc rfl
  have parentMachineTrace := seg1.confined.trans callPrefix 0 callMachine callEnd
  have parentTraceExact := liftOptionalParentTrace before (fun parentPc inside => by
    rcases inside with rfl | rfl
    · exact site.notHost0
    · exact site.notHost1) parentMachineTrace
  have parentTrace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep 2 before callState := by
    simpa [callState] using parentTraceExact.weaken (fun _ inside => by
      rcases inside with rfl | rfl
      · exact site.owned0
      · exact site.owned1)
  obtain ⟨childUsed, after, _unit, positive, bounded, childTrace, exitPc, allowed,
      childExit⟩ := EncoderCallInstanceContract.implements child childArgs
        (fromStep + 2) callState childEntry
  rcases childExit with ⟨afterPc, stdout, stdin, cursor, exitCode, childFits, childMemory,
    childFrame⟩
  have childTrace' := childTrace.weaken (fun _ childPc => site.childInside childPc)
  have trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep (2 + childUsed) before after := by
    simpa [Nat.add_assoc] using parentTrace.append childTrace'
  have memory : WritesOnlyWithin
      (optionalEncoderMemory localFrameSize scratchOffset scratchSize args.stackPointer)
      before.machine after.machine := by
    intro address outside
    rw [childMemory address (by
      intro inside
      apply outside
      rcases inside with childFrameInside | outputInside
      · left
        change byteRange (args.stackPointer - 16) 16 address at childFrameInside
        unfold byteRange at childFrameInside ⊢
        omega
      · right
        exact Or.inr outputInside), callMemEq]
  have parentAgree : Agree encoderInlinePreserved before.machine callMachine :=
    (seg1.writes.agree encoderInlinePreserved_disjoint_optionalBooleanCallWrites).trans
      (callWrites.agree (by
        intro register preserved written
        apply encoderInlinePreserved_disjoint_optionalBooleanCallWrites register preserved
        rcases written with bookkeeping | rfl
        · exact Or.inl bookkeeping
        · exact Or.inr (Or.inl rfl)))
  have allAgree : Agree encoderInlinePreserved before.machine after.machine :=
    parentAgree.trans
      (childFrame.1.weaken encoderInlinePreserved_abiCalleePreserved_optional)
  have callChoice : callMachine.choiceState = before.machine.choiceState := by
    change baseMachine.choiceState = before.machine.choiceState
    exact seg1.aux.1
  have callTags : callMachine.tags = before.machine.tags := by
    change baseMachine.tags = before.machine.tags
    exact seg1.aux.2.1
  have callOutput : callMachine.sailOutput = before.machine.sailOutput := by
    change baseMachine.sailOutput = before.machine.sailOutput
    exact seg1.aux.2.2
  have aux : EndpointMachineAuxAgree before.machine after.machine := by
    refine ⟨?_, ?_, ?_⟩
    · exact childFrame.2.2.2.1.trans callChoice
    · exact childFrame.2.2.2.2.1.trans callTags
    · exact childFrame.2.2.2.2.2.trans callOutput
  have frame : EncoderInlineFrame before after :=
    ⟨allAgree, childFrame.2.1, childFrame.2.2.1, aux⟩
  have childInlineFrame : EncoderInlineFrame callState after := by
    exact ⟨childFrame.1.weaken encoderInlinePreserved_abiCalleePreserved_optional,
      childFrame.2.1, childFrame.2.2.1,
      childFrame.2.2.2.1, childFrame.2.2.2.2.1, childFrame.2.2.2.2.2⟩
  exact ⟨childUsed, after, {
    trace
    atPc := by simpa [childArgs] using afterPc
    stack := by
      simpa [childArgs] using
        (childFrame.1 x2 (by simp [abiCalleePreserved])).trans childEntry.2.2.2.2.2.1
    stdout := by simpa [childArgs] using stdout
    stdin := by simpa [callState] using stdin
    stdinCursor := by simpa [callState] using cursor
    exitCode := by simpa [callState] using exitCode
    memory
    frame
    access := callAccess.ofEncoderFrame callState childInlineFrame }⟩

def OptionalEncoderEntry (entry localFrameSize scratchOffset scratchSize : Nat)
    (bindValue : OptionalEncoderArgs Value → EndpointState → Prop)
    (args : OptionalEncoderArgs Value) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  bindValue args state ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args state.machine

def OptionalEncoderExit (successPc localFrameSize scratchOffset scratchSize : Nat)
    (encodePayload : Value → Array UInt8) (args : OptionalEncoderArgs Value)
    (_outcome : Unit) (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 successPc) ∧
  after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  after.stdout = before.stdout ++ encodeOptional encodePayload args.value ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧
  WritesOnlyWithin
    (optionalEncoderMemory localFrameSize scratchOffset scratchSize args.stackPointer)
    before.machine after.machine ∧
  EncoderInlineFrame before after

def optionalEncoderContract (entry successPc localFrameSize scratchOffset scratchSize : Nat)
    (encodePayload : Value → Array UInt8)
    (bindValue : OptionalEncoderArgs Value → EndpointState → Prop)
    (stepBound : Nat → Nat) :
    RelationalMachineContract EndpointState (OptionalEncoderArgs Value) Unit :=
  { allows := fun _ _ => True
    entry := OptionalEncoderEntry entry localFrameSize scratchOffset scratchSize bindValue
    exit := OptionalEncoderExit successPc localFrameSize scratchOffset scratchSize encodePayload
    stepBound := fun args => stepBound args.inputSize }

def OptionalEncoderInstanceContract (entry successPc localFrameSize scratchOffset scratchSize : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat)
    (encodePayload : Value → Array UInt8)
    (bindValue : OptionalEncoderArgs Value → EndpointState → Prop) : Prop :=
  ∃ stepBound : Nat → Nat,
    (∀ inputSize, inputSize ≤ maxSszInputSize → stepBound inputSize < level2ContractFuel) ∧
    (optionalEncoderContract entry successPc localFrameSize scratchOffset scratchSize
      encodePayload bindValue stepBound).Implements EndpointStep EndpointPc
        (pcInRanges executionPcs) (pcInList exitPcs)

set_option genInjectivity false in
/-- The two semantic routes shared by every optional encoder. -/
structure OptionalEncoderRouteHandoff {Value : Type}
    (encodePayload : Value → Array UInt8) (value : Option Value)
    (beforeOutput afterOutput : Array UInt8) : Prop where
  route :
    (value = none ∧ afterOutput = beforeOutput ++ #[0]) ∨
    (∃ payload, value = some payload ∧
      afterOutput = beforeOutput ++ #[1] ++ encodePayload payload)

/-- Convert either reviewed tag route into the common optional-output expression. -/
theorem OptionalEncoderRouteHandoff.output {Value : Type}
    {encodePayload : Value → Array UInt8} {value : Option Value}
    {beforeOutput afterOutput : Array UInt8}
    (handoff : OptionalEncoderRouteHandoff encodePayload value beforeOutput afterOutput) :
    afterOutput = beforeOutput ++ @encodeOptional Value encodePayload value := by
  rcases handoff.route with absent | present
  · rcases absent with ⟨rfl, output⟩
    simpa [encodeOptional] using output
  · rcases present with ⟨payload, rfl, output⟩
    simpa [encodeOptional, Array.append_assoc] using output

set_option genInjectivity false in
/-- The common machine and endpoint facts after either optional route reaches its join PC. -/
structure OptionalEncoderCompletedHandoff {Value : Type}
    (successPc localFrameSize scratchOffset scratchSize fromStep count : Nat)
    (executionPcs : List Elflings.PcRange) (encodePayload : Value → Array UInt8)
    (args : OptionalEncoderArgs Value) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
    fromStep count before after
  atPc : after.machine.regs.get? PC = some (BitVec.ofNat 64 successPc)
  stack : after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer)
  output : OptionalEncoderRouteHandoff encodePayload args.value before.stdout after.stdout
  stdin : after.stdin = before.stdin
  stdinCursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : WritesOnlyWithin
    (optionalEncoderMemory localFrameSize scratchOffset scratchSize args.stackPointer)
    before.machine after.machine
  frame : EncoderInlineFrame before after

/-- Close the shared optional-encoder exit from one route handoff. -/
theorem OptionalEncoderCompletedHandoff.exit
    (handoff : OptionalEncoderCompletedHandoff successPc localFrameSize scratchOffset scratchSize
      fromStep count executionPcs encodePayload args before after) :
    OptionalEncoderExit successPc localFrameSize scratchOffset scratchSize encodePayload args ()
      before after := by
  exact ⟨handoff.atPc, handoff.stack, handoff.output.output, handoff.stdin,
    handoff.stdinCursor, handoff.exitCode, handoff.memory, handoff.frame⟩

/-- Exact machine routes for one specialization of the shared optional encoder. -/
structure OptionalEncoderSite {Value : Type}
    (entry successPc localFrameSize scratchOffset scratchSize : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat)
    (encodePayload : Value → Array UInt8)
    (bindValue : OptionalEncoderArgs Value → EndpointState → Prop) where
  stepBound : Nat
  stepBoundFits : stepBound < level2ContractFuel
  run : ∀ fromStep args before,
    OptionalEncoderEntry entry localFrameSize scratchOffset scratchSize bindValue args before →
    ∃ count after,
      0 < count ∧ count ≤ stepBound ∧
      OptionalEncoderCompletedHandoff successPc localFrameSize scratchOffset scratchSize
        fromStep count executionPcs encodePayload args before after
  successListed : successPc ∈ exitPcs
  successFits : successPc < 2 ^ 64

/-- Prove each compatible optional encoder through the shared route and exit theorem. -/
theorem optionalEncoderInstanceContract_of_site
    (site : OptionalEncoderSite entry successPc localFrameSize scratchOffset scratchSize
      executionPcs exitPcs encodePayload bindValue) :
    OptionalEncoderInstanceContract entry successPc localFrameSize scratchOffset scratchSize
      executionPcs exitPcs encodePayload bindValue := by
  refine ⟨fun _ => site.stepBound, fun _ _ => site.stepBoundFits, ?_⟩
  intro args fromStep before entryPre
  obtain ⟨count, after, positive, bounded, handoff⟩ := site.run fromStep args before entryPre
  exact ⟨count, after, (), positive, bounded, handoff.trace,
    ⟨BitVec.ofNat 64 successPc, handoff.atPc, by
      unfold pcInList
      simpa [Nat.mod_eq_of_lt site.successFits] using site.successListed⟩,
    trivial, handoff.exit⟩

structure OptionalU128Words where
  low : Nat
  high : Nat
  lowFits : low < 2 ^ 64
  highFits : high < 2 ^ 64

def encodeOptionalU128Words (value : OptionalU128Words) : Array UInt8 :=
  encodeNatLE 8 value.low ++ encodeNatLE 8 value.high

def OptionalU128Binding (args : OptionalEncoderArgs OptionalU128Words)
    (state : EndpointState) : Prop :=
  state.machine.regs.get? x27 = some (if args.value.isSome then 1 else 0) ∧
  ∀ value, args.value = some value →
    state.machine.regs.get? x9 = some (BitVec.ofNat 64 value.low) ∧
    state.machine.regs.get? x23 = some (BitVec.ofNat 64 value.high)

def OptionalAddressBinding (args : OptionalEncoderArgs (Array UInt8))
    (state : EndpointState) : Prop :=
  state.machine.regs.get? x10 = some (if args.value.isSome then 1 else 0) ∧
  ∀ value, args.value = some value → value.size = 20 ∧
    BytesRep state.machine.mem (args.stackPointer + 0x668) value

def optionalU128ExecutionPcs : List Elflings.PcRange :=
  [(0x10190, 0x101c4), (0x15118, 0x15148), (0x15b9c, 0x15bc8), (0x15ce4, 0x15d10)]

def optionalU128ExitPcs : List Nat := [0x14d10, 0x15148]

def optionalAddressExecutionPcs : List Elflings.PcRange :=
  [(0x10190, 0x101c4), (0x15158, 0x1519c), (0x15b9c, 0x15bc8)]

def optionalAddressExitPcs : List Nat := [0x14d10, 0x1519c]

private def optionalU128PresentBooleanSite :
    OptionalBooleanCallSite 0x15120 0x15128 0x16120 optionalU128ExecutionPcs :=
  optionalBooleanCallSiteOfLiterals 0x15120 0x15128 0x16120 1 0xa7c
    0x97 0x10 0x00 0x00 0xe7 0x80 0xc0 0xa7 optionalU128ExecutionPcs
    (0x15118, 0x15148)

private def optionalU128AbsentBooleanSite :
    OptionalBooleanCallSite 0x15140 0x15148 0x16140 optionalU128ExecutionPcs :=
  optionalBooleanCallSiteOfLiterals 0x15140 0x15148 0x16140 1 0xa5c
    0x97 0x10 0x00 0x00 0xe7 0x80 0xc0 0xa5 optionalU128ExecutionPcs
    (0x15118, 0x15148)

private def optionalAddressPresentBooleanSite :
    OptionalBooleanCallSite 0x15178 0x15180 0x16178 optionalAddressExecutionPcs :=
  optionalBooleanCallSiteOfLiterals 0x15178 0x15180 0x16178 1 0xa24
    0x97 0x10 0x00 0x00 0xe7 0x80 0x40 0xa2 optionalAddressExecutionPcs
    (0x15158, 0x1519c)

private def optionalAddressAbsentBooleanSite :
    OptionalBooleanCallSite 0x15194 0x1519c 0x16194 optionalAddressExecutionPcs :=
  optionalBooleanCallSiteOfLiterals 0x15194 0x1519c 0x16194 1 0xa08
    0x97 0x10 0x00 0x00 0xe7 0x80 0x80 0xa0 optionalAddressExecutionPcs
    (0x15158, 0x1519c)

abbrev Proposed_ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b_Contract : Prop :=
  OptionalEncoderInstanceContract 0x15118 0x15148 32 0 0 optionalU128ExecutionPcs
    optionalU128ExitPcs encodeOptionalU128Words OptionalU128Binding

abbrev Proposed_ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94_Contract : Prop :=
  OptionalEncoderInstanceContract 0x15158 0x1519c 16 0x6d0 20 optionalAddressExecutionPcs
    optionalAddressExitPcs (fun value => value) OptionalAddressBinding

end BinaryFv.Zesu.Staging
