import BinaryFv.Zesu.Staging.IntegerEncoder
import BinaryFv.Zesu.Staging.RawEncoder
import BinaryFv.Zesu.Staging.BooleanEncoder

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
    (stepBound : Nat → Nat)
    (child : (encoderCallContract Elflings.writeSuccessBooleanEntry
      Elflings.writeSuccessBooleanExitPcs 16
      (fun value => #[if value then 1 else 0]) BooleanEncoderBinding stepBound).Implements
        EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessBooleanExecutionPcRanges)
        (pcInList Elflings.writeSuccessBooleanExitPcs))
    (site : OptionalBooleanCallSite pc returnPc callBase executionPcs)
    (frameLower : 16 ≤ localFrameSize) (fromStep : Nat)
    (args : OptionalEncoderArgs Value) (tag : Bool) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer))
    (tagReg : before.machine.regs.get? x10 = some (if tag then 1 else 0))
    (access : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args
      before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem) :
    ∃ childUsed after, childUsed ≤ stepBound args.inputSize ∧
      OptionalBooleanCallHandoff localFrameSize scratchOffset scratchSize fromStep
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
      childExit⟩ := child childArgs (fromStep + 2) callState childEntry
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
  exact ⟨childUsed, after, bounded, {
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

set_option genInjectivity false in
/-- Parent facts required immediately before the shared two-word integer encoder starts. -/
structure OptionalIntegerChildReady
    (localFrameSize scratchOffset scratchSize fromStep parentCount returnPc word0 word1 : Nat)
    (executionPcs : List Elflings.PcRange) (args : OptionalEncoderArgs Value)
    (before ready : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
    fromStep parentCount before ready
  atPc : ready.machine.regs.get? PC = some 0x15ce4
  link : ready.machine.regs.get? x1 = some (BitVec.ofNat 64 returnPc)
  stack : ready.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer)
  word0Reg : ready.machine.regs.get? x10 = some (BitVec.ofNat 64 word0)
  word1Reg : ready.machine.regs.get? x11 = some (BitVec.ofNat 64 word1)
  returnListed : returnPc ∈ integerEncoderU128ExitPcs
  childInside : ∀ {childPc}, pcInRanges integerEncoderU128ExecutionPcs childPc →
    pcInRanges executionPcs childPc
  word0Fits : word0 < 2 ^ 64
  word1Fits : word1 < 2 ^ 64
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully ready.machine.mem
  access : IntegerEncoderMachineAccess (args.stackPointer - 32) 32 ready.machine
  outerAccess : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args
    ready.machine
  stdout : ready.stdout = before.stdout
  stdin : ready.stdin = before.stdin
  stdinCursor : ready.stdinCursor = before.stdinCursor
  exitCode : ready.exitCode = before.exitCode
  memory : WritesOnlyWithin
    (optionalEncoderMemory localFrameSize scratchOffset scratchSize args.stackPointer)
    before.machine ready.machine
  frame : EncoderInlineFrame before ready

def optionalIntegerParentPc (pc : Nat) (parentPc : BitVec 64) : Prop :=
  parentPc = BitVec.ofNat 64 pc ∨ parentPc = BitVec.ofNat 64 (pc + 4) ∨
    parentPc = BitVec.ofNat 64 (pc + 8) ∨ parentPc = BitVec.ofNat 64 (pc + 12)

def optionalIntegerCallWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x1 ∨ register = x10 ∨ register = x11

private theorem encoderInlinePreserved_disjoint_optionalIntegerCallWrites :
    RegSet.Disjoint encoderInlinePreserved optionalIntegerCallWrites := by
  intro register preserved written
  simp [encoderInlinePreserved, optionalIntegerCallWrites, instructionPreserved,
    platformPreserved, stepBookkeeping] at preserved written
  grind

private theorem instructionPreserved_disjoint_optionalIntegerCallWrites :
    RegSet.Disjoint instructionPreserved optionalIntegerCallWrites := by
  intro register preserved
  exact encoderInlinePreserved_disjoint_optionalIntegerCallWrites register (Or.inl preserved)

set_option genInjectivity false in
/-- Four exact parent steps that move two words and enter the shared integer encoder. -/
structure OptionalIntegerCallSite (pc returnPc callBase : Nat)
    (executionPcs : List Elflings.PcRange) where
  move0 : ∀ stepNo state source,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 pc) →
    state.regs.get? x9 = some source →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10 source) false
  move1 : ∀ stepNo state source,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 (pc + 4)) →
    state.regs.get? x23 = some source →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 (pc + 4)) retired x11 source) false
  base : ∀ stepNo state,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 (pc + 8)) →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 (pc + 8)) retired x1
        (BitVec.ofNat 64 callBase)) false
  call : ∀ stepNo state,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 (pc + 12)) →
    state.regs.get? x1 = some (BitVec.ofNat 64 callBase) →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 (pc + 12)) 0x15ce4 x1 (BitVec.ofNat 64 returnPc))
        0x15ce4 retired) false
  owned : ∀ offset, offset ∈ [0, 4, 8, 12] →
    pcInRanges executionPcs (BitVec.ofNat 64 (pc + offset))
  next0 : BitVec.ofNat 64 pc + 4 = BitVec.ofNat 64 (pc + 4)
  next1 : BitVec.ofNat 64 (pc + 4) + 4 = BitVec.ofNat 64 (pc + 8)
  next2 : BitVec.ofNat 64 (pc + 8) + 4 = BitVec.ofNat 64 (pc + 12)
  notExit : ∀ offset, offset ∈ [0, 4, 8, 12] →
    BitVec.ofNat 64 (pc + offset) ≠ 0x15ce4
  returnListed : returnPc ∈ integerEncoderU128ExitPcs
  childInside : ∀ {childPc}, pcInRanges integerEncoderU128ExecutionPcs childPc →
    pcInRanges executionPcs childPc
  notHost : ∀ offset, offset ∈ [0, 4, 8, 12] →
    ¬BareMetalHostTransitionPc (BitVec.ofNat 64 (pc + offset))

/-- Compose the common two-register setup and direct integer call before consuming the child. -/
theorem optionalIntegerCallReady
    (site : OptionalIntegerCallSite pc returnPc callBase executionPcs)
    (fromStep : Nat) (args : OptionalEncoderArgs Value) (word0 word1 : Nat)
    (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer))
    (word0Reg : before.machine.regs.get? x9 = some (BitVec.ofNat 64 word0))
    (word1Reg : before.machine.regs.get? x23 = some (BitVec.ofNat 64 word1))
    (word0Fits : word0 < 2 ^ 64) (word1Fits : word1 < 2 ^ 64)
    (access : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args
      before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (childInsideFrame : 32 ≤ localFrameSize) :
    ∃ ready, OptionalIntegerChildReady localFrameSize scratchOffset scratchSize fromStep 4
      returnPc word0 word1 executionPcs args before ready := by
  have seg0 : Seg (optionalIntegerParentPc pc) (fun target => target = 0x15ce4)
      (fun _ _ _ _ _ => False) optionalIntegerCallWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 args.stackPointer⟩, ⟨x9, BitVec.ofNat 64 word0⟩,
        ⟨x23, BitVec.ofNat 64 word1⟩]
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
      rcases member with rfl | rfl | rfl
      · exact stack
      · exact word0Reg
      · exact word1Reg }
  obtain ⟨machine1, seg1⟩ := seg0.step (by simp [optionalIntegerParentPc])
    (site.notExit 0 (by simp)) x10
    (BitVec.ofNat 64 word0) (BitVec.ofNat 64 (pc + 4))
    (site.move0 fromStep _ _ access.output.configured atPc word0Reg loaded) site.next0
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [optionalIntegerCallWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := access.ofWrites seg1.writes
    (by simp [optionalIntegerCallWrites, stepBookkeeping])
    (access.output.configured.mono
      (seg1.agree instructionPreserved_disjoint_optionalIntegerCallWrites) seg1.retired)
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨machine2, seg2⟩ := seg1.step (by simp [optionalIntegerParentPc])
    (site.notExit 4 (by simp)) x11
    (BitVec.ofNat 64 word1) (BitVec.ofNat 64 (pc + 8))
    (site.move1 (fromStep + 1) _ _ access1.output.configured seg1.atPc
      (seg1.reg x23 (BitVec.ofNat 64 word1) (by simp)) loaded1) site.next1
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [optionalIntegerCallWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := access.ofWrites seg2.writes
    (by simp [optionalIntegerCallWrites, stepBookkeeping])
    (access.output.configured.mono
      (seg2.agree instructionPreserved_disjoint_optionalIntegerCallWrites) seg2.retired)
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully machine2.mem := by
    simpa [seg2.memEq (by simp)] using loaded
  obtain ⟨machine3, seg3⟩ := seg2.step (by simp [optionalIntegerParentPc])
    (site.notExit 8 (by simp)) x1
    (BitVec.ofNat 64 callBase) (BitVec.ofNat 64 (pc + 12))
    (site.base (fromStep + 2) _ access2.output.configured seg2.atPc loaded2) site.next2
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [optionalIntegerCallWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := access.ofWrites seg3.writes
    (by simp [optionalIntegerCallWrites, stepBookkeeping])
    (access.output.configured.mono
      (seg3.agree instructionPreserved_disjoint_optionalIntegerCallWrites) seg3.retired)
  have loaded3 : Artifacts.programImage.fileBytesLoadedFaithfully machine3.mem := by
    simpa [seg3.memEq (by simp)] using loaded
  obtain ⟨retired3, callRun⟩ := site.call (fromStep + 3) machine3
    access3.output.configured seg3.atPc
    (seg3.reg x1 (BitVec.ofNat 64 callBase) (by simp)) loaded3
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement machine3)
      (BitVec.ofNat 64 (pc + 12)) 0x15ce4 x1 (BitVec.ofNat 64 returnPc)) 0x15ce4 retired3
  let ready : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes machine3 (BitVec.ofNat 64 (pc + 12))
    0x15ce4 retired3 x1 (BitVec.ofNat 64 returnPc)
  have callAtPc : callMachine.regs.get? PC = some 0x15ce4 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    have one : callMachine.mem = machine3.mem := by
      change
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement machine3)
            (BitVec.ofNat 64 (pc + 12)) 0x15ce4 x1 (BitVec.ofNat 64 returnPc))
          0x15ce4 retired3).mem = machine3.mem
      rw [tryStepControlFlowAfterRetired_mem]
      change (controlFlowJumpState (tryStepControlFlowAfterIncrement machine3)
        (BitVec.ofNat 64 (pc + 12)) 0x15ce4).mem = machine3.mem
      rw [controlFlowJumpState_mem]
      rfl
    exact one.trans (seg3.memEq (by simp))
  have callConfigured := configuredAfterWriteSuccessCall (BitVec.ofNat 64 (pc + 12)) 0x15ce4
    (BitVec.ofNat 64 returnPc) retired3 access3.output.configured
  have callAccess := access3.ofWrites callWrites (by simp [stepBookkeeping]) callConfigured
  have callPrefix : ConfinedPrefix (optionalIntegerParentPc pc) (fun target => target = 0x15ce4)
      (fun _ _ _ _ _ => False) (fromStep + 3) 1 machine3 callMachine :=
    ConfinedPrefix.ownStep seg3.atPc (by simp [optionalIntegerParentPc])
      (site.notExit 12 (by simp)) callRun
  have callEnd : ScopedTrace (optionalIntegerParentPc pc) (fun target => target = 0x15ce4)
      (fun _ _ _ _ _ => False) (fromStep + 4) 0 callMachine callMachine :=
    .exitAt _ _ 0x15ce4 callAtPc rfl
  have machineTrace := seg3.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace := liftOptionalParentTrace before (fun parentPc inside => by
    rcases inside with rfl | rfl | rfl | rfl
    · exact site.notHost 0 (by simp)
    · exact site.notHost 4 (by simp)
    · exact site.notHost 8 (by simp)
    · exact site.notHost 12 (by simp)) machineTrace
  have trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep 4 before ready := by
    simpa [ready] using parentTrace.weaken (fun _ inside => by
      rcases inside with rfl | rfl | rfl | rfl
      · exact site.owned 0 (by simp)
      · exact site.owned 4 (by simp)
      · exact site.owned 8 (by simp)
      · exact site.owned 12 (by simp))
  have parentAgree := seg3.writes.agree encoderInlinePreserved_disjoint_optionalIntegerCallWrites
  have allAgree : Agree encoderInlinePreserved before.machine callMachine :=
    parentAgree.trans (callWrites.agree (by
      intro register preserved written
      apply encoderInlinePreserved_disjoint_optionalIntegerCallWrites register preserved
      rcases written with bookkeeping | rfl
      · exact Or.inl bookkeeping
      · exact Or.inr (Or.inl rfl)))
  have callChoice : callMachine.choiceState = before.machine.choiceState := by
    change machine3.choiceState = before.machine.choiceState
    exact seg3.aux.1
  have callTags : callMachine.tags = before.machine.tags := by
    change machine3.tags = before.machine.tags
    exact seg3.aux.2.1
  have callOutput : callMachine.sailOutput = before.machine.sailOutput := by
    change machine3.sailOutput = before.machine.sailOutput
    exact seg3.aux.2.2
  have frame : EncoderInlineFrame before ready := ⟨allAgree, callConfigured.retiredCounter,
    by simpa [ready, callMemEq] using loaded,
    by
      change EndpointMachineAuxAgree before.machine callMachine
      exact ⟨callChoice, callTags, callOutput⟩⟩
  exact ⟨ready, {
    trace
    atPc := by simpa [ready] using callAtPc
    link := by simp [ready, callMachine, callLinkState, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
    stack := by
      change callMachine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer)
      exact (callWrites.get x2 (by decide)).trans
        (seg3.reg x2 (BitVec.ofNat 64 args.stackPointer) (by simp))
    word0Reg := by
      change callMachine.regs.get? x10 = some (BitVec.ofNat 64 word0)
      exact (callWrites.get x10 (by decide)).trans
        (seg3.reg x10 (BitVec.ofNat 64 word0) (by simp))
    word1Reg := by
      change callMachine.regs.get? x11 = some (BitVec.ofNat 64 word1)
      exact (callWrites.get x11 (by decide)).trans
        (seg3.reg x11 (BitVec.ofNat 64 word1) (by simp))
    returnListed := site.returnListed
    childInside := site.childInside
    word0Fits
    word1Fits
    loaded := by simpa [ready, callMemEq] using loaded
    access := by simpa [ready] using callAccess.integerEncoder 32 childInsideFrame (by decide)
    outerAccess := by simpa [ready] using callAccess
    stdout := rfl
    stdin := rfl
    stdinCursor := rfl
    exitCode := rfl
    memory := by intro address outside; simp [ready, callMemEq]
    frame }⟩

set_option genInjectivity false in
/-- Shared result after the two-word integer child returns to one optional encoder. -/
structure OptionalIntegerCallHandoff
    (localFrameSize scratchOffset scratchSize fromStep parentCount childUsed returnPc word0 word1 :
      Nat)
    (executionPcs : List Elflings.PcRange) (args : OptionalEncoderArgs Value)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
    fromStep (parentCount + childUsed) before after
  atPc : after.machine.regs.get? PC = some (BitVec.ofNat 64 returnPc)
  stack : after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer)
  stdout : after.stdout = before.stdout ++ encodeNatLE 8 word0 ++ encodeNatLE 8 word1
  stdin : after.stdin = before.stdin
  stdinCursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : WritesOnlyWithin
    (optionalEncoderMemory localFrameSize scratchOffset scratchSize args.stackPointer)
    before.machine after.machine
  frame : EncoderInlineFrame before after
  access : OptionalEncoderMachineAccess localFrameSize scratchOffset scratchSize args after.machine

/-- Consume the shared two-word integer contract after any reviewed parent setup trace. -/
theorem optionalIntegerChildHandoff
    (stepBound : Nat)
    (child : (integerEncoderContract 0x15ce4 32 2 integerEncoderU128ExitPcs
      (fun _ => stepBound)).Implements EndpointStep EndpointPc
        (pcInRanges integerEncoderU128ExecutionPcs) (pcInList integerEncoderU128ExitPcs))
    (ready : OptionalIntegerChildReady localFrameSize scratchOffset scratchSize fromStep
      parentCount returnPc word0 word1 executionPcs args before callState)
    (childInside : 32 ≤ localFrameSize) :
    ∃ childUsed after, childUsed ≤ stepBound ∧
      OptionalIntegerCallHandoff localFrameSize scratchOffset scratchSize fromStep parentCount
        childUsed returnPc word0 word1 executionPcs args before after := by
  let childArgs : IntegerEncoderArgs :=
    { stackPointer := args.stackPointer
      returnPc
      word0
      word1
      word2 := 0
      word3 := 0
      stackFits := args.stackFits
      returnFits := by
        have listed := ready.returnListed
        simp [integerEncoderU128ExitPcs] at listed
        omega
      word0Fits := ready.word0Fits
      word1Fits := ready.word1Fits
      word2Fits := by omega
      word3Fits := by omega }
  have entry : IntegerEncoderEntry 0x15ce4 32 2 integerEncoderU128ExitPcs childArgs
      callState := by
    refine ⟨ready.atPc, ready.link, ready.stack, ?_, ?_, ?_, ?_, ready.loaded⟩
    · exact ⟨ready.word0Reg, ready.word1Reg, Or.inl rfl⟩
    · unfold pcInList
      simpa [childArgs, Nat.mod_eq_of_lt childArgs.returnFits] using ready.returnListed
    · have frameFits := ready.outerAccess.frameFits
      simpa [childArgs] using (show 32 ≤ args.stackPointer by omega)
    · simpa [childArgs] using ready.outerAccess.integerEncoder 32 childInside (by decide)
  obtain ⟨childUsed, after, _unit, positive, bounded, childTrace, _exitAt, _allowed,
      childExit⟩ := child childArgs (fromStep + parentCount) callState entry
  rcases childExit with ⟨afterPc, _link, afterStack, stdout, stdin, cursor, exitCode,
    childMemory, childAgree, childRetired, childLoaded, childAux⟩
  have childTrace' := childTrace.weaken (fun _ childPc => ready.childInside childPc)
  have trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep (parentCount + childUsed) before after := by
    simpa [Nat.add_assoc] using ready.trace.append childTrace'
  have memory : WritesOnlyWithin
      (optionalEncoderMemory localFrameSize scratchOffset scratchSize args.stackPointer)
      before.machine after.machine := by
    intro address outside
    rw [childMemory address (by
      intro inside
      apply outside
      rcases inside with childFrame | output
      · left
        change byteRange (args.stackPointer - 32) 32 address at childFrame
        unfold byteRange at childFrame ⊢
        have frameFits := ready.outerAccess.frameFits
        omega
      · exact Or.inr (Or.inr output))]
    exact ready.memory address outside
  have frame : EncoderInlineFrame before after := by
    refine ⟨ready.frame.1.trans (childAgree.weaken (fun _ preserved => Or.inl preserved)),
      childRetired, childLoaded, ?_⟩
    exact ⟨childAux.1.trans ready.frame.2.2.2.1,
      childAux.2.1.trans ready.frame.2.2.2.2.1,
      childAux.2.2.trans ready.frame.2.2.2.2.2⟩
  have childFrame : EncoderInlineFrame callState after :=
    ⟨childAgree.weaken (fun _ preserved => Or.inl preserved), childRetired, childLoaded,
      childAux⟩
  exact ⟨childUsed, after, bounded, {
    trace
    atPc := by simpa [childArgs] using afterPc
    stack := by simpa [childArgs] using afterStack
    stdout := by simpa [childArgs, integerEncoderBytes, Array.append_assoc, ready.stdout] using stdout
    stdin := by simpa [ready.stdin] using stdin
    stdinCursor := by simpa [ready.stdinCursor] using cursor
    exitCode := by simpa [ready.exitCode] using exitCode
    memory
    frame
    access := ready.outerAccess.ofEncoderFrame callState childFrame }⟩

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
    {Value : Type} {encodePayload : Value → Array UInt8}
    {args : OptionalEncoderArgs Value} {before after : EndpointState}
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
    {Value : Type}
    {encodePayload : Value → Array UInt8}
    {bindValue : OptionalEncoderArgs Value → EndpointState → Prop}
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

private theorem optionalU128PresenceCondition (state : State) (value : BitVec 64)
    (valueAt : state.regs.get? x27 = some value) :
    Runs (bTypeTaken (.Regidx 0#5) (.Regidx 27#5) .BEQ) state state (value == 0) := by
  unfold bTypeTaken
  refine Runs.bind (rX_x27_run state value valueAt) ?_
  refine Runs.bind (rX_x0_run state) ?_
  rfl

/-- Execute the shared U128 presence branch for either reviewed semantic route. -/
private theorem optionalU128PresenceBranchStep (stepNo : Nat) (state : State)
    (present : Bool) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15118)
    (presenceAt : state.regs.get? x27 = some (if present then 1 else 0))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    if present then
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15118)
          0x1511c retired) false
    else
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x15118 0x1513c)
          0x1513c retired) false := by
  cases present
  · simp only [Bool.false_eq_true, ↓reduceIte] at presenceAt ⊢
    apply configuredBranchTakenStep stepNo 0x15118 0x1513c state 0x024 (.Regidx 0#5)
      (.Regidx 27#5) .BEQ 0x63 0x82 0x0d 0x02 configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode configured
    · simpa using optionalU128PresenceCondition
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15118) 0
        ((stepPremiseState_writes state 0x15118).get x27 (by decide) |>.trans presenceAt)
    all_goals native_decide
  · simp only [↓reduceIte] at presenceAt ⊢
    apply configuredBranchNotTakenStep stepNo 0x15118 state 0x024 (.Regidx 0#5)
      (.Regidx 27#5) .BEQ 0x63 0x82 0x0d 0x02 configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode configured
    · simpa using optionalU128PresenceCondition
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15118) 1
        ((stepPremiseState_writes state 0x15118).get x27 (by decide) |>.trans presenceAt)

/-- Execute either exact Boolean tag literal used by the U128 routes. -/
private theorem optionalU128TagStep (stepNo pc value : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (site : ExactInstructionSite pc 0x13 0x05 (if value = 0 then 0x00 else 0x10) 0x00 := by
      native_decide)
    (valueCase : value = 0 ∨ value = 1) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10 (BitVec.ofNat 64 value)) false := by
  rcases valueCase with rfl | rfl
  · exact configuredITypeX10Step stepNo pc state 0 (.Regidx 0#5) .ADDI 0 0
      0x13 0x05 0x00 0x00 configured atPc loaded
      (by native_decide)
      (by intro premise _; exact rX_x0_run premise)
      (by intro premise; exact wX_x10_run premise 0)
      (by write_success_decode configured) (base := by rfl) (site := site)
  · exact configuredITypeX10Step stepNo pc state 1 (.Regidx 0#5) .ADDI 0 1
      0x13 0x05 0x10 0x00 configured atPc loaded
      (by native_decide)
      (by intro premise _; exact rX_x0_run premise)
      (by intro premise; exact wX_x10_run premise 1)
      (by write_success_decode configured) (base := by rfl) (site := site)

/-- Exact U128 present-route jump from the integer return to the shared join. -/
private theorem optionalU128JoinJumpStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15138)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x15138 0x15148)
        0x15148 retired) false := by
  exact configuredJStep stepNo 0x15138 0x15148 state 0x10
    0x6f 0x00 0x00 0x01 configured atPc loaded
    (by configured_decode configured) (by native_decide) (by native_decide) (by native_decide)
    (base := by rfl)

def optionalU128TagWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x10

private theorem encoderInlinePreserved_disjoint_optionalU128TagWrites :
    RegSet.Disjoint encoderInlinePreserved optionalU128TagWrites := by
  intro register preserved written
  simp [encoderInlinePreserved, optionalU128TagWrites, instructionPreserved,
    platformPreserved, stepBookkeeping] at preserved written
  grind

set_option genInjectivity false in
/-- The shared two-step prefix leaves one Boolean tag ready for its child call. -/
private structure OptionalU128TagReady (fromStep tag booleanPc : Nat)
    (args : OptionalEncoderArgs OptionalU128Words) (before ready : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges optionalU128ExecutionPcs)
    fromStep 2 before ready
  atPc : ready.machine.regs.get? PC = some (BitVec.ofNat 64 booleanPc)
  stack : ready.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer)
  tagReg : ready.machine.regs.get? x10 = some (BitVec.ofNat 64 tag)
  lowReg : ∀ value, args.value = some value →
    ready.machine.regs.get? x9 = some (BitVec.ofNat 64 value.low)
  highReg : ∀ value, args.value = some value →
    ready.machine.regs.get? x23 = some (BitVec.ofNat 64 value.high)
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully ready.machine.mem
  access : OptionalEncoderMachineAccess 32 0 0 args ready.machine
  stdout : ready.stdout = before.stdout
  stdin : ready.stdin = before.stdin
  stdinCursor : ready.stdinCursor = before.stdinCursor
  exitCode : ready.exitCode = before.exitCode
  memory : WritesOnlyWithin (optionalEncoderMemory 32 0 0 args.stackPointer)
    before.machine ready.machine
  frame : EncoderInlineFrame before ready

/-- Convert the shared two-step U128 `Seg` into the endpoint handoff used by both routes. -/
private theorem optionalU128TagReadyOfSeg
    (fromStep tag booleanPc : Nat) (args : OptionalEncoderArgs OptionalU128Words)
    (before : EndpointState) (access : OptionalEncoderMachineAccess 32 0 0 args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (lowReg : ∀ value, args.value = some value →
      afterMachine.regs.get? x9 = some (BitVec.ofNat 64 value.low))
    (highReg : ∀ value, args.value = some value →
      afterMachine.regs.get? x23 = some (BitVec.ofNat 64 value.high))
    (seg : Seg (fun pc => pcInRanges [(0x15118, 0x15148)] pc)
      (fun pc => pc = BitVec.ofNat 64 booleanPc)
      (fun _ _ _ _ _ => False) optionalU128TagWrites (fun _ => False)
      [⟨x10, BitVec.ofNat 64 tag⟩, ⟨x2, BitVec.ofNat 64 args.stackPointer⟩]
      fromStep 2 before.machine afterMachine (BitVec.ofNat 64 booleanPc)) :
    OptionalU128TagReady fromStep tag booleanPc args before
      { before with machine := afterMachine } := by
  have frame : EncoderInlineFrame before { before with machine := afterMachine } :=
    ⟨seg.agree encoderInlinePreserved_disjoint_optionalU128TagWrites, seg.retired,
      by simpa [seg.memEq (by simp)] using loaded, seg.aux⟩
  exact {
    trace := by
      have terminal : ScopedTrace (fun pc => pcInRanges [(0x15118, 0x15148)] pc)
          (fun pc => pc = BitVec.ofNat 64 booleanPc) (fun _ _ _ _ _ => False)
          (fromStep + 2) 0 afterMachine afterMachine :=
        .exitAt _ _ _ seg.atPc rfl
      have parentScoped := seg.confined 0 afterMachine terminal
      exact (liftOptionalParentTrace before (fun pc inside => by
        unfold pcInRanges at inside
        rcases inside with ⟨range, member, lower, upper⟩
        simp at member
        subst range
        simp [BareMetalHostTransitionPc, readContextReturnPc, writeContextReturnPc,
          exitContextStorePc]
        omega) parentScoped).weaken (fun pc inside => by
          unfold pcInRanges at inside ⊢
          rcases inside with ⟨range, member, lower, upper⟩
          simp at member
          subst range
          exact ⟨(0x15118, 0x15148), by simp [optionalU128ExecutionPcs], lower, upper⟩)
    atPc := seg.atPc
    stack := seg.reg x2 _ (by simp)
    tagReg := seg.reg x10 _ (by simp)
    lowReg
    highReg
    loaded := frame.2.2.1
    access := access.ofEncoderFrame before frame
    stdout := rfl
    stdin := rfl
    stdinCursor := rfl
    exitCode := rfl
    memory := by intro address outside; simpa [seg.memEq (by simp)]
    frame }

/-- Compose the common branch and Boolean tag for the present U128 route. -/
private theorem optionalU128PresentTagReady (fromStep : Nat)
    (args : OptionalEncoderArgs OptionalU128Words) (value : OptionalU128Words)
    (before : EndpointState) (atPc : before.machine.regs.get? PC = some 0x15118)
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer))
    (valueEq : args.value = some value)
    (presenceAt : before.machine.regs.get? x27 = some 1)
    (lowAt : before.machine.regs.get? x9 = some (BitVec.ofNat 64 value.low))
    (highAt : before.machine.regs.get? x23 = some (BitVec.ofNat 64 value.high))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (access : OptionalEncoderMachineAccess 32 0 0 args before.machine) :
    ∃ ready, OptionalU128TagReady fromStep 1 0x15120 args before ready := by
  have seg0 : Seg (fun pc => pcInRanges [(0x15118, 0x15148)] pc)
      (fun pc => pc = 0x15120) (fun _ _ _ _ _ => False) optionalU128TagWrites
      (fun _ => False)
      [⟨x2, BitVec.ofNat 64 args.stackPointer⟩, ⟨x9, BitVec.ofNat 64 value.low⟩,
        ⟨x23, BitVec.ofNat 64 value.high⟩]
      fromStep 0 before.machine before.machine 0x15118 := {
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
      rcases member with rfl | rfl | rfl
      · exact stack
      · exact lowAt
      · exact highAt }
  obtain ⟨machine1, seg1⟩ := seg0.stepFallThrough 0x1511c
    (by owned_pc [pcInRanges]) (by native_decide)
    (optionalU128PresenceBranchStep fromStep before.machine true access.output.configured atPc
      presenceAt loaded)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have configured1 := access.output.configured.mono
    (seg1.agree (fun register preserved written =>
      encoderInlinePreserved_disjoint_optionalU128TagWrites register (Or.inl preserved) written))
    seg1.retired
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨machine2, seg2⟩ := seg1.step (by owned_pc [pcInRanges]) (by native_decide)
    x10 1 0x15120
    (optionalU128TagStep (fromStep + 1) 0x1511c 1 machine1 configured1 seg1.atPc loaded1
      (valueCase := Or.inr rfl))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr rfl) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  refine ⟨{ before with machine := machine2 }, ?_⟩
  apply optionalU128TagReadyOfSeg fromStep 1 0x15120 args before access loaded
  · intro current currentEq
    rw [valueEq] at currentEq
    cases Option.some.inj currentEq
    exact (seg2.get x9 (by simp [optionalU128TagWrites])).trans lowAt
  · intro current currentEq
    rw [valueEq] at currentEq
    cases Option.some.inj currentEq
    exact (seg2.get x23 (by simp [optionalU128TagWrites])).trans highAt
  · exact seg2.forget (kv' :=
      [⟨x10, 1⟩, ⟨x2, BitVec.ofNat 64 args.stackPointer⟩]) (by simp)

/-- Compose the common branch and Boolean tag for the absent U128 route. -/
private theorem optionalU128AbsentTagReady (fromStep : Nat)
    (args : OptionalEncoderArgs OptionalU128Words) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x15118)
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer))
    (valueEq : args.value = none) (presenceAt : before.machine.regs.get? x27 = some 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (access : OptionalEncoderMachineAccess 32 0 0 args before.machine) :
    ∃ ready, OptionalU128TagReady fromStep 0 0x15140 args before ready := by
  have seg0 : Seg (fun pc => pcInRanges [(0x15118, 0x15148)] pc)
      (fun pc => pc = 0x15140) (fun _ _ _ _ _ => False) optionalU128TagWrites
      (fun _ => False) [⟨x2, BitVec.ofNat 64 args.stackPointer⟩]
      fromStep 0 before.machine before.machine 0x15118 := {
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
      cases member
      exact stack }
  obtain ⟨machine1, seg1⟩ := seg0.stepJump 0x1513c
    (by owned_pc [pcInRanges]) (by native_decide)
    (optionalU128PresenceBranchStep fromStep before.machine false access.output.configured atPc
      presenceAt loaded)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have configured1 := access.output.configured.mono
    (seg1.agree (fun register preserved written =>
      encoderInlinePreserved_disjoint_optionalU128TagWrites register (Or.inl preserved) written))
    seg1.retired
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨machine2, seg2⟩ := seg1.step (by owned_pc [pcInRanges]) (by native_decide)
    x10 0 0x15140
    (optionalU128TagStep (fromStep + 1) 0x1513c 0 machine1 configured1 seg1.atPc loaded1
      (valueCase := Or.inl rfl))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr rfl) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  refine ⟨{ before with machine := machine2 }, ?_⟩
  apply optionalU128TagReadyOfSeg fromStep 0 0x15140 args before access loaded
  · intro current currentEq
    rw [valueEq] at currentEq
    contradiction
  · intro current currentEq
    rw [valueEq] at currentEq
    contradiction
  · exact seg2

set_option genInjectivity false in
/-- Either U128 route after its shared Boolean child returns. -/
private structure OptionalU128BooleanHandoff (fromStep childUsed tag returnPc : Nat)
    (args : OptionalEncoderArgs OptionalU128Words) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges optionalU128ExecutionPcs)
    fromStep (4 + childUsed) before after
  childBound : childUsed ≤ 16
  atPc : after.machine.regs.get? PC = some (BitVec.ofNat 64 returnPc)
  stack : after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer)
  lowReg : ∀ value, args.value = some value →
    after.machine.regs.get? x9 = some (BitVec.ofNat 64 value.low)
  highReg : ∀ value, args.value = some value →
    after.machine.regs.get? x23 = some (BitVec.ofNat 64 value.high)
  stdout : after.stdout = before.stdout ++ #[if tag = 1 then 1 else 0]
  stdin : after.stdin = before.stdin
  stdinCursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : WritesOnlyWithin (optionalEncoderMemory 32 0 0 args.stackPointer)
    before.machine after.machine
  frame : EncoderInlineFrame before after
  access : OptionalEncoderMachineAccess 32 0 0 args after.machine

/-- Append the unconditional Boolean child to either typed U128 tag prefix. -/
private theorem optionalU128BooleanHandoff
    (site : OptionalBooleanCallSite booleanPc returnPc callBase optionalU128ExecutionPcs)
    (fromStep tag : Nat) (tagCase : tag = 0 ∨ tag = 1)
    (args : OptionalEncoderArgs OptionalU128Words) (before ready : EndpointState)
    (tagReady : OptionalU128TagReady fromStep tag booleanPc args before ready) :
    ∃ childUsed after,
      OptionalU128BooleanHandoff fromStep childUsed tag returnPc args before after := by
  obtain ⟨childUsed, after, childBound, call⟩ := optionalBooleanCallHandoff (fun _ => 16)
    writeSuccessBooleanContract_implements site (by omega) (fromStep + 2)
    args (tag = 1) ready tagReady.atPc tagReady.stack (by
      rcases tagCase with rfl | rfl <;> simpa using tagReady.tagReg)
    tagReady.access tagReady.loaded
  have trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges optionalU128ExecutionPcs)
      fromStep (4 + childUsed) before after := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tagReady.trace.append call.trace
  have frame : EncoderInlineFrame before after :=
    ⟨tagReady.frame.1.trans call.frame.1, call.frame.2.1, call.frame.2.2.1,
      call.frame.2.2.2.1.trans tagReady.frame.2.2.2.1,
      call.frame.2.2.2.2.1.trans tagReady.frame.2.2.2.2.1,
      call.frame.2.2.2.2.2.trans tagReady.frame.2.2.2.2.2⟩
  exact ⟨childUsed, after, {
    trace
    childBound
    atPc := call.atPc
    stack := call.stack
    lowReg := by
      intro value valueEq
      exact (call.frame.1 x9 (by simp [encoderInlinePreserved])).trans
        (tagReady.lowReg value valueEq)
    highReg := by
      intro value valueEq
      exact (call.frame.1 x23 (by simp [encoderInlinePreserved])).trans
        (tagReady.highReg value valueEq)
    stdout := by
      rcases tagCase with rfl | rfl <;> simpa [tagReady.stdout] using call.stdout
    stdin := call.stdin.trans tagReady.stdin
    stdinCursor := call.stdinCursor.trans tagReady.stdinCursor
    exitCode := call.exitCode.trans tagReady.exitCode
    memory := WritesOnlyWithin.trans_same tagReady.memory call.memory
    frame
    access := call.access }⟩

private theorem optionalU128MoveLowStep (stepNo : Nat) (state : State) (source : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15128)
    (sourceReg : state.regs.get? x9 = some source)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15128 retired x10 source) false := by
  have resultEq : source = iTypeResult .ADDI 0 source := by
    change source = source + sign_extend (m := 64) (0#12)
    rw [show sign_extend (m := 64) (0#12) = 0 by native_decide]
    simp
  exact configuredITypeX10Step stepNo 0x15128 state 0 (.Regidx 9#5) .ADDI source source
    0x13 0x85 0x04 0x00 configured atPc loaded resultEq
    (by
      intro premise writes
      exact rX_x9_run premise source ((writes.get x9 (by decide)).trans sourceReg))
    (by intro premise; rw [← resultEq]; exact wX_x10_run premise source)
    (by write_success_decode configured) (base := by rfl)

private theorem optionalU128MoveHighStep (stepNo : Nat) (state : State) (source : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x1512c)
    (sourceReg : state.regs.get? x23 = some source)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1512c retired x11 source) false := by
  have resultEq : source = iTypeResult .ADDI 0 source := by
    change source = source + sign_extend (m := 64) (0#12)
    rw [show sign_extend (m := 64) (0#12) = 0 by native_decide]
    simp
  exact configuredITypeX11Step stepNo 0x1512c state 0 (.Regidx 23#5) .ADDI source source
    0x93 0x85 0x0b 0x00 configured atPc loaded
    (by
      intro premise writes
      exact rX_x23_run premise source ((writes.get x23 (by decide)).trans sourceReg))
    (by intro premise; rw [← resultEq]; exact wX_x11_run premise source)
    (by write_success_decode configured) (base := by rfl)

private theorem optionalU128IntegerBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15130)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15130 retired x1 0x16130) false := by
  exact configuredRawWriteOutputCallBaseStep stepNo 0x15130 1 0x16130
    0x97 0x10 0x00 0x00 state configured atPc loaded (by native_decide) (by rfl)
    (by native_decide) (by write_success_decode configured)

private theorem optionalU128IntegerCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15134)
    (link : state.regs.get? x1 = some 0x16130)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x15134 0x15ce4 x1 0x15138)
        0x15ce4 retired) false := by
  exact configuredJalrCallStep stepNo state 0x15134 0x16130 0xbb4 0x15ce4 0x15138
    0xe7 0x80 0x40 0xbb configured atPc link loaded
    (base := by rfl) (decode := by write_success_decode configured)

private def optionalU128IntegerSite :
    OptionalIntegerCallSite 0x15128 0x15138 0x16130 optionalU128ExecutionPcs := {
  move0 := optionalU128MoveLowStep
  move1 := optionalU128MoveHighStep
  base := optionalU128IntegerBaseStep
  call := optionalU128IntegerCallStep
  owned := by intro offset member; simp at member; rcases member with rfl | rfl | rfl | rfl <;>
    owned_pc [pcInRanges, optionalU128ExecutionPcs]
  next0 := by native_decide
  next1 := by native_decide
  next2 := by native_decide
  notExit := by intro offset member; simp at member; rcases member with rfl | rfl | rfl | rfl <;>
    native_decide
  returnListed := by simp [integerEncoderU128ExitPcs]
  childInside := by
    intro childPc inside
    unfold pcInRanges at inside ⊢
    rcases inside with ⟨range, member, lower, upper⟩
    simp [integerEncoderU128ExecutionPcs] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨(0x10190, 0x101c4), by simp [optionalU128ExecutionPcs], lower, upper⟩
    all_goals
      exact ⟨(0x15ce4, 0x15d10), by simp [optionalU128ExecutionPcs], by omega, by omega⟩
  notHost := by intro offset member; simp at member; rcases member with rfl | rfl | rfl | rfl <;>
    simp [BareMetalHostTransitionPc, readContextReturnPc, writeContextReturnPc,
      exitContextStorePc] }

private def optionalU128Site : OptionalEncoderSite 0x15118 0x15148 32 0 0
    optionalU128ExecutionPcs optionalU128ExitPcs encodeOptionalU128Words OptionalU128Binding where
  stepBound := 41
  stepBoundFits := by simp [level2ContractFuel]
  run := by
    intro fromStep args before entry
    rcases entry with ⟨atPc, stack, binding, loaded, access⟩
    rcases binding with ⟨presenceAt, wordsAt⟩
    cases valueEq : args.value with
    | none =>
        have presenceZero : before.machine.regs.get? x27 = some 0 := by
          simpa [valueEq] using presenceAt
        obtain ⟨tagState, tagReady⟩ := optionalU128AbsentTagReady fromStep args before atPc
          stack valueEq presenceZero loaded access
        obtain ⟨booleanUsed, after, booleanHandoff⟩ := optionalU128BooleanHandoff
          optionalU128AbsentBooleanSite fromStep 0 (Or.inl rfl) args before tagState tagReady
        have booleanBound := booleanHandoff.childBound
        refine ⟨4 + booleanUsed, after, by omega, by omega, ?_⟩
        exact {
          trace := booleanHandoff.trace
          atPc := booleanHandoff.atPc
          stack := booleanHandoff.stack
          output := ⟨Or.inl ⟨valueEq, by simpa using booleanHandoff.stdout⟩⟩
          stdin := booleanHandoff.stdin
          stdinCursor := booleanHandoff.stdinCursor
          exitCode := booleanHandoff.exitCode
          memory := booleanHandoff.memory
          frame := booleanHandoff.frame }
    | some value =>
        have presenceOne : before.machine.regs.get? x27 = some 1 := by
          simpa [valueEq] using presenceAt
        obtain ⟨lowAt, highAt⟩ := wordsAt value valueEq
        obtain ⟨tagState, tagReady⟩ := optionalU128PresentTagReady fromStep args value before
          atPc stack valueEq presenceOne lowAt highAt loaded access
        obtain ⟨booleanUsed, booleanState, booleanHandoff⟩ := optionalU128BooleanHandoff
          optionalU128PresentBooleanSite fromStep 1 (Or.inr rfl) args before tagState tagReady
        obtain ⟨integerReadyState, integerReady⟩ := optionalIntegerCallReady
          optionalU128IntegerSite (fromStep + 4 + booleanUsed) args value.low value.high
          booleanState booleanHandoff.atPc booleanHandoff.stack
          (booleanHandoff.lowReg value valueEq) (booleanHandoff.highReg value valueEq)
          value.lowFits value.highFits booleanHandoff.access booleanHandoff.frame.2.2.1 (by omega)
        obtain ⟨integerUsed, integerState, integerBound, integerHandoff⟩ :=
          optionalIntegerChildHandoff 16 integerEncoderU128Contract_implements integerReady
            (by omega)
        obtain ⟨retired, jumpRun⟩ := optionalU128JoinJumpStep
          (fromStep + 4 + booleanUsed + 4 + integerUsed) integerState.machine
          integerHandoff.access.output.configured integerHandoff.atPc
          integerHandoff.frame.2.2.1
        let finalMachine := tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement integerState.machine)
            0x15138 0x15148) 0x15148 retired
        let after : EndpointState := { integerState with machine := finalMachine }
        have jumpTrace : ConfinedTrace EndpointStep EndpointPc
            (pcInRanges optionalU128ExecutionPcs)
            (fromStep + 4 + booleanUsed + 4 + integerUsed) 1 integerState after := by
          apply ConfinedTrace.step _ 0 0x15138 integerState after after
          · exact integerHandoff.atPc
          · owned_pc [pcInRanges, optionalU128ExecutionPcs]
          · exact endpointStep_sail _ integerState finalMachine (by
              intro observed observedPc
              change integerState.machine.regs.get? PC = some observed at observedPc
              rw [integerHandoff.atPc] at observedPc
              cases Option.some.inj observedPc
              simp [BareMetalHostTransitionPc, readContextReturnPc, writeContextReturnPc,
                exitContextStorePc]) jumpRun
          · exact .refl _ _
        have wholeTrace : ConfinedTrace EndpointStep EndpointPc
            (pcInRanges optionalU128ExecutionPcs) fromStep
            (9 + booleanUsed + integerUsed) before after := by
          have integerTrace : ConfinedTrace EndpointStep EndpointPc
              (pcInRanges optionalU128ExecutionPcs) (fromStep + (4 + booleanUsed))
              (4 + integerUsed) booleanState integerState := by
            simpa [Nat.add_assoc] using integerHandoff.trace
          have throughInteger := booleanHandoff.trace.append integerTrace
          have jumpTrace' : ConfinedTrace EndpointStep EndpointPc
              (pcInRanges optionalU128ExecutionPcs)
              (fromStep + (4 + booleanUsed + (4 + integerUsed))) 1 integerState after := by
            simpa [Nat.add_assoc] using jumpTrace
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            throughInteger.append jumpTrace'
        have jumpWrites := jumpRetirement_writes integerState.machine 0x15138 0x15148 retired
        have jumpFrame : EncoderInlineFrame integerState after := by
          refine ⟨?_, jumpRetirement_retired_present _ _ _ _, ?_, ⟨rfl, rfl, rfl⟩⟩
          · exact jumpWrites.agree (by
              intro register preserved written
              exact encoderInlinePreserved_disjoint_optionalU128TagWrites register preserved
                (Or.inl written))
          · simpa [after, finalMachine, jumpRetirement_mem] using integerHandoff.frame.2.2.1
        have frame : EncoderInlineFrame before after :=
          ⟨booleanHandoff.frame.1.trans
              (integerHandoff.frame.1.trans jumpFrame.1),
            jumpFrame.2.1, jumpFrame.2.2.1,
            jumpFrame.2.2.2.1.trans
              (integerHandoff.frame.2.2.2.1.trans booleanHandoff.frame.2.2.2.1),
            jumpFrame.2.2.2.2.1.trans
              (integerHandoff.frame.2.2.2.2.1.trans booleanHandoff.frame.2.2.2.2.1),
            jumpFrame.2.2.2.2.2.trans
              (integerHandoff.frame.2.2.2.2.2.trans booleanHandoff.frame.2.2.2.2.2)⟩
        have booleanBound := booleanHandoff.childBound
        refine ⟨9 + booleanUsed + integerUsed, after, by omega, by omega, ?_⟩
        exact {
          trace := wholeTrace
          atPc := by exact jumpRetirement_pc integerState.machine 0x15138 0x15148 retired
          stack := (jumpWrites.get x2 (by simp [stepBookkeeping])).trans integerHandoff.stack
          output := ⟨Or.inr ⟨value, valueEq, by
            rw [integerHandoff.stdout, booleanHandoff.stdout]
            simp [encodeOptionalU128Words, Array.append_assoc]⟩⟩
          stdin := integerHandoff.stdin.trans booleanHandoff.stdin
          stdinCursor := integerHandoff.stdinCursor.trans booleanHandoff.stdinCursor
          exitCode := integerHandoff.exitCode.trans booleanHandoff.exitCode
          memory := by
            simpa [after, finalMachine, jumpRetirement_mem] using
              WritesOnlyWithin.trans_same booleanHandoff.memory integerHandoff.memory
          frame }
  successListed := by simp [optionalU128ExitPcs]
  successFits := by native_decide

abbrev Proposed_ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b_Contract : Prop :=
  OptionalEncoderInstanceContract 0x15118 0x15148 32 0 0 optionalU128ExecutionPcs
    optionalU128ExitPcs encodeOptionalU128Words OptionalU128Binding

abbrev Proposed_ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94_Contract : Prop :=
  OptionalEncoderInstanceContract 0x15158 0x1519c 16 0x6d0 20 optionalAddressExecutionPcs
    optionalAddressExitPcs (fun value => value) OptionalAddressBinding

/-- `fi:1:3f5b` uses the shared optional route theorem and exact U128 site data. -/
theorem proposed_optionalU128_3f5b_proved :
    Proposed_ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b_Contract :=
  optionalEncoderInstanceContract_of_site (Value := OptionalU128Words)
    (encodePayload := encodeOptionalU128Words) optionalU128Site

end BinaryFv.Zesu.Staging
