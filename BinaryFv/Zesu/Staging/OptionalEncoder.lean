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
open BinaryFv.Zesu
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

abbrev Proposed_ssz_decode_observation_Encoder_optionalU128_fi_1_3f5b_Contract : Prop :=
  OptionalEncoderInstanceContract 0x15118 0x15148 32 0 0 optionalU128ExecutionPcs
    optionalU128ExitPcs encodeOptionalU128Words OptionalU128Binding

abbrev Proposed_ssz_decode_observation_Encoder_optionalAddress_fi_1_3f94_Contract : Prop :=
  OptionalEncoderInstanceContract 0x15158 0x1519c 16 0x6d0 20 optionalAddressExecutionPcs
    optionalAddressExitPcs (fun value => value) OptionalAddressBinding

end BinaryFv.Zesu.Staging
