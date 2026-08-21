import BinaryFv.Zesu.MachineExecution.HLevel3RawEncoderSteps
import BinaryFv.Zesu.DecodedValue.Encoder

/-!
# The fixed-width integer encoder hLevel3 boundary

The two standalone integer encoders have the same semantics. One encodes two 64-bit register
pieces. The other encodes four pieces. Their contracts differ only in word count, frame size,
and exact machine-code sites.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.Zesu
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

structure IntegerEncoderArgs where
  stackPointer : Nat
  returnPc : Nat
  word0 : Nat
  word1 : Nat
  word2 : Nat
  word3 : Nat
  stackFits : stackPointer < 2 ^ 64
  returnFits : returnPc < 2 ^ 64
  word0Fits : word0 < 2 ^ 64
  word1Fits : word1 < 2 ^ 64
  word2Fits : word2 < 2 ^ 64
  word3Fits : word3 < 2 ^ 64

def integerEncoderBytes (wordCount : Nat) (args : IntegerEncoderArgs) : Array UInt8 :=
  if wordCount = 2 then
    encodeNatLE 8 args.word0 ++ encodeNatLE 8 args.word1
  else
    encodeNatLE 8 args.word0 ++ encodeNatLE 8 args.word1 ++
      encodeNatLE 8 args.word2 ++ encodeNatLE 8 args.word3

def IntegerEncoderWordBindings (wordCount : Nat) (args : IntegerEncoderArgs)
    (state : EndpointState) : Prop :=
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.word0) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 args.word1) ∧
  (wordCount = 2 ∨
    (wordCount = 4 ∧
      state.machine.regs.get? x12 = some (BitVec.ofNat 64 args.word2) ∧
      state.machine.regs.get? x13 = some (BitVec.ofNat 64 args.word3)))

def integerEncoderFrame (frameBase frameSize : Nat) : Region :=
  byteRange frameBase frameSize

def integerEncoderMemory (frameBase frameSize : Nat) : Region :=
  Region.union (integerEncoderFrame frameBase frameSize) writeOutputMemory

structure IntegerEncoderMachineAccess (frameBase frameSize : Nat) (state : State) : Prop where
  output : EncoderOutputMachineAccess state
  frameFits : frameBase + frameSize ≤ 2 ^ 64
  frameAligned : frameBase % 16 = 0
  storePma : ∀ offset, offset + 8 ≤ frameSize → offset % 8 = 0 →
    StorePmaAllows state (BitVec.ofNat 64 (frameBase + offset)) 8
  storeNoMMIO : ∀ offset, offset + 8 ≤ frameSize → offset % 8 = 0 →
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (frameBase + offset)) 8
  loadPma : ∀ offset, offset + 8 ≤ frameSize → offset % 8 = 0 →
    LoadPmaAllows state (BitVec.ofNat 64 (frameBase + offset)) 8
  loadNoMMIO : ∀ offset, offset + 8 ≤ frameSize → offset % 8 = 0 →
    LoadMMIOAddressExcluded (BitVec.ofNat 64 (frameBase + offset)) 8
  codeDisjoint : ∀ offset, offset < frameSize →
    Artifacts.programImage.readFileByte? (frameBase + offset) = none
  outputDisjoint : ∀ offset, offset < frameSize → ¬writeOutputMemory (frameBase + offset)

def integerEncoderPreserved (register : Register) : Prop :=
  encoderInlinePreserved register ∨ register = x1

def IntegerEncoderEntry (entry frameSize wordCount : Nat) (args : IntegerEncoderArgs)
    (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnPc) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  IntegerEncoderWordBindings wordCount args state ∧
  frameSize ≤ args.stackPointer ∧
  IntegerEncoderMachineAccess (args.stackPointer - frameSize) frameSize state.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def IntegerEncoderExit (frameSize wordCount : Nat) (args : IntegerEncoderArgs)
    (_outcome : Unit) (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnPc) ∧
  after.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnPc) ∧
  after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  after.stdout = before.stdout ++ integerEncoderBytes wordCount args ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧
  WritesOnlyWithin
    (integerEncoderMemory (args.stackPointer - frameSize) frameSize)
    before.machine after.machine ∧
  Agree integerEncoderPreserved before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine

def integerEncoderContract (entry frameSize wordCount : Nat)
    (stepBound : IntegerEncoderArgs → Nat) :
    RelationalMachineContract EndpointState IntegerEncoderArgs Unit :=
  { allows := fun _ _ => True
    entry := IntegerEncoderEntry entry frameSize wordCount
    exit := IntegerEncoderExit frameSize wordCount
    stepBound }

def IntegerEncoderInstanceContract (entry frameSize wordCount : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat) : Prop :=
  ∃ stepBound : Nat,
    stepBound < level2ContractFuel ∧
    (integerEncoderContract entry frameSize wordCount (fun _ => stepBound)).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs)

set_option genInjectivity false in
/-- The shared boundary after an integer encoder writes its words and prepares `write_output`. -/
structure IntegerEncoderPreparedHandoff (executionPcs : List Elflings.PcRange)
    (outputEntry frameSize wordCount fromStep prefixCount : Nat)
    (args : IntegerEncoderArgs) (before prepared : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
    fromStep prefixCount before prepared
  atPc : prepared.machine.regs.get? PC = some (BitVec.ofNat 64 (outputEntry + 4))
  source : prepared.machine.regs.get? x10 =
    some (BitVec.ofNat 64 (args.stackPointer - frameSize))
  length : prepared.machine.regs.get? x11 = some (BitVec.ofNat 64 (8 * wordCount))
  bytes : BytesRep prepared.machine.mem (args.stackPointer - frameSize)
    (integerEncoderBytes wordCount args)
  bytesSize : (integerEncoderBytes wordCount args).size = 8 * wordCount
  outsideOutput : ∀ index, index < (integerEncoderBytes wordCount args).size →
    ¬writeOutputMemory (args.stackPointer - frameSize + index)
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully prepared.machine.mem
  access : EncoderOutputMachineAccess prepared.machine

/-- Exact site data for one width of the shared fixed-width integer encoder. -/
structure IntegerEncoderSite (entry frameSize wordCount outputEntry callReturn prefixCount
    suffixCount : Nat) (executionPcs : List Elflings.PcRange) (exitPcs : List Nat) where
  totalCount : prefixCount + 7 + suffixCount < level2ContractFuel
  output : RawWriteOutputPreparedSite outputEntry (8 * wordCount) callReturn
    executionPcs [callReturn]
  prepare : ∀ fromStep args before,
    IntegerEncoderEntry entry frameSize wordCount args before →
      ∃ prepared, IntegerEncoderPreparedHandoff executionPcs outputEntry frameSize wordCount
        fromStep prefixCount args before prepared
  finish : ∀ fromStep args before prepared outputState,
    IntegerEncoderPreparedHandoff executionPcs outputEntry frameSize wordCount
      fromStep prefixCount args before prepared →
    RawEncoderExit callReturn
      { sourceAddress := args.stackPointer - frameSize
        bytes := integerEncoderBytes wordCount args }
      () prepared outputState →
    ∃ after,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
        (fromStep + prefixCount + 7) suffixCount outputState after ∧
      (∃ pc, EndpointPc after = some pc ∧ pcInList exitPcs pc) ∧
      IntegerEncoderExit frameSize wordCount args () before after

/-- Prove every compatible integer encoder from one prepare/output/finish composition. -/
theorem integerEncoderInstanceContract_of_site
    (site : IntegerEncoderSite entry frameSize wordCount outputEntry callReturn
      prefixCount suffixCount executionPcs exitPcs) :
    IntegerEncoderInstanceContract entry frameSize wordCount executionPcs exitPcs := by
  refine ⟨prefixCount + 7 + suffixCount, site.totalCount, ?_⟩
  intro args fromStep before entryPre
  obtain ⟨prepared, preparedHandoff⟩ := site.prepare fromStep args before entryPre
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := args.stackPointer - frameSize
      bytes := integerEncoderBytes wordCount args }
  obtain ⟨outputState, outputTrace, outputExit⟩ := rawWriteOutputPreparedHandoff
    site.output (fromStep + prefixCount) rawArgs prepared preparedHandoff.atPc
      preparedHandoff.source preparedHandoff.length preparedHandoff.bytesSize
      preparedHandoff.bytes preparedHandoff.outsideOutput preparedHandoff.loaded
      preparedHandoff.access
  obtain ⟨after, suffixTrace, exitAt, exitState⟩ :=
    site.finish fromStep args before prepared outputState preparedHandoff outputExit
  have prefixOutput : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep (prefixCount + 7) before outputState := by
    simpa [Nat.add_assoc] using preparedHandoff.trace.append outputTrace
  have wholeTrace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep (prefixCount + 7 + suffixCount) before after := by
    simpa [Nat.add_assoc] using prefixOutput.append suffixTrace
  refine ⟨prefixCount + 7 + suffixCount, after, (), by omega, Nat.le_refl _, wholeTrace,
    exitAt, trivial, exitState⟩

end BinaryFv.Zesu.Staging
