import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level1Contracts
import BinaryFv.Zesu.Elflings.GeneratedLevel2
import BinaryFv.Zesu.DecodedValue.Encoder
import BinaryFv.RiscV.Step.ConfiguredMachine
import BinaryFv.RiscV.Platform.PhysicalAccess
import BinaryFv.RiscV.Platform.FetchMmio

/-!
# Level 2 contracts for the SSZ endpoint

The fixed raw encoders all implement the same reviewed operation: append a source byte window to
stdout while changing only the two bare-metal output-context words. Exact entry, execution, and
exit sets come from the pinned ELF. The source pointer is `x10` at the eight decoded-field callsites;
the two format-prefix callsites append source constants and therefore need no caller-provided
pointer.
-/

namespace BinaryFv.Zesu

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.RiscV

/-! ## Inlined `ssz.decode` boundary

The generated Level 2 instance starts at `0x121ac`, after `decodeInput` has saved its frame and
bound the result, allocator, and input arguments. Its error path leaves the inline instance at
`0x14ca8`; two parent-owned instructions copy the error value to `s6` and jump to the generated
re-entry at `0x1230c`. Keeping the initial and resumed runs separate makes those two instructions an
obligation of `level1Contracts_of_level2`, rather than silently absorbing them into `hLevel2`.
-/

structure DecodeInlineArgs where
  boundary : DecodeBoundaryArgs
  origin : EndpointState

def DecodeCalleeSavedAtStack (stackPointer returnAddress : Nat) (values : DecodeCalleeSavedValues)
    (state : EndpointState) : Prop :=
  UIntRep 8 state.machine.mem (stackPointer + 0xba8) returnAddress ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xba0) values.s0.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb98) values.s1.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb90) values.s2.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb88) values.s3.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb80) values.s4.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb78) values.s5.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb70) values.s6.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb68) values.s7.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb60) values.s8.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb58) values.s9.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb50) values.s10.toNat ∧
  UIntRep 8 state.machine.mem (stackPointer + 0xb48) values.s11.toNat

set_option genInjectivity false in
structure DecodeInlineFrame (args : DecodeInlineArgs) (values : DecodeCalleeSavedValues)
    (state : EndpointState) : Prop where
  stackFits : 0xbb0 ≤ args.boundary.stackPointer
  atStack : state.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0))
  saved : DecodeCalleeSavedAtStack (args.boundary.stackPointer - 0xbb0)
    args.boundary.returnAddress values state
  inputAddress : UIntRep 8 state.machine.mem args.boundary.stackPointer args.boundary.inputAddress
  inputSize : UIntRep 8 state.machine.mem (args.boundary.stackPointer + 8)
    args.boundary.input.size
  savedReturn : UIntRep 8 state.machine.mem (args.boundary.stackPointer + 0x378)
    args.boundary.savedReturnAddress
  input : BytesRep state.machine.mem args.boundary.inputAddress args.boundary.input
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem
  configured : ConfiguredMachinePre EndpointMachinePc state.machine
  stdin : state.stdin = args.origin.stdin
  stdinCursor : state.stdinCursor = args.origin.stdinCursor
  stdout : state.stdout = args.origin.stdout
  exitCode : state.exitCode = args.origin.exitCode

def DecodeInlineInitialEntry (args : DecodeInlineArgs) (state : EndpointState) : Prop :=
  DecodeBoundaryEntry args.boundary args.origin ∧
  ∃ values : DecodeCalleeSavedValues,
    DecodeCalleeSavedAtRegisters values args.origin ∧
    DecodeInlineFrame args values state ∧
    state.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.sszDecodeEntry) ∧
    state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.boundary.returnAddress) ∧
    state.machine.regs.get? x10 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)) ∧
    state.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)) ∧
    state.machine.regs.get? x12 = some (BitVec.ofNat 64 args.boundary.inputAddress) ∧
    state.machine.regs.get? x13 = some (BitVec.ofNat 64 args.boundary.input.size)

inductive DecodeInlineInitialOutcome where
  | final (outcome : DecodeBoundaryOutcome)
  | resume (status : BitVec 64)

def DecodeInlineInitialMeaning (args : DecodeInlineArgs) : DecodeInlineInitialOutcome → Prop
  | .final outcome => DecodeMeaningModuloKnownBugs args.boundary outcome
  | .resume status => status ≠ 0 ∧ DecodeMeaningModuloKnownBugs args.boundary .failure

def DecodeInlineInitialExit (args : DecodeInlineArgs) (outcome : DecodeInlineInitialOutcome)
    (_before after : EndpointState) : Prop :=
  match outcome with
  | .final result => DecodeBoundaryExit args.boundary result args.origin after
  | .resume status =>
      ∃ values, DecodeCalleeSavedAtRegisters values args.origin ∧
        DecodeInlineFrame args values after ∧
        after.machine.regs.get? PC = some (BitVec.ofNat 64 0x14ca8) ∧
        after.machine.regs.get? x10 = some status

def decodeInlineInitialContract (stepBound : DecodeInlineArgs → Nat) :
    RelationalMachineContract EndpointState DecodeInlineArgs DecodeInlineInitialOutcome :=
  { allows := DecodeInlineInitialMeaning
    entry := DecodeInlineInitialEntry
    exit := DecodeInlineInitialExit
    stepBound }

structure DecodeInlineResumeArgs where
  inline : DecodeInlineArgs
  saved : DecodeCalleeSavedValues
  status : BitVec 64

def DecodeInlineResumeEntry (args : DecodeInlineResumeArgs) (state : EndpointState) : Prop :=
  DecodeCalleeSavedAtRegisters args.saved args.inline.origin ∧
  DecodeInlineFrame args.inline args.saved state ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 0x1230c) ∧
  state.machine.regs.get? x22 = some args.status

def decodeInlineResumeContract (stepBound : DecodeInlineResumeArgs → Nat) :
    RelationalMachineContract EndpointState DecodeInlineResumeArgs Unit :=
  { allows := fun args _ =>
      args.status ≠ 0 ∧ DecodeMeaningModuloKnownBugs args.inline.boundary .failure
    entry := DecodeInlineResumeEntry
    exit := fun args _ _ after =>
      DecodeBoundaryExit args.inline.boundary .failure args.inline.origin after
    stepBound }

def DecodeInlineInitialExecutionPc (pc : BitVec 64) : Prop :=
  pcInRanges Elflings.sszDecodeExecutionPcRanges pc

def DecodeInlineInitialExitPc (pc : BitVec 64) : Prop :=
  pcInList Elflings.sszDecodeExitPcs pc

def DecodeInlineResumeExitPc (pc : BitVec 64) : Prop := pc.toNat = 0x14cfc

/-- The exact generated Level 2 decoder instance. The second implementation obligation is the
continuation reached only after `level1Contracts_of_level2` retires the two parent-owned error-path
instructions at `0x14ca8` and `0x14cac`. -/
structure SszDecodeLevel2InstanceContract : Prop where
  initial : ∃ initialBound : Nat → Nat,
    (decodeInlineInitialContract (fun args => initialBound args.boundary.input.size)).Implements
      EndpointStep EndpointPc DecodeInlineInitialExecutionPc DecodeInlineInitialExitPc
  resume : ∃ resumeBound : Nat → Nat,
    (decodeInlineResumeContract (fun args => resumeBound args.inline.boundary.input.size)).Implements
      EndpointStep EndpointPc DecodeInlineInitialExecutionPc DecodeInlineResumeExitPc

structure RawEncoderArgs where
  sourceAddress : Nat
  bytes : Array UInt8

set_option genInjectivity false in
/-- Shared bare-metal output permissions required by every observation encoder. -/
structure EncoderOutputMachineAccess (state : MachineState) : Prop where
  configured : ConfiguredMachinePre EndpointMachinePc state
  outputBufferStore :
    StorePmaAllows state (BitVec.ofNat 64 (Elflings.ioContextAddress + 8)) 8
  outputLengthStore :
    StorePmaAllows state (BitVec.ofNat 64 (Elflings.ioContextAddress + 16)) 8
  outputBufferNoMMIO :
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (Elflings.ioContextAddress + 8)) 8
  outputLengthNoMMIO :
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (Elflings.ioContextAddress + 16)) 8

namespace EncoderOutputMachineAccess

/-- Regression: no encoder entry may hide a missing configured-machine premise. -/
theorem rejects_missing_configuration
    (missing : ¬ConfiguredMachinePre EndpointMachinePc state) :
    ¬EncoderOutputMachineAccess state := by
  intro access
  exact missing access.configured

/-- Regression: no encoder entry may hide denied access to the output-buffer word. -/
theorem rejects_denied_output_store
    (denied : ¬StorePmaAllows state (BitVec.ofNat 64 (Elflings.ioContextAddress + 8)) 8) :
    ¬EncoderOutputMachineAccess state := by
  intro access
  exact denied access.outputBufferStore

end EncoderOutputMachineAccess

/-- The exact two-word memory region written by the bare-metal `write_output` implementation. -/
def writeOutputMemory : Region :=
  Region.union (byteRange (Elflings.ioContextAddress + 8) 8)
    (byteRange (Elflings.ioContextAddress + 16) 8)

def RawEncoderEntry (entry : Nat) (args : RawEncoderArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.sourceAddress) ∧
  BytesRep state.machine.mem args.sourceAddress args.bytes ∧
  (∀ index, index < args.bytes.size → ¬writeOutputMemory (args.sourceAddress + index)) ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  EncoderOutputMachineAccess state.machine

def RawEncoderExit (successPc : Nat) (args : RawEncoderArgs) (_outcome : Unit)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 successPc) ∧
  after.stdout = before.stdout ++ args.bytes ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧
  WritesOnlyWithin writeOutputMemory before.machine after.machine ∧
  EndpointCallFrame before after

def rawEncoderContract (entry successPc : Nat)
    (stepBound : RawEncoderArgs → Nat) :
    RelationalMachineContract EndpointState RawEncoderArgs Unit :=
  { allows := fun _ _ => True
    entry := RawEncoderEntry entry
    exit := RawEncoderExit successPc
    stepBound }

def RawEncoderInstanceContract (entry : Nat) (executionPcs : List Elflings.PcRange)
    (exitPcs : List Nat) (successPc : Nat) : Prop :=
  ∃ stepBound : Nat → Nat,
    (rawEncoderContract entry successPc (fun args => stepBound args.bytes.size)).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs)

namespace RawEncoderInstanceContract

noncomputable def stepBound {entry : Nat} {executionPcs : List Elflings.PcRange}
    {exitPcs : List Nat} {successPc : Nat}
    (contract : RawEncoderInstanceContract entry executionPcs exitPcs successPc) : Nat → Nat :=
  Classical.choose contract

theorem implements {entry : Nat} {executionPcs : List Elflings.PcRange}
    {exitPcs : List Nat} {successPc : Nat}
    (contract : RawEncoderInstanceContract entry executionPcs exitPcs successPc) :
    (rawEncoderContract entry successPc
      (fun args => contract.stepBound args.bytes.size)).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs) :=
  Classical.choose_spec contract

end RawEncoderInstanceContract

def ConstantEncoderEntry (entry : Nat) (_args : Unit) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  EncoderOutputMachineAccess state.machine

def ConstantEncoderExit (successPc : Nat) (bytes : Array UInt8) (_args _outcome : Unit)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 successPc) ∧
  after.stdout = before.stdout ++ bytes ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧
  WritesOnlyWithin writeOutputMemory before.machine after.machine ∧
  EndpointCallFrame before after

def constantEncoderContract (entry successPc : Nat) (bytes : Array UInt8)
    (stepBound : Nat) : RelationalMachineContract EndpointState Unit Unit :=
  { allows := fun _ _ => True
    entry := ConstantEncoderEntry entry
    exit := ConstantEncoderExit successPc bytes
    stepBound := fun _ => stepBound }

def ConstantEncoderInstanceContract (entry : Nat) (executionPcs : List Elflings.PcRange)
    (exitPcs : List Nat) (successPc : Nat) (bytes : Array UInt8) : Prop :=
  ∃ stepBound : Nat,
    (constantEncoderContract entry successPc bytes stepBound).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs)

namespace ConstantEncoderInstanceContract

noncomputable def stepBound {entry : Nat} {executionPcs : List Elflings.PcRange}
    {exitPcs : List Nat} {successPc : Nat} {bytes : Array UInt8}
    (contract : ConstantEncoderInstanceContract entry executionPcs exitPcs successPc bytes) : Nat :=
  Classical.choose contract

theorem implements {entry : Nat} {executionPcs : List Elflings.PcRange}
    {exitPcs : List Nat} {successPc : Nat} {bytes : Array UInt8}
    (contract : ConstantEncoderInstanceContract entry executionPcs exitPcs successPc bytes) :
    (constantEncoderContract entry successPc bytes contract.stepBound).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs) :=
  Classical.choose_spec contract

end ConstantEncoderInstanceContract

def successPrefixBytes : Array UInt8 := #[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x01]
def failureRecordBytes : Array UInt8 := #[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x00]

abbrev WriteSuccessPrefixInstanceContract : Prop :=
  ConstantEncoderInstanceContract Elflings.writeSuccessRawLine131Entry
    Elflings.writeSuccessRawLine131ExecutionPcRanges
    Elflings.writeSuccessRawLine131ExitPcs 0x14e14 successPrefixBytes

abbrev WriteFailureRecordInstanceContract : Prop :=
  ConstantEncoderInstanceContract Elflings.writeFailureRawLine127Entry
    Elflings.writeFailureRawLine127ExecutionPcRanges
    Elflings.writeFailureRawLine127ExitPcs 0x14d24 failureRecordBytes

abbrev WriteSuccessParentHashInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine135Entry
    Elflings.writeSuccessRawLine135ExecutionPcRanges Elflings.writeSuccessRawLine135ExitPcs 0x14e38

abbrev WriteSuccessFeeRecipientInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine136Entry
    Elflings.writeSuccessRawLine136ExecutionPcRanges Elflings.writeSuccessRawLine136ExitPcs 0x14e48

abbrev WriteSuccessStateRootInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine137Entry
    Elflings.writeSuccessRawLine137ExecutionPcRanges Elflings.writeSuccessRawLine137ExitPcs 0x14e58

abbrev WriteSuccessReceiptsRootInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine138Entry
    Elflings.writeSuccessRawLine138ExecutionPcRanges Elflings.writeSuccessRawLine138ExitPcs 0x14e68

abbrev WriteSuccessLogsBloomInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine139Entry
    Elflings.writeSuccessRawLine139ExecutionPcRanges Elflings.writeSuccessRawLine139ExitPcs 0x14e78

abbrev WriteSuccessPrevRandaoInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine140Entry
    Elflings.writeSuccessRawLine140ExecutionPcRanges Elflings.writeSuccessRawLine140ExitPcs 0x14e88

abbrev WriteSuccessBlockHashInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine147Entry
    Elflings.writeSuccessRawLine147ExecutionPcRanges Elflings.writeSuccessRawLine147ExitPcs 0x14ee4

abbrev WriteSuccessParentBeaconRootInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine156Entry
    Elflings.writeSuccessRawLine156ExecutionPcRanges Elflings.writeSuccessRawLine156ExitPcs 0x1573c

structure EncoderCallArgs (Value : Type) where
  returnAddress : Nat
  callerStack : Nat
  inputSize : Nat
  value : Value

set_option genInjectivity false in
/-- Machine permissions for one genuine called encoder's local stack frame and output leaf. -/
structure EncoderCallMachineAccess (frameSize : Nat) (args : EncoderCallArgs Value)
    (state : MachineState) : Prop where
  output : EncoderOutputMachineAccess state
  frameLoad : ∀ offset width, offset + width ≤ frameSize →
    LoadPmaAllows state (BitVec.ofNat 64 (args.callerStack - frameSize + offset)) width
  frameStore : ∀ offset width, offset + width ≤ frameSize →
    StorePmaAllows state (BitVec.ofNat 64 (args.callerStack - frameSize + offset)) width
  frameLoadNoMMIO : ∀ offset width, offset + width ≤ frameSize →
    LoadMMIOAddressExcluded (BitVec.ofNat 64 (args.callerStack - frameSize + offset)) width
  frameStoreNoMMIO : ∀ offset width, offset + width ≤ frameSize →
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (args.callerStack - frameSize + offset)) width
  frameNotCode : ∀ address, args.callerStack - frameSize ≤ address →
    address < args.callerStack → Artifacts.programImage.readFileByte? address = none

def EncoderCallEntry (entry : Nat) (exitPcs : List Nat) (frameSize : Nat)
    (bindValue : EndpointState → Value → Prop) (args : EncoderCallArgs Value)
    (state : EndpointState) : Prop :=
  args.returnAddress ∈ exitPcs ∧ frameSize ≤ args.callerStack ∧ args.callerStack < 2 ^ 64 ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.callerStack) ∧
  bindValue state args.value ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  EncoderCallMachineAccess frameSize args state.machine

theorem encoderCallEntry_rejects_small_stack
    (small : args.callerStack < frameSize) :
    ¬EncoderCallEntry entry exitPcs frameSize bindValue args state := by
  intro accepted
  exact (Nat.not_le_of_gt small) accepted.2.1

def EncoderCallExit (frameSize : Nat)
    (encode : Value → Array UInt8) (args : EncoderCallArgs Value) (_outcome : Unit)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) ∧
  after.stdout = before.stdout ++ encode args.value ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧
  frameSize ≤ args.callerStack ∧
  BinaryFv.RiscV.WritesOnlyWithin
    (BinaryFv.RiscV.byteRange (args.callerStack - frameSize) frameSize)
    before.machine after.machine ∧
  EndpointCallFrame before after

def encoderCallContract (entry : Nat) (exitPcs : List Nat) (frameSize : Nat)
    (encode : Value → Array UInt8) (bindValue : EndpointState → Value → Prop)
    (stepBound : Nat → Nat) : RelationalMachineContract EndpointState (EncoderCallArgs Value) Unit :=
  { allows := fun _ _ => True
    entry := EncoderCallEntry entry exitPcs frameSize bindValue
    exit := EncoderCallExit frameSize encode
    stepBound := fun args => stepBound args.inputSize }

def EncoderCallInstanceContract (entry : Nat) (executionPcs : List Elflings.PcRange)
    (exitPcs : List Nat) (frameSize : Nat) (encode : Value → Array UInt8)
    (bindValue : EndpointState → Value → Prop) : Prop :=
  ∃ stepBound : Nat → Nat,
    (encoderCallContract entry exitPcs frameSize encode bindValue stepBound).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs)

namespace EncoderCallInstanceContract

noncomputable def stepBound {Value : Type} {entry : Nat}
    {executionPcs : List Elflings.PcRange} {exitPcs : List Nat} {frameSize : Nat}
    {encode : Value → Array UInt8} {bindValue : EndpointState → Value → Prop}
    (contract : EncoderCallInstanceContract entry executionPcs exitPcs frameSize encode bindValue) :
    Nat → Nat :=
  Classical.choose contract

theorem implements {Value : Type} {entry : Nat}
    {executionPcs : List Elflings.PcRange} {exitPcs : List Nat} {frameSize : Nat}
    {encode : Value → Array UInt8} {bindValue : EndpointState → Value → Prop}
    (contract : EncoderCallInstanceContract entry executionPcs exitPcs frameSize encode bindValue) :
    (encoderCallContract entry exitPcs frameSize encode bindValue contract.stepBound).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs) :=
  Classical.choose_spec contract

end EncoderCallInstanceContract

def BooleanEncoderBinding (state : EndpointState) (value : Bool) : Prop :=
  state.machine.regs.get? x10 = some (if value then 1 else 0)

structure BytesEncoderValue where
  address : Nat
  bytes : Array UInt8

def BytesEncoderBinding (state : EndpointState) (value : BytesEncoderValue) : Prop :=
  value.address + value.bytes.size ≤ 2 ^ 64 ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 value.address) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 value.bytes.size) ∧
  BytesRep state.machine.mem value.address value.bytes

def UInt64EncoderBinding (state : EndpointState) (value : Nat) : Prop :=
  value < 2 ^ 64 ∧ state.machine.regs.get? x10 = some (BitVec.ofNat 64 value)

structure ByteListsEncoderValue where
  address : Nat
  values : Array (Array UInt8)

def ByteListsEncoderBinding (state : EndpointState) (value : ByteListsEncoderValue) : Prop :=
  value.address + value.values.size * 16 ≤ 2 ^ 64 ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 value.address) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 value.values.size) ∧
  ArrayRep 16 ByteSliceRep state.machine.mem value.address value.values

structure OptionalUInt64EncoderValue where
  address : Nat
  value : Option Nat

def OptionalUInt64EncoderBinding (state : EndpointState)
    (value : OptionalUInt64EncoderValue) : Prop :=
  value.address + 9 ≤ 2 ^ 64 ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 value.address) ∧
  OptionalUIntRep 8 state.machine.mem value.address value.value

abbrev WriteSuccessBooleanInstanceContract : Prop :=
  EncoderCallInstanceContract Elflings.writeSuccessBooleanEntry
    Elflings.writeSuccessBooleanExecutionPcRanges Elflings.writeSuccessBooleanExitPcs 16
    (fun value => #[if value then 1 else 0]) BooleanEncoderBinding

abbrev WriteSuccessOptionalU64InstanceContract : Prop :=
  EncoderCallInstanceContract Elflings.writeSuccessOptionalU64Entry
    Elflings.writeSuccessOptionalU64ExecutionPcRanges Elflings.writeSuccessOptionalU64ExitPcs 16
    (fun value => encodeOptional (encodeNatLE 8) value.value) OptionalUInt64EncoderBinding

abbrev WriteSuccessByteListsInstanceContract : Prop :=
  EncoderCallInstanceContract Elflings.writeSuccessByteListsEntry
    Elflings.writeSuccessByteListsExecutionPcRanges Elflings.writeSuccessByteListsExitPcs 64
    (fun value => encodeMany encodeBytes value.values) ByteListsEncoderBinding

abbrev WriteSuccessBytesInstanceContract : Prop :=
  EncoderCallInstanceContract Elflings.writeSuccessBytesEntry
    Elflings.writeSuccessBytesExecutionPcRanges Elflings.writeSuccessBytesExitPcs 48
    (fun value => encodeBytes value.bytes) BytesEncoderBinding

abbrev WriteSuccessIntInstanceContract : Prop :=
  EncoderCallInstanceContract Elflings.writeSuccessIntEntry
    Elflings.writeSuccessIntExecutionPcRanges Elflings.writeSuccessIntExitPcs 16
    (encodeNatLE 8) UInt64EncoderBinding

structure MemcpyArgs where
  returnAddress : Nat
  destination : Nat
  source : Nat
  bytes : Array UInt8

/-- Actual machine permissions needed by every byte-copy iteration. These are caller-derived facts
about the concrete source and destination windows, not a semantic oracle or a Level 2 assumption. -/
structure MemcpyMachineAccess (args : MemcpyArgs) (state : EndpointState) : Prop where
  configured : ConfiguredMachinePre EndpointMachinePc state.machine
  sourcePma : ∀ index, index < args.bytes.size →
    LoadPmaAllows state.machine (BitVec.ofNat 64 (args.source + index)) 1
  destinationPma : ∀ index, index < args.bytes.size →
    StorePmaAllows state.machine (BitVec.ofNat 64 (args.destination + index)) 1
  sourceNotMMIO : ∀ index, index < args.bytes.size →
    LoadMMIOAddressExcluded (BitVec.ofNat 64 (args.source + index)) 1
  destinationNotMMIO : ∀ index, index < args.bytes.size →
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (args.destination + index)) 1
  destinationNotCode : ∀ index, index < args.bytes.size →
    Artifacts.programImage.readFileByte? (args.destination + index) = none

def MemcpyEntry (args : MemcpyArgs) (state : EndpointState) : Prop :=
  args.returnAddress ∈ Elflings.memcpyExitPcs ∧
  args.bytes.size < 2 ^ 64 ∧
  args.destination + args.bytes.size ≤ 2 ^ 64 ∧
  args.source + args.bytes.size ≤ 2 ^ 64 ∧
  (args.destination + args.bytes.size ≤ args.source ∨
    args.source + args.bytes.size ≤ args.destination) ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.memcpyEntry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.destination) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 args.source) ∧
  state.machine.regs.get? x12 = some (BitVec.ofNat 64 args.bytes.size) ∧
  BytesRep state.machine.mem args.source args.bytes ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  MemcpyMachineAccess args state

def MemcpyExit (args : MemcpyArgs) (_outcome : Unit)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode ∧
  BytesRep after.machine.mem args.destination args.bytes ∧
  BytesRep after.machine.mem args.source args.bytes ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  BinaryFv.RiscV.WritesOnlyWithin
    (BinaryFv.RiscV.byteRange args.destination args.bytes.size) before.machine after.machine ∧
  EndpointCallFrame before after

def memcpyContract (stepBound : Nat → Nat) :
    RelationalMachineContract EndpointState MemcpyArgs Unit :=
  { allows := fun _ _ => True
    entry := MemcpyEntry
    exit := MemcpyExit
    stepBound := fun args => stepBound args.bytes.size }

def MemcpyInstanceContract : Prop :=
  ∃ stepBound : Nat → Nat,
    (memcpyContract stepBound).Implements EndpointStep EndpointPc
      (pcInRanges Elflings.memcpyExecutionPcRanges) (pcInList Elflings.memcpyExitPcs)

namespace MemcpyInstanceContract

noncomputable def stepBound (contract : MemcpyInstanceContract) : Nat → Nat :=
  Classical.choose contract

theorem implements (contract : MemcpyInstanceContract) :
    (memcpyContract contract.stepBound).Implements EndpointStep EndpointPc
      (pcInRanges Elflings.memcpyExecutionPcRanges) (pcInList Elflings.memcpyExitPcs) :=
  Classical.choose_spec contract

end MemcpyInstanceContract

/-- Registers that remain stable across an optimized encoder region inside `writeSuccess`. This is
not an ABI set: the optimizer may use every integer register except the live stack pointer, while
the Sail platform registers remain unchanged. -/
def inlineEncoderPreserved : Register → Prop := fun register =>
  register = x2 ∨ register = hart_state ∨ register = cur_privilege ∨ register = satp ∨
    register = mideleg ∨ register = mie ∨ register = mip ∨ register = pmpcfg_n ∨
    register = pmpaddr_n ∨ register = mcountinhibit ∨ register = minstretcfg ∨
    register = elp ∨ register = misa ∨ register = mstatus ∨ register = sig_meip ∨
    register = pma_regions ∨ register = mseccfg ∨ register = htif_tohost_base

structure InlineEncoderArgs (Value : Type) where
  stackPointer : Nat
  inputSize : Nat
  value : Value
  savedWords : List (Nat × Nat)
  decodedAddress : Nat
  copiedParentRootAddress : Nat
  copiedVersionedHashesAddress : Nat
  copiedPayloadAddress : Nat
  copiedSourceAddress : Nat
  copiedParentRootBytes : Array UInt8
  copiedPayloadBytes : Array UInt8
  copiedSourceBytes : Array UInt8
  decoded : ZesuDecodedResult

def InlineEncoderSavedWords (mem : Std.ExtHashMap Nat (BitVec 8))
    (words : List (Nat × Nat)) : Prop :=
  ∀ word ∈ words, UIntRep 8 mem word.1 word.2

/-- Exact optimized-inline write window. The parent uses `sp..sp+0x740`; its shared called
encoders use at most 0xb0 bytes below `sp`. The writer's ABI save area begins at `sp+0x768`. -/
def inlineEncoderMemoryRegion (stackPointer : Nat) : BinaryFv.RiscV.Region :=
  BinaryFv.RiscV.byteRange (stackPointer - 0xb0) 0x7f0

set_option genInjectivity false in
/-- Machine permissions for the complete optimized inline encoder region and its output leaf. -/
structure InlineEncoderMachineAccess (args : InlineEncoderArgs Value) (state : MachineState) : Prop where
  output : EncoderOutputMachineAccess state
  localLoad : ∀ offset width, offset + width ≤ 0xb0 →
    LoadPmaAllows state (BitVec.ofNat 64 (args.stackPointer - 0xb0 + offset)) width
  localStore : ∀ offset width, offset + width ≤ 0xb0 →
    StorePmaAllows state (BitVec.ofNat 64 (args.stackPointer - 0xb0 + offset)) width
  localLoadNoMMIO : ∀ offset width, offset + width ≤ 0xb0 →
    LoadMMIOAddressExcluded (BitVec.ofNat 64 (args.stackPointer - 0xb0 + offset)) width
  localStoreNoMMIO : ∀ offset width, offset + width ≤ 0xb0 →
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (args.stackPointer - 0xb0 + offset)) width
  writerLoad : ∀ offset width, offset + width ≤ 0x740 →
    LoadPmaAllows state (BitVec.ofNat 64 (args.stackPointer + offset)) width
  writerStore : ∀ offset width, offset + width ≤ 0x740 →
    StorePmaAllows state (BitVec.ofNat 64 (args.stackPointer + offset)) width
  writerLoadNoMMIO : ∀ offset width, offset + width ≤ 0x740 →
    LoadMMIOAddressExcluded (BitVec.ofNat 64 (args.stackPointer + offset)) width
  writerStoreNoMMIO : ∀ offset width, offset + width ≤ 0x740 →
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (args.stackPointer + offset)) width
  regionNotCode : ∀ address, args.stackPointer - 0xb0 ≤ address →
    address < args.stackPointer + 0x740 → Artifacts.programImage.readFileByte? address = none

def InlineEncoderEntry (entry : Nat) (bindValue : EndpointState → Value → Prop)
    (args : InlineEncoderArgs Value) (state : EndpointState) : Prop :=
  0xb0 ≤ args.stackPointer ∧ args.stackPointer + 0x740 ≤ 2 ^ 64 ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  bindValue state args.value ∧
  InlineEncoderSavedWords state.machine.mem args.savedWords ∧
  StatelessInputRep state.machine.mem args.decodedAddress args.decoded ∧
  args.copiedParentRootBytes = args.decoded.parentBeaconBlockRoot ∧
  BytesRep state.machine.mem args.copiedParentRootAddress args.copiedParentRootBytes ∧
  ByteWindowRelocation state.machine.mem state.machine.mem (args.decodedAddress + 592)
    args.copiedVersionedHashesAddress 16 ∧
  ExecutionPayloadRep state.machine.mem args.copiedPayloadAddress args.decoded.payload ∧
  BytesRep state.machine.mem args.copiedPayloadAddress args.copiedPayloadBytes ∧
  BytesRep state.machine.mem args.decodedAddress args.copiedSourceBytes ∧
  BytesRep state.machine.mem args.copiedSourceAddress args.copiedSourceBytes ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  InlineEncoderMachineAccess args state.machine

def InlineEncoderExit (successPc : Nat) (encode : Value → Array UInt8)
    (preservedValue : EndpointState → Value → Prop) (args : InlineEncoderArgs Value)
    (_outcome : Unit) (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 successPc) ∧
  after.stdout = before.stdout ++ encode args.value ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧
  after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  preservedValue after args.value ∧
  InlineEncoderSavedWords after.machine.mem args.savedWords ∧
  StatelessInputRep after.machine.mem args.decodedAddress args.decoded ∧
  BytesRep after.machine.mem args.copiedParentRootAddress args.copiedParentRootBytes ∧
  ByteWindowRelocation after.machine.mem after.machine.mem (args.decodedAddress + 592)
    args.copiedVersionedHashesAddress 16 ∧
  ExecutionPayloadRep after.machine.mem args.copiedPayloadAddress args.decoded.payload ∧
  BytesRep after.machine.mem args.copiedPayloadAddress args.copiedPayloadBytes ∧
  BytesRep after.machine.mem args.decodedAddress args.copiedSourceBytes ∧
  BytesRep after.machine.mem args.copiedSourceAddress args.copiedSourceBytes ∧
  EndpointMachineAuxAgree before.machine after.machine ∧
  BinaryFv.RiscV.WritesOnlyWithin
    (inlineEncoderMemoryRegion args.stackPointer) before.machine after.machine ∧
  BinaryFv.RiscV.Agree inlineEncoderPreserved before.machine after.machine ∧
  BinaryFv.RiscV.RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem

def inlineEncoderContract (entry successPc : Nat)
    (encode : Value → Array UInt8) (bindValue : EndpointState → Value → Prop)
    (stepBound : Nat → Nat) : RelationalMachineContract EndpointState (InlineEncoderArgs Value) Unit :=
  { allows := fun _ _ => True
    entry := InlineEncoderEntry entry bindValue
    exit := InlineEncoderExit successPc encode bindValue
    stepBound := fun args => stepBound args.inputSize }

def InlineEncoderInstanceContract (entry : Nat) (executionPcs : List Elflings.PcRange)
    (exitPcs : List Nat) (successPc : Nat) (encode : Value → Array UInt8)
    (bindValue : EndpointState → Value → Prop) : Prop :=
  ∃ stepBound : Nat → Nat,
    (inlineEncoderContract entry successPc encode bindValue stepBound).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs)

namespace InlineEncoderInstanceContract

noncomputable def stepBound {Value : Type} {entry successPc : Nat}
    {executionPcs : List Elflings.PcRange} {exitPcs : List Nat}
    {encode : Value → Array UInt8} {bindValue : EndpointState → Value → Prop}
    (contract : InlineEncoderInstanceContract entry executionPcs exitPcs successPc encode bindValue) :
    Nat → Nat :=
  Classical.choose contract

theorem implements {Value : Type} {entry successPc : Nat}
    {executionPcs : List Elflings.PcRange} {exitPcs : List Nat}
    {encode : Value → Array UInt8} {bindValue : EndpointState → Value → Prop}
    (contract : InlineEncoderInstanceContract entry executionPcs exitPcs successPc encode bindValue) :
    (inlineEncoderContract entry successPc encode bindValue contract.stepBound).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs) :=
  Classical.choose_spec contract

end InlineEncoderInstanceContract

structure InlineArrayEncoderValue (Element : Type) where
  address : Nat
  values : Array Element

def InlineArrayEncoderBinding (countBinding addressBinding : EndpointState → Nat → Prop)
    (stride : Nat)
    (elementRep : Std.ExtHashMap Nat (BitVec 8) → Nat → Element → Prop)
    (state : EndpointState) (value : InlineArrayEncoderValue Element) : Prop :=
  value.address + value.values.size * stride ≤ 2 ^ 64 ∧
  countBinding state value.values.size ∧
  addressBinding state value.address ∧
  ArrayRep stride elementRep state.machine.mem value.address value.values

abbrev WriteSuccessTransactionsInstanceContract : Prop :=
  InlineEncoderInstanceContract Elflings.writeSuccessTransactionsEntry
    Elflings.writeSuccessTransactionsExecutionPcRanges Elflings.writeSuccessTransactionsExitPcs 0x15668
    (fun value => encodeMany encodeTransaction value.values)
    (InlineArrayEncoderBinding
      (fun state count => state.machine.regs.get? x10 = some (BitVec.ofNat 64 count))
      (fun state address => ∃ stackPointer,
        state.machine.regs.get? x2 = some (BitVec.ofNat 64 stackPointer) ∧
        UIntRep 8 state.machine.mem (stackPointer + 104) address)
      288 TransactionRep)

abbrev WriteSuccessWithdrawalsInstanceContract : Prop :=
  InlineEncoderInstanceContract Elflings.writeSuccessWithdrawalsEntry
    Elflings.writeSuccessWithdrawalsExecutionPcRanges Elflings.writeSuccessWithdrawalsExitPcs 0x156e8
    (fun value => encodeMany encodeWithdrawal value.values)
    (InlineArrayEncoderBinding
      (fun state count => state.machine.regs.get? x9 = some (BitVec.ofNat 64 count))
      (fun state address => state.machine.regs.get? x8 = some (BitVec.ofNat 64 address))
      48 WithdrawalRep)

abbrev WriteSuccessHashesInstanceContract : Prop :=
  InlineEncoderInstanceContract Elflings.writeSuccessHashesEntry
    Elflings.writeSuccessHashesExecutionPcRanges Elflings.writeSuccessHashesExitPcs 0x158e0
    (fun value => encodeMany (fun hash => hash) value.values)
    (InlineArrayEncoderBinding
      (fun state count => state.machine.regs.get? x8 = some (BitVec.ofNat 64 count))
      (fun state address => state.machine.regs.get? x9 = some (BitVec.ofNat 64 address)) 32
      (fun mem address hash => hash.size = 32 ∧ BytesRep mem address hash))

/-- The exact unresolved contracts selected at UI Level 2. Linux read/exit and the shared `memcpy`
are omitted because `level1Contracts_of_level2` must discharge those three leaves unconditionally. -/
structure Level2ContractAssumptions : Prop where
  sszDecode : SszDecodeLevel2InstanceContract
  writeSuccessPrefix : WriteSuccessPrefixInstanceContract
  writeSuccessParentHash : WriteSuccessParentHashInstanceContract
  writeSuccessFeeRecipient : WriteSuccessFeeRecipientInstanceContract
  writeSuccessStateRoot : WriteSuccessStateRootInstanceContract
  writeSuccessReceiptsRoot : WriteSuccessReceiptsRootInstanceContract
  writeSuccessLogsBloom : WriteSuccessLogsBloomInstanceContract
  writeSuccessPrevRandao : WriteSuccessPrevRandaoInstanceContract
  writeSuccessBlockHash : WriteSuccessBlockHashInstanceContract
  writeSuccessParentBeaconRoot : WriteSuccessParentBeaconRootInstanceContract
  writeSuccessTransactions : WriteSuccessTransactionsInstanceContract
  writeSuccessWithdrawals : WriteSuccessWithdrawalsInstanceContract
  writeSuccessHashes : WriteSuccessHashesInstanceContract
  writeSuccessBoolean : WriteSuccessBooleanInstanceContract
  writeSuccessOptionalU64 : WriteSuccessOptionalU64InstanceContract
  writeSuccessByteLists : WriteSuccessByteListsInstanceContract
  writeSuccessBytes : WriteSuccessBytesInstanceContract
  writeSuccessInt : WriteSuccessIntInstanceContract
  writeFailureRecord : WriteFailureRecordInstanceContract

end BinaryFv.Zesu
