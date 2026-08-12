import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level1Contracts
import BinaryFv.Zesu.Elflings.GeneratedLevel2
import BinaryFv.Zesu.DecodedValue.Encoder

/-!
# Level 2 contracts for the SSZ endpoint

The fixed raw encoders all implement the same reviewed operation: append a source byte window to
stdout without changing machine memory. Exact entry, execution, and exit sets come from the pinned
ELF. The source pointer is `x10` at the eight decoded-field callsites; the two format-prefix
callsites append source constants and therefore need no caller-provided pointer.
-/

namespace BinaryFv.Zesu

open PreSail LeanRV64DExecutable.Functions Register

structure RawEncoderArgs where
  sourceAddress : Nat
  bytes : Array UInt8

def RawEncoderEntry (entry : Nat) (args : RawEncoderArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.sourceAddress) ∧
  BytesRep state.machine.mem args.sourceAddress args.bytes ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def RawEncoderExit (exitPcs : List Nat) (args : RawEncoderArgs) (_outcome : Unit)
    (before after : EndpointState) : Prop :=
  (∃ pc, after.machine.regs.get? PC = some pc ∧ pcInList exitPcs pc) ∧
  after.stdout = before.stdout ++ args.bytes ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧ after.machine.mem = before.machine.mem ∧
  EndpointCallFrame before after

def rawEncoderContract (entry : Nat) (exitPcs : List Nat)
    (stepBound : RawEncoderArgs → Nat) :
    RelationalMachineContract EndpointState RawEncoderArgs Unit :=
  { allows := fun _ _ => True
    entry := RawEncoderEntry entry
    exit := RawEncoderExit exitPcs
    stepBound }

def RawEncoderInstanceContract (entry : Nat) (executionPcs : List Elflings.PcRange)
    (exitPcs : List Nat) : Prop :=
  ∃ stepBound : Nat → Nat,
    (rawEncoderContract entry exitPcs (fun args => stepBound args.bytes.size)).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs)

def ConstantEncoderEntry (entry : Nat) (_args : Unit) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def ConstantEncoderExit (exitPcs : List Nat) (bytes : Array UInt8) (_args _outcome : Unit)
    (before after : EndpointState) : Prop :=
  (∃ pc, after.machine.regs.get? PC = some pc ∧ pcInList exitPcs pc) ∧
  after.stdout = before.stdout ++ bytes ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧ after.machine.mem = before.machine.mem ∧
  EndpointCallFrame before after

def constantEncoderContract (entry : Nat) (exitPcs : List Nat) (bytes : Array UInt8)
    (stepBound : Nat) : RelationalMachineContract EndpointState Unit Unit :=
  { allows := fun _ _ => True
    entry := ConstantEncoderEntry entry
    exit := ConstantEncoderExit exitPcs bytes
    stepBound := fun _ => stepBound }

def ConstantEncoderInstanceContract (entry : Nat) (executionPcs : List Elflings.PcRange)
    (exitPcs : List Nat) (bytes : Array UInt8) : Prop :=
  ∃ stepBound : Nat,
    (constantEncoderContract entry exitPcs bytes stepBound).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs)

def successPrefixBytes : Array UInt8 := #[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x01]
def failureRecordBytes : Array UInt8 := #[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x00]

abbrev WriteSuccessPrefixInstanceContract : Prop :=
  ConstantEncoderInstanceContract Elflings.writeSuccessRawLine131Entry
    Elflings.writeSuccessRawLine131ExecutionPcRanges
    Elflings.writeSuccessRawLine131ExitPcs successPrefixBytes

abbrev WriteFailureRecordInstanceContract : Prop :=
  ConstantEncoderInstanceContract Elflings.writeFailureRawLine127Entry
    Elflings.writeFailureRawLine127ExecutionPcRanges
    Elflings.writeFailureRawLine127ExitPcs failureRecordBytes

abbrev WriteSuccessParentHashInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine135Entry
    Elflings.writeSuccessRawLine135ExecutionPcRanges Elflings.writeSuccessRawLine135ExitPcs

abbrev WriteSuccessFeeRecipientInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine136Entry
    Elflings.writeSuccessRawLine136ExecutionPcRanges Elflings.writeSuccessRawLine136ExitPcs

abbrev WriteSuccessStateRootInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine137Entry
    Elflings.writeSuccessRawLine137ExecutionPcRanges Elflings.writeSuccessRawLine137ExitPcs

abbrev WriteSuccessReceiptsRootInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine138Entry
    Elflings.writeSuccessRawLine138ExecutionPcRanges Elflings.writeSuccessRawLine138ExitPcs

abbrev WriteSuccessLogsBloomInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine139Entry
    Elflings.writeSuccessRawLine139ExecutionPcRanges Elflings.writeSuccessRawLine139ExitPcs

abbrev WriteSuccessPrevRandaoInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine140Entry
    Elflings.writeSuccessRawLine140ExecutionPcRanges Elflings.writeSuccessRawLine140ExitPcs

abbrev WriteSuccessBlockHashInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine147Entry
    Elflings.writeSuccessRawLine147ExecutionPcRanges Elflings.writeSuccessRawLine147ExitPcs

abbrev WriteSuccessParentBeaconRootInstanceContract : Prop :=
  RawEncoderInstanceContract Elflings.writeSuccessRawLine156Entry
    Elflings.writeSuccessRawLine156ExecutionPcRanges Elflings.writeSuccessRawLine156ExitPcs

structure EncoderCallArgs (Value : Type) where
  callerStack : Nat
  value : Value

def EncoderCallEntry (entry : Nat) (bindValue : EndpointState → Value → Prop)
    (args : EncoderCallArgs Value) (state : EndpointState) : Prop :=
  args.callerStack < 2 ^ 64 ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.callerStack) ∧
  bindValue state args.value ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def EncoderCallExit (exitPcs : List Nat) (frameSize : Nat)
    (encode : Value → Array UInt8) (args : EncoderCallArgs Value) (_outcome : Unit)
    (before after : EndpointState) : Prop :=
  (∃ pc, after.machine.regs.get? PC = some pc ∧ pcInList exitPcs pc) ∧
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
    (stepBound : Value → Nat) : RelationalMachineContract EndpointState (EncoderCallArgs Value) Unit :=
  { allows := fun _ _ => True
    entry := EncoderCallEntry entry bindValue
    exit := EncoderCallExit exitPcs frameSize encode
    stepBound := fun args => stepBound args.value }

def EncoderCallInstanceContract (entry : Nat) (executionPcs : List Elflings.PcRange)
    (exitPcs : List Nat) (frameSize : Nat) (encode : Value → Array UInt8)
    (bindValue : EndpointState → Value → Prop) : Prop :=
  ∃ stepBound : Value → Nat,
    (encoderCallContract entry exitPcs frameSize encode bindValue stepBound).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs)

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

end BinaryFv.Zesu
