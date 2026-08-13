import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level1Boundary

/-!
# Level 1 contract assumptions for the SSZ endpoint

These are the six contracts selected by the generated Level 1 manifest. They bind source values
to the production registers and memory, state exact generated execution and exit sets, and expose
the register, memory, and endpoint-state frames needed by the Level 0 proof. This file states the
assumptions; later refinement levels discharge them.
-/

namespace BinaryFv.Zesu

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.RiscV

structure ReadInputArgs where
  returnAddress : Nat
  bufferSlot : Nat
  sizeSlot : Nat
  savedFrameAddress : Nat
  savedReturnAddress : Nat
  input : Array UInt8

structure ReadInputOutcome where
  inputAddress : Nat

def ReadInputEntry (args : ReadInputArgs) (state : EndpointState) : Prop :=
  args.returnAddress ∈ Elflings.readInputExitPcs ∧
  args.input.size ≤ 64 * 1024 * 1024 ∧
  state.stdin = args.input ∧ state.stdinCursor = 0 ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.readInputEntry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.bufferSlot) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 args.sizeSlot) ∧
  BytesRep state.machine.mem Elflings.inputBufferAddress args.input ∧
  UIntRep 8 state.machine.mem args.savedFrameAddress args.savedReturnAddress ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  ConfiguredMachinePre EndpointMachinePc state.machine

def ReadInputExit (args : ReadInputArgs) (outcome : ReadInputOutcome)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) ∧
  after.stdin = before.stdin ∧ after.stdinCursor = args.input.size ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode ∧
  UIntRep 8 after.machine.mem args.bufferSlot outcome.inputAddress ∧
  UIntRep 8 after.machine.mem args.sizeSlot args.input.size ∧
  BytesRep after.machine.mem outcome.inputAddress args.input ∧
  UIntRep 8 after.machine.mem args.savedFrameAddress args.savedReturnAddress ∧
  WritesOnlyWithin
    (Region.union (byteRange args.bufferSlot 8) (byteRange args.sizeSlot 8))
    before.machine after.machine ∧
  EndpointCallFrame before after

def readInputContract (stepBound : ReadInputArgs → Nat) :
    RelationalMachineContract EndpointState ReadInputArgs ReadInputOutcome :=
  { allows := fun _ _ => True
    entry := ReadInputEntry
    exit := ReadInputExit
    stepBound }

def ReadInputInstanceContract : Prop :=
  ∃ stepBound : Nat → Nat,
    (readInputContract (fun args => stepBound args.input.size)).Implements EndpointStep EndpointPc
    (pcInRanges Elflings.readInputExecutionPcRanges)
    (pcInList Elflings.readInputExitPcs)

theorem readInputExitPc_14ccc : 0x14ccc ∈ Elflings.readInputExitPcs := by native_decide

structure AllocatorGetArgs where
  returnAddress : Nat
  stackPointer : Nat
  inputAddress : Nat
  input : Array UInt8
  savedReturnAddress : Nat

structure AllocatorGetOutcome where
  stateAddress : Nat
  vtableAddress : Nat

def AllocatorGetEntry (args : AllocatorGetArgs) (state : EndpointState) : Prop :=
  args.returnAddress ∈ Elflings.allocatorGetExitPcs ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.allocatorGetEntry) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  UIntRep 8 state.machine.mem args.stackPointer args.inputAddress ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 8) args.input.size ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x378) args.savedReturnAddress ∧
  BytesRep state.machine.mem args.inputAddress args.input ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def AllocatorGetExit (args : AllocatorGetArgs) (outcome : AllocatorGetOutcome)
    (before after : EndpointState) : Prop :=
  outcome.vtableAddress = Elflings.allocatorVtableAddress ∧
  after.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) ∧
  after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  after.machine.regs.get? x10 = some (BitVec.ofNat 64 outcome.stateAddress) ∧
  after.machine.regs.get? x11 = some (BitVec.ofNat 64 outcome.vtableAddress) ∧
  after.machine.regs.get? x12 = some (BitVec.ofNat 64 args.inputAddress) ∧
  after.machine.regs.get? x13 = some (BitVec.ofNat 64 args.input.size) ∧
  after.machine.regs.get? x18 = some (BitVec.ofNat 64 args.input.size) ∧
  after.machine.regs.get? x23 = some (BitVec.ofNat 64 args.inputAddress) ∧
  UIntRep 8 after.machine.mem args.stackPointer args.inputAddress ∧
  UIntRep 8 after.machine.mem (args.stackPointer + 8) args.input.size ∧
  UIntRep 8 after.machine.mem (args.stackPointer + 0x10) outcome.stateAddress ∧
  UIntRep 8 after.machine.mem (args.stackPointer + 0x18) outcome.vtableAddress ∧
  UIntRep 8 after.machine.mem (args.stackPointer + 0x378) args.savedReturnAddress ∧
  BytesRep after.machine.mem args.inputAddress args.input ∧
  WritesOnlyWithin
    (Region.union (byteRange (args.stackPointer + 0x10) 8)
      (byteRange (args.stackPointer + 0x18) 8)) before.machine after.machine ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode ∧
  EndpointCallFrame before after

def allocatorGetContract (stepBound : AllocatorGetArgs → Nat) :
    RelationalMachineContract EndpointState AllocatorGetArgs AllocatorGetOutcome :=
  { allows := fun _ _ => True
    entry := AllocatorGetEntry
    exit := AllocatorGetExit
    stepBound }

def AllocatorGetInstanceContract : Prop :=
  ∃ stepBound : Nat → Nat,
    (allocatorGetContract (fun args => stepBound args.input.size)).Implements EndpointStep EndpointPc
    (pcInRanges Elflings.allocatorGetExecutionPcRanges)
    (pcInList Elflings.allocatorGetExitPcs)

theorem allocatorGetExitPc_14cec : 0x14cec ∈ Elflings.allocatorGetExitPcs := by native_decide

structure WriteSuccessArgs where
  returnAddress : Nat
  stackPointer : Nat
  decodedAddress : Nat
  decoded : ZesuDecodedResult
  inputSize : Nat

def WriteSuccessEntry (args : WriteSuccessArgs) (state : EndpointState) : Prop :=
  args.returnAddress ∈ Elflings.writeSuccessExitPcs ∧ 0x7d0 ≤ args.stackPointer ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.writeSuccessEntry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.decodedAddress) ∧
  StatelessInputRep state.machine.mem args.decodedAddress args.decoded ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def WriteSuccessExit (args : WriteSuccessArgs) (bytes : Array UInt8)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) ∧
  decodeZesuObservation bytes = some (.success args.decoded) ∧
  after.stdout = before.stdout ++ bytes ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧
  WritesOnlyWithin (byteRange (args.stackPointer - 0x7d0) 0x7d0)
    before.machine after.machine ∧
  EndpointCallFrame before after

def writeSuccessContract (stepBound : WriteSuccessArgs → Nat) :
    RelationalMachineContract EndpointState WriteSuccessArgs (Array UInt8) :=
  { allows := fun args bytes => decodeZesuObservation bytes = some (.success args.decoded)
    entry := WriteSuccessEntry
    exit := WriteSuccessExit
    stepBound }

def WriteSuccessInstanceContract : Prop :=
  ∃ stepBound : Nat → Nat,
    (writeSuccessContract (fun args => stepBound args.inputSize)).Implements EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges)
    (pcInList Elflings.writeSuccessExitPcs)

structure WriteFailureArgs where
  returnAddress : Nat

def WriteFailureEntry (args : WriteFailureArgs) (state : EndpointState) : Prop :=
  args.returnAddress ∈ Elflings.writeFailureExitPcs ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.writeFailureEntry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def WriteFailureExit (args : WriteFailureArgs) (bytes : Array UInt8)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) ∧
  decodeZesuObservation bytes = some .failure ∧
  after.stdout = before.stdout ++ bytes ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧ after.machine.mem = before.machine.mem ∧
  EndpointCallFrame before after

def writeFailureContract (stepBound : WriteFailureArgs → Nat) :
    RelationalMachineContract EndpointState WriteFailureArgs (Array UInt8) :=
  { allows := fun _ bytes => decodeZesuObservation bytes = some .failure
    entry := WriteFailureEntry
    exit := WriteFailureExit
    stepBound }

def WriteFailureInstanceContract : Prop :=
  ∃ stepBound : Nat,
    (writeFailureContract (fun _ => stepBound)).Implements EndpointStep EndpointPc
    (pcInRanges Elflings.writeFailureExecutionPcRanges)
    (pcInList Elflings.writeFailureExitPcs)

structure ZkvmExitArgs where
  code : Nat

def ZkvmExitEntry (args : ZkvmExitArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.zkvmExitEntry) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.code) ∧
  StorePmaAllows state.machine (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8 ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  ConfiguredMachinePre EndpointMachinePc state.machine

def ZkvmExitPost (args : ZkvmExitArgs) (_outcome : Unit)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.zkvmExitTerminalPc) ∧
  after.exitCode = some args.code ∧ after.stdin = before.stdin ∧
  after.stdinCursor = before.stdinCursor ∧ after.stdout = before.stdout ∧
  WritesOnlyWithin (byteRange (Elflings.ioContextAddress + 24) 8)
    before.machine after.machine

def zkvmExitContract (stepBound : ZkvmExitArgs → Nat) :
    RelationalMachineContract EndpointState ZkvmExitArgs Unit :=
  { allows := fun _ _ => True
    entry := ZkvmExitEntry
    exit := ZkvmExitPost
    stepBound }

def ZkvmExitInstanceContract : Prop :=
  ∃ stepBound : Nat,
    (zkvmExitContract (fun _ => stepBound)).Implements EndpointStep EndpointPc
    (pcInRanges Elflings.zkvmExitExecutionPcRanges)
    (pcInList Elflings.zkvmExitExitPcs)

/-- The sole proof-progress argument of the initial conditional compliance theorem. -/
structure Level1ContractAssumptions : Prop where
  readInput : ReadInputInstanceContract
  zkvmExit : ZkvmExitInstanceContract
  allocatorGet : AllocatorGetInstanceContract
  sszDecode : DecodeInstanceContractModuloKnownBugs
  writeSuccess : WriteSuccessInstanceContract
  writeFailure : WriteFailureInstanceContract

end BinaryFv.Zesu
