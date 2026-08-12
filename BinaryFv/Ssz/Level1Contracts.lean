import BinaryFv.Ssz.Level1Boundary

/-!
# Level 1 contract assumptions for the SSZ endpoint

These are the six contracts selected by the generated Level 1 manifest. They bind source values
to the production registers and memory, state exact generated execution and exit sets, and expose
the register, memory, and endpoint-state frames needed by the Level 0 proof. This file states the
assumptions; later refinement levels discharge them.
-/

namespace BinaryFv.Ssz

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.RiscV

def abiCalleePreserved : Register → Prop := fun register =>
  register = x1 ∨ register = hart_state ∨ register = cur_privilege ∨ register = satp ∨
    register = mideleg ∨ register = mie ∨ register = mip ∨ register = pmpcfg_n ∨
    register = pmpaddr_n ∨ register = mcountinhibit ∨ register = minstretcfg ∨
    register = elp ∨ register = misa ∨ register = mstatus ∨ register = sig_meip ∨
    register = pma_regions ∨ register = mseccfg ∨ register = htif_tohost_base ∨
    register = x2 ∨ register = x8 ∨ register = x9 ∨
    register = x18 ∨ register = x19 ∨ register = x20 ∨ register = x21 ∨
    register = x22 ∨ register = x23 ∨ register = x24 ∨ register = x25 ∨
    register = x26 ∨ register = x27

/-- State preserved by every returning Level 1 ABI boundary. Memory permissions are contract-specific. -/
def EndpointCallFrame (before after : EndpointState) : Prop :=
  Agree abiCalleePreserved before.machine after.machine ∧
  Generated.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  after.machine.choiceState = before.machine.choiceState ∧
  after.machine.tags = before.machine.tags ∧
  after.machine.sailOutput = before.machine.sailOutput

structure ReadInputArgs where
  returnAddress : Nat
  bufferSlot : Nat
  sizeSlot : Nat
  input : Array UInt8

structure ReadInputOutcome where
  inputAddress : Nat

def ReadInputEntry (args : ReadInputArgs) (state : EndpointState) : Prop :=
  args.returnAddress ∈ Generated.readInputExitPcs ∧
  args.input.size ≤ 64 * 1024 * 1024 ∧
  state.stdin = args.input ∧ state.stdinCursor = 0 ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Generated.readInputEntry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.bufferSlot) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 args.sizeSlot) ∧
  Generated.programImage.fileBytesLoadedFaithfully state.machine.mem

def ReadInputExit (args : ReadInputArgs) (outcome : ReadInputOutcome)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) ∧
  after.stdin = before.stdin ∧ after.stdinCursor = args.input.size ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode ∧
  UIntRep 8 after.machine.mem args.bufferSlot outcome.inputAddress ∧
  UIntRep 8 after.machine.mem args.sizeSlot args.input.size ∧
  BytesRep after.machine.mem outcome.inputAddress args.input ∧
  WritesOnlyWithin
    (Region.union (byteRange outcome.inputAddress args.input.size)
      (Region.union (byteRange args.bufferSlot 8) (byteRange args.sizeSlot 8)))
    before.machine after.machine ∧
  EndpointCallFrame before after

def readInputContract (stepBound : ReadInputArgs → Nat) :
    RelationalMachineContract EndpointState ReadInputArgs ReadInputOutcome :=
  { allows := fun _ _ => True
    entry := ReadInputEntry
    exit := ReadInputExit
    stepBound }

def ReadInputInstanceContract : Prop :=
  ∃ stepBound, (readInputContract stepBound).Implements EndpointStep EndpointPc
    (pcInRanges Generated.readInputExecutionPcRanges)
    (pcInList Generated.readInputExitPcs)

structure AllocatorGetArgs where
  returnAddress : Nat
  stackPointer : Nat
  inputAddress : Nat
  input : Array UInt8
  savedFrame : Array UInt8

structure AllocatorGetOutcome where
  stateAddress : Nat
  vtableAddress : Nat

def AllocatorGetEntry (args : AllocatorGetArgs) (state : EndpointState) : Prop :=
  args.returnAddress ∈ Generated.allocatorGetExitPcs ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Generated.allocatorGetEntry) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  UIntRep 8 state.machine.mem args.stackPointer args.inputAddress ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 8) args.input.size ∧
  args.savedFrame.size = 8 ∧
  BytesRep state.machine.mem (args.stackPointer + 0x378) args.savedFrame ∧
  BytesRep state.machine.mem args.inputAddress args.input ∧
  Generated.programImage.fileBytesLoadedFaithfully state.machine.mem

def AllocatorGetExit (args : AllocatorGetArgs) (outcome : AllocatorGetOutcome)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) ∧
  after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  after.machine.regs.get? x10 = some (BitVec.ofNat 64 outcome.stateAddress) ∧
  after.machine.regs.get? x11 = some (BitVec.ofNat 64 outcome.vtableAddress) ∧
  after.machine.regs.get? x12 = some (BitVec.ofNat 64 3) ∧
  after.machine.regs.get? x18 = some (BitVec.ofNat 64 args.input.size) ∧
  after.machine.regs.get? x23 = some (BitVec.ofNat 64 args.inputAddress) ∧
  UIntRep 8 after.machine.mem (args.stackPointer + 0x10) outcome.stateAddress ∧
  UIntRep 8 after.machine.mem (args.stackPointer + 0x18) outcome.vtableAddress ∧
  BytesRep after.machine.mem (args.stackPointer + 0x378) args.savedFrame ∧
  BytesRep after.machine.mem args.inputAddress args.input ∧
  WritesOnlyWithin
    (Region.union (byteRange (args.stackPointer + 0x10) 8)
      (byteRange (args.stackPointer + 0x18) 8)) before.machine after.machine ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode ∧
  Generated.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  after.machine.choiceState = before.machine.choiceState ∧
  after.machine.tags = before.machine.tags ∧
  after.machine.sailOutput = before.machine.sailOutput

def allocatorGetContract (stepBound : AllocatorGetArgs → Nat) :
    RelationalMachineContract EndpointState AllocatorGetArgs AllocatorGetOutcome :=
  { allows := fun _ _ => True
    entry := AllocatorGetEntry
    exit := AllocatorGetExit
    stepBound }

def AllocatorGetInstanceContract : Prop :=
  ∃ stepBound, (allocatorGetContract stepBound).Implements EndpointStep EndpointPc
    (pcInRanges Generated.allocatorGetExecutionPcRanges)
    (pcInList Generated.allocatorGetExitPcs)

structure WriteSuccessArgs where
  returnAddress : Nat
  stackPointer : Nat
  decodedAddress : Nat
  decoded : ZesuDecodedResult

def WriteSuccessEntry (args : WriteSuccessArgs) (state : EndpointState) : Prop :=
  args.returnAddress ∈ Generated.writeSuccessExitPcs ∧ 0x7d0 ≤ args.stackPointer ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Generated.writeSuccessEntry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.decodedAddress) ∧
  StatelessInputRep state.machine.mem args.decodedAddress args.decoded ∧
  Generated.programImage.fileBytesLoadedFaithfully state.machine.mem

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
  ∃ stepBound, (writeSuccessContract stepBound).Implements EndpointStep EndpointPc
    (pcInRanges Generated.writeSuccessExecutionPcRanges)
    (pcInList Generated.writeSuccessExitPcs)

structure WriteFailureArgs where
  returnAddress : Nat

def WriteFailureEntry (args : WriteFailureArgs) (state : EndpointState) : Prop :=
  args.returnAddress ∈ Generated.writeFailureExitPcs ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Generated.writeFailureEntry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
  Generated.programImage.fileBytesLoadedFaithfully state.machine.mem

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
  ∃ stepBound, (writeFailureContract stepBound).Implements EndpointStep EndpointPc
    (pcInRanges Generated.writeFailureExecutionPcRanges)
    (pcInList Generated.writeFailureExitPcs)

structure ZkvmExitArgs where
  code : Nat

def ZkvmExitEntry (args : ZkvmExitArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Generated.zkvmExitEntry) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.code) ∧
  Generated.programImage.fileBytesLoadedFaithfully state.machine.mem

def ZkvmExitPost (args : ZkvmExitArgs) (_outcome : Unit)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 Generated.zkvmExitTerminalPc) ∧
  after.exitCode = some args.code ∧ after.stdin = before.stdin ∧
  after.stdinCursor = before.stdinCursor ∧ after.stdout = before.stdout ∧
  after.machine.mem = before.machine.mem

def zkvmExitContract (stepBound : ZkvmExitArgs → Nat) :
    RelationalMachineContract EndpointState ZkvmExitArgs Unit :=
  { allows := fun _ _ => True
    entry := ZkvmExitEntry
    exit := ZkvmExitPost
    stepBound }

def ZkvmExitInstanceContract : Prop :=
  ∃ stepBound, (zkvmExitContract stepBound).Implements EndpointStep EndpointPc
    (pcInRanges Generated.zkvmExitExecutionPcRanges)
    (pcInList Generated.zkvmExitExitPcs)

/-- The sole proof-progress argument of the initial conditional compliance theorem. -/
structure Level1ContractAssumptions : Prop where
  readInput : ReadInputInstanceContract
  zkvmExit : ZkvmExitInstanceContract
  allocatorGet : AllocatorGetInstanceContract
  sszDecode : DecodeInstanceContractModuloKnownBugs
  writeSuccess : WriteSuccessInstanceContract
  writeFailure : WriteFailureInstanceContract

end BinaryFv.Ssz
