import BinaryFv.Ssz.Relation
import BinaryFv.Ssz.ZigRepresentation
import BinaryFv.Ssz.Generated.Level1
import BinaryFv.Ssz.Generated.ProgramImage
import BinaryFv.Ssz.HostExecution
import BinaryFv.Ssz.Level0MainSteps
import BinaryFv.RiscV.Logic.LoadedImage
import BinaryFv.RiscV.Model.Abi

/-!
# Typed boundary for the noinline Level 1 decoder

The endpoint wrapper makes result materialization part of `ssz_decode_root.decodeInput`, avoiding a
compiler-specific relation over scattered caller temporaries. This file deliberately does not claim
a step bound or implementation theorem yet.
-/

namespace BinaryFv.Ssz

open PreSail LeanRV64DExecutable.Functions Register

structure DecodeBoundaryArgs where
  returnAddress : Nat
  savedReturnAddress : Nat
  inputAddress : Nat
  input : Array UInt8
  stackPointer : Nat
  allocatorStateAddress : Nat
  allocatorVtableAddress : Nat

inductive DecodeBoundaryOutcome where
  | failure
  | success (decoded : ZesuDecodedResult)

/-- Strict common-revision meaning. Reviewed version divergences widen this relation separately. -/
def StrictDecodeMeaning (args : DecodeBoundaryArgs) : DecodeBoundaryOutcome → Prop
  | .failure => ¬∃ decoded, SailDecode args.input decoded
  | .success zesu => ∃ sail, SailDecode args.input sail ∧
      decodedResultRelModuloKnownBugs args.input zesu sail

/-- The fixed compatibility policy: ordinary results match EVM-Sail; only a classified rejected
reference input may use one of the six reviewed domain exceptions. -/
def DecodeMeaningModuloKnownBugs (args : DecodeBoundaryArgs) : DecodeBoundaryOutcome → Prop
  | .failure => ¬∃ decoded, SailDecode args.input decoded
  | .success zesu =>
      (∃ sail, SailDecode args.input sail ∧
        decodedResultRelModuloKnownBugs args.input zesu sail) ∨
      ((¬∃ sail, SailDecode args.input sail) ∧
        ∃ bug ∈ knownBugs, KnownBugApplies args.input zesu bug)

/-- The actual noinline wrapper ABI: main supplies an 848-byte result slot in `a0`, an allocator
descriptor address in `a1`, and the input slice in `a2`/`a3`. -/
def DecodeBoundaryEntry (args : DecodeBoundaryArgs) (state : EndpointState) : Prop :=
  state.stdin = args.input ∧
  args.returnAddress ∈ Generated.decodeInputExitPcs ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Generated.decodeInputEntry) ∧
  Generated.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  args.stackPointer + 0x380 < 2 ^ 64 ∧
  args.inputAddress + args.input.size ≤ 2 ^ 64 ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 (args.stackPointer + 0x20)) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 (args.stackPointer + 0x10)) ∧
  state.machine.regs.get? x12 = some (BitVec.ofNat 64 args.inputAddress) ∧
  state.machine.regs.get? x13 = some (BitVec.ofNat 64 args.input.size) ∧
  UIntRep 8 state.machine.mem args.stackPointer args.inputAddress ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 8) args.input.size ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x10) args.allocatorStateAddress ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x18) args.allocatorVtableAddress ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x378) args.savedReturnAddress ∧
  BytesRep state.machine.mem args.inputAddress args.input

/-- The exact Sail read consumed by main's `lhu`, tied to the represented decoder status. -/
def DecodeStatusLoadWitness (state : EndpointState) (status : Nat) : Prop :=
  ∃ access : MainHalfLoadAccess state.machine 0x14cfc 0x370 BinaryFv.RiscV.stackPointer,
    access.data = BitVec.ofNat 16 status

/-- Both outcomes return to main at the same ABI continuation. The two-byte error-union tag selects
the parent branch; success exposes the fully materialized 848-byte result in main's result slot. -/
def DecodeBoundaryExit (args : DecodeBoundaryArgs) (outcome : DecodeBoundaryOutcome)
    (before state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) ∧
  state.stdin = before.stdin ∧ state.stdinCursor = before.stdinCursor ∧
  state.stdout = before.stdout ∧ state.exitCode = before.exitCode ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  UIntRep 8 state.machine.mem args.stackPointer args.inputAddress ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 8) args.input.size ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x378) args.savedReturnAddress ∧
  BytesRep state.machine.mem args.inputAddress args.input ∧
  Generated.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  state.machine.choiceState = before.machine.choiceState ∧
  state.machine.tags = before.machine.tags ∧
  state.machine.sailOutput = before.machine.sailOutput ∧
  EndpointCallFrame before state ∧
    match outcome with
    | .failure => ∃ status : Nat, status ≠ 0 ∧ status < 2 ^ 16 ∧
        UIntRep 2 state.machine.mem (args.stackPointer + 0x370) status ∧
        DecodeStatusLoadWitness state status
    | .success decoded =>
      UIntRep 2 state.machine.mem (args.stackPointer + 0x370) 0 ∧
        DecodeStatusLoadWitness state 0 ∧
        StatelessInputRep state.machine.mem (args.stackPointer + 0x20) decoded

/-- The strict contract shape. The reviewed Level 1 contract will instantiate its bound and widen
only the fixed accept/reject domains represented by `knownBugs`. -/
def strictDecodeContract (stepBound : DecodeBoundaryArgs → Nat) :
    RelationalMachineContract EndpointState DecodeBoundaryArgs DecodeBoundaryOutcome :=
  { allows := StrictDecodeMeaning
    entry := DecodeBoundaryEntry
    exit := DecodeBoundaryExit
    stepBound }

/-- The actual Level 1 semantic contract shape. Its implementation proof supplies the input-indexed
termination bound; observed fixture counts are evidence, not a universal premise. -/
def decodeContractModuloKnownBugs (stepBound : DecodeBoundaryArgs → Nat) :
    RelationalMachineContract EndpointState DecodeBoundaryArgs DecodeBoundaryOutcome :=
  { allows := DecodeMeaningModuloKnownBugs
    entry := DecodeBoundaryEntry
    exit := DecodeBoundaryExit
    stepBound }

def DecodeExecutionPc : BitVec 64 → Prop :=
  pcInRanges Generated.decodeInputExecutionPcRanges

def DecodeExitPc (pc : BitVec 64) : Prop :=
  pcInList Generated.decodeInputExitPcs pc

theorem decodeInputExitPc_14cfc : 0x14cfc ∈ Generated.decodeInputExitPcs := by native_decide

/-- The exact strict implementation obligation at the generated production boundary. -/
abbrev StrictDecodeInstanceContract (stepBound : DecodeBoundaryArgs → Nat) : Prop :=
  (strictDecodeContract stepBound).Implements EndpointStep EndpointPc DecodeExecutionPc DecodeExitPc

/-- The generated decode instance terminates within some input-indexed bound and has the reviewed
compatibility semantics. The bound is implementation evidence, not caller-selected contract data. -/
def DecodeInstanceContractModuloKnownBugs : Prop :=
  ∃ stepBound : Nat → Nat,
    (decodeContractModuloKnownBugs (fun args => stepBound args.input.size)).Implements
      EndpointStep EndpointPc DecodeExecutionPc DecodeExitPc

end BinaryFv.Ssz
