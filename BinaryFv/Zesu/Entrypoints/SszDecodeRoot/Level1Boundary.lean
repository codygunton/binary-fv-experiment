import BinaryFv.Zesu.Contracts.DecodedResultRelation
import BinaryFv.Zesu.DecodedValue.Representation
import BinaryFv.Zesu.Elflings.GeneratedLevel1
import BinaryFv.Zesu.Artifacts.Image
import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.HostExecution
import BinaryFv.Zesu.MachineExecution.Level0MainSteps
import BinaryFv.RiscV.Logic.LoadedImage
import BinaryFv.RiscV.Model.Abi
import BinaryFv.RiscV.Step.ConfiguredMachine
import BinaryFv.RiscV.Platform.PhysicalAccess
import BinaryFv.RiscV.Platform.FetchMmio

/-!
# Typed boundary for the noinline Level 1 decoder

The endpoint wrapper makes result materialization part of `ssz_decode_root.decodeInput`, avoiding a
compiler-specific relation over scattered caller temporaries. This file deliberately does not claim
a step bound or implementation theorem yet.
-/

namespace BinaryFv.Zesu

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.Specs.SSZ
open BinaryFv.RiscV

structure DecodeBoundaryArgs where
  returnAddress : Nat
  savedReturnAddress : Nat
  inputAddress : Nat
  input : Array UInt8
  stackPointer : Nat
  allocatorStateAddress : Nat
  allocatorVtableAddress : Nat

structure DecodeCalleeSavedValues where
  s0 : BitVec 64
  s1 : BitVec 64
  s2 : BitVec 64
  s3 : BitVec 64
  s4 : BitVec 64
  s5 : BitVec 64
  s6 : BitVec 64
  s7 : BitVec 64
  s8 : BitVec 64
  s9 : BitVec 64
  s10 : BitVec 64
  s11 : BitVec 64

def DecodeCalleeSavedAtRegisters (values : DecodeCalleeSavedValues)
    (state : EndpointState) : Prop :=
  state.machine.regs.get? x8 = some values.s0 ∧
  state.machine.regs.get? x9 = some values.s1 ∧
  state.machine.regs.get? x18 = some values.s2 ∧
  state.machine.regs.get? x19 = some values.s3 ∧
  state.machine.regs.get? x20 = some values.s4 ∧
  state.machine.regs.get? x21 = some values.s5 ∧
  state.machine.regs.get? x22 = some values.s6 ∧
  state.machine.regs.get? x23 = some values.s7 ∧
  state.machine.regs.get? x24 = some values.s8 ∧
  state.machine.regs.get? x25 = some values.s9 ∧
  state.machine.regs.get? x26 = some values.s10 ∧
  state.machine.regs.get? x27 = some values.s11

def decodeCalleeSavedRegister (register : Register) : Prop :=
  register = x8 ∨ register = x9 ∨ register = x18 ∨ register = x19 ∨ register = x20 ∨
    register = x21 ∨ register = x22 ∨ register = x23 ∨ register = x24 ∨ register = x25 ∨
    register = x26 ∨ register = x27

theorem DecodeCalleeSavedAtRegisters.of_agree {values : DecodeCalleeSavedValues}
    {before after : EndpointState}
    (agree : Agree decodeCalleeSavedRegister before.machine after.machine)
    (saved : DecodeCalleeSavedAtRegisters values before) :
    DecodeCalleeSavedAtRegisters values after := by
  rcases saved with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact (agree x8 (by simp [decodeCalleeSavedRegister])).trans s0
    | exact (agree x9 (by simp [decodeCalleeSavedRegister])).trans s1
    | exact (agree x18 (by simp [decodeCalleeSavedRegister])).trans s2
    | exact (agree x19 (by simp [decodeCalleeSavedRegister])).trans s3
    | exact (agree x20 (by simp [decodeCalleeSavedRegister])).trans s4
    | exact (agree x21 (by simp [decodeCalleeSavedRegister])).trans s5
    | exact (agree x22 (by simp [decodeCalleeSavedRegister])).trans s6
    | exact (agree x23 (by simp [decodeCalleeSavedRegister])).trans s7
    | exact (agree x24 (by simp [decodeCalleeSavedRegister])).trans s8
    | exact (agree x25 (by simp [decodeCalleeSavedRegister])).trans s9
    | exact (agree x26 (by simp [decodeCalleeSavedRegister])).trans s10
    | exact (agree x27 (by simp [decodeCalleeSavedRegister])).trans s11

set_option genInjectivity false in
/-- Caller-derived permissions for the concrete `decodeInput` frame below its incoming stack
pointer. These facts enable the parent-owned prologue; they are not part of `hLevel2`. -/
structure DecodeBoundaryMachineAccess (args : DecodeBoundaryArgs) (state : MachineState) : Prop where
  configured : ConfiguredMachinePre EndpointMachinePc state
  frameStore : ∀ offset width, offset + width ≤ 0xbb0 →
    StorePmaAllows state (BitVec.ofNat 64 (args.stackPointer - 0xbb0 + offset)) width
  frameNoMMIO : ∀ offset width, offset + width ≤ 0xbb0 →
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (args.stackPointer - 0xbb0 + offset)) width
  frameNotCode : ∀ address, args.stackPointer - 0xbb0 ≤ address →
    address < args.stackPointer → Artifacts.programImage.readFileByte? address = none

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
  args.returnAddress ∈ Elflings.decodeInputExitPcs ∧
  args.allocatorVtableAddress = Elflings.allocatorVtableAddress ∧
  state.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.decodeInputEntry) ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  0xbb0 ≤ args.stackPointer ∧ args.stackPointer % 16 = 0 ∧
  args.stackPointer + 0x380 < 2 ^ 64 ∧
  args.inputAddress + args.input.size ≤ 2 ^ 64 ∧
  (args.stackPointer ≤ args.inputAddress ∨
    args.inputAddress + args.input.size ≤ args.stackPointer - 0xbb0) ∧
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
  BytesRep state.machine.mem args.inputAddress args.input ∧
  DecodeBoundaryMachineAccess args state.machine ∧
  ∃ values, DecodeCalleeSavedAtRegisters values state

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
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
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
        StatelessInputRep state.machine.mem (args.stackPointer + 0x20) decoded ∧
        InitializedByteWindow state.machine.mem (args.stackPointer + 0x20) 720 ∧
        DwordWindowRep state.machine.mem (args.stackPointer + 0x20 + 720) 16

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
  pcInRanges Elflings.decodeInputExecutionPcRanges

def DecodeExitPc (pc : BitVec 64) : Prop :=
  pcInList Elflings.decodeInputExitPcs pc

theorem decodeInputExitPc_14cfc : 0x14cfc ∈ Elflings.decodeInputExitPcs := by native_decide

/-- The exact strict implementation obligation at the generated production boundary. -/
abbrev StrictDecodeInstanceContract (stepBound : DecodeBoundaryArgs → Nat) : Prop :=
  (strictDecodeContract stepBound).Implements EndpointStep EndpointPc DecodeExecutionPc DecodeExitPc

/-- The generated decode instance terminates within some input-indexed bound and has the reviewed
compatibility semantics. The bound is implementation evidence, not caller-selected contract data. -/
def DecodeInstanceContractModuloKnownBugs : Prop :=
  ∃ stepBound : Nat → Nat,
    (decodeContractModuloKnownBugs (fun args => stepBound args.input.size)).Implements
      EndpointStep EndpointPc DecodeExecutionPc DecodeExitPc

end BinaryFv.Zesu
