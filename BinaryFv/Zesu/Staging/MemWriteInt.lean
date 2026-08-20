import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.DecodedValue.Encoder
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps

/-!
# The `mem.writeInt` hLevel3 boundary

The inlined instance at `0x15d18` is the fixed-width store in the integer encoder.  The
caller supplies the destination through `x2` and the integer through `x10`.  The entry
records the configured machine and data-side store checks before the instruction runs.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.Zesu
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register
open MemoryAccessType mem_payload page_based_mem_type

structure MemWriteIntArgs where
  address : Nat
  value : Nat
  addressFits : address + 8 ≤ 2 ^ 64
  valueFits : value < 2 ^ 64

structure MemWriteIntStoreAccess (args : MemWriteIntArgs) (state : State) : Prop where
  nonwrap : args.address + 8 ≤ 2 ^ 64
  aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 args.address)) 8 = true
  pma : StorePmaAllows state (BitVec.ofNat 64 args.address) 8
  noMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 args.address) 8
  codeDisjoint : ∀ index : Fin 8,
    Artifacts.programImage.readFileByte? (args.address + index.val) = none

def memWriteIntStorePre (args : MemWriteIntArgs) (state : State) : Prop :=
  ∃ (byte0 byte1 byte2 byte3 : UInt8),
    BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) ∧
    Artifacts.programImage.readFileByte? 0x15d18 = some byte0 ∧
    Artifacts.programImage.readFileByte? (0x15d18 + 1) = some byte1 ∧
    Artifacts.programImage.readFileByte? (0x15d18 + 2) = some byte2 ∧
    Artifacts.programImage.readFileByte? (0x15d18 + 3) = some byte3 ∧
    Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (0#12, .Regidx 10#5, .Regidx 2#5, 8)) ∧
    MemWriteIntStoreAccess args state

theorem memWriteIntStoreAccess_rejects_denied_pma
    (denied : ¬StorePmaAllows state (BitVec.ofNat 64 args.address) 8) :
    ¬MemWriteIntStoreAccess args state := by
  intro access
  exact denied access.pma

theorem memWriteIntStoreAccess_rejects_mmio
    (denied : ¬StoreMMIOAddressExcluded (BitVec.ofNat 64 args.address) 8) :
    ¬MemWriteIntStoreAccess args state := by
  intro access
  exact denied access.noMMIO

theorem memWriteIntStoreAccess_rejects_misaligned
    (misaligned : ¬is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 args.address)) 8 = true) :
    ¬MemWriteIntStoreAccess args state := by
  intro access
  exact misaligned access.aligned

theorem memWriteIntStoreAccess_rejects_wrap
    (wraps : ¬args.address + 8 ≤ 2 ^ 64) :
    ¬MemWriteIntStoreAccess args state := by
  intro access
  exact wraps access.nonwrap

theorem memWriteIntStoreAccess_rejects_code_overlap
    (overlap : ∃ index : Fin 8,
      Artifacts.programImage.readFileByte? (args.address + index.val) ≠ none) :
    ¬MemWriteIntStoreAccess args state := by
  intro access
  obtain ⟨index, different⟩ := overlap
  exact different (access.codeDisjoint index)

def memWriteIntEntry (args : MemWriteIntArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 0x15d18) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.address) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.value) ∧
  ConfiguredMachinePre EndpointMachinePc state.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  memWriteIntStorePre args state.machine

def memWriteIntPreserved (register : Register) : Prop :=
  register = x2 ∨ register = x10 ∨ inlineEncoderPreserved register

def memWriteIntExit (args : MemWriteIntArgs) (_outcome : Unit)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 0x15d1c) ∧
  BytesRep after.machine.mem args.address (encodeNatLE 8 args.value) ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode ∧
  WritesOnlyWithin (byteRange args.address 8) before.machine after.machine ∧
  Agree memWriteIntPreserved before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine

def memWriteIntContract (stepBound : MemWriteIntArgs → Nat) :
    RelationalMachineContract EndpointState MemWriteIntArgs Unit :=
  { allows := fun _ _ => True
    entry := memWriteIntEntry
    exit := memWriteIntExit
    stepBound := stepBound }

def Proposed_mem_writeInt_fi_1_45b2_Contract : Prop :=
  ∃ stepBound : Nat,
    stepBound < level2ContractFuel ∧
    (memWriteIntContract (fun _ => stepBound)).Implements EndpointStep EndpointPc
      (pcInList [0x15d18]) (pcInList [0x15d1c])

end BinaryFv.Zesu.Staging
