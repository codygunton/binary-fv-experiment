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

def memWriteIntStoreState (state : State) : State :=
  coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 0x15d18)

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
    ∃ (destination mstatusBits dataBits : BitVec 64),
      destination = BitVec.ofNat 64 args.address ∧
      dataBits = BitVec.ofNat 64 args.value ∧
      (memWriteIntStoreState state).regs.get? mstatus = some mstatusBits ∧
      (memWriteIntStoreState state).regs.get? cur_privilege = some .Machine ∧
      _get_Mstatus_MPRV mstatusBits = 0#1 ∧
      Runs (rX_bits (.Regidx 10#5)) (memWriteIntStoreState state)
        (memWriteIntStoreState state) dataBits ∧
      Runs (get_transformed_data_addr (.Regidx 2#5) (sign_extend (m := 64) (0#12))
        (Store Data) 8)
        (memWriteIntStoreState state) (memWriteIntStoreState state)
        (.Ext_DataAddr_OK (virtaddr.Virtaddr destination)) ∧
      is_aligned_vaddr (virtaddr.Virtaddr destination) 8 = true ∧
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine
        (physaddr.Physaddr destination) 8 false)
        (memWriteIntStoreState state) (memWriteIntStoreState state) none ∧
      Runs (within_mmio_writable (physaddr.Physaddr destination) 8)
        (memWriteIntStoreState state) (memWriteIntStoreState state) false

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
