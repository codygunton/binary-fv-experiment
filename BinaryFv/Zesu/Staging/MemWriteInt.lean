import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.DecodedValue.Encoder
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.Level1DecodeInputSteps

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
  aligned : args.address % 8 = 0
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
    (misaligned : ¬args.address % 8 = 0) :
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
  encoderInlinePreserved register

def memWriteIntExit (args : MemWriteIntArgs) (_outcome : Unit)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 0x15d1c) ∧
  UIntRep 8 after.machine.mem args.address args.value ∧
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

private theorem memWriteIntPreserved_disjoint :
    RegSet.Disjoint memWriteIntPreserved stepBookkeeping := by
  intro register preserved written
  rcases written with rfl | rfl | rfl | rfl
  all_goals simp [memWriteIntPreserved, encoderInlinePreserved, instructionPreserved,
    platformPreserved] at preserved

/-- The production `mem.writeInt` instance implements its exact one-step contract. -/
theorem memWriteIntContract_implements :
    (memWriteIntContract (fun _ => 1)).Implements EndpointStep EndpointPc
      (pcInList [0x15d18]) (pcInList [0x15d1c]) := by
  intro args fromStep before entry
  rcases entry with ⟨atPc, stackRead, valueRead, configured, loaded, storePre⟩
  rcases storePre with ⟨byte0, byte1, byte2, byte3, base, read0, read1, read2, read3,
    decode, access⟩
  obtain ⟨retired, run⟩ := decodeInputStoreStep fromStep 0x15d18 0 before.machine
    args.address (BitVec.ofNat 64 args.value) 0 (.Regidx 10#5) byte0 byte1 byte2 byte3
    configured atPc stackRead access.pma access.noMMIO
    access.aligned args.addressFits loaded
    (by simp [show sign_extend (m := 64) (0#12) = 0#64 by native_decide])
    decode (by
      intro premise writes
      exact rX_x10_run premise (BitVec.ofNat 64 args.value)
        ((writes x10 (by simp [stepBookkeeping])).trans valueRead))
    (base := base) (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)
  let premise := coreStoreNextState
    (tryStepStoreAfterIncrement before.machine) (BitVec.ofNat 64 0x15d18)
  let afterWrite := afterWriteBytes (width := 8) premise args.address
    (BitVec.ofNat 64 args.value)
  let finalMachine := tryStepStoreAfterRetired afterWrite (BitVec.ofNat 64 0x15d18) retired
  let after : EndpointState := { before with machine := finalMachine }
  have writes : WritesOnlyRegs stepBookkeeping before.machine finalMachine := by
    simpa [finalMachine, afterWrite, premise, tryStepStoreAfterRetired, tryStepStoreAfterTick,
      coreStoreNextState, tryStepStoreAfterIncrement] using
      storeRetirement_writes before.machine (BitVec.ofNat 64 0x15d18)
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x15d18) 4) retired args.address
        (BitVec.ofNat 64 args.value)
  have memoryFrame : WritesOnlyWithin (byteRange args.address 8) before.machine finalMachine := by
    intro address outside
    change afterWrite.mem.get? address = before.machine.mem.get? address
    rw [afterWriteBytes_mem_get?_of_outside]
    · rfl
    · intro index equal
      apply outside
      constructor <;> omega
  have valueRep : UIntRep 8 finalMachine.mem args.address args.value := by
    change UIntRep 8 afterWrite.mem args.address args.value
    exact uintRep_afterWriteBytes_eight premise args.address args.value args.valueFits
      args.addressFits
  have codeAfterWrite : Artifacts.programImage.fileBytesLoadedFaithfully afterWrite.mem := by
    apply fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage premise args.address
      (BitVec.ofNat 64 args.value)
    · exact access.codeDisjoint
    · simpa [premise, coreStoreNextState, tryStepStoreAfterIncrement] using loaded
  have codeFinal : Artifacts.programImage.fileBytesLoadedFaithfully finalMachine.mem := by
    exact codeAfterWrite
  have endpointRun : EndpointStep fromStep before after := by
    apply endpointStep_sail fromStep before finalMachine
    · intro pc observed
      change before.machine.regs.get? PC = some pc at observed
      rw [atPc] at observed
      cases Option.some.inj observed
      simpa [BareMetalHostTransitionPc, readContextReturnPc, writeContextReturnPc,
        exitContextStorePc] using observed
    · exact run
  refine ⟨1, after, (), by omega, by simp [memWriteIntContract], ?_, ?_, trivial, ?_⟩
  · exact .step fromStep 0 (BitVec.ofNat 64 0x15d18) before after after (by
      unfold EndpointPc
      exact atPc)
      (by unfold pcInList; native_decide) endpointRun (.refl (fromStep + 1) after)
  · refine ⟨BitVec.ofNat 64 0x15d1c, ?_, ?_⟩
    · unfold EndpointPc
      change (((afterWrite.regs.insert PC
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x15d18) 4)).insert minstret
          (Sail.BitVec.addInt retired 1)).get? PC) = some (BitVec.ofNat 64 0x15d1c)
      rw [Std.ExtDHashMap.get?_insert]
      simp
      rfl
    · unfold pcInList
      native_decide
  · refine ⟨?_, valueRep, rfl, rfl, rfl, rfl, memoryFrame,
      writes.agree memWriteIntPreserved_disjoint, ?_, codeFinal, ?_⟩
    · change (((afterWrite.regs.insert PC
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x15d18) 4)).insert minstret
          (Sail.BitVec.addInt retired 1)).get? PC) = some (BitVec.ofNat 64 0x15d1c)
      rw [Std.ExtDHashMap.get?_insert]
      simp
      rfl
    · simpa [finalMachine, tryStepStoreAfterRetired] using
        tryStepControlFlowAfterRetired_retired_present afterWrite
          (Sail.BitVec.addInt (BitVec.ofNat 64 0x15d18) 4) retired
    · simpa [after, finalMachine, afterWrite, premise, tryStepStoreAfterRetired,
        tryStepStoreAfterTick, coreStoreNextState, tryStepStoreAfterIncrement] using
        AuxStateAgree.storeRetirement before.machine (BitVec.ofNat 64 0x15d18) retired
          args.address (BitVec.ofNat 64 args.value)

/-- `fi:1:45b2` is a thin use of the shared exact one-step theorem. -/
theorem proposed_memWriteInt_proved : Proposed_mem_writeInt_fi_1_45b2_Contract :=
  ⟨1, by native_decide, memWriteIntContract_implements⟩

end BinaryFv.Zesu.Staging
