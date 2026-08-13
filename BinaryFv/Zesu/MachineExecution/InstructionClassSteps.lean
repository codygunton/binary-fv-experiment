import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level1Contracts
import BinaryFv.RiscV.Instruction.RegisterRuns
import BinaryFv.RiscV.Instruction.Execute.DataAddress
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.RiscV.Step.RegisterWrite
import BinaryFv.RiscV.Step.Store
import BinaryFv.RiscV.Proof.ImageFetch

/-!
# Shared instruction-class steps for the Zesu endpoint

These theorems spend the endpoint-wide configured-machine and exact program-image facts once. A
concrete Zesu instruction supplies only its literal bytes, decoded instruction, and generated Sail
execution. Straight-line compositions consume the resulting `afterRegisterWrite` shape through
`Seg`, rather than rebuilding fetch, counter, and retirement plumbing at every PC.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.Binary BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register
open MemoryAccessType mem_payload page_based_mem_type

/-- Data-side premises for an exact generated double-word store. -/
structure ConfiguredDwordStoreAccess (state afterWrite : State) (pc : BitVec 64)
    (imm : BitVec 12) (rs1 rs2 : regidx) where
  destination : BitVec 64
  mstatusBits : BitVec 64
  dataBits : BitVec 64
  mstatusRead : (coreStoreNextState (tryStepStoreAfterIncrement state) pc).regs.get? mstatus =
    some mstatusBits
  privilegeRead :
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc).regs.get? cur_privilege =
      some .Machine
  mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1
  dataRead : Runs (rX_bits rs2) (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc) dataBits
  addressRead : Runs
    (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Store Data) 8)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
    (.Ext_DataAddr_OK (virtaddr.Virtaddr destination))
  aligned : is_aligned_vaddr (virtaddr.Virtaddr destination) 8 = true
  physicalAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
    (physaddr.Physaddr destination) 8 false)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc) none
  noMMIO : Runs (within_mmio_writable (physaddr.Physaddr destination) 8)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc) false
  write : Runs (PreSail.writeBytes (n := 8) destination.toNat dataBits)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc) afterWrite true

/-- Retire one exact fall-through instruction whose Sail execution writes one register. -/
theorem configuredRegisterWriteStep (stepNo pc : Nat) (state : State)
    (destination : Register) (value : RegisterType destination)
    (decoded : instruction) (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) decoded)
    (execute : Runs (execute decoded)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 pc)).regs.insert destination value }
      (.Retire_Success ()))
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (destinationNotNextPc : destination ≠ nextPC := by decide)
    (destinationNotHart : destination ≠ hart_state := by decide)
    (destinationNotIncrement : destination ≠ minstret_increment := by decide)
    (destinationNotRetired : destination ≠ minstret := by decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination value) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc trivial
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc pcFits loadedAfter
    byte0 byte1 byte2 byte3 read0 read1 read2 read3
  let afterExec : State :=
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 pc)).regs.insert destination value }
  have nextPc : afterExec.regs.get? nextPC =
      some (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) := by
    simp [afterExec, coreControlFlowNextState, Std.ExtDHashMap.get?_insert,
      destinationNotNextPc]
  have hart : afterExec.regs.get? hart_state =
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state := by
    simp [afterExec, coreControlFlowNextState, Std.ExtDHashMap.get?_insert,
      destinationNotHart]
  have increment : afterExec.regs.get? minstret_increment =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment := by
    simp [afterExec, coreControlFlowNextState, Std.ExtDHashMap.get?_insert,
      destinationNotIncrement]
  have retiredRead : afterExec.regs.get? minstret =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret := by
    simp [afterExec, coreControlFlowNextState, Std.ExtDHashMap.get?_insert,
      destinationNotRetired]
  have run := tryStepFallThroughRetires stepNo state afterExec (BitVec.ofNat 64 pc) retired
    0 0 (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
    (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
    decoded platform noMMIO bytes interrupts base decode notExpected (by simpa [afterExec] using execute)
    nextPc hart increment retiredRead counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
    counters.2.2.2.2.1 counters.2.2.2.2.2
  exact ⟨retired, by simpa [afterRegisterWrite, afterExec] using run⟩

/-- Retire one exact generated double-word store. -/
theorem configuredDwordStoreStep (stepNo pc : Nat) (state afterWrite : State)
    (imm : BitVec 12) (rs1 rs2 : regidx) (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (imm, rs2, rs1, 8)))
    (access : ConfiguredDwordStoreAccess state afterWrite (BitVec.ofNat 64 pc) imm rs1 rs2)
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired afterWrite (BitVec.ofNat 64 pc) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noFetchMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc trivial
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepStoreAfterIncrement state).mem := by
    simpa [tryStepStoreAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepStoreAfterIncrement state) pc pcFits loadedAfter byte0 byte1 byte2 byte3
      read0 read1 read2 read3
  refine ⟨retired, tryStepStoreDwordRetires stepNo state afterWrite (BitVec.ofNat 64 pc)
    imm rs2 rs1 access.destination access.mstatusBits access.dataBits retired 0 0
    (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
    (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) ?_ ?_ bytes ?_ base decode ?_
    access.mstatusRead access.privilegeRead access.mprvZero access.dataRead access.addressRead
    access.aligned access.physicalAccess access.noMMIO access.write counters.1 counters.2.1
    counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2⟩
  · simpa [tryStepStoreAfterIncrement, tryStepControlFlowAfterIncrement] using platform
  · simpa [tryStepStoreAfterIncrement, tryStepControlFlowAfterIncrement] using noFetchMMIO
  · simpa [tryStepStoreAfterIncrement, tryStepControlFlowAfterIncrement] using interrupts
  · simpa [tryStepStoreAfterIncrement, tryStepControlFlowAfterIncrement] using notExpected

end BinaryFv.Zesu.MachineExecution
