import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level1Contracts
import BinaryFv.RiscV.Instruction.RegisterRuns
import BinaryFv.RiscV.Instruction.Execute.DataAddress
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.RiscV.Step.RegisterWrite
import BinaryFv.RiscV.Step.Store
import BinaryFv.RiscV.Step.AbstractPremise
import BinaryFv.RiscV.Step.LandingPad
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Instruction.DecodeTactic

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

private theorem configuredOfNatAlignedEight (address : Nat) (fits : address < 2 ^ 64)
    (aligned : address % 8 = 0) :
    is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 address)) 8 = true ∧
      is_aligned_paddr (physaddr.Physaddr (BitVec.ofNat 64 address)) 8 = true := by
  have tmodEight : ((address : Nat) : Int).tmod 8 = 0 := congrArg Int.ofNat aligned
  constructor
  · unfold is_aligned_vaddr
    simp only
    change ((((BitVec.ofNat 64 address).toNat : Int).tmod 8) == 0) = true
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    simpa [tmodEight]
  · unfold is_aligned_paddr
    simp only
    change ((((BitVec.ofNat 64 address).toNat : Int).tmod 8) == 0) = true
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    simpa [tmodEight]

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

/-- Retire one exact generated double-word load from a represented little-endian word. -/
theorem configuredDwordLoadStep (stepNo pc : Nat) (state : State)
    (imm : BitVec 12) (rs1 rd : regidx) (destination : Register)
    (baseAddress offset value : Nat) (result : RegisterType destination)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (rep : UIntRep 8 state.mem (baseAddress + offset) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 8)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 8)
    (sumFits : baseAddress + offset < 2 ^ 64)
    (aligned : (baseAddress + offset) % 8 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 baseAddress + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (baseAddress + offset))
    (baseRun : ∀ premise, Runs (rX_bits rs1) premise premise (BitVec.ofNat 64 baseAddress))
    (writeRun : ∀ premise, Runs (wX_bits rd (BitVec.ofNat 64 value)) premise
      { premise with regs := premise.regs.insert destination result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, rs1, rd, false, 8)))
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
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨seccfgBits, seccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise := (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have addressRun : Runs
      (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 8)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (baseAddress + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .load premise rs1 8
      (BitVec.ofNat 64 baseAddress) (sign_extend (m := 64) imm) mstatusBits seccfgBits
      (baseRun premise) mstatusPremise privilegePremise mprvZero
      ((agree mseccfg (by simp [platformPreserved])).trans seccfgRead) pmmDisabled
  have physical := phys_access_check_machine_load_allowed premise
    (BitVec.ofNat 64 (baseAddress + offset)) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (loadPmaAllows_of_agree agree pma)
    (configuredOfNatAlignedEight (baseAddress + offset) sumFits aligned).2
  have noMMIO := loadMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (baseAddress + offset)) 8 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  have bytes : ∀ index (bound :
      index < (BinaryFv.RiscV.Sep.leBytes 8 (BitVec.ofNat 64 value)).length),
      premise.mem.get? ((BitVec.ofNat 64 (baseAddress + offset)).toNat + index) =
        some (BinaryFv.RiscV.Sep.leBytes 8 (BitVec.ofNat 64 value))[index] := by
    intro index bound
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sumFits]
    simpa [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using
      rep.leBytes index (by simpa only [BinaryFv.RiscV.Sep.leBytes_length] using bound)
  have execute : Runs (execute (.LOAD (imm, rs1, rd, false, 8))) premise
      { premise with regs := premise.regs.insert destination result } (.Retire_Success ()) := by
    change Runs (execute_LOAD imm rs1 rd false 8) _ _ _
    exact execute_LOAD_ld_run premise _ imm rs1 rd
      (BitVec.ofNat 64 (baseAddress + offset)) mstatusBits (BitVec.ofNat 64 value)
      mstatusPremise privilegePremise mprvZero addressRun
      (configuredOfNatAlignedEight (baseAddress + offset) sumFits aligned).1 physical noMMIO bytes
      (writeRun premise)
  exact configuredRegisterWriteStep stepNo pc state destination result
    (.LOAD (imm, rs1, rd, false, 8)) byte0 byte1 byte2 byte3 configured atPc loaded decode execute
    (pcFits := pcFits) (base := base) (destinationNotNextPc := destinationNotNextPc)
    (destinationNotHart := destinationNotHart) (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3)

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

/-- Retire a production unconditional `j target` (`jal x0, target`) from a configured state. -/
theorem configuredJStep (stepNo pc target : Nat) (state : State) (imm : BitVec 21)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (imm, zreg)))
    (targetEq : BitVec.ofNat 64 pc + sign_extend (m := 64) imm = BitVec.ofNat 64 target)
    (aligned0 : Sail.BitVec.access
      (BitVec.ofNat 64 pc + sign_extend (m := 64) imm) 0 = 0#1)
    (aligned1 : Sail.BitVec.access
      (BitVec.ofNat 64 pc + sign_extend (m := 64) imm) 1 = 0#1)
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
          (BitVec.ofNat 64 target))
        (BitVec.ofNat 64 target) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc trivial
  rcases platform with ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeAfter,
    pcLow0, pcLow1, alignedVirt, alignedPhys, pmpDisabled, pmaAllowed⟩
  have platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 pc) :=
    ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeAfter,
      pcLow0, pcLow1, alignedVirt, alignedPhys, pmpDisabled, pmaAllowed⟩
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc pcFits loadedAfter byte0 byte1 byte2 byte3
      read0 read1 read2 read3
  have pcAtPremise : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 pc)).regs.get? PC = some (BitVec.ofNat 64 pc) := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC PC
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) (by decide)).trans pcRead
  have linkRead : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) := by
    unfold get_next_pc
    exact readReg_run _ nextPC _ (by simp [coreControlFlowNextState])
  have pcRun : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (BitVec.ofNat 64 pc) := readReg_run _ PC _ pcAtPremise
  have misaAtPremise : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 pc)).regs.get? misa = some misaBits := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC misa
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) (by decide)).trans misaRead
  have zca := currentlyEnabledZca_run _ misaBits misaAtPremise
  refine ⟨retired, ?_⟩
  simpa only [targetEq] using tryStepJRetires stepNo state (BitVec.ofNat 64 pc)
    (BitVec.ofNat 64 pc) retired imm 0 0 (BitVec.ofNat 8 byte0.toNat)
    (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
    (BitVec.ofNat 8 byte3.toNat) (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4)
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected
    linkRead pcRun aligned0 aligned1 zca counters.1 counters.2.1
    counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2

/-- Retire a production `ret` (`jalr x0, 0(ra)`) from a configured endpoint state. -/
theorem configuredRetStep (stepNo pc : Nat) (state : State) (returnAddress : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (link : state.regs.get? x1 = some returnAddress)
    (targetAligned : Sail.BitVec.access returnAddress 1 = 0#1)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (read0 : Artifacts.programImage.readFileByte? pc = some 0x67 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some 0x80 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some 0x00 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some 0x00 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
          (Sail.BitVec.update returnAddress 0 0#1))
        (Sail.BitVec.update returnAddress 0 0#1) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc trivial
  rcases platform with ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeAfter,
    pcLow0, pcLow1, alignedVirt, alignedPhys, pmpDisabled, pmaAllowed⟩
  have platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 pc) :=
    ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeAfter,
      pcLow0, pcLow1, alignedVirt, alignedPhys, pmpDisabled, pmaAllowed⟩
  obtain ⟨mseccfgBits, mseccfgRead, _⟩ := configured.seccfgPresent
  have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some mseccfgBits := by
    calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
      _ = some mseccfgBits := mseccfgRead
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc pcFits loadedAfter 0x67 0x80 0x00 0x00
      read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x67#8 0x80#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0#12, .Regidx 1#5, zreg)) := by
    decode_run
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have linkAtPremise : premise.regs.get? x1 = some returnAddress :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x1 (by decide) |>.trans link
  have returnRead : Runs (rX_bits (.Regidx 1#5)) premise premise returnAddress :=
    rX_x1_run premise returnAddress linkAtPremise
  have nextRead : Runs (get_next_pc ()) premise premise
      (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) := by
    unfold get_next_pc
    exact readReg_run premise nextPC _ (by simp [premise, coreControlFlowNextState])
  have helpElp := updateElpState_run_atStepPremise state (BitVec.ofNat 64 pc)
    (.Regidx 1#5) mseccfgBits configured.normal.2.1 mseccfgRead
  have misaAtPremise : premise.regs.get? misa = some misaBits :=
    (by
      calc
        premise.regs.get? misa = (tryStepControlFlowAfterIncrement state).regs.get? misa := by
          simpa [premise, coreControlFlowNextState] using
            writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC misa
              (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) (by decide)
        _ = some misaBits := misaRead)
  have zca := currentlyEnabledZca_run premise misaBits misaAtPremise
  exact ⟨retired, tryStepRetRetires stepNo state (BitVec.ofNat 64 pc) retired (.Regidx 1#5)
    (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) returnAddress 0 0
    0x67#8 0x80#8 0x00#8 0x00#8 (_get_Misa_C misaBits == 1#1)
    platform noMMIO bytes interrupts (by unfold BaseInstructionEncoding; decide) decode notExpected
    helpElp nextRead returnRead
    targetAligned zca counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
    counters.2.2.2.2.1 counters.2.2.2.2.2⟩

end BinaryFv.Zesu.MachineExecution
