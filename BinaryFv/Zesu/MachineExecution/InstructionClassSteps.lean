import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.HostExecution
import BinaryFv.RiscV.Instruction.RegisterRuns
import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Instruction.Execute.DataAddress
import BinaryFv.RiscV.Instruction.Execute.StoreByte
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

/-- Artifact-only facts shared by concrete instruction proofs. Bundling them makes one native
decision check the instruction bytes, PC classification, and fall-through arithmetic together. -/
abbrev ExactInstructionSite (pc : Nat) (byte0 byte1 byte2 byte3 : UInt8) : Prop :=
  pc < 2 ^ 64 ∧ Artifacts.programImage.readFileByte? pc = some byte0 ∧
  Artifacts.programImage.readFileByte? (pc + 1) = some byte1 ∧
  Artifacts.programImage.readFileByte? (pc + 2) = some byte2 ∧
  Artifacts.programImage.readFileByte? (pc + 3) = some byte3 ∧
  Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 (pc + 4) ∧
  pc % 4 = 0

namespace ExactInstructionSite

theorem pcFits (h : ExactInstructionSite pc byte0 byte1 byte2 byte3) : pc < 2 ^ 64 := h.1
theorem read0 (h : ExactInstructionSite pc byte0 byte1 byte2 byte3) :
    Artifacts.programImage.readFileByte? pc = some byte0 := h.2.1
theorem read1 (h : ExactInstructionSite pc byte0 byte1 byte2 byte3) :
    Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := h.2.2.1
theorem read2 (h : ExactInstructionSite pc byte0 byte1 byte2 byte3) :
    Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := h.2.2.2.1
theorem read3 (h : ExactInstructionSite pc byte0 byte1 byte2 byte3) :
    Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := h.2.2.2.2.1
theorem advance (h : ExactInstructionSite pc byte0 byte1 byte2 byte3) :
    Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 (pc + 4) := h.2.2.2.2.2.1
theorem pcAligned (h : ExactInstructionSite pc byte0 byte1 byte2 byte3) : pc % 4 = 0 :=
  h.2.2.2.2.2.2

end ExactInstructionSite

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

private theorem configuredOfNatAlignedFour (address : Nat) (fits : address < 2 ^ 64)
    (aligned : address % 4 = 0) :
    is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 address)) 4 = true ∧
      is_aligned_paddr (physaddr.Physaddr (BitVec.ofNat 64 address)) 4 = true := by
  have tmodFour : ((address : Nat) : Int).tmod 4 = 0 := congrArg Int.ofNat aligned
  constructor
  · unfold is_aligned_vaddr
    simp only
    change ((((BitVec.ofNat 64 address).toNat : Int).tmod 4) == 0) = true
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    simpa [tmodFour]
  · unfold is_aligned_paddr
    simp only
    change ((((BitVec.ofNat 64 address).toNat : Int).tmod 4) == 0) = true
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    simpa [tmodFour]

private theorem configuredOfNatAlignedTwo (address : Nat) (fits : address < 2 ^ 64)
    (aligned : address % 2 = 0) :
    is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 address)) 2 = true ∧
      is_aligned_paddr (physaddr.Physaddr (BitVec.ofNat 64 address)) 2 = true := by
  have tmodTwo : ((address : Nat) : Int).tmod 2 = 0 := congrArg Int.ofNat aligned
  constructor
  · unfold is_aligned_vaddr
    simp only
    change ((((BitVec.ofNat 64 address).toNat : Int).tmod 2) == 0) = true
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    simpa [tmodTwo]
  · unfold is_aligned_paddr
    simp only
    change ((((BitVec.ofNat 64 address).toNat : Int).tmod 2) == 0) = true
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    simpa [tmodTwo]

private theorem configuredOfNatAlignedOne (address : Nat) :
    is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 address)) 1 = true ∧
      is_aligned_paddr (physaddr.Physaddr (BitVec.ofNat 64 address)) 1 = true := by
  constructor <;> simp [is_aligned_vaddr, is_aligned_paddr]

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
    (pcAligned : pc % 4 = 0 := by native_decide)
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
    configured.stepContext (BitVec.ofNat 64 pc) atPc ⟨by simpa using pcAligned, ⟨byte0, by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFits] using read0⟩⟩
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

/-- Retire one exact generated unsigned-byte load from a represented byte. -/
theorem configuredByteLoadStep (stepNo pc : Nat) (state : State)
    (imm : BitVec 12) (rs1 rd : regidx) (destination : Register)
    (baseAddress offset value : Nat) (result : RegisterType destination)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (rep : UIntRep 1 state.mem (baseAddress + offset) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (sumFits : baseAddress + offset < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 baseAddress + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (baseAddress + offset))
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise (BitVec.ofNat 64 baseAddress))
    (writeRun : ∀ premise,
      Runs (wX_bits rd (zero_extend (m := 64) (BitVec.ofNat 8 value))) premise
        { premise with regs := premise.regs.insert destination result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, rs1, rd, true, 1)))
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (pcAligned : pc % 4 = 0 := by native_decide)
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
      (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (baseAddress + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .load premise rs1 1
      (BitVec.ofNat 64 baseAddress) (sign_extend (m := 64) imm) mstatusBits seccfgBits
      (baseRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)))
      mstatusPremise privilegePremise mprvZero
      ((agree mseccfg (by simp [platformPreserved])).trans seccfgRead) pmmDisabled
  have physical := phys_access_check_machine_load_allowed premise
    (BitVec.ofNat 64 (baseAddress + offset)) 1
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (loadPmaAllows_of_agree agree pma) (configuredOfNatAlignedOne (baseAddress + offset)).2
  have noMMIO := loadMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (baseAddress + offset)) 1 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  have bytes : ∀ index (bound :
      index < (BinaryFv.RiscV.Sep.leBytes 1 (BitVec.ofNat 8 value)).length),
      premise.mem.get? ((BitVec.ofNat 64 (baseAddress + offset)).toNat + index) =
        some (BinaryFv.RiscV.Sep.leBytes 1 (BitVec.ofNat 8 value))[index] := by
    intro index bound
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sumFits]
    simpa [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using
      rep.leBytes index (by simpa only [BinaryFv.RiscV.Sep.leBytes_length] using bound)
  have execute : Runs (execute (.LOAD (imm, rs1, rd, true, 1))) premise
      { premise with regs := premise.regs.insert destination result } (.Retire_Success ()) := by
    change Runs (execute_LOAD imm rs1 rd true 1) _ _ _
    exact execute_LOAD_lbu_run premise _ imm rs1 rd
      (BitVec.ofNat 64 (baseAddress + offset)) mstatusBits (BitVec.ofNat 8 value)
      mstatusPremise privilegePremise mprvZero addressRun
      (configuredOfNatAlignedOne (baseAddress + offset)).1 physical noMMIO bytes
      (writeRun premise)
  exact configuredRegisterWriteStep stepNo pc state destination result
    (.LOAD (imm, rs1, rd, true, 1)) byte0 byte1 byte2 byte3 configured atPc loaded decode execute
    (pcFits := pcFits) (pcAligned := pcAligned) (base := base)
    (destinationNotNextPc := destinationNotNextPc)
    (destinationNotHart := destinationNotHart) (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3)

/-- Retire one exact generated signed-byte load from a represented byte. -/
theorem configuredSignedByteLoadStep (stepNo pc : Nat) (state : State)
    (imm : BitVec 12) (rs1 rd : regidx) (destination : Register)
    (baseAddress offset value : Nat) (result : RegisterType destination)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (rep : UIntRep 1 state.mem (baseAddress + offset) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (sumFits : baseAddress + offset < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 baseAddress + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (baseAddress + offset))
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise (BitVec.ofNat 64 baseAddress))
    (writeRun : ∀ premise,
      Runs (wX_bits rd (sign_extend (m := 64) (BitVec.ofNat 8 value))) premise
        { premise with regs := premise.regs.insert destination result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, rs1, rd, false, 1)))
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (pcAligned : pc % 4 = 0 := by native_decide)
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
      (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (baseAddress + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .load premise rs1 1
      (BitVec.ofNat 64 baseAddress) (sign_extend (m := 64) imm) mstatusBits seccfgBits
      (baseRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)))
      mstatusPremise privilegePremise mprvZero
      ((agree mseccfg (by simp [platformPreserved])).trans seccfgRead) pmmDisabled
  have physical := phys_access_check_machine_load_allowed premise
    (BitVec.ofNat 64 (baseAddress + offset)) 1
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (loadPmaAllows_of_agree agree pma) (configuredOfNatAlignedOne (baseAddress + offset)).2
  have noMMIO := loadMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (baseAddress + offset)) 1 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  have bytes : ∀ index (bound :
      index < (BinaryFv.RiscV.Sep.leBytes 1 (BitVec.ofNat 8 value)).length),
      premise.mem.get? ((BitVec.ofNat 64 (baseAddress + offset)).toNat + index) =
        some (BinaryFv.RiscV.Sep.leBytes 1 (BitVec.ofNat 8 value))[index] := by
    intro index bound
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sumFits]
    simpa [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using
      rep.leBytes index (by simpa only [BinaryFv.RiscV.Sep.leBytes_length] using bound)
  have execute : Runs (execute (.LOAD (imm, rs1, rd, false, 1))) premise
      { premise with regs := premise.regs.insert destination result } (.Retire_Success ()) := by
    change Runs (execute_LOAD imm rs1 rd false 1) _ _ _
    exact execute_LOAD_lb_run premise _ imm rs1 rd
      (BitVec.ofNat 64 (baseAddress + offset)) mstatusBits (BitVec.ofNat 8 value)
      mstatusPremise privilegePremise mprvZero addressRun
      (configuredOfNatAlignedOne (baseAddress + offset)).1 physical noMMIO bytes
      (writeRun premise)
  exact configuredRegisterWriteStep stepNo pc state destination result
    (.LOAD (imm, rs1, rd, false, 1)) byte0 byte1 byte2 byte3 configured atPc loaded decode execute
    (pcFits := pcFits) (pcAligned := pcAligned) (base := base)
    (destinationNotNextPc := destinationNotNextPc)
    (destinationNotHart := destinationNotHart) (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3)

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
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise (BitVec.ofNat 64 baseAddress))
    (writeRun : ∀ premise, Runs (wX_bits rd (BitVec.ofNat 64 value)) premise
      { premise with regs := premise.regs.insert destination result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, rs1, rd, false, 8)))
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (pcAligned : pc % 4 = 0 := by native_decide)
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
      (baseRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)))
      mstatusPremise privilegePremise mprvZero
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
    (pcFits := pcFits) (pcAligned := pcAligned) (base := base)
    (destinationNotNextPc := destinationNotNextPc)
    (destinationNotHart := destinationNotHart) (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3)

/-- Retire one exact generated signed word load from represented little-endian bytes. -/
theorem configuredWordLoadStep (stepNo pc : Nat) (state : State)
    (imm : BitVec 12) (rs1 rd : regidx) (destination : Register)
    (baseAddress offset value : Nat) (result : RegisterType destination)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (rep : UIntRep 4 state.mem (baseAddress + offset) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 4)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 4)
    (sumFits : baseAddress + offset < 2 ^ 64)
    (aligned : (baseAddress + offset) % 4 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 baseAddress + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (baseAddress + offset))
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise (BitVec.ofNat 64 baseAddress))
    (writeRun : ∀ premise, Runs (wX_bits rd
      (extend_value false (BitVec.ofNat 32 value))) premise
      { premise with regs := premise.regs.insert destination result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, rs1, rd, false, 4)))
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (pcAligned : pc % 4 = 0 := by native_decide)
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
      (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 4)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (baseAddress + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .load premise rs1 4
      (BitVec.ofNat 64 baseAddress) (sign_extend (m := 64) imm) mstatusBits seccfgBits
      (baseRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)))
      mstatusPremise privilegePremise mprvZero
      ((agree mseccfg (by simp [platformPreserved])).trans seccfgRead) pmmDisabled
  have physical := phys_access_check_machine_load_allowed premise
    (BitVec.ofNat 64 (baseAddress + offset)) 4
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (loadPmaAllows_of_agree agree pma)
    (configuredOfNatAlignedFour (baseAddress + offset) sumFits aligned).2
  have noMMIO := loadMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (baseAddress + offset)) 4 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  have bytes : ∀ index (bound :
      index < (BinaryFv.RiscV.Sep.leBytes 4 (BitVec.ofNat 32 value)).length),
      premise.mem.get? ((BitVec.ofNat 64 (baseAddress + offset)).toNat + index) =
        some (BinaryFv.RiscV.Sep.leBytes 4 (BitVec.ofNat 32 value))[index] := by
    intro index bound
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sumFits]
    simpa [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using
      rep.leBytes index (by simpa only [BinaryFv.RiscV.Sep.leBytes_length] using bound)
  have read := vmem_read_word_from_bytes_run premise rs1 (sign_extend (m := 64) imm)
    (BitVec.ofNat 64 (baseAddress + offset)) mstatusBits (BitVec.ofNat 32 value)
    mstatusPremise privilegePremise mprvZero addressRun
    (configuredOfNatAlignedFour (baseAddress + offset) sumFits aligned).1 physical noMMIO bytes
  have execute : Runs (execute (.LOAD (imm, rs1, rd, false, 4))) premise
      { premise with regs := premise.regs.insert destination result } (.Retire_Success ()) :=
    execute_LOAD_lw_run premise _ imm rs1 rd (BitVec.ofNat 32 value) read (writeRun premise)
  exact configuredRegisterWriteStep stepNo pc state destination result
    (.LOAD (imm, rs1, rd, false, 4)) byte0 byte1 byte2 byte3 configured atPc loaded decode execute
    (pcFits := pcFits) (pcAligned := pcAligned) (base := base)
    (destinationNotNextPc := destinationNotNextPc)
    (destinationNotHart := destinationNotHart) (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3)

/-- Retire one exact `lw offset(sp)` from a represented stack word. -/
theorem configuredStackWordLoadStep (stepNo pc stackPointer offset value : Nat)
    (state : State) (imm : BitVec 12) (rd : regidx) (destination : Register)
    (result : RegisterType destination) (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (rep : UIntRep 4 state.mem (stackPointer + offset) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 4)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 4)
    (sumFits : stackPointer + offset < 2 ^ 64)
    (aligned : (stackPointer + offset) % 4 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 stackPointer + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (stackPointer + offset))
    (writeRun : ∀ premise, Runs (wX_bits rd
      (extend_value false (BitVec.ofNat 32 value))) premise
      { premise with regs := premise.regs.insert destination result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, .Regidx 2#5, rd, false, 4)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide)
    (destinationNotNextPc : destination ≠ nextPC := by decide)
    (destinationNotHart : destination ≠ hart_state := by decide)
    (destinationNotIncrement : destination ≠ minstret_increment := by decide)
    (destinationNotRetired : destination ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  exact configuredWordLoadStep stepNo pc state imm (.Regidx 2#5) rd destination
    stackPointer offset value result byte0 byte1 byte2 byte3 configured atPc rep pma notMMIO
    sumFits aligned loaded addressEq
    (fun premise writes => rX_x2_run premise (BitVec.ofNat 64 stackPointer)
      ((writes.get x2 (by decide)).trans stackRead))
    writeRun decode (pcFits := site.pcFits) (pcAligned := site.pcAligned) (base := base)
    (destinationNotNextPc := destinationNotNextPc)
    (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)

/-- A signed word load preserves the original low 32 bits. -/
theorem signedWordLowBits (value : BitVec 32) :
    BitVec.setWidth 32 (extend_value false value) = value := by
  simp only [extend_value, Bool.false_eq_true, ↓reduceIte, sign_extend,
    Sail.BitVec.signExtend]
  bv_decide

/-- Retire one exact `ld offset(sp)` from a represented stack word. -/
theorem configuredStackDwordLoadStep (stepNo pc stackPointer offset value : Nat)
    (state : State) (imm : BitVec 12) (rd : regidx) (destination : Register)
    (result : RegisterType destination) (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (rep : UIntRep 8 state.mem (stackPointer + offset) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 8)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 8)
    (sumFits : stackPointer + offset < 2 ^ 64)
    (aligned : (stackPointer + offset) % 8 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 stackPointer + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (stackPointer + offset))
    (writeRun : ∀ premise, Runs (wX_bits rd (BitVec.ofNat 64 value)) premise
      { premise with regs := premise.regs.insert destination result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, .Regidx 2#5, rd, false, 8)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide)
    (destinationNotNextPc : destination ≠ nextPC := by decide)
    (destinationNotHart : destination ≠ hart_state := by decide)
    (destinationNotIncrement : destination ≠ minstret_increment := by decide)
    (destinationNotRetired : destination ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  exact configuredDwordLoadStep stepNo pc state imm (.Regidx 2#5) rd destination
    stackPointer offset value result byte0 byte1 byte2 byte3 configured atPc rep pma notMMIO
    sumFits aligned loaded addressEq
    (fun premise writes =>
      rX_x2_run premise (BitVec.ofNat 64 stackPointer)
        ((writes.get x2 (by decide)).trans stackRead))
    writeRun decode (pcFits := site.pcFits) (pcAligned := site.pcAligned) (base := base)
    (destinationNotNextPc := destinationNotNextPc)
    (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)

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
    (pcAligned : pc % 4 = 0 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired afterWrite (BitVec.ofNat 64 pc) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noFetchMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc ⟨by simpa using pcAligned, ⟨byte0, by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFits] using read0⟩⟩
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

/-- Retire one exact generated immediate arithmetic instruction that writes one register. -/
theorem configuredITypeRegisterStep (stepNo pc : Nat) (state : State) (immediate : BitVec 12)
    (rs1 rd : regidx) (destination : Register) (operation : iop) (source : BitVec 64)
    (result : RegisterType destination)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise source)
    (writeRun : ∀ premise, Runs (wX_bits rd
      (iTypeResult operation immediate source)) premise
      { premise with regs := premise.regs.insert destination result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (immediate, rs1, rd, operation)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have execute : Runs (execute (.ITYPE (immediate, rs1, rd, operation))) premise
      { premise with regs := premise.regs.insert destination result } (.Retire_Success ()) := by
    change Runs (execute_ITYPE immediate rs1 rd operation) _ _ _
    exact execute_ITYPE_run premise _ immediate rs1 rd operation source
      (baseRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)))
      (writeRun premise)
  exact configuredRegisterWriteStep stepNo pc state destination result
    (.ITYPE (immediate, rs1, rd, operation)) byte0 byte1 byte2 byte3
    configured atPc loaded decode
    execute (pcFits := site.pcFits) (pcAligned := site.pcAligned) (base := base)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)
    (destinationNotNextPc := destinationNotNextPc) (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired)

/-- Retire one exact generated immediate arithmetic instruction that writes `a0`. -/
theorem configuredITypeX10Step (stepNo pc : Nat) (state : State) (immediate : BitVec 12)
    (rs1 : regidx) (operation : iop) (source result : BitVec 64)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : result = iTypeResult operation immediate source)
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise source)
    (writeRun : ∀ premise, Runs (wX_bits (.Regidx 10#5)
      (iTypeResult operation immediate source)) premise
      { premise with regs := premise.regs.insert x10 result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (immediate, rs1, .Regidx 10#5, operation)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10 result) false :=
  configuredITypeRegisterStep stepNo pc state immediate rs1 (.Regidx 10#5) x10 operation
    source result byte0 byte1 byte2 byte3 configured atPc loaded baseRun writeRun decode site base
    (by decide) (by decide) (by decide) (by decide)

/-- Retire one exact generated immediate arithmetic instruction that writes `a1`. -/
theorem configuredITypeX11Step (stepNo pc : Nat) (state : State) (immediate : BitVec 12)
    (rs1 : regidx) (operation : iop) (source result : BitVec 64)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise source)
    (writeRun : ∀ premise, Runs (wX_bits (.Regidx 11#5)
      (iTypeResult operation immediate source)) premise
      { premise with regs := premise.regs.insert x11 result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (immediate, rs1, .Regidx 11#5, operation)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x11 result) false :=
  configuredITypeRegisterStep stepNo pc state immediate rs1 (.Regidx 11#5) x11 operation
    source result byte0 byte1 byte2 byte3 configured atPc loaded baseRun writeRun decode site base
    (by decide) (by decide) (by decide) (by decide)

/-- Retire one exact `addi sp, sp, immediate`. -/
theorem configuredAddiX2Step (stepNo pc : Nat) (state : State) (immediate : BitVec 12)
    (source result : BitVec 64) (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (atSource : state.regs.get? x2 = some source)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : result = iTypeResult .ADDI immediate source)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (immediate, .Regidx 2#5, .Regidx 2#5, .ADDI)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x2 result) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have sourceRead : premise.regs.get? x2 = some source :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x2
      (by decide) |>.trans atSource
  have execute : Runs (execute (.ITYPE (immediate, .Regidx 2#5, .Regidx 2#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x2 result } (.Retire_Success ()) := by
    change Runs (execute_ITYPE immediate (.Regidx 2#5) (.Regidx 2#5) .ADDI) _ _ _
    rw [resultEq]
    exact execute_ITYPE_run premise _ immediate (.Regidx 2#5) (.Regidx 2#5) .ADDI source
      (rX_x2_run premise source sourceRead) (wX_x2_run premise _)
  exact configuredRegisterWriteStep stepNo pc state x2 result
    (.ITYPE (immediate, .Regidx 2#5, .Regidx 2#5, .ADDI)) byte0 byte1 byte2 byte3
    configured atPc loaded decode execute (pcFits := site.pcFits) (base := base)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)
    (pcAligned := site.pcAligned)

/-- Normalize a nonwrapping stack subtraction implemented by one `addi sp,sp,-frameSize`. -/
theorem stackSubtractResult (stackPointer frameSize : Nat) (immediate : BitVec 12)
    (lower : frameSize ≤ stackPointer) (upper : stackPointer < 2 ^ 64)
    (sign : sign_extend (m := 64) immediate = BitVec.ofNat 64 (2 ^ 64 - frameSize)) :
    BitVec.ofNat 64 (stackPointer - frameSize) =
      iTypeResult .ADDI immediate (BitVec.ofNat 64 stackPointer) := by
  unfold iTypeResult
  change BitVec.ofNat 64 (stackPointer - frameSize) =
    BitVec.ofNat 64 stackPointer + sign_extend (m := 64) immediate
  rw [sign, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have sum : stackPointer + (2 ^ 64 - frameSize) =
      (stackPointer - frameSize) + 2 ^ 64 := by omega
  rw [sum, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

/-- Normalize the matching nonwrapping `addi sp,sp,frameSize` restoration. -/
theorem stackRestoreResult (stackPointer frameSize : Nat) (immediate : BitVec 12)
    (lower : frameSize ≤ stackPointer) (upper : stackPointer < 2 ^ 64)
    (sign : sign_extend (m := 64) immediate = BitVec.ofNat 64 frameSize) :
    BitVec.ofNat 64 stackPointer =
      iTypeResult .ADDI immediate (BitVec.ofNat 64 (stackPointer - frameSize)) := by
  unfold iTypeResult
  change BitVec.ofNat 64 stackPointer =
    BitVec.ofNat 64 (stackPointer - frameSize) + sign_extend (m := 64) immediate
  rw [sign, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.sub_add_cancel lower,
    Nat.mod_eq_of_lt upper]

/-- Retire one exact `sd offset(base)` with generated base and source register witnesses. -/
theorem configuredBaseDwordStoreStep (stepNo pc baseAddress offset : Nat)
    (state : State) (value : BitVec 64) (imm : BitVec 12) (baseIndex sourceIndex : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 8)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 8)
    (aligned : (baseAddress + offset) % 8 = 0)
    (fits : baseAddress + offset + 8 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 baseAddress + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (baseAddress + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (imm, sourceIndex, baseIndex, 8)))
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits baseIndex) premise premise (BitVec.ofNat 64 baseAddress))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits sourceIndex) premise premise value)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc))
          (baseAddress + offset) value)
        (BitVec.ofNat 64 pc) retired) false := by
  let premise := coreStoreNextState
    (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc)
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise := (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise := (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have addressRun : Runs
      (get_transformed_data_addr baseIndex (sign_extend (m := 64) imm) (Store Data) 8)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (baseAddress + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .store premise
      baseIndex 8 (BitVec.ofNat 64 baseAddress) (sign_extend (m := 64) imm)
      mstatusBits mseccfgBits
      (baseRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)))
      mstatusPremise privilegePremise mprvZero mseccfgPremise pmmDisabled
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 (baseAddress + offset)) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (storePmaAllows_of_agree agree pma)
    (configuredOfNatAlignedEight (baseAddress + offset) (by omega) aligned).2
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (baseAddress + offset)) 8 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 8) premise (baseAddress + offset) value
  have access : ConfiguredDwordStoreAccess state afterWrite (BitVec.ofNat 64 pc) imm
      baseIndex sourceIndex :=
    ⟨_, mstatusBits, _, mstatusPremise, privilegePremise, mprvZero,
      dataRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)), addressRun,
      (configuredOfNatAlignedEight (baseAddress + offset) (by omega) aligned).1,
      physical, noMMIO, by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact writeBytes_run_exact premise (baseAddress + offset) value⟩
  simpa [afterWrite] using configuredDwordStoreStep stepNo pc state afterWrite imm
    baseIndex sourceIndex byte0 byte1 byte2 byte3 configured atPc loaded decode access
    (pcFits := site.pcFits) (pcAligned := site.pcAligned) (base := base)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)

/-- Retire one exact `sd offset(sp)` with a generated source-register witness. -/
theorem configuredStackDwordStoreStep (stepNo pc stackPointer offset : Nat)
    (state : State) (value : BitVec 64) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 8)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 8)
    (aligned : (stackPointer + offset) % 8 = 0)
    (fits : stackPointer + offset + 8 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 stackPointer + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (stackPointer + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (imm, rs2, .Regidx 2#5, 8)))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs2) premise premise value)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc))
          (stackPointer + offset) value)
        (BitVec.ofNat 64 pc) retired) false := by
  let premise := coreStoreNextState
    (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc)
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise := (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise := (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have stackPremise := (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x2
    (by decide) |>.trans stackRead
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 2#5) (sign_extend (m := 64) imm) (Store Data) 8)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (stackPointer + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .store premise
      (.Regidx 2#5) 8 (BitVec.ofNat 64 stackPointer) (sign_extend (m := 64) imm)
      mstatusBits mseccfgBits (rX_x2_run premise (BitVec.ofNat 64 stackPointer) stackPremise)
      mstatusPremise privilegePremise mprvZero mseccfgPremise pmmDisabled
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 (stackPointer + offset)) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (storePmaAllows_of_agree agree pma)
    (configuredOfNatAlignedEight (stackPointer + offset) (by omega) aligned).2
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (stackPointer + offset)) 8 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 8) premise (stackPointer + offset) value
  have access : ConfiguredDwordStoreAccess state afterWrite (BitVec.ofNat 64 pc) imm
      (.Regidx 2#5) rs2 :=
    ⟨_, mstatusBits, _, mstatusPremise, privilegePremise, mprvZero,
      dataRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)), addressRun,
      (configuredOfNatAlignedEight (stackPointer + offset) (by omega) aligned).1,
      physical, noMMIO, by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact writeBytes_run_exact premise (stackPointer + offset) value⟩
  simpa [afterWrite] using configuredDwordStoreStep stepNo pc state afterWrite imm
    (.Regidx 2#5) rs2 byte0 byte1 byte2 byte3 configured atPc loaded decode access
    (pcFits := site.pcFits) (pcAligned := site.pcAligned) (base := base)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)

/-- Retire one exact `sw offset(base)` with generated base and source register witnesses. -/
theorem configuredBaseWordStoreStep (stepNo pc baseAddress offset : Nat)
    (state : State) (value : BitVec 64) (imm : BitVec 12) (baseIndex rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 4)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 4)
    (aligned : (baseAddress + offset) % 4 = 0)
    (fits : baseAddress + offset + 4 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 baseAddress + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (baseAddress + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (imm, rs2, baseIndex, 4)))
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits baseIndex) premise premise (BitVec.ofNat 64 baseAddress))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs2) premise premise value)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 4)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pc))
          (baseAddress + offset) value)
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise := (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise := (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have addressRun : Runs
      (get_transformed_data_addr baseIndex (sign_extend (m := 64) imm) (Store Data) 4)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (baseAddress + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .store premise
      baseIndex 4 (BitVec.ofNat 64 baseAddress) (sign_extend (m := 64) imm)
      mstatusBits mseccfgBits
      (baseRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)))
      mstatusPremise privilegePremise mprvZero mseccfgPremise pmmDisabled
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 (baseAddress + offset)) 4
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (storePmaAllows_of_agree agree pma)
    (configuredOfNatAlignedFour (baseAddress + offset) (by omega) aligned).2
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (baseAddress + offset)) 4 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 4) premise (baseAddress + offset) value
  have write : Runs (PreSail.writeBytes (n := 4)
      (BitVec.ofNat 64 (baseAddress + offset)).toNat
      (Sail.BitVec.extractLsb value 31 0)) premise afterWrite true := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact writeBytes_run_exact premise (baseAddress + offset)
      (Sail.BitVec.extractLsb value 31 0)
  have execute : Runs (execute (.STORE (imm, rs2, baseIndex, 4))) premise afterWrite
      (.Retire_Success ()) := by
    change Runs (execute_STORE imm rs2 baseIndex 4) _ _ _
    exact execute_STORE_word_aligned_run premise afterWrite rs2 baseIndex imm
      (BitVec.ofNat 64 (baseAddress + offset)) mstatusBits value mstatusPremise privilegePremise
      mprvZero (dataRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc))) addressRun
      (configuredOfNatAlignedFour (baseAddress + offset) (by omega) aligned).1 physical noMMIO write
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noFetchMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc
      ⟨by simpa using site.pcAligned, ⟨byte0, by
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt site.pcFits] using site.read0⟩⟩
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc site.pcFits loadedAfter byte0 byte1 byte2 byte3
      site.read0 site.read1 site.read2 site.read3
  have regsEq : afterWrite.regs = premise.regs :=
    writeBytes_preserves_regs _ _ premise afterWrite write
  refine ⟨retired, tryStepFallThroughRetires stepNo state afterWrite (BitVec.ofNat 64 pc) retired
    0 0 (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
    (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
    (.STORE (imm, rs2, baseIndex, 4)) platform noFetchMMIO bytes interrupts base decode
    notExpected execute ?_ ?_ ?_ ?_ counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
    counters.2.2.2.2.1 counters.2.2.2.2.2⟩
  · rw [regsEq]
    simp [premise, coreControlFlowNextState]
  · rw [regsEq]
    simp [premise, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
  · rw [regsEq]
    simp [premise, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
  · rw [regsEq]
    simp [premise, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]

/-- Retire one exact `sw offset(sp)` with a generated source-register witness. -/
theorem configuredStackWordStoreStep (stepNo pc stackPointer offset : Nat)
    (state : State) (value : BitVec 64) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 4)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 4)
    (aligned : (stackPointer + offset) % 4 = 0)
    (fits : stackPointer + offset + 4 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 stackPointer + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (stackPointer + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (imm, rs2, .Regidx 2#5, 4)))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs2) premise premise value)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 4)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pc))
          (stackPointer + offset) value)
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  apply configuredBaseWordStoreStep stepNo pc stackPointer offset state value imm
    (.Regidx 2#5) rs2 byte0 byte1 byte2 byte3 configured atPc pma notMMIO aligned fits loaded
    addressEq decode (site := site) (base := base)
  · intro premise writes
    exact rX_x2_run premise _ ((writes.get x2 (by decide)).trans stackRead)
  · exact dataRun

/-- Retire one exact `sh offset(sp)` with a generated source-register witness. -/
theorem configuredStackHalfStoreStep (stepNo pc stackPointer offset : Nat)
    (state : State) (value : BitVec 64) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 2)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 2)
    (aligned : (stackPointer + offset) % 2 = 0)
    (fits : stackPointer + offset + 2 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 stackPointer + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (stackPointer + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (imm, rs2, .Regidx 2#5, 2)))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs2) premise premise value)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 2)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pc))
          (stackPointer + offset) value)
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise := (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise := (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have stackPremise := (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x2
    (by decide) |>.trans stackRead
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 2#5) (sign_extend (m := 64) imm) (Store Data) 2)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (stackPointer + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .store premise
      (.Regidx 2#5) 2 (BitVec.ofNat 64 stackPointer) (sign_extend (m := 64) imm)
      mstatusBits mseccfgBits (rX_x2_run premise (BitVec.ofNat 64 stackPointer) stackPremise)
      mstatusPremise privilegePremise mprvZero mseccfgPremise pmmDisabled
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 (stackPointer + offset)) 2
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (storePmaAllows_of_agree agree pma)
    (configuredOfNatAlignedTwo (stackPointer + offset) (by omega) aligned).2
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (stackPointer + offset)) 2 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 2) premise (stackPointer + offset) value
  have write : Runs (PreSail.writeBytes (n := 2)
      (BitVec.ofNat 64 (stackPointer + offset)).toNat
      (Sail.BitVec.extractLsb value 15 0)) premise afterWrite true := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact writeBytes_run_exact premise (stackPointer + offset)
      (Sail.BitVec.extractLsb value 15 0)
  have execute : Runs (execute (.STORE (imm, rs2, .Regidx 2#5, 2))) premise afterWrite
      (.Retire_Success ()) := by
    change Runs (execute_STORE imm rs2 (.Regidx 2#5) 2) _ _ _
    exact execute_STORE_half_aligned_run premise afterWrite rs2 (.Regidx 2#5) imm
      (BitVec.ofNat 64 (stackPointer + offset)) mstatusBits value mstatusPremise privilegePremise
      mprvZero (dataRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc))) addressRun
      (configuredOfNatAlignedTwo (stackPointer + offset) (by omega) aligned).1 physical noMMIO write
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noFetchMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc
      ⟨by simpa using site.pcAligned, ⟨byte0, by
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt site.pcFits] using site.read0⟩⟩
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc site.pcFits loadedAfter
    byte0 byte1 byte2 byte3 site.read0 site.read1 site.read2 site.read3
  have regsEq : afterWrite.regs = premise.regs :=
    writeBytes_preserves_regs _ _ premise afterWrite write
  refine ⟨retired, tryStepFallThroughRetires stepNo state afterWrite (BitVec.ofNat 64 pc) retired
    0 0 (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
    (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
    (.STORE (imm, rs2, .Regidx 2#5, 2)) platform noFetchMMIO bytes interrupts base decode
    notExpected execute ?_ ?_ ?_ ?_ counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
    counters.2.2.2.2.1 counters.2.2.2.2.2⟩
  · rw [regsEq]
    simp [premise, coreControlFlowNextState]
  · rw [regsEq]
    simp [premise, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
  · rw [regsEq]
    simp [premise, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
  · rw [regsEq]
    simp [premise, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]

/-- Retire one exact `sb offset(sp)` with a generated source-register witness. -/
theorem configuredStackByteStoreStep (stepNo pc stackPointer offset : Nat)
    (state : State) (value : BitVec 64) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 1)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 1)
    (fits : stackPointer + offset + 1 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 stackPointer + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (stackPointer + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (imm, rs2, .Regidx 2#5, 1)))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs2) premise premise value)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pc))
          (stackPointer + offset) value)
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise := (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise := (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have stackPremise := (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x2
    (by decide) |>.trans stackRead
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 2#5) (sign_extend (m := 64) imm) (Store Data) 1)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (stackPointer + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .store premise
      (.Regidx 2#5) 1 (BitVec.ofNat 64 stackPointer) (sign_extend (m := 64) imm)
      mstatusBits mseccfgBits (rX_x2_run premise (BitVec.ofNat 64 stackPointer) stackPremise)
      mstatusPremise privilegePremise mprvZero mseccfgPremise pmmDisabled
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 (stackPointer + offset)) 1
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (storePmaAllows_of_agree agree pma) (configuredOfNatAlignedOne _).2
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (stackPointer + offset)) 1 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 1) premise (stackPointer + offset) value
  have write : Runs (PreSail.writeBytes (n := 1)
      (BitVec.ofNat 64 (stackPointer + offset)).toNat
      (Sail.BitVec.extractLsb value 7 0)) premise afterWrite true := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact writeBytes_run_exact premise (stackPointer + offset)
      (Sail.BitVec.extractLsb value 7 0)
  have execute : Runs (execute (.STORE (imm, rs2, .Regidx 2#5, 1))) premise afterWrite
      (.Retire_Success ()) := by
    change Runs (execute_STORE imm rs2 (.Regidx 2#5) 1) _ _ _
    exact execute_STORE_byte_run premise afterWrite rs2 (.Regidx 2#5) imm
      (BitVec.ofNat 64 (stackPointer + offset)) mstatusBits value mstatusPremise privilegePremise
      mprvZero (dataRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc))) addressRun
      physical noMMIO write
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noFetchMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc
      ⟨by simpa using site.pcAligned, ⟨byte0, by
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt site.pcFits] using site.read0⟩⟩
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc site.pcFits loadedAfter
    byte0 byte1 byte2 byte3 site.read0 site.read1 site.read2 site.read3
  have regsEq : afterWrite.regs = premise.regs :=
    writeBytes_preserves_regs _ _ premise afterWrite write
  refine ⟨retired, tryStepFallThroughRetires stepNo state afterWrite (BitVec.ofNat 64 pc) retired
    0 0 (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
    (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
    (.STORE (imm, rs2, .Regidx 2#5, 1)) platform noFetchMMIO bytes interrupts base decode
    notExpected execute ?_ ?_ ?_ ?_ counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
    counters.2.2.2.2.1 counters.2.2.2.2.2⟩
  · rw [regsEq]
    simp [premise, coreControlFlowNextState]
  · rw [regsEq]
    simp [premise, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
  · rw [regsEq]
    simp [premise, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
  · rw [regsEq]
    simp [premise, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]

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
    (pcAligned : pc % 4 = 0 := by native_decide)
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
    configured.stepContext (BitVec.ofNat 64 pc) atPc ⟨by simpa using pcAligned, ⟨byte0, by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFits] using read0⟩⟩
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

/-- Evaluate the unsigned comparison used by one exact `BLTU` branch. -/
theorem bltuConditionRun (state : State) (rs2 rs1 : regidx) (right left : BitVec 64)
    (rightRun : Runs (rX_bits rs2) state state right)
    (leftRun : Runs (rX_bits rs1) state state left) :
    Runs (bTypeTaken rs1 rs2 .BLTU) state state (zopz0zI_u right left) := by
  unfold bTypeTaken
  exact Runs.bind rightRun (Runs.bind leftRun rfl)

/-- Retire one exact taken conditional branch from a configured state. -/
theorem configuredBranchTakenStep (stepNo pc target : Nat) (state : State)
    (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (imm, rs2, rs1, op)))
    (condition : Runs (bTypeTaken rs2 rs1 op)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)) true)
    (targetEq : BitVec.ofNat 64 pc + sign_extend (m := 64) imm = BitVec.ofNat 64 target)
    (targetAligned0 : Sail.BitVec.access (BitVec.ofNat 64 target) 0 = 0#1)
    (targetAligned1 : Sail.BitVec.access (BitVec.ofNat 64 target) 1 = 0#1)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
          (BitVec.ofNat 64 target))
        (BitVec.ofNat 64 target) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc ⟨by simpa using site.pcAligned, ⟨byte0, by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt site.pcFits] using site.read0⟩⟩
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
    (tryStepControlFlowAfterIncrement state) pc site.pcFits loadedAfter
    byte0 byte1 byte2 byte3 site.read0 site.read1 site.read2 site.read3
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have pcAtPremise : premise.regs.get? PC = some (BitVec.ofNat 64 pc) := by
    simpa [premise, coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC PC
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) (by decide)).trans pcRead
  have misaAtPremise : premise.regs.get? misa = some misaBits := by
    simpa [premise, coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC misa
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) (by decide)).trans misaRead
  have zca := currentlyEnabledZca_run premise misaBits misaAtPremise
  refine ⟨retired, ?_⟩
  simpa only [targetEq] using tryStepBranchTakenRetires stepNo state
    (BitVec.ofNat 64 pc) (BitVec.ofNat 64 pc) retired imm rs2 rs1 op
    0 0 (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
    (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) (_get_Misa_C misaBits == 1#1)
    platform noMMIO bytes interrupts base decode notExpected condition
    (readReg_run premise PC _ pcAtPremise) (by simpa only [targetEq] using targetAligned0)
    (by simpa only [targetEq] using targetAligned1) zca counters.1 counters.2.1
    counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2

/-- Retire one exact not-taken conditional branch from a configured state. -/
theorem configuredBranchNotTakenStep (stepNo pc : Nat) (state : State)
    (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (imm, rs2, rs1, op)))
    (condition : Runs (bTypeTaken rs2 rs1 op)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)) false)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc ⟨by simpa using site.pcAligned, ⟨byte0, by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt site.pcFits] using site.read0⟩⟩
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc site.pcFits loadedAfter
    byte0 byte1 byte2 byte3 site.read0 site.read1 site.read2 site.read3
  exact ⟨retired, tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 pc) retired
    imm rs2 rs1 op 0 0 (BitVec.ofNat 8 byte0.toNat)
    (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
    platform noMMIO bytes interrupts base decode notExpected condition counters.1 counters.2.1
    counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2⟩

/-- Retire one exact `jalr x0,imm(rs1)` tail jump from a configured state. -/
theorem configuredJrOffsetStep (stepNo pc : Nat) (state : State) (imm : BitVec 12)
    (rs1 : regidx) (source target : BitVec 64) (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (imm, rs1, zreg)))
    (sourceRun : Runs (rX_bits rs1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)) source)
    (targetEq : Sail.BitVec.update (source + sign_extend (m := 64) imm) 0 0#1 = target)
    (targetAligned : Sail.BitVec.access (source + sign_extend (m := 64) imm) 1 = 0#1)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
          target) target retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc ⟨by simpa using site.pcAligned, ⟨byte0, by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt site.pcFits] using site.read0⟩⟩
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc site.pcFits loadedAfter
    byte0 byte1 byte2 byte3 site.read0 site.read1 site.read2 site.read3
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have helpElp := updateElpState_run_atStepPremise state (BitVec.ofNat 64 pc) rs1
    seccfgBits configured.normal.2.1 seccfgRead
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have nextRead : Runs (get_next_pc ()) premise premise
      (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) := by
    unfold get_next_pc
    exact readReg_run premise nextPC _ (by simp [premise, coreControlFlowNextState])
  cases misaRead : state.regs.get? misa with
  | none =>
      have impossible := configured.normal.2.2.2.2.2.2.2.2.2.2.2
      simp [misaRead] at impossible
  | some misaBits =>
      have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 pc)
        misaBits misaRead
      refine ⟨retired, ?_⟩
      simpa only [targetEq] using
        tryStepJrDiscardRetires stepNo state (BitVec.ofNat 64 pc) source retired imm rs1
          (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) 0 0
          (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
          (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
          (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected
          helpElp nextRead sourceRun targetAligned zca counters.1 counters.2.1
          counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2

/-- Retire one exact `jalr x0,0(rs1)` indirect jump from a configured state. -/
theorem configuredJrStep (stepNo pc : Nat) (state : State) (rs1 : regidx)
    (source : BitVec 64) (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0#12, rs1, zreg)))
    (sourceRun : Runs (rX_bits rs1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)) source)
    (targetAligned : Sail.BitVec.access source 1 = 0#1)
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
          (Sail.BitVec.update source 0 0#1))
        (Sail.BitVec.update source 0 0#1) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc ⟨by simpa using site.pcAligned, ⟨byte0, by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt site.pcFits] using site.read0⟩⟩
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc site.pcFits loadedAfter
    byte0 byte1 byte2 byte3 site.read0 site.read1 site.read2 site.read3
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have helpElp := updateElpState_run_atStepPremise state (BitVec.ofNat 64 pc) rs1
    seccfgBits configured.normal.2.1 seccfgRead
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have nextRead : Runs (get_next_pc ()) premise premise
      (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) := by
    unfold get_next_pc
    exact readReg_run premise nextPC _ (by simp [premise, coreControlFlowNextState])
  cases misaRead : state.regs.get? misa with
  | none =>
      have impossible := configured.normal.2.2.2.2.2.2.2.2.2.2.2
      simp [misaRead] at impossible
  | some misaBits =>
      have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 pc)
        misaBits misaRead
      exact ⟨retired, tryStepRetRetires stepNo state (BitVec.ofNat 64 pc) retired rs1
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) source 0 0
        (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
        (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
        (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected
        helpElp nextRead sourceRun targetAligned zca counters.1 counters.2.1 counters.2.2.1
        counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2⟩

/-- Retire a production `ret` (`jalr x0, 0(ra)`) from a configured endpoint state. -/
theorem configuredRetStep (stepNo pc : Nat) (state : State) (returnAddress : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (link : state.regs.get? x1 = some returnAddress)
    (targetAligned : Sail.BitVec.access returnAddress 1 = 0#1)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (pcAligned : pc % 4 = 0 := by native_decide)
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
    configured.stepContext (BitVec.ofNat 64 pc) atPc ⟨by simpa using pcAligned, ⟨0x67, by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFits] using read0⟩⟩
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
