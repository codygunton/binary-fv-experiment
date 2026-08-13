import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Instruction.Decode
import BinaryFv.RiscV.Step.ConfiguredMachine
import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Instruction.Execute.DataAddress
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Step.Call
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.RiscV.Step.RegisterWrite
import BinaryFv.RiscV.Step.Store
import BinaryFv.RiscV.Step.TryStepStackAddiMemory
import BinaryFv.Zesu.Artifacts.Image
import BinaryFv.Zesu.Contracts.Machine
import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.HostExecution

/-!
# Concrete Level 0 instructions of the SSZ endpoint

Each theorem below instantiates a target-independent instruction-class lemma with a word named by
the generated production-ELF artifact. No `try_step` execution fact is assumed.
-/

namespace BinaryFv.Zesu

open BinaryFv.Binary
open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register
open MemoryAccessType mem_payload page_based_mem_type

/-- The exact generated Level 0 instruction addresses. -/
def mainGluePcs (pc : BitVec 64) : Prop := pcInRanges Elflings.mainGluePcRanges pc

private theorem endpointStepContext {state : State}
    (configured : ConfiguredMachinePre EndpointMachinePc state) (pc : BitVec 64)
    (atPc : state.regs.get? PC = some pc) (_inside : mainGluePcs pc) :
    FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc ∧
      FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc ∧
      InterruptDisabled (tryStepControlFlowAfterIncrement state) ∧
      LandingPadNotExpected (tryStepControlFlowAfterIncrement state) :=
  configured.stepContext pc atPc trivial

theorem mainGluePcs_14cbc : mainGluePcs 0x14cbc := by
  unfold mainGluePcs
  refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide

theorem mainGluePcs_14cc0 : mainGluePcs 0x14cc0 := by
  unfold mainGluePcs
  refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide

theorem mainGluePcs_14cc4 : mainGluePcs 0x14cc4 := by
  unfold mainGluePcs
  refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide

theorem mainGluePcs_14cc8 : mainGluePcs 0x14cc8 := by
  unfold mainGluePcs
  refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide

theorem mainGluePcs_14cec : mainGluePcs 0x14cec := by
  unfold mainGluePcs
  refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide

theorem mainGluePcs_14cf0 : mainGluePcs 0x14cf0 := by
  unfold mainGluePcs
  refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide

theorem mainGluePcs_14cf4 : mainGluePcs 0x14cf4 := by
  unfold mainGluePcs
  refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide

theorem mainGluePcs_14cf8 : mainGluePcs 0x14cf8 := by
  unfold mainGluePcs
  refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide

/-- The data-side premises for one concrete Level 0 double-word store. They are kept separate from
the generated fetch/decode facts because the eventual `main` frame derives them from its stack
layout, while the instruction wrapper below is reusable at both prologue stores. -/
structure MainDwordStoreAccess (state afterWrite : State) (pc : BitVec 64)
    (imm : BitVec 12) (rs2 : regidx) where
  dstBits : BitVec 64
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
    (get_transformed_data_addr stackPointer (sign_extend (m := 64) imm) (Store Data) 8)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
    (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits))
  aligned : is_aligned_vaddr (virtaddr.Virtaddr dstBits) 8 = true
  physicalAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
    (physaddr.Physaddr dstBits) 8 false)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc) none
  noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 8)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc) false
  write : Runs (PreSail.writeBytes (n := 8) dstBits.toNat dataBits)
    (coreStoreNextState (tryStepStoreAfterIncrement state) pc) afterWrite true

/-- Construct a Level 0 stack-store access from the configured machine and the concrete stack/data
register bindings. The resulting memory state is the exact generated little-endian byte write. -/
def MainDwordStoreAccess.of_stack (state : State) (pc : BitVec 64) (imm : BitVec 12)
    (rs2 : regidx) (stackValue dataValue destination mstatusBits mseccfgBits : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some pc) (inside : mainGluePcs pc)
    (stackRead : state.regs.get? x2 = some stackValue)
    (dataRead : Runs (rX_bits rs2)
      (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
      (coreStoreNextState (tryStepStoreAfterIncrement state) pc) dataValue)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (destinationEq : stackValue + sign_extend (m := 64) imm = destination)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr destination) 8 = true)
    (pmaAllowed : StorePmaAllows state destination 8)
    (noMMIO : StoreMMIOAddressExcluded destination 8) :
    MainDwordStoreAccess state
      (afterWriteBytes (width := 8)
        (coreStoreNextState (tryStepStoreAfterIncrement state) pc)
        destination.toNat dataValue)
      pc imm rs2 := by
  let premise := coreStoreNextState (tryStepStoreAfterIncrement state) pc
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state pc).agree platformPreserved_disjoint
  have stackPremise : premise.regs.get? x2 = some stackValue :=
    (stepPremiseState_writes state pc).get x2 (by decide) |>.trans stackRead
  have stackRun : Runs (rX_bits stackPointer) premise premise stackValue :=
    rX_x2_run premise stackValue stackPremise
  have mstatusPremise : premise.regs.get? mstatus = some mstatusBits :=
    (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise : premise.regs.get? cur_privilege = some .Machine :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise : premise.regs.get? mseccfg = some mseccfgBits :=
    (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have htifPremise : premise.regs.get? htif_tohost_base = some none :=
    (agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled
  have pmaPremise : StorePmaAllows premise destination 8 :=
    storePmaAllows_of_agree agree pmaAllowed
  refine ⟨destination, mstatusBits, dataValue, mstatusPremise, privilegePremise, mprvZero,
    dataRead, ?_, aligned, ?_, ?_, writeBytes_run_exact premise destination.toNat dataValue⟩
  · simpa [premise, coreStoreNextState, destinationEq] using
      get_transformed_data_addr_machine_data_run .store premise stackPointer 8 stackValue
        (sign_extend (m := 64) imm) mstatusBits mseccfgBits stackRun mstatusPremise
        privilegePremise mprvZero mseccfgPremise pmmDisabled
  · exact phys_access_check_machine_store_allowed premise destination 8
      (fetchPmpDisabled_of_normal
        (normalExecutionState_of_platformPreserved agree configured.normal)) pmaPremise
      (by simpa [is_aligned_vaddr, is_aligned_paddr] using aligned)
  · exact storeMemoryNoMMIO_of_state_layout_excluded premise destination 8 noMMIO htifPremise

/-- The source-register binding needed by a concrete Level 0 `addi`. -/
structure MainAddiSource (state : State) (pc : BitVec 64) (source : regidx) where
  value : BitVec 64
  read : Runs (rX_bits source)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) value

/-- Construct the recurring `sp` source read from a concrete architectural register binding. -/
def MainAddiSource.stackPointer {state : State} {pc value : BitVec 64}
    (read : state.regs.get? x2 = some value) : MainAddiSource state pc stackPointer := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  have premiseRead : premise.regs.get? x2 = some value := by
    calc
      premise.regs.get? x2 = state.regs.get? x2 :=
        (stepPremiseState_writes state pc).get x2 (by decide)
      _ = some value := read
  refine ⟨value, ?_⟩
  change Runs (regval_from_reg <$> readReg x2) premise premise value
  exact Runs.bind (readReg_run premise x2 value premiseRead) rfl

/-- The data-side read performed by the Level 0 decoder-status `lhu`. -/
structure MainHalfLoadAccess (state : State) (pc : BitVec 64) (imm : BitVec 12)
    (source : regidx) where
  data : BitVec 16
  read : Runs (vmem_read source (sign_extend (m := 64) imm) 2 (Load Data) false false false)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) (.Ok data)

private theorem main_xreg_write_callback_run (state : State) (register : regidx)
    (data : BitVec 64) : (xreg_write_callback register data).run state = .ok () state := by
  rcases register with ⟨index⟩
  simp [xreg_write_callback, xreg_full_write_callback, reg_name_forwards,
    encdec_reg_forwards, encdec_reg_forwards_matches, get_config_use_abi_names,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad,
    LeanRV64DExecutable.Functions.not]
  rfl

private theorem main_assert_true_run (state : State) (condition : Bool) (message : String)
    (holds : condition = true) : Runs (PreSail.assert condition message) state state () := by
  unfold PreSail.assert Runs
  simp only [holds, ↓reduceIte]
  rfl

private theorem main_execute_load_half_run (state after : State) (imm : BitVec 12)
    (source destination : regidx) (data : BitVec 16)
    (read : Runs (vmem_read source (sign_extend (m := 64) imm) 2 (Load Data) false false false)
      state state (.Ok data))
    (write : Runs (wX_bits destination (extend_value true data)) state after ()) :
    Runs (execute_LOAD imm source destination true 2) state after (.Retire_Success ()) := by
  unfold execute_LOAD
  refine Runs.bind (main_assert_true_run state _ _ (by decide)) ?_
  refine Runs.bind read ?_
  refine Runs.bind write ?_
  rfl

private theorem main_wX_bits_run_x10 (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 10#5) value) state
      { state with regs := state.regs.insert x10 value } () := by
  change Runs (do
    Sail.writeReg x10 (regval_into_reg value)
    xreg_write_callback (.Regidx 10#5) value) state _ ()
  exact Runs.bind (by simpa using writeReg_run state x10 value)
    (main_xreg_write_callback_run _ _ _)

private theorem main_wX_bits_run_x1 (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 1#5) value) state
      { state with regs := state.regs.insert x1 value } () := by
  change Runs (do
    Sail.writeReg x1 (regval_into_reg value)
    xreg_write_callback (.Regidx 1#5) value) state _ ()
  exact Runs.bind (by simpa using writeReg_run state x1 value)
    (main_xreg_write_callback_run _ _ _)

private theorem main_wX_bits_run_x11 (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 11#5) value) state
      { state with regs := state.regs.insert x11 value } () := by
  change Runs (do
    Sail.writeReg x11 (regval_into_reg value)
    xreg_write_callback (.Regidx 11#5) value) state _ ()
  exact Runs.bind (by simpa using writeReg_run state x11 value)
    (main_xreg_write_callback_run _ _ _)

private theorem main_load_half_step (stepNo : Nat) (state : State) (pc : Nat)
    (imm : BitVec 12) (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (inside : mainGluePcs (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (pcFits : pc < 2 ^ 64)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, stackPointer, .Regidx 10#5, true, 2)))
    (access : MainHalfLoadAccess state (BitVec.ofNat 64 pc) imm stackPointer) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pc)).regs.insert x10 (extend_value true access.data) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured (BitVec.ofNat 64 pc) atPc inside
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc pcFits loadedAfter byte0 byte1 byte2 byte3
      read0 read1 read2 read3
  have execute : Runs (execute (.LOAD (imm, stackPointer, .Regidx 10#5, true, 2)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 pc)).regs.insert x10 (extend_value true access.data) }
      (.Retire_Success ()) := by
    change Runs (execute_LOAD imm stackPointer (.Regidx 10#5) true 2) _ _ _
    exact main_execute_load_half_run _ _ imm stackPointer (.Regidx 10#5) access.data access.read
      (main_wX_bits_run_x10 _ _)
  refine ⟨retired, tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 pc) retired
    0 0 (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
    (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
    (.LOAD (imm, stackPointer, .Regidx 10#5, true, 2)) x10 (extend_value true access.data)
    platform noMMIO bytes interrupts base decode notExpected execute (by decide) (by decide)
    (by decide) (by decide) counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
    counters.2.2.2.2.1 counters.2.2.2.2.2⟩

theorem configuredAuipcStep (stepNo : Nat) (state : State) (pc : Nat)
    (imm : BitVec 20) (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (pcFits : pc < 2 ^ 64)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (imm, .Regidx 1#5, .AUIPC))) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pc)).regs.insert x1
              (BitVec.ofNat 64 pc + sign_extend (m := 64) (imm ++ 0x000#12)) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc trivial
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc pcFits loadedAfter byte0 byte1 byte2 byte3
      read0 read1 read2 read3
  have pcRead : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (BitVec.ofNat 64 pc) := by
    apply readReg_run
    simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (imm, .Regidx 1#5, .AUIPC)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 pc)).regs.insert x1
            (BitVec.ofNat 64 pc + sign_extend (m := 64) (imm ++ 0x000#12)) }
      (.Retire_Success ()) := by
    change Runs (execute_UTYPE imm (.Regidx 1#5) .AUIPC) _ _ _
    exact execute_UTYPE_auipc_run _ _ imm (.Regidx 1#5) (BitVec.ofNat 64 pc) pcRead
      (main_wX_bits_run_x1 _ _)
  refine ⟨retired, tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 pc) retired
    0 0 (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
    (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
    (.UTYPE (imm, .Regidx 1#5, .AUIPC)) x1
    (BitVec.ofNat 64 pc + sign_extend (m := 64) (imm ++ 0x000#12)) platform noMMIO bytes
    interrupts base decode notExpected execute (by decide) (by decide) (by decide) (by decide)
    counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1
    counters.2.2.2.2.2⟩

/-- Production `0x14d78: auipc ra,-5`, used by the `writeSuccess` parent before `memcpy`. -/
theorem writeSuccessMemcpyCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d78)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14d78 retired x1 0xfd78) false := by
  apply configuredAuipcStep stepNo state 0x14d78 0xffffb 0x97 0xb0 0xff 0xff
    configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl

private theorem main_li_zero_step (stepNo : Nat) (state : State) (pc : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (inside : mainGluePcs (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (pcFits : pc < 2 ^ 64)
    (read0 : Artifacts.programImage.readFileByte? pc = some 0x13)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some 0x05)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some 0x00)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some 0x00) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pc)).regs.insert x10 0 }
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured (BitVec.ofNat 64 pc) atPc inside
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc pcFits loadedAfter 0x13 0x05 0x00 0x00
      read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x13 0x05 0x00 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0, .Regidx 0#5, .Regidx 10#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have zeroRead : Runs (rX_bits (.Regidx 0#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)) 0 :=
    rX_x0_run _
  have execute : Runs (execute (.ITYPE (0, .Regidx 0#5, .Regidx 10#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 pc)).regs.insert x10 0 }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 0#5) (.Regidx 10#5) .ADDI) _ _ _
    simpa using execute_ITYPE_run _ _ 0 (.Regidx 0#5) (.Regidx 10#5) .ADDI 0 zeroRead
      (main_wX_bits_run_x10 _ 0)
  refine ⟨retired, tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 pc) retired
    0 0 0x13 0x05 0x00 0x00 (.ITYPE (0, .Regidx 0#5, .Regidx 10#5, .ADDI)) x10 0
    platform noMMIO bytes interrupts (by rfl) decode notExpected execute (by decide) (by decide)
    (by decide) (by decide) counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
    counters.2.2.2.2.1 counters.2.2.2.2.2⟩

theorem configuredJalrCallStep (stepNo : Nat) (state : State) (pc : Nat)
    (callBase : BitVec 64) (imm : BitVec 12) (target returnPc : BitVec 64)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (baseRead : state.regs.get? x1 = some callBase)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (pcFits : pc < 2 ^ 64)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (imm, .Regidx 1#5, .Regidx 1#5)))
    (targetEq : Sail.BitVec.update (callBase + sign_extend (m := 64) imm) 0 0#1 = target)
    (returnEq : Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = returnPc)
    (targetBit1 : Sail.BitVec.access (callBase + sign_extend (m := 64) imm) 1 = 0#1) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc) target x1
          returnPc) target retired) false := by
  subst target
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc trivial
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc pcFits loadedAfter byte0 byte1 byte2 byte3
      read0 read1 read2 read3
  have hwrite : Runs (wX_bits (.Regidx 1#5) returnPc)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
        (Sail.BitVec.update (callBase + sign_extend (m := 64) imm) 0 0#1))
      (callLinkState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
        (Sail.BitVec.update (callBase + sign_extend (m := 64) imm) 0 0#1) x1
        returnPc) () := by
    simpa [callLinkState] using
      wX_x1_run
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
          (Sail.BitVec.update (callBase + sign_extend (m := 64) imm) 0 0#1))
        returnPc
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have helpElp := updateElpState_run_atStepPremise state (BitVec.ofNat 64 pc) (.Regidx 1#5)
    seccfgBits configured.normal.2.1 seccfgRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      returnPc := by
    apply get_next_pc_run
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4)).get? nextPC = some returnPc
    simpa [Std.ExtDHashMap.get?_insert] using returnEq
  have hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      callBase := by
    apply rX_x1_run
    simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, baseRead]
  cases misaRead : state.regs.get? misa with
  | none =>
    have impossible := configured.normal.2.2.2.2.2.2.2.2.2.2.2
    simp [misaRead] at impossible
  | some misaBits =>
    have hzca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 pc) misaBits misaRead
    refine ⟨retired, ?_⟩
    simpa [returnEq] using
      (tryStepJalrCallRetires stepNo state (BitVec.ofNat 64 pc) callBase retired returnPc imm
        (.Regidx 1#5) (.Regidx 1#5) x1 returnPc 0 0
        (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
        (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
        (_get_Misa_C misaBits == 1#1) hwrite (by decide) (by decide) (by decide) (by decide)
        platform noMMIO bytes interrupts base decode notExpected helpElp hlink hrs1
        targetBit1 hzca counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
        counters.2.2.2.2.1 counters.2.2.2.2.2)

private theorem main_store_dword_step (stepNo : Nat) (state afterWrite : State)
    (pc : Nat) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (inside : mainGluePcs (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (pcFits : pc < 2 ^ 64)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (imm, rs2, stackPointer, 8)))
    (access : MainDwordStoreAccess state afterWrite (BitVec.ofNat 64 pc) imm rs2) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired afterWrite (BitVec.ofNat 64 pc) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noFetchMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured (BitVec.ofNat 64 pc) atPc inside
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepStoreAfterIncrement state).mem := by
    simpa [tryStepStoreAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepStoreAfterIncrement state) pc pcFits loadedAfter byte0 byte1 byte2 byte3
      read0 read1 read2 read3
  refine ⟨retired, tryStepStoreDwordRetires stepNo state afterWrite (BitVec.ofNat 64 pc)
    imm rs2 stackPointer access.dstBits access.mstatusBits access.dataBits retired 0 0
    (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
    (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) ?_ ?_ bytes ?_ base decode ?_
    access.mstatusRead access.privilegeRead access.mprvZero access.dataRead access.addressRead
    access.aligned access.physicalAccess access.noMMIO access.write counters.1 counters.2.1
    counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2⟩
  · simpa [tryStepStoreAfterIncrement, tryStepControlFlowAfterIncrement] using platform
  · simpa [tryStepStoreAfterIncrement, tryStepControlFlowAfterIncrement] using noFetchMMIO
  · simpa [tryStepStoreAfterIncrement, tryStepControlFlowAfterIncrement] using interrupts
  · simpa [tryStepStoreAfterIncrement, tryStepControlFlowAfterIncrement] using notExpected

/-- Production `0x14cb4: sd ra, 888(sp)`. -/
theorem main_save_return_address_step (stepNo : Nat) (state afterWrite : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x14cb4))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (access : MainDwordStoreAccess state afterWrite 0x14cb4 0x378 (.Regidx 1#5)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired afterWrite 0x14cb4 retired) false := by
  apply main_store_dword_step stepNo state afterWrite 0x14cb4 0x378 (.Regidx 1#5)
    0x23 0x3c 0x11 0x36 configured atPc (by
      refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide) loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepStoreAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepStoreAfterIncrement] using writeReg_read_unchanged state
            minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepStoreAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepStoreAfterIncrement] using writeReg_read_unchanged state
            minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure,
      EStateM.instMonad, EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
      EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
      privilegeAfter, seccfgAfter, *]
    rfl
  · exact access

/-- Production `0x14cb8: sd zero, 8(sp)`. -/
theorem main_clear_input_slot_step (stepNo : Nat) (state afterWrite : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x14cb8))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (access : MainDwordStoreAccess state afterWrite 0x14cb8 0x008 (.Regidx 0#5)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired afterWrite 0x14cb8 retired) false := by
  apply main_store_dword_step stepNo state afterWrite 0x14cb8 0x008 (.Regidx 0#5)
    0x23 0x34 0x01 0x00 configured atPc (by
      refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide) loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepStoreAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepStoreAfterIncrement] using writeReg_read_unchanged state
            minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepStoreAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepStoreAfterIncrement] using writeReg_read_unchanged state
            minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure,
      EStateM.instMonad, EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
      EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
      privilegeAfter, seccfgAfter, *]
    rfl
  · exact access

/-- Production `0x14cbc: addi a0, sp, 0`. -/
theorem main_input_buffer_address_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cbc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (source : MainAddiSource state 0x14cbc stackPointer) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cbc with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cbc).regs.insert
            x10 (iTypeResult .ADDI 0 source.value) }
        0x14cc0 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14cbc atPc (by
      refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14cbc (by native_decide) loadedAfter
    0x13 0x05 0x01 0x00 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x05 : BitVec 8) (0x01 : BitVec 8)
        (0x00 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0, stackPointer, .Regidx 10#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have execute : Runs (execute (.ITYPE (0, stackPointer, .Regidx 10#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cbc)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cbc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cbc).regs.insert
          x10 (iTypeResult .ADDI 0 source.value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 stackPointer (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run _ _ 0 stackPointer (.Regidx 10#5) .ADDI source.value source.read
      (main_wX_bits_run_x10 _ _)
  refine ⟨retired, tryStepFallThroughWriteRegRetires stepNo state 0x14cbc retired 0 0
    0x13 0x05 0x01 0x00 (.ITYPE (0, stackPointer, .Regidx 10#5, .ADDI)) x10
    (iTypeResult .ADDI 0 source.value) platform noMMIO bytes interrupts ?_ decode notExpected
    execute (by decide) (by decide) (by decide) (by decide) counters.1 counters.2.1
    counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2⟩
  rfl

/-- Production `0x14cc0: addi a1, sp, 8`. -/
theorem main_input_size_slot_address_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cc0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (source : MainAddiSource state 0x14cc0 stackPointer) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc0 with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc0).regs.insert
            x11 (iTypeResult .ADDI 8 source.value) }
        0x14cc4 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14cc0 atPc (by
      refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14cc0 (by native_decide) loadedAfter
    0x93 0x05 0x81 0x00 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x93 : BitVec 8) (0x05 : BitVec 8) (0x81 : BitVec 8)
        (0x00 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (8, stackPointer, .Regidx 11#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have execute : Runs (execute (.ITYPE (8, stackPointer, .Regidx 11#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc0)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc0 with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc0).regs.insert
          x11 (iTypeResult .ADDI 8 source.value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 8 stackPointer (.Regidx 11#5) .ADDI) _ _ _
    exact execute_ITYPE_run _ _ 8 stackPointer (.Regidx 11#5) .ADDI source.value source.read
      (main_wX_bits_run_x11 _ _)
  refine ⟨retired, tryStepFallThroughWriteRegRetires stepNo state 0x14cc0 retired 0 0
    0x93 0x05 0x81 0x00 (.ITYPE (8, stackPointer, .Regidx 11#5, .ADDI)) x11
    (iTypeResult .ADDI 8 source.value) platform noMMIO bytes interrupts ?_ decode notExpected
    execute (by decide) (by decide) (by decide) (by decide) counters.1 counters.2.1
    counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2⟩
  rfl

/-- Production `0x14cc4: auipc ra, -5`, producing the base used by the `read_input` call. -/
theorem main_read_input_call_base_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cc4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc4 with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc4).regs.insert
            x1 (0x14cc4 + sign_extend (m := 64) (0xffffb#20 ++ 0x000#12)) }
        0x14cc8 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14cc4 atPc (by
      refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14cc4 (by native_decide) loadedAfter
    0x97 0xb0 0xff 0xff (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x97 : BitVec 8) (0xb0 : BitVec 8) (0xff : BitVec 8)
        (0xff : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0xffffb#20, .Regidx 1#5, .AUIPC)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have pcRead : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc4)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc4) 0x14cc4 := by
    apply readReg_run
    simp [coreControlFlowNextState, atPc, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have execute : Runs (execute (.UTYPE (0xffffb#20, .Regidx 1#5, .AUIPC)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc4)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc4 with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc4).regs.insert
          x1 (0x14cc4 + sign_extend (m := 64) (0xffffb#20 ++ 0x000#12)) }
      (.Retire_Success ()) := by
    change Runs (execute_UTYPE 0xffffb#20 (.Regidx 1#5) .AUIPC) _ _ _
    exact execute_UTYPE_auipc_run _ _ 0xffffb#20 (.Regidx 1#5) 0x14cc4 pcRead
      (main_wX_bits_run_x1 _ _)
  refine ⟨retired, tryStepFallThroughWriteRegRetires stepNo state 0x14cc4 retired 0 0
    0x97 0xb0 0xff 0xff (.UTYPE (0xffffb#20, .Regidx 1#5, .AUIPC)) x1
    (0x14cc4 + sign_extend (m := 64) (0xffffb#20 ++ 0x000#12)) platform noMMIO bytes
    interrupts ?_ decode notExpected execute (by decide) (by decide) (by decide) (by decide)
    counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1
    counters.2.2.2.2.2⟩
  rfl

theorem main_read_input_call_base_value :
    (0x14cc4 : BitVec 64) + sign_extend (m := 64) (0xffffb#20 ++ 0x000#12) = 0xfcc4 := by
  native_decide

/-- Production `0x14cc8: jalr ra, 0x47c(ra)`, entering `read_input` at `0x10140` and
saving the return address `0x14ccc` in `ra`. -/
theorem main_read_input_call_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cc8)
    (callBase : state.regs.get? x1 = some 0xfcc4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14cc8 0x10140 x1 0x14ccc)
        0x10140 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14cc8 atPc (by
      refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14cc8 (by native_decide) loadedAfter
    0xe7 0x80 0xc0 0x47 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0xe7 : BitVec 8) (0x80 : BitVec 8) (0xc0 : BitVec 8)
        (0x47 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0x47c, .Regidx 1#5, .Regidx 1#5)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have target : Sail.BitVec.update
      ((0xfcc4 : BitVec 64) + sign_extend (m := 64) (0x47c : BitVec 12)) 0 0#1 = 0x10140 := by
    native_decide
  have link : Sail.BitVec.addInt (0x14cc8 : BitVec 64) 4 = 0x14ccc := by
    native_decide
  have hwrite : Runs (wX_bits (.Regidx 1#5) 0x14ccc)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x14cc8 0x10140)
      (callLinkState (tryStepControlFlowAfterIncrement state) 0x14cc8 0x10140 x1 0x14ccc) () := by
    simpa [callLinkState] using
      wX_x1_run (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x14cc8 0x10140)
        0x14ccc
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have helpElp := updateElpState_run_atStepPremise state 0x14cc8 (.Regidx 1#5) seccfgBits
    configured.normal.2.1 seccfgRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc8) 0x14ccc := by
    apply get_next_pc_run
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt 0x14cc8 4)).get? nextPC = some 0x14ccc
    simpa [Std.ExtDHashMap.get?_insert] using link
  have hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cc8) 0xfcc4 := by
    apply rX_x1_run
    simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, callBase]
  cases misaRead : state.regs.get? misa with
  | none =>
    have impossible := configured.normal.2.2.2.2.2.2.2.2.2.2.2
    simp [misaRead] at impossible
  | some misaBits =>
    have hzca := currentlyEnabledZca_run_atStepPremise state 0x14cc8 misaBits misaRead
    refine ⟨retired, ?_⟩
    simpa [target, link] using
      (tryStepJalrCallRetires stepNo state 0x14cc8 0xfcc4 retired 0x14ccc 0x47c
        (.Regidx 1#5) (.Regidx 1#5) x1 0x14ccc 0 0 0xe7 0x80 0xc0 0x47
        (_get_Misa_C misaBits == 1#1) hwrite (by decide) (by decide) (by decide) (by decide)
        platform noMMIO bytes interrupts (by rfl) decode notExpected helpElp hlink hrs1
        (by native_decide) hzca counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
        counters.2.2.2.2.1 counters.2.2.2.2.2)

/-- Production `0x14cec: addi a0, sp, 32`, selecting main's decoded-result slot. -/
theorem main_decode_result_address_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cec)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (source : MainAddiSource state 0x14cec stackPointer) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cec with
          regs := (coreControlFlowNextState
            (tryStepControlFlowAfterIncrement state) 0x14cec).regs.insert
              x10 (iTypeResult .ADDI 0x20 source.value) }
        0x14cf0 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14cec atPc (by
      refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14cec (by native_decide) loadedAfter
    0x13 0x05 0x01 0x02 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x05 : BitVec 8) (0x01 : BitVec 8)
        (0x02 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x20, stackPointer, .Regidx 10#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have execute : Runs (execute (.ITYPE (0x20, stackPointer, .Regidx 10#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cec)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cec with
        regs := (coreControlFlowNextState
          (tryStepControlFlowAfterIncrement state) 0x14cec).regs.insert
            x10 (iTypeResult .ADDI 0x20 source.value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x20 stackPointer (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run _ _ 0x20 stackPointer (.Regidx 10#5) .ADDI source.value source.read
      (main_wX_bits_run_x10 _ _)
  refine ⟨retired, tryStepFallThroughWriteRegRetires stepNo state 0x14cec retired 0 0
    0x13 0x05 0x01 0x02 (.ITYPE (0x20, stackPointer, .Regidx 10#5, .ADDI)) x10
    (iTypeResult .ADDI 0x20 source.value) platform noMMIO bytes interrupts ?_ decode notExpected
    execute (by decide) (by decide) (by decide) (by decide) counters.1 counters.2.1
    counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2⟩
  rfl

/-- Production `0x14cf0: addi a1, sp, 16`, selecting the allocator descriptor slot. -/
theorem main_decode_allocator_address_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cf0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (source : MainAddiSource state 0x14cf0 stackPointer) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf0 with
          regs := (coreControlFlowNextState
            (tryStepControlFlowAfterIncrement state) 0x14cf0).regs.insert
              x11 (iTypeResult .ADDI 0x10 source.value) }
        0x14cf4 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14cf0 atPc (by
      refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14cf0 (by native_decide) loadedAfter
    0x93 0x05 0x01 0x01 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x93 : BitVec 8) (0x05 : BitVec 8) (0x01 : BitVec 8)
        (0x01 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x10, stackPointer, .Regidx 11#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have execute : Runs (execute (.ITYPE (0x10, stackPointer, .Regidx 11#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf0)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf0 with
        regs := (coreControlFlowNextState
          (tryStepControlFlowAfterIncrement state) 0x14cf0).regs.insert
            x11 (iTypeResult .ADDI 0x10 source.value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x10 stackPointer (.Regidx 11#5) .ADDI) _ _ _
    exact execute_ITYPE_run _ _ 0x10 stackPointer (.Regidx 11#5) .ADDI source.value source.read
      (main_wX_bits_run_x11 _ _)
  refine ⟨retired, tryStepFallThroughWriteRegRetires stepNo state 0x14cf0 retired 0 0
    0x93 0x05 0x01 0x01 (.ITYPE (0x10, stackPointer, .Regidx 11#5, .ADDI)) x11
    (iTypeResult .ADDI 0x10 source.value) platform noMMIO bytes interrupts ?_ decode notExpected
    execute (by decide) (by decide) (by decide) (by decide) counters.1 counters.2.1
    counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2⟩
  rfl

/-- Production `0x14cf4: auipc ra, -3`, producing the base used by the `decodeInput` call. -/
theorem main_decode_call_base_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cf4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf4 with
          regs := (coreControlFlowNextState
            (tryStepControlFlowAfterIncrement state) 0x14cf4).regs.insert
              x1 (0x14cf4 + sign_extend (m := 64) (0xffffd#20 ++ 0x000#12)) }
        0x14cf8 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14cf4 atPc (by
      refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14cf4 (by native_decide) loadedAfter
    0x97 0xd0 0xff 0xff (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x97 : BitVec 8) (0xd0 : BitVec 8) (0xff : BitVec 8)
        (0xff : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0xffffd#20, .Regidx 1#5, .AUIPC)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have pcRead : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf4)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf4) 0x14cf4 := by
    apply readReg_run
    simp [coreControlFlowNextState, atPc, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have execute : Runs (execute (.UTYPE (0xffffd#20, .Regidx 1#5, .AUIPC)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf4)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf4 with
        regs := (coreControlFlowNextState
          (tryStepControlFlowAfterIncrement state) 0x14cf4).regs.insert
            x1 (0x14cf4 + sign_extend (m := 64) (0xffffd#20 ++ 0x000#12)) }
      (.Retire_Success ()) := by
    change Runs (execute_UTYPE 0xffffd#20 (.Regidx 1#5) .AUIPC) _ _ _
    exact execute_UTYPE_auipc_run _ _ 0xffffd#20 (.Regidx 1#5) 0x14cf4 pcRead
      (main_wX_bits_run_x1 _ _)
  refine ⟨retired, tryStepFallThroughWriteRegRetires stepNo state 0x14cf4 retired 0 0
    0x97 0xd0 0xff 0xff (.UTYPE (0xffffd#20, .Regidx 1#5, .AUIPC)) x1
    (0x14cf4 + sign_extend (m := 64) (0xffffd#20 ++ 0x000#12)) platform noMMIO bytes
    interrupts ?_ decode notExpected execute (by decide) (by decide) (by decide) (by decide)
    counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1
    counters.2.2.2.2.2⟩
  rfl

theorem main_decode_call_base_value :
    (0x14cf4 : BitVec 64) + sign_extend (m := 64) (0xffffd#20 ++ 0x000#12) = 0x11cf4 := by
  native_decide

/-- Production `0x14cf8: jalr ra, 0x474(ra)`, entering `decodeInput` at `0x12168`. -/
theorem main_decode_call_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cf8)
    (callBase : state.regs.get? x1 = some 0x11cf4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14cf8 0x12168 x1 0x14cfc)
        0x12168 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14cf8 atPc (by
      refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14cf8 (by native_decide) loadedAfter
    0xe7 0x80 0x40 0x47 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0xe7 : BitVec 8) (0x80 : BitVec 8) (0x40 : BitVec 8)
        (0x47 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0x474, .Regidx 1#5, .Regidx 1#5)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have target : Sail.BitVec.update
      ((0x11cf4 : BitVec 64) + sign_extend (m := 64) (0x474 : BitVec 12)) 0 0#1 = 0x12168 := by
    native_decide
  have link : Sail.BitVec.addInt (0x14cf8 : BitVec 64) 4 = 0x14cfc := by
    native_decide
  have hwrite : Runs (wX_bits (.Regidx 1#5) 0x14cfc)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x14cf8 0x12168)
      (callLinkState (tryStepControlFlowAfterIncrement state) 0x14cf8 0x12168 x1 0x14cfc) () := by
    simpa [callLinkState] using
      wX_x1_run (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x14cf8 0x12168)
        0x14cfc
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have helpElp := updateElpState_run_atStepPremise state 0x14cf8 (.Regidx 1#5) seccfgBits
    configured.normal.2.1 seccfgRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf8) 0x14cfc := by
    apply get_next_pc_run
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt 0x14cf8 4)).get? nextPC = some 0x14cfc
    simpa [Std.ExtDHashMap.get?_insert] using link
  have hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cf8) 0x11cf4 := by
    apply rX_x1_run
    simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, callBase]
  cases misaRead : state.regs.get? misa with
  | none =>
    have impossible := configured.normal.2.2.2.2.2.2.2.2.2.2.2
    simp [misaRead] at impossible
  | some misaBits =>
    have hzca := currentlyEnabledZca_run_atStepPremise state 0x14cf8 misaBits misaRead
    refine ⟨retired, ?_⟩
    simpa [target, link] using
      (tryStepJalrCallRetires stepNo state 0x14cf8 0x11cf4 retired 0x14cfc 0x474
        (.Regidx 1#5) (.Regidx 1#5) x1 0x14cfc 0 0 0xe7 0x80 0x40 0x47
        (_get_Misa_C misaBits == 1#1) hwrite (by decide) (by decide) (by decide) (by decide)
        platform noMMIO bytes interrupts (by rfl) decode notExpected helpElp hlink hrs1
        (by native_decide) hzca counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
        counters.2.2.2.2.1 counters.2.2.2.2.2)

/-- Production `0x14cfc: lhu a0, 0x370(sp)`, loading the decoder status. -/
theorem main_decode_status_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cfc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (access : MainHalfLoadAccess state 0x14cfc 0x370 stackPointer) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cfc with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cfc).regs.insert
            x10 (extend_value true access.data) }
        0x14d00 retired) false := by
  apply main_load_half_step stepNo state 0x14cfc 0x370 0x03 0x55 0x01 0x37 configured atPc
    (by refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide) loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl

private theorem main_decode_status_branch_decode (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord (0x63 : BitVec 8) (0x1e : BitVec 8) (0x05 : BitVec 8)
      (0x00 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x01c, .Regidx 0#5, .Regidx 10#5, .BNE)) := by
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine := by
    calc
      _ = state.regs.get? cur_privilege := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := configured.normal.2.1
  have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some seccfgBits := by
    calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
      _ = some seccfgBits := seccfgRead
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
    instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
    MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
  rfl

/-- Production `0x14d00: bnez a0,0x14d1c`, on the successful zero-status route. -/
theorem main_decode_status_success_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d00)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 10#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d00)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d00) false) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d00)
        0x14d04 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14d00 atPc (by
      refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14d00 (by native_decide) loadedAfter
    0x63 0x1e 0x05 0x00 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  refine ⟨retired, tryStepBranchNotTakenRetires stepNo state 0x14d00 retired 0x01c
    (.Regidx 0#5) (.Regidx 10#5) .BNE 0 0 0x63 0x1e 0x05 0x00 platform noMMIO bytes
    interrupts (by rfl) (main_decode_status_branch_decode state configured) notExpected condition
    counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1
    counters.2.2.2.2.2⟩

/-- Production `0x14d00: bnez a0,0x14d1c`, on a nonzero decoder status. -/
theorem main_decode_status_failure_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d00)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 10#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d00)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d00) true) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x14d00 0x14d1c)
        0x14d1c retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14d00 atPc (by
      refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14d00 (by native_decide) loadedAfter
    0x63 0x1e 0x05 0x00 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have pcRead : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d00)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d00) 0x14d00 := by
    apply readReg_run
    simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  cases misaRead : state.regs.get? misa with
  | none =>
    have impossible := configured.normal.2.2.2.2.2.2.2.2.2.2.2
    simp [misaRead] at impossible
  | some misaBits =>
    have zca := currentlyEnabledZca_run_atStepPremise state 0x14d00 misaBits misaRead
    refine ⟨retired, ?_⟩
    simpa only [show (0x14d00 : BitVec 64) + sign_extend (m := 64) (0x01c : BitVec 13) =
        0x14d1c by native_decide] using
      (tryStepBranchTakenRetires stepNo state 0x14d00 0x14d00 retired 0x01c
        (.Regidx 0#5) (.Regidx 10#5) .BNE 0 0 0x63 0x1e 0x05 0x00
        (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts (by rfl)
        (main_decode_status_branch_decode state configured) notExpected condition pcRead
        (by native_decide) (by native_decide) zca counters.1 counters.2.1 counters.2.2.1
        counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2)

/-- Production `0x14d04: addi a0,sp,32`, selecting the successful decoded result. -/
theorem main_success_result_address_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d04)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (source : MainAddiSource state 0x14d04 stackPointer) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d04 with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d04).regs.insert
            x10 (iTypeResult .ADDI 0x20 source.value) }
        0x14d08 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14d04 atPc (by
      refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14d04 (by native_decide) loadedAfter
    0x13 0x05 0x01 0x02 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x05 : BitVec 8) (0x01 : BitVec 8)
        (0x02 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x20, stackPointer, .Regidx 10#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have execute : Runs (execute (.ITYPE (0x20, stackPointer, .Regidx 10#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d04)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d04 with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d04).regs.insert
          x10 (iTypeResult .ADDI 0x20 source.value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x20 stackPointer (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run _ _ 0x20 stackPointer (.Regidx 10#5) .ADDI source.value source.read
      (main_wX_bits_run_x10 _ _)
  refine ⟨retired, tryStepFallThroughWriteRegRetires stepNo state 0x14d04 retired 0 0
    0x13 0x05 0x01 0x02 (.ITYPE (0x20, stackPointer, .Regidx 10#5, .ADDI)) x10
    (iTypeResult .ADDI 0x20 source.value) platform noMMIO bytes interrupts (by rfl) decode
    notExpected execute (by decide) (by decide) (by decide) (by decide) counters.1 counters.2.1
    counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2⟩

/-- Production `0x14d08: auipc ra,0`, forming the `writeSuccess` call base. -/
theorem main_write_success_call_base_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d08)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d08 with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d08).regs.insert
            x1 0x14d08 }
        0x14d0c retired) false := by
  apply configuredAuipcStep stepNo state 0x14d08 0 0x97 0x00 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl

/-- Production `0x14d0c: jalr ra,0x28(ra)`, entering `writeSuccess` at `0x14d30`. -/
theorem main_write_success_call_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d0c)
    (callBase : state.regs.get? x1 = some 0x14d08)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14d0c 0x14d30 x1 0x14d10)
        0x14d30 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured 0x14d0c atPc (by
      refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x14d0c (by native_decide) loadedAfter
    0xe7 0x80 0x80 0x02 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0xe7 : BitVec 8) (0x80 : BitVec 8) (0x80 : BitVec 8)
        (0x02 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0x028, .Regidx 1#5, .Regidx 1#5)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have target : Sail.BitVec.update
      ((0x14d08 : BitVec 64) + sign_extend (m := 64) (0x028 : BitVec 12)) 0 0#1 = 0x14d30 := by
    native_decide
  have link : Sail.BitVec.addInt (0x14d0c : BitVec 64) 4 = 0x14d10 := by
    native_decide
  have hwrite : Runs (wX_bits (.Regidx 1#5) 0x14d10)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x14d0c 0x14d30)
      (callLinkState (tryStepControlFlowAfterIncrement state) 0x14d0c 0x14d30 x1 0x14d10) () := by
    simpa [callLinkState] using
      wX_x1_run (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x14d0c 0x14d30)
        0x14d10
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have helpElp := updateElpState_run_atStepPremise state 0x14d0c (.Regidx 1#5) seccfgBits
    configured.normal.2.1 seccfgRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d0c)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d0c) 0x14d10 := by
    apply get_next_pc_run
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt 0x14d0c 4)).get? nextPC = some 0x14d10
    simpa [Std.ExtDHashMap.get?_insert] using link
  have hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d0c)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d0c) 0x14d08 := by
    apply rX_x1_run
    simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, callBase]
  cases misaRead : state.regs.get? misa with
  | none =>
    have impossible := configured.normal.2.2.2.2.2.2.2.2.2.2.2
    simp [misaRead] at impossible
  | some misaBits =>
    have hzca := currentlyEnabledZca_run_atStepPremise state 0x14d0c misaBits misaRead
    refine ⟨retired, ?_⟩
    simpa [target, link] using
      (tryStepJalrCallRetires stepNo state 0x14d0c 0x14d08 retired 0x14d10 0x028
        (.Regidx 1#5) (.Regidx 1#5) x1 0x14d10 0 0 0xe7 0x80 0x80 0x02
        (_get_Misa_C misaBits == 1#1) hwrite (by decide) (by decide) (by decide) (by decide)
        platform noMMIO bytes interrupts (by rfl) decode notExpected helpElp hlink hrs1
        (by native_decide) hzca counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
        counters.2.2.2.2.1 counters.2.2.2.2.2)

/-- Production `0x14d10: li a0,0`, preparing the successful exit code. -/
theorem main_success_exit_code_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d10)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d10 with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d10).regs.insert
            x10 0 }
        0x14d14 retired) false := by
  apply main_li_zero_step stepNo state 0x14d10 configured atPc
    (by refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide) loaded <;> native_decide

/-- Production `0x14d24: li a0,0`, preparing the rejected-input exit code. -/
theorem main_failure_exit_code_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d24)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d24 with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d24).regs.insert
            x10 0 }
        0x14d28 retired) false := by
  apply main_li_zero_step stepNo state 0x14d24 configured atPc
    (by refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide) loaded <;> native_decide

private theorem main_auipc_neg5_decode (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x97 0xb0 0xff 0xff))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0xffffb, .Regidx 1#5, .AUIPC)) := by
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine := by
    calc
      _ = state.regs.get? cur_privilege := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := configured.normal.2.1
  have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some seccfgBits := by
    calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
      _ = some seccfgBits := seccfgRead
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
    instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
    MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
  rfl

private theorem main_auipc_plus1_decode (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x97 0x10 0x00 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (1, .Regidx 1#5, .AUIPC)) := by
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine := by
    calc
      _ = state.regs.get? cur_privilege := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := configured.normal.2.1
  have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some seccfgBits := by
    calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
      _ = some seccfgBits := seccfgRead
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
    instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
    MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
  rfl

/-- Production `0x14d14: auipc ra,-5`, forming the successful `zkvm_exit` call base. -/
theorem main_success_exit_call_base_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d14)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d14 with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d14).regs.insert
            x1 0xfd14 }
        0x14d18 retired) false := by
  apply configuredAuipcStep stepNo state 0x14d14 0xffffb 0x97 0xb0 0xff 0xff configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · exact main_auipc_neg5_decode state configured

/-- Production `0x14d1c: auipc ra,1`, forming the `writeFailure` call base. -/
theorem main_write_failure_call_base_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d1c)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d1c with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d1c).regs.insert
            x1 0x15d1c }
        0x14d20 retired) false := by
  apply configuredAuipcStep stepNo state 0x14d1c 1 0x97 0x10 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · exact main_auipc_plus1_decode state configured

/-- Production `0x14d28: auipc ra,-5`, forming the failure-route `zkvm_exit` call base. -/
theorem main_failure_exit_call_base_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d28)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d28 with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d28).regs.insert
            x1 0xfd28 }
        0x14d2c retired) false := by
  apply configuredAuipcStep stepNo state 0x14d28 0xffffb 0x97 0xb0 0xff 0xff configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · exact main_auipc_neg5_decode state configured

private theorem main_jalr_decode (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (byte0 byte1 byte2 byte3 : BitVec 8) (imm : BitVec 12)
    (decoded : fetchWord byte0 byte1 byte2 byte3 = 0x000080e7#32 ∨
      fetchWord byte0 byte1 byte2 byte3 = 0x4b0080e7#32 ∨
      fetchWord byte0 byte1 byte2 byte3 = 0x4a4080e7#32 ∨
      fetchWord byte0 byte1 byte2 byte3 = 0x49c080e7#32)
    (immEq : imm = Sail.BitVec.extractLsb (fetchWord byte0 byte1 byte2 byte3) 31 20) :
    Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (imm, .Regidx 1#5, .Regidx 1#5)) := by
  rcases decoded with decoded | decoded | decoded | decoded <;> subst imm <;> rw [decoded]
  all_goals
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl

/-- Production `0x14d18: jalr ra,0x4b0(ra)`, entering `zkvm_exit` at `0x101c4`. -/
theorem main_success_exit_call_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d18)
    (baseRead : state.regs.get? x1 = some 0xfd14)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14d18 0x101c4 x1 0x14d1c)
        0x101c4 retired) false := by
  apply configuredJalrCallStep stepNo state 0x14d18 0xfd14 0x4b0 0x101c4 0x14d1c
    0xe7 0x80 0x00 0x4b configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · exact main_jalr_decode state configured 0xe7 0x80 0x00 0x4b 0x4b0
      (by right; left; native_decide) (by native_decide)
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14d20: jalr ra,0x4a4(ra)`, entering `writeFailure` at `0x161c0`. -/
theorem main_write_failure_call_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d20)
    (baseRead : state.regs.get? x1 = some 0x15d1c)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14d20 0x161c0 x1 0x14d24)
        0x161c0 retired) false := by
  apply configuredJalrCallStep stepNo state 0x14d20 0x15d1c 0x4a4 0x161c0 0x14d24
    0xe7 0x80 0x40 0x4a configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · exact main_jalr_decode state configured 0xe7 0x80 0x40 0x4a 0x4a4
      (by right; right; left; native_decide) (by native_decide)
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14d2c: jalr ra,0x49c(ra)`, entering `zkvm_exit` at `0x101c4`. -/
theorem main_failure_exit_call_step (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d2c)
    (baseRead : state.regs.get? x1 = some 0xfd28)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14d2c 0x101c4 x1 0x14d30)
        0x101c4 retired) false := by
  apply configuredJalrCallStep stepNo state 0x14d2c 0xfd28 0x49c 0x101c4 0x14d30
    0xe7 0x80 0xc0 0x49 configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · exact main_jalr_decode state configured 0xe7 0x80 0xc0 0x49 0x49c
      (by right; right; right; native_decide) (by native_decide)
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14cb0: addi sp, sp, -896`, including generated fetch and retirement. -/
theorem main_stack_allocate_step (stepNo : Nat) (state : State) (stackValue : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 Elflings.mainEntry))
    (stackRead : state.regs.get? x2 = some stackValue)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStackAddiAfterRetired state (BitVec.ofNat 64 Elflings.mainEntry)
        (BitVec.ofNat 12 0xc80) stackValue retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    endpointStepContext configured (BitVec.ofNat 64 Elflings.mainEntry) atPc (by
      refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepStackAddiAfterIncrement state).mem := by
    simpa [tryStepStackAddiAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepStackAddiAfterIncrement state) Elflings.mainEntry (by native_decide) loadedAfter
    0x13 0x01 0x01 0xc8 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x01 : BitVec 8) (0x01 : BitVec 8)
        (0xc8 : BitVec 8)))
      (tryStepStackAddiAfterIncrement state) (tryStepStackAddiAfterIncrement state)
      (.ITYPE (BitVec.ofNat 12 0xc80, stackPointer, stackPointer, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepStackAddiAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepStackAddiAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepStackAddiAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepStackAddiAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports,
      bool_bit_backwards, PreSail.readReg, EStateM.run, Bind.bind, Pure.pure,
      Functor.map, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
      EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
      EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get,
      MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have wordEq : fetchWord (0x13 : BitVec 8) (0x01 : BitVec 8) (0x01 : BitVec 8)
      (0xc8 : BitVec 8) = BitVec.ofNat 32 Elflings.mainGlueWordAt14cb0 := by
    native_decide
  have stackAfterNext :
      (stackAddiNextState (tryStepStackAddiAfterIncrement state)
        (BitVec.ofNat 64 Elflings.mainEntry)).regs.get? x2 = some stackValue := by
    calc
      _ = (tryStepStackAddiAfterIncrement state).regs.get? x2 := by
        simpa [stackAddiNextState] using
          writeReg_read_unchanged (tryStepStackAddiAfterIncrement state) nextPC x2
            (Sail.BitVec.addInt (BitVec.ofNat 64 Elflings.mainEntry) 4) (by decide)
      _ = state.regs.get? x2 := by
        simpa [tryStepStackAddiAfterIncrement] using
          writeReg_read_unchanged state minstret_increment x2 true (by decide)
      _ = some stackValue := stackRead
  refine ⟨retired, tryStepStackAddiRetiresWithFetchMemory stepNo state
    (BitVec.ofNat 64 Elflings.mainEntry) (BitVec.ofNat 12 0xc80) stackValue retired 0 0
    0x13 0x01 0x01 0xc8 platform noMMIO bytes interrupts ?_ decode notExpected stackAfterNext
    counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1
    counters.2.2.2.2.2⟩
  rfl

end BinaryFv.Zesu
