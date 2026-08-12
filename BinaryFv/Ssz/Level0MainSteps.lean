import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Instruction.Decode
import BinaryFv.RiscV.Step.ConfiguredMachine
import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.RiscV.Step.Store
import BinaryFv.RiscV.Step.TryStepStackAddiMemory
import BinaryFv.Ssz.Generated.ProgramImage
import BinaryFv.Ssz.MachineContract

/-!
# Concrete Level 0 instructions of the SSZ endpoint

Each theorem below instantiates a target-independent instruction-class lemma with a word named by
the generated production-ELF artifact. No `try_step` execution fact is assumed.
-/

namespace BinaryFv.Ssz

open BinaryFv.Binary
open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register
open MemoryAccessType mem_payload page_based_mem_type

/-- The exact generated Level 0 instruction addresses. -/
def mainGluePcs (pc : BitVec 64) : Prop := pcInRanges Generated.mainGluePcRanges pc

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

/-- The source-register binding needed by a concrete Level 0 `addi`. -/
structure MainAddiSource (state : State) (pc : BitVec 64) (source : regidx) where
  value : BitVec 64
  read : Runs (rX_bits source)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) value

private theorem main_xreg_write_callback_run (state : State) (register : regidx)
    (data : BitVec 64) : (xreg_write_callback register data).run state = .ok () state := by
  rcases register with ⟨index⟩
  simp [xreg_write_callback, xreg_full_write_callback, reg_name_forwards,
    encdec_reg_forwards, encdec_reg_forwards_matches, get_config_use_abi_names,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad,
    LeanRV64DExecutable.Functions.not]
  rfl

private theorem main_wX_bits_run_x10 (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 10#5) value) state
      { state with regs := state.regs.insert x10 value } () := by
  change Runs (do
    Sail.writeReg x10 (regval_into_reg value)
    xreg_write_callback (.Regidx 10#5) value) state _ ()
  exact Runs.bind (by simpa using writeReg_run state x10 value)
    (main_xreg_write_callback_run _ _ _)

private theorem main_store_dword_step (stepNo : Nat) (state afterWrite : State)
    (pc : Nat) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre mainGluePcs state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (inside : mainGluePcs (BitVec.ofNat 64 pc))
    (loaded : Generated.programImage.fileBytesLoadedFaithfully state.mem)
    (pcFits : pc < 2 ^ 64)
    (read0 : Generated.programImage.readFileByte? pc = some byte0)
    (read1 : Generated.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Generated.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Generated.programImage.readFileByte? (pc + 3) = some byte3)
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
    configured.stepContext (BitVec.ofNat 64 pc) atPc inside
  have loadedAfter : Generated.programImage.fileBytesLoadedFaithfully
      (tryStepStoreAfterIncrement state).mem := by
    simpa [tryStepStoreAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Generated.programImage
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
    (configured : ConfiguredMachinePre mainGluePcs state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x14cb4))
    (loaded : Generated.programImage.fileBytesLoadedFaithfully state.mem)
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
  · obtain ⟨seccfgBits, seccfgRead⟩ := configured.seccfgPresent
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
    (configured : ConfiguredMachinePre mainGluePcs state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x14cb8))
    (loaded : Generated.programImage.fileBytesLoadedFaithfully state.mem)
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
  · obtain ⟨seccfgBits, seccfgRead⟩ := configured.seccfgPresent
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
    (configured : ConfiguredMachinePre mainGluePcs state)
    (atPc : state.regs.get? PC = some 0x14cbc)
    (loaded : Generated.programImage.fileBytesLoadedFaithfully state.mem)
    (source : MainAddiSource state 0x14cbc stackPointer) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cbc with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cbc).regs.insert
            x10 (iTypeResult .ADDI 0 source.value) }
        0x14cc0 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext 0x14cbc atPc (by
      refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Generated.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Generated.programImage
    (tryStepControlFlowAfterIncrement state) 0x14cbc (by native_decide) loadedAfter
    0x13 0x05 0x01 0x00 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x05 : BitVec 8) (0x01 : BitVec 8)
        (0x00 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0, stackPointer, .Regidx 10#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead⟩ := configured.seccfgPresent
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

/-- Production `0x14cb0: addi sp, sp, -896`, including generated fetch and retirement. -/
theorem main_stack_allocate_step (stepNo : Nat) (state : State) (stackValue : BitVec 64)
    (configured : ConfiguredMachinePre mainGluePcs state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 Generated.mainEntry))
    (stackRead : state.regs.get? x2 = some stackValue)
    (loaded : Generated.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStackAddiAfterRetired state (BitVec.ofNat 64 Generated.mainEntry)
        (BitVec.ofNat 12 0xc80) stackValue retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 Generated.mainEntry) atPc (by
      refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Generated.programImage.fileBytesLoadedFaithfully
      (tryStepStackAddiAfterIncrement state).mem := by
    simpa [tryStepStackAddiAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Generated.programImage
    (tryStepStackAddiAfterIncrement state) Generated.mainEntry (by native_decide) loadedAfter
    0x13 0x01 0x01 0xc8 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x01 : BitVec 8) (0x01 : BitVec 8)
        (0xc8 : BitVec 8)))
      (tryStepStackAddiAfterIncrement state) (tryStepStackAddiAfterIncrement state)
      (.ITYPE (BitVec.ofNat 12 0xc80, stackPointer, stackPointer, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead⟩ := configured.seccfgPresent
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
      (0xc8 : BitVec 8) = BitVec.ofNat 32 Generated.mainGlueWordAt14cb0 := by
    native_decide
  have stackAfterNext :
      (stackAddiNextState (tryStepStackAddiAfterIncrement state)
        (BitVec.ofNat 64 Generated.mainEntry)).regs.get? x2 = some stackValue := by
    calc
      _ = (tryStepStackAddiAfterIncrement state).regs.get? x2 := by
        simpa [stackAddiNextState] using
          writeReg_read_unchanged (tryStepStackAddiAfterIncrement state) nextPC x2
            (Sail.BitVec.addInt (BitVec.ofNat 64 Generated.mainEntry) 4) (by decide)
      _ = state.regs.get? x2 := by
        simpa [tryStepStackAddiAfterIncrement] using
          writeReg_read_unchanged state minstret_increment x2 true (by decide)
      _ = some stackValue := stackRead
  refine ⟨retired, tryStepStackAddiRetiresWithFetchMemory stepNo state
    (BitVec.ofNat 64 Generated.mainEntry) (BitVec.ofNat 12 0xc80) stackValue retired 0 0
    0x13 0x01 0x01 0xc8 platform noMMIO bytes interrupts ?_ decode notExpected stackAfterNext
    counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1
    counters.2.2.2.2.2⟩
  rfl

end BinaryFv.Ssz
