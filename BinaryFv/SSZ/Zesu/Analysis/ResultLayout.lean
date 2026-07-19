import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.SSZ.Zesu.Analysis.Decode

namespace BinaryFv.SSZ.Zesu.Analysis

open BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

macro "decode_run" : tactic =>
  `(tactic|
    (unfold Runs
     rw [extDecode_eq]
     simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
       PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
       EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, getThe,
       MonadState.get, MonadStateOf.get, *]
     rfl))

/-- The canonical decoder's success epilogue builds an 832-byte `RawStatelessInput` on its
stack, stores the zero success status at result offset 832, and copies that payload to result. -/
def rawResultSuccessSites : Array Nat := #[0x12f90, 0x12f94, 0x12f98, 0x12f9c, 0x12fa0, 0x12fa4,
  0x12fa8]

def rawResultSuccessWords : Array Nat := #[0x61613023, 0x60913423, 0x28013503, 0x34051023,
  0x2d010593, 0x34000613, 0xd44fd06f]

/-- This fact is checked directly against immutable ELF bytes, not source or debug mappings. -/
def rawResultSuccessBlockValid : Bool :=
  rawResultSuccessSites.zip rawResultSuccessWords |>.all fun entry =>
    Artifact.programImage.readU32LE? entry.1 == some entry.2

theorem raw_result_success_block_valid : rawResultSuccessBlockValid = true := by
  native_decide

/-- The decoder writes chain-config fields into the final root-object tail before result copy.
The stores cover offsets 736, 744, 752/760, 768/776, and 784/792/800/808 relative to the root. -/
def rawChainConfigResultStoreSites : Array Nat := #[
  0x12e64, 0x12e68, 0x12e6c, 0x12e70, 0x12e8c, 0x12e90, 0x12e94, 0x12e98, 0x12e9c, 0x12ea0]

def rawChainConfigResultStoreWords : Array Nat := #[
  0x5ce13023, 0x5cf13423, 0x5d013823, 0x5d113c23, 0x5a813823, 0x5ba13c23, 0x5f613023,
  0x5f513423, 0x5f313823, 0x5f210c23]

/-- The field-placement evidence is checked only against the immutable decoder image. -/
def rawChainConfigResultStoresValid : Bool :=
  rawChainConfigResultStoreSites.zip rawChainConfigResultStoreWords |>.all fun entry =>
    Artifact.programImage.readU32LE? entry.1 == some entry.2

theorem raw_chain_config_result_stores_valid : rawChainConfigResultStoresValid = true := by
  native_decide

/-- Generated Sail decodes the ELF-pinned stores that materialize the chain-config tail of the
stack root.  This fixes each source register and stack offset without asserting an unobserved Zig
optional-value encoding. -/
theorem raw_chain_config_result_stores_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x5a813823 : BitVec 32)) state state
        (.STORE (1456#12, .Regidx 8#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5ba13c23 : BitVec 32)) state state
        (.STORE (1464#12, .Regidx 26#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5ce13023 : BitVec 32)) state state
        (.STORE (1472#12, .Regidx 14#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5cf13423 : BitVec 32)) state state
        (.STORE (1480#12, .Regidx 15#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5d013823 : BitVec 32)) state state
        (.STORE (1488#12, .Regidx 16#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5d113c23 : BitVec 32)) state state
        (.STORE (1496#12, .Regidx 17#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f613023 : BitVec 32)) state state
        (.STORE (1504#12, .Regidx 22#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f513423 : BitVec 32)) state state
        (.STORE (1512#12, .Regidx 21#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f313823 : BitVec 32)) state state
        (.STORE (1520#12, .Regidx 19#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f210c23 : BitVec 32)) state state
        (.STORE (1528#12, .Regidx 18#5, .Regidx 2#5, 1)) := by
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  decode_run

/-- The present-blob-schedule branch begins by loading byte zero of its checked 24-byte span. -/
theorem raw_blob_schedule_first_lbu_image_bytes :
    Artifact.programImage.readByte? 0x12cbc = some 0x03 ∧
      Artifact.programImage.readByte? 0x12cbd = some 0xc5 ∧
        Artifact.programImage.readByte? 0x12cbe = some 0x0b ∧
          Artifact.programImage.readByte? 0x12cbf = some 0x00 := by
  native_decide

/-- The first present-blob-schedule read is fetched from the immutable canonical ELF image. -/
theorem raw_blob_schedule_first_lbu_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cbc)
      0x03#8 0xc5#8 0x0b#8 0x00#8 := by
  rcases raw_blob_schedule_first_lbu_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cbc (by omega)
    afterIncrement 0x03 0xc5 0x0b 0x00 read0 read1 read2 read3

/-- Generated Sail decodes the ELF-pinned first byte load of the present schedule payload. -/
theorem raw_blob_schedule_first_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x03#8 0xc5#8 0x0b#8 0x00#8)) state state
      (.LOAD (0#12, .Regidx 23#5, .Regidx 10#5, true, 1)) := by
  decode_run

private theorem rX_x23_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x23 = some value) :
    Runs (rX_bits (.Regidx 23#5)) state state value := by
  have index : (Sail.BitVec.toNatInt (23#5)).toNat = 23 := by decide
  unfold Runs
  simp [rX_bits, rX, index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
    EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg]

private theorem wX_x10_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 10#5) value) state { state with regs := state.regs.insert x10 value } () := by
  have index : (Sail.BitVec.toNatInt (10#5)).toNat = 10 := by decide
  unfold Runs
  simp [wX_bits, wX, PreSail.writeReg, index, EStateM.run, EStateM.bind, EStateM.modifyGet,
    EStateM.pure, EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet, modify,
    xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
    encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
    LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg]

private theorem raw_blob_schedule_first_lbu_address (state : State)
    (base mstatusBits mseccfgBits : BitVec 64)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled) :
    Runs (get_transformed_data_addr (.Regidx 23#5) 0#64
      (MemoryAccessType.Load mem_payload.Data) 1) state state
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 0#64))) := by
  exact get_transformed_data_addr_machine_load_run state (.Regidx 23#5) base 0#64 mstatusBits
    mseccfgBits (rX_x23_run state base baseRead) mstatusRead privilegeRead mprvZero mseccfgRead
    pmmDisabled

/-- The first schedule-payload byte read executes from `s7` and writes zero-extended `a0`. -/
theorem raw_blob_schedule_first_lbu_execute (state : State)
    (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr base) 1 false false false) state state (.Ok data)) :
    Runs (execute_LOAD 0#12 (.Regidx 23#5) (.Regidx 10#5) true 1) state
      { state with regs := state.regs.insert x10 (zero_extend (m := 64) data) }
      (.Retire_Success ()) := by
  apply execute_LOAD_run state _ 0#12 (.Regidx 23#5) (.Regidx 10#5) true 1 data (by decide)
  · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 0#12)
        (MemoryAccessType.Load mem_payload.Data) 1) state state
        (.Ext_DataAddr_OK (virtaddr.Virtaddr base)) := by
      simpa using raw_blob_schedule_first_lbu_address state base mstatusBits mseccfgBits baseRead
        mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled
    exact vmem_read_byte_run state (.Regidx 23#5) (sign_extend (m := 64) 0#12) base mstatusBits
      data mstatusRead privilegeRead mprvZero address (BinaryFv.RiscV.is_aligned_vaddr_one _)
      (by simpa using hread)
  · exact wX_x10_run state (zero_extend (m := 64) data)

end BinaryFv.SSZ.Zesu.Analysis
