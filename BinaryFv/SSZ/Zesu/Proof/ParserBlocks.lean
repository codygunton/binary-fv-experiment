import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.SSZ.Zesu.Analysis.Primitives
import SizzLean.Spec.Deserialize

namespace BinaryFv.SSZ.Zesu.Proof

open BinaryFv BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

private macro "decode_run" : tactic =>
  `(tactic|
    (unfold Runs
     rw [extDecode_eq]
     simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
       PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
       EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, getThe,
       MonadState.get, MonadStateOf.get, *]
     rfl))

/-- The parser's `s8` base register read is the generated `rX_bits x24` action. -/
private theorem rX_x24_run (state : State) (base : BitVec 64)
    (stored : state.regs.get? x24 = some base) :
    Runs (rX_bits (.Regidx 24#5)) state state base := by
  have index : (Sail.BitVec.toNatInt (24#5)).toNat = 24 := by decide
  unfold Runs
  simp [rX_bits, rX, index, stored, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

private macro "gen_rx_run" idx:num " ↦ " reg:ident ", " name:ident : command =>
  `(theorem $name (state : State) (value : BitVec 64)
      (stored : state.regs.get? $reg = some value) :
      Runs (rX_bits (.Regidx (BitVec.ofNat 5 $idx))) state state value := by
    have index : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [rX_bits, rX, index, stored, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
      regval_from_reg])

gen_rx_run 11 ↦ x11, rX_x11_run
gen_rx_run 12 ↦ x12, rX_x12_run
gen_rx_run 13 ↦ x13, rX_x13_run
gen_rx_run 5 ↦ x5, rX_x5_run
gen_rx_run 28 ↦ x28, rX_x28_run
gen_rx_run 14 ↦ x14, rX_x14_run
gen_rx_run 15 ↦ x15, rX_x15_run
gen_rx_run 16 ↦ x16, rX_x16_run
gen_rx_run 17 ↦ x17, rX_x17_run
gen_rx_run 6 ↦ x6, rX_x6_run

private macro "gen_wx_run" idx:num " ↦ " reg:ident ", " name:ident : command =>
  `(theorem $name (state : State) (value : BitVec 64) :
      Runs (wX_bits (.Regidx (BitVec.ofNat 5 $idx)) value) state
        { state with regs := state.regs.insert $reg value } () := by
    have index : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [wX_bits, wX, PreSail.writeReg, index, EStateM.run, EStateM.bind, EStateM.modifyGet,
      EStateM.pure, EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet, modify,
      xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
      encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
      LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg])

gen_wx_run 5 ↦ x5, wX_x5_run
gen_wx_run 11 ↦ x11, wX_x11_run
gen_wx_run 12 ↦ x12, wX_x12_run
gen_wx_run 13 ↦ x13, wX_x13_run
gen_wx_run 18 ↦ x18, wX_x18_run
gen_wx_run 28 ↦ x28, wX_x28_run
gen_wx_run 14 ↦ x14, wX_x14_run
gen_wx_run 15 ↦ x15, wX_x15_run
gen_wx_run 16 ↦ x16, wX_x16_run
gen_wx_run 17 ↦ x17, wX_x17_run
gen_wx_run 6 ↦ x6, wX_x6_run

/-- Each byte of the parser's native 32-bit assembly is addressed directly from `s8`: under the
configured Machine/Bare/PMM-disabled platform, the generated address action returns `s8 + imm`. -/
theorem raw_parser_u32_lbu_address (state : State) (imm base mstatusBits mseccfgBits : BitVec 64)
    (baseRead : state.regs.get? x24 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled) :
    Runs (get_transformed_data_addr (.Regidx 24#5) imm (MemoryAccessType.Load mem_payload.Data) 1)
      state state (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + imm))) := by
  exact get_transformed_data_addr_machine_load_run state (.Regidx 24#5) base imm mstatusBits
    mseccfgBits (rX_x24_run state base baseRead) mstatusRead privilegeRead mprvZero mseccfgRead
    pmmDisabled

/-- Shared generated-Sail execution shape for the adjacent `s8`-based byte reads. -/
private macro "define_adjacent_lbu_execute " name:ident " " imm:num " " rdidx:num " ↦ " rd:ident ", " write:ident : command =>
  `(theorem $name (state : State)
      (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
      (baseRead : state.regs.get? x24 = some base)
      (mstatusRead : state.regs.get? mstatus = some mstatusBits)
      (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
      (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
      (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
      (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
      (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
        (physaddr.Physaddr (base + sign_extend (m := 64) (BitVec.ofNat 12 $imm))) 1 false false false)
        state state (.Ok data)) :
      Runs (execute_LOAD (BitVec.ofNat 12 $imm) (.Regidx 24#5)
        (.Regidx (BitVec.ofNat 5 $rdidx)) true 1) state
        { state with regs := state.regs.insert $rd (zero_extend (m := 64) data) }
        (.Retire_Success ()) := by
    apply execute_LOAD_run state _ (BitVec.ofNat 12 $imm) (.Regidx 24#5)
      (.Regidx (BitVec.ofNat 5 $rdidx)) true 1 data (by decide)
    · exact vmem_read_byte_run state (.Regidx 24#5)
        (sign_extend (m := 64) (BitVec.ofNat 12 $imm))
        (base + sign_extend (m := 64) (BitVec.ofNat 12 $imm)) mstatusBits data mstatusRead
        privilegeRead mprvZero
        (raw_parser_u32_lbu_address state (sign_extend (m := 64) (BitVec.ofNat 12 $imm)) base
          mstatusBits mseccfgBits baseRead mstatusRead privilegeRead mprvZero mseccfgRead
          pmmDisabled)
        (is_aligned_vaddr_one _) hread
    · exact $write state (zero_extend (m := 64) data))

define_adjacent_lbu_execute raw_parser_u32_adjacent_first_lbu_execute 504 14 ↦ x14, wX_x14_run
define_adjacent_lbu_execute raw_parser_u32_adjacent_second_lbu_execute 505 15 ↦ x15, wX_x15_run
define_adjacent_lbu_execute raw_parser_u32_adjacent_third_lbu_execute 506 16 ↦ x16, wX_x16_run
define_adjacent_lbu_execute raw_parser_u32_adjacent_fourth_lbu_execute 507 17 ↦ x17, wX_x17_run
define_adjacent_lbu_execute raw_parser_u32_next_word_first_lbu_execute 508 11 ↦ x11, wX_x11_run
define_adjacent_lbu_execute raw_parser_u32_next_word_second_lbu_execute 509 13 ↦ x13, wX_x13_run
define_adjacent_lbu_execute raw_parser_u32_next_word_third_lbu_execute 510 5 ↦ x5, wX_x5_run
define_adjacent_lbu_execute raw_parser_u32_next_word_fourth_lbu_execute 511 6 ↦ x6, wX_x6_run

/-- The first of the parser's four native-word byte loads executes with its concrete `s8 + 436`
address and writes the zero-extended byte to `t0`; the physical read itself remains an explicit
runtime premise. -/
theorem raw_parser_u32_first_lbu_execute (state : State)
    (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
    (baseRead : state.regs.get? x24 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 436#12)) 1 false false false)
      state state (.Ok data)) :
    Runs (execute_LOAD 436#12 (.Regidx 24#5) (.Regidx 5#5) true 1) state
      { state with regs := state.regs.insert x5 (zero_extend (m := 64) data) }
      (.Retire_Success ()) := by
  apply execute_LOAD_run state _ 436#12 (.Regidx 24#5) (.Regidx 5#5) true 1 data (by decide)
  · exact vmem_read_byte_run state (.Regidx 24#5) (sign_extend (m := 64) 436#12)
      (base + sign_extend (m := 64) 436#12) mstatusBits data mstatusRead privilegeRead mprvZero
      (raw_parser_u32_lbu_address state (sign_extend (m := 64) 436#12) base mstatusBits mseccfgBits
        baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled)
      (is_aligned_vaddr_one _) hread
  · exact wX_x5_run state (zero_extend (m := 64) data)

theorem raw_parser_u32_second_lbu_execute (state : State)
    (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
    (baseRead : state.regs.get? x24 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 437#12)) 1 false false false)
      state state (.Ok data)) :
    Runs (execute_LOAD 437#12 (.Regidx 24#5) (.Regidx 11#5) true 1) state
      { state with regs := state.regs.insert x11 (zero_extend (m := 64) data) }
      (.Retire_Success ()) := by
  apply execute_LOAD_run state _ 437#12 (.Regidx 24#5) (.Regidx 11#5) true 1 data (by decide)
  · exact vmem_read_byte_run state (.Regidx 24#5) (sign_extend (m := 64) 437#12)
      (base + sign_extend (m := 64) 437#12) mstatusBits data mstatusRead privilegeRead mprvZero
      (raw_parser_u32_lbu_address state (sign_extend (m := 64) 437#12) base mstatusBits mseccfgBits
        baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled)
      (is_aligned_vaddr_one _) hread
  · exact wX_x11_run state (zero_extend (m := 64) data)

theorem raw_parser_u32_third_lbu_execute (state : State)
    (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
    (baseRead : state.regs.get? x24 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 438#12)) 1 false false false)
      state state (.Ok data)) :
    Runs (execute_LOAD 438#12 (.Regidx 24#5) (.Regidx 12#5) true 1) state
      { state with regs := state.regs.insert x12 (zero_extend (m := 64) data) }
      (.Retire_Success ()) := by
  apply execute_LOAD_run state _ 438#12 (.Regidx 24#5) (.Regidx 12#5) true 1 data (by decide)
  · exact vmem_read_byte_run state (.Regidx 24#5) (sign_extend (m := 64) 438#12)
      (base + sign_extend (m := 64) 438#12) mstatusBits data mstatusRead privilegeRead mprvZero
      (raw_parser_u32_lbu_address state (sign_extend (m := 64) 438#12) base mstatusBits mseccfgBits
        baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled)
      (is_aligned_vaddr_one _) hread
  · exact wX_x12_run state (zero_extend (m := 64) data)

theorem raw_parser_u32_fourth_lbu_execute (state : State)
    (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
    (baseRead : state.regs.get? x24 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 439#12)) 1 false false false)
      state state (.Ok data)) :
    Runs (execute_LOAD 439#12 (.Regidx 24#5) (.Regidx 13#5) true 1) state
      { state with regs := state.regs.insert x13 (zero_extend (m := 64) data) }
      (.Retire_Success ()) := by
  apply execute_LOAD_run state _ 439#12 (.Regidx 24#5) (.Regidx 13#5) true 1 data (by decide)
  · exact vmem_read_byte_run state (.Regidx 24#5) (sign_extend (m := 64) 439#12)
      (base + sign_extend (m := 64) 439#12) mstatusBits data mstatusRead privilegeRead mprvZero
      (raw_parser_u32_lbu_address state (sign_extend (m := 64) 439#12) base mstatusBits mseccfgBits
        baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled)
      (is_aligned_vaddr_one _) hread
  · exact wX_x13_run state (zero_extend (m := 64) data)

theorem raw_parser_u32_first_lbu_image_bytes :
    Artifact.programImage.readByte? 0x10764 = some 0x83 ∧
      Artifact.programImage.readByte? 0x10765 = some 0x42 ∧
        Artifact.programImage.readByte? 0x10766 = some 0x4c ∧
          Artifact.programImage.readByte? 0x10767 = some 0x1b := by
  native_decide

theorem raw_parser_u32_first_lbu_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764)
      0x83#8 0x42#8 0x4c#8 0x1b := by
  rcases raw_parser_u32_first_lbu_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10764 (by omega)
    afterIncrement 0x83 0x42 0x4c 0x1b read0 read1 read2 read3

theorem raw_parser_u32_first_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x83#8 0x42#8 0x4c#8 0x1b)) state state
      (.LOAD (436#12, .Regidx 24#5, .Regidx 5#5, true, 1)) := by
  decode_run

/-- The second byte load of the native 32-bit parser word is encoded immediately after the first. -/
theorem raw_parser_u32_second_lbu_image_bytes :
    Artifact.programImage.readByte? 0x10768 = some 0x83 ∧
      Artifact.programImage.readByte? 0x10769 = some 0x45 ∧
        Artifact.programImage.readByte? 0x1076a = some 0x5c ∧
          Artifact.programImage.readByte? 0x1076b = some 0x1b := by
  native_decide

theorem raw_parser_u32_second_lbu_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10768)
      0x83#8 0x45#8 0x5c#8 0x1b := by
  rcases raw_parser_u32_second_lbu_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10768 (by omega)
    afterIncrement 0x83 0x45 0x5c 0x1b read0 read1 read2 read3

theorem raw_parser_u32_second_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x83#8 0x45#8 0x5c#8 0x1b)) state state
      (.LOAD (437#12, .Regidx 24#5, .Regidx 11#5, true, 1)) := by
  decode_run

theorem raw_parser_u32_third_lbu_image_bytes :
    Artifact.programImage.readByte? 0x1076c = some 0x03 ∧
      Artifact.programImage.readByte? 0x1076d = some 0x46 ∧
        Artifact.programImage.readByte? 0x1076e = some 0x6c ∧
          Artifact.programImage.readByte? 0x1076f = some 0x1b := by
  native_decide

theorem raw_parser_u32_third_lbu_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1076c)
      0x03#8 0x46#8 0x6c#8 0x1b := by
  rcases raw_parser_u32_third_lbu_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x1076c (by omega)
    afterIncrement 0x03 0x46 0x6c 0x1b read0 read1 read2 read3

theorem raw_parser_u32_third_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x03#8 0x46#8 0x6c#8 0x1b)) state state
      (.LOAD (438#12, .Regidx 24#5, .Regidx 12#5, true, 1)) := by
  decode_run

theorem raw_parser_u32_fourth_lbu_image_bytes :
    Artifact.programImage.readByte? 0x10770 = some 0x83 ∧
      Artifact.programImage.readByte? 0x10771 = some 0x46 ∧
        Artifact.programImage.readByte? 0x10772 = some 0x7c ∧
          Artifact.programImage.readByte? 0x10773 = some 0x1b := by
  native_decide

theorem raw_parser_u32_fourth_lbu_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10770)
      0x83#8 0x46#8 0x7c#8 0x1b := by
  rcases raw_parser_u32_fourth_lbu_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10770 (by omega)
    afterIncrement 0x83 0x46 0x7c 0x1b read0 read1 read2 read3

theorem raw_parser_u32_fourth_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x83#8 0x46#8 0x7c#8 0x1b)) state state
      (.LOAD (439#12, .Regidx 24#5, .Regidx 13#5, true, 1)) := by
  decode_run

/-- The first byte of the parser's native 32-bit assembly retires from its canonical PC.
Its fetch and decode are immutable-ELF facts, while its execute premise is derived from the
concrete `s8 + 436` byte load rather than an assumed register write. -/
theorem raw_parser_u32_first_lbu_retire (stepNo : Nat) (state afterExec : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 436#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764))
      (.Ok data))
    (afterExecEq : afterExec = { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764) with regs :=
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10764)).regs.insert x5 (zero_extend (m := 64) data) })
    (nextPcAfterExec : afterExec.regs.get? nextPC = some (BitVec.ofNat 64 0x10768))
    (hartAgree : afterExec.regs.get? hart_state =
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state)
    (incrementAgree : afterExec.regs.get? minstret_increment =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment)
    (retiredAgree : afterExec.regs.get? minstret =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired afterExec (BitVec.ofNat 64 0x10768) retired) false := by
  subst afterExec
  have bytes := raw_parser_u32_first_lbu_fetch state loaded
  have decode := raw_parser_u32_first_lbu_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  exact tryStepFallThroughRetires stepNo state afterExec (BitVec.ofNat 64 0x10764) retired inhibit
    config 0x83#8 0x42#8 0x4c#8 0x1b (.LOAD (436#12, .Regidx 24#5, .Regidx 5#5, true, 1))
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_first_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    nextPcAfterExec hartAgree incrementAgree retiredAgree hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- Fully concrete post-state form of `raw_parser_u32_first_lbu_retire`.  The generated `lbu`
write changes only `t0`, so the fall-through PC and retirement bookkeeping agreements follow by
register-map preservation. -/
theorem raw_parser_u32_first_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10764)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 436#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10764)).regs.insert x5 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x10768) retired) false := by
  apply raw_parser_u32_first_lbu_retire stepNo state _ base mstatusBits retired mseccfgBits data
    inhibit config loaded platform fetchNoMMIO interrupts notExpected privilege mseccfg baseRead
    mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread rfl
  · calc
      ({ coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764)
        with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10764)).regs.insert x5 (zero_extend (m := 64) data) }).regs.get? nextPC =
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10764)).regs.get? nextPC := by
            simpa using writeReg_read_unchanged
              (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764))
              x5 nextPC (zero_extend (m := 64) data) (by decide)
      _ = some (BitVec.ofNat 64 0x10768) := by native_decide
  · calc
      ({ coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764)
        with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10764)).regs.insert x5 (zero_extend (m := 64) data) }).regs.get? hart_state =
          (tryStepControlFlowAfterIncrement state).regs.get? hart_state := by
            simp [coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
  · calc
      ({ coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764)
        with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10764)).regs.insert x5 (zero_extend (m := 64) data) }).regs.get? minstret_increment =
          (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment := by
            simp [coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
  · calc
      ({ coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10764)
        with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10764)).regs.insert x5 (zero_extend (m := 64) data) }).regs.get? minstret =
          (tryStepControlFlowAfterIncrement state).regs.get? minstret := by
            simp [coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
  · exact hartRead
  · exact inhibitRead
  · exact configRead
  · exact notInhibited
  · exact machineEnabled
  · exact retiredRead

/-- The second native-word byte load retires with its generated `a1` write and no assumed
postlude agreements. -/
theorem raw_parser_u32_second_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10768))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10768))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10768)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10768)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10768)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10768)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 437#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10768))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10768))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10768)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10768)).regs.insert x11 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x1076c) retired) false := by
  have bytes := raw_parser_u32_second_lbu_fetch state loaded
  have decode := raw_parser_u32_second_lbu_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10768)
    retired inhibit config 0x83#8 0x45#8 0x5c#8 0x1b
    (.LOAD (437#12, .Regidx 24#5, .Regidx 11#5, true, 1)) x11 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_second_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10768))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The third adjacent-field byte read retires at its actual ELF PC. -/
theorem raw_parser_u32_adjacent_third_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1077c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1077c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1077c)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1077c)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1077c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1077c)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 506#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1077c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1077c))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1077c)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x1077c)).regs.insert x16 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x10780) retired) false := by
  have image : Artifact.programImage.readByte? 0x1077c = some 0x03 ∧
      Artifact.programImage.readByte? 0x1077d = some 0x48 ∧
        Artifact.programImage.readByte? 0x1077e = some 0xac ∧
          Artifact.programImage.readByte? 0x1077f = some 0x1f := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x1077c (by omega) afterIncrement
    0x03 0x48 0xac 0x1f read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0x48#8 0xac#8 0x1f))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (506#12, .Regidx 24#5, .Regidx 16#5, true, 1)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x1077c)
    retired inhibit config 0x03#8 0x48#8 0xac#8 0x1f
    (.LOAD (506#12, .Regidx 24#5, .Regidx 16#5, true, 1)) x16 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_adjacent_third_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1077c))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The fourth adjacent-field byte read retires at its actual ELF PC. -/
theorem raw_parser_u32_adjacent_fourth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10780))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10780))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10780)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10780)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10780)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10780)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 507#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10780))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10780))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10780)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10780)).regs.insert x17 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x10784) retired) false := by
  have image : Artifact.programImage.readByte? 0x10780 = some 0x83 ∧
      Artifact.programImage.readByte? 0x10781 = some 0x48 ∧
        Artifact.programImage.readByte? 0x10782 = some 0xbc ∧
          Artifact.programImage.readByte? 0x10783 = some 0x1f := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10780 (by omega) afterIncrement
    0x83 0x48 0xbc 0x1f read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0x48#8 0xbc#8 0x1f))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (507#12, .Regidx 24#5, .Regidx 17#5, true, 1)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10780)
    retired inhibit config 0x83#8 0x48#8 0xbc#8 0x1f
    (.LOAD (507#12, .Regidx 24#5, .Regidx 17#5, true, 1)) x17 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_adjacent_fourth_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10780))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- Kernel-checked composition of the four real parser reads between the first word and its
shift/OR assembly.  Each premise can now be supplied by its exact-PC retirement theorem. -/
theorem raw_parser_u32_adjacent_four_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 : State)
    (first : Runs (try_step stepNo false) state0 state1 false)
    (second : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (third : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (fourth : Runs (try_step (stepNo + 3) false) state3 state4 false) :
    Trace stepNo 4 state0 state4 := by
  trace_steps [first, second, third, fourth]

/-- The first byte read of the next adjacent word retires at its actual ELF PC. -/
theorem raw_parser_u32_next_word_first_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10798))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10798))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10798)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10798)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10798)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10798)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 508#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10798))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10798))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10798)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10798)).regs.insert x11 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x1079c) retired) false := by
  have image : Artifact.programImage.readByte? 0x10798 = some 0x83 ∧
      Artifact.programImage.readByte? 0x10799 = some 0x45 ∧
        Artifact.programImage.readByte? 0x1079a = some 0xcc ∧
          Artifact.programImage.readByte? 0x1079b = some 0x1f := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10798 (by omega) afterIncrement
    0x83 0x45 0xcc 0x1f read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0x45#8 0xcc#8 0x1f))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (508#12, .Regidx 24#5, .Regidx 11#5, true, 1)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10798)
    retired inhibit config 0x83#8 0x45#8 0xcc#8 0x1f
    (.LOAD (508#12, .Regidx 24#5, .Regidx 11#5, true, 1)) x11 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_next_word_first_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10798))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The second byte read of the next adjacent word retires at its actual ELF PC. -/
theorem raw_parser_u32_next_word_second_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1079c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1079c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1079c)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1079c)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1079c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1079c)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 509#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1079c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1079c))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1079c)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x1079c)).regs.insert x13 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x107a0) retired) false := by
  have image : Artifact.programImage.readByte? 0x1079c = some 0x83 ∧
      Artifact.programImage.readByte? 0x1079d = some 0x46 ∧
        Artifact.programImage.readByte? 0x1079e = some 0xdc ∧
          Artifact.programImage.readByte? 0x1079f = some 0x1f := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x1079c (by omega) afterIncrement
    0x83 0x46 0xdc 0x1f read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0x46#8 0xdc#8 0x1f))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (509#12, .Regidx 24#5, .Regidx 13#5, true, 1)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x1079c)
    retired inhibit config 0x83#8 0x46#8 0xdc#8 0x1f
    (.LOAD (509#12, .Regidx 24#5, .Regidx 13#5, true, 1)) x13 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_next_word_second_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1079c))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The third byte read of the next adjacent word retires at its actual ELF PC. -/
theorem raw_parser_u32_next_word_third_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x107a0))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x107a0))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x107a0)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x107a0)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x107a0)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x107a0)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 510#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x107a0))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x107a0))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x107a0)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x107a0)).regs.insert x5 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x107a4) retired) false := by
  have image : Artifact.programImage.readByte? 0x107a0 = some 0x83 ∧
      Artifact.programImage.readByte? 0x107a1 = some 0x42 ∧
        Artifact.programImage.readByte? 0x107a2 = some 0xec ∧
          Artifact.programImage.readByte? 0x107a3 = some 0x1f := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x107a0 (by omega) afterIncrement
    0x83 0x42 0xec 0x1f read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0x42#8 0xec#8 0x1f))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (510#12, .Regidx 24#5, .Regidx 5#5, true, 1)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x107a0)
    retired inhibit config 0x83#8 0x42#8 0xec#8 0x1f
    (.LOAD (510#12, .Regidx 24#5, .Regidx 5#5, true, 1)) x5 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_next_word_third_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x107a0))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The third native-word byte load retires with its generated `a2` write and no assumed
postlude agreements. -/
theorem raw_parser_u32_third_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1076c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1076c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1076c)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1076c)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1076c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1076c)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 438#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1076c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1076c))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1076c)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x1076c)).regs.insert x12 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x10770) retired) false := by
  have bytes := raw_parser_u32_third_lbu_fetch state loaded
  have decode := raw_parser_u32_third_lbu_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x1076c)
    retired inhibit config 0x03#8 0x46#8 0x6c#8 0x1b
    (.LOAD (438#12, .Regidx 24#5, .Regidx 12#5, true, 1)) x12 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_third_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1076c))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The fourth native-word byte load retires with its generated `a3` write and no assumed
postlude agreements. -/
theorem raw_parser_u32_fourth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10770))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10770))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10770)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10770)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10770)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10770)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 439#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10770))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10770))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10770)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10770)).regs.insert x13 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x10774) retired) false := by
  have bytes := raw_parser_u32_fourth_lbu_fetch state loaded
  have decode := raw_parser_u32_fourth_lbu_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10770)
    retired inhibit config 0x83#8 0x46#8 0x7c#8 0x1b
    (.LOAD (439#12, .Regidx 24#5, .Regidx 13#5, true, 1)) x13 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_fourth_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10770))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- Kernel-checked composition of the four consecutive native-word byte-load retirements.  The
four concrete `raw_parser_u32_*_lbu_retire_exact` theorems provide the hypotheses; their dynamic
machine premises are intentionally kept at the individual states of this trace. -/
theorem raw_parser_u32_four_lbu_trace (stepNo : Nat) (state0 state1 state2 state3 state4 : State)
    (first : Runs (try_step stepNo false) state0 state1 false)
    (second : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (third : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (fourth : Runs (try_step (stepNo + 3) false) state3 state4 false) :
    Trace stepNo 4 state0 state4 := by
  trace_steps [first, second, third, fourth]

/-- The first byte-assembly shift is the generated `slli a1, a1, 8` action. -/
theorem raw_parser_u32_second_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x11 = some value) :
    Runs (execute_SHIFTIOP 8#6 (.Regidx 11#5) (.Regidx 11#5) .SLLI) state
      { state with regs := state.regs.insert x11
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 8#6 (.Regidx 11#5) (.Regidx 11#5) value
    (rX_x11_run state value stored)
    (wX_x11_run state
      (Sail.shift_bits_left value
        (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_parser_u32_second_byte_shift_image_bytes :
    Artifact.programImage.readByte? 0x10784 = some 0x93 ∧
      Artifact.programImage.readByte? 0x10785 = some 0x95 ∧
        Artifact.programImage.readByte? 0x10786 = some 0x85 ∧
          Artifact.programImage.readByte? 0x10787 = some 0x00 := by
  native_decide

theorem raw_parser_u32_second_byte_shift_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10784)
      0x93#8 0x95#8 0x85#8 0x00#8 := by
  rcases raw_parser_u32_second_byte_shift_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10784 (by omega)
    afterIncrement 0x93 0x95 0x85 0x00 read0 read1 read2 read3

theorem raw_parser_u32_second_byte_shift_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x93#8 0x95#8 0x85#8 0x00#8)) state state
      (.SHIFTIOP (8#6, .Regidx 11#5, .Regidx 11#5, .SLLI)) := by
  decode_run

theorem raw_parser_u32_second_byte_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10784))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10784))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10784)).regs.get? x11 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10784)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10784)).regs.insert x11
              (Sail.shift_bits_left value
                (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) }
        (BitVec.ofNat 64 0x10788) retired) false := by
  have bytes := raw_parser_u32_second_byte_shift_fetch state loaded
  have decode := raw_parser_u32_second_byte_shift_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10784)
    retired inhibit config 0x93#8 0x95#8 0x85#8 0x00#8
    (.SHIFTIOP (8#6, .Regidx 11#5, .Regidx 11#5, .SLLI)) x11
    (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_second_byte_shift_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10784))
      value stored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_parser_u32_third_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x12 = some value) :
    Runs (execute_SHIFTIOP 16#6 (.Regidx 12#5) (.Regidx 12#5) .SLLI) state
      { state with regs := state.regs.insert x12
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 16#6 (.Regidx 12#5) (.Regidx 12#5) value
    (rX_x12_run state value stored)
    (wX_x12_run state
      (Sail.shift_bits_left value
        (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_parser_u32_third_byte_shift_image_bytes :
    Artifact.programImage.readByte? 0x10788 = some 0x13 ∧
      Artifact.programImage.readByte? 0x10789 = some 0x16 ∧
        Artifact.programImage.readByte? 0x1078a = some 0x06 ∧
          Artifact.programImage.readByte? 0x1078b = some 0x01 := by
  native_decide

theorem raw_parser_u32_third_byte_shift_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10788)
      0x13#8 0x16#8 0x06#8 0x01#8 := by
  rcases raw_parser_u32_third_byte_shift_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10788 (by omega)
    afterIncrement 0x13 0x16 0x06 0x01 read0 read1 read2 read3

theorem raw_parser_u32_third_byte_shift_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x16#8 0x06#8 0x01#8)) state state
      (.SHIFTIOP (16#6, .Regidx 12#5, .Regidx 12#5, .SLLI)) := by
  decode_run

theorem raw_parser_u32_third_byte_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10788))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10788))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10788)).regs.get? x12 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10788)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10788)).regs.insert x12
              (Sail.shift_bits_left value
                (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) }
        (BitVec.ofNat 64 0x1078c) retired) false := by
  have bytes := raw_parser_u32_third_byte_shift_fetch state loaded
  have decode := raw_parser_u32_third_byte_shift_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10788)
    retired inhibit config 0x13#8 0x16#8 0x06#8 0x01#8
    (.SHIFTIOP (16#6, .Regidx 12#5, .Regidx 12#5, .SLLI)) x12
    (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_third_byte_shift_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10788))
      value stored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_parser_u32_fourth_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x13 = some value) :
    Runs (execute_SHIFTIOP 24#6 (.Regidx 13#5) (.Regidx 13#5) .SLLI) state
      { state with regs := state.regs.insert x13
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 24#6 (.Regidx 13#5) (.Regidx 13#5) value
    (rX_x13_run state value stored)
    (wX_x13_run state
      (Sail.shift_bits_left value
        (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_parser_u32_fourth_byte_shift_image_bytes :
    Artifact.programImage.readByte? 0x1078c = some 0x93 ∧
      Artifact.programImage.readByte? 0x1078d = some 0x96 ∧
        Artifact.programImage.readByte? 0x1078e = some 0x86 ∧
          Artifact.programImage.readByte? 0x1078f = some 0x01 := by
  native_decide

theorem raw_parser_u32_fourth_byte_shift_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1078c)
      0x93#8 0x96#8 0x86#8 0x01#8 := by
  rcases raw_parser_u32_fourth_byte_shift_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x1078c (by omega)
    afterIncrement 0x93 0x96 0x86 0x01 read0 read1 read2 read3

theorem raw_parser_u32_fourth_byte_shift_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x93#8 0x96#8 0x86#8 0x01#8)) state state
      (.SHIFTIOP (24#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) := by
  decode_run

theorem raw_parser_u32_fourth_byte_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1078c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1078c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1078c)).regs.get? x13 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1078c)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x1078c)).regs.insert x13
              (Sail.shift_bits_left value
                (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) }
        (BitVec.ofNat 64 0x10790) retired) false := by
  have bytes := raw_parser_u32_fourth_byte_shift_fetch state loaded
  have decode := raw_parser_u32_fourth_byte_shift_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x1078c)
    retired inhibit config 0x93#8 0x96#8 0x86#8 0x01#8
    (.SHIFTIOP (24#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) x13
    (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_fourth_byte_shift_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1078c))
      value stored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_parser_u32_low_half_or_execute (state : State) (low high : BitVec 64)
    (lowStored : state.regs.get? x5 = some low) (highStored : state.regs.get? x11 = some high) :
    Runs (execute_RTYPE (.Regidx 5#5) (.Regidx 11#5) (.Regidx 28#5) .OR) state
      { state with regs := state.regs.insert x28 (high ||| low) } (.Retire_Success ()) := by
  exact execute_RTYPE_or_run state _ (.Regidx 5#5) (.Regidx 11#5) (.Regidx 28#5) high low
    (rX_x11_run state high highStored) (rX_x5_run state low lowStored) (wX_x28_run state (high ||| low))

theorem raw_parser_u32_low_half_or_image_bytes :
    Artifact.programImage.readByte? 0x10790 = some 0x33 ∧
      Artifact.programImage.readByte? 0x10791 = some 0xee ∧
        Artifact.programImage.readByte? 0x10792 = some 0x55 ∧
          Artifact.programImage.readByte? 0x10793 = some 0x00 := by
  native_decide

theorem raw_parser_u32_low_half_or_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10790)
      0x33#8 0xee#8 0x55#8 0x00#8 := by
  rcases raw_parser_u32_low_half_or_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10790 (by omega)
    afterIncrement 0x33 0xee 0x55 0x00 read0 read1 read2 read3

theorem raw_parser_u32_low_half_or_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x33#8 0xee#8 0x55#8 0x00#8)) state state
      (.RTYPE (.Regidx 5#5, .Regidx 11#5, .Regidx 28#5, .OR)) := by
  decode_run

theorem raw_parser_u32_low_half_or_retire_exact (stepNo : Nat) (state : State)
    (low high retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10790))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10790))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10790)).regs.get? x5 = some low)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10790)).regs.get? x11 = some high)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10790)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10790)).regs.insert x28 (high ||| low) }
        (BitVec.ofNat 64 0x10794) retired) false := by
  have bytes := raw_parser_u32_low_half_or_fetch state loaded
  have decode := raw_parser_u32_low_half_or_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10790)
    retired inhibit config 0x33#8 0xee#8 0x55#8 0x00#8
    (.RTYPE (.Regidx 5#5, .Regidx 11#5, .Regidx 28#5, .OR)) x28 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_low_half_or_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10790))
      low high lowStored highStored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_parser_u32_high_half_or_execute (state : State) (mid high : BitVec 64)
    (midStored : state.regs.get? x12 = some mid) (highStored : state.regs.get? x13 = some high) :
    Runs (execute_RTYPE (.Regidx 12#5) (.Regidx 13#5) (.Regidx 12#5) .OR) state
      { state with regs := state.regs.insert x12 (high ||| mid) } (.Retire_Success ()) := by
  exact execute_RTYPE_or_run state _ (.Regidx 12#5) (.Regidx 13#5) (.Regidx 12#5) high mid
    (rX_x13_run state high highStored) (rX_x12_run state mid midStored) (wX_x12_run state (high ||| mid))

theorem raw_parser_u32_high_half_or_image_bytes :
    Artifact.programImage.readByte? 0x10794 = some 0x33 ∧
      Artifact.programImage.readByte? 0x10795 = some 0xe6 ∧
        Artifact.programImage.readByte? 0x10796 = some 0xc6 ∧
          Artifact.programImage.readByte? 0x10797 = some 0x00 := by
  native_decide

theorem raw_parser_u32_high_half_or_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10794)
      0x33#8 0xe6#8 0xc6#8 0x00#8 := by
  rcases raw_parser_u32_high_half_or_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10794 (by omega)
    afterIncrement 0x33 0xe6 0xc6 0x00 read0 read1 read2 read3

theorem raw_parser_u32_high_half_or_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x33#8 0xe6#8 0xc6#8 0x00#8)) state state
      (.RTYPE (.Regidx 12#5, .Regidx 13#5, .Regidx 12#5, .OR)) := by
  decode_run

theorem raw_parser_u32_high_half_or_retire_exact (stepNo : Nat) (state : State)
    (mid high retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10794))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10794))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (midStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10794)).regs.get? x12 = some mid)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10794)).regs.get? x13 = some high)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10794)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10794)).regs.insert x12 (high ||| mid) }
        (BitVec.ofNat 64 0x10798) retired) false := by
  have bytes := raw_parser_u32_high_half_or_fetch state loaded
  have decode := raw_parser_u32_high_half_or_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10794)
    retired inhibit config 0x33#8 0xe6#8 0xc6#8 0x00#8
    (.RTYPE (.Regidx 12#5, .Regidx 13#5, .Regidx 12#5, .OR)) x12 (high ||| mid)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_high_half_or_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10794))
      mid high midStored highStored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_parser_u32_word_or_execute (state : State) (low high : BitVec 64)
    (lowStored : state.regs.get? x28 = some low) (highStored : state.regs.get? x12 = some high) :
    Runs (execute_RTYPE (.Regidx 28#5) (.Regidx 12#5) (.Regidx 18#5) .OR) state
      { state with regs := state.regs.insert x18 (high ||| low) } (.Retire_Success ()) := by
  exact execute_RTYPE_or_run state _ (.Regidx 28#5) (.Regidx 12#5) (.Regidx 18#5) high low
    (rX_x12_run state high highStored) (rX_x28_run state low lowStored) (wX_x18_run state (high ||| low))

theorem raw_parser_u32_word_or_image_bytes :
    Artifact.programImage.readByte? 0x107f4 = some 0x33 ∧
      Artifact.programImage.readByte? 0x107f5 = some 0x69 ∧
        Artifact.programImage.readByte? 0x107f6 = some 0xc6 ∧
          Artifact.programImage.readByte? 0x107f7 = some 0x01 := by
  native_decide

theorem raw_parser_u32_word_or_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x107f4)
      0x33#8 0x69#8 0xc6#8 0x01#8 := by
  rcases raw_parser_u32_word_or_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x107f4 (by omega)
    afterIncrement 0x33 0x69 0xc6 0x01 read0 read1 read2 read3

theorem raw_parser_u32_word_or_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x33#8 0x69#8 0xc6#8 0x01#8)) state state
      (.RTYPE (.Regidx 28#5, .Regidx 12#5, .Regidx 18#5, .OR)) := by
  decode_run

theorem raw_parser_u32_word_or_retire_exact (stepNo : Nat) (state : State)
    (low high retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x107f4))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x107f4))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x107f4)).regs.get? x28 = some low)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x107f4)).regs.get? x12 = some high)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x107f4)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x107f4)).regs.insert x18 (high ||| low) }
        (BitVec.ofNat 64 0x107f8) retired) false := by
  have bytes := raw_parser_u32_word_or_fetch state loaded
  have decode := raw_parser_u32_word_or_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x107f4)
    retired inhibit config 0x33#8 0x69#8 0xc6#8 0x01#8
    (.RTYPE (.Regidx 28#5, .Regidx 12#5, .Regidx 18#5, .OR)) x18 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_word_or_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x107f4))
      low high lowStored highStored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The three shifts and two half-word ORs occupy five contiguous retiring parser instructions. -/
theorem raw_parser_u32_shift_or_prefix_trace
    (stepNo : Nat) (state0 state1 state2 state3 state4 state5 : State)
    (shift8 : Runs (try_step stepNo false) state0 state1 false)
    (shift16 : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (shift24 : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (lowOr : Runs (try_step (stepNo + 3) false) state3 state4 false)
    (highOr : Runs (try_step (stepNo + 4) false) state4 state5 false) :
    Trace stepNo 5 state0 state5 := by
  trace_steps [shift8, shift16, shift24, lowOr, highOr]

/-- Compose the first native word's four reads, the four intervening reads for the next field,
and the five contiguous shifts/ORs.  The middle fragment is deliberately an explicit live trace:
its load values and memory premises must come from the decoder run, rather than being hidden by
an instruction-shape argument. -/
theorem raw_parser_u32_live_prefix_trace
    (stepNo : Nat) (state0 state4 state8 state13 : State)
    (firstWord : Trace stepNo 4 state0 state4)
    (intervening : Trace (stepNo + 4) 4 state4 state8)
    (assembly : Trace (stepNo + 8) 5 state8 state13) :
    Trace stepNo 13 state0 state13 := by
  have reads : Trace stepNo 8 state0 state8 := by
    simpa only [Nat.add_assoc] using Trace.append firstWord intervening
  have combined := Trace.append reads assembly
  norm_num at combined ⊢
  exact combined

/-- The first raw-header `lbu` is encoded at `0x104bc` in the immutable decoder image. -/
theorem raw_header_first_lbu_image_bytes :
    Artifact.programImage.readByte? 0x104bc = some 0x03 ∧
      Artifact.programImage.readByte? 0x104bd = some 0x45 ∧
        Artifact.programImage.readByte? 0x104be = some 0x0a ∧
          Artifact.programImage.readByte? 0x104bf = some 0x00 := by
  native_decide

/-- Register-only retirement bookkeeping preserves the loaded immutable code image. -/
theorem image_loaded_after_increment (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    Artifact.programImage.matchesMemory (tryStepControlFlowAfterIncrement state).mem := by
  simpa [tryStepControlFlowAfterIncrement] using loaded

/-- The generated Sail fetch at the first raw-header read sees its exact ELF instruction bytes. -/
theorem raw_header_first_lbu_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc)
      (BitVec.ofNat 8 0x03) (BitVec.ofNat 8 0x45) (BitVec.ofNat 8 0x0a) (BitVec.ofNat 8 0x00) := by
  rcases raw_header_first_lbu_image_bytes with ⟨read0, read1, read2, read3⟩
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x104bc (by omega)
    (image_loaded_after_increment state loaded) 0x03 0x45 0x0a 0x00 read0 read1 read2 read3

/-- Generated Sail decodes the fetched word at `0x104bc` as `lbu a0, 0(s4)`. -/
theorem raw_header_first_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x03#8 0x45#8 0x0a#8 0x00#8)) state state
      (.LOAD (0#12, .Regidx 20#5, .Regidx 10#5, true, 1)) := by
  decode_run

/-- The first parser `lbu` retires from its canonical PC once its dynamic machine premises hold.
Its fetch bytes and generated-Sail decode are derived here from the immutable Zesu ELF. -/
theorem raw_header_first_lbu_retire (stepNo : Nat) (state afterExec : State)
    (srcBits mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x104bc))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x104bc)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x104bc)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 20#5) (sign_extend (m := 64) 0#12)
      (MemoryAccessType.Load mem_payload.Data) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc))
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (physAccess : Runs (phys_access_check (MemoryAccessType.Load mem_payload.Data)
      page_based_mem_type.PBMT_PMA .Machine (physaddr.Physaddr srcBits) 1 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc)) none)
    (loadNoMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc)) false)
    (hmem : ∀ index (h : index < (BinaryFv.RiscV.Sep.leBytes 1 data).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc)).mem.get?
        (srcBits.toNat + index) = some (BinaryFv.RiscV.Sep.leBytes 1 data)[index])
    (hwrite : Runs (wX_bits (.Regidx 10#5) (zero_extend (m := 64) data))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc)) afterExec ())
    (nextPcAfterExec : afterExec.regs.get? nextPC = some (BitVec.ofNat 64 0x104c0))
    (hartAgree : afterExec.regs.get? hart_state =
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state)
    (incrementAgree : afterExec.regs.get? minstret_increment =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment)
    (retiredAgree : afterExec.regs.get? minstret =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired afterExec (BitVec.ofNat 64 0x104c0) retired) false := by
  have bytes := raw_header_first_lbu_fetch state loaded
  have decode := raw_header_first_lbu_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  exact tryStepFallThroughRetires stepNo state afterExec (BitVec.ofNat 64 0x104bc) retired inhibit
    config 0x03#8 0x45#8 0x0a#8 0x00#8 (.LOAD (0#12, .Regidx 20#5, .Regidx 10#5, true, 1))
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (execute_LOAD_lbu_run _ _ 0#12 (.Regidx 20#5) (.Regidx 10#5) srcBits mstatusBits data
      mstatusRead privilegeRead mprvZero addrReg (is_aligned_vaddr_one _) physAccess loadNoMMIO hmem
      hwrite)
    nextPcAfterExec hartAgree incrementAgree retiredAgree hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- The parser's result-status read at `0x11f5c` is an unsigned half-word load. -/
theorem raw_parser_lhu_image_bytes :
    Artifact.programImage.readByte? 0x11f5c = some 0x83 ∧
      Artifact.programImage.readByte? 0x11f5d = some 0xdb ∧
        Artifact.programImage.readByte? 0x11f5e = some 0x4c ∧
          Artifact.programImage.readByte? 0x11f5f = some 0x0e := by
  native_decide

theorem raw_parser_lhu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x83#8 0xdb#8 0x4c#8 0x0e#8)) state state
      (.LOAD (228#12, .Regidx 25#5, .Regidx 23#5, true, 2)) := by
  decode_run

theorem raw_parser_lhu_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x11f5c)
      (BitVec.ofNat 8 0x83) (BitVec.ofNat 8 0xdb) (BitVec.ofNat 8 0x4c) (BitVec.ofNat 8 0x0e) := by
  rcases raw_parser_lhu_image_bytes with ⟨read0, read1, read2, read3⟩
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x11f5c (by omega)
    (image_loaded_after_increment state loaded) 0x83 0xdb 0x4c 0x0e read0 read1 read2 read3

/-- The parser's concrete unsigned half-word result-status read retires from `0x11f5c`. -/
theorem raw_parser_lhu_retire (stepNo : Nat) (state afterExec : State)
    (retired : BitVec 64) (data : BitVec 16) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x11f5c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x11f5c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (hread : Runs (vmem_read (.Regidx 25#5) (sign_extend (m := 64) 228#12) 2
      (MemoryAccessType.Load mem_payload.Data) false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x11f5c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x11f5c))
      (.Ok data))
    (hwrite : Runs (wX_bits (.Regidx 23#5) (extend_value true data))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x11f5c)) afterExec ())
    (nextPcAfterExec : afterExec.regs.get? nextPC = some (BitVec.ofNat 64 0x11f60))
    (hartAgree : afterExec.regs.get? hart_state =
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state)
    (incrementAgree : afterExec.regs.get? minstret_increment =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment)
    (retiredAgree : afterExec.regs.get? minstret =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired afterExec (BitVec.ofNat 64 0x11f60) retired) false := by
  have bytes := raw_parser_lhu_fetch state loaded
  have decode := raw_parser_lhu_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  exact tryStepFallThroughRetires stepNo state afterExec (BitVec.ofNat 64 0x11f5c) retired inhibit
    config 0x83#8 0xdb#8 0x4c#8 0x0e#8 (.LOAD (228#12, .Regidx 25#5, .Regidx 23#5, true, 2))
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (execute_LOAD_lhu_run _ _ 228#12 (.Regidx 25#5) (.Regidx 23#5) data hread hwrite)
    nextPcAfterExec hartAgree incrementAgree retiredAgree hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- The parser's slice-descriptor read at `0x1060c` is a native double-word load. -/
theorem raw_parser_ld_image_bytes :
    Artifact.programImage.readByte? 0x1060c = some 0x83 ∧
      Artifact.programImage.readByte? 0x1060d = some 0x36 ∧
        Artifact.programImage.readByte? 0x1060e = some 0x04 ∧
          Artifact.programImage.readByte? 0x1060f = some 0x00 := by
  native_decide

theorem raw_parser_ld_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x83#8 0x36#8 0x04#8 0x00#8)) state state
      (.LOAD (0#12, .Regidx 8#5, .Regidx 13#5, false, 8)) := by
  decode_run

theorem raw_parser_ld_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1060c)
      (BitVec.ofNat 8 0x83) (BitVec.ofNat 8 0x36) (BitVec.ofNat 8 0x04) (BitVec.ofNat 8 0x00) := by
  rcases raw_parser_ld_image_bytes with ⟨read0, read1, read2, read3⟩
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x1060c (by omega)
    (image_loaded_after_increment state loaded) 0x83 0x36 0x04 0x00 read0 read1 read2 read3

/-- The parser's concrete slice-descriptor double-word read retires from `0x1060c`. -/
theorem raw_parser_ld_retire (stepNo : Nat) (state afterExec : State)
    (retired data : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1060c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1060c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (hread : Runs (vmem_read (.Regidx 8#5) (sign_extend (m := 64) 0#12) 8
      (MemoryAccessType.Load mem_payload.Data) false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1060c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1060c))
      (.Ok data))
    (hwrite : Runs (wX_bits (.Regidx 13#5) (extend_value false data))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1060c)) afterExec ())
    (nextPcAfterExec : afterExec.regs.get? nextPC = some (BitVec.ofNat 64 0x10610))
    (hartAgree : afterExec.regs.get? hart_state =
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state)
    (incrementAgree : afterExec.regs.get? minstret_increment =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment)
    (retiredAgree : afterExec.regs.get? minstret =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired afterExec (BitVec.ofNat 64 0x10610) retired) false := by
  have bytes := raw_parser_ld_fetch state loaded
  have decode := raw_parser_ld_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  exact tryStepFallThroughRetires stepNo state afterExec (BitVec.ofNat 64 0x1060c) retired inhibit
    config 0x83#8 0x36#8 0x04#8 0x00#8 (.LOAD (0#12, .Regidx 8#5, .Regidx 13#5, false, 8))
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (execute_LOAD_run _ _ 0#12 (.Regidx 8#5) (.Regidx 13#5) false 8 data (by decide) hread hwrite)
    nextPcAfterExec hartAgree incrementAgree retiredAgree hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- A contiguous parser byte-read sequence feeding a native little-endian 32-bit assembly. -/
theorem raw_parser_u32_byte_assembly_image_words :
    Artifact.programImage.readU32LE? 0x10764 = some 0x1b4c4283 ∧
      Artifact.programImage.readU32LE? 0x10768 = some 0x1b5c4583 ∧
        Artifact.programImage.readU32LE? 0x1076c = some 0x1b6c4603 ∧
          Artifact.programImage.readU32LE? 0x10770 = some 0x1b7c4683 := by
  native_decide

/-- The four instructions between the first word's byte reads and its shifts are real parser
byte reads for the adjacent field; they are not a control-flow gap. -/
theorem raw_parser_u32_intervening_byte_load_image_words :
    Artifact.programImage.readU32LE? 0x10774 = some 0x1f8c4703 ∧
      Artifact.programImage.readU32LE? 0x10778 = some 0x1f9c4783 ∧
        Artifact.programImage.readU32LE? 0x1077c = some 0x1fac4803 ∧
          Artifact.programImage.readU32LE? 0x10780 = some 0x1fbc4883 := by
  native_decide

theorem raw_parser_u32_intervening_byte_load_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x1f8c4703 : BitVec 32)) state state
        (.LOAD (504#12, .Regidx 24#5, .Regidx 14#5, true, 1)) ∧
      Runs (ext_decode (0x1f9c4783 : BitVec 32)) state state
        (.LOAD (505#12, .Regidx 24#5, .Regidx 15#5, true, 1)) ∧
      Runs (ext_decode (0x1fac4803 : BitVec 32)) state state
        (.LOAD (506#12, .Regidx 24#5, .Regidx 16#5, true, 1)) ∧
      Runs (ext_decode (0x1fbc4883 : BitVec 32)) state state
        (.LOAD (507#12, .Regidx 24#5, .Regidx 17#5, true, 1)) := by
  constructor
  · decode_run
  constructor
  · decode_run
  constructor <;> decode_run

/-- The first adjacent-field byte read retires at its actual ELF PC.  This is the first live
middle-fragment step needed by `raw_parser_u32_live_prefix_trace`. -/
theorem raw_parser_u32_adjacent_first_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10774))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10774))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10774)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10774)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10774)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10774)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 504#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10774))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10774))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10774)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10774)).regs.insert x14 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x10778) retired) false := by
  have image : Artifact.programImage.readByte? 0x10774 = some 0x03 ∧
      Artifact.programImage.readByte? 0x10775 = some 0x47 ∧
        Artifact.programImage.readByte? 0x10776 = some 0x8c ∧
          Artifact.programImage.readByte? 0x10777 = some 0x1f := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10774 (by omega) afterIncrement
    0x03 0x47 0x8c 0x1f read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0x47#8 0x8c#8 0x1f))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (504#12, .Regidx 24#5, .Regidx 14#5, true, 1)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10774)
    retired inhibit config 0x03#8 0x47#8 0x8c#8 0x1f
    (.LOAD (504#12, .Regidx 24#5, .Regidx 14#5, true, 1)) x14 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_adjacent_first_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10774))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The second adjacent-field byte read retires at its actual ELF PC. -/
theorem raw_parser_u32_adjacent_second_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifact.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10778))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10778))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10778)).regs.get? x24 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10778)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10778)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10778)).regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + sign_extend (m := 64) 505#12)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10778))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10778))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10778)
          with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10778)).regs.insert x15 (zero_extend (m := 64) data) }
        (BitVec.ofNat 64 0x1077c) retired) false := by
  have image : Artifact.programImage.readByte? 0x10778 = some 0x83 ∧
      Artifact.programImage.readByte? 0x10779 = some 0x47 ∧
        Artifact.programImage.readByte? 0x1077a = some 0x9c ∧
          Artifact.programImage.readByte? 0x1077b = some 0x1f := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifact.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x10778 (by omega) afterIncrement
    0x83 0x47 0x9c 0x1f read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0x47#8 0x9c#8 0x1f))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (505#12, .Regidx 24#5, .Regidx 15#5, true, 1)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x10778)
    retired inhibit config 0x83#8 0x47#8 0x9c#8 0x1f
    (.LOAD (505#12, .Regidx 24#5, .Regidx 15#5, true, 1)) x15 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by native_decide) decode notExpected
    (raw_parser_u32_adjacent_second_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10778))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_parser_u32_byte_assembly_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x1b4c4283 : BitVec 32)) state state
        (.LOAD (436#12, .Regidx 24#5, .Regidx 5#5, true, 1)) ∧
      Runs (ext_decode (0x1b5c4583 : BitVec 32)) state state
        (.LOAD (437#12, .Regidx 24#5, .Regidx 11#5, true, 1)) ∧
      Runs (ext_decode (0x1b6c4603 : BitVec 32)) state state
        (.LOAD (438#12, .Regidx 24#5, .Regidx 12#5, true, 1)) ∧
      Runs (ext_decode (0x1b7c4683 : BitVec 32)) state state
        (.LOAD (439#12, .Regidx 24#5, .Regidx 13#5, true, 1)) := by
  constructor
  · decode_run
  constructor
  · decode_run
  constructor <;> decode_run

/-- The same ELF block shifts and combines those bytes into its little-endian word in `s2`. -/
theorem raw_parser_u32_assembly_image_words :
    Artifact.programImage.readU32LE? 0x10784 = some 0x00859593 ∧
      Artifact.programImage.readU32LE? 0x10788 = some 0x01061613 ∧
        Artifact.programImage.readU32LE? 0x1078c = some 0x01869693 ∧
          Artifact.programImage.readU32LE? 0x10790 = some 0x0055ee33 ∧
            Artifact.programImage.readU32LE? 0x10794 = some 0x00c6e633 ∧
              Artifact.programImage.readU32LE? 0x107f4 = some 0x01c66933 := by
  native_decide

theorem raw_parser_u32_assembly_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x00859593 : BitVec 32)) state state
        (.SHIFTIOP (8#6, .Regidx 11#5, .Regidx 11#5, .SLLI)) ∧
      Runs (ext_decode (0x01061613 : BitVec 32)) state state
        (.SHIFTIOP (16#6, .Regidx 12#5, .Regidx 12#5, .SLLI)) ∧
      Runs (ext_decode (0x01869693 : BitVec 32)) state state
        (.SHIFTIOP (24#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) ∧
      Runs (ext_decode (0x0055ee33 : BitVec 32)) state state
        (.RTYPE (.Regidx 5#5, .Regidx 11#5, .Regidx 28#5, .OR)) ∧
      Runs (ext_decode (0x00c6e633 : BitVec 32)) state state
        (.RTYPE (.Regidx 12#5, .Regidx 13#5, .Regidx 12#5, .OR)) ∧
      Runs (ext_decode (0x01c66933 : BitVec 32)) state state
        (.RTYPE (.Regidx 28#5, .Regidx 12#5, .Regidx 18#5, .OR)) := by
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor <;> decode_run

/-- The pinned SizzLean `UInt32` reader is the same little-endian byte expression used by the
parser's four-byte assembly block. -/
theorem read_uint32_le_four_bytes (b0 b1 b2 b3 : UInt8) :
    SizzLean.Spec.readUInt32LE (ByteArray.mk #[b0, b1, b2, b3]) 0 =
      some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)) := by
  unfold SizzLean.Spec.readUInt32LE
  simp

/-- The 64-bit register value assembled by the parser's byte loads, shifts, and ORs. -/
def parserU32Assembly (b0 b1 b2 b3 : BitVec 8) : BitVec 64 :=
  zero_extend b0 ||| (zero_extend b1 <<< 8) ||| (zero_extend b2 <<< 16) |||
    (zero_extend b3 <<< 24)

theorem parser_u32_assembly_value (b0 b1 b2 b3 : BitVec 8) :
    parserU32Assembly b0 b1 b2 b3 = BitVec.ofNat 64
      (b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat) := by
  bv_decide

/-- The parser's zero-extended register result is the pinned SizzLean `UInt32` value. -/
theorem parser_u32_assembly_matches_sizzlean (b0 b1 b2 b3 : UInt8) :
    parserU32Assembly (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
      (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat) =
      BitVec.ofNat 64 (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)).toNat := by
  bv_decide

end BinaryFv.SSZ.Zesu.Proof
