import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.SSZ.Zesu.Analysis.Primitives

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

end BinaryFv.SSZ.Zesu.Proof
