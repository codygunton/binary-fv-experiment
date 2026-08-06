import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Zesu.ControlFlow.Decode
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_1
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_2
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_3
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_1
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_2

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

/-- Shared `lbu`-from-`s7` execution contract for the present blob-schedule branch.  The
destination is left general: each site supplies its own generated `wX_bits` reduction, so this
factors the address transformation and physical byte read out of the individual byte proofs. -/
theorem raw_blob_schedule_lbu_execute_general (state post : State) (immBits : BitVec 12)
    (imm base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8) (rd : regidx)
    (immAgree : sign_extend (m := 64) immBits = imm)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + imm)) 1 false false false) state state (.Ok data))
    (write : Runs (wX_bits rd (zero_extend (m := 64) data)) state post ()) :
    Runs (execute_LOAD immBits (.Regidx 23#5) rd true 1) state post (.Retire_Success ()) := by
  apply execute_LOAD_run _ _ immBits (.Regidx 23#5) rd true 1 data (by decide)
  · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) immBits)
        (MemoryAccessType.Load mem_payload.Data) 1) state state
        (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + imm))) := by
      simpa [immAgree] using raw_blob_schedule_lbu_address state imm base mstatusBits mseccfgBits
        baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled
    exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) immBits) (base + imm)
      mstatusBits data mstatusRead privilegeRead mprvZero address
      (BinaryFv.RiscV.is_aligned_vaddr_one _) (by simpa [immAgree] using hread)
  · exact write

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
      simpa using raw_blob_schedule_lbu_address state 0#64 base mstatusBits mseccfgBits baseRead
        mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled
    exact vmem_read_byte_run state (.Regidx 23#5) (sign_extend (m := 64) 0#12) base mstatusBits
      data mstatusRead privilegeRead mprvZero address (BinaryFv.RiscV.is_aligned_vaddr_one _)
      (by simpa using hread)
  · exact wX_x10_run state (zero_extend (m := 64) data)

/-- The second schedule-payload byte read executes from `s7 + 1` and writes zero-extended `a1`. -/
theorem raw_blob_schedule_second_lbu_execute (state : State)
    (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 1#64)) 1 false false false) state state (.Ok data)) :
    Runs (execute_LOAD 1#12 (.Regidx 23#5) (.Regidx 11#5) true 1) state
      { state with regs := state.regs.insert x11 (zero_extend (m := 64) data) }
      (.Retire_Success ()) := by
  apply execute_LOAD_run state _ 1#12 (.Regidx 23#5) (.Regidx 11#5) true 1 data (by decide)
  · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 1#12)
        (MemoryAccessType.Load mem_payload.Data) 1) state state
        (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 1#64))) := by
      simpa using raw_blob_schedule_lbu_address state 1#64 base mstatusBits mseccfgBits baseRead
        mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled
    exact vmem_read_byte_run state (.Regidx 23#5) (sign_extend (m := 64) 1#12) (base + 1#64)
      mstatusBits data mstatusRead privilegeRead mprvZero address
      (BinaryFv.RiscV.is_aligned_vaddr_one _) (by simpa using hread)
  · exact wX_x11_run state (zero_extend (m := 64) data)

/-- The third present-schedule byte load is fetched from immutable ELF bytes and retires at PC
`0x12cc4`, preserving all unmodeled runtime behavior as explicit premises. -/
theorem raw_blob_schedule_third_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc4))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc4)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc4)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc4)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc4)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 2#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cc4)).regs.insert x12 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cc8) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cc4 = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12cc5 = some 0xc6 ∧
        Artifacts.programImage.readByte? 0x12cc6 = some 0x2b ∧
          Artifacts.programImage.readByte? 0x12cc7 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cc4 (by omega)
    afterIncrement 0x03 0xc6 0x2b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc6#8 0x2b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (2#12, .Regidx 23#5, .Regidx 12#5, true, 1)) := by decode_run
  have execute : Runs (execute_LOAD 2#12 (.Regidx 23#5) (.Regidx 12#5) true 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4)
        with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x12cc4)).regs.insert x12 (zero_extend (m := 64) data)) }
      (.Retire_Success ()) := by
    apply execute_LOAD_run _ _ 2#12 (.Regidx 23#5) (.Regidx 12#5) true 1 data (by decide)
    · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 2#12)
          (MemoryAccessType.Load mem_payload.Data) 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
          (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 2#64))) := by
        simpa using raw_blob_schedule_lbu_address
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
          2#64 base mstatusBits mseccfgBits baseRead mstatusRead privilegeRead mprvZero mseccfgRead
          pmmDisabled
      exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) 2#12) (base + 2#64)
        mstatusBits data mstatusRead privilegeRead mprvZero address
        (BinaryFv.RiscV.is_aligned_vaddr_one _) hread
    · exact wX_x12_run _ (zero_extend (m := 64) data)
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cc4)
    retired inhibit config 0x03#8 0xc6#8 0x2b#8 0x00
    (.LOAD (2#12, .Regidx 23#5, .Regidx 12#5, true, 1)) x12 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The fourth present-schedule byte load is checked and retired at its immutable ELF PC. -/
theorem raw_blob_schedule_fourth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc8))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc8)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc8)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc8)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc8)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 3#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cc8)).regs.insert x13 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12ccc) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cc8 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12cc9 = some 0xc6 ∧
        Artifacts.programImage.readByte? 0x12cca = some 0x3b ∧
          Artifacts.programImage.readByte? 0x12ccb = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cc8 (by omega)
    afterIncrement 0x83 0xc6 0x3b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc6#8 0x3b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (3#12, .Regidx 23#5, .Regidx 13#5, true, 1)) := by decode_run
  have execute : Runs (execute_LOAD 3#12 (.Regidx 23#5) (.Regidx 13#5) true 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8)
        with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x12cc8)).regs.insert x13 (zero_extend (m := 64) data)) }
      (.Retire_Success ()) := by
    apply execute_LOAD_run _ _ 3#12 (.Regidx 23#5) (.Regidx 13#5) true 1 data (by decide)
    · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 3#12)
          (MemoryAccessType.Load mem_payload.Data) 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
          (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 3#64))) := by
        simpa using raw_blob_schedule_lbu_address
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
          3#64 base mstatusBits mseccfgBits baseRead mstatusRead privilegeRead mprvZero mseccfgRead
          pmmDisabled
      exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) 3#12) (base + 3#64)
        mstatusBits data mstatusRead privilegeRead mprvZero address
        (BinaryFv.RiscV.is_aligned_vaddr_one _) hread
    · exact wX_x13_run _ (zero_extend (m := 64) data)
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cc8)
    retired inhibit config 0x83#8 0xc6#8 0x3b#8 0x00
    (.LOAD (3#12, .Regidx 23#5, .Regidx 13#5, true, 1)) x13 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The fifth present-schedule byte load is checked and retired at its immutable ELF PC. -/
theorem raw_blob_schedule_fifth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ccc))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ccc)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ccc)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ccc)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ccc)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 4#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12ccc)).regs.insert x14 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cd0) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12ccc = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12ccd = some 0xc7 ∧
        Artifacts.programImage.readByte? 0x12cce = some 0x4b ∧
          Artifacts.programImage.readByte? 0x12ccf = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12ccc (by omega)
    afterIncrement 0x03 0xc7 0x4b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc7#8 0x4b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (4#12, .Regidx 23#5, .Regidx 14#5, true, 1)) := by decode_run
  have execute : Runs (execute_LOAD 4#12 (.Regidx 23#5) (.Regidx 14#5) true 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc)
        with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x12ccc)).regs.insert x14 (zero_extend (m := 64) data)) }
      (.Retire_Success ()) := by
    apply execute_LOAD_run _ _ 4#12 (.Regidx 23#5) (.Regidx 14#5) true 1 data (by decide)
    · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 4#12)
          (MemoryAccessType.Load mem_payload.Data) 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
          (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 4#64))) := by
        simpa using raw_blob_schedule_lbu_address
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
          4#64 base mstatusBits mseccfgBits baseRead mstatusRead privilegeRead mprvZero mseccfgRead
          pmmDisabled
      exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) 4#12) (base + 4#64)
        mstatusBits data mstatusRead privilegeRead mprvZero address
        (BinaryFv.RiscV.is_aligned_vaddr_one _) hread
    · exact wX_x14_run _ (zero_extend (m := 64) data)
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12ccc)
    retired inhibit config 0x03#8 0xc7#8 0x4b#8 0x00
    (.LOAD (4#12, .Regidx 23#5, .Regidx 14#5, true, 1)) x14 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_sixth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd0))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd0)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd0)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd0)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd0)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 5#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cd0)).regs.insert x15 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cd4) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cd0 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12cd1 = some 0xc7 ∧
        Artifacts.programImage.readByte? 0x12cd2 = some 0x5b ∧
          Artifacts.programImage.readByte? 0x12cd3 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cd0 (by omega)
    afterIncrement 0x83 0xc7 0x5b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc7#8 0x5b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (5#12, .Regidx 23#5, .Regidx 15#5, true, 1)) := by decode_run
  have execute : Runs (execute_LOAD 5#12 (.Regidx 23#5) (.Regidx 15#5) true 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0)
        with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x12cd0)).regs.insert x15 (zero_extend (m := 64) data)) }
      (.Retire_Success ()) := by
    apply execute_LOAD_run _ _ 5#12 (.Regidx 23#5) (.Regidx 15#5) true 1 data (by decide)
    · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 5#12)
          (MemoryAccessType.Load mem_payload.Data) 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
          (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 5#64))) := by
        simpa using raw_blob_schedule_lbu_address
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
          5#64 base mstatusBits mseccfgBits baseRead mstatusRead privilegeRead mprvZero mseccfgRead
          pmmDisabled
      exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) 5#12) (base + 5#64)
        mstatusBits data mstatusRead privilegeRead mprvZero address
        (BinaryFv.RiscV.is_aligned_vaddr_one _) hread
    · exact wX_x15_run _ (zero_extend (m := 64) data)
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cd0)
    retired inhibit config 0x83#8 0xc7#8 0x5b#8 0x00
    (.LOAD (5#12, .Regidx 23#5, .Regidx 15#5, true, 1)) x15 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
