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
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_4
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_5
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_6
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_7
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_8
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_9
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_10
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_11
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_12
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_13
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_14
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_15
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_16
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_17
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_1
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_2
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_3
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_4
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_5
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L3_1
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L3_2
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L3_3
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L3_4

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

theorem raw_blob_schedule_seventeenth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d40))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d40))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d40)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d40)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d40)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d40)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 16#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d40))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d40))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d40)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d40)).regs.insert x13 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d44) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d40 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12d41 = some 0xc6 ∧
        Artifacts.programImage.readByte? 0x12d42 = some 0x0b ∧
          Artifacts.programImage.readByte? 0x12d43 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d40 (by omega)
    afterIncrement 0x83 0xc6 0x0b 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc6#8 0x0b#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (16#12, .Regidx 23#5, .Regidx 13#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d40))
    _ 16#12 16#64 base mstatusBits mseccfgBits data (.Regidx 13#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x13_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d40)
    retired inhibit config 0x83#8 0xc6#8 0x0b#8 0x01
    (.LOAD (16#12, .Regidx 23#5, .Regidx 13#5, true, 1)) x13 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_eighteenth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d44))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d44))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d44)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d44)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d44)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d44)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 17#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d44))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d44)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d44)).regs.insert x6 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d48) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d44 = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12d45 = some 0xc3 ∧
        Artifacts.programImage.readByte? 0x12d46 = some 0x1b ∧
          Artifacts.programImage.readByte? 0x12d47 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d44 (by omega)
    afterIncrement 0x03 0xc3 0x1b 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc3#8 0x1b#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (17#12, .Regidx 23#5, .Regidx 6#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d44))
    _ 17#12 17#64 base mstatusBits mseccfgBits data (.Regidx 6#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x6_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d44)
    retired inhibit config 0x03#8 0xc3#8 0x1b#8 0x01
    (.LOAD (17#12, .Regidx 23#5, .Regidx 6#5, true, 1)) x6 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
