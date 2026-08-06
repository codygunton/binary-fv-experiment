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

theorem raw_blob_schedule_fifteenth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d10))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d10))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d10)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d10)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d10)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d10)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 14#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d10))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d10))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d10)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d10)).regs.insert x15 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d14) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d10 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12d11 = some 0xc7 ∧
        Artifacts.programImage.readByte? 0x12d12 = some 0xeb ∧
          Artifacts.programImage.readByte? 0x12d13 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d10 (by omega)
    afterIncrement 0x83 0xc7 0xeb 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc7#8 0xeb#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (14#12, .Regidx 23#5, .Regidx 15#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d10))
    _ 14#12 14#64 base mstatusBits mseccfgBits data (.Regidx 15#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x15_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d10)
    retired inhibit config 0x83#8 0xc7#8 0xeb#8 0x00
    (.LOAD (14#12, .Regidx 23#5, .Regidx 15#5, true, 1)) x15 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_sixteenth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d14))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d14))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d14)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d14)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d14)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d14)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 15#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d14))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d14))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d14)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d14)).regs.insert x29 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d18) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d14 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12d15 = some 0xce ∧
        Artifacts.programImage.readByte? 0x12d16 = some 0xfb ∧
          Artifacts.programImage.readByte? 0x12d17 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d14 (by omega)
    afterIncrement 0x83 0xce 0xfb 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xce#8 0xfb#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (15#12, .Regidx 23#5, .Regidx 29#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d14))
    _ 15#12 15#64 base mstatusBits mseccfgBits data (.Regidx 29#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x29_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d14)
    retired inhibit config 0x83#8 0xce#8 0xfb#8 0x00
    (.LOAD (15#12, .Regidx 23#5, .Regidx 29#5, true, 1)) x29 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
