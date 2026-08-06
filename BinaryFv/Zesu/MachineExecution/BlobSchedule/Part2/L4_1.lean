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

/-- The first present-schedule byte load retires at its actual canonical ELF PC. -/
theorem raw_blob_schedule_first_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cbc))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cbc))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cbc)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cbc)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cbc)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cbc)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr base) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cbc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cbc))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cbc)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cbc)).regs.insert x10 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cc0) retired) false := by
  have bytes := raw_blob_schedule_first_lbu_fetch state loaded
  have decode := raw_blob_schedule_first_lbu_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cbc)
    retired inhibit config 0x03#8 0xc5#8 0x0b#8 0x00#8
    (.LOAD (0#12, .Regidx 23#5, .Regidx 10#5, true, 1)) x10 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected
    (raw_blob_schedule_first_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cbc))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The second present-schedule byte load retires at its actual canonical ELF PC. -/
theorem raw_blob_schedule_second_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc0))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc0))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc0)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc0)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc0)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc0)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 1#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc0))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc0))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc0)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cc0)).regs.insert x11 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cc4) retired) false := by
  have bytes := raw_blob_schedule_second_lbu_fetch state loaded
  have decode := raw_blob_schedule_second_lbu_decode (tryStepControlFlowAfterIncrement state)
    privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cc0)
    retired inhibit config 0x83#8 0xc5#8 0x1b#8 0x00#8
    (.LOAD (1#12, .Regidx 23#5, .Regidx 11#5, true, 1)) x11 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected
    (raw_blob_schedule_second_lbu_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc0))
      base mstatusBits mseccfgBits data baseRead mstatusRead privilegeRead mprvZero mseccfgRead
      pmmDisabled hread)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
