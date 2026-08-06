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

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

theorem raw_blob_schedule_first_word_low_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc)).regs.get? x11 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc)).regs.get? x10 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ())) (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config) (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1) (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc)
        with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc)).regs.insert x10 (high ||| low)) }
        (BitVec.ofNat 64 0x12d00) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cfc = some 0x33 ∧ Artifacts.programImage.readByte? 0x12cfd = some 0xe5 ∧ Artifacts.programImage.readByte? 0x12cfe = some 0xa5 ∧ Artifacts.programImage.readByte? 0x12cff = some 0x00 := by native_decide
  rcases image with ⟨r0,r1,r2,r3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory (tryStepControlFlowAfterIncrement state).mem := by simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage (tryStepControlFlowAfterIncrement state) 0x12cfc (by omega) afterIncrement 0x33 0xe5 0xa5 0x00 r0 r1 r2 r3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0xe5#8 0xa5#8 0x00#8)) (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) (.RTYPE (.Regidx 10#5, .Regidx 11#5, .Regidx 10#5, .OR)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cfc) retired inhibit config 0x33#8 0xe5#8 0xa5#8 0x00 (.RTYPE (.Regidx 10#5, .Regidx 11#5, .Regidx 10#5, .OR)) x10 (high ||| low) platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected (raw_blob_schedule_first_word_low_or_execute (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc)) high low highStored lowStored) (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

theorem raw_blob_schedule_first_word_high_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d00))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d00))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg =
      some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d00)).regs.get? x13 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d00)).regs.get? x12 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d00)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d00)).regs.insert x12 (high ||| low)) }
        (BitVec.ofNat 64 0x12d04) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d00 = some 0x33 ∧
      Artifacts.programImage.readByte? 0x12d01 = some 0xe6 ∧
        Artifacts.programImage.readByte? 0x12d02 = some 0xc6 ∧
          Artifacts.programImage.readByte? 0x12d03 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d00 (by omega) afterIncrement
    0x33 0xe6 0xc6 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0xe6#8 0xc6#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 12#5, .Regidx 13#5, .Regidx 12#5, .OR)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d00)
    retired inhibit config 0x33#8 0xe6#8 0xc6#8 0x00
    (.RTYPE (.Regidx 12#5, .Regidx 13#5, .Regidx 12#5, .OR)) x12 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected
    (raw_blob_schedule_first_word_high_or_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x12d00)) high low highStored lowStored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_second_word_low_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d04))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d04))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg =
      some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d04)).regs.get? x15 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d04)).regs.get? x14 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d04)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d04)).regs.insert x14 (high ||| low)) }
        (BitVec.ofNat 64 0x12d08) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d04 = some 0x33 ∧
      Artifacts.programImage.readByte? 0x12d05 = some 0xe7 ∧
        Artifacts.programImage.readByte? 0x12d06 = some 0xe7 ∧
          Artifacts.programImage.readByte? 0x12d07 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d04 (by omega) afterIncrement
    0x33 0xe7 0xe7 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0xe7#8 0xe7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 14#5, .Regidx 15#5, .Regidx 14#5, .OR)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d04)
    retired inhibit config 0x33#8 0xe7#8 0xe7#8 0x00
    (.RTYPE (.Regidx 14#5, .Regidx 15#5, .Regidx 14#5, .OR)) x14 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected
    (raw_blob_schedule_second_word_low_or_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x12d04)) high low highStored lowStored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_lbu_address (state : State)
    (imm base mstatusBits mseccfgBits : BitVec 64)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled) :
    Runs (get_transformed_data_addr (.Regidx 23#5) imm
      (MemoryAccessType.Load mem_payload.Data) 1) state state
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + imm))) := by
  exact get_transformed_data_addr_machine_load_run state (.Regidx 23#5) base imm mstatusBits
    mseccfgBits (rX_x23_run state base baseRead) mstatusRead privilegeRead mprvZero mseccfgRead
    pmmDisabled

end BinaryFv.Zesu.MachineExecution
