import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Zesu.ControlFlow.Decode
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterRuns

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

theorem raw_blob_schedule_second_assembly_t0_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d38))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d38))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d38)).regs.get? x28 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d38)).regs.get? x7 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d38)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d38)).regs.insert x5 (high ||| low)) }
        (BitVec.ofNat 64 0x12d3c) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d38 = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12d39 = some 0x62 ∧
        Artifacts.programImage.readByte? 0x12d3a = some 0x7e ∧
          Artifacts.programImage.readByte? 0x12d3b = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d38 (by omega)
    afterIncrement 0xb3 0x62 0x7e 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x62#8 0x7e#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 7#5, .Regidx 28#5, .Regidx 5#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d38))
    _ (.Regidx 7#5) (.Regidx 28#5) (.Regidx 5#5) high low
    (rX_x28_run _ high highStored) (rX_x7_run _ low lowStored)
    (wX_x5_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d38)
    retired inhibit config 0xb3#8 0x62#8 0x7e#8 0x00
    (.RTYPE (.Regidx 7#5, .Regidx 28#5, .Regidx 5#5, .OR)) x5 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_second_assembly_a1_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d3c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d3c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d3c)).regs.get? x13 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d3c)).regs.get? x11 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d3c)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d3c)).regs.insert x11 (high ||| low)) }
        (BitVec.ofNat 64 0x12d40) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d3c = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12d3d = some 0xe5 ∧
        Artifacts.programImage.readByte? 0x12d3e = some 0xb6 ∧
          Artifacts.programImage.readByte? 0x12d3f = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d3c (by omega)
    afterIncrement 0xb3 0xe5 0xb6 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe5#8 0xb6#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 11#5, .Regidx 13#5, .Regidx 11#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d3c))
    _ (.Regidx 11#5) (.Regidx 13#5) (.Regidx 11#5) high low
    (rX_x13_run _ high highStored) (rX_x11_run _ low lowStored)
    (wX_x11_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d3c)
    retired inhibit config 0xb3#8 0xe5#8 0xb6#8 0x00
    (.RTYPE (.Regidx 11#5, .Regidx 13#5, .Regidx 11#5, .OR)) x11 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
