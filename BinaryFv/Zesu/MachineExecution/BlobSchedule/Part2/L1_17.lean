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

theorem raw_blob_schedule_third_assembly_a3_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d68))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d68))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d68)).regs.get? x6 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d68)).regs.get? x13 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d68)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d68)).regs.insert x13 (high ||| low)) }
        (BitVec.ofNat 64 0x12d6c) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d68 = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12d69 = some 0x66 ∧
        Artifacts.programImage.readByte? 0x12d6a = some 0xd3 ∧
          Artifacts.programImage.readByte? 0x12d6b = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d68 (by omega)
    afterIncrement 0xb3 0x66 0xd3 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x66#8 0xd3#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 13#5, .Regidx 6#5, .Regidx 13#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d68))
    _ (.Regidx 13#5) (.Regidx 6#5) (.Regidx 13#5) high low
    (rX_x6_run _ high highStored) (rX_x13_run _ low lowStored)
    (wX_x13_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d68)
    retired inhibit config 0xb3#8 0x66#8 0xd3#8 0x00
    (.RTYPE (.Regidx 13#5, .Regidx 6#5, .Regidx 13#5, .OR)) x13 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_third_assembly_t1_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d6c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d6c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d6c)).regs.get? x28 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d6c)).regs.get? x7 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d6c)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d6c)).regs.insert x6 (high ||| low)) }
        (BitVec.ofNat 64 0x12d70) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d6c = some 0x33 ∧
      Artifacts.programImage.readByte? 0x12d6d = some 0x63 ∧
        Artifacts.programImage.readByte? 0x12d6e = some 0x7e ∧
          Artifacts.programImage.readByte? 0x12d6f = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d6c (by omega)
    afterIncrement 0x33 0x63 0x7e 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x63#8 0x7e#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 7#5, .Regidx 28#5, .Regidx 6#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d6c))
    _ (.Regidx 7#5) (.Regidx 28#5) (.Regidx 6#5) high low
    (rX_x28_run _ high highStored) (rX_x7_run _ low lowStored)
    (wX_x6_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d6c)
    retired inhibit config 0x33#8 0x63#8 0x7e#8 0x00
    (.RTYPE (.Regidx 7#5, .Regidx 28#5, .Regidx 6#5, .OR)) x6 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
