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

theorem raw_blob_schedule_second_assembly_a6_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d30))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d30))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d30)).regs.get? x17 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d30)).regs.get? x16 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d30)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d30)).regs.insert x16 (high ||| low)) }
        (BitVec.ofNat 64 0x12d34) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d30 = some 0x33 ∧
      Artifacts.programImage.readByte? 0x12d31 = some 0xe8 ∧
        Artifacts.programImage.readByte? 0x12d32 = some 0x08 ∧
          Artifacts.programImage.readByte? 0x12d33 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d30 (by omega)
    afterIncrement 0x33 0xe8 0x08 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0xe8#8 0x08#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 16#5, .Regidx 17#5, .Regidx 16#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d30))
    _ (.Regidx 16#5) (.Regidx 17#5) (.Regidx 16#5) high low
    (rX_x17_run _ high highStored) (rX_x16_run _ low lowStored)
    (wX_x16_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d30)
    retired inhibit config 0x33#8 0xe8#8 0x08#8 0x01
    (.RTYPE (.Regidx 16#5, .Regidx 17#5, .Regidx 16#5, .OR)) x16 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_second_assembly_a7_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d34))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d34))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d34)).regs.get? x6 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d34)).regs.get? x5 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d34)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d34)).regs.insert x17 (high ||| low)) }
        (BitVec.ofNat 64 0x12d38) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d34 = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12d35 = some 0x68 ∧
        Artifacts.programImage.readByte? 0x12d36 = some 0x53 ∧
          Artifacts.programImage.readByte? 0x12d37 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d34 (by omega)
    afterIncrement 0xb3 0x68 0x53 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x68#8 0x53#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 5#5, .Regidx 6#5, .Regidx 17#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d34))
    _ (.Regidx 5#5) (.Regidx 6#5) (.Regidx 17#5) high low
    (rX_x6_run _ high highStored) (rX_x5_run _ low lowStored)
    (wX_x17_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d34)
    retired inhibit config 0xb3#8 0x68#8 0x53#8 0x00
    (.RTYPE (.Regidx 5#5, .Regidx 6#5, .Regidx 17#5, .OR)) x17 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
