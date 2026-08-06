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

theorem raw_blob_schedule_third_assembly_t3_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d60))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d60))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d60)).regs.get? x28 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d60)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d60)).regs.insert x28 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d64) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d60 = some 0x13 ∧
      Artifacts.programImage.readByte? 0x12d61 = some 0x1e ∧
        Artifacts.programImage.readByte? 0x12d62 = some 0x8e ∧
          Artifacts.programImage.readByte? 0x12d63 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d60 (by omega)
    afterIncrement 0x13 0x1e 0x8e 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x1e#8 0x8e#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (24#6, .Regidx 28#5, .Regidx 28#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d60))
    _ 24#6 (.Regidx 28#5) (.Regidx 28#5) value (rX_x28_run _ value stored)
    (wX_x28_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d60)
    retired inhibit config 0x13#8 0x1e#8 0x8e#8 0x01
    (.SHIFTIOP (24#6, .Regidx 28#5, .Regidx 28#5, .SLLI)) x28 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_third_assembly_a5_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d64))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d64))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d64)).regs.get? x29 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d64)).regs.get? x15 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d64)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d64)).regs.insert x15 (high ||| low)) }
        (BitVec.ofNat 64 0x12d68) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d64 = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12d65 = some 0xe7 ∧
        Artifacts.programImage.readByte? 0x12d66 = some 0xfe ∧
          Artifacts.programImage.readByte? 0x12d67 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d64 (by omega)
    afterIncrement 0xb3 0xe7 0xfe 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe7#8 0xfe#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 29#5, .Regidx 15#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d64))
    _ (.Regidx 15#5) (.Regidx 29#5) (.Regidx 15#5) high low
    (rX_x29_run _ high highStored) (rX_x15_run _ low lowStored)
    (wX_x15_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d64)
    retired inhibit config 0xb3#8 0xe7#8 0xfe#8 0x00
    (.RTYPE (.Regidx 15#5, .Regidx 29#5, .Regidx 15#5, .OR)) x15 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
