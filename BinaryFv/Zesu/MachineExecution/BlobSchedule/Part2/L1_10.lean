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

theorem raw_blob_schedule_second_assembly_t1_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d20))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d20))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d20)).regs.get? x6 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d20)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d20)).regs.insert x6 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d24) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d20 = some 0x13 ∧
      Artifacts.programImage.readByte? 0x12d21 = some 0x13 ∧
        Artifacts.programImage.readByte? 0x12d22 = some 0x83 ∧
          Artifacts.programImage.readByte? 0x12d23 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d20 (by omega)
    afterIncrement 0x13 0x13 0x83 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x13#8 0x83#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (8#6, .Regidx 6#5, .Regidx 6#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d20))
    _ 8#6 (.Regidx 6#5) (.Regidx 6#5) value (rX_x6_run _ value stored)
    (wX_x6_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d20)
    retired inhibit config 0x13#8 0x13#8 0x83#8 0x00
    (.SHIFTIOP (8#6, .Regidx 6#5, .Regidx 6#5, .SLLI)) x6 (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_second_assembly_t2_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d24))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d24))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d24)).regs.get? x7 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d24)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d24)).regs.insert x7 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d28) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d24 = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12d25 = some 0x93 ∧
        Artifacts.programImage.readByte? 0x12d26 = some 0x03 ∧
          Artifacts.programImage.readByte? 0x12d27 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d24 (by omega)
    afterIncrement 0x93 0x93 0x03 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x93#8 0x03#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (16#6, .Regidx 7#5, .Regidx 7#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d24))
    _ 16#6 (.Regidx 7#5) (.Regidx 7#5) value (rX_x7_run _ value stored)
    (wX_x7_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d24)
    retired inhibit config 0x93#8 0x93#8 0x03#8 0x01
    (.SHIFTIOP (16#6, .Regidx 7#5, .Regidx 7#5, .SLLI)) x7 (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
