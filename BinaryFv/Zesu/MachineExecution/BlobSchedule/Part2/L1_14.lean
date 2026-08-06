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

theorem raw_blob_schedule_third_assembly_a5_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d50))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d50))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d50)).regs.get? x15 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d50)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d50)).regs.insert x15 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d54) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d50 = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12d51 = some 0x97 ∧
        Artifacts.programImage.readByte? 0x12d52 = some 0x07 ∧
          Artifacts.programImage.readByte? 0x12d53 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d50 (by omega)
    afterIncrement 0x93 0x97 0x07 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x97#8 0x07#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (16#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d50))
    _ 16#6 (.Regidx 15#5) (.Regidx 15#5) value (rX_x15_run _ value stored)
    (wX_x15_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d50)
    retired inhibit config 0x93#8 0x97#8 0x07#8 0x01
    (.SHIFTIOP (16#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) x15 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_third_assembly_t4_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d54))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d54))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d54)).regs.get? x29 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d54)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d54)).regs.insert x29 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d58) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d54 = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12d55 = some 0x9e ∧
        Artifacts.programImage.readByte? 0x12d56 = some 0x8e ∧
          Artifacts.programImage.readByte? 0x12d57 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d54 (by omega)
    afterIncrement 0x93 0x9e 0x8e 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x9e#8 0x8e#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (24#6, .Regidx 29#5, .Regidx 29#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d54))
    _ 24#6 (.Regidx 29#5) (.Regidx 29#5) value (rX_x29_run _ value stored)
    (wX_x29_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d54)
    retired inhibit config 0x93#8 0x9e#8 0x8e#8 0x01
    (.SHIFTIOP (24#6, .Regidx 29#5, .Regidx 29#5, .SLLI)) x29 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
