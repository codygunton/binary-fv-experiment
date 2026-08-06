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

theorem raw_blob_schedule_fourth_assembly_t2_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d80))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d80))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d80)).regs.get? x7 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d80)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d80)).regs.insert x7 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d84) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d80 = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12d81 = some 0x93 ∧
        Artifacts.programImage.readByte? 0x12d82 = some 0x83 ∧
          Artifacts.programImage.readByte? 0x12d83 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d80 (by omega)
    afterIncrement 0x93 0x93 0x83 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x93#8 0x83#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (8#6, .Regidx 7#5, .Regidx 7#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d80))
    _ 8#6 (.Regidx 7#5) (.Regidx 7#5) value (rX_x7_run _ value stored)
    (wX_x7_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d80)
    retired inhibit config 0x93#8 0x93#8 0x83#8 0x00
    (.SHIFTIOP (8#6, .Regidx 7#5, .Regidx 7#5, .SLLI)) x7 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_t2_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d84))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d84))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d84)).regs.get? x7 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d84)).regs.get? x28 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d84)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d84)).regs.insert x7 (high ||| low)) }
        (BitVec.ofNat 64 0x12d88) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d84 = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12d85 = some 0xe3 ∧
        Artifacts.programImage.readByte? 0x12d86 = some 0xc3 ∧
          Artifacts.programImage.readByte? 0x12d87 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d84 (by omega)
    afterIncrement 0xb3 0xe3 0xc3 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe3#8 0xc3#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 28#5, .Regidx 7#5, .Regidx 7#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d84))
    _ (.Regidx 28#5) (.Regidx 7#5) (.Regidx 7#5) high low
    (rX_x7_run _ high highStored) (rX_x28_run _ low lowStored)
    (wX_x7_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d84)
    retired inhibit config 0xb3#8 0xe3#8 0xc3#8 0x01
    (.RTYPE (.Regidx 28#5, .Regidx 7#5, .Regidx 7#5, .OR)) x7 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_t4_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d88))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d88))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d88)).regs.get? x29 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d88)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d88)).regs.insert x29 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d8c) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d88 = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12d89 = some 0x9e ∧
        Artifacts.programImage.readByte? 0x12d8a = some 0x0e ∧
          Artifacts.programImage.readByte? 0x12d8b = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d88 (by omega)
    afterIncrement 0x93 0x9e 0x0e 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x9e#8 0x0e#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (16#6, .Regidx 29#5, .Regidx 29#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d88))
    _ 16#6 (.Regidx 29#5) (.Regidx 29#5) value (rX_x29_run _ value stored)
    (wX_x29_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d88)
    retired inhibit config 0x93#8 0x9e#8 0x0e#8 0x01
    (.SHIFTIOP (16#6, .Regidx 29#5, .Regidx 29#5, .SLLI)) x29 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_t5_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d8c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d8c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d8c)).regs.get? x30 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d8c)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d8c)).regs.insert x30 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d90) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d8c = some 0x13 ∧
      Artifacts.programImage.readByte? 0x12d8d = some 0x1f ∧
        Artifacts.programImage.readByte? 0x12d8e = some 0x8f ∧
          Artifacts.programImage.readByte? 0x12d8f = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d8c (by omega)
    afterIncrement 0x13 0x1f 0x8f 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x1f#8 0x8f#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (24#6, .Regidx 30#5, .Regidx 30#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d8c))
    _ 24#6 (.Regidx 30#5) (.Regidx 30#5) value (rX_x30_run _ value stored)
    (wX_x30_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d8c)
    retired inhibit config 0x13#8 0x1f#8 0x8f#8 0x01
    (.SHIFTIOP (24#6, .Regidx 30#5, .Regidx 30#5, .SLLI)) x30 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_t3_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d90))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d90))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d90)).regs.get? x30 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d90)).regs.get? x29 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d90)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d90)).regs.insert x28 (high ||| low)) }
        (BitVec.ofNat 64 0x12d94) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d90 = some 0x33 ∧
      Artifacts.programImage.readByte? 0x12d91 = some 0x6e ∧
        Artifacts.programImage.readByte? 0x12d92 = some 0xdf ∧
          Artifacts.programImage.readByte? 0x12d93 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d90 (by omega)
    afterIncrement 0x33 0x6e 0xdf 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x6e#8 0xdf#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 29#5, .Regidx 30#5, .Regidx 28#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d90))
    _ (.Regidx 29#5) (.Regidx 30#5) (.Regidx 28#5) high low
    (rX_x30_run _ high highStored) (rX_x29_run _ low lowStored)
    (wX_x28_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d90)
    retired inhibit config 0x33#8 0x6e#8 0xdf#8 0x01
    (.RTYPE (.Regidx 29#5, .Regidx 30#5, .Regidx 28#5, .OR)) x28 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_a0_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d94))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d94))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d94)).regs.get? x12 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d94)).regs.get? x10 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d94)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d94)).regs.insert x10 (high ||| low)) }
        (BitVec.ofNat 64 0x12d98) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d94 = some 0x33 ∧
      Artifacts.programImage.readByte? 0x12d95 = some 0x65 ∧
        Artifacts.programImage.readByte? 0x12d96 = some 0xa6 ∧
          Artifacts.programImage.readByte? 0x12d97 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d94 (by omega)
    afterIncrement 0x33 0x65 0xa6 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x65#8 0xa6#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 10#5, .Regidx 12#5, .Regidx 10#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d94))
    _ (.Regidx 10#5) (.Regidx 12#5) (.Regidx 10#5) high low
    (rX_x12_run _ high highStored) (rX_x10_run _ low lowStored)
    (wX_x10_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d94)
    retired inhibit config 0x33#8 0x65#8 0xa6#8 0x00
    (.RTYPE (.Regidx 10#5, .Regidx 12#5, .Regidx 10#5, .OR)) x10 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_a2_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d98))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d98))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d98)).regs.get? x16 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d98)).regs.get? x14 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d98)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d98)).regs.insert x12 (high ||| low)) }
        (BitVec.ofNat 64 0x12d9c) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d98 = some 0x33 ∧
      Artifacts.programImage.readByte? 0x12d99 = some 0x66 ∧
        Artifacts.programImage.readByte? 0x12d9a = some 0xe8 ∧
          Artifacts.programImage.readByte? 0x12d9b = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d98 (by omega)
    afterIncrement 0x33 0x66 0xe8 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x66#8 0xe8#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 14#5, .Regidx 16#5, .Regidx 12#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d98))
    _ (.Regidx 14#5) (.Regidx 16#5) (.Regidx 12#5) high low
    (rX_x16_run _ high highStored) (rX_x14_run _ low lowStored)
    (wX_x12_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d98)
    retired inhibit config 0x33#8 0x66#8 0xe8#8 0x00
    (.RTYPE (.Regidx 14#5, .Regidx 16#5, .Regidx 12#5, .OR)) x12 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_a4_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d9c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d9c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d9c)).regs.get? x5 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d9c)).regs.get? x17 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d9c)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d9c)).regs.insert x14 (high ||| low)) }
        (BitVec.ofNat 64 0x12da0) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d9c = some 0x33 ∧
      Artifacts.programImage.readByte? 0x12d9d = some 0xe7 ∧
        Artifacts.programImage.readByte? 0x12d9e = some 0x12 ∧
          Artifacts.programImage.readByte? 0x12d9f = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d9c (by omega)
    afterIncrement 0x33 0xe7 0x12 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0xe7#8 0x12#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 17#5, .Regidx 5#5, .Regidx 14#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d9c))
    _ (.Regidx 17#5) (.Regidx 5#5) (.Regidx 14#5) high low
    (rX_x5_run _ high highStored) (rX_x17_run _ low lowStored)
    (wX_x14_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d9c)
    retired inhibit config 0x33#8 0xe7#8 0x12#8 0x01
    (.RTYPE (.Regidx 17#5, .Regidx 5#5, .Regidx 14#5, .OR)) x14 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_a1_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12da0))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12da0))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12da0)).regs.get? x15 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12da0)).regs.get? x11 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12da0)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12da0)).regs.insert x11 (high ||| low)) }
        (BitVec.ofNat 64 0x12da4) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12da0 = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12da1 = some 0xe5 ∧
        Artifacts.programImage.readByte? 0x12da2 = some 0xb7 ∧
          Artifacts.programImage.readByte? 0x12da3 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12da0 (by omega)
    afterIncrement 0xb3 0xe5 0xb7 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe5#8 0xb7#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 11#5, .Regidx 15#5, .Regidx 11#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12da0))
    _ (.Regidx 11#5) (.Regidx 15#5) (.Regidx 11#5) high low
    (rX_x15_run _ high highStored) (rX_x11_run _ low lowStored)
    (wX_x11_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12da0)
    retired inhibit config 0xb3#8 0xe5#8 0xb7#8 0x00
    (.RTYPE (.Regidx 11#5, .Regidx 15#5, .Regidx 11#5, .OR)) x11 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_a3_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12da4))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12da4))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12da4)).regs.get? x6 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12da4)).regs.get? x13 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12da4)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12da4)).regs.insert x13 (high ||| low)) }
        (BitVec.ofNat 64 0x12da8) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12da4 = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12da5 = some 0x66 ∧
        Artifacts.programImage.readByte? 0x12da6 = some 0xd3 ∧
          Artifacts.programImage.readByte? 0x12da7 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12da4 (by omega)
    afterIncrement 0xb3 0x66 0xd3 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x66#8 0xd3#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 13#5, .Regidx 6#5, .Regidx 13#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12da4))
    _ (.Regidx 13#5) (.Regidx 6#5) (.Regidx 13#5) high low
    (rX_x6_run _ high highStored) (rX_x13_run _ low lowStored)
    (wX_x13_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12da4)
    retired inhibit config 0xb3#8 0x66#8 0xd3#8 0x00
    (.RTYPE (.Regidx 13#5, .Regidx 6#5, .Regidx 13#5, .OR)) x13 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_a5_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12da8))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12da8))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12da8)).regs.get? x28 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12da8)).regs.get? x7 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12da8)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12da8)).regs.insert x15 (high ||| low)) }
        (BitVec.ofNat 64 0x12dac) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12da8 = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12da9 = some 0x67 ∧
        Artifacts.programImage.readByte? 0x12daa = some 0x7e ∧
          Artifacts.programImage.readByte? 0x12dab = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12da8 (by omega)
    afterIncrement 0xb3 0x67 0x7e 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x67#8 0x7e#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 7#5, .Regidx 28#5, .Regidx 15#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12da8))
    _ (.Regidx 7#5) (.Regidx 28#5) (.Regidx 15#5) high low
    (rX_x28_run _ high highStored) (rX_x7_run _ low lowStored)
    (wX_x15_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12da8)
    retired inhibit config 0xb3#8 0x67#8 0x7e#8 0x00
    (.RTYPE (.Regidx 7#5, .Regidx 28#5, .Regidx 15#5, .OR)) x15 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_a2_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12dac))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12dac))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12dac)).regs.get? x12 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12dac)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12dac)).regs.insert x12 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 32#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12db0) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12dac = some 0x13 ∧
      Artifacts.programImage.readByte? 0x12dad = some 0x16 ∧
        Artifacts.programImage.readByte? 0x12dae = some 0x06 ∧
          Artifacts.programImage.readByte? 0x12daf = some 0x02 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12dac (by omega)
    afterIncrement 0x13 0x16 0x06 0x02 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x16#8 0x06#8 0x02))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (32#6, .Regidx 12#5, .Regidx 12#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12dac))
    _ 32#6 (.Regidx 12#5) (.Regidx 12#5) value (rX_x12_run _ value stored)
    (wX_x12_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 32#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12dac)
    retired inhibit config 0x13#8 0x16#8 0x06#8 0x02
    (.SHIFTIOP (32#6, .Regidx 12#5, .Regidx 12#5, .SLLI)) x12 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 32#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_a1_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12db0))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12db0))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12db0)).regs.get? x11 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12db0)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12db0)).regs.insert x11 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 32#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12db4) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12db0 = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12db1 = some 0x95 ∧
        Artifacts.programImage.readByte? 0x12db2 = some 0x05 ∧
          Artifacts.programImage.readByte? 0x12db3 = some 0x02 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12db0 (by omega)
    afterIncrement 0x93 0x95 0x05 0x02 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x95#8 0x05#8 0x02))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (32#6, .Regidx 11#5, .Regidx 11#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12db0))
    _ 32#6 (.Regidx 11#5) (.Regidx 11#5) value (rX_x11_run _ value stored)
    (wX_x11_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 32#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12db0)
    retired inhibit config 0x93#8 0x95#8 0x05#8 0x02
    (.SHIFTIOP (32#6, .Regidx 11#5, .Regidx 11#5, .SLLI)) x11 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 32#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_a5_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12db4))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12db4))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12db4)).regs.get? x15 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12db4)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12db4)).regs.insert x15 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 32#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12db8) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12db4 = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12db5 = some 0x97 ∧
        Artifacts.programImage.readByte? 0x12db6 = some 0x07 ∧
          Artifacts.programImage.readByte? 0x12db7 = some 0x02 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12db4 (by omega)
    afterIncrement 0x93 0x97 0x07 0x02 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x97#8 0x07#8 0x02))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (32#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12db4))
    _ 32#6 (.Regidx 15#5) (.Regidx 15#5) value (rX_x15_run _ value stored)
    (wX_x15_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 32#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12db4)
    retired inhibit config 0x93#8 0x97#8 0x07#8 0x02
    (.SHIFTIOP (32#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) x15 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 32#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_s6_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12db8))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12db8))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12db8)).regs.get? x12 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12db8)).regs.get? x10 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12db8)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12db8)).regs.insert x22 (high ||| low)) }
        (BitVec.ofNat 64 0x12dbc) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12db8 = some 0x33 ∧
      Artifacts.programImage.readByte? 0x12db9 = some 0x6b ∧
        Artifacts.programImage.readByte? 0x12dba = some 0xa6 ∧
          Artifacts.programImage.readByte? 0x12dbb = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12db8 (by omega)
    afterIncrement 0x33 0x6b 0xa6 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x6b#8 0xa6#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 10#5, .Regidx 12#5, .Regidx 22#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12db8))
    _ (.Regidx 10#5) (.Regidx 12#5) (.Regidx 22#5) high low
    (rX_x12_run _ high highStored) (rX_x10_run _ low lowStored)
    (wX_x22_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12db8)
    retired inhibit config 0x33#8 0x6b#8 0xa6#8 0x00
    (.RTYPE (.Regidx 10#5, .Regidx 12#5, .Regidx 22#5, .OR)) x22 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_s5_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12dbc))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12dbc))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12dbc)).regs.get? x11 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12dbc)).regs.get? x14 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12dbc)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12dbc)).regs.insert x21 (high ||| low)) }
        (BitVec.ofNat 64 0x12dc0) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12dbc = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12dbd = some 0xea ∧
        Artifacts.programImage.readByte? 0x12dbe = some 0xe5 ∧
          Artifacts.programImage.readByte? 0x12dbf = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12dbc (by omega)
    afterIncrement 0xb3 0xea 0xe5 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xea#8 0xe5#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 14#5, .Regidx 11#5, .Regidx 21#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12dbc))
    _ (.Regidx 14#5) (.Regidx 11#5) (.Regidx 21#5) high low
    (rX_x11_run _ high highStored) (rX_x14_run _ low lowStored)
    (wX_x21_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12dbc)
    retired inhibit config 0xb3#8 0xea#8 0xe5#8 0x00
    (.RTYPE (.Regidx 14#5, .Regidx 11#5, .Regidx 21#5, .OR)) x21 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_assembly_s3_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12dc0))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12dc0))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12dc0)).regs.get? x15 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12dc0)).regs.get? x13 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12dc0)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12dc0)).regs.insert x19 (high ||| low)) }
        (BitVec.ofNat 64 0x12dc4) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12dc0 = some 0xb3 ∧
      Artifacts.programImage.readByte? 0x12dc1 = some 0xe9 ∧
        Artifacts.programImage.readByte? 0x12dc2 = some 0xd7 ∧
          Artifacts.programImage.readByte? 0x12dc3 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12dc0 (by omega)
    afterIncrement 0xb3 0xe9 0xd7 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe9#8 0xd7#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 13#5, .Regidx 15#5, .Regidx 19#5, .OR)) := by decode_run
  have execute := execute_RTYPE_or_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12dc0))
    _ (.Regidx 13#5) (.Regidx 15#5) (.Regidx 19#5) high low
    (rX_x15_run _ high highStored) (rX_x13_run _ low lowStored)
    (wX_x19_run _ (high ||| low))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12dc0)
    retired inhibit config 0xb3#8 0xe9#8 0xd7#8 0x00
    (.RTYPE (.Regidx 13#5, .Regidx 15#5, .Regidx 19#5, .OR)) x19 (high ||| low)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The second contiguous read group at `0x12d08–0x12d14` covers schedule bytes 12--15. -/
theorem raw_blob_schedule_second_group_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 : State)
    (thirteenth : Runs (try_step stepNo false) state0 state1 false)
    (fourteenth : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (fifteenth : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (sixteenth : Runs (try_step (stepNo + 3) false) state3 state4 false) :
    Trace stepNo 4 state0 state4 := by
  trace_steps [thirteenth, fourteenth, fifteenth, sixteenth]

/-- The remaining eight schedule-byte reads at `0x12ccc–0x12ce8` are contiguous, so their exact
retirements compose directly. -/
theorem raw_blob_schedule_middle_eight_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 state5 state6 state7 state8 : State)
    (fifth : Runs (try_step stepNo false) state0 state1 false)
    (sixth : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (seventh : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (eighth : Runs (try_step (stepNo + 3) false) state3 state4 false)
    (ninth : Runs (try_step (stepNo + 4) false) state4 state5 false)
    (tenth : Runs (try_step (stepNo + 5) false) state5 state6 false)
    (eleventh : Runs (try_step (stepNo + 6) false) state6 state7 false)
    (twelfth : Runs (try_step (stepNo + 7) false) state7 state8 false) :
    Trace stepNo 8 state0 state8 := by
  trace_steps [fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth]

/-- Compose the first four schedule-byte reads, the eight remaining reads of the present branch,
and the seven contiguous assembly instructions.  Every one of the nineteen instructions now has an
exact actual-PC retirement theorem, so each fragment is discharged from immutable ELF bytes and
generated Sail rather than assumed.  What still has to come from the live decoder run is the
dynamic data: each read's physical byte and the successive fetch/platform/counter premises. -/
theorem raw_blob_schedule_present_prefix_trace (stepNo : Nat)
    (state0 state4 state12 state19 : State)
    (firstReads : Trace stepNo 4 state0 state4)
    (remainingReads : Trace (stepNo + 4) 8 state4 state12)
    (assembly : Trace (stepNo + 12) 7 state12 state19) :
    Trace stepNo 19 state0 state19 := by
  have reads : Trace stepNo 12 state0 state12 := by
    simpa only [Nat.add_assoc] using Trace.append firstReads remainingReads
  have combined := Trace.append reads assembly
  simpa only [Nat.reduceAdd] using combined

/-- The second assembly fragment at `0x12d18–0x12d3c` is ten contiguous retiring instructions:
six shifts scaling schedule bytes 6--15, then four ORs folding them into `a6`, `a7`, `t0`, `a1`. -/
theorem raw_blob_schedule_second_assembly_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 state5 state6 state7 state8 state9 state10 : State)
    (a6Shift : Runs (try_step stepNo false) state0 state1 false)
    (a7Shift : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (t1Shift : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (t2Shift : Runs (try_step (stepNo + 3) false) state3 state4 false)
    (t3Shift : Runs (try_step (stepNo + 4) false) state4 state5 false)
    (a3Shift : Runs (try_step (stepNo + 5) false) state5 state6 false)
    (a6Or : Runs (try_step (stepNo + 6) false) state6 state7 false)
    (a7Or : Runs (try_step (stepNo + 7) false) state7 state8 false)
    (t0Or : Runs (try_step (stepNo + 8) false) state8 state9 false)
    (a1Or : Runs (try_step (stepNo + 9) false) state9 state10 false) :
    Trace stepNo 10 state0 state10 := by
  trace_steps [a6Shift, a7Shift, t1Shift, t2Shift, t3Shift, a3Shift, a6Or, a7Or, t0Or, a1Or]

/-- Extend the 19-step prefix through the second read group and the second assembly fragment,
covering every instruction from `0x12cbc` to `0x12d3c` inclusive.  As with the shorter prefix,
each fragment is discharged by exact actual-PC retirements; what remains to come from a live
decoder run is the dynamic data behind those retirements' premises. -/
theorem raw_blob_schedule_present_extended_trace (stepNo : Nat)
    (state0 state19 state23 state33 : State)
    (prefix19 : Trace stepNo 19 state0 state19)
    (secondGroup : Trace (stepNo + 19) 4 state19 state23)
    (secondAssembly : Trace (stepNo + 23) 10 state23 state33) :
    Trace stepNo 33 state0 state33 := by
  have throughReads : Trace stepNo 23 state0 state23 := by
    simpa only [Nat.add_assoc] using Trace.append prefix19 secondGroup
  have combined := Trace.append throughReads secondAssembly
  simpa only [Nat.reduceAdd] using combined

/-- The third contiguous read group at `0x12d40–0x12d4c` covers schedule bytes 16--19. -/
theorem raw_blob_schedule_third_group_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 : State)
    (seventeenth : Runs (try_step stepNo false) state0 state1 false)
    (eighteenth : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (nineteenth : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (twentieth : Runs (try_step (stepNo + 3) false) state3 state4 false) :
    Trace stepNo 4 state0 state4 := by
  trace_steps [seventeenth, eighteenth, nineteenth, twentieth]

/-- The third assembly fragment at `0x12d50–0x12d6c` is eight contiguous retiring instructions. -/
theorem raw_blob_schedule_third_assembly_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 state5 state6 state7 state8 : State)
    (a5Shift : Runs (try_step stepNo false) state0 state1 false)
    (t4Shift : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (t1Shift : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (t2Shift : Runs (try_step (stepNo + 3) false) state3 state4 false)
    (t3Shift : Runs (try_step (stepNo + 4) false) state4 state5 false)
    (a5Or : Runs (try_step (stepNo + 5) false) state5 state6 false)
    (a3Or : Runs (try_step (stepNo + 6) false) state6 state7 false)
    (t1Or : Runs (try_step (stepNo + 7) false) state7 state8 false) :
    Trace stepNo 8 state0 state8 := by
  trace_steps [a5Shift, t4Shift, t1Shift, t2Shift, t3Shift, a5Or, a3Or, t1Or]

/-- The fourth contiguous read group at `0x12d70–0x12d7c` covers the branch's final schedule bytes.
The decoder reads offset 21 before 20, so the group is not offset-ordered. -/
theorem raw_blob_schedule_fourth_group_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 : State)
    (twentyFirst : Runs (try_step stepNo false) state0 state1 false)
    (twentySecond : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (twentyThird : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (twentyFourth : Runs (try_step (stepNo + 3) false) state3 state4 false) :
    Trace stepNo 4 state0 state4 := by
  trace_steps [twentyFirst, twentySecond, twentyThird, twentyFourth]

/-- Every instruction from `0x12cbc` through `0x12d7c` -- all twenty-four schedule-byte reads and
the three intervening endian-assembly fragments -- now has an exact actual-PC retirement theorem,
and they compose into one forty-nine step trace.  This fixes the branch's complete instruction
sequence; instantiating it still requires the live decoder run's dynamic data, namely each read's
physical byte together with the successive fetch, platform, and counter premises. -/
theorem raw_blob_schedule_present_branch_trace (stepNo : Nat)
    (state0 state33 state37 state45 state49 : State)
    (through33 : Trace stepNo 33 state0 state33)
    (thirdGroup : Trace (stepNo + 33) 4 state33 state37)
    (thirdAssembly : Trace (stepNo + 37) 8 state37 state45)
    (fourthGroup : Trace (stepNo + 45) 4 state45 state49) :
    Trace stepNo 49 state0 state49 := by
  have a : Trace stepNo 37 state0 state37 := by
    simpa only [Nat.add_assoc] using Trace.append through33 thirdGroup
  have b : Trace stepNo 45 state0 state45 := by
    simpa only [Nat.add_assoc] using Trace.append a thirdAssembly
  have c := Trace.append b fourthGroup
  simpa only [Nat.reduceAdd] using c

/-- The fourth assembly fragment at `0x12d80–0x12dc0` is seventeen contiguous retiring
instructions.  It folds the branch's twenty-four bytes into the three 64-bit schedule words,
leaving them in `s6` (`x22`), `s5` (`x21`), and `s3` (`x19`). -/
theorem raw_blob_schedule_fourth_assembly_trace (stepNo : Nat)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 : State)
    (step0 : Runs (try_step stepNo false) s0 s1 false)
    (step1 : Runs (try_step (stepNo + 1) false) s1 s2 false)
    (step2 : Runs (try_step (stepNo + 2) false) s2 s3 false)
    (step3 : Runs (try_step (stepNo + 3) false) s3 s4 false)
    (step4 : Runs (try_step (stepNo + 4) false) s4 s5 false)
    (step5 : Runs (try_step (stepNo + 5) false) s5 s6 false)
    (step6 : Runs (try_step (stepNo + 6) false) s6 s7 false)
    (step7 : Runs (try_step (stepNo + 7) false) s7 s8 false)
    (step8 : Runs (try_step (stepNo + 8) false) s8 s9 false)
    (step9 : Runs (try_step (stepNo + 9) false) s9 s10 false)
    (step10 : Runs (try_step (stepNo + 10) false) s10 s11 false)
    (step11 : Runs (try_step (stepNo + 11) false) s11 s12 false)
    (step12 : Runs (try_step (stepNo + 12) false) s12 s13 false)
    (step13 : Runs (try_step (stepNo + 13) false) s13 s14 false)
    (step14 : Runs (try_step (stepNo + 14) false) s14 s15 false)
    (step15 : Runs (try_step (stepNo + 15) false) s15 s16 false)
    (step16 : Runs (try_step (stepNo + 16) false) s16 s17 false) :
    Trace stepNo 17 s0 s17 := by
  trace_steps [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
    step11, step12, step13, step14, step15, step16]

/-- The complete present blob-schedule byte assembly: every instruction from `0x12cbc` through
`0x12dc0` composes into one sixty-six step trace.  The branch's twenty-four bytes are read and
folded into its three 64-bit schedule words with no instruction assumed and none skipped.
Instantiation still requires the live decoder run's dynamic data -- each read's physical byte and
the successive fetch, platform, and counter premises -- so this is the branch's exact instruction
sequence, not a claim that it was executed. -/
theorem raw_blob_schedule_present_assembly_complete_trace (stepNo : Nat)
    (state0 state49 state66 : State)
    (through49 : Trace stepNo 49 state0 state49)
    (fourthAssembly : Trace (stepNo + 49) 17 state49 state66) :
    Trace stepNo 66 state0 state66 := by
  simpa only [Nat.reduceAdd] using Trace.append through49 fourthAssembly

end BinaryFv.Zesu.MachineExecution
