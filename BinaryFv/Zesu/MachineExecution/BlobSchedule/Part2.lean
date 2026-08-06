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

/-- The present-blob-schedule branch begins by loading byte zero of its checked 24-byte span. -/
theorem raw_blob_schedule_first_lbu_image_bytes :
    Artifacts.programImage.readByte? 0x12cbc = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12cbd = some 0xc5 ∧
        Artifacts.programImage.readByte? 0x12cbe = some 0x0b ∧
          Artifacts.programImage.readByte? 0x12cbf = some 0x00 := by
  native_decide

/-- The first present-blob-schedule read is fetched from the immutable canonical ELF image. -/
theorem raw_blob_schedule_first_lbu_fetch (state : State)
    (loaded : Artifacts.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cbc)
      0x03#8 0xc5#8 0x0b#8 0x00#8 := by
  rcases raw_blob_schedule_first_lbu_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cbc (by omega)
    afterIncrement 0x03 0xc5 0x0b 0x00 read0 read1 read2 read3

/-- Generated Sail decodes the ELF-pinned first byte load of the present schedule payload. -/
theorem raw_blob_schedule_first_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x03#8 0xc5#8 0x0b#8 0x00#8)) state state
      (.LOAD (0#12, .Regidx 23#5, .Regidx 10#5, true, 1)) := by
  decode_run

private theorem rX_x23_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x23 = some value) :
    Runs (rX_bits (.Regidx 23#5)) state state value := by
  have index : (Sail.BitVec.toNatInt (23#5)).toNat = 23 := by decide
  unfold Runs
  simp [rX_bits, rX, index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
    EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg]



/-- The first six present-schedule bytes are assembled little-endian by these four shifts and
three ORs before the decoder continues with bytes 12--23.  These contracts retain the generated
Sail bit-vector expressions so a later live trace can connect them to the actual byte reads. -/
theorem raw_blob_schedule_second_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x11 = some value) :
    Runs (execute_SHIFTIOP 8#6 (.Regidx 11#5) (.Regidx 11#5) .SLLI) state
      { state with regs := (state.regs.insert x11
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 8#6 (.Regidx 11#5) (.Regidx 11#5) value
    (rX_x11_run state value stored)
    (wX_x11_run state (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_blob_schedule_third_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x12 = some value) :
    Runs (execute_SHIFTIOP 16#6 (.Regidx 12#5) (.Regidx 12#5) .SLLI) state
      { state with regs := (state.regs.insert x12
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 16#6 (.Regidx 12#5) (.Regidx 12#5) value
    (rX_x12_run state value stored)
    (wX_x12_run state (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_blob_schedule_fourth_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x13 = some value) :
    Runs (execute_SHIFTIOP 24#6 (.Regidx 13#5) (.Regidx 13#5) .SLLI) state
      { state with regs := (state.regs.insert x13
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 24#6 (.Regidx 13#5) (.Regidx 13#5) value
    (rX_x13_run state value stored)
    (wX_x13_run state (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_blob_schedule_sixth_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x15 = some value) :
    Runs (execute_SHIFTIOP 8#6 (.Regidx 15#5) (.Regidx 15#5) .SLLI) state
      { state with regs := (state.regs.insert x15
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 8#6 (.Regidx 15#5) (.Regidx 15#5) value
    (rX_x15_run state value stored)
    (wX_x15_run state (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_blob_schedule_first_word_low_or_execute (state : State) (high low : BitVec 64)
    (highStored : state.regs.get? x11 = some high) (lowStored : state.regs.get? x10 = some low) :
    Runs (execute_RTYPE (.Regidx 10#5) (.Regidx 11#5) (.Regidx 10#5) .OR) state
      { state with regs := state.regs.insert x10 (high ||| low) } (.Retire_Success ()) := by
  exact execute_RTYPE_or_run state _ (.Regidx 10#5) (.Regidx 11#5) (.Regidx 10#5) high low
    (rX_x11_run state high highStored) (rX_x10_run state low lowStored)
    (wX_x10_run state (high ||| low))

theorem raw_blob_schedule_first_word_high_or_execute (state : State) (high low : BitVec 64)
    (highStored : state.regs.get? x13 = some high) (lowStored : state.regs.get? x12 = some low) :
    Runs (execute_RTYPE (.Regidx 12#5) (.Regidx 13#5) (.Regidx 12#5) .OR) state
      { state with regs := state.regs.insert x12 (high ||| low) } (.Retire_Success ()) := by
  exact execute_RTYPE_or_run state _ (.Regidx 12#5) (.Regidx 13#5) (.Regidx 12#5) high low
    (rX_x13_run state high highStored) (rX_x12_run state low lowStored)
    (wX_x12_run state (high ||| low))

theorem raw_blob_schedule_second_word_low_or_execute (state : State) (high low : BitVec 64)
    (highStored : state.regs.get? x15 = some high) (lowStored : state.regs.get? x14 = some low) :
    Runs (execute_RTYPE (.Regidx 14#5) (.Regidx 15#5) (.Regidx 14#5) .OR) state
      { state with regs := state.regs.insert x14 (high ||| low) } (.Retire_Success ()) := by
  exact execute_RTYPE_or_run state _ (.Regidx 14#5) (.Regidx 15#5) (.Regidx 14#5) high low
    (rX_x15_run state high highStored) (rX_x14_run state low lowStored)
    (wX_x14_run state (high ||| low))

theorem raw_blob_schedule_second_byte_shift_fetch (state : State)
    (loaded : Artifacts.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cec)
      0x93#8 0x95#8 0x85#8 0x00#8 := by
  have image : Artifacts.programImage.readByte? 0x12cec = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12ced = some 0x95 ∧
        Artifacts.programImage.readByte? 0x12cee = some 0x85 ∧
          Artifacts.programImage.readByte? 0x12cef = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cec (by omega) afterIncrement
    0x93 0x95 0x85 0x00 read0 read1 read2 read3

theorem raw_blob_schedule_second_byte_shift_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x93#8 0x95#8 0x85#8 0x00#8)) state state
      (.SHIFTIOP (8#6, .Regidx 11#5, .Regidx 11#5, .SLLI)) := by
  decode_run

theorem raw_blob_schedule_second_byte_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cec))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cec))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cec)).regs.get? x11 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cec)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cec)).regs.insert x11
              (Sail.shift_bits_left value
                (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12cf0) retired) false := by
  have bytes := raw_blob_schedule_second_byte_shift_fetch state loaded
  have decode := raw_blob_schedule_second_byte_shift_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfg
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cec)
    retired inhibit config 0x93#8 0x95#8 0x85#8 0x00#8
    (.SHIFTIOP (8#6, .Regidx 11#5, .Regidx 11#5, .SLLI)) x11
    (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected
    (raw_blob_schedule_second_byte_shift_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cec))
      value stored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_third_byte_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf0))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf0))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cf0)).regs.get? x12 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf0)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cf0)).regs.insert x12 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12cf4) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cf0 = some 0x13 ∧
      Artifacts.programImage.readByte? 0x12cf1 = some 0x16 ∧
        Artifacts.programImage.readByte? 0x12cf2 = some 0x06 ∧
          Artifacts.programImage.readByte? 0x12cf3 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cf0 (by omega) afterIncrement
    0x13 0x16 0x06 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x16#8 0x06#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (16#6, .Regidx 12#5, .Regidx 12#5, .SLLI)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cf0)
    retired inhibit config 0x13#8 0x16#8 0x06#8 0x01
    (.SHIFTIOP (16#6, .Regidx 12#5, .Regidx 12#5, .SLLI)) x12 (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected
    (raw_blob_schedule_third_byte_shift_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf0))
      value stored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourth_byte_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf4))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf4))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cf4)).regs.get? x13 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf4)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cf4)).regs.insert x13 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12cf8) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cf4 = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12cf5 = some 0x96 ∧
        Artifacts.programImage.readByte? 0x12cf6 = some 0x86 ∧
          Artifacts.programImage.readByte? 0x12cf7 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cf4 (by omega) afterIncrement
    0x93 0x96 0x86 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x96#8 0x86#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (24#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cf4)
    retired inhibit config 0x93#8 0x96#8 0x86#8 0x01
    (.SHIFTIOP (24#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) x13 (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected
    (raw_blob_schedule_fourth_byte_shift_execute
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf4)) value stored)
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_sixth_byte_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf8))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf8))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cf8)).regs.get? x15 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf8)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cf8)).regs.insert x15 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12cfc) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cf8 = some 0x93 ∧ Artifacts.programImage.readByte? 0x12cf9 = some 0x97 ∧ Artifacts.programImage.readByte? 0x12cfa = some 0x87 ∧ Artifacts.programImage.readByte? 0x12cfb = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory (tryStepControlFlowAfterIncrement state).mem := by simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage (tryStepControlFlowAfterIncrement state) 0x12cf8 (by omega) afterIncrement 0x93 0x97 0x87 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x97#8 0x87#8 0x00#8)) (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cf8) retired inhibit config 0x93#8 0x97#8 0x87#8 0x00 (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) x15 (Sail.shift_bits_left value (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected (raw_blob_schedule_sixth_byte_shift_execute (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf8)) value stored) (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

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

private theorem raw_blob_schedule_lbu_address (state : State)
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

/-- Shared `lbu`-from-`s7` execution contract for the present blob-schedule branch.  The
destination is left general: each site supplies its own generated `wX_bits` reduction, so this
factors the address transformation and physical byte read out of the individual byte proofs. -/
private theorem raw_blob_schedule_lbu_execute_general (state post : State) (immBits : BitVec 12)
    (imm base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8) (rd : regidx)
    (immAgree : sign_extend (m := 64) immBits = imm)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + imm)) 1 false false false) state state (.Ok data))
    (write : Runs (wX_bits rd (zero_extend (m := 64) data)) state post ()) :
    Runs (execute_LOAD immBits (.Regidx 23#5) rd true 1) state post (.Retire_Success ()) := by
  apply execute_LOAD_run _ _ immBits (.Regidx 23#5) rd true 1 data (by decide)
  · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) immBits)
        (MemoryAccessType.Load mem_payload.Data) 1) state state
        (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + imm))) := by
      simpa [immAgree] using raw_blob_schedule_lbu_address state imm base mstatusBits mseccfgBits
        baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled
    exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) immBits) (base + imm)
      mstatusBits data mstatusRead privilegeRead mprvZero address
      (BinaryFv.RiscV.is_aligned_vaddr_one _) (by simpa [immAgree] using hread)
  · exact write

/-- The first schedule-payload byte read executes from `s7` and writes zero-extended `a0`. -/
theorem raw_blob_schedule_first_lbu_execute (state : State)
    (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr base) 1 false false false) state state (.Ok data)) :
    Runs (execute_LOAD 0#12 (.Regidx 23#5) (.Regidx 10#5) true 1) state
      { state with regs := state.regs.insert x10 (zero_extend (m := 64) data) }
      (.Retire_Success ()) := by
  apply execute_LOAD_run state _ 0#12 (.Regidx 23#5) (.Regidx 10#5) true 1 data (by decide)
  · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 0#12)
        (MemoryAccessType.Load mem_payload.Data) 1) state state
        (.Ext_DataAddr_OK (virtaddr.Virtaddr base)) := by
      simpa using raw_blob_schedule_lbu_address state 0#64 base mstatusBits mseccfgBits baseRead
        mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled
    exact vmem_read_byte_run state (.Regidx 23#5) (sign_extend (m := 64) 0#12) base mstatusBits
      data mstatusRead privilegeRead mprvZero address (BinaryFv.RiscV.is_aligned_vaddr_one _)
      (by simpa using hread)
  · exact wX_x10_run state (zero_extend (m := 64) data)

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

/-- The second present-schedule byte load is fetched from the immutable canonical ELF image. -/
theorem raw_blob_schedule_second_lbu_fetch (state : State)
    (loaded : Artifacts.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc0)
      0x83#8 0xc5#8 0x1b#8 0x00#8 := by
  have image : Artifacts.programImage.readByte? 0x12cc0 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12cc1 = some 0xc5 ∧
        Artifacts.programImage.readByte? 0x12cc2 = some 0x1b ∧
          Artifacts.programImage.readByte? 0x12cc3 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cc0 (by omega)
    afterIncrement 0x83 0xc5 0x1b 0x00 read0 read1 read2 read3

/-- Generated Sail decodes the ELF-pinned second byte load of the present schedule payload. -/
theorem raw_blob_schedule_second_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x83#8 0xc5#8 0x1b#8 0x00#8)) state state
      (.LOAD (1#12, .Regidx 23#5, .Regidx 11#5, true, 1)) := by
  decode_run

/-- The second schedule-payload byte read executes from `s7 + 1` and writes zero-extended `a1`. -/
theorem raw_blob_schedule_second_lbu_execute (state : State)
    (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 1#64)) 1 false false false) state state (.Ok data)) :
    Runs (execute_LOAD 1#12 (.Regidx 23#5) (.Regidx 11#5) true 1) state
      { state with regs := state.regs.insert x11 (zero_extend (m := 64) data) }
      (.Retire_Success ()) := by
  apply execute_LOAD_run state _ 1#12 (.Regidx 23#5) (.Regidx 11#5) true 1 data (by decide)
  · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 1#12)
        (MemoryAccessType.Load mem_payload.Data) 1) state state
        (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 1#64))) := by
      simpa using raw_blob_schedule_lbu_address state 1#64 base mstatusBits mseccfgBits baseRead
        mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled
    exact vmem_read_byte_run state (.Regidx 23#5) (sign_extend (m := 64) 1#12) (base + 1#64)
      mstatusBits data mstatusRead privilegeRead mprvZero address
      (BinaryFv.RiscV.is_aligned_vaddr_one _) (by simpa using hread)
  · exact wX_x11_run state (zero_extend (m := 64) data)

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

/-- The third present-schedule byte load is fetched from immutable ELF bytes and retires at PC
`0x12cc4`, preserving all unmodeled runtime behavior as explicit premises. -/
theorem raw_blob_schedule_third_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc4))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc4)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc4)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc4)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc4)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 2#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cc4)).regs.insert x12 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cc8) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cc4 = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12cc5 = some 0xc6 ∧
        Artifacts.programImage.readByte? 0x12cc6 = some 0x2b ∧
          Artifacts.programImage.readByte? 0x12cc7 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cc4 (by omega)
    afterIncrement 0x03 0xc6 0x2b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc6#8 0x2b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (2#12, .Regidx 23#5, .Regidx 12#5, true, 1)) := by decode_run
  have execute : Runs (execute_LOAD 2#12 (.Regidx 23#5) (.Regidx 12#5) true 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4)
        with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x12cc4)).regs.insert x12 (zero_extend (m := 64) data)) }
      (.Retire_Success ()) := by
    apply execute_LOAD_run _ _ 2#12 (.Regidx 23#5) (.Regidx 12#5) true 1 data (by decide)
    · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 2#12)
          (MemoryAccessType.Load mem_payload.Data) 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
          (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 2#64))) := by
        simpa using raw_blob_schedule_lbu_address
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc4))
          2#64 base mstatusBits mseccfgBits baseRead mstatusRead privilegeRead mprvZero mseccfgRead
          pmmDisabled
      exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) 2#12) (base + 2#64)
        mstatusBits data mstatusRead privilegeRead mprvZero address
        (BinaryFv.RiscV.is_aligned_vaddr_one _) hread
    · exact wX_x12_run _ (zero_extend (m := 64) data)
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cc4)
    retired inhibit config 0x03#8 0xc6#8 0x2b#8 0x00
    (.LOAD (2#12, .Regidx 23#5, .Regidx 12#5, true, 1)) x12 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The fourth present-schedule byte load is checked and retired at its immutable ELF PC. -/
theorem raw_blob_schedule_fourth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc8))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc8)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc8)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc8)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cc8)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 3#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cc8)).regs.insert x13 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12ccc) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cc8 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12cc9 = some 0xc6 ∧
        Artifacts.programImage.readByte? 0x12cca = some 0x3b ∧
          Artifacts.programImage.readByte? 0x12ccb = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cc8 (by omega)
    afterIncrement 0x83 0xc6 0x3b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc6#8 0x3b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (3#12, .Regidx 23#5, .Regidx 13#5, true, 1)) := by decode_run
  have execute : Runs (execute_LOAD 3#12 (.Regidx 23#5) (.Regidx 13#5) true 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8)
        with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x12cc8)).regs.insert x13 (zero_extend (m := 64) data)) }
      (.Retire_Success ()) := by
    apply execute_LOAD_run _ _ 3#12 (.Regidx 23#5) (.Regidx 13#5) true 1 data (by decide)
    · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 3#12)
          (MemoryAccessType.Load mem_payload.Data) 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
          (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 3#64))) := by
        simpa using raw_blob_schedule_lbu_address
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc8))
          3#64 base mstatusBits mseccfgBits baseRead mstatusRead privilegeRead mprvZero mseccfgRead
          pmmDisabled
      exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) 3#12) (base + 3#64)
        mstatusBits data mstatusRead privilegeRead mprvZero address
        (BinaryFv.RiscV.is_aligned_vaddr_one _) hread
    · exact wX_x13_run _ (zero_extend (m := 64) data)
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cc8)
    retired inhibit config 0x83#8 0xc6#8 0x3b#8 0x00
    (.LOAD (3#12, .Regidx 23#5, .Regidx 13#5, true, 1)) x13 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- The fifth present-schedule byte load is checked and retired at its immutable ELF PC. -/
theorem raw_blob_schedule_fifth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ccc))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ccc)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ccc)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ccc)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ccc)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 4#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12ccc)).regs.insert x14 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cd0) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12ccc = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12ccd = some 0xc7 ∧
        Artifacts.programImage.readByte? 0x12cce = some 0x4b ∧
          Artifacts.programImage.readByte? 0x12ccf = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12ccc (by omega)
    afterIncrement 0x03 0xc7 0x4b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc7#8 0x4b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (4#12, .Regidx 23#5, .Regidx 14#5, true, 1)) := by decode_run
  have execute : Runs (execute_LOAD 4#12 (.Regidx 23#5) (.Regidx 14#5) true 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc)
        with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x12ccc)).regs.insert x14 (zero_extend (m := 64) data)) }
      (.Retire_Success ()) := by
    apply execute_LOAD_run _ _ 4#12 (.Regidx 23#5) (.Regidx 14#5) true 1 data (by decide)
    · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 4#12)
          (MemoryAccessType.Load mem_payload.Data) 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
          (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 4#64))) := by
        simpa using raw_blob_schedule_lbu_address
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ccc))
          4#64 base mstatusBits mseccfgBits baseRead mstatusRead privilegeRead mprvZero mseccfgRead
          pmmDisabled
      exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) 4#12) (base + 4#64)
        mstatusBits data mstatusRead privilegeRead mprvZero address
        (BinaryFv.RiscV.is_aligned_vaddr_one _) hread
    · exact wX_x14_run _ (zero_extend (m := 64) data)
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12ccc)
    retired inhibit config 0x03#8 0xc7#8 0x4b#8 0x00
    (.LOAD (4#12, .Regidx 23#5, .Regidx 14#5, true, 1)) x14 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_sixth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd0))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd0)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd0)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd0)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd0)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 5#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cd0)).regs.insert x15 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cd4) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cd0 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12cd1 = some 0xc7 ∧
        Artifacts.programImage.readByte? 0x12cd2 = some 0x5b ∧
          Artifacts.programImage.readByte? 0x12cd3 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cd0 (by omega)
    afterIncrement 0x83 0xc7 0x5b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc7#8 0x5b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (5#12, .Regidx 23#5, .Regidx 15#5, true, 1)) := by decode_run
  have execute : Runs (execute_LOAD 5#12 (.Regidx 23#5) (.Regidx 15#5) true 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0)
        with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x12cd0)).regs.insert x15 (zero_extend (m := 64) data)) }
      (.Retire_Success ()) := by
    apply execute_LOAD_run _ _ 5#12 (.Regidx 23#5) (.Regidx 15#5) true 1 data (by decide)
    · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 5#12)
          (MemoryAccessType.Load mem_payload.Data) 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
          (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 5#64))) := by
        simpa using raw_blob_schedule_lbu_address
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd0))
          5#64 base mstatusBits mseccfgBits baseRead mstatusRead privilegeRead mprvZero mseccfgRead
          pmmDisabled
      exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) 5#12) (base + 5#64)
        mstatusBits data mstatusRead privilegeRead mprvZero address
        (BinaryFv.RiscV.is_aligned_vaddr_one _) hread
    · exact wX_x15_run _ (zero_extend (m := 64) data)
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cd0)
    retired inhibit config 0x83#8 0xc7#8 0x5b#8 0x00
    (.LOAD (5#12, .Regidx 23#5, .Regidx 15#5, true, 1)) x15 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_seventh_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd4))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd4))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd4)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd4)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd4)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd4)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 6#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd4))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd4)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cd4)).regs.insert x16 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cd8) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cd4 = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12cd5 = some 0xc8 ∧
        Artifacts.programImage.readByte? 0x12cd6 = some 0x6b ∧
          Artifacts.programImage.readByte? 0x12cd7 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cd4 (by omega)
    afterIncrement 0x03 0xc8 0x6b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc8#8 0x6b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (6#12, .Regidx 23#5, .Regidx 16#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd4))
    _ 6#12 6#64 base mstatusBits mseccfgBits data (.Regidx 16#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x16_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cd4)
    retired inhibit config 0x03#8 0xc8#8 0x6b#8 0x00
    (.LOAD (6#12, .Regidx 23#5, .Regidx 16#5, true, 1)) x16 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_eighth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd8))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd8))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd8)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd8)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd8)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cd8)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 7#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd8))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd8)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cd8)).regs.insert x17 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cdc) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cd8 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12cd9 = some 0xc8 ∧
        Artifacts.programImage.readByte? 0x12cda = some 0x7b ∧
          Artifacts.programImage.readByte? 0x12cdb = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cd8 (by omega)
    afterIncrement 0x83 0xc8 0x7b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc8#8 0x7b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (7#12, .Regidx 23#5, .Regidx 17#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cd8))
    _ 7#12 7#64 base mstatusBits mseccfgBits data (.Regidx 17#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x17_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cd8)
    retired inhibit config 0x83#8 0xc8#8 0x7b#8 0x00
    (.LOAD (7#12, .Regidx 23#5, .Regidx 17#5, true, 1)) x17 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_ninth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cdc))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cdc))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cdc)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cdc)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cdc)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cdc)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 8#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cdc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cdc))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cdc)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cdc)).regs.insert x5 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12ce0) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cdc = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12cdd = some 0xc2 ∧
        Artifacts.programImage.readByte? 0x12cde = some 0x8b ∧
          Artifacts.programImage.readByte? 0x12cdf = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cdc (by omega)
    afterIncrement 0x83 0xc2 0x8b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc2#8 0x8b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (8#12, .Regidx 23#5, .Regidx 5#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cdc))
    _ 8#12 8#64 base mstatusBits mseccfgBits data (.Regidx 5#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x5_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cdc)
    retired inhibit config 0x83#8 0xc2#8 0x8b#8 0x00
    (.LOAD (8#12, .Regidx 23#5, .Regidx 5#5, true, 1)) x5 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_tenth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce0))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce0))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce0)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce0)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce0)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce0)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 9#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce0))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce0))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce0)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12ce0)).regs.insert x6 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12ce4) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12ce0 = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12ce1 = some 0xc3 ∧
        Artifacts.programImage.readByte? 0x12ce2 = some 0x9b ∧
          Artifacts.programImage.readByte? 0x12ce3 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12ce0 (by omega)
    afterIncrement 0x03 0xc3 0x9b 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc3#8 0x9b#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (9#12, .Regidx 23#5, .Regidx 6#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce0))
    _ 9#12 9#64 base mstatusBits mseccfgBits data (.Regidx 6#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x6_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12ce0)
    retired inhibit config 0x03#8 0xc3#8 0x9b#8 0x00
    (.LOAD (9#12, .Regidx 23#5, .Regidx 6#5, true, 1)) x6 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_eleventh_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce4))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce4))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce4)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce4)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce4)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce4)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 10#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce4))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce4)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12ce4)).regs.insert x7 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12ce8) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12ce4 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12ce5 = some 0xc3 ∧
        Artifacts.programImage.readByte? 0x12ce6 = some 0xab ∧
          Artifacts.programImage.readByte? 0x12ce7 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12ce4 (by omega)
    afterIncrement 0x83 0xc3 0xab 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc3#8 0xab#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (10#12, .Regidx 23#5, .Regidx 7#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce4))
    _ 10#12 10#64 base mstatusBits mseccfgBits data (.Regidx 7#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x7_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12ce4)
    retired inhibit config 0x83#8 0xc3#8 0xab#8 0x00
    (.LOAD (10#12, .Regidx 23#5, .Regidx 7#5, true, 1)) x7 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_twelfth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce8))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce8))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce8)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce8)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce8)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12ce8)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 11#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce8))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce8)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12ce8)).regs.insert x28 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12cec) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12ce8 = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12ce9 = some 0xce ∧
        Artifacts.programImage.readByte? 0x12cea = some 0xbb ∧
          Artifacts.programImage.readByte? 0x12ceb = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12ce8 (by omega)
    afterIncrement 0x03 0xce 0xbb 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xce#8 0xbb#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (11#12, .Regidx 23#5, .Regidx 28#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ce8))
    _ 11#12 11#64 base mstatusBits mseccfgBits data (.Regidx 28#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x28_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12ce8)
    retired inhibit config 0x03#8 0xce#8 0xbb#8 0x00
    (.LOAD (11#12, .Regidx 23#5, .Regidx 28#5, true, 1)) x28 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- Kernel-checked composition of the first four concrete schedule-byte retirements.  Instantiating
this trace requires the corresponding successive runtime fetch/platform/read premises. -/
theorem raw_blob_schedule_first_four_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 : State)
    (first : Runs (try_step stepNo false) state0 state1 false)
    (second : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (third : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (fourth : Runs (try_step (stepNo + 3) false) state3 state4 false) :
    Trace stepNo 4 state0 state4 := by
  trace_steps [first, second, third, fourth]

/-- The four shifts and three ORs at `0x12cec–0x12d04` are seven contiguous retiring instructions,
so their exact retirements compose without an intervening parser instruction. -/
theorem raw_blob_schedule_assembly_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 state5 state6 state7 : State)
    (shift8 : Runs (try_step stepNo false) state0 state1 false)
    (shift16 : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (shift24 : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (shift8' : Runs (try_step (stepNo + 3) false) state3 state4 false)
    (lowOr : Runs (try_step (stepNo + 4) false) state4 state5 false)
    (highOr : Runs (try_step (stepNo + 5) false) state5 state6 false)
    (secondLowOr : Runs (try_step (stepNo + 6) false) state6 state7 false) :
    Trace stepNo 7 state0 state7 := by
  trace_steps [shift8, shift16, shift24, shift8', lowOr, highOr, secondLowOr]

theorem raw_blob_schedule_thirteenth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d08))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d08))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d08)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d08)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d08)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d08)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 12#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d08))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d08))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d08)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d08)).regs.insert x11 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d0c) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d08 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12d09 = some 0xc5 ∧
        Artifacts.programImage.readByte? 0x12d0a = some 0xcb ∧
          Artifacts.programImage.readByte? 0x12d0b = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d08 (by omega)
    afterIncrement 0x83 0xc5 0xcb 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc5#8 0xcb#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (12#12, .Regidx 23#5, .Regidx 11#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d08))
    _ 12#12 12#64 base mstatusBits mseccfgBits data (.Regidx 11#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x11_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d08)
    retired inhibit config 0x83#8 0xc5#8 0xcb#8 0x00
    (.LOAD (12#12, .Regidx 23#5, .Regidx 11#5, true, 1)) x11 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_fourteenth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d0c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d0c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d0c)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d0c)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d0c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d0c)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 13#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d0c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d0c))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d0c)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d0c)).regs.insert x13 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d10) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d0c = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12d0d = some 0xc6 ∧
        Artifacts.programImage.readByte? 0x12d0e = some 0xdb ∧
          Artifacts.programImage.readByte? 0x12d0f = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d0c (by omega)
    afterIncrement 0x83 0xc6 0xdb 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc6#8 0xdb#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (13#12, .Regidx 23#5, .Regidx 13#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d0c))
    _ 13#12 13#64 base mstatusBits mseccfgBits data (.Regidx 13#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x13_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d0c)
    retired inhibit config 0x83#8 0xc6#8 0xdb#8 0x00
    (.LOAD (13#12, .Regidx 23#5, .Regidx 13#5, true, 1)) x13 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

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

theorem raw_blob_schedule_second_assembly_a6_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d18))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d18))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d18)).regs.get? x16 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d18)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d18)).regs.insert x16 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d1c) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d18 = some 0x13 ∧
      Artifacts.programImage.readByte? 0x12d19 = some 0x18 ∧
        Artifacts.programImage.readByte? 0x12d1a = some 0x08 ∧
          Artifacts.programImage.readByte? 0x12d1b = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d18 (by omega)
    afterIncrement 0x13 0x18 0x08 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x18#8 0x08#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (16#6, .Regidx 16#5, .Regidx 16#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d18))
    _ 16#6 (.Regidx 16#5) (.Regidx 16#5) value (rX_x16_run _ value stored)
    (wX_x16_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d18)
    retired inhibit config 0x13#8 0x18#8 0x08#8 0x01
    (.SHIFTIOP (16#6, .Regidx 16#5, .Regidx 16#5, .SLLI)) x16 (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_second_assembly_a7_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d1c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d1c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d1c)).regs.get? x17 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d1c)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d1c)).regs.insert x17 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d20) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d1c = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12d1d = some 0x98 ∧
        Artifacts.programImage.readByte? 0x12d1e = some 0x88 ∧
          Artifacts.programImage.readByte? 0x12d1f = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d1c (by omega)
    afterIncrement 0x93 0x98 0x88 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x98#8 0x88#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (24#6, .Regidx 17#5, .Regidx 17#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d1c))
    _ 24#6 (.Regidx 17#5) (.Regidx 17#5) value (rX_x17_run _ value stored)
    (wX_x17_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d1c)
    retired inhibit config 0x93#8 0x98#8 0x88#8 0x01
    (.SHIFTIOP (24#6, .Regidx 17#5, .Regidx 17#5, .SLLI)) x17 (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

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

theorem raw_blob_schedule_second_assembly_t3_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d28))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d28))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d28)).regs.get? x28 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d28)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d28)).regs.insert x28 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d2c) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d28 = some 0x13 ∧
      Artifacts.programImage.readByte? 0x12d29 = some 0x1e ∧
        Artifacts.programImage.readByte? 0x12d2a = some 0x8e ∧
          Artifacts.programImage.readByte? 0x12d2b = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d28 (by omega)
    afterIncrement 0x13 0x1e 0x8e 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x1e#8 0x8e#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (24#6, .Regidx 28#5, .Regidx 28#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d28))
    _ 24#6 (.Regidx 28#5) (.Regidx 28#5) value (rX_x28_run _ value stored)
    (wX_x28_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d28)
    retired inhibit config 0x13#8 0x1e#8 0x8e#8 0x01
    (.SHIFTIOP (24#6, .Regidx 28#5, .Regidx 28#5, .SLLI)) x28 (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_second_assembly_a3_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d2c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d2c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d2c)).regs.get? x13 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d2c)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d2c)).regs.insert x13 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d30) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d2c = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12d2d = some 0x96 ∧
        Artifacts.programImage.readByte? 0x12d2e = some 0x86 ∧
          Artifacts.programImage.readByte? 0x12d2f = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d2c (by omega)
    afterIncrement 0x93 0x96 0x86 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x96#8 0x86#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (8#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d2c))
    _ 8#6 (.Regidx 13#5) (.Regidx 13#5) value (rX_x13_run _ value stored)
    (wX_x13_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d2c)
    retired inhibit config 0x93#8 0x96#8 0x86#8 0x00
    (.SHIFTIOP (8#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) x13 (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

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

theorem raw_blob_schedule_seventeenth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d40))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d40))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d40)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d40)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d40)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d40)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 16#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d40))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d40))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d40)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d40)).regs.insert x13 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d44) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d40 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12d41 = some 0xc6 ∧
        Artifacts.programImage.readByte? 0x12d42 = some 0x0b ∧
          Artifacts.programImage.readByte? 0x12d43 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d40 (by omega)
    afterIncrement 0x83 0xc6 0x0b 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc6#8 0x0b#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (16#12, .Regidx 23#5, .Regidx 13#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d40))
    _ 16#12 16#64 base mstatusBits mseccfgBits data (.Regidx 13#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x13_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d40)
    retired inhibit config 0x83#8 0xc6#8 0x0b#8 0x01
    (.LOAD (16#12, .Regidx 23#5, .Regidx 13#5, true, 1)) x13 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_eighteenth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d44))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d44))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d44)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d44)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d44)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d44)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 17#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d44))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d44)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d44)).regs.insert x6 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d48) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d44 = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12d45 = some 0xc3 ∧
        Artifacts.programImage.readByte? 0x12d46 = some 0x1b ∧
          Artifacts.programImage.readByte? 0x12d47 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d44 (by omega)
    afterIncrement 0x03 0xc3 0x1b 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc3#8 0x1b#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (17#12, .Regidx 23#5, .Regidx 6#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d44))
    _ 17#12 17#64 base mstatusBits mseccfgBits data (.Regidx 6#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x6_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d44)
    retired inhibit config 0x03#8 0xc3#8 0x1b#8 0x01
    (.LOAD (17#12, .Regidx 23#5, .Regidx 6#5, true, 1)) x6 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_nineteenth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d48))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d48))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d48)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d48)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d48)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d48)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 18#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d48))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d48))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d48)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d48)).regs.insert x7 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d4c) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d48 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12d49 = some 0xc3 ∧
        Artifacts.programImage.readByte? 0x12d4a = some 0x2b ∧
          Artifacts.programImage.readByte? 0x12d4b = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d48 (by omega)
    afterIncrement 0x83 0xc3 0x2b 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc3#8 0x2b#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (18#12, .Regidx 23#5, .Regidx 7#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d48))
    _ 18#12 18#64 base mstatusBits mseccfgBits data (.Regidx 7#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x7_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d48)
    retired inhibit config 0x83#8 0xc3#8 0x2b#8 0x01
    (.LOAD (18#12, .Regidx 23#5, .Regidx 7#5, true, 1)) x7 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_twentieth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d4c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d4c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d4c)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d4c)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d4c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d4c)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 19#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d4c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d4c))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d4c)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d4c)).regs.insert x28 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d50) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d4c = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12d4d = some 0xce ∧
        Artifacts.programImage.readByte? 0x12d4e = some 0x3b ∧
          Artifacts.programImage.readByte? 0x12d4f = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d4c (by omega)
    afterIncrement 0x03 0xce 0x3b 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xce#8 0x3b#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (19#12, .Regidx 23#5, .Regidx 28#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d4c))
    _ 19#12 19#64 base mstatusBits mseccfgBits data (.Regidx 28#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x28_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d4c)
    retired inhibit config 0x03#8 0xce#8 0x3b#8 0x01
    (.LOAD (19#12, .Regidx 23#5, .Regidx 28#5, true, 1)) x28 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

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

theorem raw_blob_schedule_third_assembly_t1_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d58))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d58))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d58)).regs.get? x6 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d58)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d58)).regs.insert x6 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d5c) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d58 = some 0x13 ∧
      Artifacts.programImage.readByte? 0x12d59 = some 0x13 ∧
        Artifacts.programImage.readByte? 0x12d5a = some 0x83 ∧
          Artifacts.programImage.readByte? 0x12d5b = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d58 (by omega)
    afterIncrement 0x13 0x13 0x83 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x13#8 0x83#8 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (8#6, .Regidx 6#5, .Regidx 6#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d58))
    _ 8#6 (.Regidx 6#5) (.Regidx 6#5) value (rX_x6_run _ value stored)
    (wX_x6_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d58)
    retired inhibit config 0x13#8 0x13#8 0x83#8 0x00
    (.SHIFTIOP (8#6, .Regidx 6#5, .Regidx 6#5, .SLLI)) x6 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_third_assembly_t2_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d5c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d5c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d5c)).regs.get? x7 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d5c)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d5c)).regs.insert x7 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12d60) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d5c = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12d5d = some 0x93 ∧
        Artifacts.programImage.readByte? 0x12d5e = some 0x03 ∧
          Artifacts.programImage.readByte? 0x12d5f = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d5c (by omega)
    afterIncrement 0x93 0x93 0x03 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x93#8 0x03#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (16#6, .Regidx 7#5, .Regidx 7#5, .SLLI)) := by decode_run
  have execute := execute_SHIFTIOP_slli_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d5c))
    _ 16#6 (.Regidx 7#5) (.Regidx 7#5) value (rX_x7_run _ value stored)
    (wX_x7_run _ (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d5c)
    retired inhibit config 0x93#8 0x93#8 0x03#8 0x01
    (.SHIFTIOP (16#6, .Regidx 7#5, .Regidx 7#5, .SLLI)) x7 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

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

theorem raw_blob_schedule_twenty_first_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d70))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d70))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d70)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d70)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d70)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d70)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 21#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d70))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d70))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d70)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d70)).regs.insert x7 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d74) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d70 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12d71 = some 0xc3 ∧
        Artifacts.programImage.readByte? 0x12d72 = some 0x5b ∧
          Artifacts.programImage.readByte? 0x12d73 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d70 (by omega)
    afterIncrement 0x83 0xc3 0x5b 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc3#8 0x5b#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (21#12, .Regidx 23#5, .Regidx 7#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d70))
    _ 21#12 21#64 base mstatusBits mseccfgBits data (.Regidx 7#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x7_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d70)
    retired inhibit config 0x83#8 0xc3#8 0x5b#8 0x01
    (.LOAD (21#12, .Regidx 23#5, .Regidx 7#5, true, 1)) x7 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_twenty_second_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d74))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d74))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d74)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d74)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d74)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d74)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 20#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d74))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d74))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d74)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d74)).regs.insert x28 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d78) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d74 = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12d75 = some 0xce ∧
        Artifacts.programImage.readByte? 0x12d76 = some 0x4b ∧
          Artifacts.programImage.readByte? 0x12d77 = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d74 (by omega)
    afterIncrement 0x03 0xce 0x4b 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xce#8 0x4b#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (20#12, .Regidx 23#5, .Regidx 28#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d74))
    _ 20#12 20#64 base mstatusBits mseccfgBits data (.Regidx 28#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x28_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d74)
    retired inhibit config 0x03#8 0xce#8 0x4b#8 0x01
    (.LOAD (20#12, .Regidx 23#5, .Regidx 28#5, true, 1)) x28 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_twenty_third_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d78))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d78))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d78)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d78)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d78)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d78)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 22#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d78))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d78))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d78)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d78)).regs.insert x29 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d7c) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d78 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12d79 = some 0xce ∧
        Artifacts.programImage.readByte? 0x12d7a = some 0x6b ∧
          Artifacts.programImage.readByte? 0x12d7b = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d78 (by omega)
    afterIncrement 0x83 0xce 0x6b 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xce#8 0x6b#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (22#12, .Regidx 23#5, .Regidx 29#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d78))
    _ 22#12 22#64 base mstatusBits mseccfgBits data (.Regidx 29#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x29_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d78)
    retired inhibit config 0x83#8 0xce#8 0x6b#8 0x01
    (.LOAD (22#12, .Regidx 23#5, .Regidx 29#5, true, 1)) x29 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

theorem raw_blob_schedule_twenty_fourth_lbu_retire_exact (stepNo : Nat) (state : State)
    (base mstatusBits retired mseccfgBits : BitVec 64) (data : BitVec 8)
    (inhibit : BitVec 32) (config : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d7c))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d7c))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (baseRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d7c)).regs.get? x23 = some base)
    (mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d7c)).regs.get? mstatus = some mstatusBits)
    (privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d7c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12d7c)).regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 23#64)) 1 false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d7c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d7c))
      (.Ok data))
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d7c)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12d7c)).regs.insert x30 (zero_extend (m := 64) data)) }
        (BitVec.ofNat 64 0x12d80) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12d7c = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12d7d = some 0xcf ∧
        Artifacts.programImage.readByte? 0x12d7e = some 0x7b ∧
          Artifacts.programImage.readByte? 0x12d7f = some 0x01 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12d7c (by omega)
    afterIncrement 0x03 0xcf 0x7b 0x01 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xcf#8 0x7b#8 0x01))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (23#12, .Regidx 23#5, .Regidx 30#5, true, 1)) := by decode_run
  have execute := raw_blob_schedule_lbu_execute_general
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12d7c))
    _ 23#12 23#64 base mstatusBits mseccfgBits data (.Regidx 30#5) (by decide)
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled hread
    (wX_x30_run _ (zero_extend (m := 64) data))
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12d7c)
    retired inhibit config 0x03#8 0xcf#8 0x7b#8 0x01
    (.LOAD (23#12, .Regidx 23#5, .Regidx 30#5, true, 1)) x30 (zero_extend (m := 64) data)
    platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected execute
    (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
