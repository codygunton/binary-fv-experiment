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

/-- Generated Sail decodes the ELF-pinned first byte load of the present schedule payload. -/
theorem raw_blob_schedule_first_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x03#8 0xc5#8 0x0b#8 0x00#8)) state state
      (.LOAD (0#12, .Regidx 23#5, .Regidx 10#5, true, 1)) := by
  decode_run

theorem rX_x23_run (state : State) (value : BitVec 64)
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

end BinaryFv.Zesu.MachineExecution
