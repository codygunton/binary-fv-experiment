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

end BinaryFv.Zesu.MachineExecution
