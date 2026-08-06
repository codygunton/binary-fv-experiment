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

end BinaryFv.Zesu.MachineExecution
