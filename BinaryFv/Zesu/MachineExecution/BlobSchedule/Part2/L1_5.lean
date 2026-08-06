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

end BinaryFv.Zesu.MachineExecution
