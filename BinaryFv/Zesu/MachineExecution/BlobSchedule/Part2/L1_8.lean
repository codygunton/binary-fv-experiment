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

end BinaryFv.Zesu.MachineExecution
