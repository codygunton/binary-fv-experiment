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

end BinaryFv.Zesu.MachineExecution
