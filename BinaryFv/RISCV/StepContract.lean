import BinaryFv.RISCV.Framing

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The hart-state selector used verbatim by generated `try_step`. -/
def activeHartStep (stepNo : Nat) (exitWait : Bool) : SailM Step := do
  match (← Sail.readReg hart_state) with
  | .HART_WAITING (reason, bits) => run_hart_waiting stepNo reason bits exitWait
  | .HART_ACTIVE () => run_hart_active stepNo

/-- `activeHartStep` is definitionally the generated selector immediately before its postlude. -/
theorem activeHartStep_eq_generated (stepNo : Nat) (exitWait : Bool) (state : State) :
    (do
      match (← Sail.readReg hart_state) with
      | .HART_WAITING (reason, bits) => run_hart_waiting stepNo reason bits exitWait
      | .HART_ACTIVE () => run_hart_active stepNo : SailM Step).run state =
        (activeHartStep stepNo exitWait).run state := by
  rfl

/-- Lift a generated active-hart step contract through the selector used by `try_step`. -/
theorem activeHartStep_active (stepNo : Nat) (exitWait : Bool) (before after : State)
    (result : Step) (hHart : before.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hActive : Runs (run_hart_active stepNo) before after result) :
    Runs (activeHartStep stepNo exitWait) before after result := by
  unfold Runs at hActive ⊢
  simp only [activeHartStep, EStateM.run, EStateM.bind, EStateM.instMonad,
    PreSail.readReg, EStateM.get, EStateM.pure, MonadState.get, MonadStateOf.get, getThe, hHart]
  exact hActive

end BinaryFv.RISCV
