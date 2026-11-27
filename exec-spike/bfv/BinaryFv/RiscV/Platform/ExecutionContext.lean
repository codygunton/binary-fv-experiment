import BinaryFv.RiscV.Model.State

/-!
# Shared machine-execution register premises

Pure register facts reused below both instruction execution and full `try_step` retirement. Keeping
them below those proof layers avoids an import cycle and gives instruction proofs the same named
context vocabulary as `StepPlatform` and `StepCounters`.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The pre-step hart and counter facts required by the generated retirement postlude. -/
def RetirementContext (state : State) (retired : BitVec 64) (inhibit : BitVec 32)
    (config : BitVec 64) : Prop :=
  state.regs.get? hart_state = some (.HART_ACTIVE ()) ∧
  state.regs.get? mcountinhibit = some inhibit ∧
  state.regs.get? minstretcfg = some config ∧
  _get_Counterin_IR inhibit = 0#1 ∧
  _get_CountSmcntrpmf_MINH config = 0#1 ∧
  state.regs.get? minstret = some retired

end BinaryFv.RiscV
