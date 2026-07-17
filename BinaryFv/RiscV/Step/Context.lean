import BinaryFv.RiscV.Step.ControlFlow
import BinaryFv.RiscV.Platform.FetchMemory

/-!
# Shared step-context bundles

The two premise bundles every per-instruction step contract carries: the generated fetch/decode
platform at the body pc, and the retirement-counter reads that make `should_inc_minstret` fire.

Both are parameterized by state, pc, and the fetched bytes, so they are target-independent.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated fetch/decode platform bundle for the body instruction at `pc`, stated about the
post-increment state `tryStepControlFlowAfterIncrement state` the generated `try_step` fetches from. -/
def StepPlatform (state : State) (pc : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (mseccfgBits : BitVec 64) : Prop :=
  FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc ∧
  FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc ∧
  FetchBytesAt (tryStepControlFlowAfterIncrement state) pc b0 b1 b2 b3 ∧
  InterruptDisabled (tryStepControlFlowAfterIncrement state) ∧
  LandingPadNotExpected (tryStepControlFlowAfterIncrement state) ∧
  (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine ∧
  (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits
/-- The retirement-counter reads about the pre-step state (`minstret` present, `mcountinhibit` /
`minstretcfg` configured so `should_inc_minstret` fires, hart active). -/
def StepCounters (state : State) (retired : BitVec 64) (inhibit : BitVec 32)
    (config : BitVec 64) : Prop :=
  state.regs.get? hart_state = some (.HART_ACTIVE ()) ∧
  state.regs.get? mcountinhibit = some inhibit ∧
  state.regs.get? minstretcfg = some config ∧
  _get_Counterin_IR inhibit = 0#1 ∧
  _get_CountSmcntrpmf_MINH config = 0#1 ∧
  state.regs.get? minstret = some retired

end BinaryFv.RiscV
