import BinaryFv.RiscV.Step.ControlFlow
import BinaryFv.RiscV.Platform.FetchMemory
import BinaryFv.RiscV.Platform.ExecutionContext

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
abbrev StepCounters := RetirementContext

end BinaryFv.RiscV
