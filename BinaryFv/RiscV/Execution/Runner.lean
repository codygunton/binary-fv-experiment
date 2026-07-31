import BinaryFv.RiscV.Model.State

/-!
# The sentinel runner

Runs generated Sail `try_step` calls until the return sentinel is reached, or fuel runs out. The
sentinel is a parameter, so this is target-independent.
-/

namespace BinaryFv.RiscV

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- Run only generated Sail `try_step` calls until the direct-call return sentinel is reached. -/
def runToSentinel (sentinel : BitVec 64) : Nat → Nat → SailM Nat
  | 0, _ => throw Sail.Error.Unreachable
  | fuel + 1, steps => do
    if (← readReg PC) == sentinel then
      pure steps
    else
      let waiting ← try_step steps false
      if waiting then throw Sail.Error.Unreachable
      else runToSentinel sentinel fuel (steps + 1)

/-- How a sentinel run ended, kept *distinct* so the caller can classify the outcomes with different
`ExecutionError`s rather than collapsing them into a single rejection: the sentinel PC was reached
after `steps` retirements; the machine stalled (`try_step` reported it was waiting, e.g. a `wfi` with
nothing to retire); or the fuel budget was exhausted before either. A genuine fault inside `try_step`
still propagates as a `SailM` error and is classified by the caller as a trap. -/
inductive SentinelOutcome where
  | reached (steps : Nat)
  | trapped
  | exhausted
  deriving Repr, DecidableEq, Inhabited

/-- The outcome-returning sentinel runner. Same stepping as `runToSentinel`, but instead of throwing
`Unreachable` for both a stall and fuel exhaustion, it returns a distinct `SentinelOutcome` so the
caller keeps trap, stall, and fuel exhaustion apart. -/
def runToOutcome (sentinel : BitVec 64) : Nat → Nat → SailM SentinelOutcome
  | 0, _ => pure .exhausted
  | fuel + 1, steps => do
    if (← readReg PC) == sentinel then
      pure (.reached steps)
    else
      let waiting ← try_step steps false
      if waiting then pure .trapped
      else runToOutcome sentinel fuel (steps + 1)

end BinaryFv.RiscV
