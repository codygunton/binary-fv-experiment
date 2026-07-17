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

end BinaryFv.RiscV
