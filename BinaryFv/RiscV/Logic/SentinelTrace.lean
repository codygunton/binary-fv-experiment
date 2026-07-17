import BinaryFv.RiscV.Logic.Trace

/-!
# Traces that run to a sentinel PC

`TraceToSentinel` bundles a step-trace with the invariant that the PC is defined and *not* the
sentinel at every non-final state, and equals the sentinel at the final one.

This is deliberately independent of the executable runner: `Logic` states what a sentinel-terminated
trace is, `Execution.Runner` provides the fuel-driven runner, and `Proof.RunnerCorrespondence`
relates them.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- A bundled trace that runs `try_step`s until the machine's PC equals `sentinel`, carrying the
invariant that PC is defined and not the sentinel at every non-final state. -/
inductive TraceToSentinel (sentinel : BitVec 64) : Nat → Nat → State → State → Prop where
  | done (fromStep : Nat) (s : State) (h : s.regs.get? PC = some sentinel) :
      TraceToSentinel sentinel fromStep 0 s s
  | step (fromStep count : Nat) (v : BitVec 64) (s s' s'' : State)
      (hpc : s.regs.get? PC = some v)
      (hne : v ≠ sentinel)
      (hstep : Runs (try_step fromStep false) s s' false)
      (hrest : TraceToSentinel sentinel (fromStep + 1) count s' s'') :
      TraceToSentinel sentinel fromStep (count + 1) s s''

end BinaryFv.RiscV
