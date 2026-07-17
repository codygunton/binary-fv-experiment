import BinaryFv.RISCV.Trace

/-!
# A small kernel-checked block-stepping tactic

`Trace.step`/`Trace.refl` (from `BinaryFv.RISCV.Trace`) already chain into a multi-step trace, but
writing the nested applications by hand is noisy for a straight-line block.  This module provides a
minimal, fully kernel-checked convenience: each `trace_step h` discharges one leading `try_step` of a
`Trace` goal using an *established* per-instruction step lemma `h`, and `trace_steps [h₀, …, hₙ]`
does the whole block.  There is no search or decision procedure — the tactic only assembles the
inductive `Trace` constructors, so every result is an ordinary proof term the kernel checks.
-/

namespace BinaryFv.RISCV

/-- Discharge one leading `try_step` of a `Trace _ (_ + 1) _ _` goal with the step lemma `h`
    (`Runs (try_step k false) s s' false`, its concrete post-state `s'` fixing the intermediate
    state), leaving the remaining `Trace` obligation. -/
macro "trace_step " h:term : tactic =>
  `(tactic| refine Trace.step _ _ _ _ _ $h ?_)

/-- Assemble a straight-line block trace from a list of established per-instruction step lemmas
    `[h₀, h₁, …]`, closing the base case by reflexivity. -/
syntax "trace_steps " "[" term,* "]" : tactic
macro_rules
  | `(tactic| trace_steps []) => `(tactic| exact Trace.refl _ _)
  | `(tactic| trace_steps [$h:term]) =>
      `(tactic| refine Trace.step _ _ _ _ _ $h ?_; exact Trace.refl _ _)
  | `(tactic| trace_steps [$h:term, $hs:term,*]) =>
      `(tactic| refine Trace.step _ _ _ _ _ $h ?_; trace_steps [$hs,*])

end BinaryFv.RISCV

/-! ### Sanity checks (private) -/
namespace BinaryFv.RISCV
open PreSail LeanRV64DExecutable.Functions Register

private example (s0 s1 s2 s3 : State)
    (h0 : Runs (try_step 0 false) s0 s1 false)
    (h1 : Runs (try_step 1 false) s1 s2 false)
    (h2 : Runs (try_step 2 false) s2 s3 false) :
    Trace 0 3 s0 s3 := by
  trace_steps [h0, h1, h2]

private example (s0 s1 : State) (h0 : Runs (try_step 0 false) s0 s1 false) :
    Trace 0 1 s0 s1 := by
  trace_step h0
  exact Trace.refl _ _

end BinaryFv.RISCV
