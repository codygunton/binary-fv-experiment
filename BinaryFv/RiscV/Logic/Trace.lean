import BinaryFv.RiscV.Logic.Framing

/-!
# Multi-step execution traces over `try_step`

This module lifts the per-instruction `Runs (try_step k false) · · false` contracts into a
multi-step relation `Trace fromStep count before after`, meaning `count` consecutive `try_step`s
numbered `fromStep … fromStep + count - 1` each retire normally (return `false`) and take the
machine from `before` to `after`.

The algebraic lemmas here (`Trace.one`, `Trace.append`, `Trace.snoc`, `Trace.iterate`) are the
combinators used to chain single-instruction contracts into straight-line runs and loops.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- `Trace fromStep count before after` records that `count` consecutive `try_step`s, numbered
`fromStep … fromStep + count - 1`, each retire normally (return `false`) and carry the machine from
`before` to `after`. -/
inductive Trace : Nat → Nat → State → State → Prop where
  | refl (fromStep : Nat) (s : State) : Trace fromStep 0 s s
  | step (fromStep count : Nat) (s s' s'' : State)
      (hstep : Runs (try_step fromStep false) s s' false)
      (hrest : Trace (fromStep + 1) count s' s'') : Trace fromStep (count + 1) s s''

/-- A single retiring `try_step` is a length-one trace. -/
theorem Trace.one (k : Nat) (s s' : State) (h : Runs (try_step k false) s s' false) :
    Trace k 1 s s' :=
  Trace.step k 0 s s' s' h (Trace.refl (k + 1) s')

/-- Sequencing: an `n`-step trace from `s` followed by an `m`-step trace picking up at step number
`a + n` composes into an `n + m`-step trace. -/
theorem Trace.append {a n m : Nat} {s s' s'' : State}
    (h1 : Trace a n s s') (h2 : Trace (a + n) m s' s'') : Trace a (n + m) s s'' := by
  induction h1 generalizing m s'' with
  | refl fromStep t => simpa using h2
  | step fromStep count u u' u'' hstep hrest ih =>
      have h2' : Trace (fromStep + 1 + count) m u'' s'' := by
        have harith : fromStep + (count + 1) = fromStep + 1 + count := by omega
        rwa [harith] at h2
      have hrec : Trace (fromStep + 1) (count + m) u' s'' := ih h2'
      have hcount : count + 1 + m = count + m + 1 := by omega
      rw [hcount]
      exact Trace.step fromStep (count + m) u u' s'' hstep hrec

/-- Extend a trace by one retiring `try_step` at the end (step number `a + n`). -/
theorem Trace.snoc {a n : Nat} {s s' s'' : State}
    (h1 : Trace a n s s') (h2 : Runs (try_step (a + n) false) s' s'' false) :
    Trace a (n + 1) s s'' :=
  Trace.append h1 (Trace.one (a + n) s' s'' h2)

/-- Loop iteration: if each of `N` iterations is a length-`L` trace starting at the appropriate step
number `start + i * L`, then the whole loop is a length-`N * L` trace. -/
theorem Trace.iterate (L N start : Nat) (f : Nat → State)
    (h : ∀ i, i < N → Trace (start + i * L) L (f i) (f (i + 1))) :
    Trace start (N * L) (f 0) (f N) := by
  induction N with
  | zero => simpa using Trace.refl start (f 0)
  | succ k ih =>
      have hprev : Trace start (k * L) (f 0) (f k) := ih (fun i hi => h i (by omega))
      have hlast : Trace (start + k * L) L (f k) (f (k + 1)) := h k (by omega)
      rw [Nat.succ_mul]
      exact Trace.append hprev hlast

end BinaryFv.RiscV
