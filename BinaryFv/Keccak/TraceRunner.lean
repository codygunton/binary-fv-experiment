import BinaryFv.Keccak.Execution
import BinaryFv.RiscV.Trace

/-!
# Sentinel trace runner correspondence

A bundled step-trace that reaches a sentinel PC corresponds exactly to the generated
`runToSentinel` fuel-runner: the "sentinel runner that checks the sentinel before fuel
exhaustion" correspondence.
-/

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

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

theorem runToSentinel_of_traceToSentinel (sentinel : BitVec 64) :
    ∀ (count fuel steps : Nat) (s s' : State),
      TraceToSentinel sentinel steps count s s' → count < fuel →
      Runs (runToSentinel sentinel fuel steps) s s' (steps + count) := by
  intro count fuel steps s s' htrace
  induction htrace generalizing fuel with
  | done fromStep s h =>
    intro hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hread : Runs (readReg PC) s s sentinel := readReg_run s PC sentinel h
    unfold runToSentinel
    refine Runs.bind hread ?_
    simp only [beq_self_eq_true, if_true]
    rfl
  | step fromStep count v s s' s'' hpc hne hstep hrest ih =>
    intro hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hread : Runs (readReg PC) s s v := readReg_run s PC v hpc
    have hvne : (v == sentinel) = false := beq_eq_false_iff_ne.mpr hne
    unfold runToSentinel
    refine Runs.bind hread ?_
    simp only [hvne, Bool.false_eq_true, if_false]
    refine Runs.bind hstep ?_
    simp only [Bool.false_eq_true, if_false]
    have harith : fromStep + (count + 1) = fromStep + 1 + count := by omega
    rw [harith]
    exact ih f (by omega)

end BinaryFv.Keccak
