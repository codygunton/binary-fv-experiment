import BinaryFv.RiscV.Logic.Trace

/-!
# Invariant-carrying loop induction over `try_step` traces

`Trace.iterate` (stage 3) chains `N` fixed-length iterations given an *explicit* state function
`f : Nat → State`.  A machine loop whose body clobbers scratch registers (memcpy's `a3`/`a4`,
memset's `a4`, xor_block's temporaries) has no convenient closed form for the intermediate state, so
this module adds the invariant-carrying variant `Trace.invariantIterate`: from a loop invariant that
each iteration advances by one length-`L` trace, it produces the whole length-`N * L` trace together
with the invariant at the end, choosing the intermediate states existentially.

This is the loop combinator used by every helper/permutation loop in the Keccak binary-compliance
proof.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- Invariant-carrying loop induction: if a loop invariant `Inv i s` (the machine is at the loop head
about to run iteration `i` in state `s`) advances by one length-`L` iteration trace for every
`i < N`, then the whole loop is a length-`N * L` trace from any `Inv 0`-state to some `Inv N`-state.
The intermediate states are chosen existentially, so the loop body may clobber scratch state with no
closed form. -/
theorem Trace.invariantIterate {L start : Nat} {Inv : Nat → State → Prop} (N : Nat)
    (adv : ∀ i s, i < N → Inv i s → ∃ s', Trace (start + i * L) L s s' ∧ Inv (i + 1) s')
    {s0 : State} (h0 : Inv 0 s0) :
    ∃ sN, Trace start (N * L) s0 sN ∧ Inv N sN := by
  induction N with
  | zero => exact ⟨s0, by simpa using Trace.refl start s0, h0⟩
  | succ k ih =>
      obtain ⟨sk, htk, hik⟩ := ih (fun i s hi hInv => adv i s (by omega) hInv)
      obtain ⟨sk1, hstep, hik1⟩ := adv k sk (by omega) hik
      exact ⟨sk1, by rw [Nat.succ_mul]; exact Trace.append htk hstep, hik1⟩

/-- After the loop, one further trace (the exit path — e.g. the not-taken loop test plus `ret`)
extends the whole run to a caller-visible end state satisfying `Post`.  The exit and end state are
chosen from the post-loop invariant. -/
theorem Trace.invariantIterate_then {L start exitLen : Nat} {Inv : Nat → State → Prop}
    {Post : State → Prop} (N : Nat)
    (adv : ∀ i s, i < N → Inv i s → ∃ s', Trace (start + i * L) L s s' ∧ Inv (i + 1) s')
    {s0 : State} (h0 : Inv 0 s0)
    (exit : ∀ s, Inv N s → ∃ sExit, Trace (start + N * L) exitLen s sExit ∧ Post sExit) :
    ∃ sExit, Trace start (N * L + exitLen) s0 sExit ∧ Post sExit := by
  obtain ⟨sN, htr, hInvN⟩ := Trace.invariantIterate N adv h0
  obtain ⟨sExit, hexit, hpost⟩ := exit sN hInvN
  exact ⟨sExit, Trace.append htr hexit, hpost⟩

end BinaryFv.RiscV
