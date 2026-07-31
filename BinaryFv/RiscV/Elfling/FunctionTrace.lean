import BinaryFv.RiscV.Logic.SentinelTrace
import BinaryFv.Binary.Elfling

/-!
# Traces confined to an Elfling occurrence

`FunctionTrace` is `try_step` execution that stays inside one occurrence's instruction regions until
it reaches one of that occurrence's generated exits.

Two design points carry weight.

*Regions are a predicate, not a symbol range.* The address set arrives as `BitVec 64 → Prop`, the
same shape `AbstractPlatform` already uses for a function's fetch addresses. It is produced from an
occurrence's possibly discontiguous `regions`, so a fragmented occurrence is the ordinary case and a
contiguous one is just the degenerate instance.

*A bare `FunctionTrace` can be empty.* Mirroring `TraceToSentinel.done`, `exitAt` proves nothing when
the machine already sits on an exit. `EnteredFunctionTrace` is the form contracts must use: it pins
the start to a generated entry that is itself not an exit, which forces at least one retired step.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary
open BinaryFv.RiscV

/-- The address set of an Elfling occurrence's regions, as a fetch-address predicate.

This is the only place an occurrence's addresses enter the execution layer, and it is deliberately a
`Prop` so that a handwritten contract never has to name one. -/
def RegionPcs (regions : Array AddressRange) (pc : BitVec 64) : Prop :=
  ∃ range ∈ regions, range.start ≤ pc.toNat ∧ pc.toNat < range.stop

/-- `try_step` execution confined to `region`, running until the pc satisfies `exit`.

`count` is the exact number of retired steps and `fromStep` the starting step number, matching
`Trace`'s discipline so the two compose. -/
inductive FunctionTrace (region exit : BitVec 64 → Prop) :
    Nat → Nat → State → State → Prop where
  /-- Termination: the machine sits on a generated exit. -/
  | exitAt (fromStep : Nat) (s : State) (pc : BitVec 64)
      (hpc : s.regs.get? PC = some pc)
      (hexit : exit pc) :
      FunctionTrace region exit fromStep 0 s s
  /-- One retired step from an in-region, non-exit pc. -/
  | step (fromStep count : Nat) (pc : BitVec 64) (s s' s'' : State)
      (hpc : s.regs.get? PC = some pc)
      (hregion : region pc)
      (hnotExit : ¬ exit pc)
      (hstep : Runs (try_step fromStep false) s s' false)
      (hrest : FunctionTrace region exit (fromStep + 1) count s' s'') :
      FunctionTrace region exit fromStep (count + 1) s s''

namespace FunctionTrace

/-- Every `FunctionTrace` is in particular a `Trace`, so all of `Trace`'s combinators apply to the
underlying step sequence. -/
theorem toTrace {region exit : BitVec 64 → Prop} {fromStep count : Nat} {s s' : State}
    (h : FunctionTrace region exit fromStep count s s') : Trace fromStep count s s' := by
  induction h with
  | exitAt fromStep t _ _ _ => exact Trace.refl fromStep t
  | step fromStep count _ u u' u'' _ _ _ hstep _ ih => exact Trace.step fromStep count u u' u'' hstep ih

/-- The final state of a `FunctionTrace` sits on an exit. -/
theorem final_at_exit {region exit : BitVec 64 → Prop} {fromStep count : Nat} {s s' : State}
    (h : FunctionTrace region exit fromStep count s s') :
    ∃ pc, s'.regs.get? PC = some pc ∧ exit pc := by
  induction h with
  | exitAt _ _ pc hpc hexit => exact ⟨pc, hpc, hexit⟩
  | step _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- Sequencing within one occurrence: a run that stops at an intermediate exit set `mid` continues as
a `FunctionTrace` to the real exits. The step numbering follows `Trace.append`.

`exitSubsetMid` is what makes this sound rather than convenient: the intermediate stopping set must
already contain every real exit, otherwise the first run could have stepped straight past a genuine
exit and the concatenation would claim a confinement it never had. -/
theorem append {region mid exit : BitVec 64 → Prop} {a n m : Nat} {s s' s'' : State}
    (exitSubsetMid : ∀ pc, exit pc → mid pc)
    (h1 : FunctionTrace region mid a n s s')
    (h2 : FunctionTrace region exit (a + n) m s' s'') :
    FunctionTrace region exit a (n + m) s s'' := by
  induction h1 generalizing m s'' with
  | exitAt fromStep t _ _ _ => simpa using h2
  | step fromStep count pc u u' u'' hpc hregion hnotExit hstep _ ih =>
      have h2' : FunctionTrace region exit (fromStep + 1 + count) m u'' s'' := by
        have harith : fromStep + (count + 1) = fromStep + 1 + count := by omega
        rwa [harith] at h2
      have hrec : FunctionTrace region exit (fromStep + 1) (count + m) u' s'' := ih h2'
      have hcount : count + 1 + m = count + m + 1 := by omega
      rw [hcount]
      exact FunctionTrace.step fromStep (count + m) pc u u' s'' hpc hregion
        (fun hx => hnotExit (exitSubsetMid pc hx)) hstep hrec

/-- A trace remains valid when its confinement region is enlarged. -/
theorem mono_region {region region' exit : BitVec 64 → Prop} {fromStep count : Nat} {s s' : State}
    (hsub : ∀ pc, region pc → region' pc)
    (h : FunctionTrace region exit fromStep count s s') :
    FunctionTrace region' exit fromStep count s s' := by
  induction h with
  | exitAt fromStep t pc hpc hexit => exact FunctionTrace.exitAt fromStep t pc hpc hexit
  | step fromStep count pc u u' u'' hpc hregion hnotExit hstep _ ih =>
      exact FunctionTrace.step fromStep count pc u u' u'' hpc (hsub pc hregion) hnotExit hstep ih

/-- Append a nested trace when every outer exit inside the inner region is already an inner stop. -/
theorem append_within {inner region mid exit : BitVec 64 → Prop} {a n m : Nat} {s s' s'' : State}
    (innerSubset : ∀ pc, inner pc → region pc)
    (outerExitsStopInner : ∀ pc, inner pc → exit pc → mid pc)
    (h1 : FunctionTrace inner mid a n s s')
    (h2 : FunctionTrace region exit (a + n) m s' s'') :
    FunctionTrace region exit a (n + m) s s'' := by
  induction h1 generalizing m s'' with
  | exitAt fromStep t _ _ _ => simpa using h2
  | step fromStep count pc u u' u'' hpc hregion hnotExit hstep _ ih =>
      have h2' : FunctionTrace region exit (fromStep + 1 + count) m u'' s'' := by
        have harith : fromStep + (count + 1) = fromStep + 1 + count := by omega
        rwa [harith] at h2
      have hrec : FunctionTrace region exit (fromStep + 1) (count + m) u' s'' := ih h2'
      have hcount : count + 1 + m = count + m + 1 := by omega
      rw [hcount]
      exact FunctionTrace.step fromStep (count + m) pc u u' s'' hpc (innerSubset pc hregion)
        (fun hx => hnotExit (outerExitsStopInner pc hregion hx)) hstep hrec

end FunctionTrace

/--
A `FunctionTrace` that genuinely enters the occurrence at a generated entry.

This is the form a contract must use. Because `entry` is required to be in region and *not* an exit,
`FunctionTrace.exitAt` cannot apply at the start, so the run retires at least one instruction. A
zero-step trace can therefore never discharge an `Implements` obligation — which is the specific way
a Hoare-style binary contract would otherwise be vacuously true.
-/
structure EnteredFunctionTrace (region exit : BitVec 64 → Prop) (entry : BitVec 64)
    (fromStep count : Nat) (s s' : State) : Prop where
  startsAtEntry : s.regs.get? PC = some entry
  entryInRegion : region entry
  entryNotExit : ¬ exit entry
  trace : FunctionTrace region exit fromStep count s s'

namespace EnteredFunctionTrace

/-- An entered trace retires at least one instruction. -/
theorem count_pos {region exit : BitVec 64 → Prop} {entry : BitVec 64} {fromStep count : Nat}
    {s s' : State} (h : EnteredFunctionTrace region exit entry fromStep count s s') :
    0 < count := by
  obtain ⟨hstart, _, hnotExit, htrace⟩ := h
  cases htrace with
  | exitAt _ _ pc hpc hexit =>
      exfalso
      have hEq : pc = entry := by
        rw [hpc] at hstart
        exact Option.some.inj hstart
      exact hnotExit (hEq ▸ hexit)
  | step _ n _ _ _ _ _ _ _ _ _ => omega

end EnteredFunctionTrace

end BinaryFv.RiscV.Elfling
