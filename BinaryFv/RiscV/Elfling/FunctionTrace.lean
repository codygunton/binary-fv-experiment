import BinaryFv.RiscV.Logic.SentinelTrace
import BinaryFv.Binary.Elfling

/-!
# Traces confined to an Elfling function instance

A function instance is the static description of one compiled appearance of a source function.
`FunctionTrace` is dynamic: it relates the machine state before one execution of that function instance to
the state where execution reaches one of its exits. It repeatedly runs `try_step`, requires every
retired PC to belong to the supplied address set, and records the exact number of retired
instructions.

Two design points carry weight.

*Regions are a predicate, not a symbol range.* The address set arrives as `BitVec 64 → Prop`, the
same shape `AbstractPlatform` already uses for a function's fetch addresses. It is produced from an
function instance's possibly discontiguous `regions`, so a fragmented function instance is the ordinary case and a
contiguous one is just the degenerate function instance.

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

/-- The address set of an Elfling function instance's regions, as a fetch-address predicate.

This is the only place a function instance's addresses enter the execution layer, and it is deliberately a
`Prop` so that a handwritten contract never has to name one. -/
def RegionPcs (regions : Array AddressRange) (pc : BitVec 64) : Prop :=
  ∃ range ∈ regions, range.start ≤ pc.toNat ∧ pc.toNat < range.stop

/-- A decidable range-array containment check discharges the corresponding address-set inclusion.

This is the bridge that lets the composition's geometry side conditions be *checked* on the generated
program rather than assumed: `Program.rangesSubsume` is a `Bool` a kernel evaluation settles, and
this turns it into the `∀ pc` inclusion the trace lemmas consume. -/
theorem RegionPcs.of_rangesSubsume {outer inner : Array AddressRange}
    (h : BinaryFv.Binary.Elfling.Program.rangesSubsume outer inner = true) {pc : BitVec 64}
    (hpc : RegionPcs inner pc) : RegionPcs outer pc := by
  obtain ⟨range, hrange, hlo, hhi⟩ := hpc
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hrange
  have hcov := (Array.all_eq_true.mp h) i hi
  rw [hget] at hcov
  obtain ⟨j, hj, hsub⟩ := Array.any_eq_true.mp hcov
  have hsub' : outer[j].start ≤ range.start ∧ range.stop ≤ outer[j].stop := of_decide_eq_true hsub
  exact ⟨outer[j], Array.mem_iff_getElem.mpr ⟨j, hj, rfl⟩,
    Nat.le_trans hsub'.1 hlo, Nat.lt_of_lt_of_le hhi hsub'.2⟩

/-- Appending range arrays is union on the address sets. -/
theorem RegionPcs.append_iff {a b : Array AddressRange} {pc : BitVec 64} :
    RegionPcs (a ++ b) pc ↔ RegionPcs a pc ∨ RegionPcs b pc := by
  constructor
  · rintro ⟨range, hrange, hlo, hhi⟩
    rcases Array.mem_append.mp hrange with h | h
    · exact Or.inl ⟨range, h, hlo, hhi⟩
    · exact Or.inr ⟨range, h, hlo, hhi⟩
  · rintro (⟨range, hrange, hlo, hhi⟩ | ⟨range, hrange, hlo, hhi⟩)
    · exact ⟨range, Array.mem_append.mpr (Or.inl hrange), hlo, hhi⟩
    · exact ⟨range, Array.mem_append.mpr (Or.inr hrange), hlo, hhi⟩

/-- `RegionPcs` is exactly the decidable membership check on the same ranges. -/
theorem RegionPcs.iff_inRanges {ranges : Array AddressRange} {pc : BitVec 64} :
    RegionPcs ranges pc ↔ BinaryFv.Binary.Elfling.Program.inRanges ranges pc.toNat = true := by
  constructor
  · rintro ⟨range, hrange, hlo, hhi⟩
    obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hrange
    exact Array.any_eq_true.mpr ⟨i, hi, by rw [hget]; exact decide_eq_true ⟨hlo, hhi⟩⟩
  · intro h
    obtain ⟨i, hi, hin⟩ := Array.any_eq_true.mp h
    exact ⟨ranges[i], Array.mem_iff_getElem.mpr ⟨i, hi, rfl⟩,
      (of_decide_eq_true hin).1, (of_decide_eq_true hin).2⟩

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

/-- Sequencing within one function instance: a run that stops at an intermediate exit set `mid` continues as
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

/-- A confined run stays confined in any larger address set. This is what lets a callee's own
confined run be read as a run inside the caller's execution extent, which is the only honest reading:
the callee's instructions are not the caller's, but they *are* inside the code the caller reaches.

It weakens only the confinement, never the exit set or the step count, so nothing about *where the
run stopped* or *how long it took* is relaxed. -/
theorem mono_region {region region' exit : BitVec 64 → Prop} {fromStep count : Nat} {s s' : State}
    (hsub : ∀ pc, region pc → region' pc)
    (h : FunctionTrace region exit fromStep count s s') :
    FunctionTrace region' exit fromStep count s s' := by
  induction h with
  | exitAt fromStep t pc hpc hexit => exact FunctionTrace.exitAt fromStep t pc hpc hexit
  | step fromStep count pc u u' u'' hpc hregion hnotExit hstep _ ih =>
      exact FunctionTrace.step fromStep count pc u u' u'' hpc (hsub pc hregion) hnotExit hstep ih

/--
Sequencing a *nested* run into an enclosing one: `append` for the case where the first run is
confined to a smaller address set with its own stopping set.

This is `append` with its side condition localized. `append` demands `exit ⊆ mid` globally, which is
the right condition when both runs belong to the same function instance but is far too strong across a
boundary: a callee's exits are its own returns, not its caller's. What actually has to hold is that
the *inner* run cannot step past one of the outer run's exits — and the inner run only ever occupies
`inner`, so it suffices that every outer exit lying inside `inner` is already an inner stopping
point. Where the two address sets are disjoint (a separately emitted callee) that is vacuous; where
they are nested (an inlined child) it is a real, decidable check on the generated exit inventories.

Dropping it would be unsound in exactly the way `append`'s condition guards against: the inner run
could step straight through the outer function instance's return and the concatenation would claim a
confinement it never had.
-/
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
A `FunctionTrace` that genuinely enters the function instance at a generated entry.

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

/-- Entering carries over to a larger confinement, since the entry pc is still in region. -/
theorem mono_region {region region' exit : BitVec 64 → Prop} {entry : BitVec 64}
    {fromStep count : Nat} {s s' : State}
    (hsub : ∀ pc, region pc → region' pc)
    (h : EnteredFunctionTrace region exit entry fromStep count s s') :
    EnteredFunctionTrace region' exit entry fromStep count s s' :=
  { startsAtEntry := h.startsAtEntry
    entryInRegion := hsub entry h.entryInRegion
    entryNotExit := h.entryNotExit
    trace := h.trace.mono_region hsub }

end EnteredFunctionTrace

end BinaryFv.RiscV.Elfling
