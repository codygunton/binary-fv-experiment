import BinaryFv.RiscV.Elfling.Boundary

/-!
# Row A vertical tests for the checked-edge boundary layer

Definitional checks on `CallSite` / `ExitBoundary` / `ScopedTrace` that the plan's Row A vertical
tests call for. They hold at the boundary layer's own abstraction (no Sail runner), so a regression
in the boundary definitions fails them.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary.Elfling

/-- **An allocator/accessor call returns to the checked continuation.** A valid `CallSite` enters the
callee at the callee's own entry pc and resumes at the fall-through `source + 4` — exactly the
continuation the emitted CFG pins, never a chosen one. -/
theorem callSite_resumes_at_checked_continuation
    {cs : CallSite} {inst callee : FunctionInstance} (h : cs.validFor inst callee) :
    cs.returnPc = cs.source + 4 ∧ callee.entryPc = cs.calleeEntry :=
  ⟨h.1, h.2.2.1⟩

/-- **The full wrapper-to-call-to-return composition names both transfer instructions.** A
`ScopedTrace.callStep` retires the call at `callPc`, consumes the callee's summary through its
return, and resumes at the checked continuation `returnPc` (in region) — so a single scoped step
carries both control transfers of a call and its continuation. -/
theorem scopedTrace_callStep_composes
    {region exit : BitVec 64 → Prop} {childSummary : Nat → State → State → Prop}
    {fromStep used count : Nat} {callPc returnPc : BitVec 64} {s s' s'' : State}
    (hpc : s.regs.get? PC = some callPc) (hregion : region callPc) (hnotExit : ¬ exit callPc)
    (hsummary : childSummary fromStep s s') (hresume : s'.regs.get? PC = some returnPc)
    (hresumeRegion : region returnPc)
    (hrest : ScopedTrace region exit childSummary (fromStep + used) count s' s'') :
    ScopedTrace region exit childSummary fromStep (used + count) s s'' :=
  ScopedTrace.callStep fromStep used count callPc returnPc s s' s''
    hpc hregion hnotExit hsummary hresume hresumeRegion hrest

/-- **A mutated return edge fails validation.** An `ExitBoundary.return_` claimed at a pc the
generator did not flag as an exit is rejected: a return may only be claimed at a real generated exit
pc. -/
theorem returnBoundary_at_nonExit_fails
    {inst : FunctionInstance} {source : Nat} (h : source ∉ inst.exitPcs) :
    ¬ (ExitBoundary.return_ source).validFor inst := by
  simpa [ExitBoundary.validFor, FunctionInstance.isExit] using h

/-- **A direct exit that stays inside the occupancy fails validation.** An `ExitBoundary.direct` whose
target is still owned by the occurrence is not a genuine occupancy-crossing exit. -/
theorem directBoundary_into_region_fails
    {inst : FunctionInstance} {source target : Nat}
    (h : inst.containsAddress target = true) :
    ¬ (ExitBoundary.direct source target).validFor inst := by
  intro hv
  simp only [ExitBoundary.validFor] at hv
  exact absurd hv.2.2 (by simp [h])

end BinaryFv.RiscV.Elfling
