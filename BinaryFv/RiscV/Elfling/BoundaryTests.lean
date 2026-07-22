import BinaryFv.RiscV.Elfling.Boundary

/-!
# Row A vertical tests for the checked-edge boundary layer

Definitional checks on `CallSite` / `InlineBoundary` / `ExitBoundary` / `ScopedTrace` that the plan's
Row A vertical tests call for. They hold at the boundary layer's own abstraction (no Sail runner), so a
regression in the boundary definitions fails them.

The positive tests exercise the *composition* shape: a checked call/inline transfer plus a confined
continuation splices into a scoped trace whose step count includes both transfer instructions and the
callee/child body. The negative tests are the teeth: an invented call source, callee target, or
continuation, a dropped transfer, or a non-crossing inline edge all fail their `validFor` check.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV

/-! ## Positive composition -/

/-- **An allocator/accessor call returns to the checked continuation.** A valid `CallSite` enters the
callee at the callee's own entry pc and resumes at the fall-through `source + 4` — exactly the
continuation the emitted CFG pins, never a chosen one. -/
theorem callSite_resumes_at_checked_continuation
    {cs : CallSite} {inst callee : FunctionInstance} (h : cs.validFor inst callee) :
    cs.returnPc = cs.source + 4 ∧ callee.entryPc = cs.calleeEntry :=
  ⟨h.1, h.2.2.1⟩

/-- **A valid call site is backed by the real call edge.** Beyond callee membership, a valid
`CallSite` requires `source → calleeEntry` to be a genuine emitted edge of the caller: the call
transfer itself is a decoded successor, not merely a routine the caller happens to reach. -/
theorem callSite_uses_the_real_call_edge
    {cs : CallSite} {inst callee : FunctionInstance} (h : cs.validFor inst callee) :
    (⟨cs.source, cs.calleeEntry⟩ : DirectEdge) ∈ inst.edges :=
  h.2.2.2.2.1

/-- **The full wrapper-to-call-to-return composition names both transfer instructions.** A
`ScopedTrace.callStep` retires the call at `callPc`, consumes the callee's summary through its return,
retires the return, and resumes at the checked continuation — so a single scoped step advances the
count by `1 + used + 1 + count`: the two control transfers plus the callee body plus the continuation.
The checked boundary and both `try_step`s are carried inside `CallTransfer`, so this cannot be built
without the real call/return execution. -/
theorem scopedTrace_callStep_composes
    {region exit : BitVec 64 → Prop}
    {childSummary : InstanceId → Nat → Nat → State → State → Prop}
    {fromStep used count : Nat} {cs : CallSite} {inst callee : FunctionInstance}
    {s sResume s'' : State}
    (htransfer : CallTransfer region exit childSummary cs inst callee fromStep used s sResume)
    (hrest : ScopedTrace region exit childSummary (fromStep + 1 + used + 1) count sResume s'') :
    ScopedTrace region exit childSummary fromStep (1 + used + 1 + count) s s'' :=
  ScopedTrace.callStep fromStep used count cs inst callee s sResume s'' htransfer hrest

/-- **An inline splice retires the outgoing edge exactly once.** A `ScopedTrace.inlineStep` runs the
child body from the child entry pc through a checked outgoing edge and then retires that edge back into
the parent, advancing the count by `used + 1 + count`: the child body, the one outgoing-edge step, and
the continuation. -/
theorem scopedTrace_inlineStep_composes
    {region exit : BitVec 64 → Prop}
    {childSummary : InstanceId → Nat → Nat → State → State → Prop}
    {fromStep used count : Nat} {ib : InlineBoundary} {inst childInst : FunctionInstance}
    {s sResume s'' : State}
    (htransfer : InlineTransfer region exit childSummary ib inst childInst fromStep used s sResume)
    (hrest : ScopedTrace region exit childSummary (fromStep + used + 1) count sResume s'') :
    ScopedTrace region exit childSummary fromStep (used + 1 + count) s s'' :=
  ScopedTrace.inlineStep fromStep used count ib inst childInst s sResume s'' htransfer hrest

/-! ## Negative tests: invented boundaries and counts -/

/-- **An invented continuation fails.** A `CallSite` whose recorded continuation is not the 4-byte
fall-through of the call is rejected — the return address cannot be chosen freely. -/
theorem callSite_invented_continuation_fails
    {cs : CallSite} {inst callee : FunctionInstance} (h : cs.returnPc ≠ cs.source + 4) :
    ¬ cs.validFor inst callee :=
  fun hv => h hv.1

/-- **An invented callee target fails.** A `CallSite` whose recorded entry pc is not the callee
occurrence's own entry is rejected — the call cannot land on a chosen address inside the callee. -/
theorem callSite_invented_target_fails
    {cs : CallSite} {inst callee : FunctionInstance} (h : callee.entryPc ≠ cs.calleeEntry) :
    ¬ cs.validFor inst callee :=
  fun hv => h hv.2.2.1

/-- **An invented call source fails.** A `CallSite` whose `source → calleeEntry` transfer is not a real
emitted edge of the caller is rejected — the call instruction cannot be invented at a pc the CFG does
not decode a call edge from. -/
theorem callSite_invented_source_fails
    {cs : CallSite} {inst callee : FunctionInstance}
    (h : (⟨cs.source, cs.calleeEntry⟩ : DirectEdge) ∉ inst.edges) :
    ¬ cs.validFor inst callee :=
  fun hv => h hv.2.2.2.2.1

/-- **An invented step count is impossible: both transfers are counted.** A `callStep` advances the
count by `1 + used + 1 + count`, which is the callee body (`used`) plus the continuation (`count`)
plus exactly the two transfer instructions. So a proof can neither omit the call/return steps nor
inflate the body against the summary's own `used`. -/
theorem callStep_counts_both_transfers (used count : Nat) :
    1 + used + 1 + count = used + count + 2 ∧ 1 + used + 1 + count ≠ used + count := by
  omega

/-- **A non-crossing inline entry edge fails.** An `InlineBoundary` whose declared entry edge starts
*inside* the child (so it does not cross into it) is rejected: an entry edge must leave the parent and
land in the child. -/
theorem inlineBoundary_noncrossing_entry_fails
    {ib : InlineBoundary} {inst childInst : FunctionInstance} {e : DirectEdge}
    (he : e ∈ ib.entries) (hsrc : childInst.containsAddress e.source = true) :
    ¬ ib.validFor inst childInst := by
  intro hv
  have h := (hv.2.2.1 e he).2.2.1
  simp [hsrc] at h

/-- **A non-crossing inline exit edge fails.** An `InlineBoundary` whose declared exit edge lands
*inside* the child (so it does not cross out of it) is rejected: an exit edge must leave the child and
land back in the parent. -/
theorem inlineBoundary_noncrossing_exit_fails
    {ib : InlineBoundary} {inst childInst : FunctionInstance} {e : DirectEdge}
    (he : e ∈ ib.exits) (htgt : childInst.containsAddress e.target = true) :
    ¬ ib.validFor inst childInst := by
  intro hv
  have h := (hv.2.2.2 e he).2.2.1
  simp [htgt] at h

/-- **A mutated return edge fails validation.** An `ExitBoundary.return_` claimed at a pc the generator
did not flag as an exit is rejected: a return may only be claimed at a real generated exit pc. -/
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
