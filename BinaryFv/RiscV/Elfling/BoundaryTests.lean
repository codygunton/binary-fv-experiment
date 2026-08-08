import BinaryFv.RiscV.Elfling.Boundary

/-!
# Examples and regression tests for checked boundaries

These small theorems show what the boundary definitions accept and reject without requiring the full
Zesu program. The positive cases account for calls, returns, and inline exits. The negative cases
mutate one edge, continuation, or step count at a time and prove that the corresponding validity
predicate becomes false.
Definitional checks on `CallSite` / `InlineBoundary` / `ExitBoundary` / `ScopedTrace` that the plan's
The function-instance contract tests require. They hold at the boundary layer's own abstraction (no Sail runner), so a
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
    {cs : CallSite} {program : Program} {functionInstance callee : FunctionInstance}
    (h : cs.validFor program functionInstance callee) :
    cs.returnPc = cs.source + 4 ∧ callee.entryPc = cs.calleeEntry :=
  ⟨h.1, h.2.2.1⟩

/-- **A valid call site is backed by the real call edge.** Beyond callee membership, a valid
`CallSite` requires `source → calleeEntry` to be a genuine emitted edge of the caller: the call
transfer itself is a decoded successor, not merely a source function the caller happens to reach. -/
theorem callSite_uses_the_real_call_edge
    {cs : CallSite} {program : Program} {functionInstance callee : FunctionInstance}
    (h : cs.validFor program functionInstance callee) :
    programContainsEdge program ⟨cs.source, cs.calleeEntry⟩ = true :=
  h.2.2.2.2.1

/-- **The full wrapper-to-call-to-return composition names both transfer instructions.** A
`ScopedTrace.callStep` retires the call at `callPc`, consumes the callee's summary through its return,
retires the return, and resumes at the checked continuation — so a single scoped step advances the
count by `1 + used + 1 + count`: the two control transfers plus the callee body plus the continuation.
The checked boundary and both `try_step`s are carried inside `CallTransfer`, so this cannot be built
without the real call/return execution. -/
theorem scopedTrace_callStep_composes
    {region exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {fromStep used count : Nat} {cs : CallSite} {program : Program}
    {functionInstance callee : FunctionInstance}
    {s sResume s'' : State}
    (htransfer : CallTransfer region exit childSummary cs program functionInstance callee
      fromStep used s sResume)
    (hrest : ScopedTrace region exit childSummary (fromStep + 1 + used + 1) count sResume s'') :
    ScopedTrace region exit childSummary fromStep (1 + used + 1 + count) s s'' :=
  ScopedTrace.callStep fromStep used count cs program functionInstance callee s sResume s''
    htransfer hrest

/-- **An inline splice retires the outgoing edge exactly once.** A `ScopedTrace.inlineStep` runs the
child body from the child entry pc through a checked outgoing edge and then retires that edge back into
the parent, advancing the count by `used + 1 + count`: the child body, the one outgoing-edge step, and
the continuation. -/
theorem scopedTrace_inlineStep_composes
    {region exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {fromStep used count : Nat} {ib : InlineBoundary} {program : Program}
    {functionInstance childFunctionInstance : FunctionInstance}
    {s sResume s'' : State}
    (htransfer : InlineTransfer region exit childSummary ib program functionInstance
      childFunctionInstance fromStep used s sResume)
    (hrest : ScopedTrace region exit childSummary (fromStep + used + 1) count sResume s'') :
    ScopedTrace region exit childSummary fromStep (used + 1 + count) s s'' :=
  ScopedTrace.inlineStep fromStep used count ib program functionInstance childFunctionInstance
    s sResume s'' htransfer hrest

/-- **A child body does not silently retire its outgoing instruction.** `childBody` consumes exactly
the child's reported steps and leaves the continuation at the child's final state. The continuation
must account for the outgoing instruction separately, which is essential for adjacent inline
segments whose branch may either exit the parent or enter the next child segment. -/
theorem scopedTrace_childBody_composes
    {region exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {fromStep used count : Nat} {child : FunctionInstanceId} {s sChild s'' : State}
    (body : childSummary child fromStep used s sChild)
    (rest : ScopedTrace region exit childSummary (fromStep + used) count sChild s'') :
    ScopedTrace region exit childSummary fromStep (used + count) s s'' :=
  ScopedTrace.childBody fromStep used count child s sChild s'' body rest

/-- **A call that leaves an inline child remains two real transfers.** The child summary stops on the
call instruction, then `ScopedTrace.inlineCallStep` retires the call, consumes the callee body,
retires its return, and continues outside the inline child. -/
theorem scopedTrace_inlineCallStep_composes
    {region exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {fromStep childUsed calleeUsed count : Nat}
    {boundary : InlineCallBoundary} {program : Program}
    {functionInstance childFunctionInstance callee : FunctionInstance}
    {s sResume s'' : State}
    (htransfer : InlineCallTransfer region exit childSummary boundary program functionInstance
      childFunctionInstance callee fromStep childUsed calleeUsed s sResume)
    (hrest : ScopedTrace region exit childSummary
      (fromStep + childUsed + 1 + calleeUsed + 1) count sResume s'') :
    ScopedTrace region exit childSummary fromStep
      (childUsed + 1 + calleeUsed + 1 + count) s s'' :=
  ScopedTrace.inlineCallStep fromStep childUsed calleeUsed count boundary program
    functionInstance childFunctionInstance callee s sResume s'' htransfer hrest

/-! ## Negative tests: invented boundaries and counts -/

/-- **An invented continuation fails.** A `CallSite` whose recorded continuation is not the 4-byte
fall-through of the call is rejected — the return address cannot be chosen freely. -/
theorem callSite_invented_continuation_fails
    {cs : CallSite} {program : Program} {functionInstance callee : FunctionInstance}
    (h : cs.returnPc ≠ cs.source + 4) :
    ¬ cs.validFor program functionInstance callee :=
  fun hv => h hv.1

/-- **An invented callee target fails.** A `CallSite` whose recorded entry pc is not the callee
function instance's own entry is rejected — the call cannot land on a chosen address inside the callee. -/
theorem callSite_invented_target_fails
    {cs : CallSite} {program : Program} {functionInstance callee : FunctionInstance}
    (h : callee.entryPc ≠ cs.calleeEntry) :
    ¬ cs.validFor program functionInstance callee :=
  fun hv => h hv.2.2.1

/-- **An invented call source fails.** A `CallSite` whose `source → calleeEntry` transfer is not a real
emitted edge of the caller is rejected — the call instruction cannot be invented at a pc the CFG does
not decode a call edge from. -/
theorem callSite_invented_source_fails
    {cs : CallSite} {program : Program} {functionInstance callee : FunctionInstance}
    (h : programContainsEdge program ⟨cs.source, cs.calleeEntry⟩ = false) :
    ¬ cs.validFor program functionInstance callee := by
  intro hv
  have edge := hv.2.2.2.2.1
  simp [h] at edge

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
    {ib : InlineBoundary} {program : Program}
    {functionInstance childFunctionInstance : FunctionInstance} {e : DirectEdge}
    (he : e ∈ ib.entries) (hsrc : childFunctionInstance.containsAddress e.source = true) :
    ¬ ib.validFor program functionInstance childFunctionInstance := by
  intro hv
  have h := (hv.2.2.1 e he).2.2.1
  simp [hsrc] at h

/-- **A non-crossing inline exit edge fails.** An `InlineBoundary` whose declared exit edge lands
*inside* the child (so it does not cross out of it) is rejected: an exit edge must leave the child and
land back in the parent. -/
theorem inlineBoundary_noncrossing_exit_fails
    {ib : InlineBoundary} {program : Program}
    {functionInstance childFunctionInstance : FunctionInstance} {e : DirectEdge}
    (he : e ∈ ib.exits) (htgt : childFunctionInstance.containsAddress e.target = true) :
    ¬ ib.validFor program functionInstance childFunctionInstance := by
  intro hv
  have h := (hv.2.2.2 e he).2.2.1
  simp [htgt] at h

/-- **A call returning inside the inline child is not an inline-child exit.** Such a call belongs to
the child's own execution and must be consumed when that child is refined. -/
theorem inlineCallBoundary_internal_return_fails
    {boundary : InlineCallBoundary} {program : Program}
    {functionInstance childFunctionInstance callee : FunctionInstance}
    (hreturn : childFunctionInstance.containsAddress boundary.call.returnPc = true) :
    ¬ boundary.validFor program functionInstance childFunctionInstance callee := by
  intro valid
  have outside := valid.2.2.2
  simp [hreturn] at outside

/-- **The call instruction of an inline-child exit must be owned by that child.** A call elsewhere
in the enclosing function cannot be relabeled as the child's outgoing transfer. -/
theorem inlineCallBoundary_external_source_fails
    {boundary : InlineCallBoundary} {program : Program}
    {functionInstance childFunctionInstance callee : FunctionInstance}
    (hsource : childFunctionInstance.containsAddress boundary.call.source = false) :
    ¬ boundary.validFor program functionInstance childFunctionInstance callee := by
  intro valid
  have inside := valid.2.2.1
  simp [hsource] at inside

/-- **A mutated return edge fails validation.** An `ExitBoundary.return_` claimed at a pc the generator
did not flag as an exit is rejected: a return may only be claimed at a real generated exit pc. -/
theorem returnBoundary_at_nonExit_fails
    {functionInstance : FunctionInstance} {source : Nat} (h : source ∉ functionInstance.exitPcs) :
    ¬ (ExitBoundary.return_ source).validFor functionInstance := by
  simpa [ExitBoundary.validFor, FunctionInstance.isExit] using h

/-- **A direct exit that stays inside the occupancy fails validation.** An `ExitBoundary.direct` whose
target is still owned by the function instance is not a genuine occupancy-crossing exit. -/
theorem directBoundary_into_region_fails
    {functionInstance : FunctionInstance} {source target : Nat}
    (h : functionInstance.containsAddress target = true) :
    ¬ (ExitBoundary.direct source target).validFor functionInstance := by
  intro hv
  simp only [ExitBoundary.validFor] at hv
  exact absurd hv.2.2 (by simp [h])

end BinaryFv.RiscV.Elfling
