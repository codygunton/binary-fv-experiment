import BinaryFv.RiscV.Elfling.FunctionTrace

/-!
# Calls, inlining, and checked trace boundaries

A boundary is a control-flow edge that crosses from one function instance's owned instructions into another
function instance, or back again. The name refers to that ownership crossing; it does not mean an arbitrary
place where a trace is split.

`FunctionTrace` describes instruction-by-instruction execution inside one compiled function instance. Real
code also calls separately emitted source functions and enters regions attributed to inlined source functions.
`ScopedTrace` lets a parent use a proved summary of either kind of child while still reconstructing
one ordinary machine trace.

The generator supplies the parent and child regions, control-flow edges, calls, and exits. The
`validFor` predicates check every boundary against that data:

- a call must use a real edge to the callee's generated entry and return to the instruction after the
  call;
- an inline entry must cross from the parent into the child;
- an inline exit must cross from the child back into the parent.

Each splice also contains the actual Sail steps at the boundary. A call counts the call instruction,
the summarized callee body, and the return instruction. An inline child counts its summarized body
and the outgoing instruction. The child summary and parent arithmetic share the same `used` value,
so a proof cannot invent a convenient step count.

`SummariesCompose` is the remaining interface: it says that each child summary expands to a confined
`FunctionTrace` of exactly the advertised length. Once that is available,
`toFunctionTrace_within` expands all splices into a flat trace.

The scoped trace keeps a parent's own steps inside its owned addresses. The reconstructed flat trace
uses the larger execution extent because a separately emitted callee does not belong to the caller's
owned region. Keeping those two sets separate prevents the local proof from claiming ownership of
callee instructions while still describing the real whole run.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV

/-! ## Checked boundary types

These name the three ways a function instance hands control across one of its edges. They are pure data;
the `validFor` predicates in the next section are what tie them to a `FunctionInstance`. -/

/--
A classified way the machine leaves a function instance.

The function instance's *generated* exit set (`exitPcs`) is address data; an `ExitBoundary` is the semantic
reading of a single member of it. Keeping the three cases apart matters because they compose
differently: a `direct` edge continues in another function instance at a known target, a `return_` hands
control back to an unknown caller, and a `terminal` transfer ends the thread. A proof that a run
finished must say *which* of these it finished by, so that the caller-side obligation matches.
-/
inductive ExitBoundary
  /-- A checked direct edge `source → target` that leaves the occupancy. `target` is a concrete,
  decoded successor address, so the continuation is pinned. -/
  | direct (source target : Nat)
  /-- A return from `source`. There is no target: control goes to whatever caller is on the stack, so
  the boundary must include the return instruction itself (`source ∈ exitPcs`) and nothing more. -/
  | return_ (source : Nat)
  /-- A terminating transfer from `source`: a trap, halt, or non-returning tail that ends the run
  rather than continuing anywhere in the program. -/
  | terminal (source : Nat)
deriving DecidableEq, Repr

/--
A resolved direct call leaving a function instance to a specific callee function instance.

`returnPc` is recorded, not derived, so the check `returnPc = source + 4` can *fail*: a call whose
recorded continuation is not the fall-through of a 4-byte RV instruction is exactly the extractor
error this type is meant to catch. `callee`/`calleeEntry` are the address-free identity and the entry
pc the callee must be entered at, checked against the callee function instance's own `entryPc`.
-/
structure CallSite where
  /-- The pc of the call instruction inside the calling function instance. -/
  source : Nat
  /-- The address-free identity of the callee function instance. -/
  callee : FunctionInstanceId
  /-- The pc at which the callee is entered; must equal the callee function instance's `entryPc`. -/
  calleeEntry : Nat
  /-- The continuation pc control returns to; must equal `source + 4` for a direct call. -/
  returnPc : Nat
deriving DecidableEq, Repr

/--
The checked interface between a parent function instance and one inlined child occupying part of it.

An inlined child shares the parent's instruction space, so it is *not* reached by a call and returns
by falling out through an edge, not a `ret`. `entries` are the direct edges that hand control into the
child; `exits` are the direct edges by which control leaves it. Both are checked to be real edges of
the parent whose endpoints straddle the child boundary, which is what lets the child's summary be
spliced without leaving a hole in the parent's confinement.
-/
structure InlineBoundary where
  /-- The address-free identity of the inlined child function instance. -/
  child : FunctionInstanceId
  /-- Checked entry edges into the inlined child. -/
  entries : Array DirectEdge
  /-- Checked outgoing edges from the inlined child. -/
  exits : Array DirectEdge
deriving Repr

/-- Whether any generated function instance owns a given CFG edge. -/
def programContainsEdge (program : Program) (edge : DirectEdge) : Bool :=
  program.functionInstances.any fun functionInstance => functionInstance.edges.contains edge

/-- A legal entry address for one segment of an inlined child. -/
def InlineBoundary.acceptsEntry (boundary : InlineBoundary) (child : FunctionInstance)
    (entry : Nat) : Prop :=
  entry = child.entryPc ∨ ∃ edge ∈ boundary.entries, edge.target = entry

/-! ## Boundary validity against a `FunctionInstance`

Each predicate reads only generated function instances and the complete generated program edge
inventory. They are `Prop`s, not `Bool`s, because they are premises of trace obligations, not
unchecked addresses introduced by a proof. -/

/--
An `ExitBoundary` is a genuine exit of `functionInstance`.

- `direct source target`: `source → target` is a real emitted edge, `source` is owned by the
  function instance, and `target` leaves every region — i.e. it is a true occupancy-crossing edge, not an
  internal jump.
- `return_ source`: `source` is one of the generated exit pcs. This is the crucial containment: a
  return may only be claimed at an address the generator already flagged as an exit.
- `terminal source`: likewise `source` is a generated exit pc; the difference from `return_` is
  semantic (the run ends here) and is carried by the constructor, not by a different address check.
-/
def ExitBoundary.validFor (eb : ExitBoundary) (functionInstance : FunctionInstance) : Prop :=
  match eb with
  | .direct source target =>
      (⟨source, target⟩ : DirectEdge) ∈ functionInstance.edges ∧
        functionInstance.containsAddress source = true ∧
        functionInstance.containsAddress target = false
  | .return_ source => functionInstance.isExit source
  | .terminal source => functionInstance.isExit source

/--
A `CallSite` is a well-formed resolved call from `functionInstance` to `callee`.

Beyond the identities, the check now pins the *actual call edge*: `source → calleeEntry` must be a
real emitted edge of `functionInstance` landing on the callee's own entry pc. Membership of the callee among the
resolved external calls no longer suffices — a call site that names a callee `functionInstance` genuinely reaches
but whose recorded entry/edge does not correspond to a decoded transfer is rejected. The continuation
is the fall-through of a 4-byte direct call (`returnPc = source + 4`); both the call instruction and
its continuation are owned by `functionInstance` (the call leaves and control comes back *inside* the function instance).
-/
def CallSite.validFor (cs : CallSite) (program : Program)
    (functionInstance callee : FunctionInstance) : Prop :=
  cs.returnPc = cs.source + 4 ∧
    callee.id = cs.callee ∧
    callee.entryPc = cs.calleeEntry ∧
    cs.callee ∈ functionInstance.externalCalls ∧
    programContainsEdge program ⟨cs.source, cs.calleeEntry⟩ = true ∧
    functionInstance.containsAddress cs.source = true ∧
    functionInstance.containsAddress cs.returnPc = true

/--
An `InlineBoundary` correctly frames `childFunctionInstance` inside `functionInstance`.

`childFunctionInstance` has the recorded child identity and is one of `functionInstance`'s children; every declared entry edge
is a real program edge that genuinely crosses *into* the child (its source is owned by the parent
and *not* the child, its target is owned by the child); and every declared exit edge is a real edge of
`functionInstance` that genuinely crosses *out of* the child (its source is owned by the child, its target leaves
the child and lands back in the parent). Requiring both endpoints of each edge to straddle the
boundary is what rejects a mislabeled edge that stays on one side.
-/
def InlineBoundary.validFor (ib : InlineBoundary) (program : Program)
    (functionInstance childFunctionInstance : FunctionInstance) : Prop :=
  childFunctionInstance.id = ib.child ∧
    ib.child ∈ functionInstance.children ∧
    (∀ e ∈ ib.entries, programContainsEdge program e = true ∧
        functionInstance.containsAddress e.source = true ∧
        childFunctionInstance.containsAddress e.source = false ∧
        childFunctionInstance.containsAddress e.target = true ∧
        ib.acceptsEntry childFunctionInstance e.target) ∧
    (∀ e ∈ ib.exits, programContainsEdge program e = true ∧
        childFunctionInstance.containsAddress e.source = true ∧
        childFunctionInstance.containsAddress e.target = false ∧
        functionInstance.containsAddress e.target = true)

/-- An inlined child can leave through a real call whose return continuation is outside the child
but still inside the parent. This is not a direct edge: retiring the source enters `callee`, consumes
its summary, retires its return, and only then reaches `call.returnPc`. -/
structure InlineCallBoundary where
  inline : InlineBoundary
  call : CallSite
deriving Repr

/-- A checked call exit from an inlined child. The call instruction belongs to the child, while its
post-return continuation belongs to the enclosing parent. -/
def InlineCallBoundary.validFor (boundary : InlineCallBoundary) (program : Program)
    (functionInstance childFunctionInstance callee : FunctionInstance) : Prop :=
  boundary.inline.validFor program functionInstance childFunctionInstance ∧
    boundary.call.validFor program functionInstance callee ∧
    childFunctionInstance.containsAddress boundary.call.source = true ∧
    childFunctionInstance.containsAddress boundary.call.returnPc = false

/-! ## Checked realizations of a boundary

A `ScopedTrace` splice must *produce the machine steps that realize the boundary*, not merely assert a
before/after pair. `CallTransfer` and `InlineTransfer` bundle those steps together with the boundary
evidence: the intermediate states, the `Runs (try_step …)` facts for each retired transfer, and the
region/exit facts the reconstruction consumes. Because they are the constructor's payload, a splice
cannot exist without a real call/return (resp. child body + outgoing edge) at the pinned pcs. -/

/--
The checked machine realization of one `CallSite`, carrying `s` to the post-return state `sResume`.

Every pc is pinned to the `CallSite` (`callPc.toNat = cs.source`, `calleeEntry`, `returnPc`), the two
transfer instructions are real retiring `try_step`s, and the callee body is a `childSummary` consuming
*exactly* `used` steps. The return instruction (`retPc`) is where the callee summary stops — sitting
on its own return, one step before retiring it — matching the flat-trace convention that a
`FunctionTrace` halts *on* an exit pc.
-/
structure CallTransfer (region exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop)
    (cs : CallSite) (program : Program) (functionInstance callee : FunctionInstance)
    (fromStep used : Nat) (s sResume : State) where
  /-- The call site is a checked resolved call from `functionInstance` to `callee`. -/
  valid : cs.validFor program functionInstance callee
  /-- The machine is at the call instruction, owned by the parent and not a parent exit. -/
  callPc : BitVec 64
  atCall : s.regs.get? PC = some callPc
  callSource : callPc.toNat = cs.source
  callInRegion : region callPc
  callNotExit : ¬ exit callPc
  /-- Retiring the call lands at the callee's checked entry pc. -/
  sCall : State
  doCall : Runs (try_step fromStep false) s sCall false
  calleeEntryPc : BitVec 64
  atCalleeEntry : sCall.regs.get? PC = some calleeEntryPc
  calleeEntryMatches : calleeEntryPc.toNat = cs.calleeEntry
  /-- The callee body summary consumes exactly `used` steps and stops on its return instruction. -/
  sRet : State
  body : childSummary cs.callee (fromStep + 1) used sCall sRet
  retPc : BitVec 64
  atRet : sRet.regs.get? PC = some retPc
  retInRegion : region retPc
  retNotExit : ¬ exit retPc
  /-- Retiring the return lands at the checked continuation `returnPc = source + 4`, back in region. -/
  doReturn : Runs (try_step (fromStep + 1 + used) false) sRet sResume false
  returnPc : BitVec 64
  atResume : sResume.regs.get? PC = some returnPc
  returnMatches : returnPc.toNat = cs.returnPc
  resumeInRegion : region returnPc

/--
The checked machine realization of one `InlineBoundary` splice, carrying `s` to the post-edge state
`sResume`.

The machine enters at the child's nominal entry or a checked later-segment entry; the child body is
a `childSummary` consuming *exactly*
`used` steps and stopping on a checked outgoing edge's source (`exitEdge ∈ ib.exits`); then the parent
retires that outgoing edge, landing at the edge's target back inside the parent. The entry edge itself
is retired by the parent step that precedes this splice, so entry and outgoing edges are each accounted
exactly once.
-/
structure InlineTransfer (region exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop)
    (ib : InlineBoundary) (program : Program)
    (functionInstance childFunctionInstance : FunctionInstance)
    (fromStep used : Nat) (s sResume : State) where
  /-- The boundary correctly frames `childFunctionInstance` inside `functionInstance`. -/
  valid : ib.validFor program functionInstance childFunctionInstance
  /-- The machine is at a checked child-segment entry, owned by the parent and not a parent exit. -/
  entryPc : BitVec 64
  atEntry : s.regs.get? PC = some entryPc
  entryAccepted : ib.acceptsEntry childFunctionInstance entryPc.toNat
  entryInRegion : region entryPc
  entryNotExit : ¬ exit entryPc
  /-- The child body summary consumes exactly `used` steps and stops on a checked outgoing edge. -/
  sExit : State
  body : childSummary ib.child fromStep used s sExit
  exitEdge : DirectEdge
  exitEdgeMem : exitEdge ∈ ib.exits
  childExitPc : BitVec 64
  atExit : sExit.regs.get? PC = some childExitPc
  exitIsEdgeSource : childExitPc.toNat = exitEdge.source
  exitInRegion : region childExitPc
  exitNotExit : ¬ exit childExitPc
  /-- Retiring the outgoing edge lands at the edge's target, back in the parent region. -/
  doExit : Runs (try_step (fromStep + used) false) sExit sResume false
  resumePc : BitVec 64
  atResume : sResume.regs.get? PC = some resumePc
  resumeIsEdgeTarget : resumePc.toNat = exitEdge.target
  resumeInRegion : region resumePc

/-- A checked inline segment whose outgoing transfer is a call. The inline child's summary stops at
the call instruction; the nested `CallTransfer` then retires the call, consumes the callee summary,
retires the callee return, and resumes outside the child but inside the parent. -/
structure InlineCallTransfer (region exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop)
    (boundary : InlineCallBoundary) (program : Program)
    (functionInstance childFunctionInstance callee : FunctionInstance)
    (fromStep childUsed calleeUsed : Nat) (s sResume : State) where
  valid : boundary.validFor program functionInstance childFunctionInstance callee
  entryPc : BitVec 64
  atEntry : s.regs.get? PC = some entryPc
  entryAccepted : boundary.inline.acceptsEntry childFunctionInstance entryPc.toNat
  entryInRegion : region entryPc
  entryNotExit : ¬ exit entryPc
  sCallSite : State
  body : childSummary boundary.inline.child fromStep childUsed s sCallSite
  call : CallTransfer region exit childSummary boundary.call program functionInstance callee
    (fromStep + childUsed) calleeUsed sCallSite sResume

/-! ## The edge-aware scoped trace

`ScopedTrace` is `FunctionTrace` plus the ability to spend a child's summary in one move instead of
re-executing the child instruction by instruction. It keeps `FunctionTrace`'s step-count discipline so
the two still compose: the count is the exact number of retired *machine* steps, and a splice advances
the step number by the transfer instructions it retires plus the summary's own consumed count. -/

/--
`try_step` execution confined to `region`, running until `exit`, *with* the ability to splice
admitted child/callee summaries at checked boundaries.

`childSummary child fromStep used before after` stands for "the function instance `child`, entered at step
`fromStep`, retired exactly `used` machine steps carrying `before` to `after`". The two splice
constructors consume such a summary through a `CallTransfer`/`InlineTransfer`, so the summary's `used`
count and the boundary's transfer instructions together determine the step arithmetic — a proof can
neither drop a transfer nor invent a body length.

With no children admitted, only `exitAt` and `ownStep` are available and the definition collapses to
`FunctionTrace` (see `ScopedTrace.toFunctionTrace_of_noChildren`).
-/
inductive ScopedTrace (region exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop) :
    Nat → Nat → State → State → Prop where
  /-- Termination: the machine sits on a generated exit. Mirrors `FunctionTrace.exitAt`. -/
  | exitAt (fromStep : Nat) (s : State) (pc : BitVec 64)
      (hpc : s.regs.get? PC = some pc)
      (hexit : exit pc) :
      ScopedTrace region exit childSummary fromStep 0 s s
  /-- One retired owned in-region, non-exit instruction. Mirrors `FunctionTrace.step`. -/
  | ownStep (fromStep count : Nat) (pc : BitVec 64) (s s' s'' : State)
      (hpc : s.regs.get? PC = some pc)
      (hregion : region pc)
      (hnotExit : ¬ exit pc)
      (hstep : Runs (try_step fromStep false) s s' false)
      (hrest : ScopedTrace region exit childSummary (fromStep + 1) count s' s'') :
      ScopedTrace region exit childSummary fromStep (count + 1) s s''
  /-- Consume an inlined child's summary through a checked `InlineBoundary`. The child body runs from
  the child's entry pc and stops on a checked outgoing edge; the parent then retires that outgoing edge
  and resumes at its target. Accounts `used` body steps plus the one outgoing-edge step. -/
  | inlineStep (fromStep used count : Nat) (ib : InlineBoundary) (program : Program)
      (functionInstance childFunctionInstance : FunctionInstance)
      (s sResume s'' : State)
      (htransfer : InlineTransfer region exit childSummary ib program functionInstance
        childFunctionInstance fromStep used s sResume)
      (hrest : ScopedTrace region exit childSummary (fromStep + used + 1) count sResume s'') :
      ScopedTrace region exit childSummary fromStep (used + 1 + count) s s''
  /-- Consume an inlined child segment that leaves through a real call. Accounts the inline body,
  call instruction, callee body, and callee return separately. -/
  | inlineCallStep (fromStep childUsed calleeUsed count : Nat)
      (boundary : InlineCallBoundary) (program : Program)
      (functionInstance childFunctionInstance callee : FunctionInstance)
      (s sResume s'' : State)
      (htransfer : InlineCallTransfer region exit childSummary boundary program functionInstance
        childFunctionInstance callee fromStep childUsed calleeUsed s sResume)
      (hrest : ScopedTrace region exit childSummary
        (fromStep + childUsed + 1 + calleeUsed + 1) count sResume s'') :
      ScopedTrace region exit childSummary fromStep
        (childUsed + 1 + calleeUsed + 1 + count) s s''
  /-- Retire a resolved call and consume the callee's summary through its return, using a checked
  `CallSite`. Accounts the call step, the `used` callee-body steps, and the return step, then resumes
  at the checked continuation. -/
  | callStep (fromStep used count : Nat) (cs : CallSite) (program : Program)
      (functionInstance callee : FunctionInstance)
      (s sResume s'' : State)
      (htransfer : CallTransfer region exit childSummary cs program functionInstance callee
        fromStep used s sResume)
      (hrest : ScopedTrace region exit childSummary (fromStep + 1 + used + 1) count sResume s'') :
      ScopedTrace region exit childSummary fromStep (1 + used + 1 + count) s s''

/--
A `ScopedTrace` that genuinely enters at a generated entry.

Same role as `EnteredFunctionTrace`: because `entry` is in region and not an exit, `exitAt` cannot
fire first, so at least one transition (owned step, inline splice, or call) is retired. This is the
form a local contract obligation uses, ruling out the vacuous "already on an exit" proof.
-/
structure EnteredScopedTrace (region exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop) (entry : BitVec 64)
    (fromStep count : Nat) (s s' : State) : Prop where
  startsAtEntry : s.regs.get? PC = some entry
  entryInRegion : region entry
  entryNotExit : ¬ exit entry
  trace : ScopedTrace region exit childSummary fromStep count s s'

/-! ## From `FunctionTrace` into `ScopedTrace` (always available)

A flat confined run is trivially an edge-aware one that never splices. This direction is
unconditional and holds for *any* admitted `childSummary`. -/

/-- Every `FunctionTrace` is a `ScopedTrace` for any child-summary relation: it simply never uses the
splicing constructors. This is the "no children" embedding in its most general form. -/
theorem FunctionTrace.toScoped {region exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop} {fromStep count : Nat}
    {s s' : State}
    (h : FunctionTrace region exit fromStep count s s') :
    ScopedTrace region exit childSummary fromStep count s s' := by
  induction h with
  | exitAt fromStep t pc hpc hexit => exact ScopedTrace.exitAt fromStep t pc hpc hexit
  | step fromStep count pc u u' u'' hpc hregion hnotExit hstep _ ih =>
      exact ScopedTrace.ownStep fromStep count pc u u' u'' hpc hregion hnotExit hstep ih

/-! ## From `ScopedTrace` back to `FunctionTrace`

The interesting direction. It needs the spliced summaries to be honest confined subtraces, captured by
`SummariesCompose`. -/

/--
The obligation that admitted child summaries splice soundly: whenever `childSummary child` carries `s`
to `s'` in `used` steps and the parent then runs confined from `s'` (at step `fromStep + used`) to a
real exit in `count` steps, the whole thing is a confined parent run of `used + count` steps.

Because the summary now carries `used`, this obligation is over the summary's *own* consumed count, so
it cannot be satisfied by a mismatched length. It is the shape `FunctionTrace.append_within` produces
for one child (see `summaryComposes_of_subtrace`): the child is a `FunctionTrace inner mid used`
confined to its own address set, and appending the parent continuation yields a
`FunctionTrace region exit (used + count)`.

Note the `region` here is the one the *reconstructed* run is confined to. For a call it must be the
caller's execution extent, not the caller's own regions: the callee's instructions are outside the
caller's code and no honest reconstruction can pretend otherwise.
-/
def SummariesCompose (region exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop) : Prop :=
  ∀ (child : FunctionInstanceId) (fromStep used count : Nat) (s s' s'' : State),
    childSummary child fromStep used s s' →
    FunctionTrace region exit (fromStep + used) count s' s'' →
    FunctionTrace region exit fromStep (used + count) s s''

/--
The canonical way to discharge one `SummariesCompose` step: a child that is itself a confined
subtrace `FunctionTrace inner mid used` — inside the reconstruction's address set, with every
enclosing `exit` that lies in `inner` already stopping it — composes with any continuation to the
real exits. This is `FunctionTrace.append_within`, recorded here to name the mechanism a
program-specific proof plugs a child `Implements` into.
-/
theorem summaryComposes_of_subtrace {inner region mid exit : BitVec 64 → Prop}
    (innerSubset : ∀ pc, inner pc → region pc)
    (outerExitsStopInner : ∀ pc, inner pc → exit pc → mid pc)
    {fromStep used count : Nat} {s s' s'' : State}
    (child : FunctionTrace inner mid fromStep used s s')
    (cont : FunctionTrace region exit (fromStep + used) count s' s'') :
    FunctionTrace region exit fromStep (used + count) s s'' :=
  FunctionTrace.append_within innerSubset outerExitsStopInner child cont

/-- A `ScopedTrace` collapses to an ordinary `FunctionTrace` once its child summaries are known to
compose — and the flat run it collapses to is confined to `outer`, the address set the *reconstructed*
run occupies, which is larger than the `own` set the scoped run retires its own steps in.

Keeping the two apart is what makes this usable. `own` is the function instance's own code (plus whatever
uncataloged source function it absorbs); a scoped `ownStep` may only retire an instruction there, so a local
proof gains no freedom to wander into a callee. `outer` is the function instance's execution extent; the
callee's instructions genuinely execute, so the flat reconstruction has to admit them.

The owned/exit constructors mirror `FunctionTrace` directly through `hsub`; each splice retires its
boundary's transfer instruction(s) with `FunctionTrace.step` and discharges the spliced body with the
`SummariesCompose` hypothesis. The step arithmetic lines up exactly because the splice count already
counts the transfer instructions. -/
theorem ScopedTrace.toFunctionTrace_within {own outer exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    (hsub : ∀ pc, own pc → outer pc)
    (hcompose : SummariesCompose outer exit childSummary)
    {fromStep count : Nat} {s s' : State}
    (h : ScopedTrace own exit childSummary fromStep count s s') :
    FunctionTrace outer exit fromStep count s s' := by
  induction h with
  | exitAt fromStep t pc hpc hexit => exact FunctionTrace.exitAt fromStep t pc hpc hexit
  | ownStep fromStep count pc u u' u'' hpc hregion hnotExit hstep _ ih =>
      exact FunctionTrace.step fromStep count pc u u' u'' hpc (hsub pc hregion) hnotExit hstep ih
  | inlineStep fromStep used count ib program functionInstance childFunctionInstance u uResume u''
      htransfer _ ih =>
      -- ih : FunctionTrace outer exit (fromStep + used + 1) count uResume u''
      have outFt : FunctionTrace outer exit (fromStep + used) (count + 1) htransfer.sExit u'' :=
        FunctionTrace.step (fromStep + used) count htransfer.childExitPc
          htransfer.sExit uResume u''
          htransfer.atExit (hsub _ htransfer.exitInRegion) htransfer.exitNotExit htransfer.doExit ih
      have bodyFt : FunctionTrace outer exit fromStep (used + (count + 1)) u u'' :=
        hcompose ib.child fromStep used (count + 1) u htransfer.sExit u'' htransfer.body outFt
      have harith : used + 1 + count = used + (count + 1) := by omega
      rw [harith]; exact bodyFt
  | inlineCallStep fromStep childUsed calleeUsed count boundary program functionInstance
      childFunctionInstance callee u uResume u'' htransfer _ ih =>
      have retFt : FunctionTrace outer exit
          (fromStep + childUsed + 1 + calleeUsed) (count + 1) htransfer.call.sRet u'' :=
        FunctionTrace.step (fromStep + childUsed + 1 + calleeUsed) count
          htransfer.call.retPc htransfer.call.sRet uResume u'' htransfer.call.atRet
          (hsub _ htransfer.call.retInRegion) htransfer.call.retNotExit
          htransfer.call.doReturn ih
      have calleeFt : FunctionTrace outer exit (fromStep + childUsed + 1)
          (calleeUsed + (count + 1)) htransfer.call.sCall u'' :=
        hcompose boundary.call.callee (fromStep + childUsed + 1) calleeUsed (count + 1)
          htransfer.call.sCall htransfer.call.sRet u'' htransfer.call.body retFt
      have callFt : FunctionTrace outer exit (fromStep + childUsed)
          (calleeUsed + (count + 1) + 1) htransfer.sCallSite u'' :=
        FunctionTrace.step (fromStep + childUsed) (calleeUsed + (count + 1))
          htransfer.call.callPc htransfer.sCallSite htransfer.call.sCall u''
          htransfer.call.atCall (hsub _ htransfer.call.callInRegion)
          htransfer.call.callNotExit htransfer.call.doCall calleeFt
      have bodyFt : FunctionTrace outer exit fromStep
          (childUsed + (calleeUsed + (count + 1) + 1)) u u'' :=
        hcompose boundary.inline.child fromStep childUsed
          (calleeUsed + (count + 1) + 1) u htransfer.sCallSite u'' htransfer.body callFt
      have harith : childUsed + 1 + calleeUsed + 1 + count =
          childUsed + (calleeUsed + (count + 1) + 1) := by omega
      rw [harith]
      exact bodyFt
  | callStep fromStep used count cs program functionInstance callee u uResume u'' htransfer _ ih =>
      -- ih : FunctionTrace outer exit (fromStep + 1 + used + 1) count uResume u''
      have retFt : FunctionTrace outer exit (fromStep + 1 + used) (count + 1) htransfer.sRet u'' :=
        FunctionTrace.step (fromStep + 1 + used) count htransfer.retPc
          htransfer.sRet uResume u''
          htransfer.atRet (hsub _ htransfer.retInRegion) htransfer.retNotExit htransfer.doReturn ih
      have bodyFt :
          FunctionTrace outer exit (fromStep + 1) (used + (count + 1)) htransfer.sCall u'' :=
        hcompose cs.callee (fromStep + 1) used (count + 1) htransfer.sCall htransfer.sRet u''
          htransfer.body retFt
      have callFt : FunctionTrace outer exit fromStep (used + (count + 1) + 1) u u'' :=
        FunctionTrace.step fromStep (used + (count + 1)) htransfer.callPc
          u htransfer.sCall u''
          htransfer.atCall (hsub _ htransfer.callInRegion) htransfer.callNotExit htransfer.doCall
          bodyFt
      have harith : 1 + used + 1 + count = used + (count + 1) + 1 := by omega
      rw [harith]; exact callFt

/-- The same-address-set case: a scoped run whose splices compose inside the very region it owns.
This is the shape a leaf function instance (no calls out of its own code) uses. -/
theorem ScopedTrace.toFunctionTrace {region exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    (hcompose : SummariesCompose region exit childSummary)
    {fromStep count : Nat} {s s' : State}
    (h : ScopedTrace region exit childSummary fromStep count s s') :
    FunctionTrace region exit fromStep count s s' :=
  h.toFunctionTrace_within (fun _ hpc => hpc) hcompose

/-- With no children admitted (`childSummary` uninhabited), a `ScopedTrace` is a `FunctionTrace`
outright — no honest composition data is needed, because the splice constructors cannot fire. This is
the degenerate instance the module promises: an edge-free function instance's scoped trace *is* its flat
trace. -/
theorem ScopedTrace.toFunctionTrace_of_noChildren {region exit : BitVec 64 → Prop}
    {fromStep count : Nat} {s s' : State}
    (h : ScopedTrace region exit (fun _ _ _ _ _ => False) fromStep count s s') :
    FunctionTrace region exit fromStep count s s' :=
  h.toFunctionTrace (fun _ _ _ _ _ _ _ hbody _ => hbody.elim)

/-- An `EnteredScopedTrace` becomes an `EnteredFunctionTrace` in the enclosing extent under the same
composition obligation: the entry facts carry over (the entry pc is owned, hence in the extent) and
the underlying trace is collapsed by `ScopedTrace.toFunctionTrace_within`. -/
theorem EnteredScopedTrace.toEnteredFunctionTrace_within {own outer exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop} {entry : BitVec 64}
    {fromStep count : Nat} {s s' : State}
    (hsub : ∀ pc, own pc → outer pc)
    (hcompose : SummariesCompose outer exit childSummary)
    (h : EnteredScopedTrace own exit childSummary entry fromStep count s s') :
    EnteredFunctionTrace outer exit entry fromStep count s s' :=
  { startsAtEntry := h.startsAtEntry
    entryInRegion := hsub entry h.entryInRegion
    entryNotExit := h.entryNotExit
    trace := h.trace.toFunctionTrace_within hsub hcompose }

/-- The same-address-set case of `toEnteredFunctionTrace_within`. -/
theorem EnteredScopedTrace.toEnteredFunctionTrace {region exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop} {entry : BitVec 64}
    {fromStep count : Nat} {s s' : State}
    (hcompose : SummariesCompose region exit childSummary)
    (h : EnteredScopedTrace region exit childSummary entry fromStep count s s') :
    EnteredFunctionTrace region exit entry fromStep count s s' :=
  h.toEnteredFunctionTrace_within (fun _ hpc => hpc) hcompose

end BinaryFv.RiscV.Elfling
