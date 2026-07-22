import BinaryFv.RiscV.Elfling.Contract

/-!
# Checked boundaries and edge-aware scoped traces for Elfling occurrences

`FunctionTrace` (see `FunctionTrace.lean`) confines execution to one occurrence's regions and stops at
that occurrence's generated exits, but it is deliberately *flat*: every retired instruction is one the
occurrence owns, and the only way out is an exit pc. Real occurrences are not flat. They contain
inlined children, they make resolved calls that return, and they leave through classified edges. This
module adds the boundary vocabulary that names those transitions and an *edge-aware* trace,
`ScopedTrace`, that can splice a child's summary in place of re-executing it.

Three design points carry the weight.

*Boundaries are checked against generated data, never invented.* Every `validFor` predicate below is
built only from a `FunctionInstance`'s own `edges`, `exitPcs`, `externalCalls`, and `children` — the
untrusted-but-validated generator output. Nothing here writes an address literal; a proof cannot pick
a convenient boundary because the boundary must already be present in the emitted CFG.

*The child summary is abstract.* `ScopedTrace` is parameterized by a relation
`childSummary : Nat → State → State → Prop` (a starting step number and the before/after states). This
is exactly the shape an `Implements` result exposes once its step count is hidden, so this module
depends on nothing from the contract layer beyond `FunctionTrace`/`Implements` themselves. It never
needs to know *how* a child was proved, only that some admitted summary carries `s` to `s'`.

*Composition is a hypothesis, not a fiction.* Reconstructing an ordinary `FunctionTrace` from a
`ScopedTrace` requires that each spliced summary really is a confined subtrace of the length the parent
accounts for it. That fact — `SummariesCompose` — is stated as an explicit obligation and discharged,
for a single child, by `FunctionTrace.append`. The generic composition theorem is then fully proved
*given* it; deriving it for a concrete program (which child fires at which state) needs the decoder's
successor data and lives above this generic layer.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV

/-! ## Checked boundary types

These name the three ways an occurrence hands control across one of its edges. They are pure data;
the `validFor` predicates in the next section are what tie them to a `FunctionInstance`. -/

/--
A classified way the machine leaves an occurrence.

The occurrence's *generated* exit set (`exitPcs`) is address data; an `ExitBoundary` is the semantic
reading of a single member of it. Keeping the three cases apart matters because they compose
differently: a `direct` edge continues in another occurrence at a known target, a `return_` hands
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
A resolved direct call leaving an occurrence to a specific callee occurrence.

`returnPc` is recorded, not derived, so the check `returnPc = source + 4` can *fail*: a call whose
recorded continuation is not the fall-through of a 4-byte RV instruction is exactly the extractor
error this type is meant to catch. `callee`/`calleeEntry` are the address-free identity and the entry
pc the callee must be entered at, checked against the callee occurrence's own `entryPc`.
-/
structure CallSite where
  /-- The pc of the call instruction inside the calling occurrence. -/
  source : Nat
  /-- The address-free identity of the callee occurrence. -/
  callee : InstanceId
  /-- The pc at which the callee is entered; must equal the callee occurrence's `entryPc`. -/
  calleeEntry : Nat
  /-- The continuation pc control returns to; must equal `source + 4` for a direct call. -/
  returnPc : Nat
deriving DecidableEq, Repr

/--
The checked interface between a parent occurrence and one inlined child occupying part of it.

An inlined child shares the parent's instruction space, so it is *not* reached by a call and returns
by falling out through an edge, not a `ret`. `entries` are the direct edges that hand control into the
child; `exits` are the direct edges by which control leaves it. Both are checked to be real edges of
the parent whose endpoints straddle the child boundary, which is what lets the child's summary be
spliced without leaving a hole in the parent's confinement.
-/
structure InlineBoundary where
  /-- The address-free identity of the inlined child occurrence. -/
  child : InstanceId
  /-- Checked entry edges into the inlined child. -/
  entries : Array DirectEdge
  /-- Checked outgoing edges from the inlined child. -/
  exits : Array DirectEdge
deriving Repr

/-! ## Boundary validity against a `FunctionInstance`

Each predicate reads only generated data off the relevant occurrence(s). They are `Prop`s, not
`Bool`s, because they are premises of the trace obligations, not something a proof decides; and they
are built from the occurrence's own arrays so that no address is ever introduced by hand. -/

/--
An `ExitBoundary` is a genuine exit of `inst`.

- `direct source target`: `source → target` is a real emitted edge, `source` is owned by the
  occurrence, and `target` leaves every region — i.e. it is a true occupancy-crossing edge, not an
  internal jump.
- `return_ source`: `source` is one of the generated exit pcs. This is the crucial containment: a
  return may only be claimed at an address the generator already flagged as an exit.
- `terminal source`: likewise `source` is a generated exit pc; the difference from `return_` is
  semantic (the run ends here) and is carried by the constructor, not by a different address check.
-/
def ExitBoundary.validFor (eb : ExitBoundary) (inst : FunctionInstance) : Prop :=
  match eb with
  | .direct source target =>
      (⟨source, target⟩ : DirectEdge) ∈ inst.edges ∧
        inst.containsAddress source = true ∧
        inst.containsAddress target = false
  | .return_ source => inst.isExit source
  | .terminal source => inst.isExit source

/--
A `CallSite` is a well-formed resolved call from `inst` to `callee`.

The continuation is the fall-through of a 4-byte direct call (`returnPc = source + 4`); the recorded
callee identity is the identity `callee` actually has; the recorded entry pc is `callee`'s own entry;
the callee is one of the occurrence's resolved external calls; and both the call instruction and its
continuation are owned by `inst` (the call leaves and control comes back *inside* the occurrence).
-/
def CallSite.validFor (cs : CallSite) (inst callee : FunctionInstance) : Prop :=
  cs.returnPc = cs.source + 4 ∧
    callee.id = cs.callee ∧
    callee.entryPc = cs.calleeEntry ∧
    cs.callee ∈ inst.externalCalls ∧
    inst.containsAddress cs.source = true ∧
    inst.containsAddress cs.returnPc = true

/--
An `InlineBoundary` correctly frames `childInst` inside `inst`.

`childInst` has the recorded child identity and is one of `inst`'s children; every declared entry edge
is a real edge of `inst` landing inside the child; every declared exit edge is a real edge of `inst`
leaving from inside the child. The endpoint checks use the child occurrence's own occupancy, so a
mislabeled edge — one that does not actually cross the child boundary — fails the check.
-/
def InlineBoundary.validFor (ib : InlineBoundary) (inst childInst : FunctionInstance) : Prop :=
  childInst.id = ib.child ∧
    ib.child ∈ inst.children ∧
    (∀ e ∈ ib.entries, e ∈ inst.edges ∧ childInst.containsAddress e.target = true) ∧
    (∀ e ∈ ib.exits, e ∈ inst.edges ∧ childInst.containsAddress e.source = true)

/-! ## The edge-aware scoped trace

`ScopedTrace` is `FunctionTrace` plus the ability to spend a child's summary in one move instead of
re-executing the child instruction by instruction. It keeps `FunctionTrace`'s step-count discipline so
the two still compose: the count is the exact number of retired *machine* steps, and a summary that
consumed `used` steps advances the step number by `used`. -/

/--
`try_step` execution confined to `region`, running until `exit`, *with* the ability to splice
admitted child/callee summaries.

The abstract parameter `childSummary fromStep before after` stands for "some already-established
confined subrun starting at step `fromStep` carried `before` to `after`". The trace records, at each
splice, how many machine steps `used` that subrun consumed, because the following owned steps must be
numbered from `fromStep + used`; the *content* of those steps is hidden inside `childSummary`.

With no children admitted, only `exitAt` and `ownStep` are available and the definition collapses to
`FunctionTrace` (see `ScopedTrace.toFunctionTrace_of_noChildren`).
-/
inductive ScopedTrace (region exit : BitVec 64 → Prop)
    (childSummary : Nat → State → State → Prop) :
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
  /-- Consume an inlined child's summary. The machine is at the child's entry pc (in region, not an
  exit); the child summary carries `s` to `s'` over `used` steps; execution resumes at `s'`. This is
  the inline splice: the child's `used` instructions are replaced by one summary step. -/
  | inlineStep (fromStep used count : Nat) (entryPc : BitVec 64) (s s' s'' : State)
      (hpc : s.regs.get? PC = some entryPc)
      (hregion : region entryPc)
      (hnotExit : ¬ exit entryPc)
      (hsummary : childSummary fromStep s s')
      (hrest : ScopedTrace region exit childSummary (fromStep + used) count s' s'') :
      ScopedTrace region exit childSummary fromStep (used + count) s s''
  /-- Retire a resolved call and consume the callee's summary through its return. The machine is at
  the call pc (in region, not an exit); the callee summary carries `s` to the post-return state `s'`
  over `used` steps; and `s'` sits at the checked continuation `returnPc`, which is itself in region,
  so the parent resumes exactly where the `CallSite` says it should. -/
  | callStep (fromStep used count : Nat) (callPc returnPc : BitVec 64) (s s' s'' : State)
      (hpc : s.regs.get? PC = some callPc)
      (hregion : region callPc)
      (hnotExit : ¬ exit callPc)
      (hsummary : childSummary fromStep s s')
      (hresume : s'.regs.get? PC = some returnPc)
      (hresumeRegion : region returnPc)
      (hrest : ScopedTrace region exit childSummary (fromStep + used) count s' s'') :
      ScopedTrace region exit childSummary fromStep (used + count) s s''

/--
A `ScopedTrace` that genuinely enters at a generated entry.

Same role as `EnteredFunctionTrace`: because `entry` is in region and not an exit, `exitAt` cannot
fire first, so at least one transition (owned step, inline splice, or call) is retired. This is the
form a local contract obligation uses, ruling out the vacuous "already on an exit" proof.
-/
structure EnteredScopedTrace (region exit : BitVec 64 → Prop)
    (childSummary : Nat → State → State → Prop) (entry : BitVec 64)
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
    {childSummary : Nat → State → State → Prop} {fromStep count : Nat} {s s' : State}
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
The obligation that admitted child summaries splice soundly: whenever `childSummary` carries `s` to
`s'` in `used` steps and the parent then runs confined from `s'` (at step `fromStep + used`) to a real
exit in `count` steps, the whole thing is a confined parent run of `used + count` steps.

This is exactly the shape `FunctionTrace.append` produces for one child (see
`summaryComposes_of_subtrace`): the child is a `FunctionTrace region mid used` whose local stop set
`mid` contains every real exit, and appending the parent continuation yields a `FunctionTrace region
exit (used + count)`. Stating it as a named obligation keeps `ScopedTrace.toFunctionTrace` honest — the
step counts must line up — without pulling the decoder's successor analysis into this generic layer.
-/
def SummariesCompose (region exit : BitVec 64 → Prop)
    (childSummary : Nat → State → State → Prop) : Prop :=
  ∀ (fromStep used count : Nat) (s s' s'' : State),
    childSummary fromStep s s' →
    FunctionTrace region exit (fromStep + used) count s' s'' →
    FunctionTrace region exit fromStep (used + count) s s''

/--
The canonical way to discharge one `SummariesCompose` step: a child that is itself a confined
subtrace `FunctionTrace region mid used` — with `mid` containing every real `exit` — composes with any
continuation to the real exits. This is just `FunctionTrace.append`, recorded here to name the
mechanism that a program-specific proof plugs a child `Implements` into.
-/
theorem summaryComposes_of_subtrace {region mid exit : BitVec 64 → Prop}
    (exitSubsetMid : ∀ pc, exit pc → mid pc)
    {fromStep used count : Nat} {s s' s'' : State}
    (child : FunctionTrace region mid fromStep used s s')
    (cont : FunctionTrace region exit (fromStep + used) count s' s'') :
    FunctionTrace region exit fromStep (used + count) s s'' :=
  FunctionTrace.append exitSubsetMid child cont

/-- A `ScopedTrace` collapses to an ordinary `FunctionTrace` once its child summaries are known to
compose. The owned/exit constructors mirror `FunctionTrace` directly; each splice is discharged by the
`SummariesCompose` hypothesis applied to the reconstructed continuation. -/
theorem ScopedTrace.toFunctionTrace {region exit : BitVec 64 → Prop}
    {childSummary : Nat → State → State → Prop}
    (hcompose : SummariesCompose region exit childSummary)
    {fromStep count : Nat} {s s' : State}
    (h : ScopedTrace region exit childSummary fromStep count s s') :
    FunctionTrace region exit fromStep count s s' := by
  induction h with
  | exitAt fromStep t pc hpc hexit => exact FunctionTrace.exitAt fromStep t pc hpc hexit
  | ownStep fromStep count pc u u' u'' hpc hregion hnotExit hstep _ ih =>
      exact FunctionTrace.step fromStep count pc u u' u'' hpc hregion hnotExit hstep ih
  | inlineStep fromStep used count entryPc u u' u'' _ _ _ hsummary _ ih =>
      exact hcompose fromStep used count u u' u'' hsummary ih
  | callStep fromStep used count callPc returnPc u u' u'' _ _ _ hsummary _ _ _ ih =>
      exact hcompose fromStep used count u u' u'' hsummary ih

/-- With no children admitted (`childSummary` uninhabited), a `ScopedTrace` is a `FunctionTrace`
outright — no composition hypothesis needed, because the splice constructors cannot fire. This is the
degenerate instance the module promises: an edge-free occurrence's scoped trace *is* its flat trace. -/
theorem ScopedTrace.toFunctionTrace_of_noChildren {region exit : BitVec 64 → Prop}
    {fromStep count : Nat} {s s' : State}
    (h : ScopedTrace region exit (fun _ _ _ => False) fromStep count s s') :
    FunctionTrace region exit fromStep count s s' := by
  induction h with
  | exitAt fromStep t pc hpc hexit => exact FunctionTrace.exitAt fromStep t pc hpc hexit
  | ownStep fromStep count pc u u' u'' hpc hregion hnotExit hstep _ ih =>
      exact FunctionTrace.step fromStep count pc u u' u'' hpc hregion hnotExit hstep ih
  | inlineStep _ _ _ _ _ _ _ _ _ _ hsummary _ _ => exact hsummary.elim
  | callStep _ _ _ _ _ _ _ _ _ _ _ hsummary _ _ _ _ => exact hsummary.elim

/-- An `EnteredScopedTrace` becomes an `EnteredFunctionTrace` under the same composition obligation:
the entry facts carry over verbatim and the underlying trace is collapsed by
`ScopedTrace.toFunctionTrace`. -/
theorem EnteredScopedTrace.toEnteredFunctionTrace {region exit : BitVec 64 → Prop}
    {childSummary : Nat → State → State → Prop} {entry : BitVec 64} {fromStep count : Nat}
    {s s' : State}
    (hcompose : SummariesCompose region exit childSummary)
    (h : EnteredScopedTrace region exit childSummary entry fromStep count s s') :
    EnteredFunctionTrace region exit entry fromStep count s s' :=
  { startsAtEntry := h.startsAtEntry
    entryInRegion := h.entryInRegion
    entryNotExit := h.entryNotExit
    trace := h.trace.toFunctionTrace hcompose }

/-! ## Local implementation and ranked composition

`LocallyImplements` is `Implements` phrased against `ScopedTrace`: an occurrence implements its
contract *given* abstract child/callee summaries. The point of the whole module is the discharge
direction — once those summaries are real (`SummariesCompose`), a local implementation is a closed
`Implements`. -/

/--
An occurrence implements its contract *relative to* admitted child/callee summaries.

Identical to `Implements` except the confined run is an `EnteredScopedTrace`, so a proof may spend
child summaries instead of re-executing inlined children and callees. This is the compositional unit:
each occurrence is verified against summaries of the occurrences below it in the call/inline order.
-/
def LocallyImplements {Error Args Result : Type}
    (region exit : BitVec 64 → Prop) (entry : BitVec 64)
    (childSummary : Nat → State → State → Prop)
    (contract : FunctionContract Error Args Result) : Prop :=
  ∀ (args : Args) (fromStep : Nat) (s : State),
    contract.pre args s →
      ∃ (count : Nat) (s' : State),
        count ≤ contract.stepBound args ∧
        EnteredScopedTrace region exit childSummary entry fromStep count s s' ∧
        contract.post args (contract.meaning args) s s'

/--
Ranked composition, closed direction: a `LocallyImplements` whose admitted summaries genuinely compose
(`SummariesCompose`) is a plain `Implements`.

This is the lemma the whole boundary layer exists to serve: proving an occurrence against summaries of
its children, then collapsing to an address-confined `Implements` once those summaries are discharged
by the children's own proofs. It is fully proved here; the residual, program-specific obligation is
supplying `SummariesCompose`, which `summaryComposes_of_subtrace` reduces to each child's
`FunctionTrace`.
-/
theorem LocallyImplements.toImplements {Error Args Result : Type}
    {region exit : BitVec 64 → Prop} {entry : BitVec 64}
    {childSummary : Nat → State → State → Prop}
    {contract : FunctionContract Error Args Result}
    (hcompose : SummariesCompose region exit childSummary)
    (h : LocallyImplements region exit entry childSummary contract) :
    Implements region exit entry contract := by
  intro args fromStep s hpre
  obtain ⟨count, s', hbound, hentered, hpost⟩ := h args fromStep s hpre
  exact ⟨count, s', hbound, hentered.toEnteredFunctionTrace hcompose, hpost⟩

end BinaryFv.RiscV.Elfling
