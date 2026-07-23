import BinaryFv.RiscV.Elfling.Boundary
import BinaryFv.RiscV.Logic.RegisterAgree
import BinaryFv.RiscV.Logic.ImageMemory

/-!
# Hoare-style contracts for Elfling occurrences

The handwritten half of the proof splits into two independent parts, because a source routine and one
of its generated occurrences are different things.

*What a routine means* is a specification-level function — it is the same for every occurrence of that
source routine, whether the occurrence was separately emitted or inlined ten frames deep. This is a
`RoutineSpec`.

*Where an occurrence lives in the machine* — the entry state its caller must establish, the exit
state it guarantees, and how many instructions it may take — is specific to that one occurrence. An
optimizer can give two occurrences of the same routine completely different register/stack/memory
bindings, and a faithful model must let them differ. This is an `OccurrenceBinding`.

An `OccurrenceContract` pairs the shared spec with one occurrence's binding, and `Implements` is the
obligation tying that pair to actual generated Sail execution confined to the occurrence.

Three things are deliberate.

*The outcome type is a parameter.* The decoder's leaf routines produce `Except DecodeError Result`,
but the exported wrapper produces a richer `DecodeCallOutcome` (success / rejected / already-decoded).
Parameterizing the outcome keeps this layer generic instead of hard-coding `Except`, and avoids a
collision with `BinaryFv.RiscV.DecodeError` (an unrelated ELF word-decode failure).

*`exit` sees both states.* Every frame predicate in this codebase is binary — `Agree P before after`,
`imageUnchanged image after` — so a postcondition that only saw the final state could not say
"unrelated memory is preserved" at all.

*`Implements` quantifies over the starting step number.* `Trace`'s step counter is a real obligation
and composition requires the callee's binding to hold at whatever step number the caller reached.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary
open BinaryFv.RiscV

/--
The handwritten specification of one semantic routine, as a spec-level function from arguments to an
outcome.

`meaning` must be a specialized or composed specification operation, never a fresh re-implementation
of the routine's control flow: a hand-rolled mirror of the machine code would always be provable and
would say nothing about the specification.

**One `RoutineSpec` is shared by every occurrence of a source routine.** It mentions no address, no
register, and no step count — those all belong to the occurrence's `OccurrenceBinding`. Relinking the
binary, or the optimizer inlining a routine into a new caller, changes bindings, never this.
-/
structure RoutineSpec (Args Outcome : Type) where
  meaning : Args → Outcome

/--
Where one generated occurrence sits in the machine: what its caller must establish on entry, what its
exit state must satisfy for a given outcome, and its instruction budget.

**Every generated occurrence has its own `OccurrenceBinding`.** The three occurrence kinds bind
differently, and this is exactly the distinction the previous single-contract model erased:

- an exported occurrence binds the real C ABI and the wrapper's global effects;
- an emitted internal occurrence binds its actual optimized ABI (which may drop or reorder source
  arguments);
- an inlined occurrence binds its actual entry/exit registers, stack slots, and memory locations.

`stepBound` is an upper bound, so a binding may not be discharged by a run that merely stops
somewhere; `exit` is what pins where it stopped and what it produced.
-/
structure OccurrenceBinding (Args Outcome : Type) where
  entry : Args → State → Prop
  exit : Args → Outcome → State → State → Prop
  stepBound : Args → Nat

/--
One occurrence's full contract: the shared `RoutineSpec` this occurrence realizes, paired with this
occurrence's own `OccurrenceBinding`.

The spec is what the occurrence must *mean*; the binding is *where and how* it means it. Keeping them
as separate fields is what lets many occurrences of one routine share a single meaning while each
carries its own machine placement.
-/
structure OccurrenceContract (Args Outcome : Type) where
  spec : RoutineSpec Args Outcome
  binding : OccurrenceBinding Args Outcome

/--
A source-shaped contract: the special case of an `OccurrenceContract` whose outcome is
`Except Error Result` and whose binding is the routine's *source-level* ABI.

Most decoder leaves are cataloged this way because their source ABI is a faithful binding for the
occurrence in question. `FunctionContract.toOccurrence` projects one into the generic form, so the
occurrence-specific bindings (the exported wrapper, deeply inlined occurrences) and the source-shaped
leaves live under one `Implements` obligation.
-/
structure FunctionContract (Error Args Result : Type) where
  meaning : Args → Except Error Result
  pre : Args → State → Prop
  post : Args → Except Error Result → State → State → Prop
  stepBound : Args → Nat

namespace FunctionContract

variable {Error Args Result : Type}

/-- The shared specification half of a source-shaped contract. -/
def toRoutineSpec (contract : FunctionContract Error Args Result) :
    RoutineSpec Args (Except Error Result) :=
  { meaning := contract.meaning }

/-- The (source-shaped) occurrence binding of a source-shaped contract. -/
def toBinding (contract : FunctionContract Error Args Result) :
    OccurrenceBinding Args (Except Error Result) :=
  { entry := contract.pre, exit := contract.post, stepBound := contract.stepBound }

/-- A source-shaped contract as a generic `OccurrenceContract`. This is the single adapter between the
old source-shaped catalog and the occurrence-aware obligation. -/
def toOccurrence (contract : FunctionContract Error Args Result) :
    OccurrenceContract Args (Except Error Result) :=
  { spec := contract.toRoutineSpec, binding := contract.toBinding }

end FunctionContract

/--
The composite preservation a callee owes its caller: the registers outside its write set agree, and
the code image is unmodified.

There was no existing predicate combining a register frame with an image frame; memory framing is
left to the instantiating layer, which knows which regions are input, result, and heap.
-/
def CalleeFrame (preserved : Register → Prop) (image : BinaryFv.Binary.ProgramImage)
    (before after : State) : Prop :=
  Agree preserved before after ∧ image.matchesMemory after.mem

namespace CalleeFrame

theorem trans {preserved : Register → Prop} {image : BinaryFv.Binary.ProgramImage}
    {a b c : State} (hab : CalleeFrame preserved image a b) (hbc : CalleeFrame preserved image b c) :
    CalleeFrame preserved image a c :=
  ⟨Agree.trans hab.1 hbc.1, hbc.2⟩

end CalleeFrame

/--
The obligation that a generated occupancy of instruction space implements an occurrence contract.

Read it as: for every argument tuple, every starting step number, and every state satisfying the
occurrence's `entry` binding, execution confined to `region` from `entry` reaches a generated exit
within `stepBound` steps, and the resulting states satisfy the occurrence's `exit` binding *at the
exact outcome `meaning` prescribes*.

Using `EnteredFunctionTrace` rather than a bare `FunctionTrace` is what rules out the degenerate
proof in which the machine already sits on an exit and nothing is executed.
-/
def OccurrenceContract.Implements {Args Outcome : Type}
    (region exit : BitVec 64 → Prop) (entry : BitVec 64)
    (contract : OccurrenceContract Args Outcome) : Prop :=
  ∀ (args : Args) (fromStep : Nat) (s : State),
    contract.binding.entry args s →
      ∃ (count : Nat) (s' : State),
        count ≤ contract.binding.stepBound args ∧
        EnteredFunctionTrace region exit entry fromStep count s s' ∧
        contract.binding.exit args (contract.spec.meaning args) s s'

/--
`Implements` for a source-shaped `FunctionContract`: it is exactly the occurrence obligation on the
projected `OccurrenceContract`.

This keeps every source-shaped leaf under the same seam the occurrence-specific bindings use, so the
local-to-global composition never has to special-case the two.
-/
def Implements {Error Args Result : Type}
    (region exit : BitVec 64 → Prop) (entry : BitVec 64)
    (contract : FunctionContract Error Args Result) : Prop :=
  OccurrenceContract.Implements region exit entry contract.toOccurrence

/--
Where a generated occurrence's execution may sit: its own possibly discontiguous ranges, together
with `reached` — the addresses of everything it may transfer control into.

The second component is not a loophole, it is the correction of one. `Implements` confines *every*
retired step to the region, so an occurrence that calls another occurrence has no confined run at all
if the region is only its own code: the callee's instructions execute and are not in it. Stating the
obligation over own-regions alone therefore makes it unsatisfiable for every calling occurrence —
false rather than merely unproved — and a local assumption built on it would be worthless.

`reached` is supplied by the generated layer as a specific computed address set (the occurrence's
transfer-graph extent), never existentially chosen, so widening it is a visible change to generated
data that the boundary inventory checks.
-/
def InstanceExecutionPcs (instance_ : BinaryFv.Binary.Elfling.FunctionInstance)
    (reached : BitVec 64 → Prop) (pc : BitVec 64) : Prop :=
  RegionPcs instance_.regions pc ∨ reached pc

/-- An occurrence's own code is part of where it executes. -/
theorem RegionPcs.subset_executionPcs {instance_ : BinaryFv.Binary.Elfling.FunctionInstance}
    {reached : BitVec 64 → Prop} {pc : BitVec 64} (h : RegionPcs instance_.regions pc) :
    InstanceExecutionPcs instance_ reached pc := Or.inl h

/--
`OccurrenceContract.Implements` for a generated Elfling occurrence: the confinement region is that
occurrence's ranges together with the addresses it reaches.

This is the single visible seam between the generated, untrusted, address-bearing layer and the
handwritten, address-free contract. The contract argument mentions no address; the occurrence and the
generated extent supply all of them.
-/
def OccurrenceContract.ImplementsInstance {Args Outcome : Type}
    (instance_ : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop)
    (contract : OccurrenceContract Args Outcome) : Prop :=
  OccurrenceContract.Implements (InstanceExecutionPcs instance_ reached) exit entry contract

/--
`Implements` for a generated Elfling occurrence of a source-shaped contract.

The catalog still joins a `FunctionContract` to an occurrence through this, and it routes through the
occurrence form.
-/
def ImplementsInstance {Error Args Result : Type}
    (instance_ : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop)
    (contract : FunctionContract Error Args Result) : Prop :=
  Implements (InstanceExecutionPcs instance_ reached) exit entry contract

/--
A contract whose entry binding no state satisfies is vacuously implemented.

Sail memory is sparse, so an `entry` must materialize every address the routine touches; it is easy
to write one that is quietly contradictory. Every cataloged routine therefore carries a companion
satisfiability claim, and this is the shape of it.
-/
def OccurrenceContract.PreSatisfiable {Args Outcome : Type}
    (contract : OccurrenceContract Args Outcome) : Prop :=
  ∃ (args : Args) (s : State), contract.binding.entry args s

/-- `PreSatisfiable` for a source-shaped `FunctionContract`. -/
def PreSatisfiable {Error Args Result : Type} (contract : FunctionContract Error Args Result) : Prop :=
  OccurrenceContract.PreSatisfiable contract.toOccurrence

theorem OccurrenceContract.Implements.not_vacuous {Args Outcome : Type}
    {region exit : BitVec 64 → Prop} {entry : BitVec 64}
    {contract : OccurrenceContract Args Outcome}
    (himpl : OccurrenceContract.Implements region exit entry contract)
    (hsat : OccurrenceContract.PreSatisfiable contract) :
    ∃ (args : Args) (count : Nat) (s s' : State),
      0 < count ∧ contract.binding.exit args (contract.spec.meaning args) s s' := by
  obtain ⟨args, s, hpre⟩ := hsat
  obtain ⟨count, s', _, hentered, hexit⟩ := himpl args 0 s hpre
  exact ⟨args, count, s, s', hentered.count_pos, hexit⟩

theorem Implements.not_vacuous {Error Args Result : Type}
    {region exit : BitVec 64 → Prop} {entry : BitVec 64}
    {contract : FunctionContract Error Args Result}
    (himpl : Implements region exit entry contract) (hsat : PreSatisfiable contract) :
    ∃ (args : Args) (count : Nat) (s s' : State),
      0 < count ∧ contract.post args (contract.meaning args) s s' :=
  OccurrenceContract.Implements.not_vacuous himpl hsat

/-! ## Local implementation

`LocallyImplements` is `Implements` phrased against `ScopedTrace`: an occurrence implements its
contract *given* summaries of the occurrences below it. This is the compositional unit the whole
proof campaign is organized around — the thing a later row proves once per occurrence — and the point
of the pair below is the discharge direction: once those summaries are real (`SummariesCompose`), a
local implementation *is* a closed `Implements`.

Two address sets appear, and the asymmetry between them is the substance:

- the local run retires its own steps only inside `own` — the occurrence's code plus whatever
  uncataloged routine it absorbs — so a local proof may not wander into a callee it holds a summary
  for;
- the closed run it collapses to is confined to `InstanceExecutionPcs`, which additionally admits the
  code the occurrence reaches, because that code genuinely executes.
-/

/--
An occurrence implements its contract *relative to* admitted child/callee summaries.

Identical to `OccurrenceContract.Implements` except the confined run is an `EnteredScopedTrace`, so a
proof may spend child summaries instead of re-executing inlined children and callees.
-/
def OccurrenceContract.LocallyImplements {Args Outcome : Type}
    (own exit : BitVec 64 → Prop) (entry : BitVec 64)
    (childSummary : BinaryFv.Binary.Elfling.InstanceId → Nat → Nat → State → State → Prop)
    (contract : OccurrenceContract Args Outcome) : Prop :=
  ∀ (args : Args) (fromStep : Nat) (s : State),
    contract.binding.entry args s →
      ∃ (count : Nat) (s' : State),
        count ≤ contract.binding.stepBound args ∧
        EnteredScopedTrace own exit childSummary entry fromStep count s s' ∧
        contract.binding.exit args (contract.spec.meaning args) s s'

/-- `LocallyImplements` for a source-shaped `FunctionContract`: exactly the occurrence-shaped local
obligation on the projected `OccurrenceContract`, so the source-shaped leaves and the
occurrence-specific bindings live under one local seam just as they do under one closed seam. -/
def LocallyImplements {Error Args Result : Type}
    (own exit : BitVec 64 → Prop) (entry : BitVec 64)
    (childSummary : BinaryFv.Binary.Elfling.InstanceId → Nat → Nat → State → State → Prop)
    (contract : FunctionContract Error Args Result) : Prop :=
  OccurrenceContract.LocallyImplements own exit entry childSummary contract.toOccurrence

/--
The local obligation of a generated Elfling occurrence: it implements its contract against summaries
of the occurrences below it, retiring its own steps only inside what it owns.

`own` is generated data — the occurrence's ranges plus the ranges of the uncataloged routines it
absorbs — so the local obligation cannot be relaxed by choosing a bigger address set. This is the
proposition `LocalContractAssumptions` quantifies, and the one a later row discharges per occurrence.
-/
def OccurrenceContract.LocallyImplementsInstance {Args Outcome : Type}
    (own : BitVec 64 → Prop) (entry : BitVec 64) (exit : BitVec 64 → Prop)
    (childSummary : BinaryFv.Binary.Elfling.InstanceId → Nat → Nat → State → State → Prop)
    (contract : OccurrenceContract Args Outcome) : Prop :=
  OccurrenceContract.LocallyImplements own exit entry childSummary contract

/-- `LocallyImplementsInstance` for a source-shaped contract. -/
def LocallyImplementsInstance {Error Args Result : Type}
    (own : BitVec 64 → Prop) (entry : BitVec 64) (exit : BitVec 64 → Prop)
    (childSummary : BinaryFv.Binary.Elfling.InstanceId → Nat → Nat → State → State → Prop)
    (contract : FunctionContract Error Args Result) : Prop :=
  OccurrenceContract.LocallyImplementsInstance own entry exit childSummary contract.toOccurrence

/--
**The local-to-closed step, proved.** A `LocallyImplements` whose admitted summaries genuinely
compose inside the enclosing address set is a plain `Implements` there.

This is the lemma the whole boundary layer exists to serve: prove an occurrence against summaries of
its children, then collapse to an address-confined `Implements` once those summaries are discharged
by the children's own proofs. The residual, program-specific obligation is supplying
`SummariesCompose`, which `summaryComposes_of_subtrace` reduces to each child's own `FunctionTrace`.
-/
theorem OccurrenceContract.LocallyImplements.toImplements {Args Outcome : Type}
    {own outer exit : BitVec 64 → Prop} {entry : BitVec 64}
    {childSummary : BinaryFv.Binary.Elfling.InstanceId → Nat → Nat → State → State → Prop}
    {contract : OccurrenceContract Args Outcome}
    (hsub : ∀ pc, own pc → outer pc)
    (hcompose : SummariesCompose outer exit childSummary)
    (h : OccurrenceContract.LocallyImplements own exit entry childSummary contract) :
    OccurrenceContract.Implements outer exit entry contract := by
  intro args fromStep s hpre
  obtain ⟨count, s', hbound, hentered, hpost⟩ := h args fromStep s hpre
  exact ⟨count, s', hbound, hentered.toEnteredFunctionTrace_within hsub hcompose, hpost⟩

/-- The occurrence-shaped local-to-closed step: from the occurrence's local obligation over what it
owns to its closed obligation over where it executes. The premise `hsub` is the generated fact that
an occurrence owns a subset of its own execution extent. -/
theorem OccurrenceContract.LocallyImplementsInstance.toImplementsInstance {Args Outcome : Type}
    {instance_ : BinaryFv.Binary.Elfling.FunctionInstance}
    {own reached : BitVec 64 → Prop} {entry : BitVec 64} {exit : BitVec 64 → Prop}
    {childSummary : BinaryFv.Binary.Elfling.InstanceId → Nat → Nat → State → State → Prop}
    {contract : OccurrenceContract Args Outcome}
    (hsub : ∀ pc, own pc → InstanceExecutionPcs instance_ reached pc)
    (hcompose : SummariesCompose (InstanceExecutionPcs instance_ reached) exit childSummary)
    (h : OccurrenceContract.LocallyImplementsInstance own entry exit childSummary contract) :
    OccurrenceContract.ImplementsInstance instance_ reached entry exit contract :=
  OccurrenceContract.LocallyImplements.toImplements hsub hcompose h

/-- `LocallyImplements.toImplements` for a source-shaped contract. -/
theorem LocallyImplements.toImplements {Error Args Result : Type}
    {own outer exit : BitVec 64 → Prop} {entry : BitVec 64}
    {childSummary : BinaryFv.Binary.Elfling.InstanceId → Nat → Nat → State → State → Prop}
    {contract : FunctionContract Error Args Result}
    (hsub : ∀ pc, own pc → outer pc)
    (hcompose : SummariesCompose outer exit childSummary)
    (h : LocallyImplements own exit entry childSummary contract) :
    Implements outer exit entry contract :=
  OccurrenceContract.LocallyImplements.toImplements hsub hcompose h

end BinaryFv.RiscV.Elfling
