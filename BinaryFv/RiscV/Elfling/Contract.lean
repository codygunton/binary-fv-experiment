import BinaryFv.RiscV.Elfling.FunctionTrace
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
`OccurrenceContract.Implements` for a generated Elfling occurrence: the confinement region is exactly
that occurrence's possibly discontiguous ranges.

This is the single visible seam between the generated, untrusted, address-bearing layer and the
handwritten, address-free contract. The contract argument mentions no address; the occurrence
supplies all of them.
-/
def OccurrenceContract.ImplementsInstance {Args Outcome : Type}
    (instance_ : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop)
    (contract : OccurrenceContract Args Outcome) : Prop :=
  OccurrenceContract.Implements (RegionPcs instance_.regions) exit entry contract

/--
`Implements` for a generated Elfling occurrence of a source-shaped contract.

The name and signature are unchanged from before the meaning/placement split: the catalog still joins
a `FunctionContract` to an occurrence through this, and it now routes through the occurrence form.
-/
def ImplementsInstance {Error Args Result : Type}
    (instance_ : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop)
    (contract : FunctionContract Error Args Result) : Prop :=
  Implements (RegionPcs instance_.regions) exit entry contract

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

end BinaryFv.RiscV.Elfling
