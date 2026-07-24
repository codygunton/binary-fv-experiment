import BinaryFv.RiscV.Elfling.FunctionTrace
import BinaryFv.RiscV.Logic.RegisterAgree
import BinaryFv.RiscV.Logic.ImageMemory

/-!
# Contracts for compiled routine function instances

This file connects source-level intent to RISC-V execution. The important distinction is between a
routine and a function instance of that routine:

- `RoutineSpec` says what the source routine computes. Every emitted or inlined function instance shares
  this meaning.
- `FunctionInstanceBinding` says where one compiled function instance receives its arguments, where it leaves its
  result, and how many instructions it may use. Optimization can give two function instances different
  registers and stack slots.
- `FunctionInstanceContract` pairs those two pieces. `Implements` states that the generated machine trace
  satisfies the pair.

The outcome type is generic because most decoder routines return `Except`, while the exported
wrapper also distinguishes a refused second call. Exit conditions receive both the initial and final
machine state so they can state preservation facts. The starting step number is also explicit so a
callee trace can begin at the exact point reached by its caller.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary
open BinaryFv.RiscV

/--
The source-level meaning shared by every compiled function instance of a routine.

This definition contains no addresses, registers, or step counts. Its `meaning` should be built from
the independent specification, not by restating the machine code.
-/
structure RoutineSpec (Args Outcome : Type) where
  meaning : Args → Outcome

/--
The machine interface for one generated function instance.

- an exported function instance binds the real C ABI and the wrapper's global effects;
- an emitted internal function instance binds its actual optimized ABI (which may drop or reorder source
  arguments);
- an inlined function instance binds its actual entry/exit registers, stack slots, and memory locations.

`entry` describes the required starting state, `exit` relates the start and finish to the expected
outcome, and `stepBound` limits the run.
-/
structure FunctionInstanceBinding (Args Outcome : Type) where
  entry : Args → State → Prop
  exit : Args → Outcome → State → State → Prop
  stepBound : Args → Nat

/--
One function instance's full contract: the shared `RoutineSpec` this function instance realizes, paired with this
function instance's own `FunctionInstanceBinding`.

The spec is what the function instance must *mean*; the binding is *where and how* it means it. Keeping them
as separate fields is what lets many function instances of one routine share a single meaning while each
carries its own machine placement.
-/
structure FunctionInstanceContract (Args Outcome : Type) where
  spec : RoutineSpec Args Outcome
  binding : FunctionInstanceBinding Args Outcome

/--
A source-shaped contract: the special case of a `FunctionInstanceContract` whose outcome is
`Except Error Result` and whose binding is the routine's *source-level* ABI.

Most decoder leaves are cataloged this way because their source ABI is a faithful binding for the
function instance in question. `FunctionContract.toFunctionInstance` projects one into the generic form, so the
function instance-specific bindings (the exported wrapper, deeply inlined function instances) and the source-shaped
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

/-- The (source-shaped) function instance binding of a source-shaped contract. -/
def toBinding (contract : FunctionContract Error Args Result) :
    FunctionInstanceBinding Args (Except Error Result) :=
  { entry := contract.pre, exit := contract.post, stepBound := contract.stepBound }

/-- A source-shaped contract as a generic `FunctionInstanceContract`. This is the single adapter between the
old source-shaped catalog and the function instance-aware obligation. -/
def toFunctionInstance (contract : FunctionContract Error Args Result) :
    FunctionInstanceContract Args (Except Error Result) :=
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
The obligation that a generated occupancy of instruction space implements a function instance contract.

Read it as: for every argument tuple, every starting step number, and every state satisfying the
function instance's `entry` binding, execution confined to `region` from `entry` reaches a generated exit
within `stepBound` steps, and the resulting states satisfy the function instance's `exit` binding *at the
exact outcome `meaning` prescribes*.

Using `EnteredFunctionTrace` rather than a bare `FunctionTrace` is what rules out the degenerate
proof in which the machine already sits on an exit and nothing is executed.
-/
def FunctionInstanceContract.Implements {Args Outcome : Type}
    (region exit : BitVec 64 → Prop) (entry : BitVec 64)
    (contract : FunctionInstanceContract Args Outcome) : Prop :=
  ∀ (args : Args) (fromStep : Nat) (s : State),
    contract.binding.entry args s →
      ∃ (count : Nat) (s' : State),
        count ≤ contract.binding.stepBound args ∧
        EnteredFunctionTrace region exit entry fromStep count s s' ∧
        contract.binding.exit args (contract.spec.meaning args) s s'

/--
`Implements` for a source-shaped `FunctionContract`: it is exactly the function instance obligation on the
projected `FunctionInstanceContract`.

This keeps every source-shaped leaf under the same seam the function instance-specific bindings use, so the
local-to-global composition never has to special-case the two.
-/
def Implements {Error Args Result : Type}
    (region exit : BitVec 64 → Prop) (entry : BitVec 64)
    (contract : FunctionContract Error Args Result) : Prop :=
  FunctionInstanceContract.Implements region exit entry contract.toFunctionInstance

/--
`FunctionInstanceContract.Implements` for a generated Elfling function instance: the confinement region is exactly
that function instance's possibly discontiguous ranges.

This is the single visible seam between the generated, untrusted, address-bearing layer and the
handwritten, address-free contract. The contract argument mentions no address; the function instance
supplies all of them.
-/
def FunctionInstanceContract.ImplementsFunctionInstance {Args Outcome : Type}
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop)
    (contract : FunctionInstanceContract Args Outcome) : Prop :=
  FunctionInstanceContract.Implements (RegionPcs functionInstance.regions) exit entry contract

/--
`Implements` for a generated Elfling function instance of a source-shaped contract.

The name and signature are unchanged from before the meaning/placement split: the catalog still joins
a `FunctionContract` to a function instance through this, and it now routes through the function instance form.
-/
def ImplementsFunctionInstance {Error Args Result : Type}
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop)
    (contract : FunctionContract Error Args Result) : Prop :=
  Implements (RegionPcs functionInstance.regions) exit entry contract

/--
A contract whose entry binding no state satisfies is vacuously implemented.

Sail memory is sparse, so an `entry` must materialize every address the routine touches; it is easy
to write one that is quietly contradictory. Every cataloged routine therefore carries a companion
satisfiability claim, and this is the shape of it.
-/
def FunctionInstanceContract.PreSatisfiable {Args Outcome : Type}
    (contract : FunctionInstanceContract Args Outcome) : Prop :=
  ∃ (args : Args) (s : State), contract.binding.entry args s

/-- `PreSatisfiable` for a source-shaped `FunctionContract`. -/
def PreSatisfiable {Error Args Result : Type} (contract : FunctionContract Error Args Result) : Prop :=
  FunctionInstanceContract.PreSatisfiable contract.toFunctionInstance

theorem FunctionInstanceContract.Implements.not_vacuous {Args Outcome : Type}
    {region exit : BitVec 64 → Prop} {entry : BitVec 64}
    {contract : FunctionInstanceContract Args Outcome}
    (himpl : FunctionInstanceContract.Implements region exit entry contract)
    (hsat : FunctionInstanceContract.PreSatisfiable contract) :
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
  FunctionInstanceContract.Implements.not_vacuous himpl hsat

end BinaryFv.RiscV.Elfling
