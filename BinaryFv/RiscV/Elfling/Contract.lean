import BinaryFv.RiscV.Elfling.FunctionTrace
import BinaryFv.RiscV.Logic.RegisterAgree
import BinaryFv.RiscV.Logic.ImageMemory

/-!
# Hoare-style contracts for Elfling occurrences

A `FunctionContract` is the handwritten half of the proof. It says what a routine *means* as a
specification-level function, what its caller must establish, what it guarantees, and how many
instructions it may take. `Implements` is the obligation tying that contract to actual generated Sail
execution confined to one occurrence.

Three things are deliberate.

*The error type is a parameter.* Issue #39 writes `meaning : Args → Except DecodeError Result`, but
`BinaryFv.RiscV.DecodeError` already exists and means something unrelated (an ELF word-decode
failure). Parameterizing keeps this layer generic and lets the decoder define its own boundary error
type without a collision.

*`post` sees both states.* Every frame predicate in this codebase is binary — `Agree P before after`,
`imageUnchanged image after` — so a postcondition that only saw the final state could not say
"unrelated memory is preserved" at all.

*`Implements` quantifies over the starting step number.* `Trace`'s step counter is a real obligation
and composition requires the callee's contract to hold at whatever step number the caller reached.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary
open BinaryFv.RiscV

/--
The handwritten specification of one semantic routine.

`meaning` must be a specialized or composed specification operation, never a fresh re-implementation
of the routine's control flow: a hand-rolled mirror of the machine code would always be provable and
would say nothing about the specification.

`stepBound` is an upper bound, so a contract may not be discharged by a run that merely stops
somewhere; `post` is what pins where it stopped and what it produced.
-/
structure FunctionContract (Error Args Result : Type) where
  meaning : Args → Except Error Result
  pre : Args → State → Prop
  post : Args → Except Error Result → State → State → Prop
  stepBound : Args → Nat

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
The obligation that a generated occupancy of instruction space implements a handwritten contract.

Read it as: for every argument tuple, every starting step number, and every state satisfying `pre`,
execution confined to `region` from `entry` reaches a generated exit within `stepBound` steps, and
the resulting states satisfy `post` *at the exact value `meaning` prescribes*.

Using `EnteredFunctionTrace` rather than a bare `FunctionTrace` is what rules out the degenerate
proof in which the machine already sits on an exit and nothing is executed.
-/
def Implements {Error Args Result : Type}
    (region exit : BitVec 64 → Prop) (entry : BitVec 64)
    (contract : FunctionContract Error Args Result) : Prop :=
  ∀ (args : Args) (fromStep : Nat) (s : State),
    contract.pre args s →
      ∃ (count : Nat) (s' : State),
        count ≤ contract.stepBound args ∧
        EnteredFunctionTrace region exit entry fromStep count s s' ∧
        contract.post args (contract.meaning args) s s'

/--
`Implements` for a generated Elfling occurrence: the confinement region is exactly that occurrence's
possibly discontiguous ranges.

This is the single visible seam between the generated, untrusted, address-bearing layer and the
handwritten, address-free contract. The contract argument mentions no address; the occurrence
supplies all of them.
-/
def ImplementsInstance {Error Args Result : Type}
    (instance_ : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop)
    (contract : FunctionContract Error Args Result) : Prop :=
  Implements (RegionPcs instance_.regions) exit entry contract

/--
A contract whose precondition no state satisfies is vacuously implemented.

Sail memory is sparse, so a `pre` must materialize every address the routine touches; it is easy to
write one that is quietly contradictory. Every cataloged routine therefore carries a companion
satisfiability claim, and this is the shape of it.
-/
def PreSatisfiable {Error Args Result : Type} (contract : FunctionContract Error Args Result) : Prop :=
  ∃ (args : Args) (s : State), contract.pre args s

theorem Implements.not_vacuous {Error Args Result : Type}
    {region exit : BitVec 64 → Prop} {entry : BitVec 64}
    {contract : FunctionContract Error Args Result}
    (himpl : Implements region exit entry contract) (hsat : PreSatisfiable contract) :
    ∃ (args : Args) (count : Nat) (s s' : State),
      0 < count ∧ contract.post args (contract.meaning args) s s' := by
  obtain ⟨args, s, hpre⟩ := hsat
  obtain ⟨count, s', _, hentered, hpost⟩ := himpl args 0 s hpre
  exact ⟨args, count, s, s', hentered.count_pos, hpost⟩

end BinaryFv.RiscV.Elfling
