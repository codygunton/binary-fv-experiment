import BinaryFv.Binary.Elfling.FunctionInstance

namespace BinaryFv.Binary.Elfling

/-!
# Extracted Elflings

An `Elfling` collects the function instances extracted from one binary, identifies the entry
function instance, and retains any unresolved attribution defects.
-/

/--
An unresolved attribution the extractor must surface rather than discard.

Silently dropping any of these would let a gap in the mapping masquerade as complete coverage, so
the generator emits them as data and validation refuses to certify a program that still carries
unreviewed ones.
-/
inductive AttributionDefect where
  /-- An address inside the analyzed range that no function instance claims. -/
  | uncovered (address : Nat)
  /-- Two sibling function instances claim the same address; neither is nested in the other. -/
  | overlappingOwnership (address : Nat) (first second : FunctionInstanceId)
  /-- Debug information proposed more than one source attribution for the same address. -/
  | ambiguousAttribution (address : Nat) (candidates : List FunctionInstanceId)
  /-- A region the extractor could not map to any canonical-ELF instruction boundary. -/
  | unmappedRegion (range : AddressRange)
deriving Repr, Inhabited

/--
A complete extracted program: its entry function instance, every reachable function instance, and
every attribution defect found while extracting it.

`defects` being nonempty is not an error in the data; it is an error in the *program's* readiness,
and the validity layer is what refuses it.
-/
structure Elfling where
  entry : FunctionInstanceId
  functionInstances : Array FunctionInstance
  defects : Array AttributionDefect
  provenance : ExtractionProvenance
deriving Repr, Inhabited

namespace Elfling

/-- Look up a function instance by its address-free identity. -/
def find? (program : Elfling) (id : FunctionInstanceId) : Option FunctionInstance :=
  program.functionInstances.find? fun functionInstance => decide (functionInstance.id = id)

/-- Every function instance claiming `address`. More than one entry means either legitimate inline nesting
or an overlapping-ownership defect; `Validity` is what distinguishes them. -/
def functionInstancesAt (program : Elfling) (address : Nat) : Array FunctionInstance :=
  program.functionInstances.filter fun functionInstance => functionInstance.containsAddress address

/-- The extraction reported no unresolved attributions. -/
def defectFree (program : Elfling) : Bool :=
  program.defects.isEmpty

/-- No two distinct function instances share an identity.

A `FunctionInstanceId` is a routine plus its inline call stack, so this forbids the extractor
emitting the same function instance twice — the failure mode that would let a duplicated function
instance pass unnoticed and be double-counted by any per-function-instance obligation. -/
def functionInstanceIdsDistinct (program : Elfling) : Prop :=
  ∀ i j, (hi : i < program.functionInstances.size) → (hj : j < program.functionInstances.size) →
    (program.functionInstances[i]).id = (program.functionInstances[j]).id → i = j

end Elfling

end BinaryFv.Binary.Elfling
