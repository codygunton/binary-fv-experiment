import BinaryFv.Binary.Address
import BinaryFv.Binary.Elfling.Source

namespace BinaryFv.Binary.Elfling

open BinaryFv.Binary

/-!
# Generated, address-bearing Elfling occurrences

Everything here is emitted by the deterministic extractor and is therefore *untrusted*. Debug
information only ever proposes a source-to-address mapping; the corresponding Lean validation checks
every range and every byte against the canonical pinned ELF before any proof may rely on it. A wrong
sidecar must be able to make extraction or validation fail, and must never be able to establish a
false semantic result.

Handwritten contracts index by `InstanceId` (address-free). They never mention anything in this
module.
-/

/-- Where a generated fact came from, so a disputed mapping can be traced back to exact inputs.

`sidecarHash` pins the debug-information-bearing object the extractor read, and `entryOffset` is the
byte offset of the originating debug entry inside it. Neither is trusted: both exist so that a
validation failure can be attributed, and so two extractor runs can be compared. -/
structure ExtractionProvenance where
  sidecarHash : String
  entryOffset : Nat
  extractorVersion : String
deriving DecidableEq, Repr, Inhabited

/--
A symbol name that happens to cover part of an instance.

**Annotation only.** In the pinned decoder object, 97% of the bytes carry no symbol at all, so
symbol boundaries cannot define proof regions and nothing may branch on this field being present.
It exists to make generated reports readable.
-/
structure SymbolAnnotation where
  name : String
  range : AddressRange
deriving DecidableEq, Repr

/--
One emitted or inlined occurrence of a source function, as located in the canonical ELF.

`regions` may hold several disjoint ranges: an optimizer routinely splits one source function into
discontiguous fragments, and representing that faithfully is the point of the whole layer. The
regions are the *proposed* extent; `BinaryFv.Binary.Elfling.Validity` is what checks them against
the canonical image.

`children` and `parent?` record nesting exactly as the debug information gave it, using address-free
identities, so the nesting survives relinking.
-/
structure FunctionInstance where
  id : InstanceId
  regions : Array AddressRange
  parent? : Option InstanceId
  children : Array InstanceId
  provenance : ExtractionProvenance
  symbol? : Option SymbolAnnotation
deriving Repr, Inhabited

namespace FunctionInstance

/-- Total instruction bytes attributed to this occurrence across all of its regions. -/
def coveredBytes (instance_ : FunctionInstance) : Nat :=
  instance_.regions.foldl (fun total range => total + range.size) 0

/-- Whether `address` falls inside any region of this occurrence. -/
def containsAddress (instance_ : FunctionInstance) (address : Nat) : Bool :=
  instance_.regions.any fun range => decide (range.start ≤ address ∧ address < range.stop)

/-- Whether this occurrence was split into discontiguous fragments. -/
def isFragmented (instance_ : FunctionInstance) : Bool :=
  instance_.regions.size > 1

end FunctionInstance

/--
An unresolved attribution the extractor must surface rather than discard.

Silently dropping any of these would let a gap in the mapping masquerade as complete coverage, so
the generator emits them as data and validation refuses to certify a program that still carries
unreviewed ones.
-/
inductive AttributionDefect where
  /-- An address inside the analyzed range that no instance claims. -/
  | uncovered (address : Nat)
  /-- Two sibling instances claim the same address; neither is nested in the other. -/
  | overlappingOwnership (address : Nat) (first second : InstanceId)
  /-- Debug information proposed more than one source attribution for the same address. -/
  | ambiguousAttribution (address : Nat) (candidates : List InstanceId)
  /-- A region the extractor could not map to any canonical-ELF instruction boundary. -/
  | unmappedRegion (range : AddressRange)
deriving Repr, Inhabited

/--
A complete extracted program: its entry occurrence, every reachable occurrence, and every
attribution defect found while extracting it.

`defects` being nonempty is not an error in the data; it is an error in the *program's* readiness,
and the validity layer is what refuses it.
-/
structure Program where
  entry : InstanceId
  instances : Array FunctionInstance
  defects : Array AttributionDefect
  provenance : ExtractionProvenance
deriving Repr, Inhabited

namespace Program

/-- Look up an occurrence by its address-free identity. -/
def find? (program : Program) (id : InstanceId) : Option FunctionInstance :=
  program.instances.find? fun instance_ => decide (instance_.id = id)

/-- Every occurrence claiming `address`. More than one entry means either legitimate inline nesting
or an overlapping-ownership defect; `Validity` is what distinguishes them. -/
def instancesAt (program : Program) (address : Nat) : Array FunctionInstance :=
  program.instances.filter fun instance_ => instance_.containsAddress address

/-- The extraction reported no unresolved attributions. -/
def defectFree (program : Program) : Bool :=
  program.defects.isEmpty

end Program

end BinaryFv.Binary.Elfling
