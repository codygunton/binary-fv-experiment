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
A basic block: a maximal straight-line run of decoded instructions, as a single contiguous address
range that stays inside one of the owning occurrence's fragments.

Generated, address-bearing, and therefore *untrusted*: the validation checks that an occurrence's
blocks exactly partition its regions and that every block byte is a decoded instruction in the
canonical CFG. It carries no classification — which edges leave a block, and what kind they are, is a
separate concern proved against the decoded control-flow graph.
-/
structure BasicBlock where
  range : AddressRange
deriving DecidableEq, Repr, Inhabited

/--
A direct control-flow edge between two decoded instruction addresses, as proposed by the extractor.

Generated and *untrusted*: the validation checks each edge is a real decoded direct successor in the
canonical CFG (`target ∈ directSuccessorsAt nodes source`). It is deliberately unlabelled — whether an
edge is internal, an inline child entry, a resolved call, a return, or an occurrence exit is a
classification proved separately, not asserted by the generator.
-/
structure DirectEdge where
  source : Nat
  target : Nat
deriving DecidableEq, Repr, Inhabited

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
  /-- The address at which this occurrence is entered. A per-instance contract obligation reads its
  entry PC from here rather than guessing it from a region boundary, so the obligation is fully
  determined by the generated data and never existentially quantified. -/
  entryPc : Nat
  /-- The generated exit addresses: returns and tail-calls that leave this occurrence. The
  confinement predicate a `FunctionTrace` runs against is derived from these, so a proof cannot pick
  a convenient exit. -/
  exitPcs : Array Nat
  parent? : Option InstanceId
  children : Array InstanceId
  /-- Resolved calls that leave this occurrence to another occurrence. The local-to-global
  composition walks these edges. -/
  externalCalls : Array InstanceId
  /-- Basic blocks partitioning this occurrence's regions: a maximal straight-line run per block,
  contiguous and confined to one fragment. Emitted by the generator; the validation checks they tile
  the regions exactly and every block byte decodes. Defaults to `#[]` for hand-written occurrences
  that do not carry a block partition. -/
  blocks : Array BasicBlock := #[]
  /-- Direct control-flow edges out of this occurrence's instructions, as proposed by the extractor.
  The validation checks each is a real decoded direct successor. Defaults to `#[]`. -/
  edges : Array DirectEdge := #[]
  /-- Validated source provenance: the pinned source file's content hash and the declaration's
  location. The generator fills this from debug information; the extraction row validates it against
  the pinned source. It is separate from `id` (stable identity) so a wrong hash fails validation
  rather than breaking identity matching. -/
  declProvenance : DeclarationProvenance
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

/-- The entry address as a machine word. -/
def entryWord (instance_ : FunctionInstance) : Nat := instance_.entryPc

/-- The exit predicate a `FunctionTrace` for this occurrence runs against: exactly the generated
exit addresses, so it is determined by the data rather than chosen. -/
def isExit (instance_ : FunctionInstance) (address : Nat) : Prop :=
  address ∈ instance_.exitPcs

/-- The entry address lies inside one of the occurrence's regions. A well-formed occurrence
satisfies this; it is what lets the entered-trace obligation start in region. -/
def entryInRegions (instance_ : FunctionInstance) : Prop :=
  ∃ range ∈ instance_.regions, range.start ≤ instance_.entryPc ∧ instance_.entryPc < range.stop

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

/-- No two distinct occurrences share an identity.

An `InstanceId` is a routine plus its inline call stack, so this forbids the extractor emitting the
same occurrence twice — the failure mode that would let a duplicated instance pass unnoticed and be
double-counted by any per-instance obligation. -/
def instanceIdsDistinct (program : Program) : Prop :=
  ∀ i j, (hi : i < program.instances.size) → (hj : j < program.instances.size) →
    (program.instances[i]).id = (program.instances[j]).id → i = j

end Program

end BinaryFv.Binary.Elfling
