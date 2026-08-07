import BinaryFv.Binary.Address
import BinaryFv.Binary.Elfling.Source

namespace BinaryFv.Binary.Elfling

open BinaryFv.Binary

/-!
# Data model for compiled Elfling function instances

This file is handwritten. It defines the architecture-independent types used to describe how source
functions appear in a compiled binary; it does not contain a generated description of any particular
binary.

A **function instance** is one compiled appearance of a source function. The compiler may leave a
function as a separately callable body, inline it into one or more callers, or split one appearance
across discontiguous address ranges. `FunctionInstance` records one such appearance.

The deterministic extractor creates address-bearing values of these types for a particular binary.
Those values are *untrusted*: debug information only proposes a source-to-address mapping, and Lean
validation checks every range and byte against the pinned ELF before a proof may rely on it. A wrong
sidecar must make extraction or validation fail; it must never establish a false semantic result.

Handwritten contracts use the address-free `FunctionInstanceId` to select a function instance. Concrete addresses
enter later through extracted `FunctionInstance` and `Program` values.
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
A symbol name that happens to cover part of a function instance.

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
range that stays inside one of the owning function instance's fragments.

Generated, address-bearing, and therefore *untrusted*: the validation checks that a function instance's
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
edge is internal, an inline child entry, a resolved call, a return, or a function instance exit is a
classification proved separately, not asserted by the generator.
-/
structure DirectEdge where
  source : Nat
  target : Nat
deriving DecidableEq, Repr, Inhabited

/--
One emitted or inlined function instance of a source function, as located in the canonical ELF.

`regions` may hold several disjoint ranges: an optimizer routinely splits one source function into
discontiguous fragments, and representing that faithfully is the point of the whole layer. The
regions are the *proposed* extent; `BinaryFv.Binary.Elfling.Validity` is what checks them against
the canonical image.

`children` and `parent?` record nesting exactly as the debug information gave it, using address-free
identities, so the nesting survives relinking.
-/
structure FunctionInstance where
  id : FunctionInstanceId
  regions : Array AddressRange
  /-- The address at which this function instance is entered. A per-function-instance contract obligation reads its
  entry PC from here rather than guessing it from a region boundary, so the obligation is fully
  determined by the generated data and never existentially quantified. -/
  entryPc : Nat
  /-- The generated exit addresses: returns and tail-calls that leave this function instance. The
  confinement predicate a `FunctionTrace` runs against is derived from these, so a proof cannot pick
  a convenient exit. -/
  exitPcs : Array Nat
  parent? : Option FunctionInstanceId
  children : Array FunctionInstanceId
  /-- Resolved calls that leave this function instance to another function instance. The local-to-global
  composition walks these edges. -/
  externalCalls : Array FunctionInstanceId
  /-- Basic blocks partitioning this function instance's regions: a maximal straight-line run per block,
  contiguous and confined to one fragment. Emitted by the generator; the validation checks they tile
  the regions exactly and every block byte decodes. Defaults to `#[]` for hand-written function instances
  that do not carry a block partition. -/
  blocks : Array BasicBlock := #[]
  /-- Direct control-flow edges out of this function instance's instructions, as proposed by the extractor.
  The validation checks each is a real decoded direct successor. Defaults to `#[]`. -/
  edges : Array DirectEdge := #[]
  /-- Validated source provenance: the pinned source file's content hash and the declaration's
  location. The generator fills this from debug information; generated-program validation checks it against
  the pinned source. It is separate from `id` (stable identity) so a wrong hash fails validation
  rather than breaking identity matching. -/
  declProvenance : DeclarationProvenance
  provenance : ExtractionProvenance
  symbol? : Option SymbolAnnotation
deriving Repr, Inhabited

namespace FunctionInstance

/-- Total instruction bytes attributed to this function instance across all of its regions. -/
def coveredBytes (functionInstance : FunctionInstance) : Nat :=
  functionInstance.regions.foldl (fun total range => total + range.size) 0

/-- Whether `address` falls inside any region of this function instance. -/
def containsAddress (functionInstance : FunctionInstance) (address : Nat) : Bool :=
  functionInstance.regions.any fun range => decide (range.start ≤ address ∧ address < range.stop)

/-- Whether this function instance was split into discontiguous fragments. -/
def isFragmented (functionInstance : FunctionInstance) : Bool :=
  functionInstance.regions.size > 1

/-- The entry address as a machine word. -/
def entryWord (functionInstance : FunctionInstance) : Nat := functionInstance.entryPc

/-- The exit predicate a `FunctionTrace` for this function instance runs against: exactly the generated
exit addresses, so it is determined by the data rather than chosen. -/
def isExit (functionInstance : FunctionInstance) (address : Nat) : Prop :=
  address ∈ functionInstance.exitPcs

/-- The entry address lies inside one of the function instance's regions. A well-formed function instance
satisfies this; it is what lets the entered-trace obligation start in region. -/
def entryInRegions (functionInstance : FunctionInstance) : Prop :=
  ∃ range ∈ functionInstance.regions, range.start ≤ functionInstance.entryPc ∧ functionInstance.entryPc < range.stop

end FunctionInstance

end BinaryFv.Binary.Elfling
