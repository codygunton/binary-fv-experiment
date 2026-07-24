import BinaryFv.Binary.Address
import BinaryFv.Binary.Elfling.Source

namespace BinaryFv.Binary.Elfling

open BinaryFv.Binary

/-!
# Data model for compiled Elfling occurrences

This file is handwritten. It defines the architecture-independent types used to describe how source
functions appear in a compiled binary; it does not contain a generated description of any particular
binary.

A **function occurrence** is one compiled appearance of a source function. The compiler may leave a
function as a separately callable body, inline it into one or more callers, or split one appearance
across discontiguous address ranges. `FunctionInstance` records one such appearance.

The deterministic extractor creates address-bearing values of these types for a particular binary.
Those values are *untrusted*: debug information only proposes a source-to-address mapping, and Lean
validation checks every range and byte against the pinned ELF before a proof may rely on it. A wrong
sidecar must make extraction or validation fail; it must never establish a false semantic result.

Handwritten contracts use the address-free `InstanceId` to select an occurrence. Concrete addresses
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
A reachable emitted routine that no catalog entry covers.

These are real code — the extraction's reachable partition proves every reachable pc is either
covered by an occurrence or one of these — reached through `externalCalls` like any other callee.
They are surfaced rather than dropped precisely so that a gap in the catalog cannot masquerade as
complete coverage.

An excluded routine has no contract of its own, so it has no summary to splice. The occurrence that
calls it therefore **absorbs** it: the excluded routine's pcs join the calling occurrence's owned
address set, and the caller's own proof accounts for its execution. That is the only placement that
keeps the per-occurrence obligation count honest without inventing a contract for uncataloged code.
-/
structure ExcludedOccurrence where
  id : InstanceId
  qualifiedName : String
  category : String
  regions : Array AddressRange
deriving Repr, Inhabited, DecidableEq

/--
A complete extracted program: its entry occurrence, every reachable occurrence, every reachable
routine deliberately left uncataloged, and every attribution defect found while extracting it.

`defects` being nonempty is not an error in the data; it is an error in the *program's* readiness,
and the validity layer is what refuses it.

`excluded` defaults to `#[]` so a program written by hand (the boundary tests, the vertical slice)
need not mention it; the generator emits the real inventory.
-/
structure Program where
  entry : InstanceId
  instances : Array FunctionInstance
  defects : Array AttributionDefect
  provenance : ExtractionProvenance
  /-- Reachable emitted routines that carry no catalog entry, absorbed by their callers. -/
  excluded : Array ExcludedOccurrence := #[]
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

/-! ## The transfer graph and the address sets it induces

An occurrence's contract cannot be about its own instructions alone. When it calls another
occurrence, the machine executes the callee's instructions; when it calls a routine the catalog
deliberately excludes, it executes that routine's instructions too. A confinement predicate built
only from `regions` therefore describes a run that does not exist, and the corresponding obligation
is unsatisfiable for every occurrence that transfers control.

Two address sets fix this, both computed here from generated data so that no proof may choose them:

* **owned** — the occurrence's own regions plus the regions of the excluded routines it absorbs.
  This is what its *local* proof may retire step by step, and it is deliberately the smaller set: an
  occurrence may not wander into a callee it has a summary for.
* **extent** — owned, plus the same for everything reachable in the transfer graph. This is what its
  *closed* obligation confines execution to, and it is exactly as large as the code the occurrence
  can actually reach.

The closure is fuel-bounded by the size of the program, deduplicated, and stops early at a fixed
point, so it is a total, decidable function a kernel evaluation can settle. -/

/-- The occurrences and excluded routines control may transfer to directly: inlined children and
resolved external calls. -/
def transferIds (instance_ : FunctionInstance) : Array InstanceId :=
  instance_.children ++ instance_.externalCalls

/-- The regions attributed to one identity, whether it names an occurrence or an excluded routine.
An identity naming neither owns nothing. -/
def rangesOf (program : Program) (id : InstanceId) : Array AddressRange :=
  match program.find? id with
  | some instance_ => instance_.regions
  | none =>
      match program.excluded.find? (fun x => decide (x.id = id)) with
      | some excluded => excluded.regions
      | none => #[]

/-- The excluded routines an occurrence absorbs: those it calls directly. They carry no contract, so
no summary can be spliced for them and the calling occurrence's own proof owes their execution. -/
def absorbedRanges (program : Program) (instance_ : FunctionInstance) : Array AddressRange :=
  program.excluded.foldl
    (fun acc excluded =>
      if (transferIds instance_).any (fun id => decide (id = excluded.id)) then acc ++ excluded.regions
      else acc)
    #[]

/-- What an occurrence's *local* proof owns: its own regions plus the excluded routines it absorbs. -/
def ownedRanges (program : Program) (instance_ : FunctionInstance) : Array AddressRange :=
  instance_.regions ++ absorbedRanges program instance_

/-- **Absorption requires a genuine transfer edge.** Every region an occurrence absorbs belongs to
an excluded routine the occurrence lists as a transfer target — so absorption can only pull in code
the occurrence actually calls or inlines, never arbitrary code. This is what stops the owned set
from quietly claiming ordinary uncovered code: an excluded routine the occurrence does not transfer
to contributes nothing. -/
theorem absorbed_requires_transfer (program : Program) (instance_ : FunctionInstance)
    (range : AddressRange) (h : range ∈ absorbedRanges program instance_) :
    ∃ x ∈ program.excluded,
      (transferIds instance_).any (fun id => decide (id = x.id)) = true ∧ range ∈ x.regions := by
  unfold absorbedRanges at h
  have gen : ∀ (l : List ExcludedOccurrence) (acc : Array AddressRange),
      range ∈ l.foldl (fun acc excluded =>
          if (transferIds instance_).any (fun id => decide (id = excluded.id))
          then acc ++ excluded.regions else acc) acc →
      range ∈ acc ∨ ∃ x ∈ l, (transferIds instance_).any (fun id => decide (id = x.id)) = true
          ∧ range ∈ x.regions := by
    intro l
    induction l with
    | nil => intro acc hacc; exact Or.inl hacc
    | cons hd tl ih =>
      intro acc hacc
      simp only [List.foldl_cons] at hacc
      rcases ih _ hacc with hrec | ⟨x, hx, hcond, hxr⟩
      · by_cases hp : (transferIds instance_).any (fun id => decide (id = hd.id)) = true
        · simp only [hp, if_true] at hrec
          rcases Array.mem_append.mp hrec with hl | hr
          · exact Or.inl hl
          · exact Or.inr ⟨hd, List.mem_cons_self, hp, hr⟩
        · simp only [Bool.not_eq_true] at hp
          simp only [hp, Bool.false_eq_true, if_false] at hrec
          exact Or.inl hrec
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hcond, hxr⟩
  rw [← Array.foldl_toList] at h
  rcases gen program.excluded.toList #[] h with hempty | ⟨x, hx, hcond, hxr⟩
  · exact absurd hempty (by simp)
  · exact ⟨x, Array.mem_iff_getElem.mpr (by
      obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hx
      exact ⟨n, by simpa using hn, by simpa using hget⟩), hcond, hxr⟩

/-- One expansion round of the transfer graph, deduplicated. -/
def expandTransfers (program : Program) (ids : Array InstanceId) : Array InstanceId :=
  ids.foldl
    (fun acc id =>
      match program.find? id with
      | some instance_ =>
          (transferIds instance_).foldl
            (fun acc callee => if acc.any (fun x => decide (x = callee)) then acc else acc.push callee)
            acc
      | none => acc)
    ids

/-- Fuel-bounded transfer closure, stopping at the first fixed point. -/
def transferClosureAux (program : Program) : Nat → Array InstanceId → Array InstanceId
  | 0, ids => ids
  | fuel + 1, ids =>
      let next := expandTransfers program ids
      if next.size = ids.size then ids else transferClosureAux program fuel next

/-- Every identity reachable from `id` in the transfer graph, including `id` itself. The fuel is the
number of identities the program can possibly name, so the closure is complete. -/
def transferClosure (program : Program) (id : InstanceId) : Array InstanceId :=
  transferClosureAux program (program.instances.size + program.excluded.size) #[id]

/-- Every address an occurrence's execution may occupy: what it owns, plus what everything it may
transfer to owns. -/
def extentRanges (program : Program) (instance_ : FunctionInstance) : Array AddressRange :=
  (transferClosure program instance_.id).foldl
    (fun acc id =>
      match program.find? id with
      | some callee => acc ++ ownedRanges program callee
      | none => acc ++ rangesOf program id)
    #[]

/-- Whether `inner` covers no address `outer` does not, checked range by range.

Sufficient rather than exact — it asks each inner range to sit inside a *single* outer range — which
is all the geometry needs, because both sides are unions of the same atomic occurrence ranges. Being
a `Bool`, it is what makes the geometry facts a decidable check on the generated program instead of
an assumption. -/
def rangesSubsume (outer inner : Array AddressRange) : Bool :=
  inner.all fun r => outer.any fun o => decide (o.start ≤ r.start ∧ r.stop ≤ o.stop)

/-- Whether `address` lies in one of the ranges. -/
def inRanges (ranges : Array AddressRange) (address : Nat) : Bool :=
  ranges.any fun r => decide (r.start ≤ address ∧ address < r.stop)

end Program

end BinaryFv.Binary.Elfling
