import BinaryFv.Binary.Elfling.FunctionInstance

namespace BinaryFv.Binary.Elfling

open BinaryFv.Binary

/--
An unresolved attribution the extractor must surface rather than discard.

Silently dropping any of these would let a gap in the mapping masquerade as complete coverage, so
the generator emits them as data and validation refuses to certify a program that still carries
unreviewed ones.
-/
inductive AttributionDefect where
  /-- An address inside the analyzed range that no function instance claims. -/
  | uncovered (address : Nat)
  /-- Two sibling instances claim the same address; neither is nested in the other. -/
  | overlappingOwnership (address : Nat) (first second : FunctionInstanceId)
  /-- Debug information proposed more than one source attribution for the same address. -/
  | ambiguousAttribution (address : Nat) (candidates : List FunctionInstanceId)
  /-- A region the extractor could not map to any canonical-ELF instruction boundary. -/
  | unmappedRegion (range : AddressRange)
deriving Repr, Inhabited

namespace Program

/--
A reachable emitted routine that no catalog entry covers.

These are real code — the extraction's reachable partition proves every reachable pc is either
covered by a function instance or one of these — reached through `externalCalls` like any other callee.
They are surfaced rather than dropped precisely so that a gap in the catalog cannot masquerade as
complete coverage.

An excluded routine has no contract of its own, so it has no summary to splice. The function instance that
calls it therefore **absorbs** it: the excluded routine's pcs join the calling function instance's owned
address set, and the caller's own proof accounts for its execution. That is the only placement that
keeps the per-function-instance obligation count honest without inventing a contract for uncataloged code.
-/
structure ExcludedFunctionInstance where
  id : FunctionInstanceId
  qualifiedName : String
  category : String
  regions : Array AddressRange
deriving Repr, Inhabited, DecidableEq

end Program

/--
A complete extracted program: its entry function instance, every reachable function instance, every reachable
routine deliberately left uncataloged, and every attribution defect found while extracting it.

`defects` being nonempty is not an error in the data; it is an error in the *program's* readiness,
and the validity layer is what refuses it.

`excludedFunctionInstances` defaults to `#[]` so a program written by hand (the boundary tests, the vertical slice)
need not mention it; the generator emits the real inventory.
-/
structure Program where
  entry : FunctionInstanceId
  functionInstances : Array FunctionInstance
  defects : Array AttributionDefect
  provenance : ExtractionProvenance
  /-- Reachable emitted routines that carry no catalog entry, absorbed by their callers. -/
  excludedFunctionInstances : Array Program.ExcludedFunctionInstance := #[]
deriving Repr, Inhabited

namespace Program

/-! Compatibility projections for retained pre-migration consumers. -/

abbrev instances (program : Program) : Array FunctionInstance := program.functionInstances

/-- Look up a function instance by its address-free identity. -/
def find? (program : Program) (id : FunctionInstanceId) : Option FunctionInstance :=
  program.functionInstances.find? fun functionInstance => decide (functionInstance.id = id)

/-- Every function instance claiming `address`. More than one entry means either legitimate inline nesting
or an overlapping-ownership defect; `Validity` is what distinguishes them. -/
def functionInstancesAt (program : Program) (address : Nat) : Array FunctionInstance :=
  program.functionInstances.filter fun functionInstance => functionInstance.containsAddress address

/-- The extraction reported no unresolved attributions. -/
def defectFree (program : Program) : Bool :=
  program.defects.isEmpty

/-- No two distinct function instances share an identity.

An `FunctionInstanceId` is a routine plus its inline call stack, so this forbids the extractor emitting the
same function instance twice — the failure mode that would let a duplicated function instance pass unnoticed and be
double-counted by any per-function-instance obligation. -/
def functionInstanceIdsDistinct (program : Program) : Prop :=
  ∀ i j, (hi : i < program.functionInstances.size) → (hj : j < program.functionInstances.size) →
    (program.functionInstances[i]).id = (program.functionInstances[j]).id → i = j

abbrev instanceIdsDistinct (program : Program) : Prop := program.functionInstanceIdsDistinct

/-! ## The transfer graph and the address sets it induces

A function instance's contract cannot be about its own instructions alone. When it calls another
function instance, the machine executes the callee's instructions; when it calls a routine the catalog
deliberately excludes, it executes that routine's instructions too. A confinement predicate built
only from `regions` therefore describes a run that does not exist, and the corresponding obligation
is unsatisfiable for every function instance that transfers control.

Two address sets fix this, both computed here from generated data so that no proof may choose them:

* **owned** — the function instance's own regions plus the regions of the excluded routines it absorbs.
  This is what its *local* proof may retire step by step, and it is deliberately the smaller set: an
  function instance may not wander into a callee it has a summary for.
* **extent** — owned, plus the same for everything reachable in the transfer graph. This is what its
  *closed* obligation confines execution to, and it is exactly as large as the code the function instance
  can actually reach.

The closure is fuel-bounded by the size of the program, deduplicated, and stops early at a fixed
point, so it is a total, decidable function a kernel evaluation can settle. -/

/-- The function instances and excluded routines control may transfer to directly: inlined children and
resolved external calls. -/
def transferIds (functionInstance : FunctionInstance) : Array FunctionInstanceId :=
  functionInstance.children ++ functionInstance.externalCalls

/-- The regions attributed to one identity, whether it names a function instance or an excluded routine.
An identity naming neither owns nothing. -/
def rangesOf (program : Program) (id : FunctionInstanceId) : Array AddressRange :=
  match program.find? id with
  | some functionInstance => functionInstance.regions
  | none =>
      match program.excludedFunctionInstances.find? (fun x => decide (x.id = id)) with
      | some excluded => excluded.regions
      | none => #[]

/-- The excluded routines a function instance absorbs: those it calls directly. They carry no contract, so
no summary can be spliced for them and the calling function instance's own proof owes their execution. -/
def absorbedRanges (program : Program) (functionInstance : FunctionInstance) : Array AddressRange :=
  program.excludedFunctionInstances.foldl
    (fun acc excluded =>
      if (transferIds functionInstance).any (fun id => decide (id = excluded.id)) then acc ++ excluded.regions
      else acc)
    #[]

/-- What a function instance's *local* proof owns: its own regions plus the excluded routines it absorbs. -/
def ownedRanges (program : Program) (functionInstance : FunctionInstance) : Array AddressRange :=
  functionInstance.regions ++ absorbedRanges program functionInstance

/-- **Absorption requires a genuine transfer edge.** Every region a function instance absorbs belongs to
an excluded routine the function instance lists as a transfer target — so absorption can only pull in code
the function instance actually calls or inlines, never arbitrary code. This is what stops the owned set
from quietly claiming ordinary uncovered code: an excluded routine the function instance does not transfer
to contributes nothing. -/
theorem absorbed_requires_transfer (program : Program) (functionInstance : FunctionInstance)
    (range : AddressRange) (h : range ∈ absorbedRanges program functionInstance) :
    ∃ x ∈ program.excludedFunctionInstances,
      (transferIds functionInstance).any (fun id => decide (id = x.id)) = true ∧ range ∈ x.regions := by
  unfold absorbedRanges at h
  have gen : ∀ (l : List Program.ExcludedFunctionInstance) (acc : Array AddressRange),
      range ∈ l.foldl (fun acc excluded =>
          if (transferIds functionInstance).any (fun id => decide (id = excluded.id))
          then acc ++ excluded.regions else acc) acc →
      range ∈ acc ∨ ∃ x ∈ l, (transferIds functionInstance).any (fun id => decide (id = x.id)) = true
          ∧ range ∈ x.regions := by
    intro l
    induction l with
    | nil => intro acc hacc; exact Or.inl hacc
    | cons hd tl ih =>
      intro acc hacc
      simp only [List.foldl_cons] at hacc
      rcases ih _ hacc with hrec | ⟨x, hx, hcond, hxr⟩
      · by_cases hp : (transferIds functionInstance).any (fun id => decide (id = hd.id)) = true
        · simp only [hp, if_true] at hrec
          rcases Array.mem_append.mp hrec with hl | hr
          · exact Or.inl hl
          · exact Or.inr ⟨hd, List.mem_cons_self, hp, hr⟩
        · simp only [Bool.not_eq_true] at hp
          simp only [hp, Bool.false_eq_true, if_false] at hrec
          exact Or.inl hrec
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hcond, hxr⟩
  rw [← Array.foldl_toList] at h
  rcases gen program.excludedFunctionInstances.toList #[] h with hempty | ⟨x, hx, hcond, hxr⟩
  · exact absurd hempty (by simp)
  · exact ⟨x, Array.mem_iff_getElem.mpr (by
      obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hx
      exact ⟨n, by simpa using hn, by simpa using hget⟩), hcond, hxr⟩

/-- One expansion round of the transfer graph, deduplicated. -/
def expandTransfers (program : Program) (ids : Array FunctionInstanceId) : Array FunctionInstanceId :=
  ids.foldl
    (fun acc id =>
      match program.find? id with
      | some functionInstance =>
          (transferIds functionInstance).foldl
            (fun acc callee => if acc.any (fun x => decide (x = callee)) then acc else acc.push callee)
            acc
      | none => acc)
    ids

/-- Fuel-bounded transfer closure, stopping at the first fixed point. -/
def transferClosureAux (program : Program) : Nat → Array FunctionInstanceId → Array FunctionInstanceId
  | 0, ids => ids
  | fuel + 1, ids =>
      let next := expandTransfers program ids
      if next.size = ids.size then ids else transferClosureAux program fuel next

/-- Every identity reachable from `id` in the transfer graph, including `id` itself. The fuel is the
number of identities the program can possibly name, so the closure is complete. -/
def transferClosure (program : Program) (id : FunctionInstanceId) : Array FunctionInstanceId :=
  transferClosureAux program (program.functionInstances.size + program.excludedFunctionInstances.size) #[id]

/-- Every address a function instance's execution may occupy: what it owns, plus what everything it may
transfer to owns. -/
def extentRanges (program : Program) (functionInstance : FunctionInstance) : Array AddressRange :=
  (transferClosure program functionInstance.id).foldl
    (fun acc id =>
      match program.find? id with
      | some callee => acc ++ ownedRanges program callee
      | none => acc ++ rangesOf program id)
    #[]

/-- Whether `inner` covers no address `outer` does not, checked range by range.

Sufficient rather than exact — it asks each inner range to sit inside a *single* outer range — which
is all the geometry needs, because both sides are unions of the same atomic function instance ranges. Being
a `Bool`, it is what makes the geometry facts a decidable check on the generated program instead of
an assumption. -/
def rangesSubsume (outer inner : Array AddressRange) : Bool :=
  inner.all fun r => outer.any fun o => decide (o.start ≤ r.start ∧ r.stop ≤ o.stop)

/-- Whether `address` lies in one of the ranges. -/
def inRanges (ranges : Array AddressRange) (address : Nat) : Bool :=
  ranges.any fun r => decide (r.start ≤ address ∧ address < r.stop)

end Program

end BinaryFv.Binary.Elfling
