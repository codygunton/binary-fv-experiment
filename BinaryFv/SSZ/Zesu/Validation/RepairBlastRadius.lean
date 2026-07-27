import BinaryFv.SSZ.Zesu.Elfling.BindingInventory
import BinaryFv.SSZ.Zesu.Elfling.GeneratedProgramEdgeClass
import BinaryFv.SSZ.Zesu.Elfling.ManifestCheck
import BinaryFv.SSZ.Zesu.Contracts.ProgramCorrectness
import BinaryFv.SSZ.Zesu.Validation.BoundarySatisfiability

/-!
# Row D½ repair blast radius

This module pins the populations behind the three human rulings that follow the local-obligation
ledger. It does not repair the extractor, change a contract, or turn a red measurement into a gate:
it asks what each proposed repair would preserve, discard, or leave broken against the current
generated program.

The measurements deliberately join data to the predicates that consume it:

* the `preReadAt` population is selected by the six handwritten catalog tags whose contracts use
  that predicate, then joined to the effective Row A `offset` bindings;
* entry/exit alternatives are evaluated with `Boundary.entryIsOwnExit`, the exact condition that
  contradicts `EnteredScopedTrace.entryNotExit`;
* inline inventory measurements retain `Boundary.crossesIn`/`crossesOut`, while consumer-shaped
  measurements additionally require an exact child-entry target and `InlineTransfer.exitNotExit`.
* the resolved-call inventory is joined to the seven remaining source-is-exit tail calls and their
  common `memcpy` target; the ledger consumer separately pins that they are informational.

All findings are exact red pins. A future artifact change must move a theorem statement; it must not
silently make this file "green".
-/

namespace BinaryFv.SSZ.Zesu.Validation.RepairBlastRadius

set_option maxRecDepth 8000

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.ControlFlow (controlFlow?)
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling.Generated
  (generatedManifest generatedProgram ManifestRow)
open BinaryFv.SSZ.Zesu.Elfling.GeneratedBindings (bindings)
open BinaryFv.SSZ.Zesu.Elfling.Validation
  (ancestorIds callRows deepestOwner? nonExitCallRows regionPcList)

/-! ## Ruling 1 — source ABI versus occurrence-local entry bindings -/

/-- Exactly the catalog tags whose handwritten contract precondition is `preReadAt`. The names come
from `RoutineTag.name`, not an extractor-local spelling table. -/
def preReadAtTagNames : List String :=
  [RoutineTag.readU32, .readU64, .readOffset, .readU256, .bytesAt, .readArray].map
    RoutineTag.name

/-- The six selected catalog branches really dispatch to the handwritten `preReadAt` predicate.
These definitional checks are the consumer-side half of the join: counting six generated tag
strings without checking what their contracts use would only validate the manifest against itself. -/
theorem readU32_entry_binding_is_preReadAt (p : ContractParams) (function : FunctionId) :
    (routineContract p function .readU32).contract.binding.entry = preReadAt p.env := rfl

theorem readU64_entry_binding_is_preReadAt (p : ContractParams) (function : FunctionId) :
    (routineContract p function .readU64).contract.binding.entry = preReadAt p.env := rfl

theorem readOffset_entry_binding_is_preReadAt (p : ContractParams) (function : FunctionId) :
    (routineContract p function .readOffset).contract.binding.entry = preReadAt p.env := rfl

theorem readU256_entry_binding_is_preReadAt (p : ContractParams) (function : FunctionId) :
    (routineContract p function .readU256).contract.binding.entry =
      fun args => preReadAt p.env args.toReadAtArgs := rfl

theorem bytesAt_entry_binding_is_preReadAt (p : ContractParams) (function : FunctionId) :
    (routineContract p function .bytesAt).contract.binding.entry =
      fun args => preReadAt p.env args.toReadAtArgs := rfl

theorem readArray_entry_binding_is_preReadAt (p : ContractParams) (function : FunctionId) :
    (routineContract p function .readArray).contract.binding.entry =
      fun args => preReadAt p.env args.toReadAtArgs := rfl

def usesPreReadAt (row : ManifestRow) : Bool :=
  preReadAtTagNames.contains row.routineTag

def preReadAtManifestRows : Array ManifestRow :=
  generatedManifest.filter usesPreReadAt

/-- The effective Row A `offset` bindings belonging to a contract occurrence that uses
`preReadAt`. This is a join of the generated manifest and binding table, not a count of either
table in isolation. -/
def preReadAtOffsetBindings : List (Nat × String × String × Int × Int) :=
  bindings.filter fun binding =>
    binding.2.1 == "offset" &&
      match generatedManifest[binding.1]? with
      | some row => usesPreReadAt row
      | none => false

def offsetBindingCount (index : Nat) : Nat :=
  (bindings.filter fun binding =>
    binding.1 == index && binding.2.1 == "offset").length

/-- **108 contract occurrences use `preReadAt`; all 108 are inlined, and each joins to exactly one
effective `offset` binding.** This is the affected population. It is not the captured-run failure
count: that independent check reaches 102 rows and refutes the `x12` clause on 100 of them. -/
theorem preReadAt_population_and_binding_join :
    preReadAtManifestRows.size = 108 ∧
      preReadAtManifestRows.all (fun row => row.kind == "inlined") = true ∧
      preReadAtOffsetBindings.length = 108 ∧
      preReadAtManifestRows.all (fun row => offsetBindingCount row.index == 1) = true := by
  native_decide

/-- The effective offsets are 68 constants, 19 register-plus-constant values, 13 direct registers,
and 8 loop-derived values. No other binding kind occurs in this population. -/
theorem preReadAt_offset_binding_kinds :
    (preReadAtOffsetBindings.filter fun row => row.2.2.1 == "const").length = 68 ∧
      (preReadAtOffsetBindings.filter fun row => row.2.2.1 == "bregValue").length = 19 ∧
      (preReadAtOffsetBindings.filter fun row => row.2.2.1 == "reg").length = 13 ∧
      (preReadAtOffsetBindings.filter fun row => row.2.2.1 == "derived").length = 8 ∧
      preReadAtOffsetBindings.all (fun row =>
        ["const", "bregValue", "reg", "derived"].contains row.2.2.1) = true := by
  native_decide

/-- **None of the 108 effective offsets is supplied by `x12`.** For the three register-bearing
kinds, field four is the actual source register; constants carry `-1`, so checking the whole
population is stronger and still exact. -/
theorem no_preReadAt_offset_uses_x12 :
    preReadAtOffsetBindings.all (fun row => row.2.2.2.1 != 12) = true := by
  native_decide

/-! ## Ruling 2 — repairing `entryPc ∈ exitPcs` -/

def entryPcs : List Nat :=
  (generatedProgram.functionInstances.map (·.entryPc)).toList

def distinctEntryPcs : List Nat :=
  entryPcs.eraseDups

def entryMultiplicity (pc : Nat) : Nat :=
  (generatedProgram.functionInstances.filter fun fi => fi.entryPc == pc).size

/-- The 141 rows occupy 95 entry addresses: 51 occur once, 42 occur twice, and 2 occur three times.
Thus there are 44 repeated-address groups, of which 42 are pairs; saying "44 shared by two" would
double-count the two triples. -/
theorem entry_pc_multiplicities :
    generatedProgram.functionInstances.size = 141 ∧
      distinctEntryPcs.length = 95 ∧
      (distinctEntryPcs.filter fun pc => entryMultiplicity pc == 1).length = 51 ∧
      (distinctEntryPcs.filter fun pc => entryMultiplicity pc == 2).length = 42 ∧
      (distinctEntryPcs.filter fun pc => entryMultiplicity pc == 3).length = 2 ∧
      distinctEntryPcs.all (fun pc => entryMultiplicity pc ≤ 3) = true := by
  native_decide

def sameEntryInlinePair (pair : FunctionInstance × FunctionInstance) : Bool :=
  pair.1.entryPc == pair.2.entryPc

def isSameEntryChild (fi : FunctionInstance) : Bool :=
  (Boundary.inlinePairs generatedProgram).any fun pair =>
    sameEntryInlinePair pair && decide (pair.2.id = fi.id)

/-- Dropping every direct inline child that shares its parent's entry deletes 46 rows. Only 14 of
those rows currently violate `entryNotExit`; 32 are structurally healthy, and 19 of the original 33
violations remain. -/
theorem same_entry_deduplication_blast_radius :
    ((Boundary.inlinePairs generatedProgram).filter sameEntryInlinePair).size = 46 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        sameEntryInlinePair pair && Boundary.entryIsOwnExit pair.2).size = 14 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        sameEntryInlinePair pair && !Boundary.entryIsOwnExit pair.2).size = 32 ∧
      (generatedProgram.functionInstances.filter fun fi =>
        Boundary.entryIsOwnExit fi && !isSameEntryChild fi).size = 19 := by
  native_decide

/-- Of the 33 bad rows, one is emitted (`allocatorFree`) and 32 are inlined. Restricting the machine
proof backlog to emitted bodies therefore leaves a real special case; it does not make the entry
defect disappear completely. -/
theorem entry_exit_failures_by_emission_kind :
    (generatedProgram.functionInstances.filter fun fi =>
      fi.parent?.isNone && Boundary.entryIsOwnExit fi).size = 1 ∧
      (generatedProgram.functionInstances.filter fun fi =>
        fi.parent?.isSome && Boundary.entryIsOwnExit fi).size = 32 := by
  native_decide

/-- If the repair merely removes `entryPc` from each `exitPcs`, these five instances have no exit
left at all. Indices are pinned because this is an option-specific blast-radius list, not a ledger
key. -/
def strandedByRemovingEntryExit : Array Nat :=
  generatedProgram.functionInstances.zipIdx.filterMap fun (fi, index) =>
    if Boundary.entryIsOwnExit fi &&
        fi.exitPcs.all (fun pc => pc == fi.entryPc) then
      some index
    else none

theorem removing_entry_from_exits_strands_five :
    strandedByRemovingEntryExit = #[5, 36, 61, 79, 127] := by
  native_decide

/-- Choosing another PC from the same regions cannot repair these 15 rows: every region PC is
already declared an exit. The other 18 bad rows have at least one non-exit region PC, but this fact
does not establish that such a PC is a genuine semantic entry. -/
def noNonExitRegionPcIndices : Array Nat :=
  generatedProgram.functionInstances.zipIdx.filterMap fun (fi, index) =>
    if Boundary.entryIsOwnExit fi &&
        (regionPcList fi).all fi.exitPcs.contains then
      some index
    else none

theorem entry_relocation_is_impossible_for_fifteen :
    noNonExitRegionPcIndices =
      #[5, 36, 48, 59, 60, 61, 79, 82, 83, 89, 90, 121, 122, 127, 128] ∧
      (generatedProgram.functionInstances.filter fun fi =>
        Boundary.entryIsOwnExit fi &&
          !(regionPcList fi).all fi.exitPcs.contains).size = 18 := by
  native_decide

/-! ## Ruling 3 — repairing inline transfer boundaries -/

/-- Every validated direct edge, independent of which deepest owner the generator attributed it
to. The current `InlineBoundary` cannot use this pool—it requires parent-edge membership—but this
pool answers whether the decoded CFG contains the needed geometry anywhere. -/
def allGeneratedEdges : Array DirectEdge :=
  generatedProgram.functionInstances.foldl (fun edges fi => edges ++ fi.edges) #[]

/-! ### The seven resolved tail-call rows -/

/-- The generated instance index, qualified function name, and offending resolved-call PCs for
every instance with a call source that is also one of its exits. -/
def tailCallExitRows : Array (Nat × String × List Nat) :=
  (controlFlow?.map fun nodes =>
    generatedProgram.functionInstances.zipIdx.filterMap fun (functionInstance, index) =>
      match Boundary.callSitesDeclaredExit nodes functionInstance with
      | [] => none
      | pcs => some (index, generatedManifest[index]!.qualifiedName, pcs)).getD #[]

def tailCallExitSources : List Nat :=
  tailCallExitRows.toList.flatMap fun row => row.2.2

/-- The full resolved-call join is 180 rows: 173 ordinary call-splice candidates and seven
source-is-exit tail calls. The seven belong to exactly four generated instances. -/
theorem resolved_call_tail_exit_join :
    (controlFlow?.map fun nodes =>
      let total := callRows nodes generatedProgram
      let ordinary := nonExitCallRows nodes generatedProgram
      (total, ordinary, total - ordinary)).getD (0, 0, 0) = (180, 173, 7) ∧
      tailCallExitRows =
        #[(3, "ssz_raw.decode", [66360]),
          (16, "ssz_raw.decodeNewPayloadRequest", [75508]),
          (23, "ssz_raw.decodeExecutionPayload", [73048, 73076, 73104, 73132]),
          (37, "ssz_raw.readArray", [69584])] := by
  native_decide

/-- All seven tail-call sources have a generated direct edge to the selected `memcpy` occurrence
at entry 81592. This is why they stop the caller rather than taking `CallTransfer.callNotExit`. -/
theorem tail_call_exit_target_is_memcpy :
    generatedManifest[139]!.routineTag = "memcpy" ∧
      generatedProgram.functionInstances[139]!.entryPc = 81592 ∧
      tailCallExitSources.length = 7 ∧
      tailCallExitSources.all (fun source =>
        allGeneratedEdges.contains { source, target := 81592 }) = true := by
  native_decide

def globalInlineEntryInhabited (pair : FunctionInstance × FunctionInstance) : Bool :=
  allGeneratedEdges.any (Boundary.crossesIn pair.1 pair.2)

def globalInlineExitInhabited (pair : FunctionInstance × FunctionInstance) : Bool :=
  allGeneratedEdges.any (Boundary.crossesOut pair.1 pair.2)

def parentChildShareExit (pair : FunctionInstance × FunctionInstance) : Bool :=
  pair.1.exitPcs.any pair.2.exitPcs.contains

/-! ### The old entry inventory was not operational -/

/-- An empty old-style boundary validates for any declared parent/child relation. Neither array is
required to be nonempty by `InlineBoundary.validFor`; the outgoing array becomes relevant only when
`InlineTransfer.exitEdgeMem` selects one of its members. -/
theorem emptyInlineBoundary_validFor (parent child : FunctionInstance)
    (hchild : child.id ∈ parent.children) :
    ({ child := child.id, entries := #[], exits := #[] } : InlineBoundary).validFor
      parent child := by
  simp [InlineBoundary.validFor, hchild]

/-- Erasing every declared entry edge preserves an already constructed old-style inline transfer.
This is the executable regression for the structural audit: no field of `InlineTransfer` consumes
`ib.entries`; only `valid` mentions it, and an empty universal check is immediate. -/
def clearInlineTransferEntries
    {region exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {ib : InlineBoundary} {functionInstance childFunctionInstance : FunctionInstance}
    {fromStep used : Nat} {s sResume : State}
    (h : InlineTransfer region exit childSummary ib functionInstance childFunctionInstance
      fromStep used s sResume) :
    InlineTransfer region exit childSummary { ib with entries := #[] }
      functionInstance childFunctionInstance fromStep used s sResume := by
  refine
    { valid := ?_
      entryPc := h.entryPc
      atEntry := h.atEntry
      entryIsChildEntry := h.entryIsChildEntry
      entryInRegion := h.entryInRegion
      entryNotExit := h.entryNotExit
      sExit := h.sExit
      body := h.body
      exitEdge := h.exitEdge
      exitEdgeMem := h.exitEdgeMem
      childExitPc := h.childExitPc
      atExit := h.atExit
      exitIsEdgeSource := h.exitIsEdgeSource
      exitInRegion := h.exitInRegion
      exitNotExit := h.exitNotExit
      doExit := h.doExit
      resumePc := h.resumePc
      atResume := h.atResume
      resumeIsEdgeTarget := h.resumeIsEdgeTarget
      resumeInRegion := h.resumeInRegion }
  rcases h.valid with ⟨hchild, hmem, _, hexits⟩
  exact ⟨hchild, hmem, by simp, by simpa using hexits⟩

/-- Inhabitance of the old transfer type is monotone under deleting every entry edge. -/
theorem inlineTransfer_entries_unconsumed
    {region exit : BitVec 64 → Prop}
    {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
    {ib : InlineBoundary} {functionInstance childFunctionInstance : FunctionInstance}
    {fromStep used : Nat} {s sResume : State} :
    Nonempty (InlineTransfer region exit childSummary ib functionInstance childFunctionInstance
      fromStep used s sResume) →
    Nonempty (InlineTransfer region exit childSummary { ib with entries := #[] }
      functionInstance childFunctionInstance fromStep used s sResume) := by
  rintro ⟨h⟩
  exact ⟨clearInlineTransferEntries h⟩

/-! ### Inventory-only edge counts -/

/-- With attribution ignored, 80 pairs have crossing edges in both directions, 11 have only a
crossing-out edge, none has only a crossing-in edge, and 36 have neither. This deliberately retains
the old inventory predicate: `crossesIn` may target any child fragment, and the transfer does not
consume entries. The exact consumer start and finish partitions are pinned below. -/
theorem global_inline_edge_categories :
    ((Boundary.inlinePairs generatedProgram).filter fun pair =>
      globalInlineEntryInhabited pair && globalInlineExitInhabited pair).size = 80 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        !globalInlineEntryInhabited pair && globalInlineExitInhabited pair).size = 11 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        globalInlineEntryInhabited pair && !globalInlineExitInhabited pair).size = 0 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        !globalInlineEntryInhabited pair && !globalInlineExitInhabited pair).size = 36 := by
  native_decide

def inlinePairNameKey (pair : FunctionInstance × FunctionInstance) :
    Nat × String × Nat × String :=
  (pair.1.entryPc, pair.1.id.function.declaration.qualifiedName,
    pair.2.entryPc, pair.2.id.function.declaration.qualifiedName)

/-- Under the inventory-only `crossesIn` predicate, the 47 pairs without any parent-contained edge
into any child fragment are the 46 same-entry pairs plus `decodeChainConfig → readOffset`. This is
not the exact-entry start partition: seven other pairs have later-fragment re-entry edges but reach
their actual `child.entryPc` from an ancestor-owned edge. -/
theorem missing_global_inline_entries_explained :
    ((Boundary.inlinePairs generatedProgram).filter fun pair =>
      !globalInlineEntryInhabited pair).size = 47 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        !globalInlineEntryInhabited pair && sameEntryInlinePair pair).size = 46 ∧
      ((Boundary.inlinePairs generatedProgram).filterMap fun pair =>
        if !globalInlineEntryInhabited pair && !sameEntryInlinePair pair
        then some (inlinePairNameKey pair) else none) =
          #[(76108, "ssz_raw.decodeChainConfig", 76124, "ssz_raw.readOffset")] := by
  native_decide

/-- The one exception visible to the coarse target-anywhere inventory has an exact entry edge from
the emitted `decodeRaw` ancestor. The exact-target consumer scan below finds seven more ancestor
entries that this inventory masks with unrelated later-fragment re-entry edges. -/
theorem distinct_entry_exception_is_ancestor_owned :
    allGeneratedEdges.contains { source := 76120, target := 76124 } = true ∧
      generatedProgram.functionInstances[6]!.containsAddress 76120 = true ∧
      generatedProgram.functionInstances[102]!.containsAddress 76120 = false ∧
      generatedProgram.functionInstances[103]!.containsAddress 76124 = true := by
  native_decide

/-- Raw edge inventory finds 91 crossing-out pairs and 36 with no such edge; the latter all share a
parent exit. This is not the consumer finish partition: `InlineTransfer.exitNotExit` rejects nine
of the 91 crossing edges because their sources are already parent exits, yielding 82 ordinary and
45 shared-exit cases below. -/
theorem missing_global_inline_exits_are_shared_exits :
    ((Boundary.inlinePairs generatedProgram).filter globalInlineExitInhabited).size = 91 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        !globalInlineExitInhabited pair).size = 36 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        !globalInlineExitInhabited pair && parentChildShareExit pair).size = 36 ∧
      (Boundary.inlinePairs generatedProgram).all (fun pair =>
        globalInlineExitInhabited pair || parentChildShareExit pair) = true := by
  native_decide

/-! ### Consumer-shaped start and finish partitions -/

/-- The edge enters the child's actual entry, not merely a later child fragment. -/
def targetsExactChildEntry
    (pair : FunctionInstance × FunctionInstance) (edge : DirectEdge) : Bool :=
  !pair.2.containsAddress edge.source && edge.target == pair.2.entryPc

/-- A non-same-entry child has a decoded edge to its exact entry whose source is contained in the
direct parent's regions. This matches the old parent-containment boundary check; it deliberately
does not claim that the overlapping source is deepest-owned by the parent. -/
def directParentInlineStart (pair : FunctionInstance × FunctionInstance) : Bool :=
  !sameEntryInlinePair pair && allGeneratedEdges.any fun edge =>
    targetsExactChildEntry pair edge && pair.1.containsAddress edge.source

/-- The deepest owner of `source` is a strict inline ancestor of `parent`. -/
def sourceOwnedByStrictAncestor (parent : FunctionInstance) (source : Nat) : Bool :=
  match deepestOwner? source with
  | some owner =>
      (ancestorIds generatedProgram.functionInstances.size parent.id).contains owner.id
  | none => false

/-- A non-same-entry child with no direct-parent exact-entry edge is reached by an exact-entry edge
whose source is deepest-owned by a strict ancestor of the direct parent. -/
def ancestorOwnedInlineStart (pair : FunctionInstance × FunctionInstance) : Bool :=
  !sameEntryInlinePair pair && !directParentInlineStart pair && allGeneratedEdges.any fun edge =>
    targetsExactChildEntry pair edge && sourceOwnedByStrictAncestor pair.1 edge.source

/-- The exact consumer start partition is 46 same-entry, 73 direct-parent exact-entry edges, and
eight strict-ancestor-owned exact-entry edges. The final conjunct pins exhaustiveness and
disjointness rather than relying on the three counts summing to 127. -/
theorem inline_start_partition :
    ((Boundary.inlinePairs generatedProgram).filter sameEntryInlinePair).size = 46 ∧
      ((Boundary.inlinePairs generatedProgram).filter directParentInlineStart).size = 73 ∧
      ((Boundary.inlinePairs generatedProgram).filter ancestorOwnedInlineStart).size = 8 ∧
      (Boundary.inlinePairs generatedProgram).all (fun pair =>
        (sameEntryInlinePair pair &&
            !directParentInlineStart pair && !ancestorOwnedInlineStart pair) ||
          (!sameEntryInlinePair pair &&
            directParentInlineStart pair && !ancestorOwnedInlineStart pair) ||
          (!sameEntryInlinePair pair &&
            !directParentInlineStart pair && ancestorOwnedInlineStart pair)) = true := by
  native_decide

/-- A global crossing-out edge that the current ordinary transfer could retire: its source is not
already a parent exit, exactly the side condition `InlineTransfer.exitNotExit` consumes. -/
def ordinaryInlineFinish (pair : FunctionInstance × FunctionInstance) : Bool :=
  allGeneratedEdges.any fun edge =>
    Boundary.crossesOut pair.1 pair.2 edge && !pair.1.exitPcs.contains edge.source

/-- If no usable ordinary edge exists, the child and parent may terminate together at a shared
exit. This is a different composition shape: it retires no outgoing edge at this inline level. -/
def sharedExitInlineFinish (pair : FunctionInstance × FunctionInstance) : Bool :=
  !ordinaryInlineFinish pair && parentChildShareExit pair

/-- Joining the raw edge inventory to `InlineTransfer.exitNotExit` leaves 82 ordinary continuations.
Nine of the 91 raw crossing-out cases move to the shared-exit class, joining the 36 raw no-edge
cases for 45 shared terminations. Every pair has exactly one finish class. -/
theorem inline_finish_partition :
    ((Boundary.inlinePairs generatedProgram).filter ordinaryInlineFinish).size = 82 ∧
      ((Boundary.inlinePairs generatedProgram).filter sharedExitInlineFinish).size = 45 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        globalInlineExitInhabited pair && !ordinaryInlineFinish pair).size = 9 ∧
      (Boundary.inlinePairs generatedProgram).all (fun pair =>
        (ordinaryInlineFinish pair && !sharedExitInlineFinish pair) ||
          (!ordinaryInlineFinish pair && sharedExitInlineFinish pair)) = true := by
  native_decide

/-- The independent start/finish partitions have only four inhabited cells: same-entry splits
1 ordinary / 45 shared, while all 73 direct-parent and all eight ancestor-owned starts continue
through an ordinary outgoing edge. -/
theorem inline_start_finish_cross_product :
    ((Boundary.inlinePairs generatedProgram).filter fun pair =>
      sameEntryInlinePair pair && ordinaryInlineFinish pair).size = 1 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        sameEntryInlinePair pair && sharedExitInlineFinish pair).size = 45 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        directParentInlineStart pair && ordinaryInlineFinish pair).size = 73 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        directParentInlineStart pair && sharedExitInlineFinish pair).size = 0 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        ancestorOwnedInlineStart pair && ordinaryInlineFinish pair).size = 8 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        ancestorOwnedInlineStart pair && sharedExitInlineFinish pair).size = 0 := by
  native_decide

/-! ### Exact ancestor-entry pairs and checked bridge paths -/

/-- One explicit decoded path from an ancestor-entry parent's own entry to its child's exact entry.
`borrowedSources` are precisely the path-edge sources outside the direct parent's regions. -/
structure AncestorEntryBridgeRow where
  parentEntry : Nat
  parentRoutine : String
  childEntry : Nat
  childRoutine : String
  entryEdgeSource : Nat
  entryEdgeOwnerEntry : Nat
  entryEdgeOwnerRoutine : String
  path : List Nat
  borrowedSources : List Nat
deriving DecidableEq, Repr

def AncestorEntryBridgeRow.pairKey (row : AncestorEntryBridgeRow) :
    Nat × String × Nat × String :=
  (row.parentEntry, row.parentRoutine, row.childEntry, row.childRoutine)

/-- The eight exact ancestor-entry pairs, each with one decoded route and its borrowed sources.
These paths are certificates of the missing bridge geometry, not a claim that every dynamic run
takes the same branch. -/
def ancestorEntryBridges : Array AncestorEntryBridgeRow := #[
  { parentEntry := 67084
    parentRoutine := "ssz_raw.decodeNewPayloadRequest"
    childEntry := 67140
    childRoutine := "ssz_raw.readOffset"
    entryEdgeSource := 67136
    entryEdgeOwnerEntry := 66628
    entryEdgeOwnerRoutine := "ssz_raw.decodeRaw"
    path := [
      67084, 67088, 67092, 67096, 67100, 67104, 67108, 67112,
      67116, 67120, 67124, 67128, 67132, 67136, 67140]
    borrowedSources := [67092, 67096, 67128, 67132, 67136] },
  { parentEntry := 67352
    parentRoutine := "ssz_raw.decodeExecutionPayload"
    childEntry := 67428
    childRoutine := "ssz_raw.readOffset"
    entryEdgeSource := 67424
    entryEdgeOwnerEntry := 67084
    entryEdgeOwnerRoutine := "ssz_raw.decodeNewPayloadRequest"
    path := [
      67352, 67356, 67360, 67364, 67368, 67372, 67376, 67392, 67396,
      67400, 67404, 67408, 67412, 67416, 67420, 67424, 67428]
    borrowedSources := [
      67360, 67364, 67392, 67396, 67400, 67404, 67408, 67412, 67416, 67420, 67424] },
  { parentEntry := 73716
    parentRoutine := "ssz_raw.decodeExecutionRequests"
    childEntry := 73880
    childRoutine := "ssz_raw.readOffset"
    entryEdgeSource := 73876
    entryEdgeOwnerEntry := 67084
    entryEdgeOwnerRoutine := "ssz_raw.decodeNewPayloadRequest"
    path := [
      73716, 73720, 73724, 73728, 73732, 73736, 73740,
      73744, 73748, 73868, 73872, 73876, 73880]
    borrowedSources := [73732, 73736, 73868, 73872, 73876] },
  { parentEntry := 75536
    parentRoutine := "ssz_raw.decodeExecutionWitness"
    childEntry := 75680
    childRoutine := "ssz_raw.readOffset"
    entryEdgeSource := 75676
    entryEdgeOwnerEntry := 66628
    entryEdgeOwnerRoutine := "ssz_raw.decodeRaw"
    path := [
      75536, 75540, 75544, 75548, 75552, 75556, 75560,
      75564, 75568, 75668, 75672, 75676, 75680]
    borrowedSources := [75552, 75556, 75668, 75672, 75676] },
  { parentEntry := 76108
    parentRoutine := "ssz_raw.decodeChainConfig"
    childEntry := 76124
    childRoutine := "ssz_raw.readOffset"
    entryEdgeSource := 76120
    entryEdgeOwnerEntry := 66628
    entryEdgeOwnerRoutine := "ssz_raw.decodeRaw"
    path := [76108, 76112, 76116, 76120, 76124]
    borrowedSources := [76112, 76116, 76120] },
  { parentEntry := 76224
    parentRoutine := "ssz_raw.decodeForkConfig"
    childEntry := 76316
    childRoutine := "ssz_raw.readOffset"
    entryEdgeSource := 76312
    entryEdgeOwnerEntry := 76108
    entryEdgeOwnerRoutine := "ssz_raw.decodeChainConfig"
    path := [
      76224, 76280, 76284, 76288, 76292, 76296, 76300, 76304, 76308, 76312, 76316]
    borrowedSources := [76280, 76284, 76288, 76292, 76296, 76300, 76304, 76308, 76312] },
  { parentEntry := 76592
    parentRoutine := "ssz_raw.decodeForkActivation"
    childEntry := 76600
    childRoutine := "ssz_raw.readOffset"
    entryEdgeSource := 76596
    entryEdgeOwnerEntry := 76224
    entryEdgeOwnerRoutine := "ssz_raw.decodeForkConfig"
    path := [76592, 76596, 76600]
    borrowedSources := [76596] },
  { parentEntry := 76888
    parentRoutine := "ssz_raw.decodeOptionalBlobSchedule"
    childEntry := 76988
    childRoutine := "ssz_raw.readU64"
    entryEdgeSource := 76984
    entryEdgeOwnerEntry := 76224
    entryEdgeOwnerRoutine := "ssz_raw.decodeForkConfig"
    path := [
      76888, 76892, 76896, 76900, 76904, 76908, 76912, 76916,
      76920, 76924, 76928, 76932, 76936, 76984, 76988]
    borrowedSources := [
      76896, 76900, 76904, 76908, 76912, 76916, 76920, 76924, 76928, 76932, 76984] }
]

/-- Consecutive path PCs as direct edges. -/
def bridgePathEdges : List Nat → List DirectEdge
  | source :: target :: rest =>
      { source, target } :: bridgePathEdges (target :: rest)
  | _ => []

def pairForBridge? (row : AncestorEntryBridgeRow) :
    Option (FunctionInstance × FunctionInstance) :=
  (Boundary.inlinePairs generatedProgram).find? fun pair =>
    inlinePairNameKey pair == row.pairKey

def functionInstanceName (functionInstance : FunctionInstance) : String :=
  functionInstance.id.function.declaration.qualifiedName

/-- The row names a measured ancestor pair; every consecutive path edge exists in the complete
validated edge pool; the final edge targets the exact child entry from the recorded strict ancestor;
and `borrowedSources` is exactly the path portion outside the direct parent's regions. -/
def bridgePathValid (row : AncestorEntryBridgeRow) : Bool :=
  match pairForBridge? row, (bridgePathEdges row.path).getLast? with
  | some pair, some lastEdge =>
      ancestorOwnedInlineStart pair &&
        row.path.head? == some pair.1.entryPc &&
        row.path.getLast? == some pair.2.entryPc &&
        (bridgePathEdges row.path).all allGeneratedEdges.contains &&
        row.borrowedSources ==
          ((bridgePathEdges row.path).map (fun edge => edge.source) |>.filter fun pc =>
            !pair.1.containsAddress pc) &&
        lastEdge.source == row.entryEdgeSource &&
        lastEdge.target == pair.2.entryPc &&
        !pair.1.containsAddress lastEdge.source &&
        match deepestOwner? lastEdge.source with
        | some owner =>
            sourceOwnedByStrictAncestor pair.1 lastEdge.source &&
              owner.entryPc == row.entryEdgeOwnerEntry &&
              functionInstanceName owner == row.entryEdgeOwnerRoutine
        | none => false
  | _, _ => false

/-- Every borrowed path source is outside both address sets available to the old direct-parent
proof: `Program.ownedRanges` and its downward transfer-closed execution ranges. -/
def bridgeBorrowedSourcesOutsideOldScopes (row : AncestorEntryBridgeRow) : Bool :=
  match pairForBridge? row with
  | some pair => row.borrowedSources.all fun pc =>
      !Program.inRanges (Program.ownedRanges generatedProgram pair.1) pc &&
        !Program.inRanges (functionInstanceExecutionRanges generatedProgram pair.1) pc
  | none => false

def measuredAncestorEntryPairKeys : Array (Nat × String × Nat × String) :=
  ((Boundary.inlinePairs generatedProgram).filter ancestorOwnedInlineStart).map inlinePairNameKey

/-- The literal bridge table is exactly the measured eight-pair set, and every path is a checked
sequence of decoded edges ending at the exact child entry from the named strict ancestor. -/
theorem exact_ancestor_entry_pairs_and_paths :
    measuredAncestorEntryPairKeys = ancestorEntryBridges.map (·.pairKey) ∧
      ancestorEntryBridges.size = 8 ∧
      ancestorEntryBridges.all bridgePathValid = true := by
  native_decide

/-- All borrowed bridge sources, not merely the eight final entry-edge sources, lie outside both old
direct-parent scopes. Any repair that keeps those scopes unchanged cannot realize these paths. -/
theorem ancestor_bridge_sources_outside_old_parent_scopes :
    ancestorEntryBridges.all bridgeBorrowedSourcesOutsideOldScopes = true := by
  native_decide

/-! ## Cost of proving nested instructions repeatedly with `ownStep` -/

def allRegionWordOccurrences : List Nat :=
  generatedProgram.functionInstances.foldl
    (fun words fi => words ++ regionPcList fi) []

def emittedRegionWordOccurrences : List Nat :=
  generatedProgram.functionInstances.foldl
    (fun words fi =>
      if fi.parent?.isNone then words ++ regionPcList fi else words) []

def inlinedRegionWordOccurrences : List Nat :=
  generatedProgram.functionInstances.foldl
    (fun words fi =>
      if fi.parent?.isSome then words ++ regionPcList fi else words) []

/-- The 14 emitted instances cover all 3,195 distinct instruction words once. Repeating a local
`ownStep` proof for all 127 inlined occurrences adds 7,398 duplicate occurrences, for 10,593 total
(about 3.315× the unique machine code). -/
theorem own_step_occurrence_cost :
    (generatedProgram.functionInstances.filter (·.parent?.isNone)).size = 14 ∧
      (generatedProgram.functionInstances.filter (·.parent?.isSome)).size = 127 ∧
      allRegionWordOccurrences.length = 10593 ∧
      allRegionWordOccurrences.eraseDups.length = 3195 ∧
      emittedRegionWordOccurrences.length = 3195 ∧
      emittedRegionWordOccurrences.eraseDups.length = 3195 ∧
      inlinedRegionWordOccurrences.length = 7398 ∧
      allRegionWordOccurrences.eraseDups.all emittedRegionWordOccurrences.contains = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation.RepairBlastRadius
