import BinaryFv.SSZ.Zesu.Elfling.BindingInventory
import BinaryFv.SSZ.Zesu.Elfling.ManifestCheck
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
* inline alternatives are evaluated with `Boundary.crossesIn`/`crossesOut`, the same geometry
  required by `InlineBoundary.validFor`, over the complete validated edge pool.

All findings are exact red pins. A future artifact change must move a theorem statement; it must not
silently make this file "green".
-/

namespace BinaryFv.SSZ.Zesu.Validation.RepairBlastRadius

set_option maxRecDepth 8000

open BinaryFv.Binary.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling.Generated
  (generatedManifest generatedProgram ManifestRow)
open BinaryFv.SSZ.Zesu.Elfling.GeneratedBindings (bindings)
open BinaryFv.SSZ.Zesu.Elfling.Validation (regionPcList)

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

def globalInlineEntryInhabited (pair : FunctionInstance × FunctionInstance) : Bool :=
  allGeneratedEdges.any (Boundary.crossesIn pair.1 pair.2)

def globalInlineExitInhabited (pair : FunctionInstance × FunctionInstance) : Bool :=
  allGeneratedEdges.any (Boundary.crossesOut pair.1 pair.2)

def parentChildShareExit (pair : FunctionInstance × FunctionInstance) : Bool :=
  pair.1.exitPcs.any pair.2.exitPcs.contains

/-- With attribution ignored, 80 pairs have ordinary crossing edges in both directions, 11 have
only a crossing-out edge, none has only a crossing-in edge, and 36 have neither. Emitting boundary
edges alone therefore cannot inhabit the current ordinary edge interface for 47 entries and 36
exits. -/
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

/-- The 47 pairs without a direct-parent crossing-in edge are exactly the 46 same-entry pairs plus
one distinct-entry pair, `decodeChainConfig → readOffset`. -/
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

/-- The exceptional distinct-entry edge exists, but its source is in the emitted ancestor
`decodeRaw` (index 6), not the direct parent `decodeChainConfig` (index 102). The target is the
`readOffset` child (index 103). A direct-parent boundary predicate therefore rejects a real
ancestor-to-descendant entry. -/
theorem distinct_entry_exception_is_ancestor_owned :
    allGeneratedEdges.contains { source := 76120, target := 76124 } = true ∧
      generatedProgram.functionInstances[6]!.containsAddress 76120 = true ∧
      generatedProgram.functionInstances[102]!.containsAddress 76120 = false ∧
      generatedProgram.functionInstances[103]!.containsAddress 76124 = true := by
  native_decide

/-- All 36 pairs without a crossing-out edge share an exit PC with their parent. Every pair has
either an ordinary global crossing-out edge (91) or this shared-exit termination case (36), so an
extended interface can classify all 127—but the current `InlineTransfer` expresses only the first
shape. -/
theorem missing_global_inline_exits_are_shared_exits :
    ((Boundary.inlinePairs generatedProgram).filter globalInlineExitInhabited).size = 91 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        !globalInlineExitInhabited pair).size = 36 ∧
      ((Boundary.inlinePairs generatedProgram).filter fun pair =>
        !globalInlineExitInhabited pair && parentChildShareExit pair).size = 36 ∧
      (Boundary.inlinePairs generatedProgram).all (fun pair =>
        globalInlineExitInhabited pair || parentChildShareExit pair) = true := by
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
