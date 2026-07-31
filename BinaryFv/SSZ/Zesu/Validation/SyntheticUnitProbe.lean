import BinaryFv.SSZ.Zesu.Contracts.Catalog
import BinaryFv.RiscV.Elfling.ProgramGeometry

/-!
# Angle 4 probe: is a synthetic, non-source-function region an admissible proof unit?

**Measurement, not a gate.** Nothing in the theorem graph imports this module.

The fixture is the real emitted routine `raw_allocator.zesu_raw_alloc`: region `[66124, 66224)`,
25 four-byte instructions, 8 basic blocks, 29 decoded edges, entry `66124`, single generated exit
`66208`, no children and no external calls (taken verbatim from
`build/elfling-program-lean/program.json`). It is split at the block boundary `66204` into two
**disjoint** units, and the head keeps *all 29* of the original edges so that no negative below can
be blamed on the extractor's edge attribution.

What the probe decides:

1. The synthetic tail reuses the *real* `FunctionId` of `zesu_raw_alloc` with a fabricated
   `inlineStack`, and `catalogEntryFor` still returns the `rawAlloc` entry — so the catalog lookup
   does **not** block a synthetic unit (`synthetic_tail_dispatches`).
2. `programGeometryB` and `callGraphRankedB` are both `true` on the two-unit split
   (`split_geometry_holds`, `split_rank_holds`), so the geometry+rank interface admits it.
3. The same check is `false` on the sentinel-exit variant (`sentinel_geometry_fails`), so 2 is not a
   check incapable of failing.
4. No edge of the whole function crosses from the tail back into the head
   (`no_child_to_parent_edge`), so `InlineBoundary.validFor`'s exit clause — and therefore
   `ScopedTrace.inlineStep` — has no witness for a chain split, for a structural reason rather than a
   bookkeeping one.
5. `CallSite.validFor` nevertheless *passes* at the split (`probeCallSite_valid`): the data-level
   call check is satisfiable for a mid-function seam.
6. The machine-side region condition is measured directly: the head's owned set contains no tail
   exit, while the nested-hole positive control does.
-/

namespace BinaryFv.SSZ.Zesu.Validation.SyntheticUnitProbe

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts

/-! ## The fixture, taken from the generated program -/

abbrev probeProvenance : ExtractionProvenance :=
  { sidecarHash := "synthetic-unit-probe", entryOffset := 4377, extractorVersion := "angle4-probe" }

/-- The real recorded provenance of `zesu_raw_alloc`: the pinned allocator-source hash and line 12. -/
abbrev allocDecl : DeclarationProvenance :=
  { sourceFileHash := "c9e9457e45a3827729adb1921e07ba31997a536dc8f719e04d2d0d6f4c742591"
    declSpan := { line := 12, column := 1 } }

/-- The **real** catalog identity of the emitted allocator entry point. -/
abbrev allocFunctionId : FunctionId :=
  { declaration := { file := { path := "src/zkvm/raw_allocator.zig" }
                     qualifiedName := "raw_allocator.zesu_raw_alloc" }
    specialization := #[] }

abbrev headId : FunctionInstanceId := { function := allocFunctionId, inlineStack := [] }

/-- A **fabricated** inline site. No DWARF entry proposes it; it names the routine as its own caller
at a column the source does not have. It exists only to make a second distinct
`FunctionInstanceId` out of one `FunctionId`. -/
abbrev syntheticSite : InlineSite :=
  { caller := { file := { path := "src/zkvm/raw_allocator.zig" }
                qualifiedName := "raw_allocator.zesu_raw_alloc" }
    callSite := { line := 12, column := 999 } }

/-- The synthetic tail unit's identity: the same `FunctionId`, a fabricated one-element stack. -/
abbrev tailId : FunctionInstanceId := { function := allocFunctionId, inlineStack := [syntheticSite] }

/-- All 29 decoded edges of `zesu_raw_alloc`, verbatim. -/
abbrev allocEdges : Array DirectEdge :=
  #[ ⟨66124, 66204⟩, ⟨66124, 66128⟩, ⟨66128, 66132⟩, ⟨66132, 66136⟩, ⟨66136, 66200⟩
   , ⟨66136, 66140⟩, ⟨66140, 66144⟩, ⟨66144, 66148⟩, ⟨66148, 66152⟩, ⟨66152, 66156⟩
   , ⟨66156, 66200⟩, ⟨66156, 66160⟩, ⟨66160, 66164⟩, ⟨66164, 66168⟩, ⟨66168, 66172⟩
   , ⟨66172, 66176⟩, ⟨66176, 66180⟩, ⟨66180, 66184⟩, ⟨66184, 66200⟩, ⟨66184, 66188⟩
   , ⟨66188, 66192⟩, ⟨66192, 66196⟩, ⟨66196, 66212⟩, ⟨66196, 66200⟩, ⟨66200, 66204⟩
   , ⟨66204, 66208⟩, ⟨66212, 66216⟩, ⟨66216, 66220⟩, ⟨66220, 66204⟩ ]

/-- The head segment `[66124, 66204)`: 20 instructions, the first six blocks.
Its declared exits are the two branch pcs whose successors leave the segment and which are not the
entry (`66124`'s branch to `66204` also leaves; declaring it would make `entryNotExit` false, which
is the separate `sentinelSplit` variant below).
It carries **all 29** edges, not just its own 25. -/
abbrev allocHead : FunctionInstance :=
  { id := headId
    regions := #[{ start := 66124, size := 80 }]
    entryPc := 66124
    exitPcs := #[66196, 66200]
    parent? := none
    children := #[]
    externalCalls := #[tailId]
    blocks := #[ ⟨{ start := 66124, size := 4 }⟩, ⟨{ start := 66128, size := 12 }⟩
               , ⟨{ start := 66140, size := 20 }⟩, ⟨{ start := 66160, size := 28 }⟩
               , ⟨{ start := 66188, size := 12 }⟩, ⟨{ start := 66200, size := 4 }⟩ ]
    edges := allocEdges
    declProvenance := allocDecl
    provenance := probeProvenance
    symbol? := none }

/-- The synthetic tail segment `[66204, 66224)`: 5 instructions, the last two blocks, carrying the
real generated exit `66208`. -/
abbrev allocTail : FunctionInstance :=
  { id := tailId
    regions := #[{ start := 66204, size := 20 }]
    entryPc := 66204
    exitPcs := #[66208]
    parent? := some headId
    children := #[]
    externalCalls := #[]
    blocks := #[ ⟨{ start := 66204, size := 8 }⟩, ⟨{ start := 66212, size := 12 }⟩ ]
    edges := #[ ⟨66204, 66208⟩, ⟨66212, 66216⟩, ⟨66216, 66220⟩, ⟨66220, 66204⟩ ]
    declProvenance := allocDecl
    provenance := probeProvenance
    symbol? := none }

abbrev splitProgram : Program :=
  { entry := headId, functionInstances := #[allocHead, allocTail], defects := #[]
    provenance := probeProvenance }

/-- The honest rank: the tail below the head. -/
def splitRank (fi : FunctionInstance) : Nat := if fi.entryPc = 66124 then 1 else 0

/-! ## 1. The two units tile the original region exactly, and the split is at a block boundary -/

theorem split_tiles :
    allocHead.coveredBytes + allocTail.coveredBytes = 100 := by native_decide

theorem split_disjoint :
    (allocHead.containsAddress 66200 = true ∧ allocTail.containsAddress 66200 = false) ∧
    (allocHead.containsAddress 66204 = false ∧ allocTail.containsAddress 66204 = true) := by native_decide

/-! ## 2. `catalogEntryFor` does not block a synthetic unit

The tail's identity is fabricated, yet the catalog lookup — which is keyed on `id.function` only and
ignores `inlineStack` entirely — returns the same live `rawAlloc` entry the head gets. So condition
(4) of the bridge interface is satisfied by a synthetic unit **with no change to the handwritten
catalog**, at the price that the synthetic unit then owes the *whole* `zesu_raw_alloc` contract at its
own entry and exits. -/

theorem head_and_tail_ids_differ : headId ≠ tailId := by decide

theorem synthetic_tail_dispatches :
    (catalogEntryFor tailId.function).map (·.tag) = some RoutineTag.rawAlloc := by native_decide

theorem synthetic_tail_dispatch_equals_head :
    (catalogEntryFor tailId.function).map (·.tag)
      = (catalogEntryFor headId.function).map (·.tag) := by native_decide

/-- A synthetic identity that is *not* a catalog identity gets `none`, so the lookup is not a check
that accepts anything. -/
theorem fabricated_name_does_not_dispatch :
    (catalogEntryFor
        { declaration := { file := { path := "src/zkvm/raw_allocator.zig" }
                           qualifiedName := "raw_allocator.zesu_raw_alloc.segment1" }
          specialization := #[] }).isSome = false := by native_decide

/-! ## 3. Geometry and rank hold on the synthetic disjoint split -/

theorem split_geometry_holds : programGeometryB splitProgram = true := by native_decide

theorem split_rank_holds : functionGraphRankedB splitProgram splitRank = true := by native_decide

theorem split_geometry : ProgramGeometry splitProgram :=
  programGeometry_of_check split_geometry_holds

theorem split_ranked : FunctionGraphRanked splitProgram splitRank :=
  functionGraphRanked_of_check split_rank_holds

/-! ## 4. The same checks can fail: the sentinel-exit variant

If the head declares its exits as the *successor* pcs (`66204`, `66212`) instead of the branch pcs —
the "sentinel exit" model — those exits land inside the tail's execution set without being tail
exits, and `calleeExitContainmentB` refuses the program. -/

abbrev sentinelHead : FunctionInstance := { allocHead with exitPcs := #[66204, 66212] }

abbrev sentinelSplitProgram : Program :=
  { splitProgram with functionInstances := #[sentinelHead, allocTail] }

theorem sentinel_geometry_fails : programGeometryB sentinelSplitProgram = false := by native_decide

theorem sentinel_exit_containment_fails :
    calleeExitContainmentB sentinelSplitProgram = false := by native_decide

/-- And the failure is specifically the exit clause: the other two clauses still pass. -/
theorem sentinel_other_clauses_pass :
    ownedWithinExecutionB sentinelSplitProgram = true ∧
      calleeWithinExecutionB sentinelSplitProgram = true := by native_decide

/-! ## 5. `inlineStep` has no witness for a chain split

`InlineBoundary.validFor`'s exit clause demands an edge of the parent whose source the child owns,
whose target the child does not own, and whose target the parent *does* own — i.e. control must come
back into the parent. The head carries all 29 edges of the function, and none of them qualifies:
a chain split's successor unit never returns to its predecessor. -/

abbrev childToParentEdgesB : Bool :=
  allocHead.edges.any fun e =>
    allocTail.containsAddress e.source && !allocTail.containsAddress e.target &&
      allocHead.containsAddress e.target

theorem no_child_to_parent_edge : childToParentEdgesB = false := by native_decide

/-- Every declared inline exit edge would have to be one of those, so `InlineBoundary.validFor` can
only hold with an `exits` array that has no members — and `InlineTransfer.exitEdgeMem` then has no
witness, which is exactly `ScopedTrace.inlineStep` being dead for this pair. -/
theorem inline_exits_have_no_witness (ib : InlineBoundary)
    (h : ib.validFor allocHead allocTail) (e : DirectEdge) (he : e ∈ ib.exits) : False := by
  obtain ⟨-, -, -, hex⟩ := h
  obtain ⟨hmem, hsrc, htgt, hptgt⟩ := hex e he
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hmem
  have : childToParentEdgesB = true := by
    unfold childToParentEdgesB
    refine Array.any_eq_true.mpr ⟨i, hi, ?_⟩
    rw [hget]
    simp [hsrc, htgt, hptgt]
  rw [no_child_to_parent_edge] at this
  exact Bool.noConfusion this

/-! ## 6. `callStep` has no witness either — and the *data* check does not see it

`CallSite.validFor` passes at the seam `66124 → 66204`: it is a real edge, the target is the tail's
entry, the fall-through `66128` is still owned by the head, and the tail is a declared external call.
So the boundary's data-level check is satisfiable for a mid-function split. -/

abbrev probeCallSite : CallSite :=
  { source := 66124, callee := tailId, calleeEntry := 66204, returnPc := 66128 }

theorem probeCallSite_valid : probeCallSite.validFor allocHead allocTail := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, by native_decide, by native_decide⟩ <;> native_decide

/-! ## 7. Positive control: the **nested hole** shape passes every structural clause

Same routine, same synthetic-identity trick, but the second unit is a *sub-region* of the first
rather than a disjoint successor. The parent keeps the whole `[66124, 66224)` region and the real
exit `66208`; the hole is the single basic block `[66212, 66224)`, whose out-edge `66220 → 66204`
lands back inside the parent.

This is the positive direction for §5 and §6: every check that came out `false` for the chain split
comes out `true` here, so none of those negatives is a check incapable of passing. -/

abbrev holeId : FunctionInstanceId :=
  { function := allocFunctionId
    inlineStack := [{ caller := syntheticSite.caller, callSite := { line := 12, column := 777 } }] }

abbrev allocWhole : FunctionInstance :=
  { allocHead with
    id := headId
    regions := #[{ start := 66124, size := 100 }]
    exitPcs := #[66208]
    children := #[holeId]
    externalCalls := #[]
    blocks := #[] }

abbrev allocHole : FunctionInstance :=
  { allocTail with
    id := holeId
    regions := #[{ start := 66212, size := 12 }]
    entryPc := 66212
    exitPcs := #[66220]
    parent? := some headId
    blocks := #[]
    edges := #[ ⟨66212, 66216⟩, ⟨66216, 66220⟩, ⟨66220, 66204⟩ ] }

abbrev holeProgram : Program :=
  { splitProgram with functionInstances := #[allocWhole, allocHole] }

def holeRank (fi : FunctionInstance) : Nat := if fi.entryPc = 66124 then 1 else 0

theorem hole_geometry_holds : programGeometryB holeProgram = true := by native_decide

theorem hole_rank_holds : functionGraphRankedB holeProgram holeRank = true := by native_decide

theorem hole_geometry : ProgramGeometry holeProgram :=
  programGeometry_of_check hole_geometry_holds

/-- The hole's identity is synthetic and still dispatches. -/
theorem hole_dispatches :
    (catalogEntryFor holeId.function).map (·.tag) = some RoutineTag.rawAlloc := by native_decide

/-- **Positive control for §5.** A child-to-parent edge exists for the nested hole. -/
def holeChildToParentEdgesB : Bool :=
  allocWhole.edges.any fun e =>
    allocHole.containsAddress e.source && !allocHole.containsAddress e.target &&
      allocWhole.containsAddress e.target

theorem hole_has_child_to_parent_edge : holeChildToParentEdgesB = true := by native_decide

/-- The full `InlineBoundary` for the hole, with a real entry edge and a real exit edge. -/
abbrev holeBoundary : InlineBoundary :=
  { child := holeId, entries := #[⟨66196, 66212⟩], exits := #[⟨66220, 66204⟩] }

/-- **Every clause of `InlineBoundary.validFor` holds for a synthetic nested hole**, exits included.
This is the clause that is `false` 127/127 times on the real artifact and `false` for the chain
split; here it is satisfied by construction. -/
theorem holeBoundary_valid : holeBoundary.validFor allocWhole allocHole := by
  refine ⟨rfl, by native_decide, ?_, ?_⟩
  · intro e he
    have : e = ⟨66196, 66212⟩ := by simpa using he
    subst this
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩
  · intro e he
    have : e = ⟨66220, 66204⟩ := by simpa using he
    subst this
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- **Positive control for §6.** `CallTransfer.retInRegion` is satisfiable for the nested hole and
unsatisfiable for the chain split — the same check, both ways. -/
def calleeExitInOwnB (program : Program) (parent child : FunctionInstance) : Bool :=
  child.exitPcs.any fun pc => Program.inRanges (Program.ownedRanges program parent) pc

theorem hole_callee_exit_in_own : calleeExitInOwnB holeProgram allocWhole allocHole = true := by
  native_decide

theorem split_callee_exit_not_in_own :
    calleeExitInOwnB splitProgram allocHead allocTail = false := by native_decide

/-! ## 8. How much a parent can actually shed: exactly the hole's *interior*

In §7 the parent still owns every hole address, so its own local proof may simply `ownStep` through
the hole and the splice buys nothing. The question is how much of the hole the parent may drop from
`regions` and still splice. Reading `InlineTransfer`'s region fields answers it exactly:

* `entryInRegion` — the parent must own the hole's **entry pc**;
* `exitInRegion` — the parent must own the pc the hole stopped at, i.e. the **source of the exit
  edge**, the hole's last instruction;
* `resumeInRegion` — the parent must own the exit edge's **target**, which is residue anyway.

Nothing else about the hole is region-checked: the `used` body steps are consumed by the summary. So a
hole of `k` instructions lets the parent shed exactly `k - 2` of them (`0` for `k ≤ 2`).

The fixture below is the same routine with a *fragmented* parent that owns the residue plus only the
hole's first and last instruction — the hole's interior (`66216`) is dropped — and it still passes the
geometry and the whole `InlineBoundary`. -/

abbrev fragmentedParent : FunctionInstance :=
  { allocWhole with
    regions := #[{ start := 66124, size := 92 }, { start := 66220, size := 4 }] }

abbrev fragmentedProgram : Program :=
  { splitProgram with functionInstances := #[fragmentedParent, allocHole] }

theorem fragmented_parent_sheds_hole_interior :
    fragmentedParent.containsAddress 66212 = true ∧
      fragmentedParent.containsAddress 66216 = false ∧
      fragmentedParent.containsAddress 66220 = true := by native_decide

theorem fragmented_geometry_holds : programGeometryB fragmentedProgram = true := by native_decide

theorem fragmented_rank_holds : functionGraphRankedB fragmentedProgram holeRank = true := by
  native_decide

theorem fragmented_geometry : ProgramGeometry fragmentedProgram :=
  programGeometry_of_check fragmented_geometry_holds

/-- The boundary is still fully valid against the fragmented parent, so `inlineStep` remains
available after the interior is shed. -/
theorem holeBoundary_valid_fragmented : holeBoundary.validFor fragmentedParent allocHole := by
  refine ⟨rfl, by native_decide, ?_, ?_⟩
  · intro e he
    have : e = ⟨66196, 66212⟩ := by simpa using he
    subst this
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩
  · intro e he
    have : e = ⟨66220, 66204⟩ := by simpa using he
    subst this
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The three region facts `InlineTransfer` needs of the fragmented parent — hole entry, hole last
instruction, and resume target — all hold, and the shed interior does not appear among them. -/
theorem fragmented_inlineTransfer_region_facts :
    Program.inRanges (Program.ownedRanges fragmentedProgram fragmentedParent) 66212 = true ∧
      Program.inRanges (Program.ownedRanges fragmentedProgram fragmentedParent) 66220 = true ∧
      Program.inRanges (Program.ownedRanges fragmentedProgram fragmentedParent) 66204 = true ∧
      Program.inRanges (Program.ownedRanges fragmentedProgram fragmentedParent) 66216 = false := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation.SyntheticUnitProbe
