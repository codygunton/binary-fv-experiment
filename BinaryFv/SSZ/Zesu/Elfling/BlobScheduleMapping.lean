import BinaryFv.SSZ.Zesu.Elfling.BlobScheduleInstance
import BinaryFv.SSZ.Zesu.Contracts.Options
import BinaryFv.SSZ.Zesu.Contracts.Catalog
import BinaryFv.SSZ.Zesu.MachineExecution.BlobScheduleAndResultStores

/-!
# `decodeOptionalBlobSchedule` vertical mapping slice (Amendment A, milestone 3)

This module validates the generated `decodeOptionalBlobSchedule` occurrence
(`BlobScheduleInstance.lean`, extracted from the DWARF sidecar and mapped to canonical-ELF PCs)
against the two things it must agree with, and exposes — rather than silently drops — everything the
extraction leaves unresolved:

1. **Identity.** Through the *address-free* catalog (`catalogEntryFor`), the generated occurrence's
   identity resolves to exactly the `decodeOptionalBlobSchedule` routine, so it is the occurrence the
   handwritten contract dispatches to. Nothing here mentions an address on the contract side.
2. **Coverage.** Every PC of the existing 66-step trace over `0x12cbc..0x12dc0`
   (`BlobScheduleAndResultStores`) lies inside the occurrence's three discontiguous fragments.
3. **Attribution.** The three nested `readU64` field-read occurrences are properly nested in the
   parent and pairwise disjoint, so there is no overlapping or ambiguous ownership; the resulting
   `AttributionDefect` list is therefore empty, and that emptiness is *proved*, not assumed.
4. **What the exemplar trace does NOT reach**, exposed as data: all 66 trace PCs are owned (deepest-
   inline rule) by the nested `readU64` reads, so `decodeOptionalBlobSchedule`'s own control flow —
   the two small leading fragments and its non-field-read third-fragment code — is unexercised by
   this trace. The semantic proof (both branches, live state) is row 3, `ssz-elfling-blob-schedule`.

This is deliberately the single-function slice that validates the representation (Amendment A). No
bulk source mapping until it lands.
-/

namespace BinaryFv.SSZ.Zesu.Elfling

open BinaryFv.Binary (AddressRange)
open BinaryFv.Binary.Elfling
open BinaryFv.SSZ.Zesu.Contracts (catalogEntryFor RoutineTag DecoderEnvironment
  correctnessClaimOptionalBlobSchedule)
open BinaryFv.SSZ.Zesu.MachineExecution

/-- The three nested `readU64` field-read occurrences. -/
def blobScheduleChildren : Array FunctionInstance :=
  #[readU64Field0Instance, readU64Field1Instance, readU64Field2Instance]

/-- The exact PCs of the existing 66-step blob-schedule trace: the present-load group and the four
assembly groups from `BlobScheduleAndResultStores`. -/
def blobScheduleTraceSites : Array Nat :=
  rawBlobSchedulePresentLoadSites ++ rawBlobSchedulePresentAssemblySites ++
    rawBlobScheduleSecondAssemblySites ++ rawBlobScheduleThirdAssemblySites ++
    rawBlobScheduleFourthAssemblySites

/-! ## 1. Identity — bound through the address-free catalog -/

/-- The generated occurrence's identity resolves, through the address-free catalog, to exactly the
`decodeOptionalBlobSchedule` routine. This is the join between generated (address-bearing) data and
the handwritten (address-free) contract dispatch. -/
theorem blobSchedule_identity_matches_catalog :
    (catalogEntryFor blobScheduleInstance.id.function).map (·.tag)
      = some RoutineTag.optionalBlobSchedule := by
  native_decide

/-! ## 2. Coverage — the 66-step trace is covered by the occurrence -/

/-- Every PC of the existing 66-step trace lies inside one of the occurrence's three fragments. -/
theorem blobSchedule_trace_covered :
    blobScheduleTraceSites.all (fun pc => blobScheduleInstance.containsAddress pc) = true := by
  native_decide

/-- Sanity: the trace has exactly 66 steps. -/
theorem blobSchedule_trace_step_count : blobScheduleTraceSites.size = 66 := by native_decide

/-! ## 3. Attribution — nesting/disjointness, hence no defects -/

/-- `range` is contained in some region of `inst`. -/
def rangeCoveredBy (inst : FunctionInstance) (range : AddressRange) : Bool :=
  inst.regions.any (fun q => q.start ≤ range.start && range.stop ≤ q.stop)

/-- Every region of `child` sits inside a region of `parent` (proper inline nesting). -/
def instanceNestedIn (child parent : FunctionInstance) : Bool :=
  child.regions.all (rangeCoveredBy parent)

/-- Two occurrences' regions are pairwise disjoint. -/
def instancesDisjoint (a b : FunctionInstance) : Bool :=
  a.regions.all (fun r => b.regions.all (fun q => q.stop ≤ r.start || r.stop ≤ q.start))

/-- Each nested `readU64` occurrence is contained in the parent occurrence's regions. -/
theorem blobSchedule_children_nested :
    blobScheduleChildren.all (fun c => instanceNestedIn c blobScheduleInstance) = true := by
  native_decide

/-- The three sibling `readU64` occurrences are pairwise disjoint: no overlapping ownership. -/
theorem blobSchedule_children_disjoint :
    (instancesDisjoint readU64Field0Instance readU64Field1Instance &&
     instancesDisjoint readU64Field0Instance readU64Field2Instance &&
     instancesDisjoint readU64Field1Instance readU64Field2Instance) = true := by
  native_decide

/-- A child region not contained in any of `parent`'s regions: the child claims a PC its parent does
not own. Surfaced as `uncovered` at the region start. -/
def nestingDefects (parent : FunctionInstance) (children : Array FunctionInstance) :
    Array AttributionDefect :=
  children.flatMap fun c =>
    c.regions.filterMap fun r =>
      if parent.regions.any (fun q => decide (q.start ≤ r.start ∧ r.stop ≤ q.stop)) then none
      else some (AttributionDefect.uncovered r.start)

/-- The first PC (if any) at which two occurrences' regions overlap. -/
def firstSharedAddress (a b : FunctionInstance) : Option Nat :=
  a.regions.foldl (init := none) fun acc r =>
    acc.orElse fun _ => b.regions.foldl (init := none) fun acc' q =>
      acc'.orElse fun _ =>
        if r.start < q.stop ∧ q.start < r.stop then some (max r.start q.start) else none

/-- Two sibling children sharing a PC (neither inlined within the other): `overlappingOwnership`. -/
def siblingOverlapDefects (children : Array FunctionInstance) : Array AttributionDefect :=
  (List.range children.size).foldl (init := #[]) fun acc i =>
    (List.range children.size).foldl (init := acc) fun acc j =>
      if i < j then
        match firstSharedAddress children[i]! children[j]! with
        | some addr =>
            acc.push (AttributionDefect.overlappingOwnership addr children[i]!.id children[j]!.id)
        | none => acc
      else acc

/-- The attribution defects for the blob-schedule occurrence, **computed** from its extracted data:
child regions not contained in the parent (`uncovered`) and sibling children sharing a PC
(`overlappingOwnership`). This is the ownership/coverage scan itself — not a defined `#[]` — so the
emptiness proved below is a *consequence* of `blobSchedule_children_nested`/`_disjoint` holding on the
real regions; a drifted extraction with a stray region or an overlap would make it nonempty. -/
def blobScheduleAttributionDefects : Array AttributionDefect :=
  nestingDefects blobScheduleInstance blobScheduleChildren ++
    siblingOverlapDefects blobScheduleChildren

theorem blobSchedule_defect_free : blobScheduleAttributionDefects.isEmpty = true := by native_decide

/-! ## 4. What the exemplar trace does not reach (exposed, not dropped) -/

/-- Trace PCs owned — by the deepest-inline rule — by a nested `readU64` field read. -/
def blobScheduleTraceOwnedByChild : Array Nat :=
  blobScheduleTraceSites.filter (fun pc => blobScheduleChildren.any (fun c => c.containsAddress pc))

/-- The exemplar 66-step trace exercises only the nested u64 field reads: every one of its PCs is
owned by a `readU64` child, none directly by `decodeOptionalBlobSchedule`. So the occurrence's own
control flow (the present-check and the two small leading fragments `0x12c58` and `0x12c88`) is not
exercised by this trace — the row-3 semantic proof must add it. -/
theorem blobSchedule_trace_is_field_reads :
    blobScheduleTraceOwnedByChild.size = blobScheduleTraceSites.size := by
  native_decide

/-- Every instruction PC (4-byte stride) the occurrence's three fragments claim. -/
def blobScheduleOccurrencePCs : Array Nat :=
  blobScheduleInstance.regions.flatMap fun r =>
    (List.range (r.size / 4)).toArray.map (fun k => r.start + 4 * k)

/-- **Every** occurrence PC the 66-step exemplar trace does not exercise, at instruction granularity —
computed by set difference against the trace, not a hand-listed pair of ranges. This surfaces not only
the two wholly-unexercised leading fragments but also the gap the trace leaves INSIDE the large third
fragment (`0x12dc4`, the `readU64` tail the trace stops one instruction short of) — exactly the
omission the review flagged. -/
def blobScheduleUnexercisedPCs : Array Nat :=
  blobScheduleOccurrencePCs.filter (fun pc => !blobScheduleTraceSites.contains pc)

/-- Nothing is dropped: every occurrence PC is either exercised by the trace or surfaced as
unexercised. -/
theorem blobSchedule_pc_partition :
    blobScheduleOccurrencePCs.all
      (fun pc => blobScheduleTraceSites.contains pc || blobScheduleUnexercisedPCs.contains pc) = true := by
  native_decide

/-- The unexercised set is genuinely disjoint from the trace. -/
theorem blobSchedule_unexercised_untraced :
    blobScheduleUnexercisedPCs.all (fun pc => !blobScheduleTraceSites.contains pc) = true := by
  native_decide

/-- The unexercised set includes the gap INSIDE the third fragment (`0x12dc4`), not only the two
leading fragments (`0x12c58`, `0x12c88`). -/
theorem blobSchedule_unexercised_covers_third_fragment_gap :
    blobScheduleUnexercisedPCs.contains 0x12c58 = true ∧
    blobScheduleUnexercisedPCs.contains 0x12c88 = true ∧
    blobScheduleUnexercisedPCs.contains 0x12dc4 = true := by native_decide

/-- 14 leading-fragment PCs plus the single third-fragment gap. -/
theorem blobSchedule_unexercised_count : blobScheduleUnexercisedPCs.size = 15 := by native_decide

/-! ## 5. Contract binding — the generated occurrence implements the handwritten contract -/

/-- The occurrence's entry PC as a machine word. -/
def blobScheduleEntry : BitVec 64 := BitVec.ofNat 64 blobScheduleInstance.entryPc

/-- The occurrence's exit predicate: exactly its generated exit PCs. -/
def blobScheduleExit (pc : BitVec 64) : Prop := pc.toNat ∈ blobScheduleInstance.exitPcs

/-- The address-free `decodeOptionalBlobSchedule` correctness obligation, bound to the generated
occurrence and its generated entry/exit. Stated here; its semantic discharge (both option branches,
live-state instantiation, stores) is row 3 (`ssz-elfling-blob-schedule`). This is the join the whole
Elfling layering exists to make: an address-free claim, every address supplied by the occurrence.
This standalone slice already includes its nested reads in `blobScheduleInstance.regions`, so it has
no additional reached extent. -/
def blobScheduleCorrectnessObligation (env : DecoderEnvironment) : Prop :=
  correctnessClaimOptionalBlobSchedule env blobScheduleInstance (fun _ => False)
    blobScheduleEntry blobScheduleExit

end BinaryFv.SSZ.Zesu.Elfling
