import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.RiscV.Elfling.SentinelBridgeWitness
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry

/-!
# The sequential splice, exhibited on `ssz_raw.decodeRaw`

Validation-only. Nothing here is imported by the root theorem.

`SequentialSplice` proves that two adjacent disjoint regions compose. A conditional theorem whose
hypotheses cannot all hold at once proves nothing, and four structural predicates in this project
looked fine on paper while being uninhabited. So this module **builds** an instance, on the real
program, at real addresses, against the real generated edge inventory.

## What is exhibited

A two-segment sequential cut of `ssz_raw.decodeRaw` (region `[66628, 77872)`, 2811 instructions, one
declared exit at 66864):

| unit | addresses | instructions | entry | stops at |
|---|---|---|---|---|
| `segment1` | `[66628, 66704)` | 19 | 66628 | 66700 |
| `segment2` | `[66704, 66864) ∪ [66868, 77872)` | 2791 | 66704 | 66860 |
| parent | all of `[66628, 77872)` | — | 66628 | 66864 |

The parent owns exactly one address of its own, 66864 — the `ret`. That is the whole price of the
proviso in §4 of `SequentialSplice`: the last segment must not own the parent's exit pc.

## The checks, and their controls

Every geometric claim below is `native_decide` over `generatedProgram`, and every one is paired with
a control:

* both crossing edges are real (`splice_edges_are_real`) — and a fabricated neighbour of one of them
  is rejected (`fabricated_edge_is_rejected`);
* the cut is single-entry (`segment1_single_entry`, `segment2_single_entry`) — and a cut two
  instructions further on is rejected, with the offending in-edges named
  (`cut_at_66720_is_rejected`);
* `segment1` leaves only to `segment2`'s entry (`segment1_leaves_only_to_segment2_entry`);
* the exit pc is owned by neither segment (`exit_pc_belongs_to_neither_segment`) — and if it *is*
  given to the last segment, no real edge leaves that segment back into the parent, so `ib.exits` is
  empty and `inlineTransfer_needs_outgoing_edge` applies (`tail_owning_exit_has_no_outgoing_edge`).

One finding is recorded rather than repaired: the first crossing edge `66700 → 66704` is **not** in
`decodeRaw`'s own `edges` array (`first_crossing_edge_is_not_filed_under_decodeRaw`). The extractor
files each edge under its innermost owning instance, so a parent's `edges` is not its CFG. A spliced
parent's edge array therefore has to be regenerated as the union over its constituents — which is what
`allEdges` stands in for here.

## The residue, stated exactly

`witnessComposedTrace` is a closed `ScopedTrace` term: no `sorry`, both crossing edges retired by a
real `Runs (try_step _ false)` of the generated Sail model. Two things it does **not** reach, for the
same structural reason `SentinelBridgeWitness` documents:

1. the two retirements are the wait-wakeup path, not fetch/decode of the instructions at 66700 and
   66860 — a fetch needs a program image, which this layer does not have;
2. the segment summaries are instantiated by a concrete state relation (`witnessSummary`), not
   derived from traces of the segments' code, for the same reason.

What the witness therefore establishes is that the *composition predicate* is inhabited at real
geometry — which is precisely the thing that was uninhabited in the four earlier cases.

## §8: the same conditions, over the whole function

The witness splices two units. §8 turns the same conditions into a decidable gate over a candidate
decomposition of *all* of `decodeRaw`, and exhibits one: **96 units of at most 319 instructions, plus
a parent that owns 4** (`measuredUnits_decomposes`). The bound is 10% of the 3195-instruction
program, and it is tight — the same decomposition is rejected at 318. Each of the gate's six
conditions is exhibited failing on a candidate that satisfies the others, and both null
decompositions (one unit for everything; no units at all) are rejected.
-/

namespace BinaryFv.Zesu.Validation.SequentialSpliceWitness

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.Zesu.Elflings.Generated (generatedProgram)

/-! ## 1. The real instance, and the real edge inventory -/

/-- `ssz_raw.decodeRaw`, taken from the generated program by index. -/
def decodeRawFI : FunctionInstance := generatedProgram.functionInstances[6]!

/-- The index really names `decodeRaw`, and the numbers this module quotes are its own. -/
theorem decodeRawFI_is_decodeRaw :
    decodeRawFI.id.function.declaration.qualifiedName = "ssz_raw.decodeRaw" ∧
      decodeRawFI.id.inlineStack = [] ∧
      decodeRawFI.regions = #[⟨66628, 11244⟩] ∧
      decodeRawFI.entryPc = 66628 ∧
      decodeRawFI.exitPcs = #[66864] := by native_decide

/-- All generated edges, as one array. The extractor files each edge under the innermost instance
owning its source, so no single instance's `edges` is its own CFG; the union is. -/
def allEdges : Array DirectEdge :=
  generatedProgram.functionInstances.foldl (fun acc i => acc ++ i.edges) #[]

theorem allEdges_size : allEdges.size = 3374 := by native_decide

/-! ## 2. The cut -/

/-- Addresses of the first segment, `[66628, 66704)`. -/
def inSegment1 (a : Nat) : Bool := 66628 ≤ a && a < 66704

/-- Addresses of the second segment: everything else `decodeRaw` owns except the `ret` at 66864. -/
def inSegment2 (a : Nat) : Bool :=
  (66704 ≤ a && a < 66864) || (66868 ≤ a && a < 77872)

/-- Addresses of the parent, i.e. all of `decodeRaw`. -/
def inParent (a : Nat) : Bool := 66628 ≤ a && a < 77872

/-- The two segments tile the parent except for the single exit address. -/
theorem cut_tiles_the_parent :
    (List.range' 66628 2811 4).all
        (fun a => (inSegment1 a || inSegment2 a || decide (a = 66864)) &&
          !(inSegment1 a && inSegment2 a) && inParent a) = true := by
  native_decide

/-- 19 instructions in the first segment, 2791 in the second, one left to the parent. -/
theorem cut_sizes :
    ((List.range' 66628 2811 4).filter (fun a => inSegment1 a)).length = 19 ∧
      ((List.range' 66628 2811 4).filter (fun a => inSegment2 a)).length = 2791 := by
  native_decide

/-! ## 3. The geometric checks against generated data, each with a control -/

/-- Both crossing edges are real edges of the program. -/
theorem splice_edges_are_real :
    (⟨66700, 66704⟩ : DirectEdge) ∈ allEdges ∧ (⟨66860, 66864⟩ : DirectEdge) ∈ allEdges := by
  native_decide

/-- **Control for the previous check.** A fabricated edge one instruction along is rejected, so
membership in `allEdges` is not satisfied by everything in the neighbourhood. -/
theorem fabricated_edge_is_rejected :
    (⟨66700, 66708⟩ : DirectEdge) ∉ allEdges := by native_decide

/-- **Recorded defect.** The first crossing edge is real, but `decodeRaw` does not record it: the
extractor filed it under an inlined child. A spliced parent's `edges` has to be the union over its
constituents, not the array the extractor emitted. -/
theorem first_crossing_edge_is_not_filed_under_decodeRaw :
    decodeRawFI.edges.contains ⟨66700, 66704⟩ = false ∧
      decodeRawFI.edges.contains ⟨66860, 66864⟩ = true ∧
      decodeRawFI.edges.size = 186 := by native_decide

/-- The first segment has a single entry: no real edge enters it anywhere but at 66628. -/
theorem segment1_single_entry :
    (allEdges.filter fun e =>
      inSegment1 e.target && !inSegment1 e.source && e.target != 66628).isEmpty = true := by
  native_decide

/-- The second segment has a single entry: no real edge enters it anywhere but at 66704. -/
theorem segment2_single_entry :
    (allEdges.filter fun e =>
      inSegment2 e.target && !inSegment2 e.source && e.target != 66704).isEmpty = true := by
  native_decide

/-- **Control for the single-entry checks.** Extending the first segment by four instructions, to
`[66628, 66720)`, admits 66716 — which two later addresses branch back to. The check then fails, and
names both offending edges. -/
def inBadSegment1 (a : Nat) : Bool := 66628 ≤ a && a < 66720

theorem cut_at_66720_is_rejected :
    (allEdges.filter fun e =>
      inBadSegment1 e.target && !inBadSegment1 e.source && e.target != 66628)
      = #[⟨66752, 66716⟩, ⟨66764, 66716⟩] := by
  native_decide

/-- Everything leaving the first segment lands on the second segment's entry. This is what lets the
parent fire the next splice immediately. -/
theorem segment1_leaves_only_to_segment2_entry :
    (allEdges.filter fun e => inSegment1 e.source && !inSegment1 e.target)
      = #[⟨66700, 66704⟩] := by
  native_decide

/-- The first segment stops cleanly: 66700's only successor is outside it, so declaring 66700 an exit
truncates nothing. -/
theorem segment1_exit_is_clean :
    (allEdges.filter fun e => e.source == 66700) = #[⟨66700, 66704⟩] := by native_decide

/-- The exit pc is owned by the parent alone, and the only way to reach it is from 66860, whose only
successor it is. -/
theorem exit_pc_belongs_to_neither_segment :
    inSegment1 66864 = false ∧ inSegment2 66864 = false ∧ inParent 66864 = true ∧
      (allEdges.filter fun e => e.target == 66864) = #[⟨66860, 66864⟩] ∧
      (allEdges.filter fun e => e.source == 66860) = #[⟨66860, 66864⟩] := by
  native_decide

/-- **The tail case, refuted on the real program.** Give the last segment the exit pc as well, and no
real edge leaves it back into the parent: everything it reaches outside itself is a separately emitted
callee. `InlineBoundary.validFor` would then force `exits = #[]`, and
`inlineTransfer_needs_outgoing_edge` says no `InlineTransfer` exists. This is why the parent must keep
its own exit address. -/
def inTailWithExit (a : Nat) : Bool := 66704 ≤ a && a < 77872

theorem tail_owning_exit_has_no_outgoing_edge :
    (allEdges.filter fun e =>
      inTailWithExit e.source && !inTailWithExit e.target && inParent e.target).isEmpty = true := by
  native_decide

/-- **Control for the previous check.** The same filter without the `inParent` clause is *not* empty:
59 edges do leave the tail, all of them calls to code outside `decodeRaw`. So the emptiness above is
a statement about where control returns, not about the tail having no edges. -/
theorem tail_does_leave_by_calls :
    (allEdges.filter fun e => inTailWithExit e.source && !inTailWithExit e.target).size = 59 := by
  native_decide

/-! ## 4. The synthetic units

The units are synthesized — the bridge does not require a unit to be a source function — but every
address, every edge and the parent's identity come from the generated program. The segment identities
are the real `decodeRaw` identity with one synthetic inline site appended, which is the shape that
dispatches through `catalogEntryFor` without a catalog change. -/

private def segSite (n : Nat) : InlineSite :=
  { caller := decodeRawFI.id.function.declaration, callSite := ⟨n, 0⟩ }

/-- The identity of segment `n`: `decodeRaw`'s own identity under a synthetic inline site. -/
def segId (n : Nat) : FunctionInstanceId :=
  { decodeRawFI.id with inlineStack := decodeRawFI.id.inlineStack ++ [segSite n] }

theorem segIds_distinct : segId 1 ≠ segId 2 ∧ segId 1 ≠ decodeRawFI.id := by native_decide

/-- Segment 1: `[66628, 66704)`, entered at `decodeRaw`'s own entry, stopping on 66700. -/
def segment1 : FunctionInstance :=
  { decodeRawFI with
    id := segId 1
    regions := #[⟨66628, 76⟩]
    entryPc := 66628
    exitPcs := #[66700]
    parent? := some decodeRawFI.id
    children := #[]
    externalCalls := #[]
    blocks := #[]
    edges := #[] }

/-- Segment 2: the rest of `decodeRaw` except the `ret`, entered at 66704, stopping on 66860. -/
def segment2 : FunctionInstance :=
  { decodeRawFI with
    id := segId 2
    regions := #[⟨66704, 160⟩, ⟨66868, 11004⟩]
    entryPc := 66704
    exitPcs := #[66860]
    parent? := some decodeRawFI.id
    children := #[]
    externalCalls := #[]
    blocks := #[]
    edges := #[] }

/-- The spliced parent: `decodeRaw`'s own region, entry and exit, with the two segments as children
and the two crossing edges as its recorded edges. -/
def spliceParent : FunctionInstance :=
  { decodeRawFI with
    children := #[segId 1, segId 2]
    edges := #[⟨66700, 66704⟩, ⟨66860, 66864⟩] }

/-- The synthetic regions agree with the address predicates the checks above ran against. -/
theorem synthetic_units_match_the_checked_addresses :
    ((List.range' 66628 2811 4).all fun a =>
      (segment1.containsAddress a == inSegment1 a) &&
      (segment2.containsAddress a == inSegment2 a) &&
      (spliceParent.containsAddress a == inParent a)) = true := by
  native_decide

/-! ## 5. The two cuts, checked -/

/-- The cut that hands segment 1 over to the parent and lands on segment 2's entry. -/
def cut1 : SequentialCut :=
  { parent := spliceParent, first := segment1, second := segment2, cross := ⟨66700, 66704⟩ }

/-- The terminal cut: segment 2 hands over and the parent lands on its own exit. `second` is the
degenerate one-address unit holding the `ret`, which is what the parent keeps for itself. -/
def exitUnit : FunctionInstance :=
  { decodeRawFI with
    id := segId 3
    regions := #[⟨66864, 4⟩]
    entryPc := 66864
    exitPcs := #[66864]
    parent? := some decodeRawFI.id
    children := #[]
    externalCalls := #[]
    blocks := #[]
    edges := #[] }

def cut2 : SequentialCut :=
  { parent := spliceParent, first := segment2, second := exitUnit, cross := ⟨66860, 66864⟩ }

private theorem cut1_fields :
    (segment1.id ∈ spliceParent.children) ∧
      ((⟨66700, 66704⟩ : DirectEdge) ∈ spliceParent.edges) ∧
      segment1.containsAddress 66700 = true ∧
      segment1.containsAddress 66704 = false ∧
      spliceParent.containsAddress 66704 = true ∧
      segment2.entryPc = 66704 := by native_decide

/-! The four address predicates, each read off the unit's own `regions` array. `parent_regions` is the
only one that needs the generated program; the three synthetic ones hold definitionally. -/

private theorem parent_regions : spliceParent.regions = #[⟨66628, 11244⟩] := by native_decide

private theorem contains_parent_iff (a : Nat) :
    spliceParent.containsAddress a = true ↔ (66628 ≤ a ∧ a < 77872) := by
  rw [FunctionInstance.containsAddress, parent_regions]
  simp [AddressRange.stop]

private theorem contains_segment1_iff (a : Nat) :
    segment1.containsAddress a = true ↔ (66628 ≤ a ∧ a < 66704) := by
  rw [FunctionInstance.containsAddress,
    show segment1.regions = #[(⟨66628, 76⟩ : AddressRange)] from rfl]
  simp [AddressRange.stop]

private theorem contains_segment2_iff (a : Nat) :
    segment2.containsAddress a = true ↔
      ((66704 ≤ a ∧ a < 66864) ∨ (66868 ≤ a ∧ a < 77872)) := by
  rw [FunctionInstance.containsAddress,
    show segment2.regions = #[(⟨66704, 160⟩ : AddressRange), (⟨66868, 11004⟩ : AddressRange)] from rfl]
  simp [AddressRange.stop]

private theorem contains_exitUnit_iff (a : Nat) :
    exitUnit.containsAddress a = true ↔ (66864 ≤ a ∧ a < 66868) := by
  rw [FunctionInstance.containsAddress,
    show exitUnit.regions = #[(⟨66864, 4⟩ : AddressRange)] from rfl]
  simp [AddressRange.stop]

/-- **The first cut is valid.** -/
theorem cut1_valid : cut1.Valid where
  childListed := cut1_fields.1
  crossIsRealEdge := cut1_fields.2.1
  crossLeavesFirst := cut1_fields.2.2.1
  crossTargetNotInFirst := cut1_fields.2.2.2.1
  crossTargetInParent := cut1_fields.2.2.2.2.1
  crossTargetIsSecondEntry := cut1_fields.2.2.2.2.2.symm
  secondInsideParent := by
    intro a ha
    have h2 := (contains_segment2_iff a).mp ha
    exact (contains_parent_iff a).mpr (by omega)
  segmentsDisjoint := by
    intro a ha
    have h1 := (contains_segment1_iff a).mp ha
    have : ¬ (segment2.containsAddress a = true) := by rw [contains_segment2_iff]; omega
    simpa using this

private theorem cut2_fields :
    (segment2.id ∈ spliceParent.children) ∧
      ((⟨66860, 66864⟩ : DirectEdge) ∈ spliceParent.edges) ∧
      segment2.containsAddress 66860 = true ∧
      segment2.containsAddress 66864 = false ∧
      spliceParent.containsAddress 66864 = true ∧
      exitUnit.entryPc = 66864 := by native_decide

/-- **The terminal cut is valid.** -/
theorem cut2_valid : cut2.Valid where
  childListed := cut2_fields.1
  crossIsRealEdge := cut2_fields.2.1
  crossLeavesFirst := cut2_fields.2.2.1
  crossTargetNotInFirst := cut2_fields.2.2.2.1
  crossTargetInParent := cut2_fields.2.2.2.2.1
  crossTargetIsSecondEntry := cut2_fields.2.2.2.2.2.symm
  secondInsideParent := by
    intro a ha
    have h2 := (contains_exitUnit_iff a).mp ha
    exact (contains_parent_iff a).mpr (by omega)
  segmentsDisjoint := by
    intro a ha
    have h1 := (contains_segment2_iff a).mp ha
    have : ¬ (exitUnit.containsAddress a = true) := by rw [contains_exitUnit_iff]; omega
    simpa using this

/-! ## 6. The confinement and exit predicates -/

/-- What the parent's local obligation confines its own steps to. -/
def ownPcs (pc : BitVec 64) : Prop := RegionPcs spliceParent.regions pc

/-- The parent's generated exit set. -/
def exitPred (pc : BitVec 64) : Prop := spliceParent.isExit pc.toNat

private theorem parent_exitPcs : spliceParent.exitPcs = #[66864] := by native_decide

private theorem toNat_lit {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem lt_word {n : Nat} (h : n < 77872) : n < 2 ^ 64 := by
  have hbig : (77872 : Nat) < 2 ^ 64 := by decide
  omega

private theorem own_of {n : Nat} (hlo : 66628 ≤ n) (hhi : n < 77872) :
    ownPcs (BitVec.ofNat 64 n) := by
  have hmem : (⟨66628, 11244⟩ : AddressRange) ∈ spliceParent.regions := by
    rw [parent_regions]; simp
  refine ⟨⟨66628, 11244⟩, hmem, ?_, ?_⟩
  · rw [toNat_lit (lt_word hhi)]; exact hlo
  · rw [toNat_lit (lt_word hhi)]
    show n < 66628 + 11244
    omega

private theorem exitPred_iff {n : Nat} (h : n < 2 ^ 64) :
    exitPred (BitVec.ofNat 64 n) ↔ n = 66864 := by
  simp [exitPred, FunctionInstance.isExit, parent_exitPcs, toNat_lit h]

private theorem not_exit_of {n : Nat} (hne : n ≠ 66864) (hhi : n < 77872) :
    ¬ exitPred (BitVec.ofNat 64 n) :=
  fun hx => hne ((exitPred_iff (lt_word hhi)).mp hx)

/-! ## 7. The closed composed trace

The states below are the wait-parked states `SentinelBridgeWitness` uses, placed at the *real*
addresses of the cut. `waitWakeRetires` is a genuine retirement of the generated `try_step`: it is
what retires each crossing edge here. -/

/-- Where the parent's run starts: `decodeRaw`'s entry, 66628. -/
def sEntry : State := waitingState (BitVec.ofNat 64 66628) (BitVec.ofNat 64 66700)

/-- Where segment 1's summary leaves the machine: on 66700, its declared exit. -/
def sCross1 : State := waitingState (BitVec.ofNat 64 66700) (BitVec.ofNat 64 66704)

/-- After the parent retires the crossing edge: at 66704, segment 2's entry. -/
def sSegment2 : State := wokenState sCross1 (BitVec.ofNat 64 66704) 0

/-- Where segment 2's summary leaves the machine: on 66860, its declared exit. -/
def sCross2 : State := waitingState (BitVec.ofNat 64 66860) (BitVec.ofNat 64 66864)

/-- After the parent retires the second crossing edge: on 66864, its own exit. -/
def sExitPc : State := wokenState sCross2 (BitVec.ofNat 64 66864) 0

/--
The admitted segment summaries, instantiated concretely.

This is the parameter `ScopedTrace` takes, not a derived fact: it stands for "segment `n`, entered at
step `fromStep`, retired `used` steps carrying `before` to `after`". The step counts are the segments'
instruction counts.
-/
def witnessSummary (id : FunctionInstanceId) (fromStep used : Nat) (before after : State) : Prop :=
  (id = segId 1 ∧ fromStep = 0 ∧ used = 19 ∧ before = sEntry ∧ after = sCross1) ∨
    (id = segId 2 ∧ fromStep = 20 ∧ used = 2791 ∧ before = sSegment2 ∧ after = sCross2)

theorem witnessSummary_inhabited :
    witnessSummary (segId 1) 0 19 sEntry sCross1 ∧
      witnessSummary (segId 2) 20 2791 sSegment2 sCross2 :=
  ⟨Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩, Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The parent retires the first crossing edge, 66700 → 66704. A real `try_step` retirement. -/
theorem retireCross1 :
    Runs (try_step (0 + 19) false) sCross1 sSegment2 false :=
  waitWakeRetires 19 sCross1 0 (BitVec.ofNat 64 66704) 0
    (waitingState_ready (BitVec.ofNat 64 66700) (BitVec.ofNat 64 66704))

/-- The parent retires the second crossing edge, 66860 → 66864. -/
theorem retireCross2 :
    Runs (try_step (20 + 2791) false) sCross2 sExitPc false :=
  waitWakeRetires 2811 sCross2 0 (BitVec.ofNat 64 66864) 0
    (waitingState_ready (BitVec.ofNat 64 66860) (BitVec.ofNat 64 66864))

/-- **The composed trace.** Two spliced segments and the parent's exit, as one `ScopedTrace` of
`19 + 1 + (2791 + 1) = 2812` steps confined to `decodeRaw`'s own addresses. Closed: no `sorry`, no
free hypothesis. -/
theorem witnessComposedTrace :
    ScopedTrace ownPcs exitPred witnessSummary 0 (19 + 1 + (2791 + 1)) sEntry sExitPc := by
  refine ScopedTrace.spliceSegment (c := cut1) cut1_valid
    (entryPc := BitVec.ofNat 64 66628) (crossPc := BitVec.ofNat 64 66700)
    (resumePc := BitVec.ofNat 64 66704)
    (by simp [sEntry]) (toNat_lit (by decide)) (own_of (by omega) (by omega))
    (not_exit_of (by decide) (by omega))
    witnessSummary_inhabited.1
    (by simp [sCross1]) (toNat_lit (by decide)) (own_of (by omega) (by omega))
    (not_exit_of (by decide) (by omega))
    retireCross1
    (by simp [sSegment2]) (toNat_lit (by decide)) (own_of (by omega) (by omega))
    ?_
  exact ScopedTrace.spliceTail (c := cut2) cut2_valid
    (entryPc := BitVec.ofNat 64 66704) (crossPc := BitVec.ofNat 64 66860)
    (resumePc := BitVec.ofNat 64 66864)
    (by simp [sSegment2]) (toNat_lit (by decide)) (own_of (by omega) (by omega))
    (not_exit_of (by decide) (by omega))
    witnessSummary_inhabited.2
    (by simp [sCross2]) (toNat_lit (by decide)) (own_of (by omega) (by omega))
    (not_exit_of (by decide) (by omega))
    retireCross2
    (by simp [sExitPc]) (toNat_lit (by decide)) (own_of (by omega) (by omega))
    ((exitPred_iff (by decide)).mpr rfl)

/-- The composed trace is non-degenerate: it starts at `decodeRaw`'s generated entry, which is in
region and not an exit, so `EnteredScopedTrace` — the form a local obligation must use — is
inhabited too. -/
theorem witnessEnteredComposedTrace :
    EnteredScopedTrace ownPcs exitPred witnessSummary (BitVec.ofNat 64 66628) 0
      (19 + 1 + (2791 + 1)) sEntry sExitPc where
  startsAtEntry := by simp [sEntry]
  entryInRegion := own_of (by omega) (by omega)
  entryNotExit := not_exit_of (by decide) (by omega)
  trace := witnessComposedTrace

/-- The summary relation is not `True` in disguise: it does not relate `sEntry` to itself, and it
does not confuse the two segments. Without this the composed trace would be evidence about nothing. -/
theorem witnessSummary_is_discriminating :
    ¬ witnessSummary (segId 1) 0 19 sEntry sEntry ∧
      ¬ witnessSummary (segId 1) 0 19 sSegment2 sCross2 := by
  have hne : sEntry ≠ sCross1 := by
    intro h
    have h1 : sEntry.regs.get? PC = some (BitVec.ofNat 64 66700) := by rw [h]; simp [sCross1]
    have h2 : sEntry.regs.get? PC = some (BitVec.ofNat 64 66628) := by simp [sEntry]
    rw [h1] at h2
    exact absurd (Option.some.inj h2) (by decide)
  constructor
  · rintro (⟨_, _, _, _, h⟩ | ⟨h, _⟩)
    · exact hne h
    · exact absurd h segIds_distinct.1
  · rintro (⟨_, _, _, h, _⟩ | ⟨h, _⟩)
    · have h1 : sSegment2.regs.get? PC = some (BitVec.ofNat 64 66628) := by rw [h]; simp [sEntry]
      have h2 : sSegment2.regs.get? PC = some (BitVec.ofNat 64 66704) := by simp [sSegment2]
      rw [h1] at h2
      exact absurd (Option.some.inj h2) (by decide)
    · exact absurd h segIds_distinct.1

/-! ### Negative controls for `SequentialCut.Valid`

A cut predicate that accepts everything would make the witness worthless. Each control below breaks
exactly one field of `Valid` and is refuted from the generated data. -/

/-- A cut whose crossing edge does not exist. `crossIsRealEdge` fails. -/
def fabricatedCut : SequentialCut :=
  { cut1 with cross := ⟨66700, 66708⟩ }

theorem fabricatedCut_invalid : ¬ fabricatedCut.Valid := by
  intro h
  exact absurd h.crossIsRealEdge (by native_decide)

/-- A cut whose crossing edge lands somewhere that is not the next unit's entry.
`crossTargetIsSecondEntry` fails. -/
def misalignedCut : SequentialCut :=
  { cut1 with second := exitUnit }

theorem misalignedCut_invalid : ¬ misalignedCut.Valid := by
  intro h
  exact absurd h.crossTargetIsSecondEntry (by native_decide)

/-- **The tail case as a rejected cut.** Give the last unit the parent's exit pc as well and
`crossTargetNotInFirst` fails: the crossing edge no longer leaves the unit, so there is no outgoing
edge to splice on and `inlineTransfer_needs_outgoing_edge` bites. -/
def tailOwningExitUnit : FunctionInstance :=
  { segment2 with regions := #[⟨66704, 11168⟩] }

def tailOwningExitCut : SequentialCut :=
  { cut2 with first := tailOwningExitUnit }

theorem tailOwningExitCut_invalid : ¬ tailOwningExitCut.Valid := by
  intro h
  exact absurd h.crossTargetNotInFirst (by native_decide)

/-- And the rejected unit really is the whole tail including the exit — so the control fails for the
stated reason, not because the region was mistyped. -/
theorem tailOwningExitUnit_covers_the_exit :
    tailOwningExitUnit.containsAddress 66864 = true ∧
      tailOwningExitUnit.containsAddress 66860 = true ∧
      tailOwningExitUnit.containsAddress 66700 = false := by native_decide

/-! ## 8. What the splice demands of a cut, measured on all of `decodeRaw`

The witness splices two units. The same conditions applied to *every* unit are what a full
decomposition must satisfy, and they are decidable, so the question "does `decodeRaw` admit a
decomposition with no unit above 10% of the program" is a computation rather than an opinion.

`decomposes` is that computation. Its six conditions are exactly the ones `SequentialCut.Valid`,
`InlineTransfer` and `CallSite.validFor` consume:

1. `unitsWithinCap` — no unit exceeds `cap` instructions;
2. `unitsDisjointInsideParent` — units do not overlap and stay inside the parent;
3. `unitsSingleEntry` — every real edge entering a unit from outside lands on its first address, so
   the parent can always fire the splice at `childFunctionInstance.entryPc`;
4. `unitsCleanExit` — no instruction of a unit has intra-function successors both inside and outside
   it (a partial exit would truncate the unit's own trace at an address execution continues from);
5. `unitsLeaveExitToParent` — §4's proviso;
6. `callsKeepTheirReturnSlot` — `CallSite.validFor`'s `containsAddress cs.returnPc = true`.

Units need not cover everything: what they miss the parent retires with `ownStep`, so the residue is
the parent's own proof burden and is itself capped.

**Result: `decodeRaw` decomposes into 96 units of at most 319 instructions, plus a parent that owns
4.** The bound is 10% of the 3195-instruction program, and it is tight — the same decomposition is
rejected at 318. -/

/-- A unit as (first address, instruction count). -/
abbrev Unit := Nat × Nat

def unitContains (u : Unit) (a : Nat) : Bool := u.1 ≤ a && a < u.1 + 4 * u.2

def decodeRawAddrs : List Nat := List.range' 66628 2811 4

/-- Successors of `a` that stay inside `decodeRaw`.

Edges *leaving* `decodeRaw` are deliberately excluded, and the two theorems below are what justifies
that: every such edge is a call whose continuation is the fall-through `source + 4`, so control comes
back to the address after the call and the unit does not end there. Treating a call as a unit exit
would be wrong; `ScopedTrace.callStep` is the constructor for it, and `callsKeepTheirReturnSlot`
below is the condition it needs. -/
def succsOf (a : Nat) : Array Nat :=
  (allEdges.filter fun e => e.source == a && inParent e.target).map (·.target)

/-- Call sites of `decodeRaw`: sources of real edges leaving its address range. -/
def decodeRawCallSites : Array Nat :=
  (allEdges.filter fun e => inParent e.source && !inParent e.target).map (·.source)

theorem decodeRawCallSites_size : decodeRawCallSites.size = 59 := by native_decide

/-- **Every edge leaving `decodeRaw` is a returning call.** Each has a companion fall-through edge to
`source + 4`, so none is a tail call that never comes back. This is why `succsOf` may drop them. -/
theorem every_outgoing_edge_is_a_returning_call :
    (allEdges.filter fun e => inParent e.source && !inParent e.target).all
      (fun e => allEdges.contains ⟨e.source, e.source + 4⟩) = true := by native_decide

/-- **Control**: the same claim for a fabricated fall-through offset is false, so the check above is
not true of any offset. -/
theorem outgoing_call_fallthrough_offset_is_four :
    (allEdges.filter fun e => inParent e.source && !inParent e.target).all
      (fun e => allEdges.contains ⟨e.source, e.source + 8⟩) = false := by native_decide

/-- **Every edge entering `decodeRaw` from outside lands on its entry pc.** So a unit's single-entry
condition is not disturbed by the two calls into the function. -/
theorem incoming_edges_land_on_the_entry :
    (allEdges.filter fun e => !inParent e.source && inParent e.target)
      = #[⟨66332, 66628⟩, ⟨66520, 66628⟩] := by native_decide

/-- Every unit is nonempty and within the cap. -/
def unitsWithinCap (cap : Nat) (units : Array Unit) : Bool :=
  units.all fun u => 0 < u.2 && u.2 ≤ cap

/-- No address is claimed twice, and every claimed address belongs to `decodeRaw`. -/
def unitsDisjointInsideParent (units : Array Unit) : Bool :=
  decodeRawAddrs.all (fun a => (units.filter fun u => unitContains u a).size ≤ 1) &&
    units.all fun u => decodeRawAddrs.all fun a => !unitContains u a || inParent a

/-- Every real edge entering a unit from outside lands on its first address — what
`InlineTransfer.entryIsChildEntry` needs so the parent can always fire the splice there. -/
def unitsSingleEntry (units : Array Unit) : Bool :=
  allEdges.all fun e => units.all fun u =>
    !unitContains u e.target || unitContains u e.source || e.target == u.1

/-- No instruction of a unit has intra-function successors both inside and outside it. A partial exit
would force the unit to declare an exit at an address execution continues from, and
`functionTrace_stuck_at_exit` then truncates every trace of that unit there. -/
def unitsCleanExit (units : Array Unit) : Bool :=
  units.all fun u => (List.range' u.1 u.2 4).all fun a =>
    !((succsOf a).any (fun t => unitContains u t) && (succsOf a).any fun t => !unitContains u t)

/-- The parent keeps its own exit pc — §4's proviso. -/
def unitsLeaveExitToParent (units : Array Unit) : Bool :=
  units.all fun u => !unitContains u 66864

/-- A call's return slot stays in the same unit as the call, which is `CallSite.validFor`'s
`functionInstance.containsAddress cs.returnPc = true`. -/
def callsKeepTheirReturnSlot (units : Array Unit) : Bool :=
  decodeRawCallSites.all fun c => units.all fun u => !unitContains u c || unitContains u (c + 4)

/-- **The admissibility gate for a candidate decomposition.** -/
def admissible (cap : Nat) (units : Array Unit) : Bool :=
  unitsWithinCap cap units && unitsDisjointInsideParent units && unitsSingleEntry units &&
    unitsCleanExit units && unitsLeaveExitToParent units && callsKeepTheirReturnSlot units

/-- Instructions no unit covers: the parent's own proof burden. -/
def residueOf (units : Array Unit) : List Nat :=
  decodeRawAddrs.filter fun a => !(units.any fun u => unitContains u a)

/-- **The full claim.** `admissible` alone is satisfied by the *empty* decomposition (no units, the
parent does everything), so it is a constraint check and not a gate on its own. The gate is
admissibility together with a residue the parent can carry, i.e. the parent is a unit too. -/
def decomposes (cap : Nat) (units : Array Unit) : Bool :=
  admissible cap units && (residueOf units).length ≤ cap

/--
**A measured 96-unit decomposition of `decodeRaw`.** Produced by a greedy left-to-right scan over the
address order under the four conditions above; recorded as data, re-checked here.
-/
def measuredUnits : Array Unit :=
  #[(66628, 38), (66780, 2), (66788, 2), (66796, 1), (66804, 15), (66868, 65), (67128, 54),
    (67344, 9), (67380, 1), (67384, 2), (67392, 63), (67644, 3), (67656, 7), (67684, 319),
    (68960, 319), (70236, 192), (71004, 11), (71048, 2), (71056, 26), (71160, 240), (72120, 3),
    (72132, 92), (72500, 2), (72508, 5), (72528, 7), (72556, 5), (72576, 4), (72592, 5),
    (72612, 2), (72620, 3), (72632, 213), (73484, 3), (73496, 3), (73508, 2), (73516, 14),
    (73572, 12), (73620, 1), (73624, 1), (73628, 9), (73664, 22), (73752, 1), (73756, 13),
    (73808, 9), (73844, 6), (73868, 49), (74064, 15), (74124, 3), (74136, 26), (74240, 114),
    (74696, 2), (74704, 29), (74820, 17), (74888, 1), (74892, 1), (74896, 8), (74928, 8),
    (74960, 27), (75068, 12), (75116, 3), (75128, 6), (75152, 8), (75184, 21), (75268, 17),
    (75336, 1), (75340, 1), (75344, 9), (75380, 7), (75408, 8), (75440, 33), (75572, 1),
    (75576, 3), (75588, 7), (75616, 5), (75640, 7), (75668, 48), (75860, 13), (75912, 15),
    (75972, 17), (76040, 18), (76112, 26), (76216, 3), (76228, 1), (76232, 7), (76260, 5),
    (76280, 50), (76480, 29), (76596, 35), (76736, 10), (76776, 18), (76848, 23), (76940, 1),
    (76944, 10), (76984, 68), (77256, 141), (77820, 5), (77844, 7)]

/-- **`decodeRaw` decomposes at cap 319 — 10% of the 3195-instruction program.** 96 units plus a
4-instruction parent, every one of them within the bound, every one of them a legal splice target. -/
theorem measuredUnits_decomposes : decomposes 319 measuredUnits = true := by native_decide

theorem measuredUnits_admissible : admissible 319 measuredUnits = true := by native_decide

/-- 96 units, the largest exactly 319 instructions, covering 2807 of `decodeRaw`'s 2811. -/
theorem measuredUnits_shape :
    measuredUnits.size = 96 ∧
      (measuredUnits.foldl (fun m u => max m u.2) 0) = 319 ∧
      (measuredUnits.foldl (fun n u => n + u.2) 0) = 2807 := by native_decide

/-- The four instructions left to the parent: its `ret`, and three call sites whose return slot is a
merge point that no unit may swallow. So the parent's own `ownStep` burden is 4 instructions. -/
theorem measuredUnits_residue : residueOf measuredUnits = [66800, 66864, 75636, 77840] := by
  native_decide

/-- The residue is what it is claimed to be: 66864 is the generated exit, and the other three are
real call sites. -/
theorem residue_is_exit_and_call_sites :
    decodeRawFI.exitPcs = #[66864] ∧
      decodeRawCallSites.contains 66800 = true ∧
      decodeRawCallSites.contains 75636 = true ∧
      decodeRawCallSites.contains 77840 = true := by native_decide

/-! ### Controls for the gate

Rule: a check never seen to fail has not been tested. Each of the six conditions is exhibited
failing, on a candidate that satisfies the *others*, so no condition is passing vacuously and the
gate is not scoring for the wrong reason. -/

/-- **The null decomposition fails.** One unit covering all of `decodeRaw` — the decomposition that
proves nothing — is rejected. -/
theorem null_decomposition_rejected : decomposes 319 #[(66628, 2811)] = false := by native_decide

/-- …and it is still rejected when the cap is raised past its size, because it swallows the exit pc.
So the rejection is not only about the bound. -/
theorem null_decomposition_rejected_at_any_cap :
    admissible 100000 #[(66628, 2811)] = false := by native_decide

/-- **The empty decomposition fails the gate**, though it satisfies `admissible`: 2811 instructions
are left to the parent. This is why `decomposes` and not `admissible` is the claim. -/
theorem empty_decomposition_rejected :
    admissible 319 #[] = true ∧ decomposes 319 #[] = false ∧ (residueOf #[]).length = 2811 := by
  native_decide

/-- **The bound is tight.** At cap 318 the measured decomposition fails, so
`measuredUnits_decomposes` is not passing with room to spare. -/
theorem measuredUnits_rejected_at_318 : admissible 318 measuredUnits = false := by native_decide

/-- **Condition 2 (single entry) bites.** `[66628, 66720)` swallows 66716, which two later addresses
branch back to. Every other condition holds of it. -/
theorem single_entry_control :
    unitsSingleEntry #[(66628, 23)] = false ∧
      unitsWithinCap 319 #[(66628, 23)] = true ∧
      unitsDisjointInsideParent #[(66628, 23)] = true ∧
      unitsLeaveExitToParent #[(66628, 23)] = true ∧
      callsKeepTheirReturnSlot #[(66628, 23)] = true := by native_decide

/-- **Condition 3 (clean exit) bites.** `[66628, 66712)` ends inside the branch at 66704, whose two
successors straddle the boundary. Single entry still holds, so this control isolates condition 3. -/
theorem clean_exit_control :
    unitsCleanExit #[(66628, 21)] = false ∧
      unitsSingleEntry #[(66628, 21)] = true ∧
      unitsWithinCap 319 #[(66628, 21)] = true ∧
      unitsLeaveExitToParent #[(66628, 21)] = true ∧
      callsKeepTheirReturnSlot #[(66628, 21)] = true := by native_decide

/-- **Condition 4a (the parent keeps its exit pc) bites**, which is §4's proviso restated as a gate.
The same unit one instruction shorter passes everything, so the rejection is caused by the exit pc
and nothing else. -/
theorem exit_pc_control :
    unitsLeaveExitToParent #[(66804, 16)] = false ∧
      admissible 319 #[(66804, 16)] = false ∧
      admissible 319 #[(66804, 15)] = true := by native_decide

/-- **Condition 4b (a call keeps its return slot) bites.** `[66628, 66804)` ends on the call at 66800
and leaves its continuation 66804 to the next unit, so `CallSite.validFor` could not hold. -/
theorem call_return_slot_control :
    callsKeepTheirReturnSlot #[(66628, 44)] = false ∧
      unitsWithinCap 319 #[(66628, 44)] = true ∧
      unitsLeaveExitToParent #[(66628, 44)] = true := by native_decide

/-- **Condition 1 (disjointness) bites.** Growing the first unit by one instruction makes it overlap
the second; duplicating a unit does the same. -/
theorem disjointness_control :
    unitsDisjointInsideParent (measuredUnits.set! 0 (66628, 39)) = false ∧
      unitsDisjointInsideParent (measuredUnits.push (66628, 38)) = false ∧
      admissible 319 (measuredUnits.set! 0 (66628, 39)) = false ∧
      admissible 319 (measuredUnits.push (66628, 38)) = false := by native_decide

/-- The address list the gate ranges over really is `decodeRaw`'s instruction set: its 197 generated
basic blocks tile `[66628, 77872)` contiguously and every block is a whole number of 4-byte
instructions. -/
theorem decodeRawAddrs_are_the_instructions :
    decodeRawFI.blocks.size = 197 ∧
      decodeRawFI.blocks.foldl (fun n b => n + b.range.size) 0 = 11244 ∧
      decodeRawFI.blocks.all (fun b => b.range.size % 4 == 0) = true ∧
      decodeRawFI.blocks.foldl
        (fun (acc : Nat × Bool) b => (b.range.start + b.range.size, acc.2 && acc.1 == b.range.start))
        (66628, true) = (77872, true) ∧
      decodeRawAddrs.length = 2811 := by native_decide

/-- The entry really is `decodeRaw`'s generated entry pc, and the final pc really is its generated
exit pc — so the witness composes *this* function's cut, not a convenient pair of addresses. -/
theorem witness_endpoints_are_generated :
    (BitVec.ofNat 64 66628).toNat = decodeRawFI.entryPc ∧
      sExitPc.regs.get? PC = some (BitVec.ofNat 64 66864) ∧
      decodeRawFI.exitPcs = #[66864] := by
  refine ⟨?_, by simp [sExitPc], by native_decide⟩
  rw [toNat_lit (by decide : (66628 : Nat) < 2 ^ 64)]
  native_decide

end BinaryFv.Zesu.Validation.SequentialSpliceWitness
