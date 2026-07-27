import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.CatalogSatisfiability
import BinaryFv.SSZ.Zesu.Elfling.ManifestCheck

/-!
# Joined refutations of generated local obligations

`entryPc ∈ exitPcs` alone does not refute a local obligation. The actual manifest proposition first
quantifies over a `childSummary` satisfying `ChildSummariesAvailable`, then its inner contract takes
`pre` as a hypothesis. A refutation therefore needs witnesses for both premise layers before the
impossible `EnteredScopedTrace.entryNotExit` field can be used.

This module performs that complete join for every generated entry-is-exit instance with no callees.
The empty child-summary relation satisfies `ChildSummariesAvailable` exactly because the consumer
`calleeFunctionInstances` returns `#[]`; catalog satisfiability supplies a model of `pre`; and the
final proof uses `functionInstanceExitPred` itself. There are 16 such instances, not the previously
reported 10. This is deliberately red validation evidence and is not imported by the theorem graph.
-/

namespace BinaryFv.SSZ.Zesu.Validation.LocalObligationRefutations

set_option maxRecDepth 100000

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedManifest generatedProgram)
open BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.SSZ.Zesu.MemoryRepresentation

private theorem routine_pre_satisfiable_of_routine_satisfiable
    {p : ContractParams} {function : FunctionId} {tag : RoutineTag}
    (henv : ValidEnvironment p.env)
    (hsat : routineSatisfiable p function tag) :
    FunctionInstanceContract.PreSatisfiable (routineContract p function tag).contract := by
  cases tag <;> exact hsat henv

private theorem catalogPreSatisfiable (i : Nat) (h : i < catalog.size)
    (hlive : catalog[i].isLive = true) :
    FunctionInstanceContract.PreSatisfiable
      (routineContract canonicalContractParams catalog[i].functionId catalog[i].tag).contract := by
  exact routine_pre_satisfiable_of_routine_satisfiable canonical_environment_valid
    (canonical_catalog_satisfiability catalog[i]
      (Array.mem_iff_getElem.mpr ⟨i, h, rfl⟩) hlive)

/-- With no actual callees, the empty relation realizes every demanded child summary. -/
theorem childSummariesAvailable_of_no_callees
    {p : ContractParams} {program : Program} {functionInstance : FunctionInstance}
    (hno : calleeFunctionInstances program functionInstance = #[]) :
    ChildSummariesAvailable p program functionInstance (fun _ _ _ _ _ => False) := by
  intro callee hcallee
  rw [hno] at hcallee
  simp at hcallee

/-- The complete refutation join: both hypothesis layers are inhabited before `entryNotExit` is
contradicted. No generated-data fact is hidden in this generic lemma. -/
theorem localTraceObligation_false_of_no_callees_entry_exit
    {p : ContractParams} {program : Program} {functionInstance : FunctionInstance}
    {entry : CatalogEntry}
    (found : catalogEntryFor functionInstance.id.function = some entry)
    (hsat : FunctionInstanceContract.PreSatisfiable
      (routineContract p functionInstance.id.function entry.tag).contract)
    (hno : calleeFunctionInstances program functionInstance = #[])
    (hexit : functionInstanceExitPred functionInstance
      (functionInstanceEntryWord functionInstance)) :
    ¬ functionInstanceLocalTraceObligation p program functionInstance := by
  intro hlocal
  unfold functionInstanceLocalTraceObligation at hlocal
  rw [found] at hlocal
  have himpl := hlocal (fun _ _ _ _ _ => False)
    (childSummariesAvailable_of_no_callees hno)
  unfold routineLocalObligation at himpl
  obtain ⟨args, state, hpre⟩ := hsat
  obtain ⟨_, _, _, htrace, _⟩ := himpl args 0 state hpre
  exact htrace.entryNotExit hexit

/-! ## Exact generated subset -/

/-- Indices are an internal join device, not the public identity of a ledger row. This computation
uses `calleeFunctionInstances`, the same dependency function consumed by
`ChildSummariesAvailable`. -/
def noCalleeEntryExitIndices : List Nat :=
  (generatedProgram.functionInstances.zipIdx.filterMap fun (functionInstance, index) =>
    if functionInstance.exitPcs.contains functionInstance.entryPc &&
        (calleeFunctionInstances generatedProgram functionInstance).isEmpty then
      some index
    else none).toList

/-- The measured subset is exact and moves the build in either direction. -/
theorem no_callee_entry_exit_indices :
    noCalleeEntryExitIndices =
      [2, 5, 36, 46, 48, 50, 59, 61, 71, 77, 79, 82, 89, 121, 127, 128] := by
  native_decide

/-- Every measured row is a genuine false individual obligation. This theorem verifies the join,
not merely its three ingredients. -/
theorem no_callee_entry_exit_obligations_false :
    ∀ i ∈ noCalleeEntryExitIndices,
      ¬ functionInstanceLocalTraceObligation canonicalContractParams generatedProgram
        generatedProgram.functionInstances[i]! := by
  intro i hi
  rw [no_callee_entry_exit_indices] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals
    apply localTraceObligation_false_of_no_callees_entry_exit
    · rfl
    · first
      | exact catalogPreSatisfiable 42 (by decide) (by decide)
      | exact catalogPreSatisfiable 41 (by decide) (by decide)
      | exact catalogPreSatisfiable 25 (by decide) (by decide)
      | exact catalogPreSatisfiable 20 (by decide) (by decide)
    · apply Array.eq_empty_of_size_eq_zero
      native_decide
    · simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
      native_decide

/-! ## Stable ledger keys -/

/-- A row key. `entryPc` alone is not unique; the fully qualified routine name completes it. -/
structure InstanceKey where
  entryPc : Nat
  routine : String
deriving Repr, DecidableEq, Inhabited

/-- The complete key population in manifest order. -/
def ledgerKeys : List InstanceKey :=
  generatedManifest.toList.map fun row =>
    { entryPc := row.entryPc, routine := row.qualifiedName }

/-- The stable keys of the 16 checked refutations. -/
def noCalleeEntryExitKeys : List InstanceKey :=
  noCalleeEntryExitIndices.map fun index =>
    { entryPc := generatedManifest[index]!.entryPc
      routine := generatedManifest[index]!.qualifiedName }

/-- The requested key is unique for all 141 rows. This prevents a ledger from silently collapsing
two instances that share an entry PC. -/
theorem ledger_keys_are_complete_and_unique :
    ledgerKeys.length = generatedProgram.functionInstances.size ∧
      generatedProgram.functionInstances.size = 141 ∧ ledgerKeys.Nodup := by
  native_decide

/-- The false set is pinned by stable key, not merely by array position. -/
theorem no_callee_entry_exit_keys :
    noCalleeEntryExitKeys =
      [{ entryPc := 66288, routine := "raw_decoder_root.allocator" },
       { entryPc := 66624, routine := "raw_decoder_root.allocatorFree" },
       { entryPc := 69564, routine := "ssz_raw.bytesAt" },
       { entryPc := 72132, routine := "ssz_raw.bytesAt" },
       { entryPc := 72232, routine := "ssz_raw.bytesAt" },
       { entryPc := 72332, routine := "ssz_raw.bytesAt" },
       { entryPc := 73620, routine := "ssz_raw.bytesAt" },
       { entryPc := 73688, routine := "ssz_raw.bytesAt" },
       { entryPc := 74300, routine := "ssz_raw.bytesAt" },
       { entryPc := 74472, routine := "ssz_raw.bytesAt" },
       { entryPc := 74508, routine := "ssz_raw.bytesAt" },
       { entryPc := 74888, routine := "ssz_raw.bytesAt" },
       { entryPc := 75336, routine := "ssz_raw.bytesAt" },
       { entryPc := 77672, routine := "ssz_raw.bytesAt" },
       { entryPc := 78560, routine := "ssz_raw.requireU32Length" },
       { entryPc := 78868, routine := "ssz_raw.bytesAt" }] := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation.LocalObligationRefutations
