import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.CatalogSatisfiability
import BinaryFv.SSZ.Zesu.Elfling.ManifestCheck

/-!
# Joined refutations of generated local obligations

`entryPc ∈ exitPcs` alone does not refute a local obligation. The actual manifest proposition first
quantifies over a `childSummary` satisfying `ChildSummariesAvailable`, then its inner contract takes
`pre` as a hypothesis. A refutation therefore needs witnesses for both premise layers before the
impossible `EnteredScopedTrace.entryNotExit` field can be used.

This module performs that complete join for generated entry-is-exit instances whose outer summary
premise can be inhabited. For the first 16, the empty child-summary relation works exactly because
the consumer `calleeFunctionInstances` returns `#[]`. For another 12, every actual callee dispatches
to `bytesAt` or `readU32`; their exit bindings are realizable from every state satisfying their entry
bindings, so the universal relation realizes the demanded child summaries.

The converse matters too. The current copy contracts permit a destination inside file-backed code,
but their postcondition requires both that destination to contain the copied bytes and that all code
remain intact. A concrete satisfiable precondition makes those clauses disagree, so no child-summary
relation can realize a `memcpy` or `memmove` callee. This proves 13 parent obligations only by
vacuity. Catalog satisfiability supplies each refutation's parent `pre`, and the final negative proof
uses `functionInstanceExitPred` itself. This is deliberately red validation evidence and is not
imported by the theorem graph.
-/

namespace BinaryFv.SSZ.Zesu.Validation.LocalObligationRefutations

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

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

/-! ## Callee-bearing refutations

`ChildSummariesAvailable` does not demand a closed machine trace by itself. It demands a relation
containing some bounded summary whose final state realizes each callee's exit binding. To prove that
premise inhabited without pretending a trace exists, the lemmas below use the universal relation and
construct only the exit state the premise actually asks for.
-/

/-- Every entry state of this selected contract admits some state satisfying its prescribed exit
binding. This is precisely the logical content needed to inhabit `ChildSummariesAvailable`; it is
not a machine-execution claim. -/
def ExitRealizable (contract : TaggedContract) : Prop :=
  ∀ (args : contract.Args) (before : State),
    contract.contract.binding.entry args before →
      ∃ after,
        contract.contract.binding.exit args (contract.contract.spec.meaning args) before after

/-! ## An unrealizable copy exit

This is a contract countermodel, not a machine-execution claim. The source byte lives at the
non-file-backed heap-position word and is zero. The permitted destination is file-backed byte
`0x10444`, whose pinned artifact value is 19. `preCopy` admits the state, but `postCopy` requires the
destination to be both zero (`MemoryBytes`) and 19 (`CodeIntact`).
-/

private def badCopyArgs : CopyArgs :=
  { destination := 0x10444
    source := zkvmHeapPos
    length := 1
    contents := ByteArray.mk #[0] }

private noncomputable def badCopyMemoryState : State :=
  { canonicalWitnessState with
      mem := canonicalWitnessState.mem.insert zkvmHeapPos (BitVec.ofNat 8 0) }

private noncomputable def badCopyState : State :=
  withArgumentRegisters badCopyMemoryState badCopyArgs.destination badCopyArgs.source
    badCopyArgs.length 0

private theorem badCopyState_codeIntact :
    canonicalEnvironment.CodeIntact badCopyState := by
  apply codeIntact_withArgumentRegisters
  exact BinaryFv.Binary.ProgramImage.fileBytesMatchMemory_insert_non_file
    (by native_decide) canonicalWitnessState_codeIntact

private theorem badCopyState_memoryBytes :
    MemoryBytes badCopyState badCopyArgs.source badCopyArgs.contents := by
  intro index hindex
  have hsize : badCopyArgs.contents.size = 1 := by native_decide
  rw [hsize] at hindex
  have hzero : index = 0 := by omega
  subst index
  have hbyte : badCopyArgs.contents[0]'hindex = 0 := by rfl
  rw [hbyte]
  simp [badCopyState, badCopyMemoryState, badCopyArgs, withArgumentRegisters,
    Std.ExtHashMap.get?_eq_getElem?]

private theorem badCopyState_preCopy :
    preCopy canonicalEnvironment badCopyArgs badCopyState := by
  refine ⟨badCopyState_memoryBytes, rfl, badCopyState_codeIntact, ?_, ?_, ?_⟩
  all_goals simp [badCopyState, badCopyArgs]

private theorem badCopyPost_impossible (after : State) :
    ¬ postCopy canonicalEnvironment badCopyArgs (.ok badCopyArgs.contents)
      badCopyState after := by
  intro hpost
  have hzero := hpost.2.2.2 0
    (show 0 < badCopyArgs.contents.size by native_decide)
  have hcode := hpost.1 0x10444 (19 : UInt8) (by native_decide)
  have hbyte :
      badCopyArgs.contents[0]'(show 0 < badCopyArgs.contents.size by native_decide) = 0 := by
    rfl
  have hzero' : after.mem.get? 0x10444 = some (BitVec.ofNat 8 0) := by
    simpa only [badCopyArgs, Nat.add_zero, hbyte, UInt8.toNat_zero] using hzero
  have heq := hzero'.symm.trans hcode
  have hne : (some (BitVec.ofNat 8 0) : Option (BitVec 8)) ≠
      some (BitVec.ofNat 8 (19 : UInt8).toNat) := by
    native_decide
  exact hne heq

/-- The canonical `memcpy` exit binding is not realizable from every state satisfying its entry
binding. Non-overlap holds for this witness; overlap is not the source of the contradiction. -/
theorem memcpy_exit_not_realizable (function : FunctionId) :
    ¬ ExitRealizable (routineContract canonicalContractParams function .memcpy) := by
  intro hexit
  have hpre : (contractMemcpy canonicalEnvironment).pre badCopyArgs badCopyState :=
    ⟨badCopyState_preCopy, by native_decide⟩
  obtain ⟨after, hpost⟩ := hexit badCopyArgs badCopyState hpre
  exact badCopyPost_impossible after hpost

/-- The same satisfiable entry state makes the canonical `memmove` exit binding unrealizable. -/
theorem memmove_exit_not_realizable (function : FunctionId) :
    ¬ ExitRealizable (routineContract canonicalContractParams function .memmove) := by
  intro hexit
  obtain ⟨after, hpost⟩ := hexit badCopyArgs badCopyState badCopyState_preCopy
  exact badCopyPost_impossible after hpost

private def unrealizableCopyCalleeB (callee : FunctionInstance) : Bool :=
  match catalogEntryFor callee.id.function with
  | some entry => entry.tag == .memcpy || entry.tag == .memmove
  | none => false

/-- The exact consumer-side predicate: an actual callee selected by
`calleeFunctionInstances` dispatches to an unrealizable copy exit. -/
def unrealizableCopySummaryPremiseB
    (program : Program) (functionInstance : FunctionInstance) : Bool :=
  (calleeFunctionInstances program functionInstance).any unrealizableCopyCalleeB

private theorem exit_not_realizable_of_unrealizableCopyCalleeB
    {callee : FunctionInstance}
    (hcopy : unrealizableCopyCalleeB callee = true) :
    ∀ entry, catalogEntryFor callee.id.function = some entry →
      ¬ ExitRealizable
        (routineContract canonicalContractParams callee.id.function entry.tag) := by
  intro entry found
  unfold unrealizableCopyCalleeB at hcopy
  rw [found] at hcopy
  have htag : entry.tag = .memcpy ∨ entry.tag = .memmove := by
    simpa [Bool.or_eq_true, beq_iff_eq] using hcopy
  rcases htag with htag | htag
  · rw [htag]
    exact memcpy_exit_not_realizable _
  · rw [htag]
    exact memmove_exit_not_realizable _

/-- One unrealizable callee exit is enough to make every candidate child-summary relation fail the
outer premise. The relation fact itself is irrelevant: the demanded exit state cannot exist. -/
theorem childSummariesUnavailable_of_unrealizable_callee
    {p : ContractParams} {program : Program} {parent callee : FunctionInstance}
    {entry : CatalogEntry}
    (hcallee : callee ∈ calleeFunctionInstances program parent)
    (found : catalogEntryFor callee.id.function = some entry)
    (hunrealizable : ¬ ExitRealizable (routineContract p callee.id.function entry.tag)) :
    ∀ childSummary, ¬ ChildSummariesAvailable p program parent childSummary := by
  intro childSummary havailable
  apply hunrealizable
  intro args before hpre
  obtain ⟨used, after, hbound, hsummary, hpost⟩ :=
    havailable callee hcallee entry found args 0 before hpre
  exact ⟨after, hpost⟩

/-- A parent selected by the exact copy-callee predicate has no possible
`ChildSummariesAvailable` witness under the canonical contracts. -/
theorem childSummariesUnavailable_of_copy_callee
    {program : Program} {parent : FunctionInstance}
    (hcopy : unrealizableCopySummaryPremiseB program parent = true) :
    ∀ childSummary,
      ¬ ChildSummariesAvailable canonicalContractParams program parent childSummary := by
  unfold unrealizableCopySummaryPremiseB at hcopy
  obtain ⟨callee, hcallee, hbad⟩ := Array.any_eq_true'.mp hcopy
  cases found : catalogEntryFor callee.id.function with
  | none => simp [unrealizableCopyCalleeB, found] at hbad
  | some entry =>
      exact childSummariesUnavailable_of_unrealizable_callee hcallee found
        (exit_not_realizable_of_unrealizableCopyCalleeB hbad entry found)

/-- If the outer summary premise has no inhabitant, the catalog-present local obligation is true,
but only vacuously. -/
theorem localTraceObligation_of_no_child_summaries
    {p : ContractParams} {program : Program} {functionInstance : FunctionInstance}
    {entry : CatalogEntry}
    (found : catalogEntryFor functionInstance.id.function = some entry)
    (hno : ∀ childSummary, ¬ ChildSummariesAvailable p program functionInstance childSummary) :
    functionInstanceLocalTraceObligation p program functionInstance := by
  unfold functionInstanceLocalTraceObligation
  rw [found]
  intro childSummary havailable
  exact False.elim (hno childSummary havailable)

/-- Updating result registers leaves all four memory-frame clauses of a leaf postcondition true. -/
private theorem leafFrame_withArgumentRegisters
    {env : DecoderEnvironment} {base : Nat} {bytes : ByteArray}
    {before : State} (hbytes : MemoryBytes before base bytes)
    (hcode : env.CodeIntact before) (a0 a1 a2 a3 : Nat) :
    LeafFrame env base bytes 0 0 before
      (withArgumentRegisters before a0 a1 a2 a3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro index hindex
    simpa only [withArgumentRegisters_mem] using hbytes index hindex
  · simpa only [DecoderEnvironment.CodeIntact, withArgumentRegisters_mem] using hcode
  · intro address haddress
    simp only [withArgumentRegisters_mem]
  · intro address haddress
    simp only [withArgumentRegisters_mem]

/-- `bytesAt`'s exit binding is realizable for both its success and failure meanings. -/
theorem bytesAt_exit_realizable (env : DecoderEnvironment) :
    ∀ (args : BytesAtArgs) (before : State),
      (contractBytesAt env).pre args before →
        ∃ after,
          (contractBytesAt env).post args ((contractBytesAt env).meaning args) before after := by
  intro args before hpre
  rcases hpre with ⟨hbytes, hcode, _⟩
  cases hmeaning : meaningBytesAt args.bytes args.offset args.length with
  | ok value =>
      let after := withArgumentRegisters before (args.base + args.offset) args.length 0 0
      refine ⟨after, ?_⟩
      change postBytesAt env args (meaningBytesAt args.bytes args.offset args.length) before after
      rw [hmeaning]
      exact ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _, by simp [after]⟩
  | error error =>
      let after := withArgumentRegisters before 0 0 0 0
      refine ⟨after, ?_⟩
      change postBytesAt env args (meaningBytesAt args.bytes args.offset args.length) before after
      rw [hmeaning]
      refine ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _, ?_⟩
      by_cases hfits :
          args.offset ≤ args.bytes.size ∧ args.length ≤ args.bytes.size - args.offset
      · simp [meaningBytesAt, hfits] at hmeaning
      · simpa [meaningBytesAt, hfits] using hmeaning.symm

/-- `readU32`'s exit binding is realizable for both its success and failure meanings. -/
theorem readU32_exit_realizable (env : DecoderEnvironment) :
    ∀ (args : ReadAtArgs) (before : State),
      (contractReadU32 env).pre args before →
        ∃ after,
          (contractReadU32 env).post args ((contractReadU32 env).meaning args) before after := by
  intro args before hpre
  rcases hpre with ⟨hbytes, hcode, _⟩
  cases hmeaning : meaningReadU32 args.bytes args.offset with
  | ok value =>
      let after := withArgumentRegisters before value.toNat 0 0 0
      refine ⟨after, ?_⟩
      change postScalarRead env args 32
        ((meaningReadU32 args.bytes args.offset).map UInt32.toNat) before after
      rw [hmeaning]
      exact
        ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _,
          UInt32.toNat_lt value, by simp [after]⟩
  | error error =>
      let after := withArgumentRegisters before 0 0 0 0
      refine ⟨after, ?_⟩
      change postScalarRead env args 32
        ((meaningReadU32 args.bytes args.offset).map UInt32.toNat) before after
      rw [hmeaning]
      exact
        ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _,
          meaningReadU32_onlyInvalid args.bytes args.offset error hmeaning⟩

private theorem routine_bytesAt_exit_realizable
    (p : ContractParams) (function : FunctionId) :
    ExitRealizable (routineContract p function .bytesAt) := by
  intro args before hpre
  exact bytesAt_exit_realizable p.env args before hpre

private theorem routine_readU32_exit_realizable
    (p : ContractParams) (function : FunctionId) :
    ExitRealizable (routineContract p function .readU32) := by
  intro args before hpre
  exact readU32_exit_realizable p.env args before hpre

private def simpleExitTagB (tag : RoutineTag) : Bool :=
  tag == .bytesAt || tag == .readU32

private def simpleExitCalleeB (callee : FunctionInstance) : Bool :=
  match catalogEntryFor callee.id.function with
  | some entry => simpleExitTagB entry.tag
  | none => false

/-- The exact generated-data check consumed by the summary-premise witness below. It is deliberately
stated with `calleeFunctionInstances`, not a second extraction of the call graph. -/
def simpleExitSummaryPremiseB
    (program : Program) (functionInstance : FunctionInstance) : Bool :=
  (calleeFunctionInstances program functionInstance).all simpleExitCalleeB

private theorem exitRealizable_of_simpleExitCalleeB
    {p : ContractParams} {callee : FunctionInstance}
    (hsimple : simpleExitCalleeB callee = true) :
    ∀ entry, catalogEntryFor callee.id.function = some entry →
      ExitRealizable (routineContract p callee.id.function entry.tag) := by
  intro entry found
  unfold simpleExitCalleeB at hsimple
  rw [found] at hsimple
  have htag : entry.tag = .bytesAt ∨ entry.tag = .readU32 := by
    simpa [simpleExitTagB, Bool.or_eq_true, beq_iff_eq] using hsimple
  rcases htag with htag | htag
  · rw [htag]
    exact routine_bytesAt_exit_realizable _ _
  · rw [htag]
    exact routine_readU32_exit_realizable _ _

/-- If every actual callee has one of the two checked-realizable exit bindings, the universal
summary relation inhabits the outer premise. -/
theorem childSummariesAvailable_of_simple_exit_callees
    {p : ContractParams} {program : Program} {functionInstance : FunctionInstance}
    (hall : simpleExitSummaryPremiseB program functionInstance = true) :
    ChildSummariesAvailable p program functionInstance (fun _ _ _ _ _ => True) := by
  unfold simpleExitSummaryPremiseB at hall
  intro callee hcallee entry found args fromStep before hpre
  have hsimple : simpleExitCalleeB callee = true :=
    Array.all_eq_true_iff_forall_mem.mp hall callee hcallee
  obtain ⟨after, hpost⟩ :=
    exitRealizable_of_simpleExitCalleeB (p := p) hsimple entry found args before hpre
  exact ⟨0, after, Nat.zero_le _, trivial, hpost⟩

/-- The complete join for an explicitly inhabited outer summary premise. -/
theorem localTraceObligation_false_of_summary_entry_exit
    {p : ContractParams} {program : Program} {functionInstance : FunctionInstance}
    {entry : CatalogEntry}
    (found : catalogEntryFor functionInstance.id.function = some entry)
    (hsat : FunctionInstanceContract.PreSatisfiable
      (routineContract p functionInstance.id.function entry.tag).contract)
    (hsummary : ChildSummariesAvailable p program functionInstance
      (fun _ _ _ _ _ => True))
    (hexit : functionInstanceExitPred functionInstance
      (functionInstanceEntryWord functionInstance)) :
    ¬ functionInstanceLocalTraceObligation p program functionInstance := by
  intro hlocal
  unfold functionInstanceLocalTraceObligation at hlocal
  rw [found] at hlocal
  have himpl := hlocal (fun _ _ _ _ _ => True) hsummary
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

/-! ### Entry-is-exit rows with simple callees -/

/-- The exact additional subset whose actual callees all dispatch to one of the two
exit-realizability theorems above. The nonempty test keeps this disjoint from
`noCalleeEntryExitIndices`. -/
def simpleCalleeEntryExitIndices : List Nat :=
  (generatedProgram.functionInstances.zipIdx.filterMap fun (functionInstance, index) =>
    let callees := calleeFunctionInstances generatedProgram functionInstance
    if functionInstance.exitPcs.contains functionInstance.entryPc &&
        !callees.isEmpty && simpleExitSummaryPremiseB generatedProgram functionInstance then
      some index
    else none).toList

/-- The measured callee-bearing subset is exact and moves the build in either direction. -/
theorem simple_callee_entry_exit_indices :
    simpleCalleeEntryExitIndices = [47, 49, 51, 60, 72, 78, 80, 83, 90, 122, 129, 130] := by
  native_decide

private theorem generated_simple_entry_exit_false
    (instanceIndex catalogIndex : Nat)
    (hcatalog : catalogIndex < catalog.size)
    (found : catalogEntryFor
      generatedProgram.functionInstances[instanceIndex]!.id.function =
        some catalog[catalogIndex])
    (hidentity : generatedProgram.functionInstances[instanceIndex]!.id.function =
      catalog[catalogIndex].functionId)
    (hlive : catalog[catalogIndex].isLive = true)
    (hall : simpleExitSummaryPremiseB generatedProgram
      generatedProgram.functionInstances[instanceIndex]! = true)
    (hexit : functionInstanceExitPred generatedProgram.functionInstances[instanceIndex]!
      (functionInstanceEntryWord generatedProgram.functionInstances[instanceIndex]!)) :
    ¬ functionInstanceLocalTraceObligation canonicalContractParams generatedProgram
      generatedProgram.functionInstances[instanceIndex]! := by
  apply localTraceObligation_false_of_summary_entry_exit (entry := catalog[catalogIndex])
  · exact found
  · rw [hidentity]
    exact catalogPreSatisfiable catalogIndex hcatalog hlive
  · exact childSummariesAvailable_of_simple_exit_callees hall
  · exact hexit

/-- All 12 simple-callee rows are genuine false individual obligations. As above, this theorem
checks the composition of the parent pre witness, the outer summary witness, and the generated exit
contradiction. -/
theorem simple_callee_entry_exit_obligations_false :
    ∀ i ∈ simpleCalleeEntryExitIndices,
      ¬ functionInstanceLocalTraceObligation canonicalContractParams generatedProgram
        generatedProgram.functionInstances[i]! := by
  intro i hi
  rw [simple_callee_entry_exit_indices] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact generated_simple_entry_exit_false 47 23 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 49 23 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 51 27 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 60 28 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 72 29 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 78 31 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 80 23 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 83 27 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 90 27 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 122 30 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 129 21 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)
  · exact generated_simple_entry_exit_false 130 22 (by decide) (by rfl)
      (by native_decide) (by decide) (by native_decide)
      (by
        simp only [functionInstanceExitPred, functionInstanceEntryWord, FunctionInstance.isExit]
        native_decide)

/-! ### Parents with an unrealizable copy callee -/

/-- All generated parents whose actual callee set contains a `memcpy` or `memmove` instance. This
uses the same `calleeFunctionInstances` consumer as `ChildSummariesAvailable`. -/
def copyCalleeParentIndices : List Nat :=
  (generatedProgram.functionInstances.zipIdx.filterMap fun (functionInstance, index) =>
    if unrealizableCopySummaryPremiseB generatedProgram functionInstance then
      some index
    else none).toList

/-- The exact affected population. This is not restricted to entry-is-exit rows. -/
theorem copy_callee_parent_indices :
    copyCalleeParentIndices = [1, 3, 6, 16, 23, 37, 45, 58, 62, 70, 81, 88, 120] := by
  native_decide

/-- Every candidate summary relation fails for every measured copy-callee parent. This is the
consumer-side join between the generated callee list and the copy-exit countermodel. -/
theorem copy_callee_summary_premises_unsatisfiable :
    ∀ i ∈ copyCalleeParentIndices, ∀ childSummary,
      ¬ ChildSummariesAvailable canonicalContractParams generatedProgram
        generatedProgram.functionInstances[i]! childSummary := by
  intro i hi
  rw [copy_callee_parent_indices] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply childSummariesUnavailable_of_copy_callee
    native_decide

/-- The 13 individual parent obligations are theorems, but only because their outer
`ChildSummariesAvailable` premise is false. -/
theorem copy_callee_obligations_vacuously_true :
    ∀ i ∈ copyCalleeParentIndices,
      functionInstanceLocalTraceObligation canonicalContractParams generatedProgram
        generatedProgram.functionInstances[i]! := by
  intro i hi
  have hno := copy_callee_summary_premises_unsatisfiable i hi
  rw [copy_callee_parent_indices] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply localTraceObligation_of_no_child_summaries (found := by rfl)
    exact hno

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

/-- Stable keys for the 12 checked callee-bearing refutations. -/
def simpleCalleeEntryExitKeys : List InstanceKey :=
  simpleCalleeEntryExitIndices.map fun index =>
    { entryPc := generatedManifest[index]!.entryPc
      routine := generatedManifest[index]!.qualifiedName }

/-- Stable keys for all 13 parents whose summary premise is refuted by a copy callee. -/
def copyCalleeParentKeys : List InstanceKey :=
  copyCalleeParentIndices.map fun index =>
    { entryPc := generatedManifest[index]!.entryPc
      routine := generatedManifest[index]!.qualifiedName }

/-- All checked-refutation keys in manifest order. Filtering the complete stable-key population
keeps the public ledger identity independent of array-index ordering. -/
def checkedEntryExitKeys : List InstanceKey :=
  ledgerKeys.filter fun key =>
    noCalleeEntryExitKeys.contains key || simpleCalleeEntryExitKeys.contains key

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

/-- The second false set is also pinned by stable key. The final two rows deliberately share an
entry PC, which is why `(entryPc, routine)` rather than `entryPc` is the ledger key. -/
theorem simple_callee_entry_exit_keys :
    simpleCalleeEntryExitKeys =
      [{ entryPc := 72132, routine := "ssz_raw.readU64" },
       { entryPc := 72232, routine := "ssz_raw.readU64" },
       { entryPc := 72332, routine := "ssz_raw.readArray" },
       { entryPc := 73620, routine := "ssz_raw.readArray" },
       { entryPc := 74300, routine := "ssz_raw.readArray" },
       { entryPc := 74472, routine := "ssz_raw.readArray" },
       { entryPc := 74508, routine := "ssz_raw.readU64" },
       { entryPc := 74888, routine := "ssz_raw.readArray" },
       { entryPc := 75336, routine := "ssz_raw.readArray" },
       { entryPc := 77672, routine := "ssz_raw.readArray" },
       { entryPc := 78868, routine := "ssz_raw.readOffset" },
       { entryPc := 78868, routine := "ssz_raw.readU32" }] := by
  native_decide

/-- The vacuous set is pinned by stable key. The two entry-is-exit members are the `readArray` row
at 73688 and the `publicKeys` row at 77500. -/
theorem copy_callee_parent_keys :
    copyCalleeParentKeys =
      [{ entryPc := 66224, routine := "raw_decoder_root.zesu_decode_raw" },
       { entryPc := 66312, routine := "ssz_raw.decode" },
       { entryPc := 66628, routine := "ssz_raw.decodeRaw" },
       { entryPc := 67084, routine := "ssz_raw.decodeNewPayloadRequest" },
       { entryPc := 67352, routine := "ssz_raw.decodeExecutionPayload" },
       { entryPc := 69564, routine := "ssz_raw.readArray" },
       { entryPc := 71012, routine := "ssz_raw.decodeWithdrawals" },
       { entryPc := 73444, routine := "ssz_raw.decodeVersionedHashes" },
       { entryPc := 73688, routine := "ssz_raw.readArray" },
       { entryPc := 74072, routine := "ssz_raw.decodeDepositRequests" },
       { entryPc := 74656, routine := "ssz_raw.decodeWithdrawalRequests" },
       { entryPc := 75072, routine := "ssz_raw.decodeConsolidationRequests" },
       { entryPc := 77500, routine := "ssz_raw.decodePublicKeys" }] := by
  native_decide

/-- The combined checked-key population remains duplicate-free despite the shared entry PC. -/
theorem checked_entry_exit_keys_complete_and_unique :
    checkedEntryExitKeys.length = 28 ∧ checkedEntryExitKeys.Nodup := by
  native_decide

/-- The vacuous population is complete and duplicate-free under the same stable row key. -/
theorem copy_callee_parent_keys_complete_and_unique :
    copyCalleeParentKeys.length = 13 ∧ copyCalleeParentKeys.Nodup := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation.LocalObligationRefutations
