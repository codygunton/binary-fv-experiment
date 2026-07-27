import BinaryFv.SSZ.Zesu.Elfling.GeneratedProgramGeometry
import BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger

/-!
# Entry-PC placement measurement

This module measures a mismatch between the source-shaped entry predicates and the trace
consumer. Every `routineContract` entry predicate is independent of `PC`, while both
`EnteredFunctionTrace` and `EnteredScopedTrace` require the initial state's `PC` to equal the
generated occurrence entry.

That mismatch refutes every closed generated obligation: all 141 selected contracts have a
satisfiable entry predicate, so changing only `PC` produces another pre-state at the wrong address,
which no entered trace can accept. For a local obligation the same refutation applies only after
`ChildSummariesAvailable` is inhabited; the existing ledger's 28 false, 16 vacuous, and 97 unknown
split is therefore preserved.

This is deliberately a pre-repair measurement. It changes neither the production contracts nor the
extractor. The private PC-sensitive contract mutation at the end is only a power test: it proves the
independence check rejects the property whose absence this module measures.
-/

namespace BinaryFv.SSZ.Zesu.Validation.EntryPcPlacement

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedProgram)
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions
open Register

/-- Change only the program counter of a machine state. -/
def stateWithPc (state : State) (pc : BitVec 64) : State :=
  { state with regs := state.regs.insert PC pc }

private def wrongPc (entry : BitVec 64) : BitVec 64 :=
  if entry = 0 then 1 else 0

private theorem wrongPc_ne (entry : BitVec 64) : wrongPc entry ≠ entry := by
  by_cases h : entry = 0
  · simp [wrongPc, h]
  · rw [wrongPc, if_neg h]
    intro hz
    exact h hz.symm

/-- A contract's entry predicate cannot observe a change to the program counter. -/
def EntryPcIndependent {Args Outcome : Type}
    (contract : FunctionInstanceContract Args Outcome) : Prop :=
  ∀ (args : Args) (state : State) (pc : BitVec 64),
    contract.binding.entry args (stateWithPc state pc) ↔
      contract.binding.entry args state

/--
Every source-selected entry predicate ignores `PC`, for every `RoutineTag`, arbitrary contract
parameters, and arbitrary function identity. This is a structural proof over the complete tag type,
not a check over the currently generated instances.
-/
theorem routineContract_entry_pc_independent
    (p : ContractParams) (function : FunctionId) (tag : RoutineTag) :
    EntryPcIndependent (routineContract p function tag).contract := by
  cases tag <;>
    simp [EntryPcIndependent, routineContract, stateWithPc,
      FunctionContract.toFunctionInstance, FunctionContract.toBinding,
      functionInstanceZesuDecodeRaw,
      contractDecode, contractDecodeRaw, contractNewPayloadRequest, contractExecutionPayload,
      contractExecutionRequests, contractExecutionWitness, contractChainConfig, contractForkConfig,
      contractForkActivation, contractOptionalU64, contractOptionalBlobSchedule,
      contractVersionedHashes, contractWithdrawals, contractDepositRequests,
      contractWithdrawalRequests, contractConsolidationRequests, contractPublicKeys,
      contractByteListList, contractRequireCanonicalOffsets, contractRequireU32Length,
      contractReadOffset, contractReadU32, contractReadU64, contractReadU256, contractReadArray,
      contractBytesAt, contractHasExactErePrefix, contractAlloc, contractMemcpy, contractMemmove,
      contractRawResult, contractRawError, contractAllocatorAlloc, contractAllocatorResize,
      contractAllocatorRemap, contractAllocatorFree, contractAllocatorCtor,
      preZesuDecodeRaw, preEntry, preContainer, preSliceToResult, preCollection,
      preCanonicalOffsets, preSlice, preReadAt, preAlloc, preCopy,
      MemoryBytes, DecoderEnvironment.CodeIntact,
      DecoderGlobalsRep, DecoderGlobalsScalarRep, StoredResultDiscriminantRep, StoredResultRep,
      DecoderGlobalsModel.fresh, FlagRep, Word32LERep, OptionTagRep,
      Std.ExtDHashMap.get?_insert]

/--
A satisfiable, entry-PC-independent predicate cannot implement a trace consumer which requires the
initial state to start at one fixed address. The counterexample changes only `PC`.
-/
theorem not_implements_of_entry_pc_independent {Args Outcome : Type}
    {contract : FunctionInstanceContract Args Outcome}
    {region exit : BitVec 64 → Prop} {entry : BitVec 64}
    (independent : EntryPcIndependent contract)
    (satisfiable : FunctionInstanceContract.PreSatisfiable contract) :
    ¬ FunctionInstanceContract.Implements region exit entry contract := by
  intro implements
  obtain ⟨args, state, pre⟩ := satisfiable
  let moved := stateWithPc state (wrongPc entry)
  have movedPre : contract.binding.entry args moved :=
    (independent args state (wrongPc entry)).2 pre
  obtain ⟨_, _, _, entered, _⟩ := implements args 0 moved movedPre
  have wrongAtEntry : wrongPc entry = entry := by
    simpa [moved, stateWithPc] using entered.startsAtEntry
  exact wrongPc_ne entry wrongAtEntry

/--
The corresponding local refutation. It applies after the outer child-summary premise has supplied a
particular relation; it does not claim that such a relation exists.
-/
theorem not_locallyImplements_of_entry_pc_independent {Args Outcome : Type}
    {contract : FunctionInstanceContract Args Outcome}
    {own exit : BitVec 64 → Prop} {entry : BitVec 64}
    {childSummary :
      BinaryFv.Binary.Elfling.FunctionInstanceId → Nat → Nat → State → State → Prop}
    (independent : EntryPcIndependent contract)
    (satisfiable : FunctionInstanceContract.PreSatisfiable contract) :
    ¬ FunctionInstanceContract.LocallyImplements own exit entry childSummary contract := by
  intro implements
  obtain ⟨args, state, pre⟩ := satisfiable
  let moved := stateWithPc state (wrongPc entry)
  have movedPre : contract.binding.entry args moved :=
    (independent args state (wrongPc entry)).2 pre
  obtain ⟨_, _, _, entered, _⟩ := implements args 0 moved movedPre
  have wrongAtEntry : wrongPc entry = entry := by
    simpa [moved, stateWithPc] using entered.startsAtEntry
  exact wrongPc_ne entry wrongAtEntry

private theorem catalog_entry_eq_of_functionId_eq {first second : CatalogEntry}
    (hfirst : first ∈ catalog) (hsecond : second ∈ catalog)
    (hid : first.functionId = second.functionId) : first = second := by
  obtain ⟨i, hi, hgeti⟩ := Array.mem_iff_getElem.mp hfirst
  obtain ⟨j, hj, hgetj⟩ := Array.mem_iff_getElem.mp hsecond
  have hij : i = j :=
    BinaryFv.SSZ.Zesu.Elfling.Validation.catalogIdentitiesDistinct_holds
      i j hi hj (hgeti ▸ hgetj ▸ hid)
  subst j
  exact hgeti.symm.trans hgetj

private theorem catalog_entry_for_mem_id {function : FunctionId} {entry : CatalogEntry}
    (hfind : catalogEntryFor function = some entry) :
    entry ∈ catalog ∧ entry.functionId = function := by
  unfold catalogEntryFor at hfind
  refine ⟨Array.mem_of_find?_eq_some hfind, ?_⟩
  have hp := @Array.find?_some CatalogEntry
    (fun candidate => decide (candidate.functionId = function)) entry catalog hfind
  exact of_decide_eq_true hp

/--
All generated closed obligations are false for the same consumer-side reason. Catalog uniqueness
joins the entry selected by `catalogEntryFor` to the per-instance satisfiability witness, rather than
assuming the two independently obtained entries are the same.
-/
theorem generated_closed_obligations_false :
    ∀ functionInstance ∈ generatedProgram.functionInstances,
      ¬ functionInstanceObligation canonicalContractParams generatedProgram functionInstance := by
  intro functionInstance hmem
  obtain ⟨selected, hselected⟩ :=
    BinaryFv.SSZ.Zesu.Elfling.Validation.functionInstancesDispatchUniquely_holds.2.2
      functionInstance hmem
  obtain ⟨witness, hwitnessMem, _, hwitnessId, hsat⟩ :=
    BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger.generated_instance_pre_satisfiable
      functionInstance hmem
  have hselectedFacts := catalog_entry_for_mem_id hselected
  have hselectedEq : selected = witness :=
    catalog_entry_eq_of_functionId_eq hselectedFacts.1 hwitnessMem
      (hselectedFacts.2.trans hwitnessId)
  rw [← hselectedEq] at hsat
  intro obligation
  unfold functionInstanceObligation at obligation
  rw [hselected] at obligation
  unfold routineObligation FunctionInstanceContract.ImplementsFunctionInstance at obligation
  exact not_implements_of_entry_pc_independent
    (routineContract_entry_pc_independent canonicalContractParams
      functionInstance.id.function selected.tag)
    hsat obligation

/-- The exact closed-obligation blast radius: 141 of 141 generated instances are refuted. -/
theorem generated_closed_obligation_blast_radius :
    generatedProgram.functionInstances.size = 141 ∧
      ∀ functionInstance ∈ generatedProgram.functionInstances,
        ¬ functionInstanceObligation canonicalContractParams generatedProgram functionInstance :=
  ⟨BinaryFv.SSZ.Zesu.Elfling.Validation.generated_function_function_instance_count,
    generated_closed_obligations_false⟩

/--
For every generated local obligation, an inhabited child-summary premise exposes the same wrong-PC
counterexample. Rows whose summary premise is uninhabited remain vacuous, and rows without a settled
summary premise remain unknown.
-/
theorem generated_local_obligations_false_when_summary_available :
    ∀ functionInstance ∈ generatedProgram.functionInstances,
      (∃ childSummary :
          FunctionInstanceId → Nat → Nat → State → State → Prop,
        ChildSummariesAvailable canonicalContractParams generatedProgram
          functionInstance childSummary) →
      ¬ functionInstanceLocalTraceObligation canonicalContractParams
        generatedProgram functionInstance := by
  intro functionInstance hmem havailable
  obtain ⟨selected, hselected⟩ :=
    BinaryFv.SSZ.Zesu.Elfling.Validation.functionInstancesDispatchUniquely_holds.2.2
      functionInstance hmem
  obtain ⟨witness, hwitnessMem, _, hwitnessId, hsat⟩ :=
    BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger.generated_instance_pre_satisfiable
      functionInstance hmem
  have hselectedFacts := catalog_entry_for_mem_id hselected
  have hselectedEq : selected = witness :=
    catalog_entry_eq_of_functionId_eq hselectedFacts.1 hwitnessMem
      (hselectedFacts.2.trans hwitnessId)
  rw [← hselectedEq] at hsat
  obtain ⟨childSummary, hsummary⟩ := havailable
  intro obligation
  unfold functionInstanceLocalTraceObligation at obligation
  simp only [hselected] at obligation
  have hlocal := obligation childSummary hsummary
  unfold routineLocalObligation
    FunctionInstanceContract.LocallyImplementsFunctionInstance at hlocal
  exact not_locallyImplements_of_entry_pc_independent
    (routineContract_entry_pc_independent canonicalContractParams
      functionInstance.id.function selected.tag)
    hsat hlocal

/--
The current local join, without duplicating the existing row proofs: the ledger still measures
0 provable, 28 false, 16 vacuous, and 97 unknown, while the theorem above supplies the generic
consumer-side refutation exactly when its summary premise is inhabited.
-/
theorem generated_local_join_measurement :
    ((BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger.ledgerRows.filter
        fun row => row.verdict == .provable).size,
     (BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger.ledgerRows.filter
        fun row => row.verdict == .false).size,
     (BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger.ledgerRows.filter
        fun row => row.verdict == .vacuous).size,
     (BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger.ledgerRows.filter
        fun row => row.verdict == .unknown).size) = (0, 28, 16, 97) ∧
      ∀ functionInstance ∈ generatedProgram.functionInstances,
        (∃ childSummary :
            FunctionInstanceId → Nat → Nat → State → State → Prop,
          ChildSummariesAvailable canonicalContractParams generatedProgram
            functionInstance childSummary) →
        ¬ functionInstanceLocalTraceObligation canonicalContractParams
          generatedProgram functionInstance :=
  ⟨BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger.verdict_totals,
    generated_local_obligations_false_when_summary_available⟩

/-! ## Mutation tooth -/

private def pcSensitiveMutation {Args Outcome : Type} (entry : BitVec 64)
    (contract : FunctionInstanceContract Args Outcome) :
    FunctionInstanceContract Args Outcome :=
  { contract with binding :=
      { contract.binding with entry := fun args state =>
          contract.binding.entry args state ∧ state.regs.get? PC = some entry } }

/--
The structural check has a negative control: adding the missing PC dependence to any satisfiable
independent entry predicate makes `EntryPcIndependent` false.
-/
private theorem pcSensitiveMutation_rejected {Args Outcome : Type}
    {entry : BitVec 64} {contract : FunctionInstanceContract Args Outcome}
    (independent : EntryPcIndependent contract)
    (satisfiable : FunctionInstanceContract.PreSatisfiable contract) :
    ¬ EntryPcIndependent (pcSensitiveMutation entry contract) := by
  intro mutatedIndependent
  obtain ⟨args, state, pre⟩ := satisfiable
  let atEntry := stateWithPc state entry
  have atEntryPre : contract.binding.entry args atEntry :=
    (independent args state entry).2 pre
  have mutatedPre : (pcSensitiveMutation entry contract).binding.entry args atEntry := by
    simp only [pcSensitiveMutation]
    exact ⟨atEntryPre, by simp [atEntry, stateWithPc]⟩
  have movedMutatedPre : (pcSensitiveMutation entry contract).binding.entry args
      (stateWithPc atEntry (wrongPc entry)) :=
    (mutatedIndependent args atEntry (wrongPc entry)).2 mutatedPre
  have wrongAtEntry : wrongPc entry = entry := by
    simpa [pcSensitiveMutation, stateWithPc] using movedMutatedPre.2
  exact wrongPc_ne entry wrongAtEntry

end BinaryFv.SSZ.Zesu.Validation.EntryPcPlacement
