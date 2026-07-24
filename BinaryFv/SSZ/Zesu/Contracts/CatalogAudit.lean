import BinaryFv.SSZ.Zesu.Contracts.ProgramCorrectness

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.Binary.Elfling

/-!
# Structural audits of the catalog

The review's item-6 checks, compiled so the build fails if the catalog stops satisfying them.

The data checks over the immutable handwritten catalog use `native_decide`. That is the same
documented "small immutable-artifact checking" trust the repository already relies on for closed
facts about fixed artifacts (`Lean.ofReduceBool`, `Lean.trustCompiler`), and none of these audit
theorems is on `root_compliance`'s dependency spine, so its axiom set is unaffected. The two genuine
obligations (per-function-instance dispatch and the root dependency) are ordinary kernel proofs with no such
trust. -/

/-- Boolean: catalog identities are pairwise distinct. -/
def catalogIdentitiesNodup : Bool :=
  let ids := catalog.map (fun e => e.functionId)
  ids.toList.length == ids.toList.eraseDups.length

/-- Boolean: every catalog identity resolves through the dispatch lookup. -/
def everyIdentityDispatches : Bool :=
  catalog.all fun e => (catalogEntryFor e.functionId).isSome

/-- Boolean: two entries share a qualified name but differ in full identity (name-only would
conflate them). -/
def existsSameNameDistinctIdentity : Bool :=
  (catalog.flatMap fun e1 => catalog.map fun e2 =>
    (e1.functionId.declaration.qualifiedName == e2.functionId.declaration.qualifiedName) &&
      (e1.functionId != e2.functionId)).any id

/-- Boolean: every required `readArray` width is a live entry. -/
def allRequiredWidthsPresent : Bool :=
  requiredReadArrayWidths.all fun w =>
    catalog.any fun e => e.tag == RoutineTag.readArray && readArrayWidthOf e.functionId == w

/-- Boolean: no excluded routine shares an identity with a live one. -/
def exclusionsDisjoint : Bool :=
  excludedRoutines.all fun x => !catalog.any fun e => e.functionId == x.functionId

/-- Boolean: every excluded routine carries an exclusion reason. -/
def exclusionsAllClassified : Bool :=
  excludedRoutines.all fun x => match x.presence with | .absent _ => true | .live => false

/-- (1) Every catalog identity has exactly one contract dispatch. -/
theorem every_identity_dispatches : everyIdentityDispatches = true := by native_decide

/-- (1') Catalog identities are distinct, so the dispatch is single-valued. -/
theorem catalog_identities_distinct : catalogIdentitiesNodup = true := by native_decide

/-- (2) Every required concrete specialization is present. -/
theorem required_specializations_present : allRequiredWidthsPresent = true := by native_decide

/-- (3) Coverage is not name-only: two entries share a qualified name but differ in full identity. -/
theorem coverage_is_not_name_only : existsSameNameDistinctIdentity = true := by native_decide

/-- (4a) Exclusions never collide with coverage. -/
theorem exclusions_disjoint_from_catalog : exclusionsDisjoint = true := by native_decide

/-- (4b) Every excluded routine is classified with a machine-checkable reason. -/
theorem exclusions_all_classified : exclusionsAllClassified = true := by native_decide

/-- (5) `sszProgramCorrectness` genuinely references the per-function-instance implementation predicate:
program correctness entails that the function instance at any cataloged identity implements its routine's
`correctnessClaim`. Ordinary kernel proof, no artifact trust. -/
theorem program_correctness_references_per_function_instance
    {program : Program} {p : ContractParams}
    (correct : sszProgramCorrectness program p)
    {functionInstance : FunctionInstance} (mem : functionInstance ∈ program.functionInstances)
    {entry : CatalogEntry} (found : catalogEntryFor functionInstance.id.function = some entry) :
    routineObligation p functionInstance (functionInstanceReachedPcs program functionInstance) entry.tag :=
  function_instance_implements_its_contract correct mem found

/-- (6) The runner/result theorems `root_compliance` is built from depend on
`sszComplianceObligations program`: it entails program correctness for the concrete
`canonicalContractParams` (which in particular witnesses the `∃ p` the old statement used). Ordinary
kernel proof. -/
theorem root_dependency_is_real :
    ∀ program : Program, sszComplianceObligations program → (∃ p, sszProgramCorrectness program p) :=
  fun _ obligations => ⟨canonicalContractParams, obligations.1⟩


/-! ## (7) The typed dispatch and the per-routine correctness claims cannot drift apart

`routineObligation` and `routineLocalObligation` are both formed from one `routineContract`
selection, so the closed and local obligations are guaranteed to be about the same contract. These
`rfl`s pin that single selection to the per-routine `correctnessClaim*` the reviewed contract modules
state, one line per `RoutineTag`: if a branch of `routineContract` were pointed at the wrong
contract, its line here would stop type-checking. -/

section ClaimAgreement

variable (p : ContractParams) (i : FunctionInstance) (r : BitVec 64 → Prop)


example : routineObligation p i r .zesuDecodeRaw
    = correctnessClaimZesuDecodeRaw p.env p.globals p.resultBuffer p.repRawV4 i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .decode
    = correctnessClaimDecode p.env p.repRawV4 i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .decodeRaw
    = correctnessClaimDecodeRaw p.env p.repRawV4 i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .newPayloadRequest
    = correctnessClaimNewPayloadRequest p.env p.repNewPayloadRequest i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .executionPayload
    = correctnessClaimExecutionPayload p.env p.repExecutionPayload i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .executionRequests
    = correctnessClaimExecutionRequests p.env p.repExecutionRequests i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .executionWitness
    = correctnessClaimExecutionWitness p.env p.repExecutionWitness i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .chainConfig
    = correctnessClaimChainConfig p.env p.repChainConfig i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .forkConfig
    = correctnessClaimForkConfig p.env p.repForkConfig i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .forkActivation
    = correctnessClaimForkActivation p.env p.repForkActivation i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .optionalU64
    = correctnessClaimOptionalU64 p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .optionalBlobSchedule
    = correctnessClaimOptionalBlobSchedule p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .versionedHashes
    = correctnessClaimVersionedHashes p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .withdrawals
    = correctnessClaimWithdrawals p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .depositRequests
    = correctnessClaimDepositRequests p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .withdrawalRequests
    = correctnessClaimWithdrawalRequests p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .consolidationRequests
    = correctnessClaimConsolidationRequests p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .publicKeys
    = correctnessClaimPublicKeys p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .byteListList
    = correctnessClaimByteListList p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .requireCanonicalOffsets
    = correctnessClaimRequireCanonicalOffsets p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .requireU32Length
    = correctnessClaimRequireU32Length p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .readOffset
    = correctnessClaimReadOffset p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .readU32
    = correctnessClaimReadU32 p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .readU64
    = correctnessClaimReadU64 p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .readU256
    = correctnessClaimReadU256 p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .readArray
    = correctnessClaimReadArray p.env (readArrayWidthOf i.id.function) i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .bytesAt
    = correctnessClaimBytesAt p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .hasExactErePrefix
    = correctnessClaimHasExactErePrefix p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .rawAlloc
    = correctnessClaimAlloc p.env p.heap i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .memcpy
    = correctnessClaimMemcpy p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .memmove
    = correctnessClaimMemmove p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .rawResult
    = correctnessClaimRawResult p.env p.globals p.resultBuffer i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .rawError
    = correctnessClaimRawError p.env p.globals i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .allocatorAlloc
    = correctnessClaimAllocatorAlloc p.env p.heap i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .allocatorResize
    = correctnessClaimAllocatorResize p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .allocatorRemap
    = correctnessClaimAllocatorRemap p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .allocatorFree
    = correctnessClaimAllocatorFree p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl

example : routineObligation p i r .allocatorCtor
    = correctnessClaimAllocatorCtor p.env i r (functionInstanceEntryWord i) (functionInstanceExitPred i) := rfl


end ClaimAgreement

end BinaryFv.SSZ.Zesu.Contracts
