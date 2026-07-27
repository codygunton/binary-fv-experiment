import BinaryFv.SSZ.Zesu.Validation.ContractGroundTruth
import BinaryFv.SSZ.Zesu.Validation.LocalObligationRefutations

/-!
# Per-instance local-obligation ledger

This is the 141-row answer to the question hidden by `LocalContractAssumptions`. It composes:

* logical `pre` satisfiability from `canonical_catalog_satisfiability`;
* satisfiability of the outer `ChildSummariesAvailable` premise where it is proved;
* the structural measurements consumed by `EnteredScopedTrace` and `InlineTransfer`;
* the captured-run evidence from `ContractGroundTruth`; and
* checked positive or negative proof status.

The order matters. `preSatisfiable` is computed first and the row suffix is represented by `Gated`,
so an unsatisfiable or unknown `pre` cannot accidentally acquire a structural or empirical failure.
The child-summary premise is a second logical gate on the final verdict: a structural contradiction
with an unknown child-summary premise stays `unknown`, never `false`.

The current ledger is intentionally red. Twenty-eight rows have a checked proof of the negated
individual obligation. Sixteen others are checked theorems only because an unrealizable callee exit
makes their outer summary premise unsatisfiable; they are classified as vacuous, not compliant.
No repair is attempted here. Captured-state `pre` and `post` failures remain evidence that the
contract misdescribes the binary, but they do not derive the logical verdict.
-/

namespace BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedManifest generatedProgram)
open BinaryFv.SSZ.Zesu.Elfling.Validation
open BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.SSZ.Zesu.MemoryRepresentation

/-! ## Logical states and enforced gating -/

inductive Satisfiability where
  | yes (witness : String)
  | no (reason : String)
  | unknown (reason : String)
deriving Repr, DecidableEq, Inhabited

def Satisfiability.render : Satisfiability → String
  | .yes witness => "yes(" ++ witness ++ ")"
  | .no reason => "no(" ++ reason ++ ")"
  | .unknown reason => "unknown(" ++ reason ++ ")"

inductive ProofStatus where
  | proved (theoremName : String)
  | refuted (theoremName : String)
  | absent
deriving Repr, DecidableEq, Inhabited

def ProofStatus.render : ProofStatus → String
  | .proved theoremName => "proved(" ++ theoremName ++ ")"
  | .refuted theoremName => "refuted(" ++ theoremName ++ ")"
  | .absent => "absent"

inductive LedgerVerdict where
  | provable
  | false
  | vacuous
  | unknown
deriving Repr, DecidableEq, Inhabited

def LedgerVerdict.render : LedgerVerdict → String
  | .provable => "provable"
  | .false => "FALSE"
  | .vacuous => "VACUOUS"
  | .unknown => "unknown"

/-- A value to the right of `preSatisfiable` either exists because `pre` has a witness, or carries
the gate that prevented it from being classified. -/
inductive Gated (α : Type) where
  | value (result : α)
  | gated (reason : String)
deriving Repr, DecidableEq, Inhabited

structure RowSuffix where
  summaryPremiseSatisfiable : Gated Satisfiability
  structural : Gated String
  evidence : Gated String
  conjunctsUnevaluated : Gated (List String)
  proof : Gated ProofStatus
  verdict : LedgerVerdict
deriving Repr, DecidableEq, Inhabited

private def gatedSuffix (pre : Satisfiability) : RowSuffix :=
  match pre with
  | .no reason =>
      { summaryPremiseSatisfiable := .gated ("pre unsatisfiable: " ++ reason)
        structural := .gated "pre unsatisfiable"
        evidence := .gated "pre unsatisfiable"
        conjunctsUnevaluated := .gated "pre unsatisfiable"
        proof := .gated "pre unsatisfiable"
        verdict := .vacuous }
  | .unknown reason =>
      { summaryPremiseSatisfiable := .gated ("pre unknown: " ++ reason)
        structural := .gated "pre unknown"
        evidence := .gated "pre unknown"
        conjunctsUnevaluated := .gated "pre unknown"
        proof := .gated "pre unknown"
        verdict := .unknown }
  | .yes _ => default

/-- The gate is structural, not a rendering convention. This power test fixes both non-`yes`
arms. -/
theorem pre_gate_controls_the_entire_suffix :
    gatedSuffix (.no "contradiction") =
        { summaryPremiseSatisfiable := .gated "pre unsatisfiable: contradiction"
          structural := .gated "pre unsatisfiable"
          evidence := .gated "pre unsatisfiable"
          conjunctsUnevaluated := .gated "pre unsatisfiable"
          proof := .gated "pre unsatisfiable"
          verdict := .vacuous } ∧
      gatedSuffix (.unknown "not measured") =
        { summaryPremiseSatisfiable := .gated "pre unknown: not measured"
          structural := .gated "pre unknown"
          evidence := .gated "pre unknown"
          conjunctsUnevaluated := .gated "pre unknown"
          proof := .gated "pre unknown"
          verdict := .unknown } := by
  decide

/-! ## Checked logical inputs -/

private theorem routine_pre_satisfiable_of_routine_satisfiable
    {p : ContractParams} {function : FunctionId} {tag : RoutineTag}
    (henv : ValidEnvironment p.env)
    (hsat : routineSatisfiable p function tag) :
    FunctionInstanceContract.PreSatisfiable (routineContract p function tag).contract := by
  cases tag <;> exact hsat henv

/-- Every generated instance is tied to a live catalog entry whose selected contract has a model of
its entry binding. This is per instance, not merely the 43-entry catalog aggregate. -/
theorem generated_instance_pre_satisfiable :
    ∀ functionInstance ∈ generatedProgram.functionInstances,
      ∃ entry ∈ catalog,
        entry.isLive = true ∧ functionInstance.id.function = entry.functionId ∧
          FunctionInstanceContract.PreSatisfiable
            (routineContract canonicalContractParams functionInstance.id.function
              entry.tag).contract := by
  intro functionInstance hmem
  obtain ⟨entry, hentry, hlive, hid⟩ :=
    everyFunctionInstanceIsCataloged_holds functionInstance hmem
  refine ⟨entry, hentry, hlive, hid, ?_⟩
  rw [hid]
  exact routine_pre_satisfiable_of_routine_satisfiable canonical_environment_valid
    (canonical_catalog_satisfiability entry hentry hlive)

def preSatisfiability (functionInstance : FunctionInstance) : Satisfiability :=
  match catalogEntryFor functionInstance.id.function with
  | some entry =>
      if entry.isLive then .yes "canonical_catalog_satisfiability"
      else .unknown "catalog dispatch selected a non-live entry"
  | none => .unknown "catalogEntryFor returned none"

def summaryPremiseSatisfiability (functionInstance : FunctionInstance) : Satisfiability :=
  let callees := calleeFunctionInstances generatedProgram functionInstance
  if callees.isEmpty then
    .yes "empty relation; calleeFunctionInstances=[]"
  else if LocalObligationRefutations.unrealizableCopySummaryPremiseB
      generatedProgram functionInstance then
    .no "copy callee: permitted code destination makes postCopy inconsistent with CodeIntact"
  else if LocalObligationRefutations.unrealizableResultSummaryPremiseB
      generatedProgram functionInstance then
    .no "result callee: unconstrained resultBase makes representation conflict with CodeIntact"
  else if LocalObligationRefutations.simpleExitSummaryPremiseB
      generatedProgram functionInstance then
    .yes "universal relation; every callee exit is realizable (bytesAt/readU32)"
  else
    .unknown (toString callees.size ++ " callee(s); no checked ChildSummariesAvailable witness")

/-! ## Structural and captured evidence -/

private def verdictFailure? : Boundary.Verdict → Option String
  | .violated clause => some clause
  | _ => none

private def verdictGap? : Boundary.Verdict → Option String
  | .gap reason => some reason
  | _ => none

private def labeledFailures (facts : List (String × Boundary.Verdict)) : List String :=
  facts.filterMap fun (label, verdict) =>
    (verdictFailure? verdict).map fun clause => label ++ "=" ++ clause

private def labeledGaps (facts : List (String × Boundary.Verdict)) : List String :=
  facts.filterMap fun (label, verdict) =>
    (verdictGap? verdict).map fun reason => label ++ "=" ++ reason

private def natList (values : List Nat) : String :=
  String.intercalate "," (values.map toString)

/-- `callNotExit` is intentionally not a blocker here. The seven remaining call-site exits are the
tail calls preserved by the repaired fall-through rule; a trace stops at them instead of taking a
`CallTransfer`. They are still printed as information so the measurement is not discarded. -/
def structureStatus (row : Boundary.BoundaryRow) : String :=
  let blockers := labeledFailures
    [("entry", row.entryNotExit), ("inline-entry", row.inlineEntryEdges),
     ("inline-exit", row.inlineExitEdges)]
  let base :=
    if blockers.isEmpty then "ok"
    else "blocked:" ++ String.intercalate "," blockers
  if row.offendingCallPcs.isEmpty then base
  else base ++ ";tail-call-exits(stop-not-splice)=" ++ natList row.offendingCallPcs

def evidenceStatus (row : GroundTruth.GroundTruthRow) : String :=
  let facts :=
    [("entered", row.entered), ("pre@capture", row.pre), ("exit@capture", row.exited),
     ("post@capture", row.post), ("steps@capture", row.steps)]
  let failures := labeledFailures facts
  let gaps := labeledGaps facts
  let classification :=
    if !failures.isEmpty then "fail:" ++ String.intercalate "," failures
    else if !gaps.isEmpty then "not-covered:" ++ String.intercalate "," gaps
    else "pass"
  classification ++ ";detail=" ++
    String.intercalate ","
      [row.entered.render, row.pre.render, row.exited.render, row.post.render, row.steps.render]

private def prePredicateName : String → String
  | "zesuDecodeRaw" => "preZesuDecodeRaw"
  | "decode" | "decodeRaw" => "preEntry"
  | "newPayloadRequest" | "executionPayload" | "executionRequests" | "executionWitness"
  | "chainConfig" | "forkConfig" | "forkActivation" => "preContainer"
  | "optionalU64" | "optionalBlobSchedule" => "preSliceToResult"
  | "versionedHashes" | "withdrawals" | "depositRequests" | "withdrawalRequests"
  | "consolidationRequests" | "publicKeys" | "byteListList" => "preCollection"
  | "requireCanonicalOffsets" => "preCanonicalOffsets"
  | "requireU32Length" | "hasExactErePrefix" => "preSlice"
  | "readOffset" | "readU32" | "readU64" | "readU256" | "readArray" | "bytesAt" =>
      "preReadAt"
  | "rawAlloc" | "allocatorAlloc" => "preAlloc"
  | "memcpy" => "contractMemcpy.pre"
  | "memmove" => "preCopy"
  | "rawResult" => "contractRawResult.pre"
  | "rawError" => "contractRawError.pre"
  | "allocatorResize" => "contractAllocatorResize.pre"
  | "allocatorRemap" => "contractAllocatorRemap.pre"
  | "allocatorFree" => "contractAllocatorFree.pre"
  | "allocatorCtor" => "contractAllocatorCtor.pre"
  | tag => "contract" ++ tag ++ ".pre"

private def postPredicateName : String → String
  | "zesuDecodeRaw" => "postZesuDecodeRaw"
  | "decode" | "decodeRaw" => "postEntry"
  | "chainConfig" | "forkConfig" | "forkActivation" => "postFixedContainer"
  | "newPayloadRequest" | "executionPayload" | "executionRequests" | "executionWitness" =>
      "postAllocatingContainer"
  | "optionalU64" => "postOptionalU64"
  | "optionalBlobSchedule" => "postOptionalBlobSchedule"
  | "versionedHashes" | "withdrawals" | "depositRequests" | "withdrawalRequests"
  | "consolidationRequests" | "publicKeys" | "byteListList" => "postCollection"
  | "requireCanonicalOffsets" => "postCanonicalOffsets"
  | "requireU32Length" => "postRequireU32Length"
  | "hasExactErePrefix" => "postHasExactErePrefix"
  | "readOffset" | "readU32" | "readU64" => "postScalarRead"
  | "readU256" => "postReadU256"
  | "readArray" => "postReadArray"
  | "bytesAt" => "postBytesAt"
  | "rawAlloc" | "allocatorAlloc" => "postAlloc"
  | "memcpy" | "memmove" => "postCopy"
  | "rawResult" => "postRawResult"
  | "rawError" => "postRawError"
  | "allocatorResize" => "contractAllocatorResize.post"
  | "allocatorRemap" => "contractAllocatorRemap.post"
  | "allocatorFree" => "contractAllocatorFree.post"
  | "allocatorCtor" => "contractAllocatorCtor.post"
  | tag => "contract" ++ tag ++ ".post"

/-- Wildcard names are deliberate lower bounds: the current harness has not decomposed those shared
predicates into individually evaluated conjuncts. A wildcard is one named unevaluated group, never a
claim that the group contains one conjunct. -/
def unevaluatedConjuncts (row : GroundTruth.GroundTruthRow) : List String :=
  let preGaps :=
    match row.pre with
    | .ok => []
    | .violated "preReadAt.x12=offset" =>
        ["preReadAt.MemoryBytes", "preReadAt.CodeIntact", "preReadAt.x10=base",
         "preReadAt.x11=bytes.size"]
    | _ => [prePredicateName row.routineTag ++ ".*"]
  let postGaps :=
    match row.post with
    | .ok => ["LeafFrame.WritesOnlyWithinOwnRecord"]
    | .violated "postScalarRead.x10=value" =>
        ["LeafFrame.WritesOnlyWithinOwnRecord"]
    | _ => [postPredicateName row.routineTag ++ ".*"]
  preGaps ++ postGaps

/-! ## Rows and derived verdict -/

structure LedgerRow where
  index : Nat
  key : LocalObligationRefutations.InstanceKey
  routineTag : String
  preSatisfiable : Satisfiability
  summaryPremiseSatisfiable : Gated Satisfiability
  structural : Gated String
  evidence : Gated String
  conjunctsUnevaluated : Gated (List String)
  proof : Gated ProofStatus
  verdict : LedgerVerdict
deriving Repr, DecidableEq, Inhabited

private def checkedProofStatus (index : Nat) : ProofStatus :=
  if LocalObligationRefutations.copyCalleeParentIndices.contains index then
    .proved "copy_callee_obligations_vacuously_true"
  else if LocalObligationRefutations.resultCollisionParentIndices.contains index then
    .proved "result_collision_obligations_vacuously_true"
  else if LocalObligationRefutations.noCalleeEntryExitIndices.contains index then
    .refuted "no_callee_entry_exit_obligations_false"
  else if LocalObligationRefutations.simpleCalleeEntryExitIndices.contains index then
    .refuted "simple_callee_entry_exit_obligations_false"
  else .absent

private def checkedSuffix (index : Nat) (functionInstance : FunctionInstance)
    (boundary : Boundary.BoundaryRow) (groundTruth : GroundTruth.GroundTruthRow) : RowSuffix :=
  let summary := summaryPremiseSatisfiability functionInstance
  let proof := checkedProofStatus index
  let verdict :=
    match summary, proof with
    | .no _, _ => LedgerVerdict.vacuous
    | .yes _, .proved _ => .provable
    | .yes _, .refuted _ => .false
    | _, _ => .unknown
  { summaryPremiseSatisfiable := .value summary
    structural := .value (structureStatus boundary)
    evidence := .value (evidenceStatus groundTruth)
    conjunctsUnevaluated := .value (unevaluatedConjuncts groundTruth)
    proof := .value proof
    verdict := verdict }

def ledgerRow (index : Nat) (functionInstance : FunctionInstance) : LedgerRow :=
  let manifest := generatedManifest[index]!
  let pre := preSatisfiability functionInstance
  let boundary :=
    match BinaryFv.SSZ.Zesu.ControlFlow.controlFlow? with
    | some nodes => Boundary.boundaryRow nodes generatedProgram index functionInstance
    | none =>
        { index := index
          qualifiedName := manifest.qualifiedName
          routineTag := manifest.routineTag
          entryPc := functionInstance.entryPc
          entryNotExit := .gap "control-flow decode failed"
          callNotExit := .gap "control-flow decode failed"
          inlineEntryEdges := .gap "control-flow decode failed"
          inlineExitEdges := .gap "control-flow decode failed"
          offendingCallPcs := []
          childrenWithoutExitEdge := #[]
          childCount := 0 }
  let suffix :=
    match pre with
    | .yes _ => checkedSuffix index functionInstance boundary GroundTruth.groundTruthRows[index]!
    | _ => gatedSuffix pre
  { index := index
    key := { entryPc := functionInstance.entryPc, routine := manifest.qualifiedName }
    routineTag := manifest.routineTag
    preSatisfiable := pre
    summaryPremiseSatisfiable := suffix.summaryPremiseSatisfiable
    structural := suffix.structural
    evidence := suffix.evidence
    conjunctsUnevaluated := suffix.conjunctsUnevaluated
    proof := suffix.proof
    verdict := suffix.verdict }

def ledgerRows : Array LedgerRow :=
  generatedProgram.functionInstances.zipIdx.map fun (functionInstance, index) =>
    ledgerRow index functionInstance

/-! ## Exact pins -/

private def countSat (pick : LedgerRow → Satisfiability)
    (which : Satisfiability → Bool) : Nat :=
  (ledgerRows.filter fun row => which (pick row)).size

private def isSatYes : Satisfiability → Bool
  | .yes _ => true
  | _ => false

private def isSatNo : Satisfiability → Bool
  | .no _ => true
  | _ => false

private def isSatUnknown : Satisfiability → Bool
  | .unknown _ => true
  | _ => false

private def summaryValues : Array Satisfiability :=
  ledgerRows.filterMap fun row =>
    match row.summaryPremiseSatisfiable with
    | .value result => some result
    | .gated _ => none

theorem ledger_population_and_keys :
    ledgerRows.size = 141 ∧
      ledgerRows.toList.map (·.key) = LocalObligationRefutations.ledgerKeys ∧
      (ledgerRows.toList.map (·.key)).Nodup := by
  native_decide

/-- Logical `pre` is satisfiable on all 141 rows. Captured-state failures do not change this
column. -/
theorem pre_satisfiability_totals :
    (countSat (·.preSatisfiable) isSatYes,
     countSat (·.preSatisfiable) isSatNo,
     countSat (·.preSatisfiable) isSatUnknown) = (141, 0, 0) := by
  native_decide

/-- The outer premise is exhibited for 76 no-callee rows and another 44 whose callees all have
checked-realizable `bytesAt`/`readU32` exits. It is refuted for 13 parents with an unrealizable copy
callee and three with an unrealizable result-record callee; five remain unknown. -/
theorem summary_premise_satisfiability_totals :
    ((summaryValues.filter isSatYes).size,
     (summaryValues.filter isSatNo).size,
     (summaryValues.filter isSatUnknown).size) = (120, 16, 5) := by
  native_decide

/-- The red result: 28 checked false obligations, 16 vacuous theorems caused by inconsistent callee
contracts, and 97 honest unknowns. Nothing is called `provable` merely because no
contradiction was measured. -/
theorem verdict_totals :
    ((ledgerRows.filter fun row => row.verdict == .provable).size,
     (ledgerRows.filter fun row => row.verdict == .false).size,
     (ledgerRows.filter fun row => row.verdict == .vacuous).size,
     (ledgerRows.filter fun row => row.verdict == .unknown).size) = (0, 28, 16, 97) := by
  native_decide

/-- This is the disputed join stated over exactly the 33 entry-is-exit rows: 28 are checked false,
and all five others are checked vacuous because of an unrealizable callee exit. -/
theorem entry_is_exit_verdict_totals :
    let rows := ledgerRows.filter fun row =>
      generatedProgram.functionInstances[row.index]!.exitPcs.contains row.key.entryPc
    (rows.size,
     (rows.filter fun row => row.verdict == .provable).size,
     (rows.filter fun row => row.verdict == .false).size,
     (rows.filter fun row => row.verdict == .vacuous).size,
     (rows.filter fun row => row.verdict == .unknown).size) = (33, 0, 28, 5, 0) := by
  native_decide

theorem false_rows_are_exactly_the_checked_refutations :
    (ledgerRows.filterMap fun row =>
      if row.verdict == .false then some row.key else none).toList =
        LocalObligationRefutations.checkedEntryExitKeys := by
  native_decide

theorem vacuous_rows_are_exactly_the_checked_vacuous_keys :
    (ledgerRows.filterMap fun row =>
      if row.verdict == .vacuous then some row.key else none).toList =
        LocalObligationRefutations.checkedVacuousKeys := by
  native_decide

/-- No entry-is-exit row remains unresolved. -/
theorem unknown_entry_is_exit_keys :
    (ledgerRows.filterMap fun row =>
      if generatedProgram.functionInstances[row.index]!.exitPcs.contains row.key.entryPc &&
          row.verdict == .unknown then some row.key else none).toList =
      [] := by
  native_decide

/-! ## Deterministic report -/

private def sanitizeCell (value : String) : String :=
  (value.replace "|" "/").replace "\n" " "

private def renderGatedSat : Gated Satisfiability → String
  | .value result => result.render
  | .gated reason => "gated(" ++ reason ++ ")"

private def renderGatedString : Gated String → String
  | .value result => result
  | .gated reason => "gated(" ++ reason ++ ")"

private def renderUnevaluated : Gated (List String) → String
  | .gated reason => "gated(" ++ reason ++ ")"
  | .value names =>
      let hasWildcard := names.any fun name => name.endsWith ".*"
      (if hasWildcard then "≥" else "") ++ toString names.length ++ ":" ++
        String.intercalate "," names

private def renderProof : Gated ProofStatus → String
  | .value result => result.render
  | .gated reason => "gated(" ++ reason ++ ")"

def LedgerRow.render (row : LedgerRow) : String :=
  "| " ++ String.intercalate " | "
    [toString row.key.entryPc, sanitizeCell row.key.routine, toString row.index, row.routineTag,
     sanitizeCell row.preSatisfiable.render,
     sanitizeCell (renderGatedSat row.summaryPremiseSatisfiable),
     sanitizeCell (renderGatedString row.structural),
     sanitizeCell (renderGatedString row.evidence),
     sanitizeCell (renderUnevaluated row.conjunctsUnevaluated),
     sanitizeCell (renderProof row.proof), row.verdict.render] ++ " |"

def report : String :=
  String.intercalate "\n"
    (["# Local-obligation ledger — 141 generated function instances",
      "",
      "Key: `(entryPc, routine)`. `entryPc` alone is not unique. Rows stay in manifest order;",
      "`idx` is diagnostic only and is not the key.",
      "",
      "`preSatisfiable` is logical satisfiability, proved from the live catalog. `pre@capture` in",
      "`evidence` is a different question: whether one measured machine state matches the " ++
        "contract.",
      "A captured failure never changes the logical verdict by itself.",
      "",
      "`summaryPremise` is the omitted outer `ChildSummariesAvailable` gate. A structural block " ++
        "with",
      "that column `unknown` stays `unknown`. Wildcards in `unevaluated` name whole predicates " ++
        "whose",
      "conjuncts have not yet been individually audited; their displayed count is therefore a " ++
        "lower",
      "bound (`≥`), never a claim of coverage.",
      "`summaryPremise = no` is a checked refutation of every possible child-summary relation.",
      "The 16 obligations proved through such a false premise are VACUOUS, never " ++
        "compliant.",
      "",
      "Totals: pre yes/no/unknown = 141/0/0; summary yes/no/unknown = 120/16/5;",
      "verdict provable/false/vacuous/unknown = 0/28/16/97.",
      "Among the disputed 33 entry-is-exit rows: 28 false, 5 vacuous, 0 unknown.",
      "",
      "| entryPc | routine | idx | tag | preSatisfiable | summaryPremise | structure | " ++
        "evidence | conjunctsUnevaluated | proof | verdict |",
      "| ---: | --- | ---: | --- | --- | --- | --- | --- | --- | --- | --- |"] ++
      (ledgerRows.map LedgerRow.render).toList ++ [""])

end BinaryFv.SSZ.Zesu.Validation.LocalObligationLedger
