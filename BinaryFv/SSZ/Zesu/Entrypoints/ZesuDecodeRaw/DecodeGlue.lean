import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Accessors
import BinaryFv.SSZ.Zesu.Contracts.SemanticObligations

/-!
# From the wrapper's exit binding to the runner's observations

`Accessors.lean` reduced `SuccessfulRun`/`RejectedRun` to two groups of premises: the machine ones
(the builder's run, the decode trace, the two accessor traces) and the **decode-side** ones —

```
observeReturnCode? finalState = some 1        -- or `some 0`
observeOptionTag? finalState storedResultDiscriminantAddr = some true   -- or `some false`
MemoryBytes finalState canonicalRunnerLayout.inputBase input
RawV4Rep finalState canonicalRunnerLayout.inputBase input Elfling.canonicalResultBuffer value
statusCategory status = .specRejection
```

This module derives **every one of those five** from one hypothesis — the exported wrapper's own exit
binding at the canonical parameters — plus `catalogGroundsInSpec` and the root's input bound. Nothing
here executes an instruction or inspects a trace; each field is a projection of the postcondition
followed by a model-level computation, and that is the point of the split.

## Where the hypothesis comes from, and why it is stated in exactly this shape

`CanonicalDecodeExit` is not a convenient repackaging: it is spelled at
`canonicalContractParams.env`/`.globals`/`.resultBuffer`/`.repRawV4` because that is what
`Catalog.routineContract`'s `.zesuDecodeRaw` arm builds, and `canonicalDecodeExit_is_contract_exit`
proves — by `Iff.rfl`, so it cannot drift — that the named predicate *is*
`(functionInstanceZesuDecodeRaw …).binding.exit args (spec.meaning args)`. That is the proposition a
`LocalContractAssumptions`-derived `ImplementsFunctionInstance` hands back at the wrapper's exit
state, and nothing else supplies it.

Stating it at the *concrete* `canonicalEnvironment`/`Elfling.canonicalDecoderGlobalsLayout` instead
would have been the recurring defect in this tree: a hypothesis whose only supplier produces a
syntactically different term, so the helper is inapplicable at its one intended call site. The
projections below are stated generically over the layout/representation wherever the conclusion
permits it, and specialized only where the conclusion names an address.

## Anti-vacuity: what discharges each hypothesis

* `CanonicalDecodeExit` — the entry function instance's closed obligation, i.e.
  `Contracts.function_instance_implements_its_contract` applied to
  `sszProgramCorrectness_of_locals`, which is `LocalContractAssumptions` and nothing more. It is the
  sibling half of the capstone; the `Iff.rfl` pin above is the check that the two halves meet.
* `catalogGroundsInSpec` — a conjunct of `catalogSemanticObligations`, and **proved**:
  `Elfling.Validation.sszComplianceObligations_of_residue` supplies it from
  `catalogSemanticObligations_of_oracleAgreement`, so it is not a new premise for the capstone.
* the input bound — the root theorem's own hypothesis, definitionally `rootComplianceScope input`.

None of the three is an obligation this module invents.

## Two corrections to what this module was expected to need

* **The error taxonomy is not a premise here.** The rejection branch needs the recorded status to be
  one the specification can produce, and the natural reading is that this comes from the catalog's
  taxonomy obligations (`leafReadsOnlyFailInvalid`, `collectionsNeverUnknownFork`,
  `onlyForkConfigRaisesUnknownFork`, `meaningNeverForkOrMemory`,
  `outOfMemoryUnreachableBelowBound`). It does not: `SemanticObligations` already proves
  `meaningDecode_onlyInvalidOrFork` **outright**, with no hypotheses, so
  `specRejection_of_spec_rejects` takes none. Those five obligations are what that theorem's own
  proof is built from, one layer down; asking for them again here would have added premises with no
  content.
* **`fresh_call_is_never_alreadyDecoded` is not needed either, and not because it is false.** The
  refusal is ruled out one step earlier and more cheaply: `meaningDecode input` is an `Except`, and
  `callOutcome DecoderGlobalsModel.fresh` on a `false` `attempted` flag reduces past the
  `alreadyDecoded` branch definitionally. The lemma is the right statement of that fact for a
  consumer holding an abstract `callOutcome`; here the model is concrete, so the branch never
  appears. `statusCategory DecodeStatus.alreadyDecoded.code = .undocumented`
  (`statusCategory_pinned`) is what would have caught the mistake had it been possible to make.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-! ## The fresh call's recorded globals

Three facts about `resultingGlobals DecoderGlobalsModel.fresh`, computed once. Everything downstream
that has to know *what* the wrapper stored, *which* status it recorded, or *what* the two accessors
therefore return goes through these rather than re-reducing `callOutcome`. -/

/-- A fresh accepting call records the attempt, the `ok` status, and the value. -/
theorem freshGlobals_ok (value : SszBridge.RawV4) :
    resultingGlobals DecoderGlobalsModel.fresh (.ok value) =
      { attempted := true, status := .ok, stored := some value } := by
  simp [resultingGlobals, callOutcome, DecoderGlobalsModel.fresh, DecodeCallOutcome.status,
    DecodeCallOutcome.stored]

/-- A fresh rejecting call records the attempt and the normalized error status, and stores nothing. -/
theorem freshGlobals_error (error : SszDecodeError) :
    resultingGlobals DecoderGlobalsModel.fresh (.error error) =
      { attempted := true, status := statusOfResult (.error error), stored := none } := by
  simp [resultingGlobals, callOutcome, DecoderGlobalsModel.fresh, DecodeCallOutcome.status,
    DecodeCallOutcome.stored]

/-- `zesu_raw_error`'s meaning at the accepted model is the `ok` code — the literal
`SuccessfulRun.accessors` names. -/
@[simp] theorem freshGlobals_ok_statusCode (value : SszBridge.RawV4) :
    (resultingGlobals DecoderGlobalsModel.fresh (.ok value)).status.code = DecodeStatus.ok.code := by
  rw [freshGlobals_ok]

/-- `zesu_raw_result`'s meaning at the accepted model is the result buffer, not null. -/
@[simp] theorem freshGlobals_ok_pointer (value : SszBridge.RawV4) (resultBuffer : Nat) :
    (if (resultingGlobals DecoderGlobalsModel.fresh (.ok value)).stored.isSome then resultBuffer
      else 0) = resultBuffer := by
  rw [freshGlobals_ok]; simp

/-- `zesu_raw_result`'s meaning at a rejected model is null — the `0` `RejectedRun.accessors`
names. -/
@[simp] theorem freshGlobals_error_pointer (error : SszDecodeError) (resultBuffer : Nat) :
    (if (resultingGlobals DecoderGlobalsModel.fresh (.error error)).stored.isSome then resultBuffer
      else 0) = 0 := by
  rw [freshGlobals_error]; simp

/-! ## The `a0` clause, read as the runner reads it -/

/-- Both codes the wrapper can leave in `a0` are `0` or `1`, so the `BitVec.toNat` round trip
`observeReturnCode?` performs loses nothing. This is where that side condition is spent, once. -/
theorem returnCode_lt_two_pow_64 (outcome : DecodeCallOutcome) : outcome.returnCode < 2 ^ 64 := by
  have : outcome.returnCode ≤ 1 := by cases outcome <;> simp [DecodeCallOutcome.returnCode]
  omega

/-- **The wrapper's return code, observed.** The postcondition pins `a0` as a 64-bit word; the runner
reads it back through `observeReturnCode?`. Generic in every parameter, because the conclusion names
no address. -/
theorem observeReturnCode_of_postZesuDecodeRaw {env : DecoderEnvironment}
    {globals : DecoderGlobalsLayout} {resultBuffer : Nat}
    {rep : ContainerRepresentation SszBridge.RawV4} {incoming : DecoderGlobalsModel}
    {args : ZesuDecodeRawArgs} {result : Except SszDecodeError SszBridge.RawV4}
    {before after : State}
    (h : postZesuDecodeRaw env globals resultBuffer rep incoming args result before after) :
    observeReturnCode? after = some (callOutcome incoming result).returnCode :=
  observeReturnCode_of_a0 (returnCode_lt_two_pow_64 _) h.2.2.1

/-! ## The stored-result object, read as the runner reads it -/

/-- The value arm of `StoredResultRep`, opened at a model known to hold a value. Separated from its
use so the `match` on `model.stored` is discharged in one place rather than at each projection. -/
theorem storedResultRep_value {globals : DecoderGlobalsLayout}
    {rep : ContainerRepresentation SszBridge.RawV4} {inputBase resultBase : Nat} {input : ByteArray}
    {model : DecoderGlobalsModel} {value : SszBridge.RawV4} {state : State}
    (hstored : model.stored = some value)
    (h : StoredResultRep globals rep inputBase input resultBase model state) :
    rep inputBase input value state resultBase := by
  have harm := h.2
  rw [hstored] at harm
  exact harm

/-- **The stored-result discriminant, observed.** `storedResultDiscriminantAddr` is *by definition*
the address `Elfling.canonicalDecoderGlobalsLayout` puts the discriminant at, so the layout is fixed
here and no address is re-derived; every other parameter stays open. -/
theorem observeOptionTag_of_postZesuDecodeRaw {env : DecoderEnvironment} {resultBuffer : Nat}
    {rep : ContainerRepresentation SszBridge.RawV4} {incoming : DecoderGlobalsModel}
    {args : ZesuDecodeRawArgs} {result : Except SszDecodeError SszBridge.RawV4}
    {before after : State}
    (h : postZesuDecodeRaw env Elfling.canonicalDecoderGlobalsLayout resultBuffer rep incoming args
      result before after) :
    observeOptionTag? after storedResultDiscriminantAddr
      = some (resultingGlobals incoming result).stored.isSome :=
  observe_option_tag_of_rep after storedResultDiscriminantAddr _ h.2.2.2.2.2.2.1

/-! ## The exit binding the capstone actually holds

Everything above is generic. What follows is the one instantiation the root theorem's runner needs,
and it is named rather than written out at each use so that a change to `canonicalContractParams`
breaks one definition instead of silently making five lemmas inapplicable. -/

/-- The exported wrapper's exit binding at the canonical parameters, the runner's pinned input
buffer, and the fresh globals model.

Every argument is `canonicalContractParams`'s own projection rather than the concrete constant it
unfolds to, because the supplier — the entry function instance's closed obligation — produces it in
exactly that spelling. `canonicalDecodeExit_is_contract_exit` is the proof that the two agree. -/
def CanonicalDecodeExit (input : ByteArray) (before after : State) : Prop :=
  postZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
    canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
    DecoderGlobalsModel.fresh ⟨canonicalRunnerLayout.inputBase, input⟩ (meaningDecode input)
    before after

/-- **The named hypothesis is the contract's own exit binding, at the contract's own outcome.**

`Iff.rfl`, and that is the content: `Implements` concludes
`contract.binding.exit args (contract.spec.meaning args) s s'`, so a helper stated at any other term
— a different outcome, a different argument tuple, or the concrete constants rather than the
parameter projections — would be inapplicable at its only call site. Pinning it as a theorem means
that mismatch fails the build here rather than surfacing as an unusable lemma in the assembly.

`Catalog.routineContract`'s `.zesuDecodeRaw` arm is literally
`functionInstanceZesuDecodeRaw p.env p.globals p.resultBuffer p.repRawV4 DecoderGlobalsModel.fresh`,
so this covers the catalog route as well. -/
theorem canonicalDecodeExit_is_contract_exit (input : ByteArray) (before after : State) :
    CanonicalDecodeExit input before after ↔
      (functionInstanceZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
          canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
          DecoderGlobalsModel.fresh).binding.exit ⟨canonicalRunnerLayout.inputBase, input⟩
        ((functionInstanceZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
          canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
          DecoderGlobalsModel.fresh).spec.meaning ⟨canonicalRunnerLayout.inputBase, input⟩)
        before after :=
  Iff.rfl

/-- **The hypothesis is suppliable, exhibited rather than argued.**

A lemma family whose one hypothesis nothing produces is worse than none — it reads as progress and
is not — so the supply route is a theorem here rather than a remark. Given the wrapper's `Implements`
obligation over *any* confinement region (`ImplementsFunctionInstance` is that, at the generated
function instance's execution pcs) and any state satisfying its entry binding, out comes a bounded
entered trace **and** `CanonicalDecodeExit` at its two ends. The obligation itself is
`LocalContractAssumptions` through `global_of_local`; the entry binding at the builder's state is
`EntryBinding.lean`'s.

The step bound is spelled `entryStepBound input.size`, which is definitionally the contract's own
`stepBound` and is also what `SuccessfulRun.withinStepBound` counts against — so the number does not
have to be re-derived when the trace is extended by the `ret` that reaches the sentinel.

Note which state each half is at, because that is the error this tree has made before: the entry
binding is at `entryState`, the exit binding relates `entryState` to `finalState`, and every
observation the five field lemmas make is at `finalState`. A version of this stated at the entry
state would be inapplicable everywhere it is wanted. -/
theorem canonicalDecodeExit_of_implements {region exit : BitVec 64 → Prop} {entryWord : BitVec 64}
    (implements : BinaryFv.RiscV.Elfling.FunctionInstanceContract.Implements region exit entryWord
      (functionInstanceZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
        canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
        DecoderGlobalsModel.fresh))
    (input : ByteArray) (fromStep : Nat) {entryState : State}
    (entryBinding : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh ⟨canonicalRunnerLayout.inputBase, input⟩ entryState) :
    ∃ count finalState,
      count ≤ entryStepBound input.size ∧
        BinaryFv.RiscV.Elfling.EnteredFunctionTrace region exit entryWord fromStep count
          entryState finalState ∧
        CanonicalDecodeExit input entryState finalState :=
  implements ⟨canonicalRunnerLayout.inputBase, input⟩ fromStep entryState entryBinding

/-! ## The spec link

The contract's meaning is `meaningDecode input`; the root theorem's goal names `SszSpec.decode
input`. `catalogGroundsInSpec` is the bridge, and it is **value-carrying** — an acceptance-level
biconditional would settle *whether* the machine accepted and leave the stored value unrelated to the
one the goal names, which is the defect its own docstring in `Contracts/Entry.lean` records. -/

/-- **A spec acceptance names the value the contract stores.** -/
theorem meaningDecode_ok_of_spec_accepts (grounds : catalogGroundsInSpec) {input : ByteArray}
    (inputBound : input.size < 2 * 1024 * 1024) {value : SszBridge.RawV4}
    (accepts : SszSpec.decode input = .accepted value) :
    meaningDecode input = .ok value :=
  (grounds input inputBound value).mpr accepts

/-- **A spec rejection forces the contract to fail**, though not yet with which error. -/
theorem meaningDecode_error_of_spec_rejects (grounds : catalogGroundsInSpec) {input : ByteArray}
    (inputBound : input.size < 2 * 1024 * 1024)
    (rejects : SszSpec.decode input = .rejected) :
    ∃ error, meaningDecode input = .error error := by
  match hm : meaningDecode input with
  | .ok value =>
    rw [(grounds input inputBound value).mp hm] at rejects
    exact absurd rejects (by simp)
  | .error error => exact ⟨error, rfl⟩

/-! ## The five fields

Each is the corresponding projection of `CanonicalDecodeExit`, at the outcome the spec pins. -/

/-- **`SuccessfulRun.inputPreserved` / the same field of the rejected branch.** The borrowed input is
still in the runner's buffer at the wrapper's exit; it is the postcondition's first conjunct, stated
absolutely rather than relative to `before`, so nothing has to be transported. -/
theorem inputPreserved_of_canonicalDecodeExit {input : ByteArray} {before after : State}
    (h : CanonicalDecodeExit input before after) :
    MemoryBytes after canonicalRunnerLayout.inputBase input :=
  h.1

/-- **`SuccessfulRun.returnCode`.** -/
theorem returnCode_of_spec_accepts (grounds : catalogGroundsInSpec) {input : ByteArray}
    (inputBound : input.size < 2 * 1024 * 1024) {value : SszBridge.RawV4}
    (accepts : SszSpec.decode input = .accepted value) {before after : State}
    (h : CanonicalDecodeExit input before after) :
    observeReturnCode? after = some 1 := by
  unfold CanonicalDecodeExit at h
  rw [meaningDecode_ok_of_spec_accepts grounds inputBound accepts] at h
  rw [observeReturnCode_of_postZesuDecodeRaw h]
  rw [(fresh_success_stores_value DecoderGlobalsModel.fresh value rfl).2.1]

/-- **`RejectedRun.returnCode`.** -/
theorem returnCode_of_spec_rejects (grounds : catalogGroundsInSpec) {input : ByteArray}
    (inputBound : input.size < 2 * 1024 * 1024)
    (rejects : SszSpec.decode input = .rejected) {before after : State}
    (h : CanonicalDecodeExit input before after) :
    observeReturnCode? after = some 0 := by
  unfold CanonicalDecodeExit at h
  obtain ⟨error, herror⟩ := meaningDecode_error_of_spec_rejects grounds inputBound rejects
  rw [herror] at h
  rw [observeReturnCode_of_postZesuDecodeRaw h]
  rw [(fresh_rejection_stores_nothing DecoderGlobalsModel.fresh error rfl).2.1]

/-- **`SuccessfulRun.storedPresent`.** -/
theorem storedPresent_of_spec_accepts (grounds : catalogGroundsInSpec) {input : ByteArray}
    (inputBound : input.size < 2 * 1024 * 1024) {value : SszBridge.RawV4}
    (accepts : SszSpec.decode input = .accepted value) {before after : State}
    (h : CanonicalDecodeExit input before after) :
    observeOptionTag? after storedResultDiscriminantAddr = some true := by
  unfold CanonicalDecodeExit at h
  rw [meaningDecode_ok_of_spec_accepts grounds inputBound accepts] at h
  rw [observeOptionTag_of_postZesuDecodeRaw h, freshGlobals_ok]
  rfl

/-- **`RejectedRun.storedAbsent`.** -/
theorem storedAbsent_of_spec_rejects (grounds : catalogGroundsInSpec) {input : ByteArray}
    (inputBound : input.size < 2 * 1024 * 1024)
    (rejects : SszSpec.decode input = .rejected) {before after : State}
    (h : CanonicalDecodeExit input before after) :
    observeOptionTag? after storedResultDiscriminantAddr = some false := by
  unfold CanonicalDecodeExit at h
  obtain ⟨error, herror⟩ := meaningDecode_error_of_spec_rejects grounds inputBound rejects
  rw [herror] at h
  rw [observeOptionTag_of_postZesuDecodeRaw h, freshGlobals_error]
  rfl

/-- **`SuccessfulRun.storedValue`.** The whole `RawV4` — root allocation, heap arrays, descriptor
table, borrowed input slices — laid out at the canonical result buffer, at the value the *spec*
names rather than at some value the machine happened to store. That last part is `catalogGroundsInSpec`
carrying the value; with the acceptance-level obligation it once had, this lemma could not be stated.

`canonicalContractParams.repRawV4` is `canonicalRepRawV4`, whose value arm is by definition
`RawV4Rep state inputBase input base value`, so no representation is chosen here. -/
theorem storedValue_of_spec_accepts (grounds : catalogGroundsInSpec) {input : ByteArray}
    (inputBound : input.size < 2 * 1024 * 1024) {value : SszBridge.RawV4}
    (accepts : SszSpec.decode input = .accepted value) {before after : State}
    (h : CanonicalDecodeExit input before after) :
    RawV4Rep after canonicalRunnerLayout.inputBase input Elfling.canonicalResultBuffer value := by
  unfold CanonicalDecodeExit at h
  rw [meaningDecode_ok_of_spec_accepts grounds inputBound accepts] at h
  exact storedResultRep_value (by rw [freshGlobals_ok]) h.2.2.2.2.2.2

/-! ## The recorded status is one the specification can produce

`RejectedRun.specRejection` is the field that stops an arena exhaustion or a refused second call from
being reported as a rejection, and it is the only one of the five that is not a projection. -/

/-- A status normalized from `invalidSsz` or `unknownFork` is a spec rejection. The two other
`DecodeStatus` codes a completed call could carry — `outOfMemory` and `alreadyDecoded` — are excluded
by `statusCategory` itself (`statusCategory_pinned`), so this is where the taxonomy has to be spent
rather than somewhere it could be forgotten. -/
theorem statusCategory_of_freshRejection {error : SszDecodeError}
    (h : error = .invalidSsz ∨ error = .unknownFork) :
    statusCategory (resultingGlobals DecoderGlobalsModel.fresh (.error error)).status.code
      = .specRejection := by
  rcases h with h | h <;> subst h <;> decide

/-- **The rejection field is not a formality**, stated as a refusal rather than asserted in prose.

`statusCategory _ = .specRejection` would be worthless content if it held of every status a fresh
call can record, and the reading that makes it worthless is available: an exhausted arena also
returns `0` and also records a nonzero status. It does **not** classify as a rejection, and this is
that fact at the same term `statusCategory_of_freshRejection` concludes about — so a categorization
that quietly widened to admit `outOfMemory` breaks the build here rather than turning the root's
rejected branch into an answer the specification never gives. -/
theorem freshRejection_outOfMemory_is_not_specRejection :
    statusCategory (resultingGlobals DecoderGlobalsModel.fresh (.error .outOfMemory)).status.code
      ≠ .specRejection := by decide

/-- **`RejectedRun.specRejection`.** The status the wrapper records for an input the specification
rejects is `invalidSsz` or `unknownFork` — never `outOfMemory`, and never `alreadyDecoded`.

**No taxonomy obligation is a premise, and that is a correction rather than an omission.**
`meaningDecode_onlyInvalidOrFork` is proved outright in `Contracts/SemanticObligations.lean`:
`meaningDecode` composes readers whose only failure is `invalidSsz` with the one chain-config path
that can raise `unknownFork`, and has no allocation-failure outcome at all. So the catalog's five
error-taxonomy obligations are what *that* proof rests on, one layer down, not premises this lemma
must carry. -/
theorem specRejection_of_spec_rejects (grounds : catalogGroundsInSpec) {input : ByteArray}
    (inputBound : input.size < 2 * 1024 * 1024)
    (rejects : SszSpec.decode input = .rejected) :
    statusCategory (resultingGlobals DecoderGlobalsModel.fresh (meaningDecode input)).status.code
      = .specRejection := by
  obtain ⟨error, herror⟩ := meaningDecode_error_of_spec_rejects grounds inputBound rejects
  rw [herror]
  exact statusCategory_of_freshRejection (meaningDecode_onlyInvalidOrFork input error herror)

/-! ## The two bundles

The shape the assembly consumes: one hypothesis in, every decode-side field out. Keeping the bundles
beside the individual lemmas is deliberate — the fields are what a reader checks against
`Execution.lean`, and the bundle is what the capstone applies. -/

/-- **Every decode-side field of `SuccessfulRun`.** What remains for the accepted branch is the
builder's run, the decode trace with its bound, and `AcceptedAccessorTraces`. -/
theorem successfulRun_fields_of_canonicalDecodeExit (grounds : catalogGroundsInSpec)
    {input : ByteArray} (inputBound : input.size < 2 * 1024 * 1024) {value : SszBridge.RawV4}
    (accepts : SszSpec.decode input = .accepted value) {before after : State}
    (h : CanonicalDecodeExit input before after) :
    observeReturnCode? after = some 1 ∧
      observeOptionTag? after storedResultDiscriminantAddr = some true ∧
      MemoryBytes after canonicalRunnerLayout.inputBase input ∧
      RawV4Rep after canonicalRunnerLayout.inputBase input Elfling.canonicalResultBuffer value :=
  ⟨returnCode_of_spec_accepts grounds inputBound accepts h,
    storedPresent_of_spec_accepts grounds inputBound accepts h,
    inputPreserved_of_canonicalDecodeExit h,
    storedValue_of_spec_accepts grounds inputBound accepts h⟩

/-- **Every decode-side field of `RejectedRun`**, at the status the wrapper actually recorded — which
is also the status `zesu_raw_error`'s contract returns from that model, so the bundle and
`RejectedAccessorTraces` name the same number. What remains for the rejected branch is the builder's
run, the decode trace with its bound, and `RejectedAccessorTraces` at that status. -/
theorem rejectedRun_fields_of_canonicalDecodeExit (grounds : catalogGroundsInSpec)
    {input : ByteArray} (inputBound : input.size < 2 * 1024 * 1024)
    (rejects : SszSpec.decode input = .rejected) {before after : State}
    (h : CanonicalDecodeExit input before after) :
    observeReturnCode? after = some 0 ∧
      observeOptionTag? after storedResultDiscriminantAddr = some false ∧
      MemoryBytes after canonicalRunnerLayout.inputBase input ∧
      statusCategory
          (resultingGlobals DecoderGlobalsModel.fresh (meaningDecode input)).status.code
        = .specRejection :=
  ⟨returnCode_of_spec_rejects grounds inputBound rejects h,
    storedAbsent_of_spec_rejects grounds inputBound rejects h,
    inputPreserved_of_canonicalDecodeExit h,
    specRejection_of_spec_rejects grounds inputBound rejects⟩

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
