import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Runner
import BinaryFv.SSZ.Zesu.Validation.MeaningAgreement

/-!
# Running the real binary against the specification

Every check here *executes the pinned RISC-V binary* in the Sail model — building the entry state,
stepping `zesu_decode_raw` to its return sentinel, calling `zesu_raw_result` and `zesu_raw_error`,
and reconstructing the decoded value out of machine memory — and compares the answer with
`SszSpec.decode`, the pinned SizzLean oracle. Nothing is stubbed or mocked.

The headline check is `runner_agrees_with_spec`: on every case of the small corpus, the runner and
the specification give the *same* answer, and on an accepted case that means the same `RawV4` down
to the last field, compared through the canonical `ssz-value-v1` render. That single check exercises
the whole stack at once — the state builder, the machine, the accessors, `observeRawV4?`, and the
classifier.

The rest are scenarios the corpus cannot express, each pinning one failure mode:

* a deliberately short budget is `fuelExhausted`, not a rejection;
* an observer pointed at the wrong address is `malformedResult`, not a bogus acceptance;
* a **second** call to the wrapper — which returns `0` with `alreadyDecoded`, exactly like a
  rejection returns `0` — is `badReturn`, not a rejection.

A bad artifact and an oversized input need no execution: `executeChecked_rejects_wrong_artifact`
and `executeChecked_rejects_oversized_input` prove the gate rejects *every* such caller, which is
stronger than any finite test.

Like the other `Validation` modules this is falsification evidence, never a proof premise: the
import guard in `nix/proof.nix` keeps any theorem module from importing it.
-/

namespace BinaryFv.SSZ.Zesu.Validation

open BinaryFv.SSZ
open BinaryFv.SSZ.Zesu
open BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

/-! ## The runner against the specification, on the whole corpus -/

/-- The runner's answer as a comparable label. An acceptance carries the full canonical render of
the decoded value, so agreement means field-for-field agreement, not just "both accepted". -/
def runnerAnswerLabel (input : ByteArray) : String :=
  match executeDecode input with
  | .ok (.accepted value) => "accept\t" ++ value.render
  | .ok .rejected => "reject"
  | .error error => "error\t" ++ toString (repr error)

/-- The specification's answer in the same vocabulary. -/
def specAnswerLabel (input : ByteArray) : String :=
  match SszSpec.decode input with
  | .accepted value => "accept\t" ++ value.render
  | .rejected => "reject"

/-- For every corpus case: the executed binary agrees with the pinned oracle, *and* its verdict
matches the corpus's own recorded expectation. Both conditions are checked in one pass over the
corpus so the machine is run once per case rather than twice. -/
def runnerAgreesWithSpec : Bool :=
  GeneratedCorpus.corpus.all fun c =>
    let input := hexToBytes c.2.2
    let answer := runnerAnswerLabel input
    (answer == specAnswerLabel input) && (answer.startsWith "accept" == c.2.1)

/-- **The real binary decodes exactly what the specification says, on every corpus case.**

This is the end-to-end differential: 46 cases — five accepted (raw and ERE-prefixed, including the
rich payload), an unknown fork, a truncated body, and every offset mutation — each run instruction
by instruction through the Sail model, with the accepted ones compared field for field, and each
verdict additionally checked against the corpus's independently recorded expectation.

**Both halves of that second conjunct matter.** Agreement with the oracle alone would pass if the
runner and the oracle were wrong in the same way; the corpus's own recorded verdict is an independent
third opinion, so all three must coincide. And the corpus is genuinely two-sided — verified by
counting rather than by reading this docstring: 46 cases, **5 accepted**
(`valid-v4-raw`, `valid-v4-ere`, `valid-v4-empty-variable-lists`, `valid-v4-rich-raw`,
`valid-v4-rich-ere`) and 41 rejected. A one-sided corpus would make the acceptance path untested
while the check still passed, which is exactly how an earlier 360-input falsity sweep in this row
turned out to have zero power.

**What this theorem does NOT cover, stated here rather than only in the generated header.** The
generator (`ssz_contract_corpus.py`) drops any case whose input exceeds its `max_bytes` budget,
because `native_decide` over the full decode is impractical there, and records the drops at the top
of `GeneratedCorpus.lean`. Three cases are currently dropped — `raw-ere-prefix-collision`,
`ere-prefixed-collision`, `versioned-hashes-over-bound` — and **two of the three are *accepted*
cases**, so the kernel-checked acceptance set is 5 of 7. All three are still exercised by
`ssz_differential_audit.py` on the Python side; they are outside the *kernel-checked* set, not
outside coverage. Recorded in this docstring because a reader citing `runner_agrees_with_spec` reads
this, not the generated file's header comment. -/
theorem runner_agrees_with_spec : runnerAgreesWithSpec = true := by native_decide

/-! ## The gate

The bad-artifact and oversized-input cases need no execution at all:
`executeChecked_rejects_wrong_artifact` and `executeChecked_rejects_oversized_input` prove the gate
rejects *every* such caller, and `executeChecked_eq_executeDecode` proves it is transparent for
every accepted one — all three universally quantified, which no finite test can match. What remains
worth checking here is that the pinned artifact really does supply the entry points the runner
calls, so those theorems are about a gate the real binary clears. -/

/-- All three exported entry points resolve in the pinned artifact. -/
theorem runner_symbols_resolve : runnerSymbols.isSome = true := by native_decide

/-! ## Scenarios the corpus cannot express

Each runs the machine but substitutes one piece of the runner, so the classifier's distinctions are
tested against real execution rather than hand-built states. -/

/-- Whether an answer is exactly this execution error. `DecodeOutcome` carries a `RawV4` and has no
`DecidableEq`, so the checks below compare through these `Bool`s rather than by equation. -/
def isExecutionError (expected : RiscvSpec.ExecutionError) :
    Except RiscvSpec.ExecutionError DecodeOutcome → Bool
  | .error error => error == expected
  | .ok _ => false

/-- Whether an answer is an acceptance. -/
def isAcceptance : Except RiscvSpec.ExecutionError DecodeOutcome → Bool
  | .ok (.accepted _) => true
  | _ => false

/-- Whether an answer is the normalized rejection. -/
def isRejection : Except RiscvSpec.ExecutionError DecodeOutcome → Bool
  | .ok .rejected => true
  | _ => false

/-- Take the first corpus case with a given id. -/
def corpusCase (name : String) : ByteArray :=
  match GeneratedCorpus.corpus.find? (fun c => c.1 == name) with
  | some c => hexToBytes c.2.2
  | none => ByteArray.empty

/-- Run the decoder with an arbitrary budget instead of the derived one. -/
def answerWithFuel (input : ByteArray) (fuel : Nat) :
    Except RiscvSpec.ExecutionError DecodeOutcome :=
  match (do
      buildZesuEntryState input
      let outcome ← runToOutcome sentinelWord fuel 0
      let final ← EStateM.get
      pure (classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
        Elfling.canonicalResultBuffer .noReturn .noReturn outcome final) : SailM _).run
      initialState with
  | .ok answer _ => answer
  | .error _ _ => .error .trapped

/-- **A budget too small to finish is fuel exhaustion, not a rejection.** The input here is one the
decoder *does* reject when given its real budget, so the run genuinely stops early rather than
finishing and being misreported. -/
theorem short_fuel_is_exhaustion :
    isExecutionError .fuelExhausted (answerWithFuel (corpusCase "truncated") 100) = true := by
  native_decide

/-- The same input with its derived budget really is a rejection — so the check above is about the
budget, not about an input that fails anyway. -/
theorem same_input_with_real_fuel_is_rejection :
    isRejection (executeDecode (corpusCase "truncated")) = true := by native_decide

/-- Run the full pipeline but observe the value at the wrong address. -/
def answerWithObserverAt (input : ByteArray) (base : Nat) :
    Except RiscvSpec.ExecutionError DecodeOutcome :=
  match runnerSymbols with
  | none => .error .invalidArtifact
  | some symbols =>
    match (do
        buildZesuEntryState input
        let outcome ← runToOutcome sentinelWord (zesuFuel input.size) 0
        let final ← EStateM.get
        let accessors ← runAccessorsIfReached symbols outcome
        pure (classifyWrapperRun (fun s => MemoryRepresentation.observeRawV4? s base)
          storedResultDiscriminantAddr Elfling.canonicalResultBuffer
          accessors.1 accessors.2 outcome final) : SailM _).run initialState with
    | .ok answer _ => answer
    | .error _ _ => .error .trapped

/-- **An observer that cannot read the value reports `malformedResult`.** The run itself succeeded —
the wrapper returned `1` and both accessors agreed — so the only thing that failed is the
observation, and it is not allowed to become a rejection or a wrong acceptance. -/
theorem misplaced_observer_is_malformed :
    isExecutionError .malformedResult
      (answerWithObserverAt (corpusCase "valid-v4-empty-variable-lists")
        (Elfling.canonicalResultBuffer + 1)) = true := by native_decide

/-- At the right address the same run is the acceptance, so the check above is about the observer's
address and nothing else. -/
theorem correct_observer_accepts :
    isAcceptance (answerWithObserverAt (corpusCase "valid-v4-empty-variable-lists")
      Elfling.canonicalResultBuffer) = true := by native_decide

/-- Decode once, then call the exported entry a **second** time on the same machine, with the C ABI
set up exactly as the first call had it. -/
def secondCallAnswer (input : ByteArray) : Except RiscvSpec.ExecutionError DecodeOutcome :=
  match runnerSymbols with
  | none => .error .invalidArtifact
  | some symbols =>
    match (do
        buildZesuEntryState input
        let _ ← runToOutcome sentinelWord (zesuFuel input.size) 0
        writeReg x10 (BitVec.ofNat 64 canonicalRunnerLayout.inputBase)
        writeReg x11 (BitVec.ofNat 64 input.size)
        writeReg x1 sentinelWord
        writeReg x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop)
        writeReg PC (BitVec.ofNat 64 symbols.decodeEntry)
        writeReg nextPC (BitVec.ofNat 64 symbols.decodeEntry)
        let outcome ← runToOutcome sentinelWord (zesuFuel input.size) 0
        let final ← EStateM.get
        let accessors ← runAccessorsIfReached symbols outcome
        pure (classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
          Elfling.canonicalResultBuffer accessors.1 accessors.2 outcome final) : SailM _).run
        initialState with
    | .ok answer _ => answer
    | .error _ _ => .error .trapped

/-- **A refused second call is `badReturn`, never a rejection.**

This is the sharpest of the negatives. The wrapper refuses the second call and returns `0` — the
same code a genuine rejection returns — and the executed `zesu_raw_error` reports `alreadyDecoded`
while `zesu_raw_result` still hands back the first call's non-null buffer. Only the status
distinguishes it, which is why `classifyWrapperRun` dispatches on the status before it looks at the
result slot. -/
theorem second_call_is_bad_return :
    isExecutionError .badReturn
      (secondCallAnswer (corpusCase "valid-v4-empty-variable-lists")) = true := by native_decide

/-- The first call on that same input is the acceptance, so the check above really is about the
second call. -/
theorem first_call_accepts :
    isAcceptance (executeDecode (corpusCase "valid-v4-empty-variable-lists")) = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation
