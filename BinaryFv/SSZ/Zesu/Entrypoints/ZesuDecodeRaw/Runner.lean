import BinaryFv.RiscV.Proof.RunnerCorrespondence
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Classify
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Fuel
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Preflight
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.StateBuilder
import BinaryFv.SSZ.Zesu.MemoryRepresentation.ValueObserver

/-!
# Running the decoder and its exported accessors

This is the executable half of the public API: build the entry state, run the machine to the return
sentinel, then **execute the two exported accessors** — `zesu_raw_result` and `zesu_raw_error` — as
real calls from the post-return state, and hand all of it to `classifyWrapperRun`.

Executing the accessors, rather than re-reading the globals the wrapper wrote, is the point. The
accessors are the documented public interface: `zesu_raw_result` decides null-versus-payload from
the inline optional's discriminant, and `zesu_raw_error` reports the recorded status. Running them
means the runner's answer depends on the same code a caller would run, and it makes the accessor
contracts (`contractRawResult`, `contractRawError`) load-bearing for the runner rather than
decorative.

Each accessor call is set up exactly like the main one: a fresh return address (the same sentinel),
a fresh stack pointer at the top of the runner's stack, and `PC`/`nextPC` at the symbol. Its fuel
comes from its own contract's step bound (`Fuel.lean`), so an accessor that runs away is reported as
fuel exhaustion rather than looping forever.

Every address here is resolved from the pinned artifact's symbol table or the checked layout; the
module writes no address literal.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu
open BinaryFv.SSZ.Zesu.MemoryRepresentation

/-! ## Symbols and addresses the runner needs -/

/-- The three exported entry points the runner calls, resolved from the pinned artifact's symbol
table in one place. Resolving them *before* building any state means a symbol table that does not
contain them is reported as an invalid artifact instead of surfacing as a Sail fault. -/
structure RunnerSymbols where
  decodeEntry : Nat
  rawResult : Nat
  rawError : Nat
deriving Repr

/-- Resolve the runner's three entry points, or fail. -/
def runnerSymbols : Option RunnerSymbols := do
  let decode ← Artifact.zesuDecodeRaw.toOption
  let result ← Artifact.zesuRawResult.toOption
  let error ← Artifact.zesuRawError.toOption
  pure ⟨decode.value, result.value, error.value⟩

/-- The canonical artifact resolves all three, so the `none` branch above is unreachable for the
binary this proof is about — and the builder's own `Unreachable` throw on an unresolved entry symbol
is likewise unreachable. -/
theorem runnerSymbols_isSome : runnerSymbols.isSome = true := by native_decide

/-- The resolved entry points, as a value rather than an `Option`. Total because the canonical
artifact resolves all three, so downstream statements do not have to carry a resolution hypothesis
around. -/
def resolvedSymbols : RunnerSymbols := runnerSymbols.get runnerSymbols_isSome

@[simp] theorem runnerSymbols_eq_resolved : runnerSymbols = some resolvedSymbols :=
  (Option.some_get runnerSymbols_isSome).symm

/-- The address of the inline `stored_result` object's discriminant byte, from the checked globals
layout and the reflected option layout. -/
def storedResultDiscriminantAddr : Nat :=
  Elfling.canonicalDecoderGlobalsLayout.storedResult +
    Elfling.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset

/-- The runner's value observation: the complete `RawV4` read from the canonical result buffer —
the address `zesu_raw_result` returns on success. -/
def observeDecodedValue (state : State) : Option SszBridge.RawV4 :=
  observeRawV4? state Elfling.canonicalResultBuffer

/-- The return sentinel as a machine word. Reaching it ends a run; it is in no mapped range, so it
cannot be a real instruction fetch. -/
def sentinelWord : BitVec 64 := BitVec.ofNat 64 canonicalRunnerLayout.sentinel

/-! ## Running one call -/

/-- Call a zero-argument exported accessor from the current state and report how it ended.

The C ABI setup is explicit rather than inherited from whatever the previous call left behind: `ra`
is the sentinel, `sp` is the top of the runner's stack, and `PC`/`nextPC` are the accessor's entry.
A reached sentinel with a readable `a0` is `returned`; the other three outcomes stay distinct. -/
def runAccessor (entryPc fuel : Nat) : SailM AccessorOutcome := do
  writeReg x1 sentinelWord
  writeReg x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop)
  writeReg PC (BitVec.ofNat 64 entryPc)
  writeReg nextPC (BitVec.ofNat 64 entryPc)
  match ← runToOutcome sentinelWord fuel 0 with
  | .reached _ =>
    let final ← EStateM.get
    match observeReturnCode? final with
    | some code => pure (.returned code)
    | none => pure .noReturn
  | .trapped => pure .trapped
  | .exhausted => pure .exhausted

/-- Call both accessors, but only for a run that actually returned. After a trap or an exhausted
budget the machine state is not one the accessors' contracts describe, so nothing is called and the
placeholder outcomes are passed along — the classifier ignores them in exactly those two cases
(`classifyWrapperRun_trapped`, `classifyWrapperRun_exhausted`). -/
def runAccessorsIfReached (symbols : RunnerSymbols) (outcome : SentinelOutcome) :
    SailM (AccessorOutcome × AccessorOutcome) :=
  match outcome with
  | .reached _ => do
    let result ← runAccessor symbols.rawResult (accessorFuel rawResultStepBound)
    let error ← runAccessor symbols.rawError (accessorFuel rawErrorStepBound)
    pure (result, error)
  | _ => pure (AccessorOutcome.noReturn, AccessorOutcome.noReturn)

/-- The whole machine-level run: build the entry state, run `zesu_decode_raw` to the sentinel,
execute both accessors, and classify — in one place, so there is no second answer to drift.

The value and the discriminant are observed from the state **as the decode left it**, before either
accessor runs, so the observation cannot be affected by accessor execution. -/
def runZesuDecodeRaw (symbols : RunnerSymbols) (input : ByteArray) :
    SailM (Except RiscvSpec.ExecutionError DecodeOutcome) := do
  buildZesuEntryState input
  let outcome ← runToOutcome sentinelWord (zesuFuel input.size) 0
  let afterCall ← EStateM.get
  let accessors ← runAccessorsIfReached symbols outcome
  pure (classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
    Elfling.canonicalResultBuffer accessors.1 accessors.2 outcome afterCall)

/-- Read a completed Sail run's answer.

A Sail-level fault that escapes the run — an access outside materialized memory, a failed model
assertion, an unreachable model branch — is a trap: the machine could not continue, which is exactly
what `.trapped` names. (The builder's own `Unreachable` throw, taken when the entry symbol does not
resolve, cannot happen here: `runnerSymbols` has already resolved it.) -/
def runAnswer (action : SailM (Except RiscvSpec.ExecutionError DecodeOutcome)) :
    Except RiscvSpec.ExecutionError DecodeOutcome :=
  match action.run initialState with
  | .ok result _ => result
  | .error _ _ => .error .trapped

/-- Execute the decoder on `input` from the pinned artifact. -/
def executeDecode (input : ByteArray) : Except RiscvSpec.ExecutionError DecodeOutcome :=
  match runnerSymbols with
  | none => .error .invalidArtifact
  | some symbols => runAnswer (runZesuDecodeRaw symbols input)

/-- The public entry: reject a non-canonical artifact or an out-of-bound input first, then run.

`preflight` is a decidable check on the caller's `ByteArray`s that touches neither machine memory
nor a Sail step, so "rejected before any address arithmetic" is literal. -/
def executeChecked (binary : RiscvSpec.ValidatedElf) (input : ByteArray) :
    Except RiscvSpec.ExecutionError DecodeOutcome :=
  match preflight binary input with
  | .error error => .error error
  | .ok () => executeDecode input

/-! ## What the public entry does with a rejected caller

These are about `executeChecked`'s gate, and hold without running the machine at all. -/

/-- A non-canonical artifact never reaches the machine. -/
theorem executeChecked_rejects_wrong_artifact {binary : RiscvSpec.ValidatedElf} (input : ByteArray)
    (h : binary.bytes ≠ Artifact.bytes) :
    executeChecked binary input = .error .invalidArtifact := by
  unfold executeChecked
  rw [preflight_rejects_wrong_artifact input h]

/-- An input outside the theorem's bound never reaches the machine either. -/
theorem executeChecked_rejects_oversized_input {binary : RiscvSpec.ValidatedElf}
    (hcanon : artifactIsCanonical binary = true) {input : ByteArray}
    (h : Runtime.maximumInputBytes ≤ input.size) :
    executeChecked binary input = .error .invalidArtifact := by
  unfold executeChecked
  rw [preflight_rejects_oversized_input hcanon h]

/-- On an accepted caller the gate is transparent: the answer is exactly the machine run's. -/
theorem executeChecked_eq_executeDecode {binary : RiscvSpec.ValidatedElf}
    (hcanon : artifactIsCanonical binary = true) {input : ByteArray}
    (h : input.size < Runtime.maximumInputBytes) :
    executeChecked binary input = executeDecode input := by
  unfold executeChecked
  rw [preflight_ok hcanon h]

/-! ## A Sail-level fault stays a trap

`runAnswer`'s docstring says a fault escaping the Sail run is `.trapped`. That was true by
definition and stated nowhere as a theorem, which is the same shape of gap the converse column
records below: a claim made in prose at a layer where nothing checks it. It is one line, and it is
the *forward* half of the trap story — the classifier's `classifyWrapperRun_trapped` covers a run
that stalled and came back, this covers a run that never came back at all. -/

/-- **A run the Sail model could not complete answers `.error .trapped`.** An access outside
materialized memory, a failed model assertion or an unreachable model branch escapes as an
`EStateM` error, and `runAnswer` maps every one of them to the same trap — in particular to *an
execution error*, never to `.ok .rejected` or `.ok (.accepted _)`.

The symbol resolution is a premise rather than `runnerSymbols_eq_resolved`, so this lemma needs no
`native_decide` witness — the same discipline the converses below follow. -/
theorem executeDecode_trapped_of_sail_fault {input : ByteArray} {symbols : RunnerSymbols}
    {fault : Sail.Error exception} {faulted : State}
    (hsymbols : runnerSymbols = some symbols)
    (h : (runZesuDecodeRaw symbols input).run initialState = .error fault faulted) :
    executeDecode input = .error .trapped := by
  unfold executeDecode runAnswer
  simp only [hsymbols, h]

/-! ## Following a real trace

The correspondence in the other direction: given a composed Sail trace from the built entry state to
the sentinel, the *executable* runner follows it and answers with the classification of the state
that trace ends in. This is the seam the local function instance proofs feed into — they produce the trace,
and these lemmas carry it through the runner to the public answer.

The budget premise is deliberately left in view. `runToOutcome_of_traceToSentinel` needs a strict
`count < fuel`, and `count_lt_zesuFuel` supplies it from the contract's own step bound, so the fuel
is never a free parameter that could be enlarged to make a proof go through. -/

/-- The main loop follows any trace whose length the exported contract's step bound covers. The
`count ≤ entryStepBound` premise is exactly what the function instance contract gives; `count_lt_zesuFuel`
turns it into the strict inequality the generic correspondence requires. -/
theorem runToOutcome_of_entry_trace (input : ByteArray) {count : Nat} {entry final : State}
    (htrace : TraceToSentinel sentinelWord 0 count entry final)
    (hbound : count ≤ entryStepBound input.size + 1) :
    Runs (runToOutcome sentinelWord (zesuFuel input.size) 0) entry final (.reached count) := by
  have := runToOutcome_of_traceToSentinel sentinelWord count (zesuFuel input.size) 0 entry final
    htrace (count_lt_zesuFuel hbound)
  simpa using this

/-- Reading the current state is a run that changes nothing. -/
theorem get_runs (state : State) : Runs (EStateM.get : SailM State) state state state := rfl

/-- **The executable runner follows a composed trace to its answer.**

Given the builder's run, a trace from the built state to the sentinel within the contract's step
bound, and the two accessor runs from the trace's final state, the whole runner runs to exactly the
classification of that final state. Nothing here re-derives machine behaviour: the trace and the
accessor runs are premises, supplied by the local proofs. -/
theorem runZesuDecodeRaw_of_trace (symbols : RunnerSymbols) (input : ByteArray) {count : Nat}
    {entry final after : State} {accessors : AccessorOutcome × AccessorOutcome}
    (hbuild : Runs (buildZesuEntryState input) initialState entry ())
    (htrace : TraceToSentinel sentinelWord 0 count entry final)
    (hbound : count ≤ entryStepBound input.size + 1)
    (haccessors : Runs (runAccessorsIfReached symbols (.reached count)) final after accessors) :
    Runs (runZesuDecodeRaw symbols input) initialState after
      (classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
        Elfling.canonicalResultBuffer accessors.1 accessors.2 (.reached count) final) :=
  Runs.bind hbuild
    (Runs.bind (runToOutcome_of_entry_trace input htrace hbound)
      (Runs.bind (get_runs final) (Runs.bind haccessors rfl)))

/-- The same, read off through the public entry: `executeDecode` answers with the classification of
the traced final state. -/
theorem executeDecode_of_trace {symbols : RunnerSymbols} (input : ByteArray) {count : Nat}
    {entry final after : State} {accessors : AccessorOutcome × AccessorOutcome}
    (hsymbols : runnerSymbols = some symbols)
    (hbuild : Runs (buildZesuEntryState input) initialState entry ())
    (htrace : TraceToSentinel sentinelWord 0 count entry final)
    (hbound : count ≤ entryStepBound input.size + 1)
    (haccessors : Runs (runAccessorsIfReached symbols (.reached count)) final after accessors) :
    executeDecode input =
      classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
        Elfling.canonicalResultBuffer accessors.1 accessors.2 (.reached count) final := by
  have hrun : (runZesuDecodeRaw symbols input).run initialState =
      .ok (classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
        Elfling.canonicalResultBuffer accessors.1 accessors.2 (.reached count) final) after :=
    runZesuDecodeRaw_of_trace symbols input hbuild htrace hbound haccessors
  unfold executeDecode runAnswer
  simp only [hsymbols, hrun]

/-! ## The two public outcomes, from a run

These are what `BinaryFv/SSZ/Root.lean` consumes. Each takes a complete description of one machine
run — the builder's run, a trace within the contract's step bound, the wrapper's own globals, and
the two accessor calls — and concludes the public answer, with no machine detail left for the root
to reconstruct. -/

/-- The canonical result buffer is not the null pointer, so `zesu_raw_result` returning it is
distinguishable from returning nothing. -/
theorem canonicalResultBuffer_ne_zero : Elfling.canonicalResultBuffer ≠ 0 := by native_decide

/-- **A successful run answers with exactly the value its memory represents.** -/
theorem executeDecode_accepted_of_run (input : ByteArray) (value : SszBridge.RawV4)
    {entry final after : State} {count : Nat}
    (hbuild : Runs (buildZesuEntryState input) initialState entry ())
    (htrace : TraceToSentinel sentinelWord 0 count entry final)
    (hbound : count ≤ entryStepBound input.size + 1)
    (haccessors : Runs (runAccessorsIfReached resolvedSymbols (.reached count)) final after
      (.returned Elfling.canonicalResultBuffer, .returned Contracts.DecodeStatus.ok.code))
    (hcode : observeReturnCode? final = some 1)
    (htag : observeOptionTag? final storedResultDiscriminantAddr = some true)
    (hinput : MemoryBytes final canonicalRunnerLayout.inputBase input)
    (hvalue : RawV4Rep final canonicalRunnerLayout.inputBase input Elfling.canonicalResultBuffer
      value) :
    executeDecode input = .ok (.accepted value) := by
  rw [executeDecode_of_trace input runnerSymbols_eq_resolved hbuild htrace hbound haccessors]
  exact classifyWrapperRun_accepted observeDecodedValue storedResultDiscriminantAddr
    Elfling.canonicalResultBuffer count _ _ final value hcode rfl rfl
    canonicalResultBuffer_ne_zero htag
    (observe_raw_v4_of_rep final canonicalRunnerLayout.inputBase input
      Elfling.canonicalResultBuffer value hinput hvalue)

/-- **A rejected run answers with the normalized rejection.** The status must be one the
specification itself can produce; an exhausted arena or a refused second call cannot reach here. -/
theorem executeDecode_rejected_of_run (input : ByteArray) {entry final after : State}
    {count status : Nat}
    (hbuild : Runs (buildZesuEntryState input) initialState entry ())
    (htrace : TraceToSentinel sentinelWord 0 count entry final)
    (hbound : count ≤ entryStepBound input.size + 1)
    (haccessors : Runs (runAccessorsIfReached resolvedSymbols (.reached count)) final after
      (.returned 0, .returned status))
    (hcode : observeReturnCode? final = some 0)
    (hstatus : statusCategory status = .specRejection)
    (htag : observeOptionTag? final storedResultDiscriminantAddr = some false) :
    executeDecode input = .ok .rejected := by
  rw [executeDecode_of_trace input runnerSymbols_eq_resolved hbuild htrace hbound haccessors]
  exact classifyWrapperRun_rejected observeDecodedValue storedResultDiscriminantAddr
    Elfling.canonicalResultBuffer count status _ _ final hcode rfl hstatus rfl htag

/-! ## The runner never invents a rejection

The classifier's converse lifts to the runner: if `executeDecode` answers `rejected`, then the
machine really reached the sentinel with `a0 = 0`, the executed `zesu_raw_result` really returned
null, the stored-result discriminant really read `absent`, and the executed `zesu_raw_error` really
returned one of the two statuses the specification itself can produce. No trap, exhausted budget,
unreadable return, or exhausted arena can reach this outcome. -/
/-- Inversion for a completed `SailM` bind: if the whole action ran normally, so did its first half,
and the second half ran from where the first left off. The mirror image of `Runs.bind`, which builds
such a run; this one takes one apart. -/
theorem run_bind_inv {α β : Type} {first : SailM α} {next : α → SailM β} {before after : State}
    {result : β} (h : (first >>= next).run before = .ok result after) :
    ∃ value middle, first.run before = .ok value middle ∧
      (next value).run middle = .ok result after := by
  change EStateM.bind first next before = .ok result after at h
  unfold EStateM.bind at h
  match hfirst : first before with
  | .error e s => rw [hfirst] at h; exact absurd h (by simp)
  | .ok value middle => exact ⟨value, middle, hfirst, by rw [hfirst] at h; exact h⟩

/-- **Every completed run answers with a classification.** The runner has exactly one place where a
result is produced, so whatever it returns is a `classifyWrapperRun` of some outcome, some final
state, and the two accessor outcomes. -/
theorem runZesuDecodeRaw_classifies (symbols : RunnerSymbols) (input : ByteArray) {before after : State}
    {result : Except RiscvSpec.ExecutionError DecodeOutcome}
    (h : (runZesuDecodeRaw symbols input).run before = .ok result after) :
    ∃ outcome final rawResult rawError,
      result = classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
        Elfling.canonicalResultBuffer rawResult rawError outcome final := by
  unfold runZesuDecodeRaw at h
  obtain ⟨_, _, _, h⟩ := run_bind_inv h
  obtain ⟨outcome, _, _, h⟩ := run_bind_inv h
  obtain ⟨final, _, _, h⟩ := run_bind_inv h
  obtain ⟨accessors, _, _, h⟩ := run_bind_inv h
  refine ⟨outcome, final, accessors.1, accessors.2, ?_⟩
  injection h with hvalue _
  exact hvalue.symm

/-- The classifier's converse, lifted to the executable entry: an answer of `rejected` really came
from a machine that reached the sentinel with `a0 = 0`, an executed `zesu_raw_result` that returned
null, a stored-result discriminant reading `absent`, and an executed `zesu_raw_error` reporting one
of the two statuses the specification itself can produce. -/
theorem executeDecode_rejected_forces_checks {input : ByteArray}
    (h : executeDecode input = .ok .rejected) :
    ∃ final steps rawResult rawError,
      observeReturnCode? final = some 0 ∧
      rawResult = AccessorOutcome.returned 0 ∧
      observeOptionTag? final storedResultDiscriminantAddr = some false ∧
      (∃ status, rawError = AccessorOutcome.returned status ∧
        statusCategory status = .specRejection) ∧
      classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
        Elfling.canonicalResultBuffer rawResult rawError (.reached steps) final = .ok .rejected := by
  unfold executeDecode at h
  match hsym : runnerSymbols with
  | none => simp only [hsym] at h; exact absurd h (by simp)
  | some symbols =>
    simp only [hsym, runAnswer] at h
    match hrun : (runZesuDecodeRaw symbols input).run initialState with
    | .error e s => simp only [hrun] at h; exact absurd h (by simp)
    | .ok result s =>
      simp only [hrun] at h
      obtain ⟨outcome, final, rawResult, rawError, hresult⟩ :=
        runZesuDecodeRaw_classifies symbols input hrun
      have hclass : classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
          Elfling.canonicalResultBuffer rawResult rawError outcome final = .ok .rejected := by
        rw [← hresult]; exact h
      obtain ⟨⟨steps, hsteps⟩, hcode, ⟨status, herror, hstatus⟩, hnull, htag⟩ :=
        wrapper_rejection_forces_checks hclass
      subst hsteps
      exact ⟨final, steps, rawResult, rawError, hcode, hnull, htag, ⟨status, herror, hstatus⟩,
        hclass⟩

/-- **What the discriminant conjunct and the classification equation add** — an independence witness,
recorded because `Root.execute_rejected_forces_checks` used to drop both of them and the loss was
invisible from reading either statement.

The first bracket is exactly the weaker body that public statement carried: return code `0`, a null
`zesu_raw_result`, and a spec-producible status from `zesu_raw_error`. Those three are satisfied here
by a state whose stored-result discriminant reads **present** — the shape a *refused second call*
leaves behind, since `alreadyDecoded` keeps the previous result in place. So they do not force the
discriminant to read `absent`, and they do not force the run to classify as a rejection at all: on
this state the classifier answers `.error .badReturn`, for every step count.

That is the whole content of the strengthening. A reader given only the weaker three conjuncts could
not rule out this state; a reader given the strengthened statement can, because the last conjunct
*is* the classification. Note the direction the implication runs once the discriminant is restored:
`classifyWrapperRun_rejected` then derives the classification from the checks, so the two added
conjuncts are independent of the old body but not of each other. -/
theorem rejection_checks_without_discriminant_admit_a_non_rejection :
    ∃ (final : State) (rawResult rawError : AccessorOutcome),
      (observeReturnCode? final = some 0 ∧
        rawResult = AccessorOutcome.returned 0 ∧
        (∃ status, rawError = AccessorOutcome.returned status ∧
          statusCategory status = .specRejection)) ∧
      observeOptionTag? final storedResultDiscriminantAddr ≠ some false ∧
      ∀ steps, classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
        Elfling.canonicalResultBuffer rawResult rawError (.reached steps) final
        = .error .badReturn := by
  refine ⟨observedShape 0 storedResultDiscriminantAddr true, .returned 0,
    .returned Contracts.DecodeStatus.invalidSsz.code,
    ⟨by simp, rfl, ⟨_, rfl, by decide⟩⟩, by simp, fun steps => ?_⟩
  unfold classifyWrapperRun
  simp [show statusCategory Contracts.DecodeStatus.invalidSsz.code = .specRejection from by decide]

/-! ## Where each direction is proved

Both directions of both outcomes, by layer. The forward direction says *these checks produce this
answer*; the converse says *this answer could only have come from those checks*, which is what makes
the answer trustworthy rather than merely produced.

| layer                | accepted forward               | accepted converse | rejected forward               | rejected converse                      |
| -------------------- | ------------------------------ | ----------------- | ------------------------------ | -------------------------------------- |
| `classifyWrapperRun` | `classifyWrapperRun_accepted`  | `wrapper_acceptance_forces_checks`     | `classifyWrapperRun_rejected`  | `wrapper_rejection_forces_checks`      |
| `executeDecode`      | `executeDecode_accepted_of_run`| `executeDecode_accepted_forces_checks` | `executeDecode_rejected_of_run`| `executeDecode_rejected_forces_checks` |
| `executeChecked`     | (gate is transparent)          | `executeChecked_accepted_forces_gate`  | (gate is transparent)          | `executeChecked_rejected_forces_gate`  |
| `RiscvSpec.execute`  | `Root.execute_accepts_of_…`    | `Root.execute_accepted_forces_checks`  | `Root.execute_rejects_of_…`    | `Root.execute_rejected_forces_checks`  |

The table is complete, and it is kept because filling it is what found the two gaps it now records
as closed. An empty cell in a grid you are forced to fill is a different object from an absence
nobody happened to look for.

**A filled cell can still be filled with something weaker than its neighbour, which the table does
not show.** `Root.execute_rejected_forces_checks` occupied its cell while carrying strictly less
than `executeDecode_rejected_forces_checks` handed it: the discriminant conjunct and the
classification equation were destructured and dropped. The table said "covered" throughout.
`rejection_checks_without_discriminant_admit_a_non_rejection` above is the missing measurement —
what the cell's *contents* fail to force, as opposed to whether the cell is occupied.

**The trap and malformed-representation paths are not converses and so have no column here.** Their
forward lemmas are `executeDecode_trapped_of_sail_fault` above and
`classifyWrapperRun_malformedResult_of_unobservable` in `Classify.lean`.

**The whole `accepted` converse column was missing.** "The runner never invents a rejection" was a
theorem; "the runner never invents an acceptance, and the value it reports is the one memory
represented" was not. Since `classifyWrapperRun` returns whatever `observeValue final` says, that
converse is what ties the reported value to the observation rather than leaving the tie asserted.

**Both converses stopped one layer below the public API**, which mattered because
`RiscvSpec.execute`'s own docstring makes the "no failure mode becomes a rejection" claim *at the
`execute` level* while the proof reached only `executeDecode`. Neither gap was visible from reading
the rejection proofs, which are correct.

**The converse column carries *less* trust than the forward one, which is the opposite of what a
reader will assume.** The forward lemmas consume `runnerSymbols_isSome` and
`canonicalResultBuffer_ne_zero`, both `native_decide`, so they carry
`Lean.ofReduceBool`/`Lean.trustCompiler`. The converses match on `runnerSymbols` directly and never
need either witness, so all four are `propext`/`Classical.choice`/`Quot.sound` only. The
harder-looking direction is the cleaner one; noted because "the inversion must be at least as
expensive" is the natural and wrong guess.
-/

/-- **The preflight gate cannot manufacture a rejection.** `executeChecked` either returns the gate's
error or defers entirely to `executeDecode`, so a `rejected` answer forces the gate to have passed
*and* the machine run itself to have rejected. The gate contributes only `.invalidArtifact`, so it
can turn an acceptance into an error but never an error into an acceptance or a rejection. -/
theorem executeChecked_rejected_forces_gate {binary : RiscvSpec.ValidatedElf} {input : ByteArray}
    (h : executeChecked binary input = .ok .rejected) :
    preflight binary input = .ok () ∧ executeDecode input = .ok .rejected := by
  unfold executeChecked at h
  match hp : preflight binary input with
  | .error e => rw [hp] at h; exact absurd h (by simp)
  | .ok u =>
      rw [hp] at h
      exact ⟨by cases u; rfl, h⟩

/-- **The acceptance converse, lifted to the executable entry.** An `accepted value` answer really
came from a machine that reached the sentinel with `a0 = 1`, an executed `zesu_raw_error` reporting
`ok`, an executed `zesu_raw_result` returning the canonical non-null buffer, a discriminant reading
`present` — and, the conjunct that matters, an observation of **that same value**. -/
theorem executeDecode_accepted_forces_checks {input : ByteArray} {value : SszBridge.RawV4}
    (h : executeDecode input = .ok (.accepted value)) :
    ∃ (final : State) (steps : Nat) (rawResult rawError : AccessorOutcome),
      observeReturnCode? final = some 1 ∧
      rawError = AccessorOutcome.returned Contracts.DecodeStatus.ok.code ∧
      rawResult = AccessorOutcome.returned Elfling.canonicalResultBuffer ∧
      observeOptionTag? final storedResultDiscriminantAddr = some true ∧
      observeDecodedValue final = some value ∧
      classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
        Elfling.canonicalResultBuffer rawResult rawError (.reached steps) final
        = .ok (.accepted value) := by
  unfold executeDecode at h
  match hsym : runnerSymbols with
  | none => simp only [hsym] at h; exact absurd h (by simp)
  | some symbols =>
    simp only [hsym, runAnswer] at h
    match hrun : (runZesuDecodeRaw symbols input).run initialState with
    | .error e s => simp only [hrun] at h; exact absurd h (by simp)
    | .ok result s =>
      simp only [hrun] at h
      obtain ⟨outcome, final, rawResult, rawError, hresult⟩ :=
        runZesuDecodeRaw_classifies symbols input hrun
      have hclass : classifyWrapperRun observeDecodedValue storedResultDiscriminantAddr
          Elfling.canonicalResultBuffer rawResult rawError outcome final
          = .ok (.accepted value) := by
        rw [← hresult]; exact h
      obtain ⟨⟨steps, hsteps⟩, hcode, herror, hnull, -, htag, hvalue⟩ := wrapper_acceptance_forces_checks hclass
      subst hsteps
      exact ⟨final, steps, rawResult, rawError, hcode, herror, hnull, htag, hvalue, hclass⟩

/-- **The preflight gate cannot manufacture an acceptance either.** Same two-way match as the
rejection version; the gate contributes only `.invalidArtifact`. -/
theorem executeChecked_accepted_forces_gate {binary : RiscvSpec.ValidatedElf} {input : ByteArray}
    {value : SszBridge.RawV4} (h : executeChecked binary input = .ok (.accepted value)) :
    preflight binary input = .ok () ∧ executeDecode input = .ok (.accepted value) := by
  unfold executeChecked at h
  match hp : preflight binary input with
  | .error e => rw [hp] at h; exact absurd h (by simp)
  | .ok u => rw [hp] at h; exact ⟨by cases u; rfl, h⟩

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
