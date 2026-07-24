import BinaryFv.RiscV.Execution.Runner
import BinaryFv.SSZ.Zesu.ExecutionTypes
import BinaryFv.SSZ.Zesu.MemoryRepresentation.Result
import BinaryFv.SSZ.Zesu.MemoryRepresentation.Observers
import BinaryFv.SSZ.Zesu.Contracts.Entry

/-!
# Classifying a finished decoder run

After the machine runs to the return sentinel, the runner has to turn what it sees into either a
public `DecodeOutcome` or a *specific* `ExecutionError`. The point of this module is that the four
ways a run can fail stay apart: running out of fuel, stalling, returning a code that is not `0` or
`1`, and returning a well-formed code whose result memory does not parse are all different errors.
None of them is allowed to quietly become `rejected` — a rejection is only ever reported when the
decoder actually said "rejected" by returning `0` with a nonzero status word.

The observation of the accepted `RawV4` value is a *parameter* (`observeValue`) rather than a fixed
function. That keeps this classification independent of the value observer: everything here — the
outcome mapping, the return-code dispatch, and the rejected path — is settled now, and the accepted
path is proved conditionally on whatever observer is supplied.

Two classifiers live here, one per result convention:

* `classifyRun` reads the 16-bit status word of the *internal* Zesu result object
  (`observeResultStatus?`, status `0` = success). That is the convention of the trace witnesses in
  `Execution.lean`; it stays until those witnesses are rewritten against the wrapper globals (a D3
  item).
* `classifyWrapperRun` speaks the *exported wrapper's* convention: `last_status` is a
  `DecodeStatus` code (`1` = ok, `2`–`4` = the documented rejections), the stored result is an
  inline optional whose discriminant sits after its 832-byte payload, and — decisively — the two
  exported accessors `zesu_raw_result`/`zesu_raw_error` are actually *executed* from the post-call
  state, so their checked returns are part of the classification rather than a re-read of the same
  memory. This is the classifier the real `RiscvSpec.execute` uses.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-- The C-ABI return code the callee left in `a0`. -/
def observeReturnCode? (state : State) : Option Nat :=
  (state.regs.get? x10).map (fun word => word.toNat)

/-- Turn a finished sentinel run into the public outcome or a distinct `ExecutionError`.

The two consistency checks are deliberate: a `1` (accepted) must come with a zero status word, and a
`0` (rejected) must come with a *nonzero* one. A code and a status word that disagree indicate the
result object is not what the ABI documents, so that is `badReturn`, not a rejection. -/
def classifyRun (observeValue : State → Option SszBridge.RawV4) (resultBase : Nat)
    (outcome : SentinelOutcome) (final : State) : Except RiscvSpec.ExecutionError DecodeOutcome :=
  match outcome with
  | .exhausted => .error .fuelExhausted
  | .trapped => .error .trapped
  | .reached _ =>
    match observeReturnCode? final with
    | none => .error .badReturn
    | some 1 =>
      match observeResultStatus? final resultBase with
      | none => .error .malformedResult
      | some 0 =>
        match observeValue final with
        | some value => .ok (.accepted value)
        | none => .error .malformedResult
      | some _ => .error .badReturn
    | some 0 =>
      match observeResultStatus? final resultBase with
      | none => .error .malformedResult
      | some 0 => .error .badReturn
      | some _ => .ok .rejected
    | some _ => .error .badReturn

/-! ## The failure modes stay distinct -/

/-- Fuel exhaustion is reported as itself, never as a rejection. -/
@[simp] theorem classifyRun_exhausted (observeValue : State → Option SszBridge.RawV4)
    (resultBase : Nat) (final : State) :
    classifyRun observeValue resultBase .exhausted final = .error .fuelExhausted := rfl

/-- A stalled machine is reported as a trap, never as a rejection. -/
@[simp] theorem classifyRun_trapped (observeValue : State → Option SszBridge.RawV4)
    (resultBase : Nat) (final : State) :
    classifyRun observeValue resultBase .trapped final = .error .trapped := rfl

/-- A return code outside `{0, 1}` is a `badReturn`, not a rejection. -/
theorem classifyRun_badReturn_of_other_code (observeValue : State → Option SszBridge.RawV4)
    (resultBase steps code : Nat) (final : State)
    (hcode : observeReturnCode? final = some code) (hne0 : code ≠ 0) (hne1 : code ≠ 1) :
    classifyRun observeValue resultBase (.reached steps) final = .error .badReturn := by
  unfold classifyRun
  rw [hcode]
  match code, hne0, hne1 with
  | 0, h, _ => exact absurd rfl h
  | 1, _, h => exact absurd rfl h
  | (n + 2), _, _ => rfl

/-- No failure mode is ever reported as `rejected`: a `rejected` outcome forces the run to have
reached the sentinel with return code `0` and a nonzero status word. This is the "do not collapse
into rejection" property, stated as a converse. -/
theorem reached_zero_of_classifyRun_rejected {observeValue : State → Option SszBridge.RawV4}
    {resultBase : Nat} {outcome : SentinelOutcome} {final : State}
    (h : classifyRun observeValue resultBase outcome final = .ok .rejected) :
    (∃ steps, outcome = .reached steps) ∧ observeReturnCode? final = some 0 ∧
      ∃ status, observeResultStatus? final resultBase = some status ∧ status ≠ 0 := by
  unfold classifyRun at h
  match outcome with
  | .exhausted => exact absurd h (by simp)
  | .trapped => exact absurd h (by simp)
  | .reached steps =>
    simp only at h
    match hcode : observeReturnCode? final with
    | none => rw [hcode] at h; exact absurd h (by simp)
    | some 0 =>
      rw [hcode] at h
      match hst : observeResultStatus? final resultBase with
      | none => rw [hst] at h; exact absurd h (by simp)
      | some 0 => rw [hst] at h; exact absurd h (by simp)
      | some (n + 1) =>
        -- the two `match … with` generalizations already rewrote the goal's observations
        exact ⟨⟨steps, rfl⟩, rfl, n + 1, rfl, by omega⟩
    | some 1 =>
      rw [hcode] at h
      match hst : observeResultStatus? final resultBase with
      | none => rw [hst] at h; exact absurd h (by simp)
      | some 0 =>
        rw [hst] at h
        match hv : observeValue final with
        | none => rw [hv] at h; exact absurd h (by simp)
        | some v => rw [hv] at h; exact absurd h (by simp)
      | some (n + 1) => rw [hst] at h; exact absurd h (by simp)
    | some (n + 2) => rw [hcode] at h; exact absurd h (by simp)

/-! ## The two success paths -/

/-- A run that returned `0` with a nonzero status is the rejection. -/
theorem classifyRun_rejected (observeValue : State → Option SszBridge.RawV4)
    (resultBase steps status : Nat) (final : State)
    (hcode : observeReturnCode? final = some 0)
    (hstatus : observeResultStatus? final resultBase = some status) (hne : status ≠ 0) :
    classifyRun observeValue resultBase (.reached steps) final = .ok .rejected := by
  unfold classifyRun
  rw [hcode, hstatus]
  match status, hne with
  | (n + 1), _ => rfl

/-- A run that returned `1` over a well-formed success result yields exactly the observed value. The
zero status word comes from the representation itself (`observe_raw_v4_success_status`), so only the
value observer has to agree with the representation. -/
theorem classifyRun_accepted (observeValue : State → Option SszBridge.RawV4)
    (resultBase steps inputBase : Nat) (input : ByteArray) (final : State)
    (value : SszBridge.RawV4)
    (hcode : observeReturnCode? final = some 1)
    (hresult : RawV4SuccessResultRep final inputBase input resultBase value)
    (hobserve : observeValue final = some value) :
    classifyRun observeValue resultBase (.reached steps) final = .ok (.accepted value) := by
  unfold classifyRun
  rw [hcode, observe_raw_v4_success_status final inputBase input resultBase value hresult, hobserve]

/-! ## The wrapper classifier

The exported wrapper records its result in the three private globals, and its two exported
accessors are real code the runner can execute. `classifyWrapperRun` therefore takes, besides the
main run's outcome, the outcome of actually *running* `zesu_raw_result` and `zesu_raw_error` from
the post-call state. An accessor that traps, exhausts its (contract-derived) fuel, or comes back
without a readable `a0` keeps its own distinct error; a return that disagrees with the wrapper's
`a0` code is `badReturn` or `malformedResult`, never a rejection.
-/

open BinaryFv.SSZ.Zesu.Contracts (DecodeStatus)

/-- How one executed accessor call ended: it reached the return sentinel with a readable `a0`, or
one of the distinct failure modes. Produced by the runner's `runAccessor`; consumed here. -/
inductive AccessorOutcome where
  | returned (a0 : Nat)
  | trapped
  | exhausted
  | noReturn
  deriving DecidableEq, Repr

/-- Map an accessor's own failure onto the runner error it names. Only non-`returned` outcomes. -/
@[simp] def AccessorOutcome.failureError : AccessorOutcome → RiscvSpec.ExecutionError
  | .returned _ => .badReturn
  | .trapped => .trapped
  | .exhausted => .fuelExhausted
  | .noReturn => .badReturn

/-- What a status recorded alongside a `0` return means for the runner. -/
inductive StatusCategory where
  /-- One of the two statuses the pure specification can produce: the run really was a rejection. -/
  | specRejection
  /-- The decoder ran out of arena. Not a rejection — see `statusCategory`. -/
  | arenaExhausted
  /-- A status a completed fresh call does not produce. -/
  | undocumented
  deriving DecidableEq, Repr

/-- Categorize a recorded status.

Only `invalidSsz` and `unknownFork` — the two `statusOfResult` can produce — are rejections. An
allocator exhaustion is deliberately not one: `SszSpec.decode` is a total function with no
out-of-memory outcome, so answering `rejected` for an exhausted arena could contradict a spec
*acceptance*. `notRun`, `ok`, and `alreadyDecoded` are undocumented for a completed fresh call;
`alreadyDecoded` in particular is what a **second** call records, which is not a decode result at
all. -/
def statusCategory (status : Nat) : StatusCategory :=
  if status = DecodeStatus.invalidSsz.code ∨ status = DecodeStatus.unknownFork.code then
    .specRejection
  else if status = DecodeStatus.outOfMemory.code then
    .arenaExhausted
  else
    .undocumented

/-- The categories of the five statuses the wrapper can record, pinned so that a change to
`DecodeStatus.code` or to the categorization is visible here. -/
theorem statusCategory_pinned :
    statusCategory DecodeStatus.invalidSsz.code = .specRejection ∧
      statusCategory DecodeStatus.unknownFork.code = .specRejection ∧
      statusCategory DecodeStatus.outOfMemory.code = .arenaExhausted ∧
      statusCategory DecodeStatus.alreadyDecoded.code = .undocumented ∧
      statusCategory DecodeStatus.ok.code = .undocumented ∧
      statusCategory DecodeStatus.notRun.code = .undocumented := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Turn a finished wrapper run into the public outcome or a distinct `ExecutionError`, requiring
the executed accessors to agree with the wrapper's return code.

* Return `1`: `zesu_raw_error` must have returned the `ok` code, `zesu_raw_result` must have
  returned the canonical non-null result buffer, the stored-result discriminant must read `present`,
  and the value observer must succeed — then the outcome is that value.
* Return `0`: the recorded status decides the category first. Only a spec-producible rejection
  status can become `rejected`, and only after `zesu_raw_result` returned null and the discriminant
  read `absent`. An exhausted arena is `outOfMemory`; any other status — including the
  `alreadyDecoded` a *second* call records — is `badReturn`.

Anything else keeps a specific error: fuel exhaustion and stalls (of the main run *or* an accessor
run) stay themselves, an undocumented status or an unreadable/other return code is `badReturn`, and
a wrong result pointer, wrong discriminant, or failed value observation is `malformedResult`. -/
def classifyWrapperRun (observeValue : State → Option SszBridge.RawV4)
    (discriminantAddr resultBase : Nat) (rawResult rawError : AccessorOutcome)
    (outcome : SentinelOutcome) (final : State) : Except RiscvSpec.ExecutionError DecodeOutcome :=
  match outcome with
  | .exhausted => .error .fuelExhausted
  | .trapped => .error .trapped
  | .reached _ =>
    match observeReturnCode? final with
    | none => .error .badReturn
    | some 1 =>
      match rawError with
      | .returned status =>
        if status = DecodeStatus.ok.code then
          match rawResult with
          | .returned pointer =>
            if pointer = resultBase ∧ pointer ≠ 0 then
              match observeOptionTag? final discriminantAddr with
              | some true =>
                match observeValue final with
                | some value => .ok (.accepted value)
                | none => .error .malformedResult
              | some false => .error .malformedResult
              | none => .error .malformedResult
            else .error .malformedResult
          | failure => .error failure.failureError
        else .error .badReturn
      | failure => .error failure.failureError
    | some 0 =>
      match rawError with
      | .returned status =>
        match statusCategory status with
        | .specRejection =>
          match rawResult with
          | .returned 0 =>
            match observeOptionTag? final discriminantAddr with
            | some false => .ok .rejected
            | some true => .error .badReturn
            | none => .error .malformedResult
          | .returned _ => .error .malformedResult
          | failure => .error failure.failureError
        | .arenaExhausted => .error .outOfMemory
        | .undocumented => .error .badReturn
      | failure => .error failure.failureError
    | some _ => .error .badReturn

/-! ### The wrapper failure modes stay distinct -/

/-- Fuel exhaustion is reported as itself, never as a rejection. -/
@[simp] theorem classifyWrapperRun_exhausted (observeValue : State → Option SszBridge.RawV4)
    (discriminantAddr resultBase : Nat) (rawResult rawError : AccessorOutcome) (final : State) :
    classifyWrapperRun observeValue discriminantAddr resultBase rawResult rawError
      .exhausted final = .error .fuelExhausted := rfl

/-- A stalled machine is reported as a trap, never as a rejection. -/
@[simp] theorem classifyWrapperRun_trapped (observeValue : State → Option SszBridge.RawV4)
    (discriminantAddr resultBase : Nat) (rawResult rawError : AccessorOutcome) (final : State) :
    classifyWrapperRun observeValue discriminantAddr resultBase rawResult rawError
      .trapped final = .error .trapped := rfl

/-- A return code outside `{0, 1}` is a `badReturn`, not a rejection, whatever the accessors did. -/
theorem classifyWrapperRun_badReturn_of_other_code (observeValue : State → Option SszBridge.RawV4)
    (discriminantAddr resultBase steps code : Nat) (rawResult rawError : AccessorOutcome)
    (final : State) (hcode : observeReturnCode? final = some code) (hne0 : code ≠ 0)
    (hne1 : code ≠ 1) :
    classifyWrapperRun observeValue discriminantAddr resultBase rawResult rawError
      (.reached steps) final = .error .badReturn := by
  unfold classifyWrapperRun
  rw [hcode]
  match code, hne0, hne1 with
  | 0, h, _ => exact absurd rfl h
  | 1, _, h => exact absurd rfl h
  | (n + 2), _, _ => rfl

/-- No failure mode is ever reported as `rejected`: a `rejected` outcome forces the run to have
reached the sentinel with return code `0`, the *executed* `zesu_raw_result` to have returned null,
the stored-result discriminant to read `absent`, and the *executed* `zesu_raw_error` to have
returned one of the two statuses the specification itself can produce — so an exhausted arena, a
trap, an unreadable return, or a stale stored result cannot arrive here. -/
theorem wrapper_rejection_forces_checks {observeValue : State → Option SszBridge.RawV4}
    {discriminantAddr resultBase : Nat} {rawResult rawError : AccessorOutcome}
    {outcome : SentinelOutcome} {final : State}
    (h : classifyWrapperRun observeValue discriminantAddr resultBase rawResult rawError
      outcome final = .ok .rejected) :
    (∃ steps, outcome = .reached steps) ∧ observeReturnCode? final = some 0 ∧
      (∃ status, rawError = .returned status ∧ statusCategory status = .specRejection) ∧
      rawResult = .returned 0 ∧
      observeOptionTag? final discriminantAddr = some false := by
  unfold classifyWrapperRun at h
  match outcome with
  | .exhausted => exact absurd h (by simp)
  | .trapped => exact absurd h (by simp)
  | .reached steps =>
    simp only at h
    match hcode : observeReturnCode? final with
    | none => rw [hcode] at h; exact absurd h (by simp)
    | some 0 =>
      rw [hcode] at h
      match rawError with
      | .returned status =>
        match hcat : statusCategory status with
        | .specRejection =>
          simp only [hcat] at h
          match rawResult with
          | .returned 0 =>
            match htag : observeOptionTag? final discriminantAddr with
            | some false => exact ⟨⟨steps, rfl⟩, rfl, ⟨status, rfl, hcat⟩, rfl, rfl⟩
            | some true => rw [htag] at h; exact absurd h (by simp)
            | none => rw [htag] at h; exact absurd h (by simp)
          | .returned (n + 1) => exact absurd h (by simp)
          | .trapped => exact absurd h (by simp)
          | .exhausted => exact absurd h (by simp)
          | .noReturn => exact absurd h (by simp)
        | .arenaExhausted => exact absurd h (by simp [hcat])
        | .undocumented => exact absurd h (by simp [hcat])
      | .trapped => exact absurd h (by simp)
      | .exhausted => exact absurd h (by simp)
      | .noReturn => exact absurd h (by simp)
    | some 1 =>
      rw [hcode] at h
      match rawError with
      | .returned status =>
        by_cases hstatus : status = DecodeStatus.ok.code
        · simp [hstatus] at h
          match rawResult with
          | .returned pointer =>
            by_cases hptr : pointer = resultBase ∧ pointer ≠ 0
            · simp [hptr] at h
              match htag : observeOptionTag? final discriminantAddr with
              | some true =>
                rw [htag] at h
                match hv : observeValue final with
                | some v =>
                  rw [hv] at h
                  have hnonnull : resultBase ≠ 0 := by omega
                  simp [hnonnull] at h
                | none => rw [hv] at h; exact absurd h (by simp)
              | some false => rw [htag] at h; exact absurd h (by simp)
              | none => rw [htag] at h; exact absurd h (by simp)
            · simp [hptr] at h
          | .trapped => exact absurd h (by simp)
          | .exhausted => exact absurd h (by simp)
          | .noReturn => exact absurd h (by simp)
        · simp [hstatus] at h
      | .trapped => exact absurd h (by simp)
      | .exhausted => exact absurd h (by simp)
      | .noReturn => exact absurd h (by simp)
    | some (n + 2) => rw [hcode] at h; exact absurd h (by simp)

/-! ### The two success paths -/

/-- A run that returned `1`, whose executed accessors returned the `ok` code and the canonical
non-null buffer, whose discriminant reads `present`, and whose value observes, is the acceptance of
exactly the observed value. -/
theorem classifyWrapperRun_accepted (observeValue : State → Option SszBridge.RawV4)
    (discriminantAddr resultBase steps : Nat) (rawResult rawError : AccessorOutcome)
    (final : State) (value : SszBridge.RawV4)
    (hcode : observeReturnCode? final = some 1)
    (herror : rawError = AccessorOutcome.returned DecodeStatus.ok.code)
    (hresult : rawResult = AccessorOutcome.returned resultBase) (hnonnull : resultBase ≠ 0)
    (htag : observeOptionTag? final discriminantAddr = some true)
    (hobserve : observeValue final = some value) :
    classifyWrapperRun observeValue discriminantAddr resultBase rawResult rawError
      (.reached steps) final = .ok (.accepted value) := by
  unfold classifyWrapperRun
  rw [hcode, herror, hresult]
  simp [hnonnull, htag, hobserve]

/-- A run that returned `0`, whose executed `zesu_raw_error` returned a spec-producible rejection
status, whose executed `zesu_raw_result` returned null, and whose discriminant reads `absent`, is
the normalized rejection. -/
theorem classifyWrapperRun_rejected (observeValue : State → Option SszBridge.RawV4)
    (discriminantAddr resultBase steps status : Nat) (rawResult rawError : AccessorOutcome)
    (final : State)
    (hcode : observeReturnCode? final = some 0)
    (herror : rawError = AccessorOutcome.returned status)
    (hstatus : statusCategory status = .specRejection)
    (hresult : rawResult = AccessorOutcome.returned 0)
    (htag : observeOptionTag? final discriminantAddr = some false) :
    classifyWrapperRun observeValue discriminantAddr resultBase rawResult rawError
      (.reached steps) final = .ok .rejected := by
  unfold classifyWrapperRun
  rw [hcode, herror, hresult]
  simp [hstatus, htag]

/-- **An exhausted arena is reported as `outOfMemory`, not as a rejection.** The status alone
settles it: whatever the result slot looks like, an implementation-level exhaustion stays
distinguishable from the spec rejection it superficially resembles. -/
theorem classifyWrapperRun_outOfMemory (observeValue : State → Option SszBridge.RawV4)
    (discriminantAddr resultBase steps : Nat) (rawResult rawError : AccessorOutcome)
    (final : State)
    (hcode : observeReturnCode? final = some 0)
    (herror : rawError = AccessorOutcome.returned DecodeStatus.outOfMemory.code) :
    classifyWrapperRun observeValue discriminantAddr resultBase rawResult rawError
      (.reached steps) final = .error .outOfMemory := by
  unfold classifyWrapperRun
  rw [hcode, herror]
  simp [show statusCategory DecodeStatus.outOfMemory.code = .arenaExhausted by decide]

/-- **A refused second call is `badReturn`, never a rejection.** Once `attempted` is set the wrapper
returns `0` and records `alreadyDecoded` while its stored result stays present — the same `0` a real
rejection returns. The status is what tells them apart, which is why it is dispatched before the
result slot is inspected. -/
theorem classifyWrapperRun_alreadyDecoded (observeValue : State → Option SszBridge.RawV4)
    (discriminantAddr resultBase steps : Nat) (rawResult rawError : AccessorOutcome)
    (final : State)
    (hcode : observeReturnCode? final = some 0)
    (herror : rawError = AccessorOutcome.returned DecodeStatus.alreadyDecoded.code) :
    classifyWrapperRun observeValue discriminantAddr resultBase rawResult rawError
      (.reached steps) final = .error .badReturn := by
  unfold classifyWrapperRun
  rw [hcode, herror]
  simp [show statusCategory DecodeStatus.alreadyDecoded.code = .undocumented by decide]

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
