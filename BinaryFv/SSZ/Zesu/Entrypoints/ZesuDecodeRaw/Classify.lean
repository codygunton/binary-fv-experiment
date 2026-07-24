import BinaryFv.RiscV.Execution.Runner
import BinaryFv.SSZ.Zesu.Interface
import BinaryFv.SSZ.Zesu.MemoryRepresentation.Result

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

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
