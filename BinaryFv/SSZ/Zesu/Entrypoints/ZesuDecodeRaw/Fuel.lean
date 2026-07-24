import BinaryFv.SSZ.Zesu.Contracts.CanonicalParams
import BinaryFv.SSZ.Zesu.Contracts.ExportedDecoder
import BinaryFv.SSZ.Zesu.Runtime.AllocationBound

/-!
# Deriving the runner's step budgets

The exported function instance contract already bounds the complete composed decode, including summarized
callees. The executable runner uses that same bound plus two steps: one to retire the final return
into the sentinel and one to make the inequality strict.

This file proves that the resulting fuel is positive, exceeds the contract bound, and remains below
the 64-bit step-counter limit for every input covered by the theorem.

The two exported accessors get their budgets the same way, from *their* contracts
(`contractRawResult`, `contractRawError`) rather than from literals here, so a contract whose step
bound changes moves the runner's fuel with it.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.SSZ.Zesu

/-- The exported wrapper's function instance step bound, as a function of the input size. Kept in one place
so the fuel is derived from it rather than from a separate literal. Matches
`functionInstanceZesuDecodeRaw`'s `stepBound`. -/
def entryStepBound (inputSize : Nat) : Nat := 2 * (16384 + 512 * inputSize) + 1024

/-- The runner's fuel: the entry step bound plus two — one slack step to retire the return that lands
on the sentinel, and one to make the budget *strictly* exceed the composed trace length. -/
def zesuFuel (inputSize : Nat) : Nat := entryStepBound inputSize + 2

/-- The fuel is positive, so `runToSentinel` never immediately exhausts. -/
theorem zesuFuel_pos (inputSize : Nat) : 0 < zesuFuel inputSize := by
  unfold zesuFuel entryStepBound; omega

/-- For an admissible input the fuel cannot wrap a 64-bit counter, so the step numbering stays exact.
`maximumInputBytes` is `2 MiB`, and `2 * (16384 + 512 * 2^21) + 1024 + 2` is far below `2^64`. -/
theorem zesuFuel_no_wrap {inputSize : Nat} (h : inputSize < Runtime.maximumInputBytes) :
    zesuFuel inputSize < 2 ^ 64 := by
  unfold zesuFuel entryStepBound
  have : inputSize < 2 * 1024 * 1024 := h
  omega

/-- The fuel strictly exceeds the entry step bound, so any entered trace within that bound has
`count < zesuFuel` — the exact premise `runToSentinel_of_traceToSentinel` requires. -/
theorem zesuFuel_exceeds_bound (inputSize : Nat) : entryStepBound inputSize < zesuFuel inputSize := by
  unfold zesuFuel; omega

/-- Consequently, any trace whose length is bounded by the entry step bound fits within the fuel. -/
theorem count_lt_zesuFuel {inputSize count : Nat} (h : count ≤ entryStepBound inputSize) :
    count < zesuFuel inputSize :=
  Nat.lt_of_le_of_lt h (zesuFuel_exceeds_bound inputSize)

/-! ## The exported accessors' budgets

Same construction, one level down: each accessor's fuel is its own contract's step bound plus the
same two slack steps. The bounds are *read from the contracts*, so there is no second literal to
drift. -/

open BinaryFv.SSZ.Zesu.Contracts in
/-- `zesu_raw_result`'s step bound, taken from `contractRawResult` at the canonical parameters. Its
`Args` is the ghost globals model, which the bound does not depend on. -/
def rawResultStepBound : Nat :=
  (contractRawResult canonicalEnvironment Elfling.canonicalDecoderGlobalsLayout
    Elfling.canonicalResultBuffer).stepBound DecoderGlobalsModel.fresh

open BinaryFv.SSZ.Zesu.Contracts in
/-- `zesu_raw_error`'s step bound, taken from `contractRawError` at the canonical parameters. -/
def rawErrorStepBound : Nat :=
  (contractRawError canonicalEnvironment Elfling.canonicalDecoderGlobalsLayout).stepBound
    DecoderGlobalsModel.fresh

/-- An accessor's fuel: its contract bound plus the same two slack steps as the main run. -/
def accessorFuel (stepBound : Nat) : Nat := stepBound + 2

/-- Both accessor budgets are positive, so neither immediately exhausts. -/
theorem accessorFuel_pos (stepBound : Nat) : 0 < accessorFuel stepBound := by
  unfold accessorFuel; omega

/-- Each accessor's fuel strictly exceeds its contract bound, so a call that respects its contract
always reaches the sentinel within budget. -/
theorem accessorFuel_exceeds_bound (stepBound : Nat) : stepBound < accessorFuel stepBound := by
  unfold accessorFuel; omega

/-- The accessors' bounds are the contracts' `32` and `16` — recorded so a contract edit that
changes them is visible here rather than silently retuning the runner. -/
theorem accessor_step_bounds : rawResultStepBound = 32 ∧ rawErrorStepBound = 16 := by
  constructor <;> rfl

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
