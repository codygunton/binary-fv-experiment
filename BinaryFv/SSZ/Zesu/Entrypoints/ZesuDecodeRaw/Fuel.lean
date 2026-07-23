import BinaryFv.SSZ.Zesu.Contracts.ExportedDecoder
import BinaryFv.SSZ.Zesu.Runtime.AllocationBound

/-!
# The runner's fuel

`runToSentinel` needs a step budget strictly larger than the composed trace it must complete. The
exported wrapper's occurrence contract bounds its own entered trace by
`stepBound args = 2 * (16384 + 512 * input.size) + 1024`, and the whole decode *is* that one entered
trace (every callee is spliced into it), so a fuel strictly above that bound suffices for the
`count < fuel` premise of `runToSentinel_of_traceToSentinel`, with one extra step for retiring the
final return that lands on the sentinel.

The fuel is therefore derived from the contract's own bound plus a fixed `+2`, not an unexplained
numeric constant, and every fact the runner needs about it — positive, non-wrapping for admissible
inputs, and strictly exceeding the entry bound — is proved here.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.SSZ.Zesu

/-- The exported wrapper's occurrence step bound, as a function of the input size. Kept in one place
so the fuel is derived from it rather than from a separate literal. Matches
`occurrenceZesuDecodeRaw`'s `stepBound`. -/
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

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
