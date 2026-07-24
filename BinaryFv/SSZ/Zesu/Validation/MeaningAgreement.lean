import BinaryFv.SSZ.Zesu.Contracts.Entry
import BinaryFv.SSZ.Zesu.Validation.GeneratedCorpus

/-!
# Checking the composed Lean meaning against the oracle

For each small whole-input corpus case, this module evaluates both the handwritten `meaningDecode`
and the independent `SszBridge.decodeStatelessInput` oracle. `native_decide` checks that they agree on
acceptance and that both match the expected classification.

These are proofs about the finite corpus, not a universal decoder theorem. They provide strong
regression evidence while remaining outside the compliance theorem's import graph.
-/

namespace BinaryFv.SSZ.Zesu.Validation

open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Validation.GeneratedCorpus

/-- A single hex digit's value (`16` for a non-digit, which `hexToBytes` never receives). -/
def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then 10 + (c.toNat - 'a'.toNat)
  else 16

/-- Decode a hex string to bytes. Iterative, so a multi-kilobyte case runs without deep recursion. -/
def hexToBytes (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  let mut i := 0
  while _h : i + 1 < cs.size do
    out := out.push (UInt8.ofNat (hexVal cs[i]! * 16 + hexVal cs[i + 1]!))
    i := i + 2
  return out

/-- Whether the pinned oracle accepts an input. -/
def oracleAccepts (input : ByteArray) : Bool :=
  match SszBridge.decodeStatelessInput input with
  | .ok _ => true
  | .error _ => false

/-- The handwritten `meaningDecode` and the pinned oracle agree on acceptance for every small corpus
case. -/
def meaningAgreesWithOracle : Bool :=
  corpus.all fun c =>
    let input := hexToBytes c.2.2
    isAccepted (meaningDecode input) == oracleAccepts input

/-- **Meaning ≈ oracle on the corpus.** Kernel-checked. -/
theorem meaning_agrees_with_oracle : meaningAgreesWithOracle = true := by native_decide

/-- Each handwritten-meaning outcome matches the corpus's expected accept/reject classification. -/
def meaningMatchesExpected : Bool :=
  corpus.all fun c => isAccepted (meaningDecode (hexToBytes c.2.2)) == c.2.1

/-- **Meaning matches the expected classification on the corpus.** Kernel-checked. -/
theorem meaning_matches_expected : meaningMatchesExpected = true := by native_decide

end BinaryFv.SSZ.Zesu.Validation
