import BinaryFv.SSZ.Zesu.Contracts.Entry
import BinaryFv.SSZ.Zesu.Validation.GeneratedCorpus

/-!
# Kernel-checked meaning/oracle agreement (Row B)

The Row B validation of the **handwritten `meaning` definitions**: for every small
`ssz-contract-corpus-v1` case, the source-shaped `meaningDecode` and the pinned oracle
`SszBridge.decodeStatelessInput` agree on acceptance, and each matches the case's expected
classification — checked in the kernel by `native_decide`.

This is `Entry.sourceShapedDecodeAgreesWithOracle` realized on the corpus, and it is *stronger* than a
runtime JSONL cross-check: it is a proof for these inputs. It is a validation module — falsification
evidence, not a proof premise — and is not imported by the theorem umbrella `BinaryFv`.
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
  while h : i + 1 < cs.size do
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
