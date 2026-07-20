import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Artifact.AbiManifest
import BinaryFv.SSZ.Zesu.Interface

namespace BinaryFv.SSZ

open BinaryFv.RiscV

/-- The one canonical, Nix-built Zesu executable covered by the SSZ proof. -/
noncomputable def binary : RiscvSpec.ValidatedElf := {
  bytes := Zesu.Artifact.bytes
  elf := Zesu.Artifact.elf
  parsed_ok := by exact Zesu.Artifact.parsed_ok
  layout := Zesu.Artifact.elf_layout
}

/-- Closed artifact facts needed before the semantic execution proof starts.  Instruction
inventories and block-specific ELF facts remain in their owning analysis files and will be consumed
by the accepted/rejected execution proofs below. -/
structure StaticEvidence : Prop where
  rawResultLayout :
    Zesu.Artifact.rawStatelessInputSize = some 832 ∧
      Zesu.Artifact.rawStatelessInputChainConfigOffset = some 736

/-- The pinned ELF and compiler-reflected result ABI satisfy the static prerequisites for execution
refinement. -/
theorem static_evidence : StaticEvidence where
  rawResultLayout := by
    exact ⟨Zesu.Artifact.raw_stateless_input_layout.1,
      Zesu.Artifact.raw_stateless_input_layout.2.2.2.2.1⟩

/-- Authorized north-star obligation for the successful decoder path.

The eventual proof starts from the public ABI state, composes the live Sail trace through
`zesu_decode_raw`, constructs `RawV4SuccessResultRep` for `value`, and connects every decoded field
to the corresponding SizzLean operation on `input`. -/
theorem execute_accepts_of_spec_accepts (evidence : StaticEvidence) (input : ByteArray)
    (inputBound : input.size < 2 * 1024 * 1024) (value : SszBridge.RawV4)
    (specAccepts : SszSpec.decode input = .accepted value) :
    RiscvSpec.execute binary input = .ok (.accepted value) := by
  sorry

/-- Authorized north-star obligation for every normalized decoder rejection path.

The eventual proof classifies the reachable failure returns of `zesu_decode_raw` and shows that
each corresponds to the single observable SizzLean outcome `DecodeOutcome.rejected`. -/
theorem execute_rejects_of_spec_rejects (evidence : StaticEvidence) (input : ByteArray)
    (inputBound : input.size < 2 * 1024 * 1024)
    (specRejects : SszSpec.decode input = .rejected) :
    RiscvSpec.execute binary input = .ok .rejected := by
  sorry

/-- Successful and rejected execution paths together refine the complete observable SSZ spec. -/
theorem execute_matches_spec (input : ByteArray) (inputBound : input.size < 2 * 1024 * 1024) :
    RiscvSpec.execute binary input = .ok (SszSpec.decode input) := by
  have evidence := static_evidence
  cases specResult : SszSpec.decode input with
  | accepted value =>
      exact execute_accepts_of_spec_accepts evidence input inputBound value specResult
  | rejected =>
      exact execute_rejects_of_spec_rejects evidence input inputBound specResult

/-- The final Amsterdam V4 compliance statement.  Its dependency spine is intentionally visible:
static artifact evidence, successful execution refinement, and rejection refinement. -/
theorem root_compliance :
    forall input : ByteArray,
      input.size < 2 * 1024 * 1024 ->
        RiscvSpec.execute binary input = .ok (SszSpec.decode input) := by
  intro input inputBound
  exact execute_matches_spec input inputBound

end BinaryFv.SSZ
