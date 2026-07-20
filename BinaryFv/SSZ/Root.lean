import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Interface
import BinaryFv.SSZ.Zesu.Proof.Compliance

namespace BinaryFv.SSZ

open BinaryFv.RiscV

/-- The one canonical, Nix-built Zesu executable covered by the SSZ proof. -/
noncomputable def binary : RiscvSpec.ValidatedElf := {
  bytes := Zesu.Artifact.bytes
  elf := Zesu.Artifact.elf
  parsed_ok := by exact Zesu.Artifact.parsed_ok
  layout := Zesu.Artifact.elf_layout
}

/-- Authorized navigation scaffold connecting the executable runner/result observer to a successful
live Sail trace.  `runToSentinel_of_traceToSentinel` supplies the runner correspondence and
`RawV4SuccessResultRep` supplies the result observation. -/
theorem execute_accepts_of_successful_trace (input : ByteArray) (value : SszBridge.RawV4)
    (execution : Zesu.Proof.SuccessfulTraceWitness input value) :
    RiscvSpec.execute binary input = .ok (.accepted value) := by
  sorry

/-- Authorized navigation scaffold connecting a classified nonzero-status trace to the executable
runner's normalized rejection result. -/
theorem execute_rejects_of_rejected_trace (input : ByteArray)
    (execution : Zesu.Proof.RejectedTraceWitness input) :
    RiscvSpec.execute binary input = .ok .rejected := by
  sorry

/-- Successful and rejected execution paths together refine the complete observable SSZ spec. -/
theorem execute_matches_spec (input : ByteArray) (inputBound : input.size < 2 * 1024 * 1024) :
    RiscvSpec.execute binary input = .ok (SszSpec.decode input) := by
  cases specResult : SszSpec.decode input with
  | accepted value =>
      obtain ⟨execution⟩ :=
        Zesu.Proof.successful_trace_of_spec_accepts input inputBound value specResult
      exact execute_accepts_of_successful_trace input value execution
  | rejected =>
      obtain ⟨execution⟩ :=
        Zesu.Proof.rejected_trace_of_spec_rejects input inputBound specResult
      exact execute_rejects_of_rejected_trace input execution

/-- The final Amsterdam V4 compliance statement.  Its dependency spine is intentionally visible:
spec classification, live Sail traces, runner/result observation, and the public execution API. -/
theorem root_compliance :
    forall input : ByteArray,
      input.size < 2 * 1024 * 1024 ->
        RiscvSpec.execute binary input = .ok (SszSpec.decode input) := by
  intro input inputBound
  exact execute_matches_spec input inputBound

end BinaryFv.SSZ
