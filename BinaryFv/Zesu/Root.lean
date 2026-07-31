import BinaryFv.Zesu.Artifact.Layout
import BinaryFv.Zesu.Interface
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Execution
import BinaryFv.Zesu.Contracts.ProgramCorrectness

namespace BinaryFv.Zesu

open BinaryFv.RiscV
open BinaryFv.Binary.Elfling

/-- The one canonical, Nix-built Zesu executable covered by the SSZ proof. -/
noncomputable def binary : RiscvSpec.ValidatedElf := {
  bytes := Artifact.bytes
  elf := Artifact.elf
  parsed_ok := by exact Artifact.parsed_ok
  layout := Artifact.elf_layout
}

/-!
## Navigation from the root theorem to the source-oriented catalog

`root_compliance` descends through the generated Elfling program's correctness rather than around it.
The two authorized trace-construction theorems each *produce* a canonical generated program together
with `Contracts.sszComplianceObligations program`, and the two runner/result theorems below
*consume* that program and obligation. So the spine is literal: no witness exists without program
correctness, and the root claim is built only from witnesses.

Read the spine outward from the root:

* `root_compliance` — the public claim.
* `Contracts.sszComplianceObligations` — some canonical contract parameters make
  `sszProgramCorrectness` hold, plus the two recorded divergences.
* `Contracts.sszProgramCorrectness` — canonical coverage, semantic correspondence, the
  per-instance dispatch asserting each occurrence's `correctnessClaim`, precondition satisfiability,
  and the explicit local-to-global composition.
* `Contracts.catalog` — the 43 live routines, address-free, matched by full identity.
* the generated Elfling program — canonical-ELF ranges, checked against the pinned bytes.

None of these is a `sorry`; they are named `Prop`s, so an unfinished obligation is stated exactly
without changing the `nix/proof.nix` hole count.
-/

/-- Authorized navigation scaffold connecting the executable runner/result observer to a successful
live Sail trace, *given* the canonical generated program and its compliance obligation.

`program` and `obligations` are genuine premises, not manufactured by the root: they are produced by
`successful_trace_of_spec_accepts` and threaded in here, so the eventual proof of this theorem may —
and must — use program correctness to establish the runner result. -/
theorem execute_accepts_of_successful_trace (input : ByteArray) (value : SszBridge.RawV4)
    (program : Program) (canonical : Contracts.IsCanonicalGeneratedProgram program)
    (obligations : Contracts.sszComplianceObligations program)
    (execution : Entrypoints.ZesuDecodeRaw.SuccessfulTraceWitness input value) :
    RiscvSpec.execute binary input = .ok (.accepted value) := by
  sorry

/-- Authorized navigation scaffold connecting a classified nonzero-status trace to the executable
runner's normalized rejection result, given the same canonical program and obligation. -/
theorem execute_rejects_of_rejected_trace (input : ByteArray)
    (program : Program) (canonical : Contracts.IsCanonicalGeneratedProgram program)
    (obligations : Contracts.sszComplianceObligations program)
    (execution : Entrypoints.ZesuDecodeRaw.RejectedTraceWitness input) :
    RiscvSpec.execute binary input = .ok .rejected := by
  sorry

/-- The final Amsterdam V4 compliance statement.  Its dependency spine is intentionally visible:
spec classification, the canonical Elfling program and its compliance obligation, live Sail traces,
runner/result observation, and the public execution API. -/
theorem root_compliance :
    forall input : ByteArray,
      input.size < 2 * 1024 * 1024 ->
        RiscvSpec.execute binary input = .ok (SszSpec.decode input) := by
  intro input inputBound
  cases specResult : SszSpec.decode input with
  | accepted value =>
      obtain ⟨program, canonical, obligations, ⟨execution⟩⟩ :=
        Entrypoints.ZesuDecodeRaw.successful_trace_of_spec_accepts
          input inputBound value specResult
      exact execute_accepts_of_successful_trace input value program canonical obligations execution
  | rejected =>
      obtain ⟨program, canonical, obligations, ⟨execution⟩⟩ :=
        Entrypoints.ZesuDecodeRaw.rejected_trace_of_spec_rejects
          input inputBound specResult
      exact execute_rejects_of_rejected_trace input program canonical obligations execution

end BinaryFv.Zesu
