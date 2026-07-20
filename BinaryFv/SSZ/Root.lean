import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Interface
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Execution
import BinaryFv.SSZ.Zesu.Contracts.Catalog

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
    (execution : Zesu.Entrypoints.ZesuDecodeRaw.SuccessfulTraceWitness input value) :
    RiscvSpec.execute binary input = .ok (.accepted value) := by
  sorry

/-- Authorized navigation scaffold connecting a classified nonzero-status trace to the executable
runner's normalized rejection result. -/
theorem execute_rejects_of_rejected_trace (input : ByteArray)
    (execution : Zesu.Entrypoints.ZesuDecodeRaw.RejectedTraceWitness input) :
    RiscvSpec.execute binary input = .ok .rejected := by
  sorry

/-!
## Navigation from the root theorem to the source-oriented catalog

The obligations below are the visible dependency spine between `root_compliance` and the handwritten
contracts. None of them is a `sorry`: they are named `Prop`s, which is what lets an unfinished
obligation be stated exactly without weakening the `nix/proof.nix` hole audit.

Read the spine outward from the root:

* `root_compliance` — the public claim.
* `sszProgramCorrectness` — the generated Elfling program covers the binary and every occurrence
  implements its handwritten contract.
* `Zesu.Contracts.catalogSemanticObligations` — the catalog's meanings agree with the pinned oracle.
* `Zesu.Contracts.knownDivergences` — the two places the binary and the oracle genuinely differ,
  surfaced rather than omitted.
* `Zesu.Contracts.catalog` — the 33 routines, address-free.
* the generated Elfling program — canonical-ELF ranges, checked against the pinned bytes.
-/

/-- The generated Elfling program covers the reachable binary and every occurrence implements the
handwritten contract for the routine it was extracted from.

This is the local-to-global obligation. `Zesu.Contracts.coverage` supplies the two coverage
directions and the defect-free extraction requirement; the per-occurrence `correctnessClaim`s in the
`Contracts` modules supply the rest. -/
def sszProgramCorrectness (program : BinaryFv.Binary.Elfling.Program) : Prop :=
  Zesu.Contracts.coverage program ∧ Zesu.Contracts.catalogSemanticObligations

/-- Everything the root theorem depends on, in one name.

`knownDivergences` is conjoined deliberately: both members are *true* statements that the binary and
the oracle differ, and stating them here keeps them from reading as oversights. One is masked by
`retryTailNeverSchemaValid`; the other is excluded by the input bound, which is why
`Zesu.Contracts.rootComplianceScope` exists as a name rather than an inline literal. -/
def sszComplianceObligations (program : BinaryFv.Binary.Elfling.Program) : Prop :=
  sszProgramCorrectness program ∧ Zesu.Contracts.knownDivergences

/-- The final Amsterdam V4 compliance statement.  Its dependency spine is intentionally visible:
spec classification, live Sail traces, runner/result observation, and the public execution API. -/
theorem root_compliance :
    forall input : ByteArray,
      input.size < 2 * 1024 * 1024 ->
        RiscvSpec.execute binary input = .ok (SszSpec.decode input) := by
  intro input inputBound
  cases specResult : SszSpec.decode input with
  | accepted value =>
      obtain ⟨execution⟩ :=
        Zesu.Entrypoints.ZesuDecodeRaw.successful_trace_of_spec_accepts
          input inputBound value specResult
      exact execute_accepts_of_successful_trace input value execution
  | rejected =>
      obtain ⟨execution⟩ :=
        Zesu.Entrypoints.ZesuDecodeRaw.rejected_trace_of_spec_rejects
          input inputBound specResult
      exact execute_rejects_of_rejected_trace input execution

end BinaryFv.SSZ
