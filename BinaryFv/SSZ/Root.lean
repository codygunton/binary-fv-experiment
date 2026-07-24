import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Interface
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Execution
import BinaryFv.SSZ.Zesu.Contracts.ProgramCorrectness

namespace BinaryFv.SSZ

open BinaryFv.RiscV
open BinaryFv.Binary.Elfling

/-- The one canonical, Nix-built Zesu executable covered by the SSZ proof. -/
noncomputable def binary : RiscvSpec.ValidatedElf := {
  bytes := Zesu.Artifact.bytes
  elf := Zesu.Artifact.elf
  parsed_ok := by exact Zesu.Artifact.parsed_ok
  layout := Zesu.Artifact.elf_layout
}

/-!
## Navigation from the root theorem to the source-oriented catalog

`root_compliance` descends through the generated Elfling program's correctness rather than around it.
The two authorized trace-construction theorems each *produce* a canonical generated program together
with `Zesu.Contracts.sszComplianceObligations program`, and the two runner/result theorems below
*consume* that program and obligation. So the spine is literal: no witness exists without program
correctness, and the root claim is built only from witnesses.

**This file contains no `sorry`.** Its two lemmas used to be scaffolds bridging a trace witness to
the public API; that bridge is now a real proof in `Entrypoints/ZesuDecodeRaw/Runner.lean`
(`executeDecode_accepted_of_run`, `executeDecode_rejected_of_run`), so the root only opens the
preflight gate and hands each witness's fields straight over. The two remaining holes in the whole
SSZ proof are the live-trace obligations in `Entrypoints/ZesuDecodeRaw/Execution.lean` — *constructing*
a run of the machine from a specification outcome. Everything downstream of a run existing is proved.

Read the spine outward from the root:

* `root_compliance` — the public claim.
* `Zesu.Contracts.sszComplianceObligations` — some canonical contract parameters make
  `sszProgramCorrectness` hold, plus the two recorded divergences.
* `Zesu.Contracts.sszProgramCorrectness` — canonical coverage, semantic correspondence, the
  per-instance dispatch asserting each occurrence's `correctnessClaim`, precondition satisfiability,
  and the explicit local-to-global composition.
* `Zesu.Contracts.catalog` — the 43 live routines, address-free, matched by full identity.
* the generated Elfling program — canonical-ELF ranges, checked against the pinned bytes.

None of these is a `sorry`; they are named `Prop`s, so an unfinished obligation is stated exactly
without changing the `nix/proof.nix` hole count.
-/

/-- The proof's own binary passes the runner's canonicality gate — by definition, since `binary`'s
bytes *are* the artifact's. Stated once so the two lemmas below can open the gate without
re-evaluating an 86 KB byte comparison. -/
theorem binary_is_canonical :
    Zesu.Entrypoints.ZesuDecodeRaw.artifactIsCanonical binary = true :=
  decide_eq_true (show binary.bytes = Zesu.Artifact.bytes from rfl)

/-- A successful run of the exported wrapper gives the public acceptance.

`program` and `obligations` are genuine premises, not manufactured by the root: they are produced by
`successful_trace_of_spec_accepts` and threaded in here, so the trace this consumes cannot exist
without Elfling program correctness. The machine reasoning itself is entirely
`executeDecode_accepted_of_run`'s — the root reconstructs none of it. -/
theorem execute_accepts_of_successful_trace (input : ByteArray)
    (inputBound : input.size < Zesu.Runtime.maximumInputBytes) (value : SszBridge.RawV4)
    (program : Program) (canonical : Zesu.Contracts.IsCanonicalGeneratedProgram program)
    (obligations : Zesu.Contracts.sszComplianceObligations program)
    (execution : Zesu.Entrypoints.ZesuDecodeRaw.SuccessfulRun input value) :
    RiscvSpec.execute binary input = .ok (.accepted value) := by
  rw [RiscvSpec.execute_eq_executeChecked,
    Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_eq_executeDecode binary_is_canonical inputBound]
  exact Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_accepted_of_run input value
    execution.builds execution.trace execution.withinStepBound execution.accessors
    execution.returnCode execution.storedPresent execution.inputPreserved execution.storedValue

/-- A run recording a spec-producible rejection status gives the public rejection, given the same
canonical program and obligation. -/
theorem execute_rejects_of_rejected_trace (input : ByteArray)
    (inputBound : input.size < Zesu.Runtime.maximumInputBytes)
    (program : Program) (canonical : Zesu.Contracts.IsCanonicalGeneratedProgram program)
    (obligations : Zesu.Contracts.sszComplianceObligations program)
    (execution : Zesu.Entrypoints.ZesuDecodeRaw.RejectedRun input) :
    RiscvSpec.execute binary input = .ok .rejected := by
  rw [RiscvSpec.execute_eq_executeChecked,
    Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_eq_executeDecode binary_is_canonical inputBound]
  exact Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_rejected_of_run input
    execution.builds execution.trace execution.withinStepBound execution.accessors
    execution.returnCode execution.specRejection execution.storedAbsent

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
        Zesu.Entrypoints.ZesuDecodeRaw.successful_trace_of_spec_accepts
          input inputBound value specResult
      exact execute_accepts_of_successful_trace input inputBound value program canonical
        obligations execution
  | rejected =>
      obtain ⟨program, canonical, obligations, ⟨execution⟩⟩ :=
        Zesu.Entrypoints.ZesuDecodeRaw.rejected_trace_of_spec_rejects
          input inputBound specResult
      exact execute_rejects_of_rejected_trace input inputBound program canonical obligations
        execution

end BinaryFv.SSZ
