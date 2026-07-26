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
  per-function-instance dispatch asserting each function instance's `correctnessClaim`, precondition satisfiability,
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
`executeDecode_accepted_of_run`'s — the root reconstructs none of it.

**`_canonical` and `_obligations` are deliberately unused, and the underscore is the honest form.**
Checked rather than assumed: the identical statement without them is provable, so they contribute
nothing to *this* proof. They are kept because the force lives in the **producer** —
`successful_trace_of_spec_accepts` returns them, so `root_compliance` cannot obtain a trace without
also obtaining program correctness — and keeping them here makes a later restructuring that drops
that threading break visibly instead of silently. What they are *not* is a dependency of the machine
bridge, and a reader who inferred one from the signature would be wrong; hence the rename rather than
a comment. Same treatment, and same reasoning, as the dead `before` binders on the four
postconditions. -/
theorem execute_accepts_of_successful_trace (input : ByteArray)
    (inputBound : input.size < Zesu.Runtime.maximumInputBytes) (value : SszBridge.RawV4)
    (program : Program) (_canonical : Zesu.Contracts.IsCanonicalGeneratedProgram program)
    (_obligations : Zesu.Contracts.sszComplianceObligations program)
    (execution : Zesu.Entrypoints.ZesuDecodeRaw.SuccessfulRun input value) :
    RiscvSpec.execute binary input = .ok (.accepted value) := by
  rw [RiscvSpec.execute_eq_executeChecked,
    Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_eq_executeDecode binary_is_canonical inputBound]
  exact Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_accepted_of_run input value
    execution.builds execution.trace execution.withinStepBound execution.accessors
    execution.returnCode execution.storedPresent execution.inputPreserved execution.storedValue

/-- A run recording a spec-producible rejection status gives the public rejection, given the same
canonical program and obligation. `_canonical` and `_obligations` are dead here for the same reason,
and kept for the same reason, as in `execute_accepts_of_successful_trace` above. -/
theorem execute_rejects_of_rejected_trace (input : ByteArray)
    (inputBound : input.size < Zesu.Runtime.maximumInputBytes)
    (program : Program) (_canonical : Zesu.Contracts.IsCanonicalGeneratedProgram program)
    (_obligations : Zesu.Contracts.sszComplianceObligations program)
    (execution : Zesu.Entrypoints.ZesuDecodeRaw.RejectedRun input) :
    RiscvSpec.execute binary input = .ok .rejected := by
  rw [RiscvSpec.execute_eq_executeChecked,
    Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_eq_executeDecode binary_is_canonical inputBound]
  exact Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_rejected_of_run input
    execution.builds execution.trace execution.withinStepBound execution.accessors
    execution.returnCode execution.specRejection execution.storedAbsent

/-- **No failure mode becomes a rejection — proved at the layer where that is claimed.**

`RiscvSpec.execute`'s own docstring says "every failure mode keeps its own error; none of them
becomes a rejection". That claim is made about `execute`; until now the theorem backing it
(`executeDecode_rejected_forces_checks`) stopped one layer below, at `executeDecode`. The claim was
true — `execute` is `executeChecked` by `rfl`, and the preflight gate can only contribute
`.invalidArtifact` — but true-and-unproved-at-the-level-it-is-stated is the shape of every defect the
reachability pass turned up, so it is worth the twenty lines to close rather than to argue.

Stated over an arbitrary `ValidatedElf` rather than `binary`, so it constrains the public API itself
and not merely the proof's own instance of it. -/
theorem execute_rejected_forces_checks {b : RiscvSpec.ValidatedElf} {input : ByteArray}
    (h : RiscvSpec.execute b input = .ok .rejected) :
    Zesu.Entrypoints.ZesuDecodeRaw.preflight b input = .ok () ∧
      ∃ (final : BinaryFv.RiscV.State)
        (rawResult rawError : Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome),
        Zesu.Entrypoints.ZesuDecodeRaw.observeReturnCode? final = some 0 ∧
        rawResult = Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome.returned 0 ∧
        (∃ status, rawError = Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome.returned status ∧
          Zesu.Entrypoints.ZesuDecodeRaw.statusCategory status = .specRejection) := by
  rw [RiscvSpec.execute_eq_executeChecked] at h
  obtain ⟨hgate, hdec⟩ := Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_rejected_forces_gate h
  obtain ⟨final, _steps, rawResult, rawError, hcode, hnull, _htag, hstatus, -⟩ :=
    Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_rejected_forces_checks hdec
  exact ⟨hgate, final, rawResult, rawError, hcode, hnull, hstatus⟩

/-- **The public API never invents an acceptance, and the value it reports is the one memory held.**

The twin of `execute_rejected_forces_checks`, and the sharper of the two. Rejection has one shape, so
its converse mostly rules failure modes out. Acceptance carries a *value*, and `classifyWrapperRun`
takes that value from `observeDecodedValue final` — so without this, nothing at the public layer ties
the reported value to the observation. The final conjunct is that tie: an `accepted value` answer
forces `observeDecodedValue final = some value`, the same `value`.

Stated over an arbitrary `ValidatedElf`, like its twin. -/
theorem execute_accepted_forces_checks {b : RiscvSpec.ValidatedElf} {input : ByteArray}
    {value : SszBridge.RawV4} (h : RiscvSpec.execute b input = .ok (.accepted value)) :
    Zesu.Entrypoints.ZesuDecodeRaw.preflight b input = .ok () ∧
      ∃ (final : BinaryFv.RiscV.State)
        (rawResult rawError : Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome),
        Zesu.Entrypoints.ZesuDecodeRaw.observeReturnCode? final = some 1 ∧
        rawError = Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome.returned
          Zesu.Contracts.DecodeStatus.ok.code ∧
        rawResult = Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome.returned
          Zesu.Elfling.canonicalResultBuffer ∧
        Zesu.MemoryRepresentation.observeOptionTag? final
          Zesu.Entrypoints.ZesuDecodeRaw.storedResultDiscriminantAddr = some true ∧
        Zesu.Entrypoints.ZesuDecodeRaw.observeDecodedValue final = some value := by
  rw [RiscvSpec.execute_eq_executeChecked] at h
  obtain ⟨hgate, hdec⟩ := Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_accepted_forces_gate h
  obtain ⟨final, _steps, rawResult, rawError, hcode, herror, hnull, htag, hvalue, -⟩ :=
    Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_accepted_forces_checks hdec
  exact ⟨hgate, final, rawResult, rawError, hcode, herror, hnull, htag, hvalue⟩

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
