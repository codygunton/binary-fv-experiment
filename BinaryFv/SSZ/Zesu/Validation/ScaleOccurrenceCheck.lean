import BinaryFv.SSZ.Zesu.Validation.ScaleOccurrenceTypes
import BinaryFv.SSZ.Zesu.Validation.GeneratedScaleEvidence

/-!
# Row C: scaled Lean diagnostic checker over ALL production-ELF occurrences

Generalizes the kernel-checked `decodeOptionalBlobSchedule` vertical slice (`BinaryOccurrenceCheck`)
to EVERY occurrence in `program.json`. It reads the generated compact evidence (`GeneratedScaleEvidence`,
captured from the UNCHANGED production ELF under pinned QEMU) and re-derives eight generic per-occurrence
checks, reproducing the Python oracle (`scale_occurrences.evaluate_facts`) exactly:

  entryReached          the first in-region PC is the declared entry PC
  controlFlowIntegrity  every executed transfer from an OWNED pc is a declared CFG edge (exact)
  exitsRespected        every leaving / dynamic transfer departs at a declared exit PC
  withinStepBound       max per-invocation instruction count ≤ the contract step bound (gap if the
                        bound is input-dependent)
  allocationConsistent  a non-allocating routine never bumps the allocator cursor
  inputPreserved        no store into the SSZ input buffer
  codePreserved         no store into .text
  writesClassified      every in-region store lands in a known memory region (re-classified here from
                        the recorded (addr, sp); raw mem primitives carry a class summary)
  meaningTie            a lightweight scalar/slice input→result tie (gap otherwise; the RIGOROUS
                        per-value meaning check is the vertical slice, not this scan)

Each check is an `Option Bool`: `none` marks an EXPLICIT gap and is NEVER counted as a pass. Coverage is
PER OCCURRENCE — an occurrence is validated only on evidence in which its own region executes.

`checker_agrees_with_oracle` pins Lean ≡ Python on every occurrence. `gating_checks_hold` records that
the six structural/effect checks pass on every COVERED occurrence. The `negative_*` theorems require
mutations of the evidence to flip a check. Validation module — never a proof premise, never imported by
the theorem graph.
-/

namespace BinaryFv.SSZ.Zesu.Validation

open BinaryFv.SSZ.Zesu.Validation.GeneratedScaleEvidence

/-- Pinned production memory layout (identical to `BinaryOccurrenceCheck.classifyWrite`). -/
def classifyWriteScaled (addr sp : Nat) : String :=
  if 65768 ≤ addr ∧ addr < 81704 then "code"
  else if 86032 ≤ addr ∧ addr < 86048 then "allocator-cursor"
  else if 86048 ≤ addr ∧ addr < 67194912 then "heap"
  else if 67194912 ≤ addr ∧ addr < 69292064 then "input"
  else if 69292064 ≤ addr ∧ addr < 69292928 then "decoder-global"
  else if sp - 65536 ≤ addr ∧ addr ≤ sp + 65536 then "stack"
  else "unclassified"

/-- The distinct-relevant write classes of an occurrence: re-classified from the carried non-stack
addresses (with `sp = 0`; carried addresses are never stack, and every non-stack region sits below the
stack window) plus the summarized `stack` flag — or the pre-classified summary for raw mem primitives.
Environment-independent: no absolute stack address appears. -/
def scaledClasses (ev : OccScaleEvidence) : List String :=
  if ev.storesSummarized then ev.storeClasses
  else (ev.inRegionStores.map (fun a => classifyWriteScaled a 0)) ++ (if ev.hadStackStore then ["stack"] else [])

/-- The scaled checker, reproducing the Python oracle `evaluate_facts`. -/
def evaluateOcc (ev : OccScaleEvidence) : ScaleChecks :=
  if !ev.covered then
    { entryReached := none, controlFlowIntegrity := none, exitsRespected := none, withinStepBound := none,
      allocationConsistent := none, inputPreserved := none, codePreserved := none,
      writesClassified := none, meaningTie := none }
  else
    let classes := scaledClasses ev
    { entryReached := some (ev.firstInRegion == ev.entryPc)
      controlFlowIntegrity := some (ev.executedOwnedEdges.all (fun e => ev.declaredEdges.contains e))
      exitsRespected := some (ev.leavingSources.all (fun s => ev.exits.contains s) &&
                              ev.dynamicTransferSources.all (fun s => ev.exits.contains s))
      withinStepBound := ev.stepBound.map (fun b => ev.maxInsnPerInvocation ≤ b)
      allocationConsistent := some (ev.allocates || !(classes.contains "allocator-cursor"))
      inputPreserved := some (!(classes.contains "input"))
      codePreserved := some (!(classes.contains "code"))
      writesClassified := some (!(classes.contains "unclassified"))
      meaningTie :=
        if ev.meaningTieKind == "scalarLE" || ev.meaningTieKind == "offset" then
          (if ev.scalarCarried then some true else none)
        else if ev.meaningTieKind == "slice" then
          (if ev.storeHasInputPtr then some true else none)
        else none }

/-- **Lean ≡ Python.** The scaled checker reproduces the oracle's result on EVERY occurrence
(present / malformed / absent arms, covered and uncovered). Kernel-checked. -/
theorem checker_agrees_with_oracle :
    allOccs.all (fun p => evaluateOcc p.1 == p.2) = true := by native_decide

/-- The six structural/effect gating checks (entry / CFG integrity / allocation / input & code
preservation / write classification) pass — `some true` — on EVERY covered occurrence. Step bound and
meaning tie are reported separately (they carry explicit gaps). Kernel-checked. -/
theorem gating_checks_hold :
    allOccs.all (fun p =>
      let ev := p.1
      !ev.covered ||
        (let r := evaluateOcc ev
         r.entryReached == some true && r.controlFlowIntegrity == some true &&
         r.exitsRespected == some true &&
         r.allocationConsistent == some true && r.inputPreserved == some true &&
         r.codePreserved == some true && r.writesClassified == some true)) = true := by
  native_decide

/-- No gating check ever FAILS (`some false`) on any occurrence: results are pass or explicit gap,
never a violation of a Row A binding against the unchanged production ELF. Kernel-checked. -/
theorem no_gating_failures :
    allOccs.all (fun p =>
      let r := evaluateOcc p.1
      r.entryReached != some false && r.controlFlowIntegrity != some false &&
      r.exitsRespected != some false &&
      r.allocationConsistent != some false && r.inputPreserved != some false &&
      r.codePreserved != some false && r.writesClassified != some false &&
      r.withinStepBound != some false && r.meaningTie != some false) = true := by
  native_decide

/-- **Step bounds hold on every covered occurrence except the one documented gap.** occurrence 134
(`requireCanonicalOffsets`) is the sole covered occurrence whose contract bound is an explicit gap — its
`offsets.length` argument is caller-passed, not present in the occurrence's own input-buffer reads (the
required interface change is recorded in the catalog / coverage report). Every OTHER covered occurrence
passes `withinStepBound`, including the input-dependent bounds resolved via sound lower bounds on their
argument. Kernel-checked; Row C's step-bound conclusion excludes occurrence 134 by construction. -/
theorem step_bounds_hold_except_documented_gap :
    allOccs.all (fun p =>
      let ev := p.1
      !ev.covered || ev.index == 134 || (evaluateOcc ev).withinStepBound == some true) = true := by
  native_decide

/-- The uncovered occurrences (allocatorRemap 123 / allocatorResize 135 / zesu_raw_error 137, each
STATICALLY classified as unreachable in this ELF's control flow — see `UNCOVERED_CLASSIFICATION.md`) are
exactly the occurrences the checker reports as not covered; every OTHER occurrence is covered and carries
concrete per-occurrence evidence. Row C's coverage conclusion excludes precisely these three. -/
theorem uncovered_are_exactly_the_statically_dead :
    allOccs.all (fun p => p.1.covered == (p.1.index != 123 && p.1.index != 135 && p.1.index != 137))
      = true := by native_decide

/-!
## Negative tests — mutating a covered occurrence's evidence must flip the responsible check. The
sampled occurrence is 116 (`decodeOptionalBlobSchedule`), the vertical-slice occurrence, located in
`allOccs`. Each theorem corrupts one field and asserts the check turns `some false`.
-/

/-- occurrence 116's evidence from the generated list (the vertical-slice occurrence). -/
def sample : OccScaleEvidence := (allOccs.filter (fun p => p.1.index == 116)).head!.1

/-- The sample is genuinely a GO baseline (all gating checks pass). -/
theorem sample_is_go :
    let r := evaluateOcc sample
    r.entryReached == some true && r.controlFlowIntegrity == some true &&
      r.allocationConsistent == some true && r.inputPreserved == some true &&
      r.codePreserved == some true && r.writesClassified == some true := by native_decide

/-- wrong entry: first in-region PC is not the declared entry. -/
theorem negative_wrong_entry :
    (evaluateOcc { sample with firstInRegion := sample.entryPc + 4 }).entryReached
      = some false := by native_decide

/-- undeclared edge: an executed transfer from an owned PC that is not in the generated CFG. -/
theorem negative_undeclared_edge :
    (evaluateOcc { sample with
        executedOwnedEdges := (sample.entryPc, 999999) :: sample.executedOwnedEdges }).controlFlowIntegrity
      = some false := by native_decide

/-- exit violation: execution leaves the occurrence from a PC that is not a declared exit. -/
theorem negative_undeclared_exit :
    (evaluateOcc { sample with
        leavingSources := 999999 :: sample.leavingSources }).exitsRespected
      = some false := by native_decide

/-- spurious allocation: a store bumping the allocator cursor in a non-allocating routine. -/
theorem negative_cursor_bump :
    (evaluateOcc { sample with storesSummarized := true, storeClasses := "allocator-cursor" :: sample.storeClasses }).allocationConsistent
      = some false := by native_decide

/-- code-preservation violation: an injected store into .text. -/
theorem negative_code_write :
    (evaluateOcc { sample with inRegionStores := (65768 + 8) :: sample.inRegionStores }).codePreserved
      = some false := by native_decide

/-- input-preservation violation: an injected store into the SSZ input buffer. -/
theorem negative_input_write :
    (evaluateOcc { sample with inRegionStores := (67194912 + 8) :: sample.inRegionStores }).inputPreserved
      = some false := by native_decide

/-- unclassified write: a store outside every known region and its stack window. -/
theorem negative_unclassified_write :
    (evaluateOcc { sample with inRegionStores := 3735879680 :: sample.inRegionStores }).writesClassified
      = some false := by native_decide

/-- step-bound violation: instruction count exceeds the contract bound. -/
theorem negative_step_bound :
    (evaluateOcc { sample with maxInsnPerInvocation := 100000 }).withinStepBound
      = some false := by native_decide

end BinaryFv.SSZ.Zesu.Validation
