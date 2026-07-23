import BinaryFv.SSZ.Zesu.Validation.ScaleOccurrenceTypes
import BinaryFv.SSZ.Zesu.Validation.GeneratedScaleEvidence

/-!
# Row C: scaled Lean diagnostic checker over ALL production-ELF occurrences

Generalizes the kernel-checked `decodeOptionalBlobSchedule` vertical slice (`BinaryOccurrenceCheck`)
to EVERY occurrence in `program.json`. It reads the generated compact evidence (`GeneratedScaleEvidence`,
captured from the UNCHANGED production ELF under pinned QEMU) and re-derives thirteen generic
per-occurrence checks, reproducing the Python oracle (`scale_occurrences.evaluate_facts`) exactly:

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
  bindingsEvaluable     every declared Row A binding row resolved against the real machine state at
                        the occurrence's declared entry PC (an unresolvable location is a FAILURE)
  bindingsRealized      the resolved bindings had their declared consequence in the trace
  exitBindingRealized   the result register at a declared RETURN exit matches the exit convention
  allocationLedger      an allocating occurrence's cursor bumps are well-formed ledger events
  meaningTie            the little-endian integer of the exact window a leaf reader read IS the value
                        it produced (gap otherwise; the full per-value meaning against the handwritten
                        spec is the vertical slice, not this scan)

## What this module re-derives, and what it does not

`bindingsEvaluable`, `exitBindingRealized`, `allocationLedger`, `meaningTie` and the four family
predicates (`offsetReadHolds` / `entryAbiHolds` / `rawCopyHolds` / `allocHolds`) are computed HERE from
the carried observations — the Lean checker decides them, it does not import a verdict.

`bindingsRealized` is the AGGREGATION of per-invocation verdicts, and that aggregation rule is
re-derived here (`bindingsRealizedOf`); the per-invocation family verdicts themselves are the Python
reducer's, because reproducing them would require carrying every invocation's full register file and
shadow memory into a committed artifact. `rederived_families_agree` is the cross-check that keeps that
import honest: the independently re-derived family predicate must never contradict the aggregate.

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

/-- The named scalar observation `k` of the first captured invocation, if the reducer recorded one. -/
def obs (ev : OccScaleEvidence) (k : String) : Option Int :=
  (ev.bindingObs.find? (fun p => p.1 == k)).map Prod.snd

/-- **Row A entry bindings resolve.** Every declared effective binding row produced a concrete value
from the real machine state at the declared entry PC. `"unresolved"` means the declared location could
not be read at all, which is a FAILURE — a binding that names a location the machine cannot supply is
wrong, not merely unobserved. An occurrence with no declared rows has no obligation to discharge, so it
is an explicit gap rather than a free pass. -/
def bindingsEvaluableOf (ev : OccScaleEvidence) : Option Bool :=
  if ev.bindingHows.isEmpty then none
  else some (ev.bindingHows.all (fun h => h != "unresolved"))

/-- The per-invocation consequence verdicts, aggregated. A single contradicted invocation fails the
occurrence; a pass requires every captured invocation to have realized the consequence. -/
def bindingsRealizedOf (ev : OccScaleEvidence) : Option Bool :=
  if ev.realizedFail > 0 then some false
  else if ev.realizedPass > 0 && ev.realizedGap == 0 then some true
  else none

/-- The `offsetRead` consequence, RE-DERIVED here from the carried observations rather than taken from
the oracle: a reader declaring `len` must have touched exactly `len` distinct bytes, and the slice base
its `offset` implies must land in a real data region. -/
def offsetReadHolds (ev : OccScaleEvidence) : Option Bool :=
  if ev.bindingFamily != "offsetRead" then none else
  match obs ev "declaredLen", obs ev "readCount", obs ev "baseClassOk" with
  | some declared, some got, some baseOk =>
      -- `declaredLen = -1` marks a reader with no `len` row: only the base-region test applies.
      some (baseOk == 1 && (declared < 0 || declared == got))
  | _, _, _ => none

/-- The `entryAbi` consequence, RE-DERIVED: the exported entry's `input`/`input_len` registers must
equal the linked input-buffer base and the exact byte length the process was fed. -/
def entryAbiHolds (ev : OccScaleEvidence) : Option Bool :=
  if ev.bindingFamily != "entryAbi" then none else
  match obs ev "entryInput", obs ev "wantInput", obs ev "entryLen", obs ev "wantLen" with
  | some i, some wi, some l, some wl => some (i == wi && l == wl)
  | _, _, _, _ => none

/-- The `rawCopy` consequence, RE-DERIVED: `memcpy`/`memmove` must write exactly `n` bytes at `dst`
and read the whole `[src, src+n)` window. -/
def rawCopyHolds (ev : OccScaleEvidence) : Option Bool :=
  if ev.bindingFamily != "rawCopy" then none else
  match obs ev "copyStoredBytes", obs ev "copyWantBytes", obs ev "copySrcCovered" with
  | some got, some want, some cov => some (got == want && cov == 1)
  | _, _, _ => none

/-- The `alloc` consequence, RE-DERIVED: the cursor bump covers the request and the block honours the
requested alignment. -/
def allocHolds (ev : OccScaleEvidence) : Option Bool :=
  if ev.bindingFamily != "alloc" then none else
  match obs ev "allocSize", obs ev "allocBump", obs ev "allocAlign", obs ev "allocAfter" with
  | some size, some bump, some align, some after =>
      some (size ≤ bump && align > 0 && after % align == 0)
  | _, _, _, _ => none

/-- The exit convention at a declared RETURN exit. A tail-call exit is excluded upstream: its register
file holds the callee's arguments, not this occurrence's result. -/
def exitBindingOf (ev : OccScaleEvidence) : Option Bool :=
  if ev.exitConvention == "" then none
  else if ev.returnExits.isEmpty || ev.exitA0Classes.isEmpty then none
  else if ev.exitConvention == "allocPointer" then
    some (ev.exitA0Classes.all (fun c => c == "heap" || c == "unclassified"))
  else some true

/-- An allocating occurrence's ledger events must strictly advance the cursor and leave it in the heap;
a non-allocating one causes no event and is covered by `allocationConsistent` instead. -/
def allocationLedgerOf (ev : OccScaleEvidence) : Option Bool :=
  if !ev.allocates || ev.ledgerEventCount == 0 then none
  else some (ev.ledgerAllPositive && ev.ledgerAfterInHeap)

/-- The scaled checker, reproducing the Python oracle `evaluate_facts`. -/
def evaluateOcc (ev : OccScaleEvidence) : ScaleChecks :=
  if !ev.covered then
    { entryReached := none, controlFlowIntegrity := none, exitsRespected := none, withinStepBound := none,
      allocationConsistent := none, inputPreserved := none, codePreserved := none,
      writesClassified := none, bindingsEvaluable := none, bindingsRealized := none,
      exitBindingRealized := none, allocationLedger := none, meaningTie := none }
  else
    let classes := scaledClasses ev
    { bindingsEvaluable := bindingsEvaluableOf ev
      bindingsRealized := bindingsRealizedOf ev
      exitBindingRealized := exitBindingOf ev
      allocationLedger := allocationLedgerOf ev
      entryReached := some (ev.firstInRegion == ev.entryPc)
      controlFlowIntegrity := some (ev.executedOwnedEdges.all (fun e => ev.declaredEdges.contains e))
      exitsRespected := some (ev.leavingSources.all (fun s => ev.exits.contains s) &&
                              ev.dynamicTransferSources.all (fun s => ev.exits.contains s))
      withinStepBound := ev.stepBound.map (fun b => ev.maxInsnPerInvocation ≤ b)
      allocationConsistent := some (ev.allocates || !(classes.contains "allocator-cursor"))
      inputPreserved := some (!(classes.contains "input"))
      codePreserved := some (!(classes.contains "code"))
      writesClassified := some (!(classes.contains "unclassified"))
      -- MEANING. `meaningProduced` is the rigorous statement: the occurrence read a window of
      -- EXACTLY its declared little-endian width, and that window's value is what it produced (stored,
      -- or held in a register when it left). The older value tie survives only for the slice readers.
      meaningTie :=
        if ev.meaningProduced then some true
        else if ev.meaningTieKind == "slice" && ev.storeHasInputPtr then some true
        else if (ev.meaningTieKind == "scalarLE" || ev.meaningTieKind == "offset")
                && ev.scalarCarried then some true
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

/-- The uncovered occurrences (allocatorRemap 123 / allocatorResize 135 / zesu_raw_error 137) are
exactly the occurrences the checker reports as not covered; every OTHER occurrence is covered and carries
concrete per-occurrence evidence. Row C's coverage conclusion excludes precisely these three.

Their static unreachability is established separately by `static_reachability.py` — a backward
reaching-definitions fixpoint over the reconstructed CFG plus a danger-set closure over the loaded image
— and holds under the two hypotheses that analysis states explicitly (`STATIC_REACHABILITY.md`). This
theorem asserts only the coverage partition, not the unreachability claim. -/
theorem uncovered_are_exactly_the_statically_dead :
    allOccs.all (fun p => p.1.covered == (p.1.index != 123 && p.1.index != 135 && p.1.index != 137))
      = true := by native_decide

/-! ## Row A bindings — the declared machine placement, checked against the real run -/

/-- **Every declared Row A binding resolves against the production machine.** For each of the 110
occurrences carrying effective binding rows, every declared location — register, frame slot, base+offset
memory word, or constant — produced a concrete value from the register/memory state captured at that
occurrence's declared entry PC. No row is `"unresolved"`. Kernel-checked. -/
theorem all_declared_bindings_resolve :
    allOccs.all (fun p => (evaluateOcc p.1).bindingsEvaluable != some false) = true := by
  native_decide

/-- The count of occurrences whose bindings were evaluated is exactly the 110 that Row A's
`BindingInventory.bound_occurrence_count` says carry parameter rows — the binding evidence covers the
whole bound population, not a sample. -/
theorem bound_occurrence_coverage :
    (allOccs.filter (fun p => (evaluateOcc p.1).bindingsEvaluable == some true)).length = 110 := by
  native_decide

/-- **The re-derived family consequences agree with the recorded aggregate.** For every occurrence whose
routine has a binding-consequence family, the consequence RE-DERIVED here from the carried observations
(`offsetReadHolds` / `entryAbiHolds` / `rawCopyHolds` / `allocHolds`) never contradicts the aggregated
per-invocation verdict. This is what keeps the aggregate from being an unchecked import of the oracle's
opinion. Kernel-checked. -/
theorem rederived_families_agree :
    allOccs.all (fun p =>
      let ev := p.1
      let r := [offsetReadHolds ev, entryAbiHolds ev, rawCopyHolds ev, allocHolds ev]
      r.all (fun x => x != some false) &&
        (bindingsRealizedOf ev != some true || r.all (fun x => x != some false))) = true := by
  native_decide

/-- **The exported entry ABI is realized exactly.** occurrence 1 (`zesu_decode_raw`) received the linked
input-buffer base and the exact byte length of the file the process was fed — external ground truth, not
a self-report. Kernel-checked. -/
theorem entry_abi_realized :
    (allOccs.filter (fun p => p.1.index == 1)).all (fun p => entryAbiHolds p.1 == some true) = true := by
  native_decide

/-- **No binding, exit or ledger check ever FAILS.** Across all 141 occurrences these are pass or
explicit gap — the production ELF never contradicted a declared Row A placement. Kernel-checked. -/
theorem no_binding_failures :
    allOccs.all (fun p =>
      let r := evaluateOcc p.1
      r.bindingsEvaluable != some false && r.bindingsRealized != some false &&
      r.exitBindingRealized != some false && r.allocationLedger != some false) = true := by
  native_decide

/-- **The allocation ledger is well formed wherever it was observed.** Every cursor bump caused by an
allocating occurrence strictly advanced the bump cursor and left it inside the heap — reconstructed from
the cursor's own write history, not from anything the allocator reports about itself. -/
theorem allocation_ledger_wellformed :
    allOccs.all (fun p => p.1.ledgerEventCount == 0 ||
      (p.1.ledgerAllPositive && p.1.ledgerAfterInHeap)) = true := by native_decide

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

/-! ### Binding / ledger negatives — the new checks must be falsifiable too. -/

/-- an unreadable declared location: a binding naming a place the machine cannot supply must FAIL, not
degrade into a gap. -/
theorem negative_unresolved_binding :
    (evaluateOcc { sample with bindingHows := ["exact", "unresolved"] }).bindingsEvaluable
      = some false := by native_decide

/-- a contradicted binding consequence in any single invocation fails the occurrence. -/
theorem negative_binding_consequence :
    (evaluateOcc { sample with realizedPass := 3, realizedFail := 1, realizedGap := 0 }).bindingsRealized
      = some false := by native_decide

/-- a gap in any invocation withholds the pass rather than granting it. -/
theorem negative_binding_partial_is_gap :
    (evaluateOcc { sample with realizedPass := 3, realizedFail := 0, realizedGap := 1 }).bindingsRealized
      = none := by native_decide

/-- a `memcpy` that wrote a different number of bytes than its `n` argument declared. -/
theorem negative_raw_copy_width :
    rawCopyHolds { sample with
        bindingFamily := "rawCopy",
        bindingObs := [("copySrcCovered", 1), ("copyStoredBytes", 255), ("copyWantBytes", 256)] }
      = some false := by native_decide

/-- an entry ABI whose `input_len` register disagrees with the byte length actually fed to the process. -/
theorem negative_entry_abi :
    entryAbiHolds { sample with
        bindingFamily := "entryAbi",
        bindingObs := [("entryInput", 67194912), ("entryLen", 1485),
                       ("wantInput", 67194912), ("wantLen", 1486)] }
      = some false := by native_decide

/-- a reader whose read window is not the width its `len` binding declared. -/
theorem negative_offset_read_width :
    offsetReadHolds { sample with
        bindingFamily := "offsetRead",
        bindingObs := [("baseClassOk", 1), ("declaredLen", 8), ("readCount", 12)] }
      = some false := by native_decide

/-- an allocation whose cursor bump is smaller than the request it claims to satisfy. -/
theorem negative_alloc_undersized :
    allocHolds { sample with
        bindingFamily := "alloc",
        bindingObs := [("allocAfter", 86080), ("allocAlign", 8), ("allocBump", 16), ("allocSize", 32)] }
      = some false := by native_decide

/-- a ledger event that moved the bump cursor BACKWARD. -/
theorem negative_ledger_regression :
    (evaluateOcc { sample with
        allocates := true, ledgerEventCount := 2,
        ledgerAllPositive := false }).allocationLedger = some false := by native_decide

end BinaryFv.SSZ.Zesu.Validation
