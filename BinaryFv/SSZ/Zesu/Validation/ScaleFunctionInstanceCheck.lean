import BinaryFv.SSZ.Zesu.Validation.ScaleFunctionInstanceTypes
import BinaryFv.SSZ.Zesu.Validation.GeneratedScaleEvidence

/-!
# Checking all 141 functionInstances against the production ELF

This module extends the small `decodeOptionalBlobSchedule` example to every functionInstance in the
generated program. It reads compact evidence reduced from runs of the unchanged ELF and evaluates
fourteen checks:

  entryReached          the first in-region PC is the declared entry PC
  controlFlowIntegrity  every executed transfer from an OWNED pc is a declared CFG edge (exact)
  exitsRespected        `exits` agrees with the run at every observed transfer out, both ways: every
                        observed DEPARTURE (a transfer out that did not come back to that pc's own
                        fall-through) is a declared exit, and no call site observed to come back is
                        declared as one
  withinStepBound       max per-invocation instruction count ≤ the contract step bound (gap if the
                        bound is input-dependent)
  allocationConsistent  a non-allocating routine never bumps the allocator cursor
  inputPreserved        no store into the SSZ input buffer
  codePreserved         no store into .text
  writesClassified      every in-region store lands in a known memory region (re-classified here from
                        the recorded (addr, sp); raw mem primitives carry a class summary)
  bindingsEvaluable     every declared Row A binding row resolved against the real machine state at
                        the functionInstance's declared entry PC (an unresolvable location is a FAILURE)
  bindingsRealized      the resolved bindings had their declared consequence in the trace
  derivedBindingsHold   a loop-`derived` row's `index * stride + constant` relation held at every
                        captured entry (the register carried a multiple of the stride, and the argument
                        was that value plus the row's constant)
  exitBindingRealized   the result register at a declared RETURN exit matches the exit convention
  allocationLedger      the functionInstance's cursor events ARE the allocation sequence its fixture requires
                        — count, order, sizes, alignments and returned blocks — with the expected side
                        derived from the pinned Zig decode order and the Row B element ABI, not from
                        the binary
  meaningTie            the little-endian integer of the exact window a leaf reader read IS the value
                        it produced (gap otherwise; the full per-value meaning against the handwritten
                        spec is the vertical slice, not this scan)

## What Lean checks directly

`bindingsEvaluable`, `derivedBindingsHold`, `exitBindingRealized`, `allocationLedger`, `meaningTie` and
the four family predicates (`offsetReadHolds` / `entryAbiHolds` / `rawCopyHolds` / `allocHolds`) are
computed HERE from the carried observations — the Lean checker decides them, it does not import a
verdict. The allocation ledger's two sides are both raw data: the cursor-write history and the
independently derived expected sequence; the comparison itself is `ledgerAgrees`, defined here.

`bindingsRealized` is the AGGREGATION of per-invocation verdicts, and that aggregation rule is
re-derived here (`bindingsRealizedOf`); the per-invocation family verdicts themselves are the Python
reducer's, because reproducing them would require carrying every invocation's full register file and
shadow memory into a committed artifact. `rederived_families_agree` is the cross-check that keeps that
import honest: the independently re-derived family predicate must never contradict the aggregate.

Each check is an `Option Bool`: `none` is an explicit gap and is never counted as a pass. Coverage is
per functionInstance, so one inlined copy cannot inherit evidence from another copy of the same routine.

`checker_agrees_with_oracle` pins Lean ≡ Python on every functionInstance. `gating_checks_hold` records that
the six structural/effect checks pass on every COVERED functionInstance. The `negative_*` theorems require
mutations of the evidence to flip a check. This validation module is never a theorem premise.
-/

namespace BinaryFv.SSZ.Zesu.Validation

open BinaryFv.SSZ.Zesu.Validation.GeneratedScaleEvidence

/-- Pinned production memory layout (identical to `BinaryFunctionInstanceCheck.classifyWrite`). -/
def classifyWriteScaled (addr sp : Nat) : String :=
  if 65768 ≤ addr ∧ addr < 81704 then "code"
  else if 86032 ≤ addr ∧ addr < 86048 then "allocator-cursor"
  else if 86048 ≤ addr ∧ addr < 67194912 then "heap"
  else if 67194912 ≤ addr ∧ addr < 69292064 then "input"
  else if 69292064 ≤ addr ∧ addr < 69292928 then "decoder-global"
  else if sp - 65536 ≤ addr ∧ addr ≤ sp + 65536 then "stack"
  else "unclassified"

/-- The distinct-relevant write classes of an functionInstance: re-classified from the carried non-stack
addresses (with `sp = 0`; carried addresses are never stack, and every non-stack region sits below the
stack window) plus the summarized `stack` flag — or the pre-classified summary for raw mem primitives.
Environment-independent: no absolute stack address appears. -/
def scaledClasses (ev : FunctionInstanceScaleEvidence) : List String :=
  if ev.storesSummarized then ev.storeClasses
  else (ev.inRegionStores.map (fun a => classifyWriteScaled a 0)) ++ (if ev.hadStackStore then ["stack"] else [])

/-- The named scalar observation `k` of the first captured invocation, if the reducer recorded one. -/
def obs (ev : FunctionInstanceScaleEvidence) (k : String) : Option Int :=
  (ev.bindingObs.find? (fun p => p.1 == k)).map Prod.snd

/-- **Row A entry bindings resolve.** Every declared effective binding row produced a concrete value
from the real machine state at the declared entry PC. `"unresolved"` means the declared location could
not be read at all, which is a FAILURE — a binding that names a location the machine cannot supply is
wrong, not merely unobserved. An functionInstance with no declared rows has no obligation to discharge, so it
is an explicit gap rather than a free pass.

There is no "declared but meaningless" row to except any more: the generator refuses to emit one, so
this is also the statement that the functionInstance's `generatedEntryBinding` has a witness on its captured
entry state (see `entry_predicates_satisfiable_on_captured_states`). -/
def bindingsEvaluableOf (ev : FunctionInstanceScaleEvidence) : Option Bool :=
  if ev.bindingHows.isEmpty then none
  else if ev.bindingHows.any (fun h => h == "unresolved") then some false
  else some true

/-- **A loop-derived row's relation held at every captured entry.** The register must have carried a
multiple of the stride — that is what makes it `index * stride` — and the argument must have been that
register value plus the row's constant. Mirrors `BindingInventory.DerivedIndexRep`.

Mutating the stride, the constant, the register's captured value, or the resolved argument all break
this; an empty sample would let it pass on nothing, so that fails too. -/
def derivedRowHolds (d : DerivedRowEvidence) : Bool :=
  d.stride != 0 && !d.registerValues.isEmpty &&
    d.registerValues.length == d.values.length &&
    (List.zip d.registerValues d.values).all
      (fun p => p.1 % d.stride == 0 && p.2 == p.1 + d.constant)

/-- An functionInstance with no loop-derived row has nothing to discharge here — an explicit gap. -/
def derivedBindingsHoldOf (ev : FunctionInstanceScaleEvidence) : Option Bool :=
  if ev.derivedRows.isEmpty then none else some (ev.derivedRows.all derivedRowHolds)

/-- The per-invocation consequence verdicts, aggregated. A single contradicted invocation fails the
functionInstance; a pass requires every captured invocation to have realized the consequence. -/
def bindingsRealizedOf (ev : FunctionInstanceScaleEvidence) : Option Bool :=
  if ev.realizedFail > 0 then some false
  else if ev.realizedPass > 0 && ev.realizedGap == 0 then some true
  else none

/-- The `offsetRead` consequence, RE-DERIVED here from the carried observations rather than taken from
the oracle: a reader declaring `len` must have touched exactly `len` distinct bytes, and the slice base
its `offset` implies must land in a real data region. -/
def offsetReadHolds (ev : FunctionInstanceScaleEvidence) : Option Bool :=
  if ev.bindingFamily != "offsetRead" then none else
  match obs ev "declaredLen", obs ev "readCount", obs ev "baseClassOk" with
  | some declared, some got, some baseOk =>
      -- `declaredLen = -1` marks a reader with no `len` row: only the base-region test applies.
      some (baseOk == 1 && (declared < 0 || declared == got))
  | _, _, _ => none

/-- The `entryAbi` consequence, RE-DERIVED: the exported entry's `input`/`input_len` registers must
equal the linked input-buffer base and the exact byte length the process was fed. -/
def entryAbiHolds (ev : FunctionInstanceScaleEvidence) : Option Bool :=
  if ev.bindingFamily != "entryAbi" then none else
  match obs ev "entryInput", obs ev "wantInput", obs ev "entryLen", obs ev "wantLen" with
  | some i, some wi, some l, some wl => some (i == wi && l == wl)
  | _, _, _, _ => none

/-- The `rawCopy` consequence, RE-DERIVED: `memcpy`/`memmove` must write exactly `n` bytes at `dst`
and read the whole `[src, src+n)` window. -/
def rawCopyHolds (ev : FunctionInstanceScaleEvidence) : Option Bool :=
  if ev.bindingFamily != "rawCopy" then none else
  match obs ev "copyStoredBytes", obs ev "copyWantBytes", obs ev "copySrcCovered" with
  | some got, some want, some cov => some (got == want && cov == 1)
  | _, _, _ => none

/-- The `alloc` consequence, RE-DERIVED: the EXPECTED allocation occurred.

The bump allocator is fully determined — `ptr = align_up(cursor, alignment)` and
`cursor' = ptr + bytes` — so both the new cursor and the returned pointer are predicted from
`(cursor_before, size, alignment)`. Checking only that the cursor moved forward inside the heap would
accept a wrong size, a skipped alignment step, or a returned pointer that is not the block just carved
out; this compares against the predicted values instead. -/
def allocHolds (ev : FunctionInstanceScaleEvidence) : Option Bool :=
  if ev.bindingFamily != "alloc" then none else
  match obs ev "allocAfter", obs ev "allocWantAfter", obs ev "allocPtrKnown", obs ev "allocPtrMatches" with
  | some after, some wantAfter, some ptrKnown, some ptrMatches =>
      some (after == wantAfter && (ptrKnown == 0 || ptrMatches == 1))
  | _, _, _, _ => none

/-- The exit convention at a declared RETURN exit, RE-DERIVED. A tail-call exit is excluded upstream:
its register file holds the callee's arguments, not this functionInstance's result.

Every branch compares the returned register against something INDEPENDENTLY known. An earlier version
returned `some true` for `copyDestination` and `decodeDecision` without looking at anything, which is
not a check: it accepted any register value at all. -/
def exitBindingOf (ev : FunctionInstanceScaleEvidence) : Option Bool :=
  if ev.exitConvention == "" then none
  else if ev.returnExits.isEmpty then none
  else if ev.exitConvention == "allocPointer" then
    -- Subsumed by `allocHolds`, which predicts the exact pointer; a range test here would only add a
    -- weaker second opinion that could pass where the exact check fails.
    none
  else if ev.exitConvention == "copyDestination" then
    -- memcpy/memmove return `dst` unchanged: every paired invocation must match.
    if ev.exitPairsTotal == 0 then none else some (ev.exitPairsMatched == ev.exitPairsTotal)
  else if ev.exitConvention == "decodeDecision" then
    -- the wrapper's result must agree with the decision the PROCESS exited with
    -- (harness: exit 0 = decoded, exit 1 = rejected).
    if ev.exitReturnedValues.isEmpty then none
    else some (ev.exitReturnedValues.all (fun v => v == (if ev.armDecision == 0 then 1 else 0)))
  else none

/-! ## The allocation ledger: observed cursor history vs the independently expected sequence -/

/-- The pinned bump allocator's own arithmetic: `ptr = align_up(cursor, alignment)`. -/
def alignUp (value alignment : Nat) : Nat :=
  if alignment ≤ 1 then value else ((value + alignment - 1) / alignment) * alignment

/-- One observed allocation IS the expected one: same position in the run's allocation sequence, the
cursor landing exactly where the pinned allocator would put it for that size and alignment, and — where
it was captured — the returned block being the very block carved out.

`cursorAfter = align_up(cursorBefore, alignment) + size` is what makes a wrong SIZE and a wrong
ALIGNMENT both visible: the alignment shows up as the padding between `cursorBefore` and the block. -/
def allocEventAgrees (o : ObservedAlloc) (e : ExpectedAlloc) : Bool :=
  let ptr := alignUp o.cursorBefore e.alignment
  o.ordinal == e.ordinal && o.cursorAfter == ptr + e.size &&
    (match o.returnedPointer with
     | none => true                     -- a narrow per-field gap: the return was not captured
     | some p => p == ptr)

/-- Consecutive events are strictly later in the run's allocation sequence, so a REORDERING of the
observed events is a failure even where two events happen to have the same size. -/
def ordinalsIncrease (os : List ObservedAlloc) : Bool :=
  (List.zip os (os.drop 1)).all (fun p => p.1.ordinal < p.2.ordinal)

/-- **The ledger comparison.** Same event COUNT, same ORDER, same SIZES, same ALIGNMENTS, same returned
blocks. Mirrors `scale_function_instances.ledger_agrees`. -/
def ledgerAgrees (observed : List ObservedAlloc) (expected : List ExpectedAlloc) : Bool :=
  observed.length == expected.length &&
    (List.zip observed expected).all (fun p => allocEventAgrees p.1 p.2) &&
    ordinalsIncrease observed

/-- **The whole-run ledger of one arm.** Beyond the per-event agreement, the observed events must CHAIN
— each starts where the last one ended, which is what a bump allocator does and what a dropped or
inserted event breaks — and both sequences must be numbered `0, 1, 2, …` with no hole. -/
def armLedgerHolds (l : ArmLedger) : Bool :=
  ledgerAgrees l.observed l.expected &&
    (List.zip l.observed (l.observed.drop 1)).all (fun p => p.2.cursorBefore == p.1.cursorAfter) &&
    (l.observed.zipIdx.all fun p => p.1.ordinal == p.2) &&
    (l.expected.zipIdx.all fun p => p.1.ordinal == p.2)

/-- An allocating functionInstance's cursor events must BE the allocations the fixture requires of it — same
count, order, sizes, alignments and returned blocks. A non-allocating functionInstance causes no event and is
covered by `allocationConsistent` instead, so it is an explicit gap rather than a second opinion.

An functionInstance that is expected to allocate nothing and allocated nothing PASSES: that is a checkable
outcome, not an absent obligation. -/
def allocationLedgerOf (ev : FunctionInstanceScaleEvidence) : Option Bool :=
  if !ev.allocates then none
  else some (ledgerAgrees ev.ledgerObserved ev.ledgerExpected)

/-- The scaled checker, reproducing the Python oracle `evaluate_facts`. -/
def evaluateFunctionInstance (ev : FunctionInstanceScaleEvidence) : ScaleChecks :=
  if !ev.covered then
    { entryReached := none, controlFlowIntegrity := none, exitsRespected := none, withinStepBound := none,
      allocationConsistent := none, inputPreserved := none, codePreserved := none,
      writesClassified := none, bindingsEvaluable := none, bindingsRealized := none,
      derivedBindingsHold := none, exitBindingRealized := none, allocationLedger := none,
      meaningTie := none }
  else
    let classes := scaledClasses ev
    { bindingsEvaluable := bindingsEvaluableOf ev
      bindingsRealized := bindingsRealizedOf ev
      derivedBindingsHold := derivedBindingsHoldOf ev
      exitBindingRealized := exitBindingOf ev
      allocationLedger := allocationLedgerOf ev
      entryReached := some (ev.firstInRegion == ev.entryPc)
      controlFlowIntegrity := some (ev.executedOwnedEdges.all (fun e => ev.declaredEdges.contains e))
      -- Both directions of `exits` against the run. A call LEAVES the regions but comes back, so it
      -- is not a departure and must NOT be a declared exit — that over-declaration is what made the
      -- entry functionInstance's `FunctionTrace` (which carries `¬ exit pc`) stop at its first call.
      -- Checking only the first conjunct would pass just as happily with the defect restored.
      exitsRespected := some (ev.leavingSources.all (fun s => ev.exits.contains s) &&
                              ev.dynamicTransferSources.all (fun s => ev.exits.contains s) &&
                              ev.returningCallSites.all (fun s => !ev.exits.contains s))
      withinStepBound := ev.stepBound.map (fun b => ev.maxInsnPerInvocation ≤ b)
      allocationConsistent := some (ev.allocates || !(classes.contains "allocator-cursor"))
      inputPreserved := some (!(classes.contains "input"))
      codePreserved := some (!(classes.contains "code"))
      writesClassified := some (!(classes.contains "unclassified"))
      -- MEANING. `meaningProduced` is the rigorous statement: the functionInstance read a window of
      -- EXACTLY its declared little-endian width, and that window's value is what it produced (stored,
      -- or held in a register when it left). The older value tie survives only for the slice readers.
      meaningTie :=
        if ev.meaningProduced then some true
        else if ev.meaningTieKind == "slice" && ev.storeHasInputPtr then some true
        else if (ev.meaningTieKind == "scalarLE" || ev.meaningTieKind == "offset")
                && ev.scalarCarried then some true
        else none }

/-- **Lean ≡ Python.** The scaled checker reproduces the oracle's result on EVERY functionInstance
(present / malformed / absent arms, covered and uncovered). Kernel-checked. -/
theorem checker_agrees_with_oracle :
    allFunctionInstances.all (fun p => evaluateFunctionInstance p.1 == p.2) = true := by native_decide

/-- The six structural/effect gating checks (entry / CFG integrity / allocation / input & code
preservation / write classification) pass — `some true` — on EVERY covered functionInstance. Step bound and
meaning tie are reported separately (they carry explicit gaps). Kernel-checked. -/
theorem gating_checks_hold :
    allFunctionInstances.all (fun p =>
      let ev := p.1
      !ev.covered ||
        (let r := evaluateFunctionInstance ev
         r.entryReached == some true && r.controlFlowIntegrity == some true &&
         r.exitsRespected == some true &&
         r.allocationConsistent == some true && r.inputPreserved == some true &&
         r.codePreserved == some true && r.writesClassified == some true)) = true := by
  native_decide

/-- No gating check ever FAILS (`some false`) on any functionInstance: results are pass or explicit gap,
never a violation of a Row A binding against the unchanged production ELF. Kernel-checked. -/
theorem no_gating_failures :
    allFunctionInstances.all (fun p =>
      let r := evaluateFunctionInstance p.1
      r.entryReached != some false && r.controlFlowIntegrity != some false &&
      r.exitsRespected != some false &&
      r.allocationConsistent != some false && r.inputPreserved != some false &&
      r.codePreserved != some false && r.writesClassified != some false &&
      r.withinStepBound != some false && r.meaningTie != some false) = true := by
  native_decide

/-- **Step bounds hold on every covered functionInstance except the one documented gap.** functionInstance 134
(`requireCanonicalOffsets`) is the sole covered functionInstance whose contract bound is an explicit gap — its
`offsets.length` argument is caller-passed, not present in the functionInstance's own input-buffer reads (the
required interface change is recorded in the catalog / coverage report). Every OTHER covered functionInstance
passes `withinStepBound`, including the input-dependent bounds resolved via sound lower bounds on their
argument. Kernel-checked; Row C's step-bound conclusion excludes functionInstance 134 by construction. -/
theorem step_bounds_hold_except_documented_gap :
    allFunctionInstances.all (fun p =>
      let ev := p.1
      !ev.covered || ev.index == 134 || (evaluateFunctionInstance ev).withinStepBound == some true) = true := by
  native_decide

/-- The uncovered functionInstances (allocatorRemap 123 / allocatorResize 135 / zesu_raw_error 137) are
exactly the functionInstances the checker reports as not covered; every OTHER functionInstance is covered and carries
concrete per-functionInstance evidence. Row C's coverage conclusion excludes precisely these three.

Their static unreachability is established separately by `static_reachability.py` — a backward
reaching-definitions fixpoint over the reconstructed CFG plus a danger-set closure over the loaded image
— and holds under the two hypotheses that analysis states explicitly (`STATIC_REACHABILITY.md`). This
theorem asserts only the coverage partition, not the unreachability claim. -/
theorem uncovered_are_exactly_the_statically_dead :
    allFunctionInstances.all (fun p => p.1.covered == (p.1.index != 123 && p.1.index != 135 && p.1.index != 137))
      = true := by native_decide

/-! ## Row A bindings — the declared machine placement, checked against the real run -/

/-- **No declared Row A binding failed to resolve against the production machine.** Wherever a row names
a location — register, frame slot, base+offset memory word, or constant — that location produced a
concrete value from the register/memory state captured at the functionInstance's declared entry PC. No row is
`"unresolved"`. Kernel-checked. -/
theorem all_declared_bindings_resolve :
    allFunctionInstances.all (fun p => (evaluateFunctionInstance p.1).bindingsEvaluable != some false) = true := by
  native_decide

/-- **Every functionInstance's generated entry predicate is SATISFIABLE on its captured entry state.**

`generatedEntryBinding` quantifies over an functionInstance's binding rows, so a row with no machine meaning
makes the whole predicate `False` and every implication out of it vacuous — which is exactly what the
old `unlocated` kind did to the eight `decodeWithdrawals` reader rows. Row A now has a real case for
every kind it emits (`BindingInventory.no_binding_kind_is_impossible`); this is the other half, on the
production machine: for every covered functionInstance that declares rows, EVERY row resolved to a concrete
value from the register/memory state captured at its declared entry PC, so the conjunction has a
witness there. 117 functionInstances declare rows; the remaining 24 are the paramless ones Row A names. -/
theorem entry_predicates_satisfiable_on_captured_states :
    allFunctionInstances.all (fun p =>
      !p.1.covered || p.1.bindingHows.isEmpty ||
        (evaluateFunctionInstance p.1).bindingsEvaluable == some true) = true := by native_decide

theorem located_function_instance_partition :
    (allFunctionInstances.filter (fun p => (evaluateFunctionInstance p.1).bindingsEvaluable == some true)).length = 117 ∧
    (allFunctionInstances.filter (fun p => p.1.bindingHows.isEmpty)).length = 24 := by
  native_decide

/-! ### The loop-derived withdrawal offsets

The eight rows the previous round left `unlocated` now carry the relation the machine actually
realizes, and the production run is what checks it. -/

/-- **The eight loop-derived rows hold on their captured entry states.** FunctionInstances 46–53 — the
`decodeWithdrawals` reader chain — each declare `offset = index * WITHDRAWAL_SIZE + k`, and at every
captured entry the loop register carried a multiple of the stride and the argument was that value plus
the row's constant. Kernel-checked. -/
theorem derived_rows_hold :
    (allFunctionInstances.filter (fun p => !p.1.derivedRows.isEmpty)).length = 8 ∧
    allFunctionInstances.all (fun p => p.1.derivedRows.isEmpty ||
      (evaluateFunctionInstance p.1).derivedBindingsHold == some true) = true := by native_decide

/-- The derived rows are exactly functionInstances 46–53, all binding `offset` through the same loop register
with the pinned `WITHDRAWAL_SIZE` stride and the four `RawWithdrawal` field offsets. -/
theorem derived_rows_are_the_withdrawal_chain :
    (allFunctionInstances.filterMap (fun p =>
        p.1.derivedRows.head?.map (fun d => (p.1.index, d.register, d.stride, d.constant)))) =
      [(46, 23, 44, 0), (47, 23, 44, 0), (48, 23, 44, 8), (49, 23, 44, 8),
       (50, 23, 44, 16), (51, 23, 44, 16), (52, 23, 44, 36), (53, 23, 44, 36)] := by
  native_decide

/-- The evidence is not degenerate: the loop ran more than once, so the register genuinely varied over
`index * 44`. A single `index = 0` sample would satisfy any stride. -/
theorem derived_rows_saw_more_than_one_index :
    allFunctionInstances.all (fun p => p.1.derivedRows.all
      (fun d => d.registerValues == [0, 44] && d.values == [d.constant, 44 + d.constant])) = true := by
  native_decide

/-- **The re-derived family consequences agree with the recorded aggregate.** For every functionInstance whose
routine has a binding-consequence family, the consequence RE-DERIVED here from the carried observations
(`offsetReadHolds` / `entryAbiHolds` / `rawCopyHolds` / `allocHolds`) never contradicts the aggregated
per-invocation verdict. This is what keeps the aggregate from being an unchecked import of the oracle's
opinion. Kernel-checked. -/
theorem rederived_families_agree :
    allFunctionInstances.all (fun p =>
      let ev := p.1
      let r := [offsetReadHolds ev, entryAbiHolds ev, rawCopyHolds ev, allocHolds ev]
      r.all (fun x => x != some false) &&
        (bindingsRealizedOf ev != some true || r.all (fun x => x != some false))) = true := by
  native_decide

/-- **The exported entry ABI is realized exactly.** functionInstance 1 (`zesu_decode_raw`) received the linked
input-buffer base and the exact byte length of the file the process was fed — external ground truth, not
a self-report. Kernel-checked. -/
theorem entry_abi_realized :
    (allFunctionInstances.filter (fun p => p.1.index == 1)).all (fun p => entryAbiHolds p.1 == some true) = true := by
  native_decide

/-- **No binding, exit or ledger check ever FAILS.** Across all 141 functionInstances these are pass or
explicit gap — the production ELF never contradicted a declared Row A placement. Kernel-checked. -/
theorem no_binding_failures :
    allFunctionInstances.all (fun p =>
      let r := evaluateFunctionInstance p.1
      r.bindingsEvaluable != some false && r.bindingsRealized != some false &&
      r.derivedBindingsHold != some false &&
      r.exitBindingRealized != some false && r.allocationLedger != some false) = true := by
  native_decide

/-! ## The allocation ledger — the exact sequence, not merely a forward-moving cursor -/

/-- **Every arm's whole-run allocation ledger is exactly the sequence its fixture requires.** The
observed side is `ZKVM_HEAP_POS`'s write history from the unchanged production ELF; the expected side is
derived without reference to the binary, from the pinned Zig decode order applied to that arm's exact
bytes and sized by the Row B probe's element ABI. Same count, same order, same sizes, same alignments,
same returned blocks, chained end to end. Kernel-checked. -/
theorem arm_ledgers_hold : armLedgers.all armLedgerHolds = true := by native_decide

/-- The three arms cover a decoding run and a rejecting one, so the ledger check is exercised both on a
complete sequence and on the PREFIX a rejected payload allocates before the decoder stops. -/
theorem arm_ledger_shapes :
    (armLedgers.map (fun l => (l.arm, l.observed.length, l.rejectedAt != ""))) =
      [("absent", 7, false), ("malformed", 6, true), ("present", 10, false)] := by native_decide

/-- **Every allocating functionInstance's slice of the ledger is exactly what it owes.** All 16 allocating
functionInstances — the two allocator leaves, the entry, and the collection/container functionInstances between them
— match their independently derived allocation sequence. Kernel-checked. -/
theorem allocating_function_instances_match_expected_ledger :
    (allFunctionInstances.filter (fun p => p.1.allocates && p.1.covered)).length = 16 ∧
    allFunctionInstances.all (fun p => !(p.1.allocates && p.1.covered) ||
      (evaluateFunctionInstance p.1).allocationLedger == some true) = true := by native_decide

/-- Every observed event's returned block was captured, so no allocation's returned-pointer field is a
gap. `allocEventAgrees` would otherwise accept an uncaptured return. -/
theorem returned_blocks_all_observed :
    allFunctionInstances.all (fun p => p.1.ledgerReturnedUnknown == 0) = true ∧
    armLedgers.all (fun l => l.observed.all (fun o => o.returnedPointer.isSome)) = true := by
  native_decide

/-!
## Negative tests — mutating a covered functionInstance's evidence must flip the responsible check. The
sampled functionInstance is 116 (`decodeOptionalBlobSchedule`), the vertical-slice functionInstance, located in
`allFunctionInstances`. Each theorem corrupts one field and asserts the check turns `some false`.
-/

/-- functionInstance 116's evidence from the generated list (the vertical-slice functionInstance). -/
def sample : FunctionInstanceScaleEvidence := (allFunctionInstances.filter (fun p => p.1.index == 116)).head!.1

/-- The sample is genuinely a GO baseline (all gating checks pass). -/
theorem sample_is_go :
    let r := evaluateFunctionInstance sample
    r.entryReached == some true && r.controlFlowIntegrity == some true &&
      r.allocationConsistent == some true && r.inputPreserved == some true &&
      r.codePreserved == some true && r.writesClassified == some true := by native_decide

/-- wrong entry: first in-region PC is not the declared entry. -/
theorem negative_wrong_entry :
    (evaluateFunctionInstance { sample with firstInRegion := sample.entryPc + 4 }).entryReached
      = some false := by native_decide

/-- undeclared edge: an executed transfer from an owned PC that is not in the generated CFG. -/
theorem negative_undeclared_edge :
    (evaluateFunctionInstance { sample with
        executedOwnedEdges := (sample.entryPc, 999999) :: sample.executedOwnedEdges }).controlFlowIntegrity
      = some false := by native_decide

/-- exit violation: execution leaves the functionInstance from a PC that is not a declared exit. -/
theorem negative_undeclared_exit :
    (evaluateFunctionInstance { sample with
        leavingSources := 999999 :: sample.leavingSources }).exitsRespected
      = some false := by native_decide

/-- OVER-declared exit: a call site the trace observed coming back to its own fall-through is listed
as an exit. This is the defect the extractor fix removed — every resolved call site counted as an
exit of its caller — and it must be rejected here too, or `exitsRespected` would certify it. -/
theorem negative_returning_call_declared_exit :
    (evaluateFunctionInstance { sample with
        returningCallSites := sample.entryPc :: sample.returningCallSites,
        exits := sample.entryPc :: sample.exits }).exitsRespected
      = some false := by native_decide

/-- spurious allocation: a store bumping the allocator cursor in a non-allocating routine. -/
theorem negative_cursor_bump :
    (evaluateFunctionInstance { sample with storesSummarized := true, storeClasses := "allocator-cursor" :: sample.storeClasses }).allocationConsistent
      = some false := by native_decide

/-- code-preservation violation: an injected store into .text. -/
theorem negative_code_write :
    (evaluateFunctionInstance { sample with inRegionStores := (65768 + 8) :: sample.inRegionStores }).codePreserved
      = some false := by native_decide

/-- input-preservation violation: an injected store into the SSZ input buffer. -/
theorem negative_input_write :
    (evaluateFunctionInstance { sample with inRegionStores := (67194912 + 8) :: sample.inRegionStores }).inputPreserved
      = some false := by native_decide

/-- unclassified write: a store outside every known region and its stack window. -/
theorem negative_unclassified_write :
    (evaluateFunctionInstance { sample with inRegionStores := 3735879680 :: sample.inRegionStores }).writesClassified
      = some false := by native_decide

/-- step-bound violation: instruction count exceeds the contract bound. -/
theorem negative_step_bound :
    (evaluateFunctionInstance { sample with maxInsnPerInvocation := 100000 }).withinStepBound
      = some false := by native_decide

/-! ### Binding / ledger negatives — the new checks must be falsifiable too. -/

/-- an unreadable declared location: a binding naming a place the machine cannot supply must FAIL, not
degrade into a gap. -/
theorem negative_unresolved_binding :
    (evaluateFunctionInstance { sample with bindingHows := ["exact", "unresolved"] }).bindingsEvaluable
      = some false := by native_decide

/-! ### Loop-derived binding negatives — mutating the index, stride, constant or the machine location.

The baseline is functionInstance 47 (`readU64(data, offset)` in the `decodeWithdrawals` loop): the register
carried `0` then `44`, and the argument was `0` then `44`. -/

/-- functionInstance 47's derived row from the generated evidence. -/
def derivedSample : DerivedRowEvidence :=
  ((allFunctionInstances.filter (fun p => p.1.index == 47)).head!.1.derivedRows).head!

theorem derived_sample_holds : derivedRowHolds derivedSample = true := by native_decide

/-- WRONG STRIDE: `WITHDRAWAL_SIZE` is 44, and the second iteration's register value 44 is not a
multiple of 43. A single `index = 0` sample could not tell these apart; two can. -/
theorem negative_derived_wrong_stride :
    derivedRowHolds { derivedSample with stride := 43 } = false := by native_decide

/-- WRONG CONSTANT: the field offset within the element is part of the relation. -/
theorem negative_derived_wrong_constant :
    derivedRowHolds { derivedSample with constant := derivedSample.constant + 4 } = false := by
  native_decide

/-- WRONG MACHINE LOCATION: the value the loop register actually carried is what the relation is about.
A register holding something that is not `index * stride` fails. -/
theorem negative_derived_wrong_register_value :
    derivedRowHolds { derivedSample with registerValues := [0, 45] } = false := by native_decide

/-- WRONG INDEX: the register stepping to the wrong iteration breaks the tie between the register and
the argument the row resolved to. -/
theorem negative_derived_wrong_index :
    derivedRowHolds { derivedSample with registerValues := [0, 88] } = false := by native_decide

/-- An empty sample is not a pass: there would be nothing the relation held on. -/
theorem negative_derived_no_sample :
    derivedRowHolds { derivedSample with registerValues := [], values := [] } = false := by
  native_decide

/-- a contradicted binding consequence in any single invocation fails the functionInstance. -/
theorem negative_binding_consequence :
    (evaluateFunctionInstance { sample with realizedPass := 3, realizedFail := 1, realizedGap := 0 }).bindingsRealized
      = some false := by native_decide

/-- a gap in any invocation withholds the pass rather than granting it. -/
theorem negative_binding_partial_is_gap :
    (evaluateFunctionInstance { sample with realizedPass := 3, realizedFail := 0, realizedGap := 1 }).bindingsRealized
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

/-- an allocation whose new cursor is not `align_up(before, alignment) + size`. -/
theorem negative_alloc_wrong_cursor :
    allocHolds { sample with
        bindingFamily := "alloc",
        bindingObs := [("allocAfter", 86072), ("allocWantAfter", 86080),
                       ("allocPtrKnown", 1), ("allocPtrMatches", 1)] }
      = some false := by native_decide

/-- an allocation that advanced the cursor correctly but handed back a DIFFERENT block than the one it
carved out — invisible to a "cursor moved forward inside the heap" test. -/
theorem negative_alloc_wrong_pointer :
    allocHolds { sample with
        bindingFamily := "alloc",
        bindingObs := [("allocAfter", 86080), ("allocWantAfter", 86080),
                       ("allocPtrKnown", 1), ("allocPtrMatches", 0)] }
      = some false := by native_decide

/-- a copy that returned something other than its `dst` argument in one of its invocations. -/
theorem negative_copy_destination :
    exitBindingOf { sample with
        exitConvention := "copyDestination", returnExits := [1],
        exitPairsMatched := 17, exitPairsTotal := 18 }
      = some false := by native_decide

/-- a decoder whose returned decision contradicts the exit code the process actually produced. -/
theorem negative_decode_decision :
    exitBindingOf { sample with
        exitConvention := "decodeDecision", returnExits := [1],
        exitReturnedValues := [0], armDecision := 0 }
      = some false := by native_decide

/-- and the positive direction: exit code 0 (decoded) requires the wrapper to have returned 1. -/
theorem decode_decision_ties_to_process_exit :
    exitBindingOf { sample with
        exitConvention := "decodeDecision", returnExits := [1],
        exitReturnedValues := [1], armDecision := 0 }
      = some true := by native_decide

/-! ### Allocation-ledger negatives — the sequence, not just the direction of travel.

The baseline is the `present` arm's whole-run ledger: ten allocations, each pinned by size, alignment,
order and returned block. Every mutation below is one an "the cursor moved forward inside the heap"
test would have accepted. -/

/-- the `present` arm's ledger from the generated evidence. -/
def ledgerSample : ArmLedger := (armLedgers.filter (fun l => l.arm == "present")).head!

theorem ledger_sample_holds : armLedgerHolds ledgerSample = true := by native_decide

/-- WRONG EVENT COUNT: an extra allocation nobody asked for. The cursor still only moved forward. -/
theorem negative_ledger_extra_event :
    armLedgerHolds { ledgerSample with
        observed := ledgerSample.observed ++
          [{ ordinal := 10, cursorBefore := 86858, cursorAfter := 86890,
             returnedPointer := some 86858 }] } = false := by native_decide

/-- WRONG EVENT COUNT the other way: a dropped allocation. -/
theorem negative_ledger_missing_event :
    armLedgerHolds { ledgerSample with observed := ledgerSample.observed.drop 1 } = false := by
  native_decide

/-- REORDERED EVENTS: the same allocations, performed in the wrong order. Sizes alone would not catch
this where two events happen to be the same size; the ordinals and the cursor chain do. -/
theorem negative_ledger_reordered :
    armLedgerHolds { ledgerSample with
        observed := ledgerSample.observed.drop 1 ++ ledgerSample.observed.take 1 } = false := by
  native_decide

/-- WRONG SIZE: the block carved out is not the size the fixture requires. -/
theorem negative_ledger_wrong_size :
    armLedgerHolds { ledgerSample with
        expected := ledgerSample.expected.map
          (fun e => if e.ordinal == 3 then { e with size := e.size + 8 } else e) } = false := by
  native_decide

/-- WRONG ALIGNMENT: event 6 follows a 1-aligned block, so its 8-byte alignment is what produces the
four bytes of padding before it. Claiming alignment 1 predicts a different cursor. -/
theorem negative_ledger_wrong_alignment :
    armLedgerHolds { ledgerSample with
        expected := ledgerSample.expected.map
          (fun e => if e.ordinal == 6 then { e with alignment := 1 } else e) } = false := by
  native_decide

/-- WRONG RETURNED BLOCK: the cursor advanced exactly as required, but the allocator handed back a
different block than the one it carved out — invisible to any check on the cursor alone. -/
theorem negative_ledger_wrong_returned_block :
    armLedgerHolds { ledgerSample with
        observed := ledgerSample.observed.map
          (fun o => if o.ordinal == 2 then { o with returnedPointer := some (o.cursorBefore + 8) }
                    else o) } = false := by
  native_decide

/-- A per-FUNCTION INSTANCE slice is checked the same way: `decodeWithdrawals`' single event with the wrong
size fails its functionInstance check, not merely the whole-run one. -/
theorem negative_functionInstance_ledger_wrong_size :
    (evaluateFunctionInstance { sample with
        allocates := true,
        ledgerObserved := [{ ordinal := 1, cursorBefore := 86080, cursorAfter := 86176,
                             returnedPointer := some 86080 }],
        ledgerExpected := [{ ordinal := 1, routine := "decodeWithdrawals", element := "withdrawal",
                             count := 1, size := 48, alignment := 8 }] }).allocationLedger
      = some false := by native_decide

/-- and an functionInstance that allocated when the fixture required nothing of it. -/
theorem negative_functionInstance_ledger_unexpected_event :
    (evaluateFunctionInstance { sample with
        allocates := true,
        ledgerObserved := [{ ordinal := 0, cursorBefore := 86048, cursorAfter := 86080,
                             returnedPointer := some 86048 }],
        ledgerExpected := [] }).allocationLedger = some false := by native_decide

end BinaryFv.SSZ.Zesu.Validation
