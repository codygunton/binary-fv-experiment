import BinaryFv.Keccak.Reth.Artifact.Analysis.StackFlowDiagnostics
import BinaryFv.Keccak.Reth.Proof.Common.StackFrames
import BinaryFv.Keccak.Reth.Artifact.Analysis.StackFlow
import BinaryFv.RiscV.Step.TryStepStackAddi

/-!
# Conditional stack-window machinery, and diagnostic static stack-flow summaries

## Scope: what this module does *not* prove

**This module does not establish a stack bound for the binary.**  The concrete, binary-wide
stack-safety proof is explicitly **deferred to the sponge/caller trace stage**
(`keccak-sponge-contract`), which is where the actual call paths and their prologues exist and where
each budget premise can be discharged per call site against a real trace.

Two independent kinds of content live here, and they must not be confused:

1. **Conditional runtime machinery** — `SpDepthInWindow` with `.alloc` / `.toWindow` / `.delta_le` /
   `.entry`, `prologue_toNat`, `tryStepStackAddiWindow`, `tryStepStackAddiRetiresInWindow`, and the
   `*_of_budget` frame exports.  These are genuine theorems about the generated semantics, but the
   budget is always an **input**: it is either carried inside the `SpDepthInWindow` invariant
   (`used ≤ stackPageSize`) or taken as an explicit premise `used + delta ≤ stackPageSize` for each
   allocation.  Either way the caller supplies it.  Given it, an actual generated
   `addi sp, sp, -delta` prologue step provably preserves the window, and the raw inequalities that
   `BinaryFv.Keccak.Reth.Proof.Common.StackFrames` merely *assumes* (`stackRange.start ≤ spLow`, `spLow ≤ spHigh`,
   `spHigh ≤ stackTop`, nested `eHigh ≤ cLow`) are discharged *from that input*.  Nothing in this
   module establishes the budget for this binary.  (`SpDepthInWindow.entry` is the one unconditional
   lemma — it merely seeds `used = 0` at the stack top, which asserts nothing about any call chain.)

2. **Diagnostic evidence** — `frontierSummaryTotalDownwardDelta`,
   `frontierSummaryMaxSingleDownwardDelta`, and the `diagnostic_*` facts about them.  These are
   closed parser facts about the **frontier-truncated** closure summaries of
   `BinaryFv.Keccak.Reth.Artifact.Analysis.StackFlow`.  As that module states, `maximumExploredDownwardDelta` is not a
   local, runtime, or global stack bound: calls and other frontiers deliberately truncate the
   explored state set.  Summing truncated per-function summaries is therefore **evidence about a
   truncated exploration, not a theorem about all call paths**.  Accordingly these facts are named
   `diagnostic_*`, and none of them is used to discharge a budget premise anywhere.

The gap between (2) and (1) — showing that some concrete, reachable call chain's accumulated depth
actually satisfies the budget — is exactly the deferred obligation.  Closing it requires discharging
the recorded frontiers and following the reachable call paths, neither of which is done here.
-/

namespace BinaryFv.Keccak

open BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

/-! ## The depth-budget window invariant (conditional infrastructure)

Everything in this section is conditional: the budget `used ≤ stackPageSize` is carried in the
invariant and the budget for each further allocation is taken as a hypothesis.  These lemmas say
what follows *given* a budget; they do not establish one. -/

/-- The runtime stack pointer sits exactly `used` bytes below the initial top, and the consumed
    depth stays within the canonical 4 KiB stack page. -/
def SpDepthInWindow (sp used : Nat) : Prop := sp + used = stackTop ∧ used ≤ stackPageSize

theorem stackPageSize_le_stackTop : stackPageSize ≤ stackTop := by
  change (0x1000 : Nat) ≤ 2 ^ 64 - 0x1000
  decide

theorem stackRange_start_eq : stackRange.start = stackTop - stackPageSize := rfl

/-- The depth-budget invariant refines the raw stack-pointer window of `StackFrames`. -/
theorem SpDepthInWindow.toWindow {sp used : Nat} (h : SpDepthInWindow sp used) :
    SpInStackWindow sp := by
  obtain ⟨hsum, hbud⟩ := h
  have hp := stackPageSize_le_stackTop
  refine ⟨?_, ?_⟩
  · rw [stackRange_start_eq]; omega
  · omega

/-- A downward allocation of `delta` bytes that keeps the consumed depth within the page preserves
    the depth-budget invariant.  Crucially there is no underflow hypothesis: the budget bound forces
    `delta ≤ sp`. -/
theorem SpDepthInWindow.alloc {sp used delta : Nat} (h : SpDepthInWindow sp used)
    (hbudget : used + delta ≤ stackPageSize) : SpDepthInWindow (sp - delta) (used + delta) := by
  obtain ⟨hsum, _⟩ := h
  have hp := stackPageSize_le_stackTop
  exact ⟨by omega, hbudget⟩

/-- The budget bound rules out stack-pointer underflow during a `delta`-byte allocation. -/
theorem SpDepthInWindow.delta_le {sp used delta : Nat} (h : SpDepthInWindow sp used)
    (hbudget : used + delta ≤ stackPageSize) : delta ≤ sp := by
  obtain ⟨hsum, _⟩ := h
  have hp := stackPageSize_le_stackTop
  omega

/-- The stack pointer is seeded at the top with zero consumed depth. -/
theorem SpDepthInWindow.entry : SpDepthInWindow stackTop 0 := ⟨by omega, Nat.zero_le _⟩

/-! ## The BitVec → Nat bridge for the generated prologue

The generated `addi sp, sp, immediate` retirement writes `x2 := stackValue + sign_extend immediate`
(a `BitVec 64`).  For a prologue `addi sp, sp, -delta` (`immediate.toInt = -delta`) that stays above
the stack limit, the register's `.toNat` is exactly `stackValue.toNat - delta`. -/

/-! ## Connecting the generated `try_step` prologue contract to the window invariant -/

/-- **Conditional (state form).**  From a depth-budget window whose stack pointer is `stackValue`,
    the packaged prologue `addi sp, sp, -delta` retirement lands in a depth-budget window that has
    consumed `delta` more bytes.

    Conditional on the caller-supplied budget premise `hbudget : used + delta ≤ stackPageSize`: the
    new `stackRange.start ≤ sp'` bound is derived *from that premise*, not established here.  No
    static fact of this module discharges `hbudget`; supplying it per call site is the deferred
    sponge/caller-trace obligation. -/
theorem tryStepStackAddiWindow (state : State) (pc : BitVec 64) (immediate : BitVec 12)
    (stackValue retired : BitVec 64) (delta used : Nat)
    (himm : immediate.toInt = -(delta : Int))
    (hwin : SpDepthInWindow stackValue.toNat used)
    (hbudget : used + delta ≤ stackPageSize) :
    (tryStepStackAddiAfterRetired state pc immediate stackValue retired).regs.get? x2
        = some (stackValue + sign_extend (m := 64) immediate) ∧
      SpDepthInWindow (stackValue + sign_extend (m := 64) immediate).toNat (used + delta) ∧
      SpInStackWindow (stackValue + sign_extend (m := 64) immediate).toNat := by
  have hdelta : delta ≤ stackValue.toNat := hwin.delta_le hbudget
  have htoNat : (stackValue + sign_extend (m := 64) immediate).toNat = stackValue.toNat - delta :=
    prologue_toNat stackValue immediate delta himm hdelta
  have hwin' : SpDepthInWindow (stackValue + sign_extend (m := 64) immediate).toNat (used + delta) := by
    rw [htoNat]; exact hwin.alloc hbudget
  exact ⟨tryStepStackAddiAfterRetired_stackPointer state pc immediate stackValue retired, hwin',
    hwin'.toWindow⟩

/-- **Conditional (execution form).**  The full generated `try_step` prologue contract *runs*, and
    its resulting state satisfies the depth-budget window invariant with `delta` more bytes consumed.
    This is `BinaryFv.RiscV.tryStepStackAddiRetires` composed with `tryStepStackAddiWindow`.

    Conditional on the caller-supplied budget premise `hbudget : used + delta ≤ stackPageSize`.  The
    execution content (an actual generated prologue step preserves the window) is unconditional; the
    window content is not. -/
theorem tryStepStackAddiRetiresInWindow (stepNo : Nat) (state : State) (pc : BitVec 64)
    (immediate : BitVec 12) (stackValue retired : BitVec 64) (inhibit : BitVec 32)
    (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (platform : FetchBasePlatform (tryStepStackAddiAfterIncrement state) pc)
    (interrupts : InterruptDisabled (tryStepStackAddiAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (fetchBytes : FetchBytesBaseContract (tryStepStackAddiAfterIncrement state) pc
      byte0 byte1 byte2 byte3)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepStackAddiAfterIncrement state) (tryStepStackAddiAfterIncrement state)
      (.ITYPE (immediate, stackPointer, stackPointer, .ADDI)))
    (notExpected : LandingPadNotExpected (tryStepStackAddiAfterIncrement state))
    (stackRead : (stackAddiNextState (tryStepStackAddiAfterIncrement state) pc).regs.get? x2 =
      some stackValue)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired)
    (delta used : Nat)
    (himm : immediate.toInt = -(delta : Int))
    (hwin : SpDepthInWindow stackValue.toNat used)
    (hbudget : used + delta ≤ stackPageSize) :
    Runs (try_step stepNo false) state
        (tryStepStackAddiAfterRetired state pc immediate stackValue retired) false ∧
      (tryStepStackAddiAfterRetired state pc immediate stackValue retired).regs.get? x2
        = some (stackValue + sign_extend (m := 64) immediate) ∧
      SpDepthInWindow (stackValue + sign_extend (m := 64) immediate).toNat (used + delta) ∧
      SpInStackWindow (stackValue + sign_extend (m := 64) immediate).toNat := by
  refine ⟨tryStepStackAddiRetires stepNo state pc immediate stackValue retired inhibit config
    byte0 byte1 byte2 byte3 platform interrupts base fetchBytes decode notExpected stackRead
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead, ?_⟩
  exact tryStepStackAddiWindow state pc immediate stackValue retired delta used himm hwin hbudget

/-! ## Diagnostic summaries of the frontier-truncated static flow

**Nothing in this section is a stack bound.**  These are closed parser facts about the
frontier-truncated closure summaries of `BinaryFv.Keccak.Reth.Artifact.Analysis.StackFlow`, recorded as evidence and as a
regression tripwire on the static analysis.  They are deliberately *not* used to discharge any
budget premise, because they cannot: the underlying exploration is truncated at calls and other
frontiers, so a per-function `maximumExploredDownwardDelta` is not a per-function stack bound and
summing them is not an over-approximation of any call chain's demand.

Being closed facts about the fixed parsed artifact, these carry `native_decide`'s compiler-trust
axioms (`Lean.ofReduceBool`, `Lean.trustCompiler`).  Nothing else in this module depends on this
section: the window machinery and the `*_of_budget` frame exports are kernel-clean
(`propext` / `Quot.sound` / `Classical.choice`).

One honest caveat: `tryStepStackAddiRetiresInWindow` *does* also report those two axioms, but it
inherits them from the upstream generated `try_step` contract
(`BinaryFv.RiscV.tryStepStackAddiRetires`), not from this diagnostic section — that is the separate,
pre-existing artifact-trust question tracked against the README policy, not a stack claim. -/

/-! ## Conditional frame containment and disjointness exports

These are the lemmas the sponge/runner stage needs, and they are **conditional**: each takes the
depth-budget invariant plus a caller-supplied budget premise `used + delta ≤ stackPageSize`.  Given
those, the raw window inequalities that `StackFrames` assumes are discharged here.  The budget
premise itself is *not* established here for this binary — the caller must supply it per call site,
which is the deferred sponge/caller-trace obligation.  The `_of_budget` suffix marks this. -/

/-- **Conditional on the caller-supplied budget premise.**  A function frame `[sp - delta, sp)`
    (bytes between the post- and pre-prologue stack pointers) lies inside the canonical stack window.
    The inequalities are derived *from* `hwin` and `hbudget`; this does not establish `hbudget`. -/
theorem funcFrame_containedIn_stackRange_of_budget {sp used delta : Nat}
    (hwin : SpDepthInWindow sp used) (hbudget : used + delta ≤ stackPageSize) :
    (stackFrame (sp - delta) sp).containedIn stackRange :=
  stackFrame_containedIn_stackRange (hwin.alloc hbudget).toWindow.1 (Nat.sub_le sp delta)
    hwin.toWindow.2

/-- **Conditional on the caller-supplied budget premise.**  A function frame is disjoint from every
    non-stack region of a well-formed Keccak layout.  The inequalities are derived *from* `hwin` and
    `hbudget`; this does not establish `hbudget`. -/
theorem funcFrame_disjoint_of_layout_of_budget {layout : KeccakLayout} (hwf : layout.wellFormed)
    (hstack : layout.stack = stackRange) {sp used delta : Nat}
    (hwin : SpDepthInWindow sp used) (hbudget : used + delta ≤ stackPageSize) :
    (stackFrame (sp - delta) sp).disjoint layout.code ∧
    (stackFrame (sp - delta) sp).disjoint layout.returnSentinel ∧
    (stackFrame (sp - delta) sp).disjoint layout.output ∧
    (stackFrame (sp - delta) sp).disjoint layout.message :=
  stackFrame_disjoint_of_layout hwf hstack (hwin.alloc hbudget).toWindow.1 (Nat.sub_le sp delta)
    hwin.toWindow.2

/-- **Conditional on the caller-supplied budget premise (nested frames).**  A callee frame allocated
    directly below its caller's frame (the callee is entered with `sp = parentSp - parentDelta`, then
    allocates `childDelta`) is contained in the stack window, as is the caller's frame, and the two
    are disjoint.

    Every inequality is derived *from* the caller's depth-budget invariant plus the combined budget
    premise `hbudget`.  This is the two-level shape a real call site needs, but the premise for an
    actual nesting in this binary is not established here — supplying it is the deferred
    sponge/caller-trace obligation. -/
theorem nestedFuncFrames_containedIn_and_disjoint_of_budget
    {parentSp parentUsed parentDelta childDelta : Nat}
    (hwin : SpDepthInWindow parentSp parentUsed)
    (hbudget : parentUsed + parentDelta + childDelta ≤ stackPageSize) :
    (stackFrame (parentSp - parentDelta - childDelta) (parentSp - parentDelta)).containedIn
        stackRange ∧
      (stackFrame (parentSp - parentDelta) parentSp).containedIn stackRange ∧
      (stackFrame (parentSp - parentDelta - childDelta) (parentSp - parentDelta)).disjoint
        (stackFrame (parentSp - parentDelta) parentSp) := by
  -- the caller's own frame is in-window from the caller budget
  have hParentFrame : (stackFrame (parentSp - parentDelta) parentSp).containedIn stackRange :=
    funcFrame_containedIn_stackRange_of_budget hwin (by omega)
  -- after the caller's prologue we are at depth `parentUsed + parentDelta`
  have hchildWin : SpDepthInWindow (parentSp - parentDelta) (parentUsed + parentDelta) :=
    hwin.alloc (by omega)
  -- the callee frame is in-window from the callee's own budget
  have hChildFrame :
      (stackFrame ((parentSp - parentDelta) - childDelta) (parentSp - parentDelta)).containedIn
        stackRange :=
    funcFrame_containedIn_stackRange_of_budget hchildWin (by omega)
  refine ⟨by simpa [Nat.sub_sub] using hChildFrame, hParentFrame, ?_⟩
  exact stackFrame_nested_disjoint (Nat.sub_le _ _) (Nat.le_refl _)

/-- **Diagnostic corollary — not a capstone, and not a stack bound.**  If an allocation from the
    seeded stack top *happens* to have depth within the diagnostic summary figure, then its frame
    lies in `stackRange`.  This is the arithmetic consequence of `1664 ≤ 4096` threaded through the
    seeded window (`SpDepthInWindow.entry`).

    It is retained only as a sanity check tying the diagnostic figure to the window machinery.  It
    says **nothing** about whether any actual run's depth is within that figure: the figure is a
    frontier-truncated summary, and no reachable call chain has been shown to respect it.  In
    particular the hypothesis `hdelta` is an assumption about `delta`, not a fact proved of this
    binary.  Any binary-wide reading would be unsound; the real result is deferred to the
    sponge/caller trace stage. -/
theorem diagnostic_frameWithinFrontierSummaryTotal_containedIn_stackRange {delta : Nat}
    (hdelta : delta ≤ frontierSummaryTotalDownwardDelta) :
    (stackFrame (stackTop - delta) stackTop).containedIn stackRange :=
  funcFrame_containedIn_stackRange_of_budget SpDepthInWindow.entry
    (by have := diagnostic_frontierSummaryTotalDownwardDelta_le_stackPageSize; omega)

end BinaryFv.Keccak
