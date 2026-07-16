import BinaryFv.Keccak.StackFrames
import BinaryFv.Keccak.StackFlow
import BinaryFv.RISCV.TryStepStackAddiContract

/-!
# Deriving runtime stack bounds from the static stack-flow analysis

`BinaryFv.Keccak.StackFrames` supplies the semantic stack-frame model but *assumes* the critical
window inequalities (`stackRange.start ≤ spLow`, `spLow ≤ spHigh`, `spHigh ≤ stackTop`, nested
`eHigh ≤ cLow`) as hypotheses.  This module *derives* those inequalities.

The runtime bridge is a *depth-budget* invariant `SpDepthInWindow sp used`:  the stack pointer sits
exactly `used` bytes below the initial top and `used` stays within the 4 KiB page.  The generated
`addi sp, sp, -delta` prologue (whose retirement is packaged by
`BinaryFv.RISCV.tryStepStackAddiRetires`) turns `SpDepthInWindow sp used` into
`SpDepthInWindow (sp - delta) (used + delta)` *whenever* `used + delta ≤ stackPageSize`.  That
side-condition is exactly what the parser-derived static flow facts of
`BinaryFv.Keccak.StackFlow` provide: the sum of per-function downward deltas across the entry call
closure (`entryClosureTotalDownwardDelta = 1664`) is bounded by the 4 KiB page, so the budget is
never exhausted along any (simple) call chain.  Hence `stackRange.start ≤ sp'` is *derived* from the
static bound, not supplied by the caller.

The `funcFrame_*` / `nestedFuncFrames_*` exports below give later callers frame containment and
pairwise disjointness taking only the budget invariant plus the static bound, never the raw
inequalities.

None of this is a semantic-reachability claim: as everywhere in this development, the static flow
facts summarise decoded edges; turning the depth budget into runtime overflow-freedom for a concrete
run remains the caller's separate obligation (discharged via the depth accumulator this module
threads).
-/

namespace BinaryFv.Keccak

open BinaryFv.RISCV
open PreSail
open LeanRV64DExecutable.Functions
open Register

/-! ## The depth-budget window invariant -/

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

theorem prologue_toNat (stackValue : BitVec 64) (immediate : BitVec 12) (delta : Nat)
    (himm : immediate.toInt = -(delta : Int)) (hle : delta ≤ stackValue.toNat) :
    (stackValue + sign_extend (m := 64) immediate).toNat = stackValue.toNat - delta := by
  show (stackValue + immediate.signExtend 64).toNat = stackValue.toNat - delta
  have hext : (immediate.signExtend 64).toInt = -(delta : Int) := by
    rw [BitVec.toInt_signExtend_of_le (by omega)]; exact himm
  have hcond := BitVec.toInt_eq_toNat_cond (immediate.signExtend 64)
  rw [hext] at hcond
  have hlt : (immediate.signExtend 64).toNat < 2 ^ 64 := (immediate.signExtend 64).isLt
  have hs : stackValue.toNat < 2 ^ 64 := stackValue.isLt
  rw [BitVec.toNat_add]
  split at hcond <;> omega

/-! ## Connecting the generated `try_step` prologue contract to the window invariant -/

/-- The stack pointer held by the state after the packaged `try_step` prologue retirement. -/
theorem tryStepStackAddiAfterRetired_stackPointer (state : State) (pc : BitVec 64)
    (immediate : BitVec 12) (stackValue retired : BitVec 64) :
    (tryStepStackAddiAfterRetired state pc immediate stackValue retired).regs.get? x2
      = some (stackValue + sign_extend (m := 64) immediate) := by
  calc
    (tryStepStackAddiAfterRetired state pc immediate stackValue retired).regs.get? x2
        = (tryStepStackAddiAfterTick state pc immediate stackValue).regs.get? x2 := by
          simpa [tryStepStackAddiAfterRetired] using
            writeReg_read_unchanged (tryStepStackAddiAfterTick state pc immediate stackValue)
              minstret x2 (Sail.BitVec.addInt retired 1) (by decide)
    _ = (tryStepStackAddiAfterActive state pc immediate stackValue).regs.get? x2 := by
          simpa [tryStepStackAddiAfterTick] using
            writeReg_read_unchanged (tryStepStackAddiAfterActive state pc immediate stackValue)
              PC x2 (Sail.BitVec.addInt pc 4) (by decide)
    _ = some (stackValue + sign_extend (m := 64) immediate) := by
          change
            ((stackAddiNextState (tryStepStackAddiAfterIncrement state) pc).regs.insert x2
              (stackValue + sign_extend (m := 64) immediate)).get? x2 = _
          rw [Std.ExtDHashMap.get?_insert]
          simp

/-- **Deliverable 1 (state form).**  From a depth-budget window whose stack pointer is `stackValue`,
    the packaged prologue `addi sp, sp, -delta` retirement lands in a depth-budget window that has
    consumed `delta` more bytes — provided the static bound `used + delta ≤ stackPageSize` holds.
    The new `stackRange.start ≤ sp'` bound is *derived* from the budget, not assumed. -/
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

/-- **Deliverable 1 (execution form).**  The full generated `try_step` prologue contract *runs*, and
    its resulting state satisfies the depth-budget window invariant with `delta` more bytes consumed.
    This is `BinaryFv.RISCV.tryStepStackAddiRetires` composed with `tryStepStackAddiWindow`. -/
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

/-! ## Concrete 4 KiB bound from the parser-derived static flow -/

/-- Sum of the per-function maximum explored downward deltas across the parser-derived entry call
    closure.  Each function contributes once, so this over-approximates the downward-delta sum of
    any simple call chain through the closure.  The `none` default deliberately exceeds the page, so
    proving the bound below also certifies that the static summaries are available. -/
def entryClosureTotalDownwardDelta : Nat :=
  match entryClosureFrontierTruncatedStackStateSummaries? with
  | some summaries =>
    summaries.foldl (fun acc s => acc + s.maximumExploredDownwardDelta) 0
  | none => stackPageSize + 1

/-- The single largest per-function explored downward delta across the entry call closure. -/
def entryClosureMaxSingleDownwardDelta : Nat :=
  match entryClosureFrontierTruncatedStackStateSummaries? with
  | some summaries =>
    summaries.foldl (fun acc s => max acc s.maximumExploredDownwardDelta) 0
  | none => stackPageSize + 1

/-- Closed parser fact: the concrete summed downward-delta demand of the entry closure. -/
theorem entryClosureTotalDownwardDelta_eq : entryClosureTotalDownwardDelta = 1664 := by
  native_decide

/-- Closed parser fact: the concrete largest single-function downward delta. -/
theorem entryClosureMaxSingleDownwardDelta_eq : entryClosureMaxSingleDownwardDelta = 912 := by
  native_decide

/-- **Deliverable 2 (concrete bound).**  The total downward-delta demand of the entry call closure
    fits within the canonical 4 KiB stack page.  Because each function contributes once, the sum of
    deltas along *any* simple call chain is bounded by this total, hence by `stackPageSize`. -/
theorem entryClosureTotalDownwardDelta_le_stackPageSize :
    entryClosureTotalDownwardDelta ≤ stackPageSize := by
  native_decide

theorem entryClosureMaxSingleDownwardDelta_le_stackPageSize :
    entryClosureMaxSingleDownwardDelta ≤ stackPageSize := by
  native_decide

/-! ## Frame containment and disjointness exports (Deliverable 3)

These are the lemmas the sponge/runner stage needs.  They take only the depth-budget invariant and
the static bound `used + delta ≤ stackPageSize`; the raw window inequalities that `StackFrames`
assumes are all discharged here. -/

/-- A function frame `[sp - delta, sp)` (bytes between the post- and pre-prologue stack pointers)
    lies inside the canonical stack window — inequalities derived from the depth budget. -/
theorem funcFrame_containedIn_stackRange {sp used delta : Nat}
    (hwin : SpDepthInWindow sp used) (hbudget : used + delta ≤ stackPageSize) :
    (stackFrame (sp - delta) sp).containedIn stackRange :=
  stackFrame_containedIn_stackRange (hwin.alloc hbudget).toWindow.1 (Nat.sub_le sp delta)
    hwin.toWindow.2

/-- A function frame is disjoint from every non-stack region of a well-formed Keccak layout —
    inequalities derived from the depth budget. -/
theorem funcFrame_disjoint_of_layout {layout : KeccakLayout} (hwf : layout.wellFormed)
    (hstack : layout.stack = stackRange) {sp used delta : Nat}
    (hwin : SpDepthInWindow sp used) (hbudget : used + delta ≤ stackPageSize) :
    (stackFrame (sp - delta) sp).disjoint layout.code ∧
    (stackFrame (sp - delta) sp).disjoint layout.returnSentinel ∧
    (stackFrame (sp - delta) sp).disjoint layout.output ∧
    (stackFrame (sp - delta) sp).disjoint layout.message :=
  stackFrame_disjoint_of_layout hwf hstack (hwin.alloc hbudget).toWindow.1 (Nat.sub_le sp delta)
    hwin.toWindow.2

/-- **Deliverable 3 (nested frames).**  A callee frame allocated directly below its caller's frame
    (the callee is entered with `sp = parentSp - parentDelta`, then allocates `childDelta`) is
    contained in the stack window, as is the caller's frame, and the two are disjoint.  Every
    inequality is derived from the caller's depth budget plus the combined static bound. -/
theorem nestedFuncFrames_containedIn_and_disjoint {parentSp parentUsed parentDelta childDelta : Nat}
    (hwin : SpDepthInWindow parentSp parentUsed)
    (hbudget : parentUsed + parentDelta + childDelta ≤ stackPageSize) :
    (stackFrame (parentSp - parentDelta - childDelta) (parentSp - parentDelta)).containedIn
        stackRange ∧
      (stackFrame (parentSp - parentDelta) parentSp).containedIn stackRange ∧
      (stackFrame (parentSp - parentDelta - childDelta) (parentSp - parentDelta)).disjoint
        (stackFrame (parentSp - parentDelta) parentSp) := by
  -- the caller's own frame is in-window from the caller budget
  have hParentFrame : (stackFrame (parentSp - parentDelta) parentSp).containedIn stackRange :=
    funcFrame_containedIn_stackRange hwin (by omega)
  -- after the caller's prologue we are at depth `parentUsed + parentDelta`
  have hchildWin : SpDepthInWindow (parentSp - parentDelta) (parentUsed + parentDelta) :=
    hwin.alloc (by omega)
  -- the callee frame is in-window from the callee's own budget
  have hChildFrame :
      (stackFrame ((parentSp - parentDelta) - childDelta) (parentSp - parentDelta)).containedIn
        stackRange :=
    funcFrame_containedIn_stackRange hchildWin (by omega)
  refine ⟨by simpa [Nat.sub_sub] using hChildFrame, hParentFrame, ?_⟩
  exact stackFrame_nested_disjoint (Nat.sub_le _ _) (Nat.le_refl _)

/-- **Deliverable 2 (capstone).**  Any allocation whose depth is within the entry closure's total
    downward-delta demand, taken from the seeded stack top, produces a frame inside `stackRange`.
    This threads the concrete parser-derived bound (`entryClosureTotalDownwardDelta ≤ stackPageSize`)
    through the seeded window (`SpDepthInWindow.entry`), so every frame reachable within the closure's
    static budget stays in the canonical 4 KiB window. -/
theorem entryClosureFrame_containedIn_stackRange {delta : Nat}
    (hdelta : delta ≤ entryClosureTotalDownwardDelta) :
    (stackFrame (stackTop - delta) stackTop).containedIn stackRange :=
  funcFrame_containedIn_stackRange SpDepthInWindow.entry
    (by have := entryClosureTotalDownwardDelta_le_stackPageSize; omega)

end BinaryFv.Keccak
