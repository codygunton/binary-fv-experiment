import BinaryFv.Keccak.Reth.Artifact.Layout

/-!
# Semantic stack-frame model over the canonical 4 KiB stack

The static ABI model (`BinaryFv.Keccak.Reth.Artifact.Layout`) fixes the 4 KiB stack window `stackRange`
(`[stackTop - stackPageSize, stackTop)`, SP seeded at `stackTop` growing down) and proves
inter-region disjointness via `KeccakLayout.wellFormed`.  This module turns that into the *semantic*
content step 3 needs: a runtime stack-pointer window invariant, that any stack frame sits inside the
window and is therefore disjoint from every non-stack region, and that nested call frames (each
allocated strictly below its caller's) are pairwise disjoint.

The lemmas are stated at the `Nat` address level; the runtime bridge is the SP value's `.toNat`
(a `BitVec 64` register), which the stack-adjust contract `tryStepStackAddiRetires` updates by
`stackValue + sign_extend imm`.
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary

open BinaryFv.RiscV

/-- The runtime stack pointer (as a `Nat` address) lies within the canonical 4 KiB stack window:
    at or above the stack limit and at or below the initial top. -/
def SpInStackWindow (sp : Nat) : Prop := stackRange.start ≤ sp ∧ sp ≤ stackTop

theorem stackRange_stop : stackRange.stop = stackTop := by
  change (stackTop - stackPageSize) + stackPageSize = stackTop
  simp only [stackTop, stackPageSize, addressLimit]

/-- A downward allocation that stays at or above the stack limit preserves the window invariant. -/
theorem SpInStackWindow.alloc {sp sp' : Nat} (h : SpInStackWindow sp)
    (hle : sp' ≤ sp) (hlow : stackRange.start ≤ sp') : SpInStackWindow sp' :=
  ⟨hlow, Nat.le_trans hle h.2⟩

/-- A deallocation that does not exceed the initial top preserves the window invariant. -/
theorem SpInStackWindow.dealloc {sp sp' : Nat} (h : SpInStackWindow sp)
    (hge : sp ≤ sp') (hhigh : sp' ≤ stackTop) : SpInStackWindow sp' :=
  ⟨Nat.le_trans h.1 hge, hhigh⟩

/-- A stack frame occupying the half-open address range `[spLow, spHigh)` (callee-allocated bytes
    between the post-allocation and pre-allocation stack pointers). -/
def stackFrame (spLow spHigh : Nat) : AddressRange := ⟨spLow, spHigh - spLow⟩

theorem stackFrame_start (spLow spHigh : Nat) : (stackFrame spLow spHigh).start = spLow := rfl

theorem stackFrame_stop {spLow spHigh : Nat} (h : spLow ≤ spHigh) :
    (stackFrame spLow spHigh).stop = spHigh := by
  simp only [stackFrame, AddressRange.stop]; omega

/-- A well-shaped frame lies inside the canonical stack window. -/
theorem stackFrame_containedIn_stackRange {spLow spHigh : Nat}
    (hlow : stackRange.start ≤ spLow) (hle : spLow ≤ spHigh) (hhigh : spHigh ≤ stackTop) :
    (stackFrame spLow spHigh).containedIn stackRange := by
  refine ⟨?_, ?_⟩
  · simpa [stackFrame_start] using hlow
  · rw [stackFrame_stop hle, stackRange_stop]; exact hhigh

/-- Any frame inside the stack window is disjoint from every non-stack region of a well-formed
    Keccak layout (code, return sentinel, output, message). -/
theorem stackFrame_disjoint_of_layout {layout : KeccakLayout} (hwf : layout.wellFormed)
    (hstack : layout.stack = stackRange) {spLow spHigh : Nat}
    (hlow : stackRange.start ≤ spLow) (hle : spLow ≤ spHigh) (hhigh : spHigh ≤ stackTop) :
    (stackFrame spLow spHigh).disjoint layout.code ∧
    (stackFrame spLow spHigh).disjoint layout.returnSentinel ∧
    (stackFrame spLow spHigh).disjoint layout.output ∧
    (stackFrame spLow spHigh).disjoint layout.message := by
  have hcont : (stackFrame spLow spHigh).containedIn layout.stack := by
    rw [hstack]; exact stackFrame_containedIn_stackRange hlow hle hhigh
  obtain ⟨_, _, _, _, _, _, _, _, dCode, _, _, dRet, _, dOut, dMsg⟩ := hwf
  exact ⟨AddressRange.disjoint_of_containedIn hcont dCode.symm,
    AddressRange.disjoint_of_containedIn hcont dRet.symm,
    AddressRange.disjoint_of_containedIn hcont dOut.symm,
    AddressRange.disjoint_of_containedIn hcont dMsg.symm⟩

/-- Nested frames are disjoint: a callee frame allocated strictly below the caller's frame
    (`eHigh ≤ cLow`) does not overlap it. -/
theorem stackFrame_nested_disjoint {cLow cHigh eLow eHigh : Nat}
    (heShape : eLow ≤ eHigh) (hbelow : eHigh ≤ cLow) :
    (stackFrame eLow eHigh).disjoint (stackFrame cLow cHigh) :=
  Or.inl (by rw [stackFrame_stop heShape, stackFrame_start]; exact hbelow)

end BinaryFv.Keccak
