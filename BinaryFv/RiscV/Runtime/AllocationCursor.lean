import BinaryFv.RiscV.Runtime.BumpAllocator

/-! Target-independent bounds for bump-allocation padding and cursor chains. -/

namespace BinaryFv.RiscV

theorem allocationPadding_lt (position alignment : Nat) (hpos : 0 < alignment) :
    allocationPadding position alignment < alignment := by
  unfold allocationPadding
  dsimp only
  by_cases hmis : (position &&& (alignment - 1)) = 0
  · rw [hmis]; simpa using hpos
  · rw [if_neg (by simpa using hmis)]
    omega

theorem allocationPadding_le (position alignment : Nat) (hpos : 0 < alignment) :
    allocationPadding position alignment ≤ alignment - 1 :=
  Nat.le_sub_one_of_lt (allocationPadding_lt position alignment hpos)

theorem allocate_delta_le {heap : BumpHeap} {bytes alignment pointer : Nat} {heap' : BumpHeap}
    (hpos : 0 < alignment) (success : allocate heap bytes alignment = some (pointer, heap')) :
    heap'.position - heap.position ≤ (alignment - 1) + bytes := by
  obtain ⟨_, hposition, _⟩ := allocate_success_shape success
  have hpad := allocationPadding_le heap.position alignment hpos
  omega

theorem allocate_position_le {heap : BumpHeap} {bytes alignment pointer : Nat} {heap' : BumpHeap}
    (success : allocate heap bytes alignment = some (pointer, heap')) :
    heap.position ≤ heap'.position := by
  obtain ⟨_, hposition, _⟩ := allocate_success_shape success
  omega

theorem allocate_isSome_of_room {heap : BumpHeap} {bytes alignment : Nat}
    (valid : powerOfTwo alignment = true) (hpos : 0 < alignment)
    (room : heap.position + (alignment - 1) + bytes ≤ heap.limit) :
    (allocate heap bytes alignment).isSome = true := by
  have hpad := allocationPadding_le heap.position alignment hpos
  unfold allocate
  rw [if_neg (by simp [valid]; omega)]
  dsimp
  rw [if_neg (by omega), if_neg (by omega)]
  rfl

def requestCost (bytes alignment : Nat) : Nat := (alignment - 1) + bytes

inductive CursorChain : Nat → Nat → List Nat → Prop where
  | nil (cursor : Nat) : CursorChain cursor cursor []
  | step {before middle finish cost : Nat} {costs : List Nat}
      (advances : before ≤ middle) (bounded : middle - before ≤ cost)
      (rest : CursorChain middle finish costs) :
      CursorChain before finish (cost :: costs)

theorem CursorChain.total_le {start finish : Nat} {costs : List Nat}
    (chain : CursorChain start finish costs) :
    start ≤ finish ∧ finish - start ≤ costs.sum := by
  induction chain with
  | nil cursor => exact ⟨Nat.le_refl cursor, by simp⟩
  | step advances bounded rest ih =>
    obtain ⟨hle, hsum⟩ := ih
    refine ⟨Nat.le_trans advances hle, ?_⟩
    simp only [List.sum_cons]
    omega

end BinaryFv.RiscV
