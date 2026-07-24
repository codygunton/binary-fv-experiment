import BinaryFv.SSZ.Zesu.Runtime.AllocationBound
import BinaryFv.SSZ.Zesu.Runtime.BumpAllocator

/-!
# How much the allocator can have handed out

The arena-exhaustion question is, literally, "did the bump cursor pass the ceiling". The binary's own
check is a comparison against `ZKVM_HEAP_TOP`, so the quantity to bound is the *real* cursor, not a
ghost counter: a counter would only settle real unreachability after being proved equal to the
cursor delta anyway.

This module supplies the three arithmetic pieces that sit between a per-routine allocation bound and
the conclusion that the decoder cannot report `outOfMemory`:

* `allocate_delta_le` — one allocation advances the cursor by at most `(alignment - 1) + bytes`. The
  `alignment - 1` is the padding the bump allocator may insert, which a naive "advances by `bytes`"
  bound would miss.
* `allocate_isSome_of_room` — the converse of exhaustion: when the cursor plus worst-case padding
  plus the request still fits under the ceiling, the allocation *succeeds*. This is what turns a
  bound on the total into "the exhaustion branch is not taken".
* `cursor_within_arena_of_bound` — the arithmetic conclusion: a total within
  `rawAllocationBound inputSize` leaves the cursor inside the arena for every admitted input.

Everything here is about the pure `BumpHeap` model and plain arithmetic. Connecting it to a machine
state (reading the cursor out of `ZKVM_HEAP_POS`) and to per-routine sums belongs above, where the
canonical addresses live; the per-occurrence delta facts themselves are local obligations of the
row proofs, not assumptions made here.
-/

namespace BinaryFv.SSZ.Zesu.Runtime

/-! ## Padding -/

/-- Alignment padding is always strictly less than the alignment. This is the clause a bound stated
only in terms of the requested size would miss. -/
theorem allocationPadding_lt (position alignment : Nat) (hpos : 0 < alignment) :
    allocationPadding position alignment < alignment := by
  unfold allocationPadding
  dsimp only
  by_cases hmis : (position &&& (alignment - 1)) = 0
  · rw [hmis]; simpa using hpos
  · rw [if_neg (by simpa using hmis)]
    omega

/-- Hence padding is at most `alignment - 1`, the form the per-call bound uses. -/
theorem allocationPadding_le (position alignment : Nat) (hpos : 0 < alignment) :
    allocationPadding position alignment ≤ alignment - 1 :=
  Nat.le_sub_one_of_lt (allocationPadding_lt position alignment hpos)

/-! ## One allocation -/

/-- **A single allocation advances the cursor by at most `(alignment - 1) + bytes`.** -/
theorem allocate_delta_le {heap : BumpHeap} {bytes alignment pointer : Nat} {heap' : BumpHeap}
    (hpos : 0 < alignment) (success : allocate heap bytes alignment = some (pointer, heap')) :
    heap'.position - heap.position ≤ (alignment - 1) + bytes := by
  obtain ⟨hptr, hposition, _⟩ := allocate_success_shape success
  have hpad := allocationPadding_le heap.position alignment hpos
  omega

/-- The cursor never moves backwards. -/
theorem allocate_position_le {heap : BumpHeap} {bytes alignment pointer : Nat} {heap' : BumpHeap}
    (success : allocate heap bytes alignment = some (pointer, heap')) :
    heap.position ≤ heap'.position := by
  obtain ⟨hptr, hposition, _⟩ := allocate_success_shape success
  omega

/-! ## Exhaustion is a comparison, so non-exhaustion is too -/

/-- **The allocation succeeds whenever there is room for it.**

Stated with the *worst-case* padding `alignment - 1` rather than the exact padding, so a caller only
has to know the request and the alignment — not the cursor's residue — to conclude the allocator
does not fail. This is the direction that makes `outOfMemory` unreachable: the decoder's exhaustion
branch is taken exactly when this comparison fails. -/
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

/-! ## The arithmetic conclusion -/

/-- **A total within the planned bound leaves the cursor inside the arena**, for every input the
theorem admits. This is `raw_allocation_bound_fits_arena` restated about the cursor: the quantity
bounded is `cursor - arenaBase`, which is what the machine actually holds. -/
theorem cursor_within_arena_of_bound {inputSize arenaBase cursor : Nat}
    (inputBound : inputSize < maximumInputBytes)
    (allocated : cursor - arenaBase ≤ rawAllocationBound inputSize)
    (started : arenaBase ≤ cursor) :
    cursor < arenaBase + zkvmArenaBytes := by
  have := raw_allocation_bound_fits_arena inputSize (cursor - arenaBase) inputBound allocated
  omega

/-- The same conclusion in the form the allocator's own check consumes: with the ceiling at
`arenaBase + zkvmArenaBytes`, a request that fits within the remaining planned budget still has room,
so the exhaustion branch is not taken. -/
theorem room_of_bound {inputSize arenaBase cursor bytes alignment : Nat}
    (inputBound : inputSize < maximumInputBytes)
    (started : arenaBase ≤ cursor)
    (budget : (cursor - arenaBase) + (alignment - 1) + bytes ≤ rawAllocationBound inputSize) :
    cursor + (alignment - 1) + bytes ≤ arenaBase + zkvmArenaBytes := by
  have hfits := raw_allocation_bound_fits_arena inputSize
    ((cursor - arenaBase) + (alignment - 1) + bytes) inputBound budget
  unfold zkvmArenaBytes at *
  omega

end BinaryFv.SSZ.Zesu.Runtime
