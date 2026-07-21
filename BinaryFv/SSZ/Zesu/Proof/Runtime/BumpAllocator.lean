import BinaryFv.SSZ.Zesu.Execution.Representation

namespace BinaryFv.SSZ.Zesu.Proof.Runtime

/-- Pure RV64 model of the checked bump-allocation arithmetic used by `zesu_raw_alloc`. -/
structure BumpHeap where
  position : Nat
  limit : Nat

def powerOfTwo (value : Nat) : Bool := value != 0 && value &&& (value - 1) == 0

def allocationPadding (position alignment : Nat) : Nat :=
  let misalignment := position &&& (alignment - 1)
  if misalignment == 0 then 0 else alignment - misalignment

def allocate (heap : BumpHeap) (bytes alignment : Nat) : Option (Nat × BumpHeap) :=
  if !powerOfTwo alignment || heap.position > heap.limit then none else
  let padding := allocationPadding heap.position alignment
  if padding > heap.limit - heap.position then none else
  let aligned := heap.position + padding
  if bytes > heap.limit - aligned then none else
  some (aligned, { position := aligned + bytes, limit := heap.limit })

theorem allocate_success_within_limit {heap : BumpHeap} {bytes alignment pointer heap'}
    (heapFits : heap.position ≤ heap.limit)
    (success : allocate heap bytes alignment = some (pointer, heap')) :
    heap.position ≤ pointer ∧ pointer ≤ heap'.position ∧ heap'.position ≤ heap.limit := by
  unfold allocate at success
  split at success <;> try contradiction
  rename_i validAlignment
  dsimp at success
  split at success <;> try contradiction
  rename_i paddingFits
  split at success <;> try contradiction
  rename_i bytesFit
  have resultEq :
      (heap.position + allocationPadding heap.position alignment,
        { position := heap.position + allocationPadding heap.position alignment + bytes,
          limit := heap.limit }) = (pointer, heap') := Option.some.inj success
  cases resultEq
  have paddingBound : allocationPadding heap.position alignment ≤ heap.limit - heap.position :=
    Nat.le_of_not_gt paddingFits
  have bytesBound : bytes ≤ heap.limit - (heap.position + allocationPadding heap.position alignment) :=
    Nat.le_of_not_gt bytesFit
  change heap.position ≤ heap.position + allocationPadding heap.position alignment ∧
    heap.position + allocationPadding heap.position alignment ≤
      heap.position + allocationPadding heap.position alignment + bytes ∧
    heap.position + allocationPadding heap.position alignment + bytes ≤ heap.limit
  constructor
  · exact Nat.le_add_right _ _
  constructor
  · exact Nat.le_add_right _ _
  · omega

end BinaryFv.SSZ.Zesu.Proof.Runtime
