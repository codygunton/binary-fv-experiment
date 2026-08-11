namespace BinaryFv.Zesu.Runtime

def maximumInputBytes : Nat := 2 * 1024 * 1024
def rawAllocationBound (inputSize : Nat) : Nat := 8 * inputSize + 65536
def zkvmArenaBytes : Nat := 64 * 1024 * 1024

/-- The planned allocation ledger cannot exhaust the fixed zkVM arena for any admitted input. -/
theorem raw_allocation_bound_fits_arena (inputSize allocatedBytes : Nat)
    (inputBound : inputSize < maximumInputBytes)
    (allocationBound : allocatedBytes ≤ rawAllocationBound inputSize) :
    allocatedBytes < zkvmArenaBytes := by
  unfold maximumInputBytes rawAllocationBound zkvmArenaBytes at *
  omega

end BinaryFv.Zesu.Runtime
