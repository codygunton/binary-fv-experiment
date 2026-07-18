namespace BinaryFv.SSZ.Zesu.Proof.Runtime

/-- Snapshot semantics for the `memmove` contract: reads are all from the pre-state. -/
def memmove (memory : Nat → UInt8) (destination source length : Nat) : Nat → UInt8 :=
  fun address =>
    if destination ≤ address ∧ address < destination + length then
      memory (source + (address - destination))
    else memory address

/-- The destination range receives exactly the original source range, including on overlap. -/
theorem memmove_destination (memory : Nat → UInt8) (destination source length index : Nat)
    (indexBound : index < length) :
    memmove memory destination source length (destination + index) = memory (source + index) := by
  unfold memmove
  have inDestination : destination ≤ destination + index ∧ destination + index < destination + length := by
    omega
  rw [if_pos inDestination]
  congr 1
  omega

/-- Addresses outside the destination range are framed unchanged. -/
theorem memmove_outside_destination (memory : Nat → UInt8) (destination source length address : Nat)
    (outside : address < destination ∨ destination + length ≤ address) :
    memmove memory destination source length address = memory address := by
  unfold memmove
  rw [if_neg]
  omega

/-- `memcpy` is the non-overlap use of the same snapshot copy relation. -/
def memcpy (memory : Nat → UInt8) (destination source length : Nat) : Nat → UInt8 :=
  memmove memory destination source length

theorem memcpy_destination (memory : Nat → UInt8) (destination source length index : Nat)
    (indexBound : index < length) :
    memcpy memory destination source length (destination + index) = memory (source + index) :=
  memmove_destination memory destination source length index indexBound

end BinaryFv.SSZ.Zesu.Proof.Runtime
