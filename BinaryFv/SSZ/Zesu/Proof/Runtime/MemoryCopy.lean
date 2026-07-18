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

/-- `memcpy` frames every address outside its destination range. -/
theorem memcpy_outside_destination (memory : Nat → UInt8) (destination source length address : Nat)
    (outside : address < destination ∨ destination + length ≤ address) :
    memcpy memory destination source length address = memory address :=
  memmove_outside_destination memory destination source length address outside

/-- One byte write in the pure result-memory model. -/
def writeByte (memory : Nat → UInt8) (address : Nat) (value : UInt8) : Nat → UInt8 :=
  fun current => if current == address then value else memory current

/-- The successful `zesu_decode_raw` epilogue: zero the 16-bit status, then copy the 832-byte root. -/
def successResultEpilogue (memory : Nat → UInt8) (resultBase stackRootBase : Nat) : Nat → UInt8 :=
  memcpy (writeByte (writeByte memory (resultBase + 832) 0) (resultBase + 833) 0)
    resultBase stackRootBase 832

theorem success_result_epilogue_status_low (memory : Nat → UInt8) (resultBase stackRootBase : Nat) :
    successResultEpilogue memory resultBase stackRootBase (resultBase + 832) = 0 := by
  unfold successResultEpilogue
  rw [memcpy_outside_destination]
  · simp [writeByte]
  · right
    omega

theorem success_result_epilogue_status_high (memory : Nat → UInt8) (resultBase stackRootBase : Nat) :
    successResultEpilogue memory resultBase stackRootBase (resultBase + 833) = 0 := by
  unfold successResultEpilogue
  rw [memcpy_outside_destination]
  · simp [writeByte]
  · right
    omega

end BinaryFv.SSZ.Zesu.Proof.Runtime
