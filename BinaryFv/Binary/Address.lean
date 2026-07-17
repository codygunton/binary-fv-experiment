namespace BinaryFv.Binary

/--
A half-open range of byte addresses, `[start, start + size)`.

Architecture-independent: nothing here knows the width of an address. The RV64 bound lives with
`BinaryFv.RiscV.addressLimit`, and `AddressRange.fits64` is declared alongside it.
-/
structure AddressRange where
  start : Nat
  size : Nat
deriving DecidableEq, Repr

namespace AddressRange

def stop (range : AddressRange) : Nat := range.start + range.size

/-- Half-open ranges are disjoint when one ends no later than the other begins. -/
def disjoint (left right : AddressRange) : Prop :=
  left.stop ≤ right.start ∨ right.stop ≤ left.start

def containedIn (range container : AddressRange) : Prop :=
  container.start ≤ range.start ∧ range.stop ≤ container.stop

theorem containedIn_trans {first second third : AddressRange}
    (firstH : first.containedIn second) (secondH : second.containedIn third) :
    first.containedIn third :=
  ⟨Nat.le_trans secondH.1 firstH.1, Nat.le_trans firstH.2 secondH.2⟩

end AddressRange

end BinaryFv.Binary
