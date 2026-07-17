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

/-- Half-open disjointness is symmetric. -/
theorem disjoint_symm {a b : AddressRange} (h : a.disjoint b) : b.disjoint a :=
  h.symm
/-- Containment refines disjointness: a range inside a region disjoint from `other` is itself
    disjoint from `other`. -/
theorem disjoint_of_containedIn {inner region other : AddressRange}
    (hin : inner.containedIn region) (hdis : region.disjoint other) : inner.disjoint other := by
  rcases hdis with h | h
  · exact Or.inl (Nat.le_trans hin.2 h)
  · exact Or.inr (Nat.le_trans h hin.1)

end AddressRange

end BinaryFv.Binary
