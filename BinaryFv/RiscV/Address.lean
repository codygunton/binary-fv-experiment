namespace BinaryFv.RiscV

/-- RV64 words are represented as naturals until no-wrap obligations are discharged. -/
abbrev Word := Nat

def addressLimit : Nat := 2 ^ 64

def maxMessageSize : Nat := 2 ^ 63

/-- Convert a proved in-range natural address or value to its RV64 representation. -/
def rv64Word (value : Nat) (_fits64 : value < addressLimit) : BitVec 64 :=
  BitVec.ofNat 64 value

theorem rv64Word_toNat (value : Nat) (fits64 : value < addressLimit) :
    (rv64Word value fits64).toNat = value := by
  unfold rv64Word
  calc
    (BitVec.ofNat 64 value).toNat = value % 2 ^ 64 := BitVec.toNat_ofNat value 64
    _ = value := Nat.mod_eq_of_lt (by simpa [addressLimit] using fits64)

structure AddressRange where
  start : Nat
  size : Nat
deriving DecidableEq, Repr

namespace AddressRange

def stop (range : AddressRange) : Nat := range.start + range.size

def fits64 (range : AddressRange) : Prop := range.stop ≤ addressLimit

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

end BinaryFv.RiscV
