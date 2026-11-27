import BinaryFv.Binary.Address

namespace BinaryFv.RiscV

open BinaryFv.Binary

/-- RV64 words are represented as naturals until no-wrap obligations are discharged. -/
abbrev Word := Nat

def addressLimit : Nat := 2 ^ 64

/-- Convert a proved in-range natural address or value to its RV64 representation. -/
def rv64Word (value : Nat) (_fits64 : value < addressLimit) : BitVec 64 :=
  BitVec.ofNat 64 value

theorem rv64Word_toNat (value : Nat) (fits64 : value < addressLimit) :
    (rv64Word value fits64).toNat = value := by
  unfold rv64Word
  calc
    (BitVec.ofNat 64 value).toNat = value % 2 ^ 64 := BitVec.toNat_ofNat value 64
    _ = value := Nat.mod_eq_of_lt (by simpa [addressLimit] using fits64)

end BinaryFv.RiscV

/--
An address range fits the RV64 address space.

This extends `BinaryFv.Binary.AddressRange`'s namespace from the RISC-V layer on purpose: the range
type itself is architecture-independent, but the `2 ^ 64` bound is not.
-/
def BinaryFv.Binary.AddressRange.fits64 (range : AddressRange) : Prop :=
  range.stop ≤ BinaryFv.RiscV.addressLimit
