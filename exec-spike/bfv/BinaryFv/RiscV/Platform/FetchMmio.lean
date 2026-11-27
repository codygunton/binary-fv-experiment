import BinaryFv.RiscV.Platform.FetchMemory

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated fixed CLINT and signature layouts exclude this physical fetch address. -/
def FetchMMIOAddressExcluded (pc : BitVec 64) : Prop :=
  ((Sail.BitVec.toNatInt plat_clint_base ≤b Sail.BitVec.toNatInt pc) &&
      ((Sail.BitVec.toNatInt pc +i 4) ≤b
        (Sail.BitVec.toNatInt plat_clint_base +i Sail.BitVec.toNatInt plat_clint_size))) = false ∧
    ((Sail.BitVec.toNatInt plat_sig_base ≤b Sail.BitVec.toNatInt pc) &&
      ((Sail.BitVec.toNatInt pc +i 4) ≤b
        (Sail.BitVec.toNatInt plat_sig_base +i Sail.BitVec.toNatInt plat_sig_size))) = false

/--
Direct generated-state/layout facts sufficient to exclude MMIO for a four-byte fetch.

The normal configuration has both CLINT and signature MMIO enabled, so their address-layout
exclusions remain explicit. PMA permission is deliberately not part of this predicate.
-/
def FetchMMIOStateLayoutExcluded (state : State) (pc : BitVec 64) : Prop :=
  FetchMMIOAddressExcluded pc ∧ state.regs.get? htif_tohost_base = some none

/-- The generated fixed CLINT and signature layouts exclude this physical data-access range. -/
def DataMMIOAddressExcluded (address : BitVec 64) (width : Nat) : Prop :=
  ((Sail.BitVec.toNatInt plat_clint_base ≤b Sail.BitVec.toNatInt address) &&
      ((Sail.BitVec.toNatInt address +i width) ≤b
        (Sail.BitVec.toNatInt plat_clint_base +i Sail.BitVec.toNatInt plat_clint_size))) = false ∧
    ((Sail.BitVec.toNatInt plat_sig_base ≤b Sail.BitVec.toNatInt address) &&
      ((Sail.BitVec.toNatInt address +i width) ≤b
        (Sail.BitVec.toNatInt plat_sig_base +i Sail.BitVec.toNatInt plat_sig_size))) = false

/-- Compatibility name for the shared data-range exclusion used by stores. -/
def StoreMMIOAddressExcluded := DataMMIOAddressExcluded

/-- Compatibility name for the shared data-range exclusion used by loads. -/
def LoadMMIOAddressExcluded := DataMMIOAddressExcluded

/--
A four-byte fetch that ends before both fixed MMIO bases avoids them.

Generic: the caller supplies the two bounds. Establishing them for a particular load image is the
target's job, since it depends on where that image is placed.
-/
theorem fetch_mmio_address_excluded_of_before_layout (pc : BitVec 64)
    (beforeClint : pc.toNat + 4 ≤ BitVec.toNat plat_clint_base)
    (beforeSig : pc.toNat + 4 ≤ BitVec.toNat plat_sig_base) :
    FetchMMIOAddressExcluded pc := by
  unfold FetchMMIOAddressExcluded
  constructor
  · unfold Sail.BitVec.toNatInt
    have noClintStart : ¬ BitVec.toNat plat_clint_base ≤ pc.toNat := by
      omega
    simp [noClintStart]
    intro starts
    exact (noClintStart starts).elim
  · unfold Sail.BitVec.toNatInt
    have noSigStart : ¬ BitVec.toNat plat_sig_base ≤ pc.toNat := by
      omega
    simp [noSigStart]
    intro starts
    exact (noSigStart starts).elim

/-- A data-access range ending before both fixed MMIO bases avoids both regions. -/
theorem data_mmio_address_excluded_of_before_layout (address : BitVec 64) (width : Nat)
    (widthPositive : 0 < width)
    (beforeClint : address.toNat + width ≤ BitVec.toNat plat_clint_base)
    (beforeSig : address.toNat + width ≤ BitVec.toNat plat_sig_base) :
    DataMMIOAddressExcluded address width := by
  unfold DataMMIOAddressExcluded
  constructor
  · unfold Sail.BitVec.toNatInt
    have noClintStart : ¬ BitVec.toNat plat_clint_base ≤ address.toNat := by
      omega
    simp [noClintStart]
    intro starts
    exact (noClintStart starts).elim
  · unfold Sail.BitVec.toNatInt
    have noSigStart : ¬ BitVec.toNat plat_sig_base ≤ address.toNat := by
      omega
    simp [noSigStart]
    intro starts
    exact (noSigStart starts).elim

/-- A data-access range starting after both fixed MMIO regions avoids both regions. -/
theorem data_mmio_address_excluded_of_after_layout (address : BitVec 64) (width : Nat)
    (widthPositive : 0 < width)
    (afterClint : BitVec.toNat plat_clint_base + BitVec.toNat plat_clint_size ≤ address.toNat)
    (afterSig : BitVec.toNat plat_sig_base + BitVec.toNat plat_sig_size ≤ address.toNat) :
    DataMMIOAddressExcluded address width := by
  unfold DataMMIOAddressExcluded
  constructor
  · unfold Sail.BitVec.toNatInt
    simp
    intro _
    have strict : BitVec.toNat plat_clint_base + BitVec.toNat plat_clint_size <
        address.toNat + width := by omega
    exact_mod_cast strict
  · unfold Sail.BitVec.toNatInt
    simp
    intro _
    have strict : BitVec.toNat plat_sig_base + BitVec.toNat plat_sig_size <
        address.toNat + width := by omega
    exact_mod_cast strict

/-- Compatibility wrapper for store proofs. -/
theorem store_mmio_address_excluded_of_before_layout (address : BitVec 64) (width : Nat)
    (widthPositive : 0 < width)
    (beforeClint : address.toNat + width ≤ BitVec.toNat plat_clint_base)
    (beforeSig : address.toNat + width ≤ BitVec.toNat plat_sig_base) :
    StoreMMIOAddressExcluded address width :=
  data_mmio_address_excluded_of_before_layout address width widthPositive beforeClint beforeSig

/-! ## The MMIO dispatch is gone

exec-spike repair: the specialised `within_clint`, `within_sig` and `within_htif_*` are the pure
`false` (`within_mmio_readable_false`/`within_mmio_writable_false` in `Logic/Framing.lean`), so the
`Runs`-valued MMIO selectors (`storeMemoryNoMMIO_of_state_layout_excluded`,
`loadMemoryNoMMIO_of_state_layout_excluded`, `fetchMemoryNoMMIO_of_state_layout_excluded`,
`within_htif_readable_runs`, `fetchMemoryNoMMIO_of_agree` and their private helpers) no longer
type-check and served only the removed `noMMIO` premises; they were deleted. -/

/-- The generated HTIF window test, as a pure function of the configured base and the address. -/
def htifWindowFlag (pc : BitVec 64) (width : Nat) : Option physaddrbits → Bool
  | none => false
  | some base =>
      zopz0zI_u pc (Sail.BitVec.addInt base (htif_tohost_size : Int)) &&
        zopz0zK_u (Sail.BitVec.addInt pc (width : Int)) base

/-- The layout-and-state form transports too, which is the shape a runner that pins
`htif_tohost_base = none` at its entry state actually carries. -/
theorem fetchMMIOStateLayoutExcluded_of_agree {before after : State} {pc : BitVec 64}
    (agree : Agree platformPreserved before after) (h : FetchMMIOStateLayoutExcluded before pc) :
    FetchMMIOStateLayoutExcluded after pc :=
  ⟨h.1, (platformPreserved_htifBase agree).trans h.2⟩

end BinaryFv.RiscV
