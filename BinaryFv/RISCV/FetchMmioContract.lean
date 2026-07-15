import BinaryFv.RISCV.FetchMemoryContract

namespace BinaryFv.RISCV

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

private theorem within_clint_of_address_excluded (state : State) (pc : BitVec 64)
    (excluded : FetchMMIOAddressExcluded pc) :
    Runs (within_clint (physaddr.Physaddr pc) 4) state state false := by
  rcases excluded with ⟨clint, _⟩
  unfold Runs within_clint
  simp [plat_have_clint, clint]
  rfl

private theorem within_sig_of_address_excluded (state : State) (pc : BitVec 64)
    (excluded : FetchMMIOAddressExcluded pc) :
    Runs (within_sig (physaddr.Physaddr pc) 4) state state false := by
  rcases excluded with ⟨_, sig⟩
  unfold Runs within_sig
  simp [plat_have_sig, sig]
  rfl

private theorem within_htif_readable_of_disabled (state : State) (pc : BitVec 64)
    (disabled : state.regs.get? htif_tohost_base = some none) :
    Runs (within_htif_readable (physaddr.Physaddr pc) 4) state state false := by
  have hRead : Runs (Sail.readReg htif_tohost_base) state state none :=
    readReg_run state htif_tohost_base none disabled
  unfold within_htif_readable within_htif_writable
  apply Runs.bind hRead
  rfl

/-- Derive the exact generated sparse-RAM selector from explicit state and layout facts. -/
theorem fetchMemoryNoMMIO_of_state_layout_excluded (state : State) (pc : BitVec 64)
    (excluded : FetchMMIOStateLayoutExcluded state pc) : FetchMemoryNoMMIO state pc := by
  rcases excluded with ⟨addressExcluded, htifDisabled⟩
  unfold FetchMemoryNoMMIO within_mmio_readable
  simp only [get_config_rvfi]
  apply Runs.bind (within_clint_of_address_excluded state pc addressExcluded)
  apply Runs.bind (within_sig_of_address_excluded state pc addressExcluded)
  apply Runs.bind (within_htif_readable_of_disabled state pc htifDisabled)
  rfl

end BinaryFv.RISCV
