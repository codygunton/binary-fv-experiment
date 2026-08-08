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

instance (address : BitVec 64) (width : Nat) : Decidable (DataMMIOAddressExcluded address width) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Compatibility name for the shared data-range exclusion used by stores. -/
abbrev StoreMMIOAddressExcluded := DataMMIOAddressExcluded

/-- Compatibility name for the shared data-range exclusion used by loads. -/
abbrev LoadMMIOAddressExcluded := DataMMIOAddressExcluded

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

private theorem within_clint_data_of_address_excluded (state : State) (address : BitVec 64)
    (width : Nat) (excluded : DataMMIOAddressExcluded address width) :
    Runs (within_clint (physaddr.Physaddr address) width) state state false := by
  rcases excluded with ⟨clint, _⟩
  unfold Runs within_clint
  simp [plat_have_clint, clint]
  rfl

private theorem within_sig_data_of_address_excluded (state : State) (address : BitVec 64)
    (width : Nat) (excluded : DataMMIOAddressExcluded address width) :
    Runs (within_sig (physaddr.Physaddr address) width) state state false := by
  rcases excluded with ⟨_, sig⟩
  unfold Runs within_sig
  simp [plat_have_sig, sig]
  rfl

private theorem within_htif_writable_of_disabled (state : State) (address : BitVec 64)
    (width : Nat) (disabled : state.regs.get? htif_tohost_base = some none) :
    Runs (within_htif_writable (physaddr.Physaddr address) width) state state false := by
  have read : Runs (Sail.readReg htif_tohost_base) state state none :=
    readReg_run state htif_tohost_base none disabled
  unfold within_htif_writable
  exact Runs.bind read rfl

/-- Derive the generated writable-MMIO dispatch result from explicit layout and HTIF facts. -/
theorem storeMemoryNoMMIO_of_state_layout_excluded (state : State) (address : BitVec 64)
    (width : Nat) (addressExcluded : StoreMMIOAddressExcluded address width)
    (htifDisabled : state.regs.get? htif_tohost_base = some none) :
    Runs (within_mmio_writable (physaddr.Physaddr address) width) state state false := by
  unfold within_mmio_writable
  simp only [get_config_rvfi]
  apply Runs.bind (within_clint_data_of_address_excluded state address width addressExcluded)
  apply Runs.bind (within_sig_data_of_address_excluded state address width addressExcluded)
  apply Runs.bind (within_htif_writable_of_disabled state address width htifDisabled)
  rfl

/-- Derive the generated readable-MMIO dispatch result for an arbitrary data-load width. -/
theorem loadMemoryNoMMIO_of_state_layout_excluded (state : State) (address : BitVec 64)
    (width : Nat) (addressExcluded : LoadMMIOAddressExcluded address width)
    (htifDisabled : state.regs.get? htif_tohost_base = some none) :
    Runs (within_mmio_readable (physaddr.Physaddr address) width) state state false := by
  unfold within_mmio_readable
  simp only [get_config_rvfi]
  apply Runs.bind (within_clint_data_of_address_excluded state address width addressExcluded)
  apply Runs.bind (within_sig_data_of_address_excluded state address width addressExcluded)
  apply Runs.bind (within_htif_writable_of_disabled state address width htifDisabled)
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
  · unfold Sail.BitVec.toNatInt
    have noSigStart : ¬ BitVec.toNat plat_sig_base ≤ pc.toNat := by
      omega
    simp [noSigStart]

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
  · unfold Sail.BitVec.toNatInt
    have noSigStart : ¬ BitVec.toNat plat_sig_base ≤ address.toNat := by
      omega
    simp [noSigStart]

/-- Compatibility wrapper for store proofs. -/
theorem store_mmio_address_excluded_of_before_layout (address : BitVec 64) (width : Nat)
    (widthPositive : 0 < width)
    (beforeClint : address.toNat + width ≤ BitVec.toNat plat_clint_base)
    (beforeSig : address.toNat + width ≤ BitVec.toNat plat_sig_base) :
    StoreMMIOAddressExcluded address width :=
  data_mmio_address_excluded_of_before_layout address width widthPositive beforeClint beforeSig

/-- Compatibility wrapper for load proofs. -/
theorem load_mmio_address_excluded_of_before_layout (address : BitVec 64) (width : Nat)
    (widthPositive : 0 < width)
    (beforeClint : address.toNat + width ≤ BitVec.toNat plat_clint_base)
    (beforeSig : address.toNat + width ≤ BitVec.toNat plat_sig_base) :
    LoadMMIOAddressExcluded address width :=
  data_mmio_address_excluded_of_before_layout address width widthPositive beforeClint beforeSig

/-! ## The MMIO dispatch needs no clause of its own

`FetchMemoryNoMMIO` is a *run* rather than a register equation, so it is not obvious from its shape
that a register-agreement clause carries it. It does, and this section proves it rather than arguing
it.

`within_mmio_readable` dispatches to three tests. `within_clint` and `within_sig` read **no**
register at all — they compare the address against `plat_clint_base`/`plat_sig_base`, which are
generated constants — so their results are the same at any two states whatsoever. `within_htif_readable`
is `within_htif_writable`, which reads exactly one register, `htif_tohost_base`, and is a pure
function of it and the address. So agreement on that single register is the whole of what the
dispatch depends on, and `Agree platformPreserved` (which names it) transports the run.

The consequence for the contract layer: the `noMMIO` premise of `tryStepRetRetires` is covered by the
same clause as the other platform premises, and does **not** need a conjunct of its own. -/

/-- The generated HTIF window test, as a pure function of the configured base and the address. -/
def htifWindowFlag (pc : BitVec 64) (width : Nat) : Option physaddrbits → Bool
  | none => false
  | some base =>
      zopz0zI_u pc (Sail.BitVec.addInt base (htif_tohost_size : Int)) &&
        zopz0zK_u (Sail.BitVec.addInt pc (width : Int)) base

private theorem runs_pure_congr {α : Type} {v r : α} {s t : State}
    (h : Runs (pure v : SailM α) s s r) : Runs (pure v : SailM α) t t r := by
  have hv : v = r := by
    unfold Runs at h
    exact congrArg (fun x => match x with | .ok y _ => y | .error _ _ => v) h
  subst hv
  rfl

/-- The HTIF test is exactly `htifWindowFlag` at the configured base. -/
theorem within_htif_readable_runs (pc : BitVec 64) (width : Nat) (base : Option physaddrbits)
    (state : State) (baseRead : state.regs.get? htif_tohost_base = some base) :
    Runs (within_htif_readable (physaddr.Physaddr pc) width) state state
      (htifWindowFlag pc width base) := by
  have read : Runs (readReg htif_tohost_base : SailM (RegisterType htif_tohost_base))
      state state base := readReg_run state htif_tohost_base base baseRead
  unfold within_htif_readable within_htif_writable
  exact Runs.bind read (by cases base <;> rfl)

private theorem within_clint_runs_at (state : State) (pc : BitVec 64) (width : Nat) :
    ∃ flag : Bool, Runs (within_clint (physaddr.Physaddr pc) width) state state flag := by
  unfold within_clint
  simp only [plat_have_clint]
  exact ⟨_, rfl⟩

private theorem within_sig_runs_at (state : State) (pc : BitVec 64) (width : Nat) :
    ∃ flag : Bool, Runs (within_sig (physaddr.Physaddr pc) width) state state flag := by
  unfold within_sig
  simp only [plat_have_sig]
  exact ⟨_, rfl⟩

/-- The CLINT layout test reads no register, so its result is state-independent. -/
private theorem within_clint_congr {before after : State} {pc : BitVec 64} {width : Nat}
    {flag : Bool} (h : Runs (within_clint (physaddr.Physaddr pc) width) before before flag) :
    Runs (within_clint (physaddr.Physaddr pc) width) after after flag := by
  unfold within_clint at h ⊢
  simp only [plat_have_clint] at h ⊢
  exact runs_pure_congr h

/-- The signature layout test reads no register either. -/
private theorem within_sig_congr {before after : State} {pc : BitVec 64} {width : Nat}
    {flag : Bool} (h : Runs (within_sig (physaddr.Physaddr pc) width) before before flag) :
    Runs (within_sig (physaddr.Physaddr pc) width) after after flag := by
  unfold within_sig at h ⊢
  simp only [plat_have_sig] at h ⊢
  exact runs_pure_congr h

/--
**`FetchMemoryNoMMIO` transports across a call that preserves `htif_tohost_base`.**

The `none` branch is not decoration: if the register were absent the generated read would throw, so a
state that satisfies the predicate at all has it, and the transport never needs presence as a
separate hypothesis.
-/
theorem fetchMemoryNoMMIO_of_agree {before after : State} {pc : BitVec 64}
    (agree : Agree platformPreserved before after) (h : FetchMemoryNoMMIO before pc) :
    FetchMemoryNoMMIO after pc := by
  have baseAgrees : after.regs.get? htif_tohost_base = before.regs.get? htif_tohost_base :=
    platformPreserved_htifBase agree
  unfold FetchMemoryNoMMIO within_mmio_readable at h ⊢
  simp only [get_config_rvfi, Bool.false_eq_true, ↓reduceIte] at h ⊢
  obtain ⟨clint, clintRuns⟩ := within_clint_runs_at before pc 4
  obtain ⟨sig, sigRuns⟩ := within_sig_runs_at before pc 4
  have afterClint := runs_bind_inv clintRuns h
  have afterSig := runs_bind_inv sigRuns afterClint
  obtain ⟨base, baseRead⟩ : ∃ base, before.regs.get? htif_tohost_base = some base := by
    cases hb : before.regs.get? htif_tohost_base with
    | some base => exact ⟨base, rfl⟩
    | none =>
      exfalso
      unfold within_htif_readable within_htif_writable Runs at afterSig
      simp [PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
        EStateM.instMonad, EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
        EStateM.instMonadExceptOfOfBacktrackable, getThe, hb] at afterSig
      exact EStateM.Result.noConfusion afterSig
  have afterHtif := runs_bind_inv (within_htif_readable_runs pc 4 base before baseRead) afterSig
  exact Runs.bind (within_clint_congr clintRuns)
    (Runs.bind (within_sig_congr sigRuns)
      (Runs.bind (within_htif_readable_runs pc 4 base after (baseAgrees.trans baseRead))
        (runs_pure_congr afterHtif)))

/-- The layout-and-state form transports too, which is the shape a runner that pins
`htif_tohost_base = none` at its entry state actually carries. -/
theorem fetchMMIOStateLayoutExcluded_of_agree {before after : State} {pc : BitVec 64}
    (agree : Agree platformPreserved before after) (h : FetchMMIOStateLayoutExcluded before pc) :
    FetchMMIOStateLayoutExcluded after pc :=
  ⟨h.1, (platformPreserved_htifBase agree).trans h.2⟩

end BinaryFv.RiscV
