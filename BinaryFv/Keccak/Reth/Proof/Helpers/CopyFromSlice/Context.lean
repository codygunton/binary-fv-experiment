import BinaryFv.Keccak.Reth.Proof.Helpers.CopyFromSlice.JrStep

/-!
# Abstract setup premises, and their transport into `memcpy`'s premises
-/

namespace BinaryFv.Keccak
open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Abstract setup premises and transport into `memcpy`'s abstract premises

The setup steps rename `a1`/`a2` and clobber `t1 = x6`, so the post-setup state does *not*
`StableAgree` (in `memcpy`'s sense, `NonW`) with the entry state: `x6`, `x11`, `x12` change.  We
carry the setup's abstract platform / data-access / landing-pad premises about the entry state `s`
under `CfsStableAgree` — agreement on every `NonW` register *except* `x6`, `x11`, `x12`.  Every setup
write lands in `memcpy`'s `W ∪ {x6, x11, x12}`, so `CfsStableAgree s s_k` is preserved across all
setup steps, and the post-setup state `s6` satisfies `CfsStableAgree s s6`.  The transport lemmas
then discharge `memcpy`'s `AbstractPlatform s6` / `AbstractDataAccess … s6` / `AbstractElp s6` purely
at the `StableAgree` level, never unfolding a genuine platform obligation. -/

/-- Two states agree on every register the setup does not clobber: `NonW` and not in
`{x6, x11, x12}`.  (The setup writes `x14 ∈ W`, `x11`, `x12`, `x6`, and the control registers, all
outside this set.) -/
def CfsStableAgree (base t : State) : Prop :=
  ∀ r : Register, NonW r → r ≠ x6 → r ≠ x11 → r ≠ x12 → t.regs.get? r = base.regs.get? r

theorem CfsStableAgree.refl (s : State) : CfsStableAgree s s := fun _ _ _ _ _ => rfl

/-- `CfsStableAgree` survives the generated counter-increment write. -/
theorem CfsStableAgree.afterInc {base t : State} (h : CfsStableAgree base t) :
    CfsStableAgree base (tryStepControlFlowAfterIncrement t) :=
  fun r hr hr6 hr11 hr12 => (afterIncGet t r hr.2.2.2.1).trans (h r hr hr6 hr11 hr12)

/-- `CfsStableAgree` lifts through the counter-increment and `nextPC` writes of the execute state. -/
theorem cfsCoreStableAgree {s : State} (s_k : State) (pc : BitVec 64)
    (hSt : CfsStableAgree s s_k) :
    CfsStableAgree s (coreControlFlowNextState (tryStepControlFlowAfterIncrement s_k) pc) :=
  fun r hr hr6 hr11 hr12 =>
    (coreGetInc' (tryStepControlFlowAfterIncrement s_k) pc r hr.2.1).trans
      ((afterIncGet s_k r hr.2.2.2.1).trans (hSt r hr hr6 hr11 hr12))

/-- The fetch addresses reachable in this contract: the 6 copy_from_slice setup addresses plus every
`memcpy` fetch address (`IsBodyPc`), positioned to satisfy both the setup fetches and — after
transport — the `memcpy` body fetches. -/
@[reducible] def IsCfsPc (pc : BitVec 64) : Prop :=
  pc = BitVec.ofNat 64 0x10c44 ∨ pc = BitVec.ofNat 64 0x10c48 ∨ pc = BitVec.ofNat 64 0x10c4c ∨
  pc = BitVec.ofNat 64 0x10c50 ∨ pc = BitVec.ofNat 64 0x10c54 ∨ pc = BitVec.ofNat 64 0x10c58 ∨
  IsBodyPc pc

/-- Abstract configured-machine fetch/decode platform for the setup and `memcpy` fetch addresses,
quantified over `CfsStableAgree`-equal states.  Never discharged here (the stage-2 trust boundary). -/
def CfsAbstractPlatform (base : State) : Prop :=
  ∀ (t : State) (pc : BitVec 64), CfsStableAgree base t → t.regs.get? PC = some pc → IsCfsPc pc →
    FetchBasePlatform t pc ∧ FetchMemoryNoMMIO t pc ∧ InterruptDisabled t ∧ LandingPadNotExpected t

/-- Abstract load/store data-access preconditions for the `memcpy` tail-call, quantified over
`CfsStableAgree`-equal states.  Same body as `memcpy`'s `AbstractDataAccess`, weakened to
`CfsStableAgree`.  Never discharged here (the stage-2 trust boundary). -/
def CfsAbstractDataAccess (n dst src : BitVec 64) (base : State) : Prop :=
  ∀ (j : Nat) (t : State), j < n.toNat → CfsStableAgree base t →
    (t.regs.get? x13 = some (src + BitVec.ofNat 64 j) →
      Runs (get_transformed_data_addr (.Regidx 13#5) (sign_extend (m := 64) 0#12) (Load Data) 1)
        t t (.Ext_DataAddr_OK (virtaddr.Virtaddr (src + BitVec.ofNat 64 j))) ∧
      Runs (phys_access_check (Load Data) PBMT_PMA .Machine
        (physaddr.Physaddr (src + BitVec.ofNat 64 j)) 1 false) t t none ∧
      Runs (within_mmio_readable (physaddr.Physaddr (src + BitVec.ofNat 64 j)) 1) t t false) ∧
    (t.regs.get? x14 = some (dst + BitVec.ofNat 64 j) →
      Runs (get_transformed_data_addr (.Regidx 14#5) (sign_extend (m := 64) 0#12) (Store Data) 1)
        t t (.Ext_DataAddr_OK (virtaddr.Virtaddr (dst + BitVec.ofNat 64 j))) ∧
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine
        (physaddr.Physaddr (dst + BitVec.ofNat 64 j)) 1 false) t t none ∧
      Runs (within_mmio_writable (physaddr.Physaddr (dst + BitVec.ofNat 64 j)) 1) t t false)

/-- Abstract Zicfilp landing-pad update, quantified over the register operand (`t1` for the `jr`
tail-call, `ra` for `memcpy`'s `ret`) and over `CfsStableAgree`-equal states.  Never discharged here
(the stage-2 trust boundary). -/
def CfsAbstractElp (base : State) : Prop :=
  ∀ (t : State) (rs1 : regidx), CfsStableAgree base t → Runs (update_elp_state rs1) t t ()

/-- Transport the setup platform premise (about the entry state `s`) into `memcpy`'s
`AbstractPlatform` about the post-setup state `s6`, given `CfsStableAgree s s6`. -/
theorem cfsPlatformTransport {s s6 : State} (hpres : CfsStableAgree s s6)
    (h : CfsAbstractPlatform s) : AbstractPlatform s6 := by
  intro t pc hSt hPC hbody
  exact h t pc (fun r hr hr6 hr11 hr12 => (hSt r hr).trans (hpres r hr hr6 hr11 hr12)) hPC
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbody))))))

/-- Transport the setup data-access premise into `memcpy`'s `AbstractDataAccess` about `s6`. -/
theorem cfsDataTransport {n dst src : BitVec 64} {s s6 : State} (hpres : CfsStableAgree s s6)
    (h : CfsAbstractDataAccess n dst src s) : AbstractDataAccess n dst src s6 := by
  intro j t hj hSt
  exact h j t hj (fun r hr hr6 hr11 hr12 => (hSt r hr).trans (hpres r hr hr6 hr11 hr12))

/-- Transport the setup landing-pad premise into `memcpy`'s `AbstractElp` about `s6` (for `ra`). -/
theorem cfsElpTransport {s s6 : State} (hpres : CfsStableAgree s s6)
    (h : CfsAbstractElp s) : AbstractElp s6 := by
  intro t r hr hSt
  subst hr
  exact h t (.Regidx 1#5) (fun r hr hr6 hr11 hr12 => (hSt r hr).trans (hpres r hr hr6 hr11 hr12))

/-- Assemble a `StepPlatform` bundle for a setup fetch address from the abstract setup platform. -/
theorem mkCfsStepPlatform {s : State} (s_k : State) (mseccfgBits pc : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hplat : CfsAbstractPlatform s) (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hSt : CfsStableAgree s s_k)
    (hPCafter : (tryStepControlFlowAfterIncrement s_k).regs.get? PC = some pc)
    (hbody : IsCfsPc pc)
    (hbytes : FetchBytesAt (tryStepControlFlowAfterIncrement s_k) pc b0 b1 b2 b3) :
    StepPlatform s_k pc b0 b1 b2 b3 mseccfgBits := by
  have hStA : CfsStableAgree s (tryStepControlFlowAfterIncrement s_k) := hSt.afterInc
  obtain ⟨hfbp, hmmio, hint, hlp⟩ := hplat _ pc hStA hPCafter hbody
  exact ⟨hfbp, hmmio, hbytes, hint, hlp,
    (hStA cur_privilege (by decide) (by decide) (by decide) (by decide)).trans hcur,
    (hStA mseccfg (by decide) (by decide) (by decide) (by decide)).trans hmseccfg⟩

/-! ### `CfsStableAgree` preservation across the setup step shapes -/

/-- A GP-writing fall-through (`rd ∈ {x6, x11, x12, x14}`) preserves `CfsStableAgree`. -/
theorem cfsAgree_fallThrough (s base : State) (pc ret : BitVec 64) (rd : Register)
    (v : RegisterType rd) (hrd : ∀ r, NonW r → r ≠ x6 → r ≠ x11 → r ≠ x12 → r ≠ rd)
    (h : CfsStableAgree s base) :
    CfsStableAgree s (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr hr6 hr11 hr12
  exact (fallThroughRetiredGet base pc ret rd v r hr.1 hr.2.2.1 (hrd r hr hr6 hr11 hr12) hr.2.1
    hr.2.2.2.1).trans (h r hr hr6 hr11 hr12)

/-- A not-taken branch preserves `CfsStableAgree`. -/
theorem cfsAgree_notTaken (s base : State) (pc ret : BitVec 64) (h : CfsStableAgree s base) :
    CfsStableAgree s (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr hr6 hr11 hr12
  exact (retiredFrameGet _ _ _ r hr.1 hr.2.2.1).trans
    ((coreGetInc' _ pc r hr.2.1).trans ((afterIncGet base r hr.2.2.2.1).trans
      (h r hr hr6 hr11 hr12)))

/-- A taken branch / jump preserves `CfsStableAgree`. -/
theorem cfsAgree_jump (s base : State) (pc target ret : BitVec 64) (h : CfsStableAgree s base) :
    CfsStableAgree s (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc target) target ret) := by
  intro r hr hr6 hr11 hr12
  exact (jumpRetiredGet base pc target ret r hr.1 hr.2.2.1 hr.2.1 hr.2.2.2.1).trans
    (h r hr hr6 hr11 hr12)

/-- Compose the setup's `CfsStableAgree` with `memcpy`'s (stronger) `StableAgree`: `memcpy` only
writes registers in `W`, so their composition still agrees off `W ∪ {x6, x11, x12}` — the honest
whole-`copy_from_slice` register postcondition (the setup does clobber `x6`, `x11`, `x12`). -/
theorem cfsAgree_compose {s s6 s' : State} (h1 : CfsStableAgree s s6) (h2 : StableAgree s6 s') :
    CfsStableAgree s s' :=
  fun r hr hr6 hr11 hr12 => (h2 r hr).trans (h1 r hr hr6 hr11 hr12)

end BinaryFv.Keccak
