import BinaryFv.Keccak.Reth.Proof.XorBlock.StoreWord

/-!
# The `xor_block` loop invariant and abstract premises
-/

namespace BinaryFv.Keccak.XorBlock
open BinaryFv.Binary
open BinaryFv.Keccak.SpecBridge
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open BinaryFv.Keccak
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Deliverable 4b: loop invariant and abstract configured-machine premises

Mirrors `MemcpyContract`'s `MemcpyInv` / `AbstractPlatform` / `AbstractDataAccess` for `xor_block`.
`origLane m` is the original 64-bit state word of lane `m`; `inByte j` the input byte at
`input0 + j`; `inputLane k` the little-endian input lane (matching `assemble_leWord`). -/

/-- The little-endian 64-bit input lane assembled from the 8 input bytes at `input0 + 8k`. -/
def inputLane (inByte : Nat → BitVec 8) (k : Nat) : BitVec 64 :=
  BitVec.cast (by rfl) (leWord [inByte (8 * k + 0), inByte (8 * k + 1), inByte (8 * k + 2),
    inByte (8 * k + 3), inByte (8 * k + 4), inByte (8 * k + 5), inByte (8 * k + 6),
    inByte (8 * k + 7)])

/-- Instruction fetch addresses of `xor_block` (entry, 29 body instructions, exit). -/
@[reducible] def IsBodyPc (pc : BitVec 64) : Prop :=
  pc = BitVec.ofNat 64 0x10c6c ∨ pc = BitVec.ofNat 64 0x10c70 ∨ pc = BitVec.ofNat 64 0x10c74 ∨
  pc = BitVec.ofNat 64 0x10c78 ∨ pc = BitVec.ofNat 64 0x10c7c ∨ pc = BitVec.ofNat 64 0x10c80 ∨
  pc = BitVec.ofNat 64 0x10c84 ∨ pc = BitVec.ofNat 64 0x10c88 ∨ pc = BitVec.ofNat 64 0x10c8c ∨
  pc = BitVec.ofNat 64 0x10c90 ∨ pc = BitVec.ofNat 64 0x10c94 ∨ pc = BitVec.ofNat 64 0x10c98 ∨
  pc = BitVec.ofNat 64 0x10c9c ∨ pc = BitVec.ofNat 64 0x10ca0 ∨ pc = BitVec.ofNat 64 0x10ca4 ∨
  pc = BitVec.ofNat 64 0x10ca8 ∨ pc = BitVec.ofNat 64 0x10cac ∨ pc = BitVec.ofNat 64 0x10cb0 ∨
  pc = BitVec.ofNat 64 0x10cb4 ∨ pc = BitVec.ofNat 64 0x10cb8 ∨ pc = BitVec.ofNat 64 0x10cbc ∨
  pc = BitVec.ofNat 64 0x10cc0 ∨ pc = BitVec.ofNat 64 0x10cc4 ∨ pc = BitVec.ofNat 64 0x10cc8 ∨
  pc = BitVec.ofNat 64 0x10ccc ∨ pc = BitVec.ofNat 64 0x10cd0 ∨ pc = BitVec.ofNat 64 0x10cd4 ∨
  pc = BitVec.ofNat 64 0x10cd8 ∨ pc = BitVec.ofNat 64 0x10cdc ∨ pc = BitVec.ofNat 64 0x10ce0 ∨
  pc = BitVec.ofNat 64 0x10ce4 ∨ pc = BitVec.ofNat 64 0x10ce8

/-- Abstract configured-machine fetch/decode platform (stage-2 trust boundary). -/
def AbstractPlatform (base : State) : Prop :=
  BinaryFv.RiscV.AbstractPlatform NonW IsBodyPc base

/-- Abstract Zicfilp landing-pad update for the leaf `ret` (stage-2 trust boundary). -/
def AbstractElp (base : State) : Prop :=
  BinaryFv.RiscV.AbstractElp NonW (fun r => r = .Regidx 1#5) base

/-- Abstract load/store data-access preconditions for lane `k`: the 8 single-byte input loads (via
`a1 = input0 + 8k`), the 8-byte state-lane load and store (via `a0 = state0 + 8k`).  Never discharged
here (the stage-2 trust boundary). -/
def AbstractDataAccess (state0 input0 : BitVec 64) (base : State) : Prop :=
  ∀ (k : Nat) (t : State), k < 17 → StableAgree base t →
    (t.regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) →
      ∀ j : Nat, j < 8 →
        Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) (BitVec.ofNat 12 j))
          (Load Data) 1) t t
          (.Ext_DataAddr_OK (virtaddr.Virtaddr (input0 + BitVec.ofNat 64 (8 * k + j)))) ∧
        Runs (phys_access_check (Load Data) PBMT_PMA .Machine
          (physaddr.Physaddr (input0 + BitVec.ofNat 64 (8 * k + j))) 1 false) t t none ∧
        Runs (within_mmio_readable (physaddr.Physaddr (input0 + BitVec.ofNat 64 (8 * k + j))) 1)
          t t false) ∧
    (t.regs.get? x10 = some (state0 + BitVec.ofNat 64 (8 * k)) →
      (Runs (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) 0#12) (Load Data) 8)
          t t (.Ext_DataAddr_OK (virtaddr.Virtaddr (state0 + BitVec.ofNat 64 (8 * k)))) ∧
        is_aligned_vaddr (virtaddr.Virtaddr (state0 + BitVec.ofNat 64 (8 * k))) 8 = true ∧
        Runs (phys_access_check (Load Data) PBMT_PMA .Machine
          (physaddr.Physaddr (state0 + BitVec.ofNat 64 (8 * k))) 8 false) t t none ∧
        Runs (within_mmio_readable (physaddr.Physaddr (state0 + BitVec.ofNat 64 (8 * k))) 8)
          t t false) ∧
      (Runs (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) 0#12) (Store Data) 8)
          t t (.Ext_DataAddr_OK (virtaddr.Virtaddr (state0 + BitVec.ofNat 64 (8 * k)))) ∧
        is_aligned_vaddr (virtaddr.Virtaddr (state0 + BitVec.ofNat 64 (8 * k))) 8 = true ∧
        Runs (phys_access_check (Store Data) PBMT_PMA .Machine
          (physaddr.Physaddr (state0 + BitVec.ofNat 64 (8 * k))) 8 false) t t none ∧
        Runs (within_mmio_writable (physaddr.Physaddr (state0 + BitVec.ofNat 64 (8 * k))) 8)
          t t false))

theorem AbstractPlatform.mono {s s' : State} (h : StableAgree s s') (hp : AbstractPlatform s) :
    AbstractPlatform s' :=
  BinaryFv.RiscV.AbstractPlatform.mono h hp

theorem AbstractElp.mono {s s' : State} (h : StableAgree s s') (he : AbstractElp s) :
    AbstractElp s' :=
  BinaryFv.RiscV.AbstractElp.mono h he

theorem AbstractDataAccess.mono {state0 input0 : BitVec 64} {s s' : State} (h : StableAgree s s')
    (hd : AbstractDataAccess state0 input0 s) : AbstractDataAccess state0 input0 s' :=
  fun k t hk hst => hd k t hk (fun r hr => (hst r hr).trans (h r hr))

theorem StableAgree.afterInc {base t : State} (h : StableAgree base t) :
    StableAgree base (tryStepControlFlowAfterIncrement t) :=
  fun r hr => (afterIncGet t r hr.2.2.2.1).trans (h r hr)

/-- Assemble a `StepPlatform` bundle from the abstract platform field. -/
theorem mkStepPlatform {s : State} (s_k : State) (mseccfgBits pc : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hplat : AbstractPlatform s) (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hSt : StableAgree s s_k)
    (hPCafter : (tryStepControlFlowAfterIncrement s_k).regs.get? PC = some pc)
    (hbody : IsBodyPc pc)
    (hbytes : FetchBytesAt (tryStepControlFlowAfterIncrement s_k) pc b0 b1 b2 b3) :
    StepPlatform s_k pc b0 b1 b2 b3 mseccfgBits := by
  have hStA : StableAgree s (tryStepControlFlowAfterIncrement s_k) := hSt.afterInc
  obtain ⟨hfbp, hmmio, hint, hlp⟩ := hplat _ pc hStA hPCafter hbody
  exact ⟨hfbp, hmmio, hbytes, hint, hlp, (hStA cur_privilege (by decide)).trans hcur,
    (hStA mseccfg (by decide)).trans hmseccfg⟩

/-! ### `StableAgree` per-transition preservation -/

/-- A GP-writing fall-through retirement only writes registers in `W`. -/
theorem stableAgree_gp (base : State) (pc ret : BitVec 64) (rd : Register) (v : RegisterType rd)
    (hrdW : rd = x5 ∨ rd = x10 ∨ rd = x11 ∨ rd = x12 ∨ rd = x13 ∨ rd = x14 ∨ rd = x15 ∨
      rd = x16 ∨ rd = x17) :
    StableAgree base (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  have hrd : r ≠ rd := by rcases hrdW with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact hr.2.2.2.2.1 | exact hr.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.1
      | exact hr.2.2.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.2.2.2.1
      | exact hr.2.2.2.2.2.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.2.2.2.2.2.2
  rw [retiredFrameGet _ _ _ r hr.1 hr.2.2.1]
  show ((coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert rd v).get? r
      = base.regs.get? r
  rw [gpFrameGet (tryStepControlFlowAfterIncrement base) pc rd v r hrd hr.2.1]
  exact afterIncGet base r hr.2.2.2.1

/-- A taken-branch / jump retirement only writes registers in `W`. -/
theorem stableAgree_jump (base : State) (pc tgt ret : BitVec 64) :
    StableAgree base (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt) tgt ret) := by
  intro r hr
  rw [jumpRetiredGet base pc tgt ret r hr.1 hr.2.2.1 hr.2.1 hr.2.2.2.1]

/-- A not-taken branch retirement only writes registers in `W`. -/
theorem stableAgree_notTaken (base : State) (pc ret : BitVec 64) :
    StableAgree base (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  rw [retiredFrameGet _ _ _ r hr.1 hr.2.2.1, coreGetInc _ pc r hr.2.1]
  exact afterIncGet base r hr.2.2.2.1

/-- Read a register untouched by a not-taken branch retirement (works for `W` registers too, as long
as it is not one of the four control registers). -/
theorem notTakenGet (base : State) (pc ret : BitVec 64) (r : Register)
    (hPC : r ≠ PC) (hmr : r ≠ minstret) (hnpc : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret).regs.get? r = base.regs.get? r := by
  rw [retiredFrameGet _ _ _ r hPC hmr, coreGetInc _ pc r hnpc]
  exact afterIncGet base r hmi

/-- A memory-writing (`sd`) retirement only writes registers in `W`. -/
theorem stableAgree_store (base s' : State) (pc ret : BitVec 64)
    (regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs) :
    StableAgree base (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  rw [retiredFrameGet _ _ _ r hr.1 hr.2.2.1, regsEq,
    coreGetInc (tryStepControlFlowAfterIncrement base) pc r hr.2.1]
  exact afterIncGet base r hr.2.2.2.1

/-! ### The loop invariant at the loop head `0x10c74` -/

/-- The `xor_block` loop invariant: about to run iteration `k` at the loop head `0x10c74`.

`sref` is the fixed reference state the compositional frame is measured against (the caller's entry
state): `hstable` and `hframe` say the run so far has touched no register outside `W` and no memory
outside the 136-byte rate window. -/
structure XorBlockInv (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (sref : State) (k : Nat) (s : State) :
    Prop where
  hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10c74)
  ha0 : s.regs.get? x10 = some (state0 + BitVec.ofNat 64 (8 * k))
  ha1 : s.regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k))
  ha2 : s.regs.get? x12 = some (BitVec.ofNat 64 (136 - 8 * k))
  hra : s.regs.get? x1 = some retAddr
  hcur : s.regs.get? cur_privilege = some Privilege.Machine
  hmstatus : s.regs.get? mstatus = some mstatusBits
  hmprv : _get_Mstatus_MPRV mstatusBits = 0#1
  hmseccfg : s.regs.get? mseccfg = some mseccfgBits
  hhart : s.regs.get? hart_state = some (.HART_ACTIVE ())
  hinhibit : s.regs.get? mcountinhibit = some inhibit
  hnotInhibited : _get_Counterin_IR inhibit = 0#1
  hcfg : s.regs.get? minstretcfg = some cfg
  hmachineEnabled : _get_CountSmcntrpmf_MINH cfg = 0#1
  hminstret : ∃ v, s.regs.get? minstret = some v
  himageEq : Artifact.programImage = .ok image
  hmatches : image.matchesMemory s.mem
  hunproc : ∀ m i : Nat, k ≤ m → m < 25 → i < 8 →
    s.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat = some ((origLane m).extractLsb' (8 * i) 8)
  hproc : ∀ m i : Nat, m < k → i < 8 →
    s.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat =
      some ((origLane m ^^^ inputLane inByte m).extractLsb' (8 * i) 8)
  hinput : ∀ j : Nat, j < 136 → s.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (inByte j)
  hk : k ≤ 17
  hstateFits : state0.toNat + 200 ≤ 2 ^ 64
  hinputFits : input0.toNat + 136 ≤ 2 ^ 64
  hstateImg : ∀ j : Nat, j < 200 → image.readByte? (state0 + BitVec.ofNat 64 j).toNat = none
  hdisj : ∀ j j' : Nat, j < 200 → j' < 136 →
    (state0 + BitVec.ofNat 64 j).toNat ≠ (input0 + BitVec.ofNat 64 j').toNat
  hplat : AbstractPlatform s
  hdata : AbstractDataAccess state0 input0 s
  hElp : AbstractElp s
  /-- Register frame: nothing outside `W` has been written since `sref`. -/
  hstable : StableAgree sref s
  /-- Memory frame: nothing outside the 136-byte rate window has been written since `sref`. -/
  hframe : MemFramed state0 (BitVec.ofNat 64 136) sref s

/-! ### Arithmetic and register-tracking helpers for the advance -/

/-- Read a GP register through the counter-increment / `nextPC` writes back to the pre-step state. -/
theorem coreGetGP (sN : State) (pc : BitVec 64) (r : Register) (hnp : r ≠ nextPC)
    (hmi : r ≠ minstret_increment) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement sN) pc).regs.get? r =
      sN.regs.get? r :=
  (coreGetInc (tryStepControlFlowAfterIncrement sN) pc r hnp).trans (afterIncGet sN r hmi)

/-- `sign_extend` of the 12-bit `8`. -/
theorem sext8 : sign_extend (m := 64) (8#12) = BitVec.ofNat 64 8 := by
  simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide

/-- `sign_extend` of the 12-bit `-8` (`0xff8`). -/
theorem sextm8 : sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (2 ^ 64 - 8) := by
  simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide

/-- Advancing a base pointer by 8 (`a0 += 8`, `a1 += 8`). -/
theorem incBy8 (X : BitVec 64) (k : Nat) :
    X + BitVec.ofNat 64 (8 * k) + sign_extend (m := 64) 8#12 = X + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [sext8, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- Decrementing the counter by 8 (`a2 -= 8`). -/
theorem decBy8 (k : Nat) (hk : k ≤ 16) :
    BitVec.ofNat 64 (136 - 8 * k) + sign_extend (m := 64) (0xff8#12)
      = BitVec.ofNat 64 (136 - 8 * (k + 1)) := by
  rw [sextm8]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The counter `136 - 8k` is nonzero as a bit-vector for `k < 17`. -/
theorem a2_ne_zero (k : Nat) (hk : k < 17) : BitVec.ofNat 64 (136 - 8 * k) ≠ zero_reg := by
  intro heq
  have h1 : (BitVec.ofNat 64 (136 - 8 * k)).toNat = (zero_reg : BitVec 64).toNat := by rw [heq]
  rw [BitVec.toNat_ofNat] at h1
  have hz : (zero_reg : BitVec 64).toNat = 0 := by decide
  rw [hz] at h1
  have hbound : 8 * k < 136 := by omega
  omega

/-- The counter `136 - 8k` is zero as a bit-vector when `k = 17`. -/
theorem a2_eq_zero : BitVec.ofNat 64 (136 - 8 * 17) = zero_reg := by decide

end BinaryFv.Keccak.XorBlock
