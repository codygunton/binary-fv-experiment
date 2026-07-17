import BinaryFv.Keccak.Reth.Proof.Helpers.Memcpy.Bytes

/-!
# The `memcpy` loop invariant and its `StableAgree` algebra
-/

namespace BinaryFv.Keccak
open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## The loop invariant

`W` is the set of registers the loop body may write (`PC`, `nextPC`, `minstret`,
`minstret_increment`, and the scratch/index GPRs `a3 = x13`, `a4 = x14`, `a5 = x15`).  `StableAgree`
says two states agree on every register outside `W`.  The genuine platform and load/store
data-access preconditions are carried as abstract fields quantified over `StableAgree`-equal states,
so they transport across the loop body's register writes and are re-established at the next loop head
by composing with `StableAgree` — exactly the stage-2 trust boundary. -/

/-- The registers the memcpy loop body may write; everything else is stable. -/
@[reducible] def NonW (r : Register) : Prop :=
  r ≠ PC ∧ r ≠ nextPC ∧ r ≠ minstret ∧ r ≠ minstret_increment ∧
    r ≠ x13 ∧ r ≠ x14 ∧ r ≠ x15

/-- Two states agree on every register the loop body does not write. -/
def StableAgree (base t : State) : Prop := Agree NonW base t

/-- The instruction fetch addresses of the memcpy function (entry, loop head, ret, and body). -/
@[reducible] def IsBodyPc (pc : BitVec 64) : Prop :=
  pc = BitVec.ofNat 64 0x10d18 ∨ pc = BitVec.ofNat 64 0x10d1c ∨ pc = BitVec.ofNat 64 0x10d20 ∨
  pc = BitVec.ofNat 64 0x10d24 ∨ pc = BitVec.ofNat 64 0x10d28 ∨ pc = BitVec.ofNat 64 0x10d2c ∨
  pc = BitVec.ofNat 64 0x10d30 ∨ pc = BitVec.ofNat 64 0x10d34 ∨ pc = BitVec.ofNat 64 0x10d38

/-- Abstract configured-machine fetch/decode platform: for any state agreeing with `base` off `W`
positioned at a memcpy fetch address, the generated base-fetch path is enabled.  Never discharged
here (the stage-2 trust boundary); satisfiable because it holds of the actual configured machine at
these aligned, executable code addresses. -/
def AbstractPlatform (base : State) : Prop :=
  BinaryFv.RiscV.AbstractPlatform NonW IsBodyPc base

/-- Abstract load/store data-access preconditions at every in-range offset, quantified over
`StableAgree`-equal states holding the resolved effective address in `a3`/`a4`.  Never discharged
here (the stage-2 trust boundary). -/
def AbstractDataAccess (n dst src : BitVec 64) (base : State) : Prop :=
  ∀ (j : Nat) (t : State), j < n.toNat → StableAgree base t →
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

/-- The abstract platform survives to a `StableAgree`-equal state. -/
theorem AbstractPlatform.mono {s s' : State} (h : StableAgree s s') (hp : AbstractPlatform s) :
    AbstractPlatform s' :=
  BinaryFv.RiscV.AbstractPlatform.mono h hp

/-- The abstract data access survives to a `StableAgree`-equal state. -/
theorem AbstractDataAccess.mono {n dst src : BitVec 64} {s s' : State} (h : StableAgree s s')
    (hd : AbstractDataAccess n dst src s) : AbstractDataAccess n dst src s' :=
  fun j t hj hst => hd j t hj (fun r hr => (hst r hr).trans (h r hr))

/-- Abstract Zicfilp landing-pad update for the leaf `ret` (`jalr x0, 0(ra)`): a no-op on the
configured machine (Zicfilp expects no landing pad here).  Never discharged here (stage-2 trust
boundary). -/
def AbstractElp (base : State) : Prop :=
  BinaryFv.RiscV.AbstractElp NonW (fun r => r = .Regidx 1#5) base

/-- The abstract Zicfilp update survives to a `StableAgree`-equal state. -/
theorem AbstractElp.mono {s s' : State} (h : StableAgree s s') (he : AbstractElp s) :
    AbstractElp s' :=
  BinaryFv.RiscV.AbstractElp.mono h he

/-- `a5 + 1` at the loop index. -/
theorem ofNat_add_one (i : Nat) :
    BitVec.ofNat 64 i + sign_extend (m := 64) (1#12) = BitVec.ofNat 64 (i + 1) := by
  have hs : sign_extend (m := 64) (1#12) = (1 : BitVec 64) := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1]
  omega

/-- The unsigned byte load's zero-extension is the width-64 setWidth used by the byte store. -/
theorem zero_extend_setWidth (v : BitVec 8) : zero_extend (m := 64) v = BitVec.setWidth 64 v := by
  simp only [zero_extend, Sail.BitVec.zeroExtend]

/-- The memcpy loop invariant at the loop head `L = 0x10d1c` about to run iteration `i`.  `sInit` is
the fixed reference state (the caller's entry state) against which the compositional framing —
`hstable` (registers) and `hframe` (memory) — is tracked. -/
structure MemcpyInv (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (sInit : State) (i : Nat) (s : State) : Prop where
  hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10d1c)
  ha5 : s.regs.get? x15 = some (BitVec.ofNat 64 i)
  ha0 : s.regs.get? x10 = some dst
  ha1 : s.regs.get? x11 = some src
  ha2 : s.regs.get? x12 = some n
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
  hsrc : ∀ j : Nat, j < n.toNat → s.mem.get? (src + BitVec.ofNat 64 j).toNat = some (srcByte j)
  hcopy : ∀ j : Nat, j < i → s.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (srcByte j)
  hle : i ≤ n.toNat
  hnLt : n.toNat < 2 ^ 64
  hsrcFits : src.toNat + n.toNat ≤ 2 ^ 64
  hdstFits : dst.toNat + n.toNat ≤ 2 ^ 64
  hdstImg : ∀ j : Nat, j < n.toNat → image.readByte? (dst + BitVec.ofNat 64 j).toNat = none
  hdisj : ∀ j k : Nat, j < n.toNat → k < n.toNat →
    (dst + BitVec.ofNat 64 j).toNat ≠ (src + BitVec.ofNat 64 k).toNat
  hplat : AbstractPlatform s
  hdata : AbstractDataAccess n dst src s
  hElp : AbstractElp s
  /-- Every register outside the loop's write set `W` still agrees with the reference state. -/
  hstable : StableAgree sInit s
  /-- The exact memory delta so far: every address not among the copied window `[dst, dst+i)` still
  reads its reference-state value. -/
  hframe : ∀ addr : Nat, (∀ j : Nat, j < i → addr ≠ (dst + BitVec.ofNat 64 j).toNat) →
    s.mem.get? addr = sInit.mem.get? addr

/-! ### `StableAgree` algebra and per-step preservation -/

theorem StableAgree.refl (s : State) : StableAgree s s := fun _ _ => rfl

theorem StableAgree.trans {a b c : State} (h1 : StableAgree a b) (h2 : StableAgree b c) :
    StableAgree a c := fun r hr => (h2 r hr).trans (h1 r hr)

/-- The counter-increment write reads through to the base for any register other than
`minstret_increment`. -/
theorem afterIncGet (base : State) (r : Register) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterIncrement base).regs.get? r = base.regs.get? r := by
  simpa [tryStepControlFlowAfterIncrement] using
    writeReg_read_unchanged base minstret_increment r true hmi

/-- The `try_step` retirement postlude (`minstret`, `PC` writes) reads through for any register
other than those two. -/
theorem retiredFrameGet (afterExec : State) (tPC ret : BitVec 64) (r : Register)
    (hPC : r ≠ PC) (hmr : r ≠ minstret) :
    (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? r = afterExec.regs.get? r := by
  calc (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? r
      = (tryStepControlFlowAfterTick afterExec tPC).regs.get? r := by
        simpa [tryStepControlFlowAfterRetired] using
          writeReg_read_unchanged (tryStepControlFlowAfterTick afterExec tPC) minstret r
            (Sail.BitVec.addInt ret 1) hmr
    _ = afterExec.regs.get? r := by
        simpa [tryStepControlFlowAfterTick] using
          writeReg_read_unchanged afterExec PC r tPC hPC

/-- The `nextPC`-overwrite of a jump reads through for any register other than `nextPC`. -/
theorem jumpFrameGet (base : State) (pc tgt : BitVec 64) (r : Register) (hnpc : r ≠ nextPC)
    (hmi : r ≠ minstret_increment) :
    (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt).regs.get? r =
      base.regs.get? r := by
  calc (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt).regs.get? r
      = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.get? r := by
        simpa [controlFlowJumpState] using
          writeReg_read_unchanged
            (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc) nextPC r tgt hnpc
    _ = base.regs.get? r := by
        rw [coreGetInc (tryStepControlFlowAfterIncrement base) pc r hnpc]; exact afterIncGet base r hmi

/-- A taken-branch / jump `try_step` retirement only writes registers in `W`. -/
theorem stableAgree_jump (base : State) (pc tgt ret : BitVec 64) :
    StableAgree base (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt) tgt ret) := by
  intro r hr
  obtain ⟨hPC, hnpc, hmr, hmi, _, _, _⟩ := hr
  rw [retiredFrameGet _ _ _ r hPC hmr, jumpFrameGet base pc tgt r hnpc hmi]

/-- A GP-writing fall-through `try_step` retirement only writes registers in `W`
(`rd ∈ {x13, x14, x15}`). -/
theorem stableAgree_fallThrough (base : State) (pc ret : BitVec 64) (rd : Register)
    (v : RegisterType rd) (hrdW : rd = x13 ∨ rd = x14 ∨ rd = x15) :
    StableAgree base (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  obtain ⟨hPC, hnpc, hmr, hmi, h13, h14, h15⟩ := hr
  have hrd : r ≠ rd := by rcases hrdW with rfl | rfl | rfl <;> assumption
  rw [retiredFrameGet _ _ _ r hPC hmr]
  show ((coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert rd v).get? r
      = base.regs.get? r
  rw [gpFrameGet (tryStepControlFlowAfterIncrement base) pc rd v r hrd hnpc]
  exact afterIncGet base r hmi

/-- A memory-writing fall-through (`sb`) retirement leaves the register file as the plain
`coreControlFlowNextState`, hence only writes `W` registers. -/
theorem stableAgree_sb (base s' : State) (pc ret : BitVec 64)
    (regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs) :
    StableAgree base (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  obtain ⟨hPC, hnpc, hmr, hmi, _, _, _⟩ := hr
  rw [retiredFrameGet _ _ _ r hPC hmr, regsEq, coreGetInc (tryStepControlFlowAfterIncrement base) pc r hnpc]
  exact afterIncGet base r hmi

/-- The counter-increment write preserves `StableAgree` on the right. -/
theorem StableAgree.afterInc {base t : State} (h : StableAgree base t) :
    StableAgree base (tryStepControlFlowAfterIncrement t) :=
  fun r hr => (afterIncGet t r hr.2.2.2.1).trans (h r hr)

/-- Reading a stable register through the counter-increment and `nextPC` writes of the execute
state, back to a `StableAgree`-equal base. -/
theorem coreGetStable {s : State} (s_k : State) (pc : BitVec 64) (r : Register) (hr : NonW r)
    (hSt : StableAgree s s_k) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s_k) pc).regs.get? r =
      s.regs.get? r := by
  rw [coreGetInc (tryStepControlFlowAfterIncrement s_k) pc r hr.2.1, afterIncGet s_k r hr.2.2.2.1]
  exact hSt r hr

/-- The retirement postlude ticks `PC := tPC`. -/
theorem retiredGetPC (afterExec : State) (tPC ret : BitVec 64) :
    (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? PC = some tPC := by
  have h1 : (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? PC
      = (tryStepControlFlowAfterTick afterExec tPC).regs.get? PC := by
    simpa [tryStepControlFlowAfterRetired] using
      writeReg_read_unchanged (tryStepControlFlowAfterTick afterExec tPC) minstret PC
        (Sail.BitVec.addInt ret 1) (by decide)
  rw [h1]
  change (afterExec.regs.insert PC tPC).get? PC = _
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- `PC` after the retirement, seen through the next step's counter increment, is `tPC`. -/
theorem afterIncRetiredPC (afterExec : State) (tPC ret : BitVec 64) :
    (tryStepControlFlowAfterIncrement
      (tryStepControlFlowAfterRetired afterExec tPC ret)).regs.get? PC = some tPC := by
  rw [afterIncGet _ PC (by decide)]; exact retiredGetPC afterExec tPC ret

/-- `StableAgree` lifts through the counter-increment and `nextPC` writes of the execute state. -/
theorem coreStableAgree {s : State} (s_k : State) (pc : BitVec 64) (hSt : StableAgree s s_k) :
    StableAgree s (coreControlFlowNextState (tryStepControlFlowAfterIncrement s_k) pc) :=
  fun r hr => coreGetStable s_k pc r hr hSt

/-- In-range offset addressing has no wraparound. -/
theorem dstAddr_toNat (base : BitVec 64) (j : Nat) (hfit : base.toNat + j < 2 ^ 64) :
    (base + BitVec.ofNat 64 j).toNat = base.toNat + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The single little-endian byte of a width-1 word is the byte itself. -/
theorem leBytes_one_mem (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 8)
    (h : mem.get? a = some v) :
    ∀ (i' : Nat) (hi : i' < (leBytes 1 v).length),
      mem.get? (a + i') = some (leBytes 1 v)[i'] := by
  intro i' hi
  rw [leBytes_length] at hi
  obtain rfl : i' = 0 := by omega
  have hval : (leBytes 1 v)[0]'(by rw [leBytes_length]; omega) = v := by
    have hv : v.extractLsb' 0 8 = v := by apply BitVec.eq_of_getLsbD_eq; intro k hk; simp
    simp [leBytes, hv]
  simpa [hval] using h

/-- The retirement postlude sets `minstret := ret + 1`. -/
theorem retiredMinstret (afterExec : State) (tPC ret : BitVec 64) :
    (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? minstret =
      some (Sail.BitVec.addInt ret 1) := by
  change ((tryStepControlFlowAfterTick afterExec tPC).regs.insert minstret
    (Sail.BitVec.addInt ret 1)).get? minstret = _
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- Read a register untouched by a taken-branch / jump retirement (needs only the four control
registers to differ; works for `x13/x14/x15` too). -/
theorem jumpRetiredGet (base : State) (pc tgt ret : BitVec 64) (r : Register)
    (hPC : r ≠ PC) (hmr : r ≠ minstret) (hnpc : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt) tgt ret).regs.get? r =
      base.regs.get? r := by
  rw [retiredFrameGet _ _ _ r hPC hmr, jumpFrameGet base pc tgt r hnpc hmi]

/-- Read a register other than the written `rd` untouched by a GP fall-through retirement. -/
theorem fallThroughRetiredGet (base : State) (pc ret : BitVec 64) (rd : Register)
    (v : RegisterType rd) (r : Register) (hPC : r ≠ PC) (hmr : r ≠ minstret) (hrd : r ≠ rd)
    (hnpc : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret).regs.get? r = base.regs.get? r := by
  rw [retiredFrameGet _ _ _ r hPC hmr]
  show ((coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert rd v).get? r
      = base.regs.get? r
  rw [gpFrameGet (tryStepControlFlowAfterIncrement base) pc rd v r hrd hnpc]
  exact afterIncGet base r hmi

/-- The written destination register of a GP fall-through retirement holds the written value. -/
theorem fallThroughRetiredRd (base : State) (pc ret : BitVec 64) (rd : Register)
    (v : RegisterType rd) (hPC : rd ≠ PC) (hmr : rd ≠ minstret) :
    (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret).regs.get? rd = some v := by
  rw [retiredFrameGet _ _ _ rd hPC hmr]
  show ((coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert rd v).get? rd
      = some v
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- The retirement postlude does not touch memory. -/
theorem retiredMem (afterExec : State) (tPC ret : BitVec 64) :
    (tryStepControlFlowAfterRetired afterExec tPC ret).mem = afterExec.mem := rfl

/-- A jump execute does not touch memory. -/
theorem jumpMem (base : State) (pc tgt : BitVec 64) :
    (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt).mem = base.mem := rfl

/-- A GP fall-through execute does not touch memory. -/
theorem fallThroughMem (base : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd) :
    ({ coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }).mem = base.mem := rfl

/-- Read a register untouched by a memory-writing (`sb`) fall-through retirement. -/
theorem sbRetiredGet (base s' : State) (pc ret : BitVec 64)
    (regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs)
    (r : Register) (hPC : r ≠ PC) (hmr : r ≠ minstret) (hnpc : r ≠ nextPC)
    (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) ret).regs.get? r = base.regs.get? r := by
  rw [retiredFrameGet _ _ _ r hPC hmr, regsEq,
    coreGetInc (tryStepControlFlowAfterIncrement base) pc r hnpc]
  exact afterIncGet base r hmi

/-- Reading a distinct address through a memory insert. -/
theorem getInsertNe (mem : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (v : BitVec 8) (h : k ≠ a) :
    (mem.insert k v).get? a = mem.get? a := by
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]; simp [h]

/-- Reading the just-inserted address. -/
theorem getInsertEq (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8) :
    (mem.insert k v).get? k = some v := by
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]; simp

/-- Inserting a byte the image does not back preserves `matchesMemory`. -/
theorem matchesMemory_insert (image : ProgramImage) (mem : Std.ExtHashMap Nat (BitVec 8))
    (k : Nat) (v : BitVec 8) (hm : image.matchesMemory mem) (hk : image.readByte? k = none) :
    image.matchesMemory (mem.insert k v) := by
  intro a byte ha
  have hak : k ≠ a := by rintro rfl; rw [hk] at ha; exact Option.noConfusion ha
  have hget : (mem.insert k v).get? a = mem.get? a := by
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp [hak]
  rw [hget]; exact hm a byte ha

/-- Assemble a `StepPlatform` bundle from the abstract platform field, the pre-step config, and a
concrete fetch fact, for a state `StableAgree`-equal to the invariant's base positioned at `pc`. -/
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

/-- The generated fixed-width byte store inserts exactly one byte and returns `true`. -/
theorem writeBytes_byte_run (s : State) (a : Nat) (value : BitVec (8 * 1)) :
    Runs (PreSail.writeBytes a value) s { s with mem := s.mem.insert a value } true := by
  rw [writeBytes_eq]
  have hv : value.extractLsb' 0 8 = value := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp
  have hlist : (List.ofFn (fun i : Fin 1 => (a + i.val, value.extractLsb' (8 * i.val) 8)))
      = [(a, value)] := by
    rw [List.ofFn_succ, List.ofFn_zero]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, hv]
  rw [hlist]
  simp only [List.forM]
  exact Runs.bind (writeByte_run s a value) rfl

end BinaryFv.Keccak
