import ZesuExec.Fn.Sha256.Svc

/-!
# `zkvm_sha256`: the prologue (`0x800ea180` → `0x800ea1ec`)

A symbolic run from the entry to the first bump-allocator store (the frame and the saved
registers), the two stores to the bump words and four register writes by hand, then the
CSR `0x813` copy of the initial hash value from rodata to `sp + 8`.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Fn

sym_run runPro := run zesuImage [0x800ea1c4] 40 entry SE

def envE (m : Machine) : Env := entryEnv m ((shapeE m).map (·.1))

@[simp] theorem envE_vars (m : Machine) (i : Nat) : (envE m).vars i = m.reg (Fin.ofNat 32 i) := rfl

/-- The initial hash value at `0x801153e0`, as the image holds it. -/
theorem h0_rodata : ∀ i < 32, zesuImage.rodataByte? (0x801153e0 + i) =
    some ((Sha256.leBytes Sha256.H0).getD i 0).toNat := by decide +kernel

theorem pro_saved : ∀ p ∈ savedRegs, ∀ t < 8,
    (runPro_leaves[0]!).S.mem.find? (·.covers 0 (p.2 + t)) = some ⟨0, p.2, 8, .var p.1.val⟩ := by
  decide

theorem pro_regs : ∀ i : Fin 32, i ≠ 2 → i ≠ 13 → i ≠ 14 →
    (runPro_leaves[0]!).S.reg i.val = if i.val = 0 then .lit 0 else .var i.val := by decide

theorem bumpBytes_get : ∀ i (h : i < bumpBytes.length), bumpBytes[i] =
    if i < 8 then byteOf (0xa05340c8 : Word) i else byteOf (0xa0d340c8 : Word) (i - 8) := by decide

theorem pro_low : ∀ j < 0x78, (runPro_leaves[0]!).S.mem.find? (·.covers 0 j) = none := by decide

theorem pro {m0 : Machine} (hpre : Pre m0) (hpc : m0.pc.toNat = entry) :
    ∃ m, RunsIn zesuImage 27 m0 m ∧ m.pc.toNat = 0x800ea1ec ∧ Mid m0 m ∧
      FrameAt m 8 (Sha256.leBytes Sha256.H0) ∧ m.reg 10 = m0.reg 10 ∧ m.reg 11 = m0.reg 11 := by
  have hpre' := hpre
  obtain ⟨hro, ⟨hal, hlo, hhi, hpres⟩, hra, hin, hout, hbump, hstage, hdis, hindis⟩ := hpre'
  obtain ⟨hspn, hspal, hsplo, hsphi⟩ := spM_facts hpre
  have hbase : (shapeE m0).map (·.1) = [(spM m0, 0xe0)] := rfl
  obtain ⟨l, hl, -, hr⟩ := seg_sound (ov := ovE) (shape := shapeE m0) runPro
    (by
      simp only [shapeE, List.mem_singleton, forall_eq, RegionOk, frameRg]
      refine ⟨by simp, hspal, ?_⟩
      simp only [if_true, writable, inRange, Bool.and_eq_true, decide_eq_true_eq]
      unfold frameSize at *; exact ⟨hsplo, hsphi⟩)
    (by simp [shapeE])
    (fun r j hr hj => by
      simp [shapeE] at hr; subst hr
      exact hpres j (by simpa [entryEnv, Env.size, shapeE, frameSize] using hj))
    (fun i hi s hs => by
      simp only [ovE] at hs
      split at hs
      · next h2 =>
        cases hs
        have : i = 2 := Fin.ext h2
        subst this
        simp only [Sym.eval, Env.base, entryEnv, shapeE, List.map, List.getD_cons_zero]
        exact BitVec.sub_add_cancel _ _
      · simp at hs)
    hpc hro
  replace hl : l = runPro_leaves[0]! := by simp only [runPro_leaves, List.mem_singleton] at hl; exact hl
  subst hl
  obtain ⟨m1, hrun1, hm1, hex1, hso1⟩ := hr (fun o ho => by simp [runPro_leaves] at ho)
  have hpc1 : m1.pc.toNat = 0x800ea1c4 := hex1
  have r2 : m1.reg 2 = spM m0 := by
    rw [reg_of_match hm1]
    show (m0.reg 2 - BitVec.ofNat 64 frameSize) + BitVec.ofInt 64 0 = _
    simp [spM]
  have r13 : m1.reg 13 = 0xa05341b8 := by rw [reg_of_match hm1]; rfl
  have r14 : m1.reg 14 = 0xa05340c8 := by rw [reg_of_match hm1]; rfl
  have rk : ∀ i : Fin 32, i ≠ 2 → i ≠ 13 → i ≠ 14 → m1.reg i = m0.reg i := by
    intro i h2 h13 h14
    exact reg_kept hm1 (pro_regs i h2 h13 h14)
  -- disjointness facts of `Pre`
  simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨-, hfb, hfs⟩, ⟨-, -⟩, hbs⟩ := hdis
  have hfr0 : frameR m0 = (spM m0, 0xe0) := rfl
  rw [hfr0] at hfb hfs
  simp only [Disjoint, bumpR, stageR, BitVec.toNat_ofNat, bump, Layout.extraParams] at hfb hfs hbs
  have hS : (spM m0).toNat % 16 = 0 ∧ 0xa0000000 ≤ (spM m0).toNat ∧
      (spM m0).toNat + 0xe0 ≤ 0xc0000000 := by
    unfold frameSize Layout.ramLo Layout.ramHi at *; omega
  clear hspal hsplo hsphi
  -- memory after the symbolic piece
  have hso1' : SameOutside (InRange (spM m0) 0xe0) m0 m1 := SameOutside.mono hso1 fun a ha => by
    obtain ⟨p, hp, -, hin⟩ := inWritable_entry ha (by
      simp only [shapeE, List.mem_singleton, forall_eq]
      show (spM m0).toNat + 0xe0 < 2 ^ 64
      omega)
    simp [shapeE] at hp; subst hp
    exact hin
  have hfr1 : ∀ j < 0xe0, (m1.mem (spM m0 + BitVec.ofNat 64 j)).isSome := fun j hj => by
    have := hm1.mem 0 j (by decide) (by simpa [Env.size, entryEnv, shapeE] using hj)
    rw [show (entryEnv m0 ((shapeE m0).map (·.1))).base 0 = spM m0 from rfl] at this
    simp [this]
  have hbumpP : present m0.mem 0xa05340b8 16 = true := by
    simp only [dstOk, Bool.and_eq_true] at hbump; exact hbump.2
  have hnf : ∀ t < 16, ¬ InRange (spM m0) 0xe0 (BitVec.ofNat 64 (0xa05340b8 + t)) :=
    fun t ht => notIn_of_disjoint hfb ht (by omega)
  -- `0x800ea1c4: sd a4, -0x100(a3)`
  have ha2 : (m1.reg 13 + Machine.sx (0xf00 : BitVec 12)).toNat = 0xa05340b8 := by rw [r13]; decide
  obtain ⟨m2, hm2⟩ : ∃ x : Machine,
      x = { m1 with mem := writeBytes m1.mem 0xa05340b8 (m1.reg 14) 8, pc := m1.pc + 4 } := ⟨_, rfl⟩
  have hn1 : next zesuImage m1 = some (m2, 1) := by
    refine next_exec (i := .sd 13 14 0xf00) (by rw [hpc1]; decide) (by rw [hpc1]; decide +kernel) ?_
    show m1.storeFrom 13 14 0xf00 8 = _
    rw [exec_store (by rw [ha2]; decide) (by
      rw [ha2]
      have := present_keep hso1' (a := 0xa05340b8) (n := 8) (fun t ht => hnf t (by omega))
        (by simp only [present]; exact readBytes_isSome_of fun t ht =>
          present_at hbumpP t (by omega))
      exact this), ha2, hm2]
  have hpc2 : m2.pc.toNat = 0x800ea1c8 := by rw [hm2]; simp only [BitVec.toNat_add, hpc1]; rfl
  -- `lui a3, 0x800; add a3, a4, a3; auipc a4, 0x2044a`
  obtain ⟨m3, hm3⟩ : ∃ x : Machine,
      x = (m2.setReg 13 (Machine.sx ((0x00800 : BitVec 20) ++ (0 : BitVec 12)))).advance := ⟨_, rfl⟩
  have hn2 : next zesuImage m2 = some (m3, 1) :=
    next_exec (i := .lui 13 0x00800) (by rw [hpc2]; decide) (by rw [hpc2]; decide +kernel)
      (by rw [hm3]; rfl)
  have hpc3 : m3.pc.toNat = 0x800ea1cc := by
    rw [hm3]; simp only [advance_pc, setReg_pc, BitVec.toNat_add, hpc2]; rfl
  obtain ⟨m4, hm4⟩ : ∃ x : Machine, x = (m3.setReg 13 (m3.reg 14 + m3.reg 13)).advance := ⟨_, rfl⟩
  have hn3 : next zesuImage m3 = some (m4, 1) :=
    next_exec (i := .add 13 14 13) (by rw [hpc3]; decide) (by rw [hpc3]; decide +kernel)
      (by rw [hm4]; rfl)
  have hpc4 : m4.pc.toNat = 0x800ea1d0 := by
    rw [hm4]; simp only [advance_pc, setReg_pc, BitVec.toNat_add, hpc3]; rfl
  obtain ⟨m5, hm5⟩ : ∃ x : Machine,
      x = (m4.setReg 14 (m4.pc + Machine.sx ((0x2044a : BitVec 20) ++ (0 : BitVec 12)))).advance :=
    ⟨_, rfl⟩
  have hn4 : next zesuImage m4 = some (m5, 1) :=
    next_exec (i := .auipc 14 0x2044a) (by rw [hpc4]; decide) (by rw [hpc4]; decide +kernel)
      (by rw [hm5]; rfl)
  have hpc5 : m5.pc.toNat = 0x800ea1d4 := by
    rw [hm5]; simp only [advance_pc, setReg_pc, BitVec.toNat_add, hpc4]; rfl
  have r5_13 : m5.reg 13 = 0xa0d340c8 := by
    rw [hm5, hm4, hm3]
    simp only [advance_reg, setReg_reg, hm2]
    simp [r14]
    decide
  have r5_14 : m5.reg 14 = 0xa05341d0 := by
    have h4 : m4.pc = 0x800ea1d0 := BitVec.eq_of_toNat_eq (by rw [hpc4]; rfl)
    rw [hm5]; simp only [advance_reg, setReg_reg, h4]; rw [if_pos (by decide)]; decide
  have hm5mem : m5.mem = writeBytes m1.mem 0xa05340b8 (m1.reg 14) 8 := by
    rw [hm5, hm4, hm3, hm2]; rfl
  -- `0x800ea1d4: sd a3, -0x110(a4)`
  have ha6 : (m5.reg 14 + Machine.sx (0xef0 : BitVec 12)).toNat = 0xa05340c0 := by rw [r5_14]; decide
  obtain ⟨m6, hm6⟩ : ∃ x : Machine,
      x = { m5 with mem := writeBytes m5.mem 0xa05340c0 (m5.reg 13) 8, pc := m5.pc + 4 } := ⟨_, rfl⟩
  have hn5 : next zesuImage m5 = some (m6, 1) := by
    refine next_exec (i := .sd 14 13 0xef0) (by rw [hpc5]; decide) (by rw [hpc5]; decide +kernel) ?_
    show m5.storeFrom 14 13 0xef0 8 = _
    rw [exec_store (by rw [ha6]; decide) (by
      rw [ha6, hm5mem]
      apply readBytes_isSome_of
      intro t ht
      rw [writeBytes_out (by omega) (by simp; omega),
        show 0xa05340c0 + t = 0xa05340b8 + (8 + t) by omega, hso1' _ (hnf (8 + t) (by omega))]
      exact present_at hbumpP (8 + t) (by omega)), ha6, hm6]
  have hpc6 : m6.pc.toNat = 0x800ea1d8 := by rw [hm6]; simp only [BitVec.toNat_add, hpc5]; rfl
  -- `auipc a3, 0x2b; addi a3, a3, 0x208; addi a4, sp, 8`
  obtain ⟨m7, hm7⟩ : ∃ x : Machine,
      x = (m6.setReg 13 (m6.pc + Machine.sx ((0x0002b : BitVec 20) ++ (0 : BitVec 12)))).advance :=
    ⟨_, rfl⟩
  have hn6 : next zesuImage m6 = some (m7, 1) :=
    next_exec (i := .auipc 13 0x0002b) (by rw [hpc6]; decide) (by rw [hpc6]; decide +kernel)
      (by rw [hm7]; rfl)
  have hpc7 : m7.pc.toNat = 0x800ea1dc := by
    rw [hm7]; simp only [advance_pc, setReg_pc, BitVec.toNat_add, hpc6]; rfl
  obtain ⟨m8, hm8⟩ : ∃ x : Machine, x = (m7.setReg 13 (m7.reg 13 + Machine.sx (0x208 : BitVec 12))).advance :=
    ⟨_, rfl⟩
  have hn7 : next zesuImage m7 = some (m8, 1) :=
    next_exec (i := .addi 13 13 0x208) (by rw [hpc7]; decide) (by rw [hpc7]; decide +kernel)
      (by rw [hm8]; rfl)
  have hpc8 : m8.pc.toNat = 0x800ea1e0 := by
    rw [hm8]; simp only [advance_pc, setReg_pc, BitVec.toNat_add, hpc7]; rfl
  obtain ⟨m9, hm9⟩ : ∃ x : Machine, x = (m8.setReg 14 (m8.reg 2 + Machine.sx (0x008 : BitVec 12))).advance :=
    ⟨_, rfl⟩
  have hn8 : next zesuImage m8 = some (m9, 1) :=
    next_exec (i := .addi 14 2 0x008) (by rw [hpc8]; decide) (by rw [hpc8]; decide +kernel)
      (by rw [hm9]; rfl)
  have hpc9 : m9.pc.toNat = 0x800ea1e4 := by
    rw [hm9]; simp only [advance_pc, setReg_pc, BitVec.toNat_add, hpc8]; rfl
  have hm9mem : m9.mem = writeBytes (writeBytes m1.mem 0xa05340b8 (m1.reg 14) 8) 0xa05340c0
      (m5.reg 13) 8 := by
    rw [hm9, hm8, hm7, hm6]; simp only [advance_mem, setReg_mem]; rw [hm5mem]
  have r82 : m8.reg 2 = m1.reg 2 := by
    rw [hm8, reg_adv_ne (by decide), hm7, reg_adv_ne (by decide), hm6, mk_reg, hm5,
      reg_adv_ne (by decide), hm4, reg_adv_ne (by decide), hm3, reg_adv_ne (by decide), hm2, mk_reg]
  have hR9 : ∀ i : Fin 32, i ≠ 13 → i ≠ 14 → m9.reg i = m1.reg i := by
    intro i h13 h14
    rw [hm9, reg_adv_ne h14, hm8, reg_adv_ne h13, hm7, reg_adv_ne h13, hm6, mk_reg, hm5,
      reg_adv_ne h14, hm4, reg_adv_ne h13, hm3, reg_adv_ne h13, hm2, mk_reg]
  have r9_13 : m9.reg 13 = 0x801153e0 := by
    have h6 : m6.pc = 0x800ea1d8 := BitVec.eq_of_toNat_eq (by rw [hpc6]; rfl)
    rw [hm9, reg_adv_ne (by decide), hm8, reg_adv_eq (by decide), hm7, reg_adv_eq (by decide), h6]
    decide
  have r9_14 : m9.reg 14 = spM m0 + 8 := by
    rw [hm9, reg_adv_eq (by decide), r82, r2]; rfl
  -- memory of `m9`: the two bump words written over `m1`
  have hm9out : ∀ x : Word, ¬ (0xa05340b8 ≤ x.toNat ∧ x.toNat < 0xa05340c8) → m9.mem x = m1.mem x := by
    intro x hx
    rw [hm9mem, writeBytes_out (by omega) (by omega), writeBytes_out (by omega) (by omega)]
  have hro_m1 : ∀ t < 32, m1.mem (BitVec.ofNat 64 (0x801153e0 + t)) =
      some (BitVec.ofNat 8 ((Sha256.leBytes Sha256.H0).getD t 0).toNat) := by
    intro t ht
    rw [hso1' _ (by
      unfold InRange; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)]
    exact hro _ _ (h0_rodata t ht)
  -- `0x800ea1e4: csrs 0x813, a3; addi zero, a4, 0x20`: copy the initial hash value
  have hn9 := next_813i (m := m9) (w0 := 2167840883) (w1 := 34013203) (s := 0x801153e0)
    (d := (spM m0 + 8).toNat) (n := 32)
    (by rw [hpc9]; decide) (by rw [hpc9]; decide +kernel) (by rw [hpc9]; decide +kernel)
    (by rw [hpc9]; decide +kernel) (by decide) (by decide) (by decide)
    (by rw [show Decode.reg 2167840883 15 = 13 by decide, r9_13]; rfl)
    (by rw [show Decode.reg 34013203 15 = 14 by decide, r9_14]) (by decide)
    (by
      simp only [srcOk, Bool.and_eq_true]
      refine ⟨by decide, ?_⟩
      apply readBytes_isSome_of
      intro t ht
      rw [hm9out _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega), hro_m1 t ht]
      rfl)
    (by
      have h8 : (spM m0 + 8).toNat = (spM m0).toNat + 8 := by
        rw [BitVec.toNat_add]; simp; omega
      simp only [dstOk, Bool.and_eq_true, h8]
      refine ⟨by simp [writable, inRange, Layout.ramLo, Layout.ramHi]; omega, ?_⟩
      apply readBytes_isSome_of
      intro t ht
      have hx : BitVec.ofNat 64 ((spM m0).toNat + 8 + t) = spM m0 + BitVec.ofNat 64 (8 + t) := by
        rw [← ofNat_toNat_add, Nat.add_assoc]
      rw [hm9out _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega), hx]
      exact hfr1 (8 + t) (by omega))
  obtain ⟨m10, hm10⟩ : ∃ x : Machine, x = { m9 with
      mem := copyMem m9.mem (spM m0 + 8).toNat 0x801153e0 32, pc := m9.pc + 8 } := ⟨_, rfl⟩
  rw [← hm10] at hn9
  have h8 : (spM m0 + 8).toNat = (spM m0).toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have hcopy : ∀ x : Word, m10.mem x = if (spM m0).toNat + 8 ≤ x.toNat ∧ x.toNat < (spM m0).toNat + 40
      then m9.mem (BitVec.ofNat 64 (0x801153e0 + x.toNat - ((spM m0).toNat + 8))) else m9.mem x := by
    intro x
    rw [hm10]
    show copyMem m9.mem (spM m0 + 8).toNat 0x801153e0 32 x = _
    simp only [copyMem, h8]
    split
    · next h => rw [if_pos (by omega)]
    · next h => rw [if_neg (by omega)]
  have hR10 : ∀ i, m10.reg i = m9.reg i := fun i => by rw [hm10]; rfl
  have hfa : ∀ j < 0xe0, (spM m0 + BitVec.ofNat 64 j).toNat = (spM m0).toNat + j := fun j hj => by
    rw [BitVec.toNat_add]; simp; omega
  -- frame bytes of `m10` outside the copy are `m1`'s
  have hkeep : ∀ j < 0xe0, (j < 8 ∨ 40 ≤ j) →
      m10.mem (spM m0 + BitVec.ofNat 64 j) = m1.mem (spM m0 + BitVec.ofNat 64 j) := by
    intro j hj hj'
    rw [hcopy, if_neg (by rw [hfa j hj]; omega), hm9out _ (by rw [hfa j hj]; omega)]
  have r10_2 : m10.reg 2 = spM m0 := by rw [hR10, hR9 _ (by decide) (by decide), r2]
  refine ⟨m10, ?_, ?_, ⟨r10_2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact hrun1.trans (RunsIn.step hn1 (RunsIn.step hn2 (RunsIn.step hn3 (RunsIn.step hn4
      (RunsIn.step hn5 (RunsIn.step hn6 (RunsIn.step hn7 (RunsIn.step hn8 (RunsIn.step hn9
      .refl)))))))))
  · rw [hm10]; simp only [BitVec.toNat_add, hpc9]; rfl
  · rw [hR10, hR9 _ (by decide) (by decide)]; exact rk _ (by decide) (by decide) (by decide)
  · intro p hp
    have := savedRegs_ne p hp
    rw [hR10, hR9 _ this.2.2.2.2.2.2.2.2.1 this.2.2.2.2.2.2.2.2.2.1]
    exact rk _ this.2.1 this.2.2.2.2.2.2.2.2.1 this.2.2.2.2.2.2.2.2.2.1
  · intro x hx
    simp only [WrittenMid, InRange, frameSize, not_or, not_and, Nat.not_lt] at hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    have hb : bumpW.toNat = 0xa05340b8 := rfl
    rw [hb] at hx2
    rw [hcopy, if_neg (by omega), hm9out _ (by omega), hso1' _ (by unfold InRange; omega)]
  · intro j hj
    rw [r10_2]
    unfold frameSize at hj
    by_cases hc : 8 ≤ j ∧ j < 40
    · rw [hcopy, if_pos (by rw [hfa j hj]; omega)]
      rw [hfa j hj, show 0x801153e0 + ((spM m0).toNat + j) - ((spM m0).toNat + 8) =
        0x801153e0 + (j - 8) by omega]
      rw [hm9out _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
        hro_m1 (j - 8) (by omega)]
      rfl
    · rw [hkeep j hj (by omega)]; exact hfr1 j hj
  · intro p hp i hi
    have hi8 : i < 8 := by simpa [le8] using hi
    have hoff := savedRegs_off p hp
    rw [r10_2, hkeep _ (by omega) (by omega)]
    have := mem_of_find hm1 (r := 0) (j := p.2 + i) (by decide) (by show _ < 0xe0; omega)
      (pro_saved p hp i hi8)
    rw [show (entryEnv m0 ((shapeE m0).map (·.1))).base 0 = spM m0 from rfl] at this
    rw [this, le8_get]
    simp [Sym.eval, entryEnv]
  · intro i hi
    have hil : i < 16 := by simpa [bumpBytes] using hi
    have hx : (bumpW + BitVec.ofNat 64 i).toNat = 0xa05340b8 + i := by
      rw [BitVec.toNat_add]; simp [bumpW, bump]; omega
    rw [hcopy, if_neg (by rw [hx]; omega), hm9mem, writeBytes_apply (by omega), hx,
      writeBytes_apply (by omega), hx, r14, r5_13, bumpBytes_get i hi]
    by_cases h8 : i < 8
    · have e1 : ¬ (0xa05340c0 ≤ 0xa05340b8 + i ∧ 0xa05340b8 + i < 0xa05340c0 + 8) := by omega
      have e2 : 0xa05340b8 ≤ 0xa05340b8 + i ∧ 0xa05340b8 + i < 0xa05340b8 + 8 := by omega
      simp only [e1, e2, if_true, if_false, h8, Nat.add_sub_cancel_left, and_self]
    · have e1 : 0xa05340c0 ≤ 0xa05340b8 + i ∧ 0xa05340b8 + i < 0xa05340c0 + 8 := by omega
      have e3 : 0xa05340b8 + i - 0xa05340c0 = i - 8 := by omega
      simp only [e1, h8, if_false, e3, and_self, if_true]
  · intro j hj
    have hx : (stageW + BitVec.ofNat 64 j).toNat = 0xa0000f00 + j := by
      rw [BitVec.toNat_add]; simp [stageW, Layout.extraParams]; omega
    rw [hcopy, if_neg (by rw [hx]; omega), hm9out _ (by rw [hx]; omega),
      hso1' _ (by unfold InRange; rw [hx]; omega)]
    have := present_at (by simp only [dstOk, Bool.and_eq_true] at hstage; exact hstage.2) j hj
    rw [show BitVec.ofNat 64 (Layout.extraParams + j) = stageW + BitVec.ofNat 64 j by
      rw [← ofNat_toNat_add]; rfl] at this
    exact this
  · intro i hi
    have hi32 : i < 32 := by simpa using hi
    rw [r10_2, hcopy, if_pos (by rw [hfa _ (by omega)]; omega), hfa _ (by omega),
      show 0x801153e0 + ((spM m0).toNat + (8 + i)) - ((spM m0).toNat + 8) = 0x801153e0 + i by omega,
      hm9out _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega), hro_m1 i hi32]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · rw [hR10, hR9 _ (by decide) (by decide)]; exact rk _ (by decide) (by decide) (by decide)
  · rw [hR10, hR9 _ (by decide) (by decide)]; exact rk _ (by decide) (by decide) (by decide)

end ZesuExec.Fn.Sha256
