import ZesuExec.Fn.Memset.Table

/-! # `memset` against the CSR `0x816` definition: `memset_spec` -/

namespace ZesuExec.Fn.Memset
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-- `csr816` at a `csrs 0x816, a0; addi zero, a2, b` site with `b ≤ 0xff`. -/
theorem csr816_site {m : Machine} {b : Nat} {byte : Byte}
    (h0 : Svc.fetch zesuImage m.pc.toNat = some 0x81652073)
    (h1 : Svc.fetch zesuImage (m.pc.toNat + 4) = some (addiWord b))
    (ha : Svc.isAddiX0 (addiWord b) = true) (hr : Decode.reg (addiWord b) 15 = 12)
    (hb : Svc.byteImm? (addiWord b) = some byte) {e : SvcEffect}
    (he : memsetEffect m (m.reg 10).toNat (m.reg 12).toNat byte 8 = some e) :
    svc zesuImage m = some e := by
  have h813 : csr813 zesuImage m = none := by
    unfold csr813; rw [h0, h1]
    simp [show Svc.isCsrs 0x81652073 0x813 = false by decide]
  have h816 : csr816 zesuImage m = memsetEffect m (m.reg 10).toNat (m.reg 12).toNat byte 8 := by
    unfold csr816; rw [h0, h1]
    simp only [show Svc.isCsrs 0x81652073 0x816 = true by decide, ha, and_self, if_true, hb,
      show Decode.reg 0x81652073 15 = 10 by decide, hr]
  simp [svc, h813, h816, he]

/-- The service step of a site, as `next` takes it. -/
theorem memsetEffect_some {m : Machine} {d n : Nat} {byte : Byte}
    (hdom : n = 0 ∨ dstOk m.mem d n = true) :
    memsetEffect m d n byte 8 = some
      { addrs := (List.range n).map (d + ·), mem := fillMem m.mem d n byte,
        pc := m.pc + BitVec.ofNat 64 8, cost := 2 } := by
  unfold memsetEffect
  rw [if_pos (by rcases hdom with h | h <;> simp [h])]

theorem addZero (x : Word) : x + (0 : Word) = x := BitVec.add_zero x

theorem reg_setReg_ne {x : Machine} {i j : Fin 32} {v : Word} (h : i ≠ j) :
    (x.setReg j v).reg i = x.reg i := by
  unfold Machine.setReg; split
  · rfl
  · simp [Machine.reg, h]

theorem reg_setReg_eq {x : Machine} {i : Fin 32} {v : Word} (h : i.val ≠ 0) :
    (x.setReg i v).reg i = v := by
  unfold Machine.setReg; simp [Machine.reg, h]

theorem reg_setReg_zero (x : Machine) (i : Fin 32) (v : Word) : (x.setReg 0 v).reg i = x.reg i := by
  unfold Machine.setReg; simp

theorem ret_exec (m : Machine) (hal : (m.reg 1 &&& ~~~(1 : Word)).toNat % 4 = 0) :
    m.exec (.jalr 0 1 0) = some { m with pc := m.reg 1 &&& ~~~1 } := by
  simp only [Machine.exec, Machine.jumpTo, Machine.setReg, Machine.sx]
  simp only [show ((0 : Fin 32).val = 0) from rfl, if_true,
    show BitVec.signExtend 64 (0 : BitVec 12) = 0 by decide, addZero]
  rw [if_pos hal]

theorem clr_table : ∀ b : Fin 256,
    (BitVec.ofNat 64 (table + 16 * b.val) &&& ~~~(1 : Word)) =
      BitVec.ofNat 64 (table + 16 * b.val) := by decide +kernel

theorem lowByte (c : Word) : (c &&& BitVec.signExtend 64 (0xff : BitVec 12)) <<< (4 : BitVec 6).toNat =
    BitVec.ofNat 64 (16 * (c.toNat % 256)) := by
  have h1 : BitVec.signExtend 64 (0xff : BitVec 12) = (0xff : Word) := by decide
  apply BitVec.eq_of_toNat_eq
  rw [h1, BitVec.toNat_shiftLeft, BitVec.toNat_and,
    show (0xff : Word).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat]
  have := Nat.mod_lt c.toNat (show 0 < 2 ^ 8 by decide)
  rw [show (4 : BitVec 6).toNat = 4 from rfl]
  omega

theorem byteOf (c : Word) : BitVec.ofNat 8 (c.toNat % 256) = c.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

theorem memset_spec : Spec zesuImage entry bound Pre Post := by
  intro m hpc ⟨hal, hdom⟩
  have hmc : ∀ x : Machine, x.pc.toNat ≠ Layout.memcpyEntry → x.pc.toNat ≠ Layout.memcpyEntry :=
    fun _ h => h
  by_cases hc : m.reg 11 = 0
  · have hc' : m.regs 11 = 0 := by simpa [Machine.reg] using hc
    -- `c = 0`: `csrs 0x816, a0; addi zero, a2, 0; ret` at `0x800e06f4`
    let m1 : Machine := m.advance
    have hpc1 : m1.pc.toNat = 0x800e06f4 := by
      simp only [m1, Machine.advance, BitVec.toNat_add, hpc]; rfl
    have hn1 : next zesuImage m = some (m1, 1) :=
      next_exec (by rw [hpc]; decide) (by rw [hpc]; exact fetch_bne)
        (by simp [Machine.exec, Machine.branch, Machine.reg, hc', m1])
    have hs1 := csr816_site (m := m1) (b := 0) (by rw [hpc1]; exact svc_zero_w0)
      (by rw [hpc1]; exact svc_zero_w1) (by decide) (by decide) (by decide)
      (memsetEffect_some (byte := BitVec.ofNat 8 0) hdom)
    have hn2 := next_svc (by rw [hpc1]; decide) (by rw [hpc1]; exact fetch_zero_csr) hs1
    let m2 : Machine := SvcEffect.apply
      { addrs := (List.range (m1.reg 12).toNat).map ((m1.reg 10).toNat + ·),
        mem := fillMem m1.mem (m1.reg 10).toNat (m1.reg 12).toNat (BitVec.ofNat 8 0),
        pc := m1.pc + BitVec.ofNat 64 8, cost := 2 } m1
    have hpc2 : m2.pc.toNat = 0x800e06fc := by
      simp only [m2, SvcEffect.apply, BitVec.toNat_add, hpc1]; rfl
    have hal2 : (m2.reg 1 &&& ~~~(1 : Word)).toNat % 4 = 0 := by
      simpa [m2, m1, SvcEffect.apply, Machine.setReg, Machine.reg, Machine.advance] using hal
    have hn3 := next_exec (by rw [hpc2]; decide) (by rw [hpc2]; exact fetch_zero_ret)
      (ret_exec m2 hal2)
    refine ⟨4, _, by decide, RunsIn.step hn1 (RunsIn.step hn2 (RunsIn.step hn3 .refl)), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [m2, m1, SvcEffect.apply, Machine.setReg, Machine.advance, Machine.reg, hc']
    · simp [m2, m1, SvcEffect.apply, Machine.setReg, Machine.advance, Machine.reg]
    · intro i _ _
      simp [m2, m1, SvcEffect.apply, Machine.setReg, Machine.advance, Machine.reg]
  · -- `c ≠ 0`: into the table at `0x800e0720 + 16 (c & 0xff)`
    have hspc : ∀ (x : Machine) (i : Fin 32) (v : Word), (x.setReg i v).pc = x.pc := by
      intro x i v; unfold Machine.setReg; split <;> rfl
    have hsmem : ∀ (x : Machine) (i : Fin 32) (v : Word), (x.setReg i v).mem = x.mem := by
      intro x i v; unfold Machine.setReg; split <;> rfl
    obtain ⟨b, hbd⟩ : ∃ b, b = (m.reg 11).toNat % 256 := ⟨_, rfl⟩
    have hb : b < 256 := by rw [hbd]; exact Nat.mod_lt _ (by decide)
    obtain ⟨t0, t1, t2, t3, ta, tr, tbyte⟩ := table_words ⟨b, hb⟩
    simp only at t0 t1 t2 t3 ta tr tbyte
    obtain ⟨m1, hm1⟩ : ∃ x : Machine, x = { m with pc := m.pc + Machine.sx (16 : BitVec 13) } :=
      ⟨_, rfl⟩
    have hpc1 : m1.pc.toNat = 0x800e0700 := by
      rw [hm1]; simp only [BitVec.toNat_add, hpc]; rfl
    have hn1 : next zesuImage m = some (m1, 1) := by
      refine next_exec (by rw [hpc]; decide) (by rw [hpc]; exact fetch_bne) ?_
      simp only [Machine.exec, Machine.branch, Machine.jumpTo]
      rw [if_pos (by rw [show m.reg 0 = 0 from rfl]; simpa using hc),
        if_pos (by simp only [BitVec.toNat_add, hpc]; rfl)]
      rw [hm1]
    obtain ⟨m2, hm2⟩ : ∃ x : Machine,
        x = (m1.setReg 11 (m1.reg 11 &&& Machine.sx (0xff : BitVec 12))).advance := ⟨_, rfl⟩
    have hpc2 : m2.pc.toNat = 0x800e0704 := by
      rw [hm2]; simp only [Machine.advance, hspc, BitVec.toNat_add, hpc1]; rfl
    have hn2 : next zesuImage m1 = some (m2, 1) :=
      next_exec (by rw [hpc1]; decide) (by rw [hpc1]; exact fetch_andi) (by rw [hm2]; rfl)
    obtain ⟨m3, hm3⟩ : ∃ x : Machine,
        x = (m2.setReg 11 (m2.reg 11 <<< (4 : BitVec 6).toNat)).advance := ⟨_, rfl⟩
    have hpc3 : m3.pc.toNat = 0x800e0708 := by
      rw [hm3]; simp only [Machine.advance, hspc, BitVec.toNat_add, hpc2]; rfl
    have hn3 : next zesuImage m2 = some (m3, 1) :=
      next_exec (by rw [hpc2]; decide) (by rw [hpc2]; exact fetch_slli) (by rw [hm3]; rfl)
    obtain ⟨m4, hm4⟩ : ∃ x : Machine,
        x = (m3.setReg 5 (m3.pc + Machine.sx ((0 : BitVec 20) ++ (0 : BitVec 12)))).advance :=
      ⟨_, rfl⟩
    have hpc4 : m4.pc.toNat = 0x800e070c := by
      rw [hm4]; simp only [Machine.advance, hspc, BitVec.toNat_add, hpc3]; rfl
    have hn4 : next zesuImage m3 = some (m4, 1) :=
      next_exec (by rw [hpc3]; decide) (by rw [hpc3]; exact fetch_auipc) (by rw [hm4]; rfl)
    obtain ⟨m5, hm5⟩ : ∃ x : Machine,
        x = (m4.setReg 5 (m4.reg 5 + Machine.sx (0x18 : BitVec 12))).advance := ⟨_, rfl⟩
    have hpc5 : m5.pc.toNat = 0x800e0710 := by
      rw [hm5]; simp only [Machine.advance, hspc, BitVec.toNat_add, hpc4]; rfl
    have hn5 : next zesuImage m4 = some (m5, 1) :=
      next_exec (by rw [hpc4]; decide) (by rw [hpc4]; exact fetch_addi) (by rw [hm5]; rfl)
    obtain ⟨m6, hm6⟩ : ∃ x : Machine, x = (m5.setReg 5 (m5.reg 5 + m5.reg 11)).advance :=
      ⟨_, rfl⟩
    have hpc6 : m6.pc.toNat = 0x800e0714 := by
      rw [hm6]; simp only [Machine.advance, hspc, BitVec.toNat_add, hpc5]; rfl
    have hn6 : next zesuImage m5 = some (m6, 1) :=
      next_exec (by rw [hpc5]; decide) (by rw [hpc5]; exact fetch_add) (by rw [hm6]; rfl)
    -- registers along the way
    have rne : ∀ {x y : Machine} {j : Fin 32} {v : Word}, y = (x.setReg j v).advance →
        ∀ i, i ≠ j → y.reg i = x.reg i := by
      intro x y j v h i hi; rw [h]; exact reg_setReg_ne hi
    have req : ∀ {x y : Machine} {j : Fin 32} {v : Word}, y = (x.setReg j v).advance →
        j.val ≠ 0 → y.reg j = v := by
      intro x y j v h hj; rw [h]; exact reg_setReg_eq hj
    have hr5 : m6.reg 5 = BitVec.ofNat 64 (table + 16 * b) := by
      have h3 : m3.pc = BitVec.ofNat 64 0x800e0708 := by
        apply BitVec.eq_of_toNat_eq; rw [hpc3]; rfl
      rw [req hm6 (by decide), req hm5 (by decide), req hm4 (by decide), h3,
        rne hm5 11 (by decide), rne hm4 11 (by decide), req hm3 (by decide), req hm2 (by decide),
        hm1]
      show _ + (m.reg 11 &&& Machine.sx (0xff : BitVec 12)) <<< (4 : BitVec 6).toNat = _
      rw [lowByte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, table]
      have : (Machine.sx ((0 : BitVec 20) ++ (0 : BitVec 12))).toNat = 0 := by decide
      have : (Machine.sx (0x18 : BitVec 12)).toNat = 0x18 := by decide
      subst hbd
      omega
    have h6t : (m6.reg 5 + Machine.sx (0 : BitVec 12) &&& ~~~(1 : Word)) =
        BitVec.ofNat 64 (table + 16 * b) := by
      rw [hr5, show Machine.sx (0 : BitVec 12) = 0 by decide, addZero]
      exact clr_table ⟨b, hb⟩
    have htn : (BitVec.ofNat 64 (table + 16 * b)).toNat = table + 16 * b := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [table]; omega)]
    obtain ⟨m7, hm7⟩ : ∃ x : Machine,
        x = { m6.setReg 0 (m6.pc + 4) with pc := BitVec.ofNat 64 (table + 16 * b) } := ⟨_, rfl⟩
    have hpc7 : m7.pc.toNat = table + 16 * b := by rw [hm7]; exact htn
    have hn7 : next zesuImage m6 = some (m7, 1) := by
      refine next_exec (by rw [hpc6]; decide) (by rw [hpc6]; exact fetch_jr) ?_
      simp only [Machine.exec, Machine.jumpTo]
      rw [h6t, if_pos (by rw [htn]; simp only [table]; omega), hm7]
    have h7 : ∀ i : Fin 32, i ≠ 5 → i ≠ 11 → m7.reg i = m.reg i := by
      intro i h5 h11
      have e7 : m7.reg i = m6.reg i := by rw [hm7]; exact reg_setReg_zero m6 i _
      rw [e7, rne hm6 i h5, rne hm5 i h5, rne hm4 i h5, rne hm3 i h11, rne hm2 i h11, hm1]; rfl
    have madv : ∀ {x y : Machine} {j : Fin 32} {v : Word}, y = (x.setReg j v).advance →
        y.mem = x.mem := by
      intro x y j v h; rw [h]; exact hsmem x j v
    have hmem7 : m7.mem = m.mem := by
      rw [hm7]
      exact (hsmem m6 0 _).trans ((madv hm6).trans ((madv hm5).trans ((madv hm4).trans
        ((madv hm3).trans ((madv hm2).trans (by rw [hm1]))))))
    have hdom7 : (m7.reg 12).toNat = 0 ∨ dstOk m7.mem (m7.reg 10).toNat (m7.reg 12).toNat = true := by
      rw [h7 12 (by decide) (by decide), h7 10 (by decide) (by decide), hmem7]; exact hdom
    have hs7 := csr816_site (m := m7) (by rw [hpc7]; exact t1) (by rw [hpc7]; exact t2) ta tr tbyte
      (memsetEffect_some hdom7)
    have hn8 := next_svc (by rw [hpc7]; simp only [table, Layout.memcpyEntry]; omega)
      (by rw [hpc7]; exact t0) hs7
    obtain ⟨m8, hm8⟩ : ∃ x : Machine, x = SvcEffect.apply
      { addrs := (List.range (m7.reg 12).toNat).map ((m7.reg 10).toNat + ·),
        mem := fillMem m7.mem (m7.reg 10).toNat (m7.reg 12).toNat (BitVec.ofNat 8 b),
        pc := m7.pc + BitVec.ofNat 64 8, cost := 2 } m7 := ⟨_, rfl⟩
    rw [← hm8] at hn8
    have hpc8 : m8.pc.toNat = table + 16 * b + 8 := by
      rw [hm8]; simp only [SvcEffect.apply, BitVec.toNat_add, hpc7, BitVec.toNat_ofNat, table]
      omega
    have h8 : ∀ i : Fin 32, i ≠ 5 → i ≠ 11 → m8.reg i = m.reg i := by
      intro i h5 h11
      rw [hm8]; exact (reg_setReg_zero m7 i 0).trans (h7 i h5 h11)
    have hal8 : (m8.reg 1 &&& ~~~(1 : Word)).toNat % 4 = 0 := by
      rw [h8 1 (by decide) (by decide)]; exact hal
    have hn9 := next_exec (by rw [hpc8]; simp only [table, Layout.memcpyEntry]; omega)
      (by rw [hpc8]; exact t3) (ret_exec m8 hal8)
    refine ⟨10, _, by decide, RunsIn.step hn1 (RunsIn.step hn2 (RunsIn.step hn3 (RunsIn.step hn4
      (RunsIn.step hn5 (RunsIn.step hn6 (RunsIn.step hn7 (RunsIn.step hn8 (RunsIn.step hn9
      .refl)))))))), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · show m8.mem = _
      rw [hm8]
      show fillMem m7.mem (m7.reg 10).toNat (m7.reg 12).toNat (BitVec.ofNat 8 b) = _
      rw [hmem7, h7 12 (by decide) (by decide), h7 10 (by decide) (by decide), hbd, byteOf]
    · show m8.reg 1 &&& ~~~1 = _
      rw [h8 1 (by decide) (by decide)]
    · intro i h5 h11
      exact h8 i h5 h11

end ZesuExec.Fn.Memset
