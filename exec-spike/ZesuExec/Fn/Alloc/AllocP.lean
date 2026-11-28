import ZesuExec.Fn.Alloc.AllocCuts

/-! # `alloc`: the leaves from the head cell (`0x800426a0`) and the pop path (`0x800426a8`) -/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

theorem shl_toNat {c : Nat} {x : Word} (hx : x.toNat < 64) (h : c * 2 ^ x.toNat < 2 ^ 64) :
    (BinOp.eval .sll (BitVec.ofNat 64 c) x).toNat = c * 2 ^ x.toNat := by
  show (BitVec.ofNat 64 c <<< (x.toNat % 64)).toNat = _
  have hc : c < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right c (Nat.pow_pos (by decide))) h
  rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hx, Nat.shiftLeft_eq, toNat_ofNat_lt hc,
    Nat.mod_eq_of_lt h]

theorem shl8 {x : Word} (hx : x.toNat < 22) :
    BinOp.eval .sll (BitVec.ofNat 64 8) x = BitVec.ofNat 64 (classBytes x.toNat) := by
  have hb := classBytes_le_24 hx
  apply BitVec.eq_of_toNat_eq
  have e : 8 * 2 ^ x.toNat = classBytes x.toNat := by
    unfold classBytes; rw [Nat.pow_add, Nat.mul_comm]
  rw [shl_toNat (by omega) (by omega), toNat_ofNat_lt (by omega), e]

theorem keep_of' {g : Sig} {m m' : Machine} {env : Env} {S : SState} (hm : Match env S m')
    (hk : ∀ i ∈ keepRegs, S.reg i = .var i) (hv : ∀ i : Fin 32, env.vars i.val = m.reg i)
    (hK : Keep g m) : Keep g m' := keep_of hm hk hv hK

theorem cP_var (g : Sig) (m : Machine) (i : Fin 32) : (cP.env g m).vars i.val = m.reg i :=
  envOf_var shapeP g m i

/-- The fresh-block path: block size and alignment `classBytes k`. -/
theorem leafPB {l : Leaf} (hex : l.exit = .at 0x80042740) (hst : l.S.steps ≤ 9)
    (hob : l.obligs = []) (hmem : l.S.mem = []) (hreg : l.S.regions = SP.regions)
    (hkeep : ∀ i ∈ keepRegs, l.S.reg i = .var i)
    (h11 : l.S.reg 11 = .bin .sll (.lit 8) (.var 13)) (h12 : l.S.reg 12 = .lit 0xa0d3473c)
    (h13 : l.S.reg 13 = .bin .sll (.lit 8) (.var 13)) : LeafGoal allocPlan cP l := by
  intro g m hA _
  obtain ⟨hwf, hm, -, -⟩ := AllocF.cut_800426a0 g m hA
  have hm : Match (cP.env g m) cP.S m := hm
  obtain ⟨⟨hpre, -, hK⟩, hmm, -, hok, -⟩ := hA
  refine ⟨by rw [hob]; simp, by show l.S.steps - 0 ≤ 22; omega, fun m' hm' he hso => ?_⟩
  have hsame : m'.mem = m.mem := funext fun a =>
    written_only hm rfl hm' hreg hso a (by rw [hmem]; simp)
  have hK' := keep_of hm' hkeep (cP_var g m) hK
  rw [hex] at he ⊢
  have hpc : m'.pc.toNat = 0x80042740 := he
  have hk := hok.2.2
  have hb : m'.reg 11 = BitVec.ofNat 64 (classBytes (m.reg 13).toNat) := by
    rw [Match.reg_of hm' 11 _ h11]; exact shl8 hk
  refine ExitGoal.at_cut rfl ⟨cB, by simp [allocPlan], hpc, ⟨⟨hpre, hpc, hK'⟩, hsame.trans hmm,
    by rw [Match.reg_of hm' 12 _ h12]; rfl, _, hok, hb, ?_⟩, by show 13 ≤ 22 - (l.S.steps - 0); omega⟩
  rw [Match.reg_of hm' 13 _ h13]; exact shl8 hk

/-- `8 << k < 1 << log2_align` never holds: the class covers the alignment. -/
theorem leafPB_inf {l : Leaf}
    (hc : SBool.ltu (.bin .sll (.lit 8) (.var 13)) (.bin .sll (.lit 1) (.var 12)) ∈ l.conds) :
    LeafGoal allocPlan cP l := by
  intro g m hA hcs
  exfalso
  have h := hcs _ hc
  obtain ⟨⟨hpre, -, -⟩, -, h12, hok, -⟩ := hA
  have hk := hok.2.2
  have ha := hpre.2.2.2.1
  simp only [SBool.eval, Sym.eval, BitVec.ult, decide_eq_true_eq] at h
  rw [show (cP.env g m).vars 13 = m.reg 13 from rfl, show (cP.env g m).vars 12 = m.reg 12 from rfl,
    h12] at h
  have hb := classBytes_le_24 hk
  rw [shl_toNat (by omega) (by unfold classBytes at hb; rw [Nat.pow_add] at hb; omega),
    shl_toNat (by omega) (by
      have := Nat.pow_le_pow_right (n := 2) (by decide) ha; simp; omega)] at h
  have := Nat.pow_le_pow_right (n := 2) (by decide) hok.2.1
  unfold alOf at this
  rw [Nat.pow_add] at this
  simp only [Nat.one_mul] at h
  omega

/-- The list is not empty: the head becomes region 1. -/
theorem leafPP1 {l : Leaf} (hex : l.exit = .at 0x800426a8) (hst : l.S.steps ≤ 12)
    (hob : l.obligs = []) (hmem : l.S.mem = []) (hreg : l.S.regions = SP.regions)
    (hkeep : ∀ i ∈ 13 :: keepRegs, l.S.reg i = .var i)
    (h10 : l.S.reg 10 = .init 0 0 8) (h11 : l.S.reg 11 = .ptr 0 (-8))
    (hc : SBool.ne (.init 0 0 8) (.lit 0) ∈ l.conds) : LeafGoal allocPlan cP l := by
  intro g m hA hcs
  obtain ⟨hwf, hm, -, -⟩ := AllocF.cut_800426a0 g m hA
  have hwf : Env.WF (cP.env g m) cP.S := hwf
  have hm : Match (cP.env g m) cP.S m := hm
  obtain ⟨⟨hpre, -, hK⟩, hmm, -, hok, h11m⟩ := hA
  have hne := hcs _ hc
  refine ⟨by rw [hob]; simp, by show l.S.steps - 0 ≤ 22; omega, fun m' hm' he hso => ?_⟩
  have hsame : m'.mem = m.mem := funext fun a =>
    written_only hm rfl hm' hreg hso a (by rw [hmem]; simp)
  have hK' := keep_of hm' (fun i hi => hkeep i (List.mem_cons_of_mem _ hi)) (cP_var g m) hK
  rw [hex] at he ⊢
  have hpc : m'.pc.toNat = 0x800426a8 := he
  have hk := hok.2.2
  have hb := fl_cell h11m hk
  have r13 : m'.reg 13 = m.reg 13 := (reg_var hm' 13 (hkeep 13 (List.mem_cons_self ..))).trans (cP_var g m 13)
  have hrd := rd_cst hwf hm (r := 0) (off := 0) (R := wordR) rfl (by show 0 + 8 ≤ 8; decide)
  have hb0 : (cP.env g m).base 0 = m.reg 11 + 8 := rfl
  rw [hb0, hb, toNat_ofNat_lt (by anum), Nat.add_zero, rd_mem hmm] at hrd
  have r10 : m'.reg 10 = (Sym.init 0 0 8).eval (cP.env g m) := Match.reg_of hm' 10 _ h10
  refine ExitGoal.at_cut rfl ⟨cP1, by simp [allocPlan], hpc, ⟨⟨hpre, hpc, hK'⟩, hsame.trans hmm,
    by rw [r13]; exact hok, ?_, ?_, ?_⟩, by show 10 ≤ 22 - (l.S.steps - 0); omega⟩
  · rw [r13, Match.reg_of hm' 11 _ h11, ← h11m]
    show m.reg 11 + 8 + BitVec.ofInt 64 (-8) = m.reg 11
    simp; bv_omega
  · rw [r13, r10]; exact hrd
  · rw [r10]
    simp only [SBool.eval, bne_iff_ne, ne_eq] at hne
    exact hne

end ZesuExec.Fn.Alloc
