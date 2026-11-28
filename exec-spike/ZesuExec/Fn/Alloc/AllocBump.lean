import ZesuExec.Fn.Alloc.AllocPost

/-!
# `alloc`: the bump paths (`sysAllocAligned`)

Rounding `HEAP_POS` up (`0x80042740` → `0x80042760`, `0x800426e0` → `0x80042708`) and the
final test against `HEAP_TOP` (to the returns).
-/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

theorem pos_val {g : Sig} (hpre : AllocPre g.L g.m) :
    ∃ st, Decode g.m st ∧ Good g.L st ∧ rd g.m posAddr = some (BitVec.ofNat 64 st.pos) ∧
      posOf g = st.pos := by
  obtain ⟨st, hd, hg⟩ := hpre.1
  refine ⟨st, hd, hg, hd.pos, ?_⟩
  unfold posOf; rw [hd.pos]; simp only [Option.getD_some]
  have := hg.pos_hi; exact toNat_ofNat_lt (by unfold Layout.ramHi at this; omega)

theorem vars_base (g : Sig) (m : Machine) :
    (envOf (fun _ => shapeV) g m).base 0 = BitVec.ofNat 64 posAddr := rfl

theorem vars_ptr (g : Sig) (m : Machine) (o : Nat) :
    (Sym.ptr 0 (Int.ofNat o)).eval (envOf (fun _ => shapeV) g m) =
      BitVec.ofNat 64 posAddr + BitVec.ofNat 64 o := by
  show BitVec.ofNat 64 posAddr + BitVec.ofInt 64 (Int.ofNat o) = _; simp

/-- The pointer at `0x8004273c`/`0x800426dc`'s `auipc` targets, region 0 being `[HEAP_POS, +16)`. -/
theorem vars_lit {g : Sig} {m : Machine} {o v : Nat} (h : posAddr + o = v) :
    (Sym.ptr 0 (Int.ofNat o)).eval (envOf (fun _ => shapeV) g m) = BitVec.ofNat 64 v := by
  rw [vars_ptr, ← ofNat_add_nat, h]

/-- The word at `HEAP_POS + off` of a machine matched by a vars-region state. -/
theorem rd_vars {env : Env} {S : SState} {m : Machine} (hwf : Env.WF env S) (hm : Match env S m)
    (hR : S.regions[0]? = some varsR) (hb : env.base 0 = BitVec.ofNat 64 posAddr) {off : Nat}
    (ho : off ≤ 8) : rd m (posAddr + off) = some ((readConst S 0 off 8).eval env) := by
  have hs : env.size 0 = 16 := hwf.size 0 varsR 16 hR rfl
  have := rd_cst hwf hm hR (off := off) (by omega)
  rwa [hb, toNat_ofNat_lt (by anum)] at this

/-- Memory after a leaf that wrote at most `HEAP_POS`. -/
theorem only_pos {env : Env} {S S' : SState} {m m' : Machine} (hm : Match env S m) (hS : S.mem = [])
    (hm' : Match env S' m') (hr : S'.regions = S.regions)
    (hso : SameOutside (InWritable env S) m m') (hb : env.base 0 = BitVec.ofNat 64 posAddr)
    (hw : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off = 0 ∧ w.n = 8) :
    SameOutside (InRange (BitVec.ofNat 64 posAddr) 8) m m' := by
  intro a ha
  refine written_only hm hS hm' hr hso a fun ⟨w, hwm, j, h1, h2, he⟩ => ha ?_
  obtain ⟨hr0, ho, hn⟩ := hw w hwm
  rw [he, hr0, hb, ← ofNat_add_nat, inRange_ofNat (by anum) (by anum)]
  omega

theorem rounded_trans {g : Sig} {m m' : Machine} {p1 : Nat} (hR : Rounded g m p1)
    (h10 : m'.reg 10 = m.reg 10) (hso : SameOutside (InRange (BitVec.ofNat 64 posAddr) 8) m m')
    (hpos : rd m' posAddr = rd m posAddr) : Rounded g m' p1 := by
  obtain ⟨r10, h1, h2, hrd, hs⟩ := hR
  exact ⟨h10.trans r10, h1, h2, hpos.trans hrd, fun a ha => (hso a ha).trans (hs a ha)⟩

/-- A rounding leaf: `HEAP_POS` is already a multiple of the alignment (`a0 = HEAP_POS`, nothing
written), or it is rounded up and stored. -/
theorem rounded_of {g : Sig} {m m' : Machine} {env : Env} {S S' : SState} (hpre : AllocPre g.L g.m)
    (hmm : m.mem = g.m.mem) (hwf : Env.WF env S) (hm : Match env S m) (hS : S.mem = [])
    (hm' : Match env S' m') (hr : S'.regions = S.regions) (hso : SameOutside (InWritable env S) m m')
    (hR : S.regions[0]? = some varsR) (hb : env.base 0 = BitVec.ofNat 64 posAddr)
    (hrc0 : readConst S 0 0 8 = .init 0 0 8) {alS : Sym} {j : Nat} (hj : j ≤ 24)
    (hal : (alS.eval env).toNat = 2 ^ j)
    (hcase : (S'.mem = [] ∧ S'.reg 10 = .init 0 0 8 ∧
        (Sym.bin .and (.init 0 0 8) (.bin .add alS (.lit 18446744073709551615))).eval env = 0) ∨
      (let v := Sym.bin .sub (.bin .add (.init 0 0 8) alS)
          (.bin .and (.init 0 0 8) (.bin .add alS (.lit 18446744073709551615)))
       S'.mem = [⟨0, 0, 8, v⟩] ∧ S'.reg 10 = v ∧ readConst S' 0 0 8 = v ∧
        (Sym.bin .and (.init 0 0 8) (.bin .add alS (.lit 18446744073709551615))).eval env ≠ 0)) :
    ∃ p1, Rounded g m' p1 := by
  obtain ⟨st, hd, hg, hpos, hposOf⟩ := pos_val hpre
  have hx := rd_vars hwf hm hR hb (off := 0) (Nat.zero_le _)
  rw [Nat.add_zero, hrc0, rd_mem hmm, hpos] at hx
  have hx' : (Sym.init 0 0 8).eval env = BitVec.ofNat 64 st.pos := (Option.some.inj hx).symm
  have hplt : st.pos < 2 ^ 64 := by have := hg.pos_hi; unfold Layout.ramHi at this; omega
  rcases hcase with ⟨hmem, h10, -⟩ | ⟨hmem, h10, hrc, hne⟩
  · have hsame : m'.mem = m.mem := funext fun a =>
      written_only hm hS hm' hr hso a (by rw [hmem]; simp)
    refine ⟨st.pos, ?_, by omega, hg.pos_hi, ?_, ?_⟩
    · rw [Match.reg_of hm' 10 _ h10, hx']
    · rw [rd_mem hsame, rd_mem hmm, hpos]
    · intro a _; rw [hsame, hmm]
  · have hvr := rd_vars (wf_regions hwf hr) hm' (by rw [hr]; exact hR) hb (off := 0)
      (Nat.zero_le _)
    rw [Nat.add_zero, hrc] at hvr
    simp only [Sym.eval_bin, Sym.eval_lit, hx'] at hvr hne
    have hxle : (BitVec.ofNat 64 st.pos).toNat ≤ Layout.ramHi := by
      rw [toNat_ofNat_lt hplt]; exact hg.pos_hi
    obtain ⟨h1, h2⟩ := round_up hj hal hxle hne
    rw [toNat_ofNat_lt hplt] at h1
    refine ⟨_, ?_, by omega, h2, ?_, fun a ha => ?_⟩
    · rw [Match.reg_of hm' 10 _ h10, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      simp only [Sym.eval_bin, Sym.eval_lit, hx']; rfl
    · rw [hvr, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
    · rw [only_pos hm hS hm' hr hso hb (by rw [hmem]; simp) a ha, hmm]

theorem leafRoundB {l : Leaf} (hex : l.exit = .at 0x80042760) (hst : l.S.steps ≤ 8)
    (hob : l.obligs = []) (hreg : l.S.regions = SB.regions)
    (hkeep : ∀ i ∈ 11 :: keepRegs, l.S.reg i = .var i)
    (h12 : l.S.reg 12 = .ptr 0 540) (h13 : l.S.reg 13 = .lit 0xa0d3475c)
    (hcase : ∀ env : Env, (∀ b ∈ l.conds, b.eval env = true) →
      (l.S.mem = [] ∧ l.S.reg 10 = .init 0 0 8 ∧
        (Sym.bin .and (.init 0 0 8) (.bin .add (.var 13) (.lit 18446744073709551615))).eval env = 0) ∨
      (let v := Sym.bin .sub (.bin .add (.init 0 0 8) (.var 13))
          (.bin .and (.init 0 0 8) (.bin .add (.var 13) (.lit 18446744073709551615)))
       l.S.mem = [⟨0, 0, 8, v⟩] ∧ l.S.reg 10 = v ∧ readConst l.S 0 0 8 = v ∧
        (Sym.bin .and (.init 0 0 8) (.bin .add (.var 13) (.lit 18446744073709551615))).eval env ≠ 0)) :
    LeafGoal allocPlan cB l := by
  intro g m hA hc
  obtain ⟨hwf, hm, -, -⟩ := AllocF.cut_80042740 g m hA
  have hwf : Env.WF (cB.env g m) cB.S := hwf
  have hm : Match (cB.env g m) cB.S m := hm
  obtain ⟨⟨hpre, -, hK⟩, hmm, -, k, hok, h11, h13m⟩ := hA
  refine ⟨by rw [hob]; simp, by show l.S.steps - 0 ≤ 13; omega, fun m' hm' he hso => ?_⟩
  have hk := hok.2.2
  have hal : ((Sym.var 13).eval (cB.env g m)).toNat = 2 ^ (k + 3) := by
    show (m.reg 13).toNat = _
    rw [h13m, toNat_ofNat_lt (by have := classBytes_le_24 hk; omega)]; rfl
  obtain ⟨p1, hR⟩ := rounded_of hpre hmm hwf hm rfl hm' hreg hso rfl rfl rfl (by omega) hal
    (hcase _ hc)
  have hK' := keep_of hm' (fun i hi => hkeep i (List.mem_cons_of_mem _ hi))
    (envOf_var (fun _ => shapeV) g m) hK
  rw [hex] at he ⊢
  have hpc : m'.pc.toNat = 0x80042760 := he
  refine ExitGoal.at_cut rfl ⟨cT, by simp [allocPlan], hpc, ⟨⟨hpre, hpc, hK'⟩, ?_, ?_, k, p1, hok,
    ?_, hR⟩, by show 5 ≤ 13 - (l.S.steps - 0); omega⟩
  · rw [Match.reg_of hm' 12 _ h12]; exact vars_lit (g := g) (m := m) (o := 540) rfl
  · rw [Match.reg_of hm' 13 _ h13]; rfl
  · exact (reg_var hm' 11 (hkeep 11 (List.mem_cons_self ..))).trans
      ((envOf_var (fun _ => shapeV) g m 11).trans h11)

theorem leafRoundO {l : Leaf} (hex : l.exit = .at 0x80042708) (hst : l.S.steps ≤ 10)
    (hob : l.obligs = []) (hreg : l.S.regions = SO.regions)
    (hkeep : ∀ i ∈ 11 :: keepRegs, l.S.reg i = .var i)
    (h12 : l.S.reg 12 = .lit 0xa0d34704) (h13 : l.S.reg 13 = .ptr 0 444)
    (hcase : ∀ env : Env, (∀ b ∈ l.conds, b.eval env = true) →
      (l.S.mem = [] ∧ l.S.reg 10 = .init 0 0 8 ∧
        (Sym.bin .and (.init 0 0 8) (.bin .add (.bin .sll (.lit 1) (.var 12))
          (.lit 18446744073709551615))).eval env = 0) ∨
      (let v := Sym.bin .sub (.bin .add (.init 0 0 8) (.bin .sll (.lit 1) (.var 12)))
          (.bin .and (.init 0 0 8) (.bin .add (.bin .sll (.lit 1) (.var 12))
            (.lit 18446744073709551615)))
       l.S.mem = [⟨0, 0, 8, v⟩] ∧ l.S.reg 10 = v ∧ readConst l.S 0 0 8 = v ∧
        (Sym.bin .and (.init 0 0 8) (.bin .add (.bin .sll (.lit 1) (.var 12))
          (.lit 18446744073709551615))).eval env ≠ 0)) :
    LeafGoal allocPlan cO l := by
  intro g m hA hc
  obtain ⟨hwf, hm, -, -⟩ := AllocF.cut_800426e0 g m hA
  have hwf : Env.WF (cO.env g m) cO.S := hwf
  have hm : Match (cO.env g m) cO.S m := hm
  obtain ⟨⟨hpre, -, hK⟩, hmm, h11, h12m, -, h22⟩ := hA
  refine ⟨by rw [hob]; simp, by show l.S.steps - 0 ≤ 15; omega, fun m' hm' he hso => ?_⟩
  have ha := hpre.2.2.2.1
  have hal : ((Sym.bin .sll (.lit 1) (.var 12)).eval (cO.env g m)).toNat = 2 ^ (g.m.reg 12).toNat := by
    show (BinOp.eval .sll (BitVec.ofNat 64 1) (m.reg 12)).toNat = _
    rw [h12m]
    show (BitVec.ofNat 64 1 <<< ((g.m.reg 12).toNat % 64)).toNat = _
    have h4 := Nat.pow_le_pow_right (n := 2) (by decide) ha
    rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt (a := (g.m.reg 12).toNat) (b := 64) (by omega),
      Nat.shiftLeft_eq, toNat_ofNat_lt (by decide), Nat.one_mul,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h4 (by decide))]
  obtain ⟨p1, hR⟩ := rounded_of hpre hmm hwf hm rfl hm' hreg hso rfl rfl rfl (by omega) hal
    (hcase _ hc)
  have hK' := keep_of hm' (fun i hi => hkeep i (List.mem_cons_of_mem _ hi))
    (envOf_var (fun _ => shapeV) g m) hK
  rw [hex] at he ⊢
  have hpc : m'.pc.toNat = 0x80042708 := he
  refine ExitGoal.at_cut rfl ⟨cO2, by simp [allocPlan], hpc, ⟨⟨hpre, hpc, hK'⟩, ?_, ?_, ?_, h22,
    p1, hR⟩, by show 5 ≤ 15 - (l.S.steps - 0); omega⟩
  · exact (reg_var hm' 11 (hkeep 11 (List.mem_cons_self ..))).trans
      ((envOf_var (fun _ => shapeV) g m 11).trans h11)
  · rw [Match.reg_of hm' 12 _ h12]; rfl
  · rw [Match.reg_of hm' 13 _ h13]; exact vars_lit (g := g) (m := m) (o := 444) rfl

/-- The final test against `HEAP_TOP`: the block `[p1, p1 + bytes)` fits and `HEAP_POS` moves
past it, or it does not and `alloc` returns null. -/
theorem leafBump {c : Cut Sig} {ov : Nat → Option Sym} {l : Leaf}
    (hcS : c.S = Fn.entryState ov [varsR] []) (henv : c.env = envOf (fun _ => shapeV))
    (hcut : ∀ g m, c.A g m → Env.WF (c.env g m) c.S ∧ Match (c.env g m) c.S m)
    (hfacts : ∀ g m, c.A g m → AllocPre g.L g.m ∧ Keep g m ∧ ∃ bytes p1,
      m.reg 11 = BitVec.ofNat 64 bytes ∧ cap (lenOf g) ≤ bytes ∧ bytes < 2 ^ 63 ∧ Rounded g m p1)
    (hex : l.exit = .ret (.bin .and (.var 1) (.lit 18446744073709551614)))
    (hob : l.obligs = [.aligned (.bin .and (.var 1) (.lit 18446744073709551614)) 4])
    (hst : ∀ g m, l.S.steps - c.S.steps ≤ c.budget g m)
    (hreg : l.S.regions = [varsR]) (hkeep : ∀ i ∈ keepRegs, l.S.reg i = .var i)
    (hrc8 : readConst (Fn.entryState ov [varsR] []) 0 8 8 = .init 0 8 8)
    (hcase : (l.conds = [.geu (.init 0 8 8) (.bin .add (.var 10) (.var 11))] ∧
        l.S.mem = [⟨0, 0, 8, .bin .add (.var 10) (.var 11)⟩] ∧ l.S.reg 10 = .var 10 ∧
        readConst l.S 0 0 8 = .bin .add (.var 10) (.var 11)) ∨
      (l.conds = [.ltu (.init 0 8 8) (.bin .add (.var 10) (.var 11))] ∧ l.S.mem = [] ∧
        l.S.reg 10 = .lit 0)) :
    LeafGoal allocPlan c l := by
  intro g m hA hc
  obtain ⟨hwf, hm⟩ := hcut g m hA
  obtain ⟨hpre, hK, bytes, p1, h11, hcap, hb63, hR⟩ := hfacts g m hA
  rw [henv] at hwf hm hc ⊢
  rw [hcS] at hwf hm
  have hv1 : (envOf (fun _ => shapeV) g m).vars 1 = m.reg 1 := envOf_var _ g m 1
  refine ⟨by rw [hob]; simp only [List.mem_singleton, forall_eq]; exact ret_oblig hv1 hK hpre,
    hst g m, fun m' hm' he hso => ?_⟩
  rw [hcS] at hso
  obtain ⟨st, hd, hg, hpos, hposOf⟩ := pos_val hpre
  obtain ⟨r10, hp1lo, hp1hi, hrdp, hsoR⟩ := hR
  have hrh : Layout.ramHi = 3221225472 := rfl
  have hht : heapTop = 3221159936 := rfl
  have hp1lt : p1 < 2 ^ 64 := by unfold Layout.ramHi at hp1hi; omega
  -- `HEAP_TOP`, unchanged since entry
  have htop := rd_vars hwf hm rfl rfl (off := 8) (by omega)
  rw [hrc8, show posAddr + 8 = topAddr from rfl, rd_congr (by anum) fun t ht =>
    hsoR _ fun hr => by rw [inRange_ofNat (by anum) (by anum)] at hr; anum, hd.top] at htop
  have htop' : (Sym.init 0 8 8).eval (envOf (fun _ => shapeV) g m) = BitVec.ofNat 64 heapTop :=
    (Option.some.inj htop).symm
  have hsum : (Sym.bin .add (.var 10) (.var 11)).eval (envOf (fun _ => shapeV) g m) =
      BitVec.ofNat 64 (p1 + bytes) := by
    show m.reg 10 + m.reg 11 = _
    rw [r10, h11, ofNat_add_nat]
  have hsoP : ∀ a, ¬ InRange (BitVec.ofNat 64 posAddr) 8 a → m'.mem a = g.m.mem a := fun a ha =>
    (only_pos hm rfl hm' (by rw [hreg]; rfl) hso rfl (by
      rcases hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h] <;> simp) a ha).trans (hsoR a ha)
  have hposP : ∀ a, InRange (BitVec.ofNat 64 posAddr) 8 a → Priv g.L a := fun a ha => by
    obtain ⟨t, ht, rfl⟩ := inRange_lit (by anum) ha
    exact priv_cell hg (by unfold posAddr heapLo; omega)
  have hsoA : SameOutside (fun a => Priv g.L a ∨ InRange (g.m.reg 2 - 16) 16 a) g.m m' :=
    fun a ha => hsoP a fun hr => ha (.inl (hposP a hr))
  have hpres : ∀ a, Arena a → (g.m.mem a).isSome → (m'.mem a).isSome := fun a _ h => by
    by_cases hr : InRange (BitVec.ofNat 64 posAddr) 8 a
    · obtain ⟨t, ht, rfl⟩ := inRange_lit (by anum) hr
      exact pres_of hm' (by rw [hreg]; rfl) hso _ (rd_present hrdp (by anum) t ht)
    · rw [hsoP a hr]; exact h
  have hagree : ∀ a, Priv g.L a → ¬ InRange (BitVec.ofNat 64 posAddr) 8 a →
      m'.mem a = g.m.mem a := fun a _ ha => hsoP a ha
  have hK' := keep_of hm' hkeep (envOf_var (fun _ => shapeV) g m) hK
  rw [hex] at he ⊢
  have hret : Returns g.m m' := returns_of hK' (by rw [he]; exact ret_target hv1 hK)
  have hlen := hpre.2.2.1
  rcases hcase with ⟨hcs, hmem, h10, hrc⟩ | ⟨hcs, hmem, h10⟩
  · rw [hcs] at hc
    have hfit := hc _ (List.mem_singleton_self _)
    simp only [SBool.eval, BitVec.ult, htop', hsum, Bool.not_eq_true', decide_eq_false_iff_not,
      Nat.not_lt] at hfit
    rw [toNat_ofNat_lt (k := heapTop) (by omega), toNat_ofNat_lt (k := p1 + bytes) (by omega)] at hfit
    have hcl := le_cap (lenOf g)
    have hnew := rd_vars (wf_regions hwf (by rw [hreg]; rfl)) hm' (by rw [hreg]; rfl) rfl
      (off := 0) (Nat.zero_le _)
    rw [Nat.add_zero, hrc, hsum] at hnew
    have hheap := bump_ok hd hg (pos' := p1 + bytes) (by omega) (by omega)
      (.inr ⟨p1, lenOf g, rfl, hpre.2.1, by omega, by omega, by omega⟩) hnew hagree hpres
    refine post_block hret hsoA (q := p1) ?_ (by have := hg.pos_lo; omega) (by unfold lenOf at *; omega)
      hheap (fun t ht => bump_priv hg (by omega) (by unfold lenOf at *; omega))
    rw [Match.reg_of hm' 10 _ h10]; exact (envOf_var _ g m 10).trans r10
  · have hheap := bump_ok hd hg (L' := g.L) (pos' := p1) (by omega) hp1hi (.inl rfl)
      (by rw [rd_mem (funext fun a => by
        refine written_only hm rfl hm' (by rw [hreg]; rfl) hso a ?_
        rw [hmem]; simp)]; exact hrdp) hagree hpres
    exact post_null hret hsoA (by rw [Match.reg_of hm' 10 _ h10]; rfl) hheap

end ZesuExec.Fn.Alloc
