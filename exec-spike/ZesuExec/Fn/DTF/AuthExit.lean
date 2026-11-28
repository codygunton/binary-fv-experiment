import ZesuExec.Fn.DTF.AuthBack

/-!
# DTF: the exits after the tuple's last field (programme plan S7 step 4)

From the s loop's exit (`0x80002868`, leaves 1–4) and the empty s field (`0x80002820`, leaves
0–3): the store path (`n < cap`, `0x80002420`), the empty buffer (`cap = 0`, `0x800029c4`), the
remap call of a full buffer (return `0x800029a8`) and the overflow check (vacuous: `mulhu` of the
new capacity and `0x90` is 0). Tools: the address reads (`addrObl`), budgets that keep the list
term (`listOk`, `call_list_budget`), the growth rule as the code computes it (`capSym`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

set_option maxRecDepth 20000

/-! ## Obligations: the cursor and the tuple's address -/

/-- The reads of the tuple's 20-byte address (`var 79`: `S-0x2f8` minus the payload base). -/
def addrObl (o : Oblig) : Bool :=
  o == .inBounds 3 0 (.var 79) 1 8 || o == .inBounds 3 8 (.var 79) 1 8 ||
    o == .inBounds 3 16 (.var 79) 1 4

theorem addrObl_holds {sh : Shape} {σ : Sig} {m : Machine} (ha : AddrOk σ m) {o : Oblig}
    (h : addrObl o = true) : o.holds (envOf sh σ m) := by
  obtain ⟨a, la, hle⟩ := ha
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hv : (Sym.var 79).eval (envOf sh σ m) = w a := by
    rw [var_slot (by decide), show 8 * (79 - 64) = 0x78 from rfl, wordAt_of_load la,
      BitVec.add_comm, BitVec.add_sub_cancel]
  have ht : (w a).toNat = a := by simp only [w, BitVec.toNat_ofNat]; omega
  simp only [addrObl, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl <;> simp only [Oblig.holds, env_size3, hv, ht] <;> omega

/-- Every obligation a read at the `.beL` loop's cursor or of the tuple's address. -/
def OblLA (d : CutData) (l : Leaf) : Bool := l.obligs.all (fun o => curOblL d o || addrObl o)

theorem oblLA_holds {d : CutData} {l : Leaf} (hpc : d.pc ≠ entry)
    (hcut : CutOK vcPlan (mkCut d)) (hck : OblLA d l = true)
    (hadd : ∀ σ m, (mkCut d).A σ m → AddrOk σ m) :
    ∀ σ m, (mkCut d).A σ m → (∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) →
      ∀ o ∈ l.obligs, o.holds (envOf d.shape σ m) := by
  intro σ m hA _ o ho
  unfold OblLA at hck
  have h := List.all_eq_true.mp hck o ho
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨-, hm, -, -⟩ := hcut σ m hA
    exact curObl_holdsL hpc hA hm h
  · exact addrObl_holds (hadd σ m hA) h

/-! ## Budgets inside the list loop -/

def listLoc : Inner → Option Loc
  | .list l => some l
  | .beL _ _ l => some l
  | _ => none

theorem listLoc_inner {i : Inner} {lo : Loc} (h : listLoc i = some lo) (σ : Sig) (m : Machine) :
    256 * (lo.word σ m).toNat ≤ innerOf σ m i := by
  cases i with
  | list l => simp only [listLoc, Option.some.injEq] at h; subst h; simp [innerOf]
  | beL c f l => simp only [listLoc, Option.some.injEq] at h; subst h; simp [innerOf]
  | _ => simp [listLoc] at h

/-- The target's budget is the source's list term (kept by the leaf) and a constant at most the
source's less the steps. -/
def listOk (d : CutData) (l : Leaf) (pc' : Nat) : Bool :=
  match listLoc (budgetAt d.pc).2, (budgetAt pc').2 with
  | some lo, .list lo' => decide (lo = lo') && locKept d.shape.S l.S lo &&
      decide ((budgetAt pc').1 + (l.S.steps - d.shape.S.steps) ≤ (budgetAt d.pc).1)
  | _, _ => false

theorem list_budget {d d' : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (hlen : restLen d' σ m' ≤ restLen d σ m) (h : listOk d l d'.pc = true) :
    CurOk σ m' (budgetAt d'.pc).2 ∧
      budgetOf d' σ m' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m := by
  unfold listOk at h
  split at h
  · next lo lo' h1 h2 =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hk⟩, hK⟩ := h
    refine ⟨by rw [h2]; trivial, ?_⟩
    have hw := locKept_word C hk
    have hi := listLoc_inner h1 σ m
    have ht : innerOf σ m' (.list lo) = 256 * (lo.word σ m).toNat := by simp only [innerOf, hw]
    unfold budgetOf
    rw [h2, ht]
    omega
  · cases h

/-- A call leaf's budget when the return site's is the list term at a frame word the callee and
the leaf keep. -/
theorem call_list_budget {d d' : CutData} {l : Leaf} {s : Site} {σ : Sig} {x : Idx}
    {m m' m'' : Machine} (C : Ctx d l σ m m') (hSF : s.kind.SiteFine s = true)
    (hsite : SiteA s d'.pc σ x m') (hpost : (calleeOf s.kind).Post σ x m' m'')
    (hR : retLen d l s d' = true) {o : Nat} (ho : o + 8 ≤ frameBytes)
    (hko : s.kind.Keeps s o = true) (hk : (Loc.slot o).sym l.S = (Loc.slot o).sym d.shape.S)
    (hlo : listLoc (budgetAt d.pc).2 = some (.slot o)) (h' : (budgetAt d'.pc).2 = .list (.slot o))
    (hK : s.kind.bound + (budgetAt d'.pc).1 + (l.S.steps - d.shape.S.steps) ≤ (budgetAt d.pc).1) :
    s.kind.bound + budgetOf d' σ m'' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m := by
  have hlen := ret_len C hSF hsite hpost hR
  have hkeep := (ret_common hSF hsite hpost).2.2 o ho hko
  have hw := ctx_slot C ho hk
  have hi := listLoc_inner hlo σ m
  have e : TX.wordAt m'' (σ.fr + w o) = TX.wordAt m (σ.fr + w o) := by
    rw [← hw]; simp only [TX.wordAt, hkeep]
  simp only [Loc.word] at hi
  have ht : innerOf σ m'' (.list (.slot o)) = 256 * (TX.wordAt m (σ.fr + w o)).toNat := by
    simp only [innerOf, Loc.word, e]
  unfold budgetOf
  rw [h', ht]
  omega

/-! ## Appending the tuple -/

theorem end_addr {σ : Sig} {m : Machine} (he : AuthEnd σ m) : AddrOk σ m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ha⟩ := he
  exact ha

/-- The frame words `end_app` needs: kept, the source's, and the three the leaf writes. -/
def appChk (d : CutData) (l : Leaf) : Bool :=
  [0x70, 0x68, 0x30, 0x48, 0x58, 0x60].all
      (fun o => (Loc.slot o).sym l.S == (Loc.slot o).sym d.shape.S) &&
    (Loc.slot 0x50).sym d.shape.S == .init 0 0x50 8 &&
    (Loc.slot 0x60).sym d.shape.S == .init 0 0x60 8 &&
    (Loc.slot 0x78).sym l.S == .bin .add (.init 0 0x50 8) (.lit 1) &&
    (Loc.slot 0x40).sym l.S == .bin .sll (.init 0 0x50 8) (.lit 4) &&
    (Loc.slot 0x38).sym l.S == .bin .sll (.init 0 0x50 8) (.lit 7)

theorem end_app' {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (h4 : σ.t = 4) (he : AuthEnd σ m) (hk : appChk d l = true) :
    ∃ n bp cap, AuthApp σ m' n ∧ m'.load (σ.fr + w 0x58) 8 = some bp ∧
      m'.load (σ.fr + w 0x60) 8 = some cap ∧ BufIs σ m' n 0 bp cap ∧ n < 2 ^ 32 ∧
      (Sym.init 0 0x50 8).eval (envOf d.shape σ m) = w n ∧
      (Sym.init 0 0x60 8).eval (envOf d.shape σ m) = cap := by
  unfold appChk at hk
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at hk
  obtain ⟨k70, k68, k30, k48, k58, k60, i50, i60, s78, s40, s38⟩ := hk
  exact end_app C h4 he k70 k68 k30 k48 k58 k60 i50 i60 s78 s40 s38

/-- The store path (`n < cap`, target `0x80002420`): room for the tuple. -/
theorem store_extra {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (h4 : σ.t = 4) (he : AuthEnd σ m) (hk : appChk d l = true)
    (hlt : ((Sym.init 0 0x50 8).eval (envOf d.shape σ m)).ult
      ((Sym.init 0 0x60 8).eval (envOf d.shape σ m)) = true) :
    Extra 0x80002420 σ m' := by
  obtain ⟨n, bp, cap, ha, l58, l60, ⟨hn, hc, hlive⟩, hn32, e50, e60⟩ := end_app' C h4 he hk
  rw [e50, e60] at hlt
  simp only [BitVec.ult, w, BitVec.toNat_ofNat, decide_eq_true_eq] at hlt
  rw [Nat.mod_eq_of_lt (by omega)] at hlt
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact ⟨n, ha, bp, cap, l58, l60, by omega, by omega, hlive⟩

/-! ## Growing the buffer -/

/-- The growth rule as the code computes it from `n` (`S-0x320`): saturating
`(n + 1) >> 1 + (n + 1) + 1`. -/
def capSym : Sym :=
  .bin .or (.bin .sub (.lit 0) (.bin .sltu
      (.bin .add (.bin .add (.bin .srl (.bin .add (.init 0 0x50 8) (.lit 1)) (.lit 1))
        (.bin .add (.init 0 0x50 8) (.lit 1))) (.lit 1))
      (.bin .add (.init 0 0x50 8) (.lit 1))))
    (.bin .add (.bin .add (.bin .srl (.bin .add (.init 0 0x50 8) (.lit 1)) (.lit 1))
      (.bin .add (.init 0 0x50 8) (.lit 1))) (.lit 1))

theorem capSym_eval {env : Env} {n : Nat} (h : (Sym.init 0 0x50 8).eval env = w n)
    (hn : n < 2 ^ 32) : capSym.eval env = w (newCap n) := by
  simp only [capSym, Sym.eval_bin, Sym.eval_lit, BinOp.eval, h]
  exact newCap_eval hn

/-- The leaf writes the new capacity, its `128`/`16` multiples and the overflow word. -/
def growChk (l : Leaf) : Bool :=
  (Loc.slot 0x08).sym l.S == capSym && (Loc.slot 0x10).sym l.S == .bin .sll capSym (.lit 7) &&
    (Loc.slot 0x18).sym l.S == .bin .sll capSym (.lit 4) &&
    (Loc.slot 0x50).sym l.S == .bin .mulhu capSym (.lit 144)

theorem grow_of {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {n : Nat} {bp : Word} (ha : AuthApp σ m' n) (l58 : m'.load (σ.fr + w 0x58) 8 = some bp)
    (l60 : m'.load (σ.fr + w 0x60) 8 = some (w n)) (hb : BufIs σ m' n 0 bp (w n))
    (hn : n < 2 ^ 32) (e50 : (Sym.init 0 0x50 8).eval (envOf d.shape σ m) = w n)
    (hg : growChk l = true) : AuthGrow σ m' n := by
  simp only [growChk, Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨⟨⟨g8, g16⟩, g24⟩, g80⟩ := hg
  have hc := capSym_eval e50 hn
  have hcl := newCap_lt hn
  have l08 := ctx_word C (o := 0x08) (by decide) g8
  have l10 := ctx_word C (o := 0x10) (by decide) g16
  have l18 := ctx_word C (o := 0x18) (by decide) g24
  have l50 := ctx_word C (o := 0x50) (by decide) g80
  simp only [Sym.eval_bin, Sym.eval_lit, hc, BinOp.eval] at l08 l10 l18 l50
  rw [show BitVec.ofNat 64 7 = w 7 from rfl, w_sll (c := 128) (by decide) (by decide)
    (by omega)] at l10
  rw [show BitVec.ofNat 64 4 = w 4 from rfl, w_sll (c := 16) (by decide) (by decide)
    (by omega)] at l18
  have h0 : BitVec.ofNat 64 ((w (newCap n)).toNat * (BitVec.ofNat 64 144).toNat / 2 ^ 64) =
      w 0 := mulhu0 (by omega)
  rw [h0] at l50
  exact ⟨ha, ⟨bp, w n, l58, l60, hb⟩, l60, l08, l10, l18, l50⟩

/-- The empty buffer (`cap = 0`, target `0x800029c4`): grow from no tuples, `a0 = 0`. -/
theorem grow0_extra {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (h4 : σ.t = 4) (he : AuthEnd σ m) (hk : appChk d l = true) (hg : growChk l = true)
    (h10 : l.S.reg 10 = .init 0 0x60 8)
    (h0 : (Sym.init 0 0x60 8).eval (envOf d.shape σ m) = 0) : Extra 0x800029c4 σ m' := by
  obtain ⟨n, bp, cap, ha, l58, l60, hb, hn32, e50, e60⟩ := end_app' C h4 he hk
  rw [e60] at h0
  subst h0
  have hn0 : n = 0 := by have := hb.1; simp at this; omega
  subst hn0
  have r10 : m'.reg 10 = 0 := by
    rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, reg_eval C.hm' (by decide), h10, e60]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact ⟨⟨0, grow_of C ha l58 l60 hb (by decide) e50 hg⟩, r10⟩

/-- A full buffer (`n ≥ cap ≠ 0`): `cap = n`, grow. -/
theorem grow_full {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (h4 : σ.t = 4) (he : AuthEnd σ m) (hk : appChk d l = true) (hg : growChk l = true)
    (hge : (!((Sym.init 0 0x50 8).eval (envOf d.shape σ m)).ult
      ((Sym.init 0 0x60 8).eval (envOf d.shape σ m))) = true) : ∃ n, AuthGrow σ m' n := by
  obtain ⟨n, bp, cap, ha, l58, l60, hb, hn32, e50, e60⟩ := end_app' C h4 he hk
  rw [e50, e60] at hge
  simp only [BitVec.ult, w, BitVec.toNat_ofNat, Bool.not_eq_true', decide_eq_false_iff_not,
    Nat.not_lt] at hge
  rw [Nat.mod_eq_of_lt (by omega)] at hge
  have hcap : cap = w n := by
    apply BitVec.eq_of_toNat_eq
    have := hb.1
    simp only [w, BitVec.toNat_ofNat]
    omega
  subst hcap
  exact ⟨n, grow_of C ha l58 l60 hb hn32 e50 hg⟩

/-- The overflow check never fails: `mulhu (newCap n) 0x90 = 0`. -/
theorem cap_mulhu {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (h4 : σ.t = 4) (he : AuthEnd σ m) (i50 : (Loc.slot 0x50).sym d.shape.S = .init 0 0x50 8) :
    (Sym.bin .mulhu capSym (.lit 144)).eval (envOf d.shape σ m) = 0 := by
  obtain ⟨c, hh, p, n, j, k, ho, l50, -, -, -, -, -⟩ := he
  obtain ⟨-, -, hn⟩ := out_n C.F.common.2.1 h4 ho
  have e50 : (Sym.init 0 0x50 8).eval (envOf d.shape σ m) = w n := by
    rw [src_init C (by decide) i50, wordAt_of_load l50]
  have hcl := newCap_lt hn
  simp only [Sym.eval_bin, Sym.eval_lit, capSym_eval e50 hn]
  exact mulhu0 (by omega)

/-- The remap call of a full buffer (return `0x800029a8`, F0: always null). -/
theorem remap_call {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (CF : CallFacts (siteAt 138) (table[138]!).pc σ m') {n : Nat} (hg : AuthGrow σ m' n)
    (hR : retLen d l (siteAt 138) (table[138]!) = true)
    (hk : (Loc.slot 0x68).sym l.S = (Loc.slot 0x68).sym d.shape.S)
    (hlo : listLoc (budgetAt d.pc).2 = some (.slot 0x68))
    (hK : 9 + 2714 + (l.S.steps - d.shape.S.steps) ≤ (budgetAt d.pc).1) :
    ∃ x, IdxOk (siteAt 138).kind σ x m' ∧ SiteX (table[138]!).pc σ x m' ∧
      ∀ m'', (calleeOf (siteAt 138).kind).Post σ x m' m'' →
        (siteAt 138).kind.bound + budgetOf (table[138]!) σ m'' +
          (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m := by
  have hsp : m'.reg 2 = σ.fr + w 0 := CF.shape.1 (2, .fr 0) (by decide) _ rfl
  have hidx : IdxOk (siteAt 138).kind σ ([], [], ⟨[], []⟩) m' := by
    rw [show (siteAt 138).kind = .remap by decide]
    exact ⟨⟨CF.common.2.2.1, stack16 CF.common hsp, CF.aligned⟩, trivial⟩
  have hsx : SiteX (table[138]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[138]!).pc = 0x800029a8 by decide]
    simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true]
    exact ⟨n, hg⟩
  refine ⟨_, hidx, hsx, fun m'' hpost => ?_⟩
  have hfld := CF.fields
  have hsite : SiteA (siteAt 138) (table[138]!).pc σ ([], [], ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx, hfld, CF.chk, hsx⟩
  exact call_list_budget C (by decide) hsite hpost hR (by decide) (by decide) hk hlo rfl
    (by rw [show (siteAt 138).kind.bound = 9 by decide]; exact hK)

/-! ## The eight exits -/

theorem DTF.leaf_80002868_1 :
    LeafGoal DTF.plan DTF.plan.cuts[137]! ((DTF.plan.leaves 0x80002868)[1]!) := by
  refine leaf_at_xo (table[137]!) (table[123]!) ((leavesAt 0x80002868)[1]!) (by decide)
    DTF.cut_80002868 (by decide) (by decide)
    (oblLA_holds (by decide) DTF.cut_80002868 (by decide) fun _ _ hA => end_addr (end_2868 hA))
    (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have hlt := hc _ (show SBool.ltu (.init 0 80 8) (.init 0 96 8) ∈ _ by decide)
  simp only [SBool.eval] at hlt
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[123]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[123]!).pc = 0x80002420 by decide]
  exact store_extra C h4 (end_2868 hA) (by decide) hlt

theorem DTF.leaf_80002868_2 :
    LeafGoal DTF.plan DTF.plan.cuts[137]! ((DTF.plan.leaves 0x80002868)[2]!) := by
  refine leaf_at_xo (table[137]!) (table[139]!) ((leavesAt 0x80002868)[2]!) (by decide)
    DTF.cut_80002868 (by decide) (by decide)
    (oblLA_holds (by decide) DTF.cut_80002868 (by decide) fun _ _ hA => end_addr (end_2868 hA))
    (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have h0 := hc _ (show SBool.eq (.init 0 96 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, Sym.eval_lit] at h0
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[139]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[139]!).pc = 0x800029c4 by decide]
  exact grow0_extra C h4 (end_2868 hA) (by decide) (by decide) (by decide) h0

theorem DTF.leaf_80002868_3 :
    LeafGoal DTF.plan DTF.plan.cuts[137]! ((DTF.plan.leaves 0x80002868)[3]!) := by
  refine leaf_call_xo (table[137]!) (table[138]!) (siteAt 138) ((leavesAt 0x80002868)[3]!)
    F0.entry (by decide) DTF.cut_80002868 (by decide) (by decide)
    (oblLA_holds (by decide) DTF.cut_80002868 (by decide) fun _ _ hA => end_addr (end_2868 hA))
    (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have hge := hc _ (show SBool.geu (.init 0 80 8) (.init 0 96 8) ∈ _ by decide)
  simp only [SBool.eval] at hge
  obtain ⟨n, hg⟩ := grow_full C h4 (end_2868 hA) (by decide) (by decide) hge
  exact remap_call C CF hg (by decide) (by decide) (by decide) (by decide)

theorem DTF.leaf_80002868_4 :
    LeafGoal DTF.plan DTF.plan.cuts[137]! ((DTF.plan.leaves 0x80002868)[4]!) := by
  refine leaf_at_xo (table[137]!) (table[139]!) ((leavesAt 0x80002868)[4]!) (by decide)
    DTF.cut_80002868 (by decide) (by decide)
    (oblLA_holds (by decide) DTF.cut_80002868 (by decide) fun _ _ hA => end_addr (end_2868 hA))
    (by decide) rfl (by decide) fun σ m m' hA hc C => ?_
  have hov := hc _ (show SBool.ne (.bin .mulhu capSym (.lit 144)) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, cap_mulhu C (arm4 C.F.arms (by decide)) (end_2868 hA) (by decide),
    Sym.eval_lit] at hov
  exact absurd hov (by decide)

theorem DTF.leaf_80002820_0 :
    LeafGoal DTF.plan DTF.plan.cuts[136]! ((DTF.plan.leaves 0x80002820)[0]!) := by
  refine leaf_at_xo (table[136]!) (table[123]!) ((leavesAt 0x80002820)[0]!) (by decide)
    DTF.cut_80002820 (by decide) (by decide)
    (oblLA_holds (by decide) DTF.cut_80002820 (by decide) fun _ _ hA => end_addr (end_2820 hA))
    (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have hlt := hc _ (show SBool.ltu (.init 0 80 8) (.init 0 96 8) ∈ _ by decide)
  simp only [SBool.eval] at hlt
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[123]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[123]!).pc = 0x80002420 by decide]
  exact store_extra C h4 (end_2820 hA) (by decide) hlt

theorem DTF.leaf_80002820_1 :
    LeafGoal DTF.plan DTF.plan.cuts[136]! ((DTF.plan.leaves 0x80002820)[1]!) := by
  refine leaf_at_xo (table[136]!) (table[139]!) ((leavesAt 0x80002820)[1]!) (by decide)
    DTF.cut_80002820 (by decide) (by decide)
    (oblLA_holds (by decide) DTF.cut_80002820 (by decide) fun _ _ hA => end_addr (end_2820 hA))
    (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have h0 := hc _ (show SBool.eq (.init 0 96 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, Sym.eval_lit] at h0
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[139]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[139]!).pc = 0x800029c4 by decide]
  exact grow0_extra C h4 (end_2820 hA) (by decide) (by decide) (by decide) h0

theorem DTF.leaf_80002820_2 :
    LeafGoal DTF.plan DTF.plan.cuts[136]! ((DTF.plan.leaves 0x80002820)[2]!) := by
  refine leaf_call_xo (table[136]!) (table[138]!) (siteAt 138) ((leavesAt 0x80002820)[2]!)
    F0.entry (by decide) DTF.cut_80002820 (by decide) (by decide)
    (oblLA_holds (by decide) DTF.cut_80002820 (by decide) fun _ _ hA => end_addr (end_2820 hA))
    (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have hge := hc _ (show SBool.geu (.init 0 80 8) (.init 0 96 8) ∈ _ by decide)
  simp only [SBool.eval] at hge
  obtain ⟨n, hg⟩ := grow_full C h4 (end_2820 hA) (by decide) (by decide) hge
  exact remap_call C CF hg (by decide) (by decide) (by decide) (by decide)

theorem DTF.leaf_80002820_3 :
    LeafGoal DTF.plan DTF.plan.cuts[136]! ((DTF.plan.leaves 0x80002820)[3]!) := by
  refine leaf_at_xo (table[136]!) (table[139]!) ((leavesAt 0x80002820)[3]!) (by decide)
    DTF.cut_80002820 (by decide) (by decide)
    (oblLA_holds (by decide) DTF.cut_80002820 (by decide) fun _ _ hA => end_addr (end_2820 hA))
    (by decide) rfl (by decide) fun σ m m' hA hc C => ?_
  have hov := hc _ (show SBool.ne (.bin .mulhu capSym (.lit 144)) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, cap_mulhu C (arm4 C.F.arms (by decide)) (end_2820 hA) (by decide),
    Sym.eval_lit] at hov
  exact absurd hov (by decide)

end ZesuExec.Fn.DTF
