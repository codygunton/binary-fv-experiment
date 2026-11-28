import ZesuExec.Fn.DTF.AuthStep

/-!
# DTF: the second half of the `txAuthList` loop (programme plan S7 step 4)

After a tuple's last field (`AuthEnd`, `0x80002868`/`0x80002820`): `n + 1` at `S-0x2f8`,
`16 n`/`128 n` at `S-0x330`/`S-0x338` (`AuthApp`), then the store into the slot `bp + 0x90 n`
(`0x80002420`, `0x80002434`) when `n < cap`; else the growth (`AuthGrow`: remap, which is F0 and
returns null; `alloc(newCap n · 0x90, log2 alignment 4)`; `memcpy`; `free(bp, n · 0x90, 4)`;
`AuthNew`, `AuthNewF`; the store with the new block). Here: the tools those leaves share.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

set_option maxRecDepth 20000

/-! ## Small facts -/

/-- A leaf whose conditions contradict its source's assertion. -/
theorem leaf_vac (d : CutData) (l : Leaf)
    (h : ∀ σ m, (mkCut d).A σ m → (∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) → False) :
    LeafGoal vcPlan (mkCut d) l := fun σ m hA hc => (h σ m hA hc).elim

theorem wordAt_of_load {m : Machine} {a v : Word} (h : m.load a 8 = some v) :
    TX.wordAt m a = v := by
  simp [TX.wordAt, h]

/-- A frame word of the source as the source's symbolic state reads it (`.init 0 o 8`). -/
theorem src_init {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {o : Nat} (ho : o + 8 ≤ frameBytes) (h : (Loc.slot o).sym d.shape.S = .init 0 o 8) :
    (Sym.init 0 o 8).eval (envOf d.shape σ m) = TX.wordAt m (σ.fr + w o) := by
  have e := loc_word_eval C.wf C.hm C.hS (loc := .slot o) (by simp only [Loc.fine]; simpa using ho)
  simp only [Loc.word] at e
  rw [e, h]

/-- `Ctx` keeps the frame word `o` the leaf does not write. -/
theorem ctx_keep {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {o : Nat} (ho : o + 8 ≤ frameBytes) (h : (Loc.slot o).sym l.S = (Loc.slot o).sym d.shape.S)
    {v : Word} (hv : m.load (σ.fr + w o) 8 = some v) : m'.load (σ.fr + w o) 8 = some v := by
  rw [ctx_load C ho h]; exact hv

/-- The list's payload lies in the payload: `c + h + p ≤ len`. -/
theorem authList_le {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (h4 : σ.t = 4) {c h p : Nat}
    (hl : AuthList σ c h p) : c + h + p ≤ σ.len := by
  obtain ⟨hs, hd⟩ := hl
  have hf := fit_of_arms hpre (arms := [4]) (.inr (by simp [h4])) (by decide) hs
  obtain ⟨-, hle, -⟩ := TX.fits_bounds hf hd
  rw [List.length_drop, payload_len hpre] at hle
  have := skip_le hs
  rw [payload_len hpre] at this
  omega

/-- The count is below `2^32`: `n ≤ j ≤ p ≤ len`. -/
theorem out_n {σ : Sig} {m : Machine} (hpre : Pre σ.A σ.g σ.m) (h4 : σ.t = 4) {n j c h p : Nat}
    (ho : AuthOut σ m n j c h p) : j ≤ p ∧ c + h + p ≤ σ.len ∧ n < 2 ^ 32 := by
  obtain ⟨hl, hs, hnj, -⟩ := ho
  have hle := authList_le hpre h4 hl
  have hj := skip_le hs
  have hlen := payload_len hpre
  simp only [TX.itemPayload, List.length_take, List.length_drop] at hj
  have := len_lt32 hpre
  omega

/-! ## Word arithmetic -/

theorem w_add1 (n : Nat) : w n + 1 = w (n + 1) := by
  simp only [w]; rw [BitVec.ofNat_add]; rfl

theorem w_sll {n k c : Nat} (hk : k < 64) (hc : 2 ^ k = c) (h : n * c < 2 ^ 64) :
    w n <<< ((w k).toNat % 64) = w (c * n) := by
  subst hc
  apply BitVec.eq_of_toNat_eq
  have hk' : (w k).toNat % 64 = k := by simp only [w, BitVec.toNat_ofNat]; omega
  have hn : n ≤ n * 2 ^ k := Nat.le_mul_of_pos_right n (Nat.two_pow_pos k)
  rw [hk', BitVec.toNat_shiftLeft]
  simp only [w, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by rw [Nat.mul_comm]; exact h), Nat.mul_comm]

/-- The growth rule without overflow: `sat((n+1) >> 1 + (n+1) + 1) = newCap n`. -/
theorem newCap_eval {n : Nat} (hn : n < 2 ^ 32) :
    let a := w n + 1
    let s := ((a >>> ((w 1).toNat % 64)) + a) + 1
    (0 - (if s.ult a then 1 else 0)) ||| s = w (newCap n) := by
  intro a s
  have ha : a = w (n + 1) := w_add1 n
  have h1 : (w 1).toNat % 64 = 1 := by decide
  have o1 : (1 : Word).toNat = 1 := rfl
  have e1 : (w (n + 1)).toNat = n + 1 := by simp only [w, BitVec.toNat_ofNat]; omega
  have en : (w (newCap n)).toNat = newCap n := by
    simp only [w, BitVec.toNat_ofNat, newCap]; omega
  have hs : s = w (newCap n) := by
    show ((a >>> ((w 1).toNat % 64)) + a) + 1 = _
    rw [ha, h1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, e1, o1, en]
    simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one, newCap]
    omega
  have hult : s.ult a = false := by
    rw [hs, ha]
    simp only [BitVec.ult, en, e1, decide_eq_false_iff_not, Nat.not_lt]
    unfold newCap; omega
  rw [hult, hs]
  simp

theorem newCap_lt {n : Nat} (hn : n < 2 ^ 32) : newCap n < 2 ^ 34 := by
  unfold newCap; omega

/-- No overflow in `newCap n · 0x90`: `mulhu` is 0. -/
theorem mulhu0 {n : Nat} (hn : n < 2 ^ 40) : BinOp.eval .mulhu (w n) (w 144) = 0 := by
  simp only [BinOp.eval, w, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.div_eq_of_lt (by omega)]
  rfl

/-! ## The state across a call: frame words below the outcome, the live list -/

/-- Every (aligned) frame word below `0x2e0` (the outcome slot of the list loop's `decodeItem`)
kept. -/
def LowKeep (σ : Sig) (m m' : Machine) : Prop :=
  ∀ o, o % 8 = 0 → o + 8 ≤ 0x2e0 → m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8

theorem lk {σ : Sig} {m m' : Machine} (h : LowKeep σ m m') {o : Nat}
    (ho : o % 8 = 0 ∧ o + 8 ≤ 0x2e0) {v : Word} (hv : m.load (σ.fr + w o) 8 = some v) :
    m'.load (σ.fr + w o) 8 = some v := by
  rw [h o ho.1 ho.2]; exact hv

theorem out_lk {σ : Sig} {m m' : Machine} (h : LowKeep σ m m') {n j c hh p : Nat}
    (ho : AuthOut σ m n j c hh p) : AuthOut σ m' n j c hh p :=
  authOut_mono (h _ (by decide) (by decide)) (h _ (by decide) (by decide))
    (h _ (by decide) (by decide)) ho

theorem buf_lk {σ : Sig} {m m' : Machine} (h : LowKeep σ m m')
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) {n r : Nat} (hb : AuthBuf σ m n r) :
    AuthBuf σ m' n r :=
  authBuf_mono (h _ (by decide) (by decide)) (h _ (by decide) (by decide)) hL hb

/-- The leaf keeps every aligned frame word below `0x2e0`. -/
def lowKept (d : CutData) (l : Leaf) : Bool :=
  (List.range 92).all fun k => (Loc.slot (8 * k)).sym l.S == (Loc.slot (8 * k)).sym d.shape.S

theorem ctx_lowKeep {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (h : lowKept d l = true) : LowKeep σ m m' := by
  intro o h8 ho
  obtain ⟨k, rfl⟩ : ∃ k, o = 8 * k := ⟨o / 8, by omega⟩
  have hk := List.all_eq_true.mp h k (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq] at hk
  exact ctx_load C (by unfold frameBytes; omega) hk

theorem addr_lk {σ : Sig} {m m' : Machine} (h : LowKeep σ m m') (ha : AddrOk σ m) :
    AddrOk σ m' := by
  obtain ⟨a, la, hle⟩ := ha
  exact ⟨a, lk h (by decide) la, hle⟩

theorem end_lk {σ : Sig} {m m' : Machine} (h : LowKeep σ m m')
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) (he : AuthEnd σ m) : AuthEnd σ m' := by
  obtain ⟨c, hh, p, n, j, k, ho, l50, hb, hs, hk, l48, ha⟩ := he
  exact ⟨c, hh, p, n, j, k, out_lk h ho, lk h (by decide) l50, buf_lk h hL hb, hs, hk,
    lk h (by decide) l48, addr_lk h ha⟩

theorem cur_lk {σ : Sig} {m m' : Machine} (h : LowKeep σ m m') {n : Nat} (hc : AuthCur σ m n) :
    AuthCur σ m' n := by
  obtain ⟨c, hh, p, j, k, ho, hs, hk, l48⟩ := hc
  exact ⟨c, hh, p, j, k, out_lk h ho, hs, hk, lk h (by decide) l48⟩

theorem app_lk {σ : Sig} {m m' : Machine} (h : LowKeep σ m m') {n : Nat} (ha : AuthApp σ m n) :
    AuthApp σ m' n := by
  obtain ⟨hc, l78, l40, l38⟩ := ha
  exact ⟨cur_lk h hc, lk h (by decide) l78, lk h (by decide) l40, lk h (by decide) l38⟩

theorem grow_lk {σ : Sig} {m m' : Machine} (h : LowKeep σ m m')
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) {n : Nat} (hg : AuthGrow σ m n) :
    AuthGrow σ m' n := by
  obtain ⟨ha, hb, l60, l08, l10, l18, l50⟩ := hg
  exact ⟨app_lk h ha, buf_lk h hL hb, lk h (by decide) l60, lk h (by decide) l08,
    lk h (by decide) l10, lk h (by decide) l18, lk h (by decide) l50⟩

theorem new_lk {σ : Sig} {m m' : Machine} (h : LowKeep σ m m') {L X : List (Word × Nat)}
    (hL : Live σ m L X → Live σ m' L X) {n : Nat}
    (hn : AuthApp σ m n ∧ ∃ bp newp : Word, m.load (σ.fr + w 0x58) 8 = some bp ∧
      m.load (σ.fr + w 0x60) 8 = some (w n) ∧ m.load (σ.fr + w 0x08) 8 = some (w (newCap n)) ∧
      m.load (σ.fr + w 0x50) 8 = some newp ∧ Live σ m L X ∧
      (newp, newCap n * 0x90) ∈ X ∧ (0 < n → (bp, n * 0x90) ∈ X)) : AuthNew σ m' n := by
  obtain ⟨ha, bp, newp, l58, l60, l08, l50, hlive, h1, h2⟩ := hn
  exact ⟨app_lk h ha, bp, newp, lk h (by decide) l58, lk h (by decide) l60, lk h (by decide) l08,
    lk h (by decide) l50, L, X, hL hlive, h1, h2⟩

theorem done_lk {σ : Sig} {m m' : Machine} (h : LowKeep σ m m')
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) {n : Nat} (hd : AuthDone σ m n) :
    AuthDone σ m' n := by
  obtain ⟨c, hh, p, hl, hs, hn, l78, l30, hp, hb⟩ := hd
  exact ⟨c, hh, p, hl, hs, hn, lk h (by decide) l78, lk h (by decide) l30, hp, buf_lk h hL hb⟩

/-- What a return gives at the return site: the frame below the outcome slot and the live list
kept, for `decodeItem` (outcome at `0x2e0`) and `remap`. -/
theorem ret_keep {s : Site} {σ : Sig} {x : Idx} {r : Nat} {mc m : Machine}
    (hSF : s.kind.SiteFine s = true) (hsite : SiteA s r σ x mc)
    (hpost : (calleeOf s.kind).Post σ x mc m)
    (hk : ∀ o, o + 8 ≤ 0x2e0 → s.kind.Keeps s o = true) : LowKeep σ mc m := by
  obtain ⟨-, -, hkeep⟩ := ret_common hSF hsite hpost
  exact fun o _ ho => hkeep o (by unfold frameBytes; omega) (hk o ho)

theorem remap_live {s : Site} {σ : Sig} {x : Idx} {r : Nat} {mc m : Machine}
    (hk : Kind.SiteFine .remap s = true) (hsite : SiteA s r σ x mc) (hq : F0.Post mc m)
    (hp : Preserved mc m) {L X : List (Word × Nat)} (hlive : Live σ mc L X) : Live σ m L X := by
  have hc := hsite.2.1
  have hpre := hc.2.1
  simp only [Kind.SiteFine, beq_iff_eq] at hk
  have r2 := sp_fr hsite hk
  have e2 := below_fr_toNat hpre
  have hfr := fr_toNat hpre
  obtain ⟨-, -, hso⟩ := hq
  refine live_keep hlive hso hp fun a h hl => ?_
  rw [r2] at h
  have hsp := pre_sp hpre
  unfold frameBytes stackBytes TX.stackBytes Layout.ramLo at *
  exact (stack_R hpre (by rw [e2]; unfold stackBytes TX.stackBytes; omega) (by rw [e2]; omega)
    h).2 (priv_sub hpre hlive hl)

/-- `memcpy` keeps a live list whose blocks hold its destination. -/
theorem memcpy_live {σ : Sig} {mc m : Machine} (hc : Common σ mc) (hq : MemcpyPost mc m)
    (hp : Preserved mc m) {L X : List (Word × Nat)} (hlive : Live σ mc L X)
    (hdst : ∀ a, InRange (mc.reg 10) (mc.reg 12).toNat a → InLive L a) : Live σ m L X := by
  have hpre := hc.2.1
  have hq' : ziskMemcpy mc = some m := hq
  refine live_keep hlive (R := fun a => InRange (mc.reg 10) (mc.reg 12).toNat a ∨
    InRange TX.scratch 8 a) (fun a ha => memcpy_out hq' (fun h => ha (.inl h))
      (fun h => ha (.inr h))) hp fun a h hP => ?_
  rcases h with h | h
  · exact σ.A.priv_not_live L a hP (hdst a h)
  · exact (scratch_R hpre h).2.1 (priv_sub hpre hlive hP)

/-! ## After the tuple's last field -/

theorem end_2868 {σ : Sig} {m : Machine} (hA : (mkCut (table[137]!)).A σ m) : AuthEnd σ m := by
  have hx := extra_of_A (d := table[137]!) (by decide) (by decide) hA
  rw [show (table[137]!).pc = 0x80002868 by decide] at hx
  simpa [Extra, AuthExtra] using hx

theorem end_2820 {σ : Sig} {m : Machine} (hA : (mkCut (table[136]!)).A σ m) : AuthEnd σ m := by
  obtain ⟨mc, x, hsite, hpost⟩ := ret_parts (i := 136) (by decide) (by decide) hA
  have hsx := hsite.2.2.2.2.2.2.2.2
  rw [show (table[136]!).pc = 0x80002820 by decide] at hsx
  simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true, or_false] at hsx
  have hkd : (siteAt 136).kind = .f2 := by decide
  have hSF : (siteAt 136).kind.SiteFine (siteAt 136) = true := by decide
  have h10 : regFr (siteAt 136) 10 = some 0x2e0 := by decide
  have hk := ret_keep hSF hsite hpost fun o ho => by
    rw [hkd]; simp only [Kind.Keeps, h10, decide_eq_true_eq]; omega
  have hq : F2.Post mc m := by have := hpost.1; rw [hkd] at this; exact this
  have hSF' : Kind.SiteFine .f2 (siteAt 136) = true := by rw [← hkd]; exact hSF
  exact end_lk hk (fun L X hl => f2_live hSF' hsite hq hpost.2 hl) hsx.1

/-- A leaf after the tuple's last field writes `n + 1`, `16 n`, `128 n` and keeps the list
cursor, the payload and tuple lengths and the buffer. -/
theorem end_app {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (h4 : σ.t = 4) (he : AuthEnd σ m)
    (k70 : (Loc.slot 0x70).sym l.S = (Loc.slot 0x70).sym d.shape.S)
    (k68 : (Loc.slot 0x68).sym l.S = (Loc.slot 0x68).sym d.shape.S)
    (k30 : (Loc.slot 0x30).sym l.S = (Loc.slot 0x30).sym d.shape.S)
    (k48 : (Loc.slot 0x48).sym l.S = (Loc.slot 0x48).sym d.shape.S)
    (k58 : (Loc.slot 0x58).sym l.S = (Loc.slot 0x58).sym d.shape.S)
    (k60 : (Loc.slot 0x60).sym l.S = (Loc.slot 0x60).sym d.shape.S)
    (i50 : (Loc.slot 0x50).sym d.shape.S = .init 0 0x50 8)
    (i60 : (Loc.slot 0x60).sym d.shape.S = .init 0 0x60 8)
    (s78 : (Loc.slot 0x78).sym l.S = .bin .add (.init 0 0x50 8) (.lit 1))
    (s40 : (Loc.slot 0x40).sym l.S = .bin .sll (.init 0 0x50 8) (.lit 4))
    (s38 : (Loc.slot 0x38).sym l.S = .bin .sll (.init 0 0x50 8) (.lit 7)) :
    ∃ n bp cap, AuthApp σ m' n ∧ m'.load (σ.fr + w 0x58) 8 = some bp ∧
      m'.load (σ.fr + w 0x60) 8 = some cap ∧ BufIs σ m' n 0 bp cap ∧ n < 2 ^ 32 ∧
      (Sym.init 0 0x50 8).eval (envOf d.shape σ m) = w n ∧
      (Sym.init 0 0x60 8).eval (envOf d.shape σ m) = cap := by
  obtain ⟨c, hh, p, n, j, k, ho, l50, ⟨bp, cap, l58, l60, hbi⟩, hs, hk, l48, -⟩ := he
  have hpre := C.F.common.2.1
  obtain ⟨-, -, hn⟩ := out_n hpre h4 ho
  have e50 : (Sym.init 0 0x50 8).eval (envOf d.shape σ m) = w n := by
    rw [src_init C (by decide) i50, wordAt_of_load l50]
  have e60 : (Sym.init 0 0x60 8).eval (envOf d.shape σ m) = cap := by
    rw [src_init C (by decide) i60, wordAt_of_load l60]
  have l78 := ctx_word C (o := 0x78) (by decide) s78
  have l40 := ctx_word C (o := 0x40) (by decide) s40
  have l38 := ctx_word C (o := 0x38) (by decide) s38
  simp only [Sym.eval_bin, Sym.eval_lit, BinOp.eval, e50] at l78 l40 l38
  rw [show w n + 1#64 = w (n + 1) from w_add1 n] at l78
  rw [show BitVec.ofNat 64 4 = w 4 from rfl, w_sll (c := 16) (by decide) (by decide)
    (by omega)] at l40
  rw [show BitVec.ofNat 64 7 = w 7 from rfl, w_sll (c := 128) (by decide) (by decide)
    (by omega)] at l38
  refine ⟨n, bp, cap, ⟨⟨c, hh, p, j, k, authOut_mono (ctx_load C (by decide) k70)
    (ctx_load C (by decide) k68) (ctx_load C (by decide) k30) ho, hs, hk,
    ctx_keep C (by decide) k48 l48⟩, l78, l40, l38⟩, ctx_keep C (by decide) k58 l58,
    ctx_keep C (by decide) k60 l60, bufIs_mono (fun L X hl => ctx_live C hl) hbi, hn, e50, e60⟩

end ZesuExec.Fn.DTF
