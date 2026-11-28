import ZesuExec.Fn.DTF.AuthFront

/-!
# DTF: the byte loops inside the `txAuthList` loop (programme plan S7 step 4)

The five field loops of a tuple (chainId `0x80002574`, nonce `0x80002690`, yParity `0x80002710`,
r `0x8000279c`, s `0x80002868`) have the budget `.beL 10 11 (.slot 0x68)`: the cursor and end
registers and the list bytes left. Here:

* `curOblL`/`curObl_holdsL`: a read at the cursor of such a loop is inside the payload (`CurOk`),
  so a leaf of the loop has its obligations (`leaf_at_xo`/`leaf_call_xo`);
* `tup_keep`/`addr_keep`/`end_keep`/`authExtra_keep`: the tuple state survives a leaf that keeps
  the frame words and (but at the s loop) the field cursor `s6`/`s7` it names;
* `leaf_beL`: one loop step (cursor `+ 1`, end and list bytes kept, at most 22 instructions)
  re-establishes the loop head's assertion.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

set_option maxRecDepth 20000

/-! ## The cursor of a byte loop inside the list loop -/

def beLOf : Inner → Option (Nat × Nat × Loc)
  | .beL cur fin l => some (cur, fin, l)
  | _ => none

theorem beLOf_spec {i : Inner} {cur fin : Nat} {lo : Loc} (h : beLOf i = some (cur, fin, lo)) :
    i = .beL cur fin lo := by
  cases i with
  | beL a b c =>
    simp only [beLOf, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1, h.2.1, h.2.2]
  | _ => simp [beLOf] at h

/-- The cursor of a `.beL` loop head, as the payload offset `c` its index `x` evaluates to. -/
theorem cur_idxL {d : CutData} {σ : Sig} {m : Machine} (hpc : d.pc ≠ entry) (hs : d.site = none)
    (hA : (mkCut d).A σ m) (hm : Match (envOf d.shape σ m) d.shape.S m) {cur fin : Nat}
    {lo : Loc} (hbe : beLOf (budgetAt d.pc).2 = some (cur, fin, lo)) (hc32 : cur < 32) {x : Sym}
    (hx : inpIdx d.shape.S cur = some x) :
    ∃ c e, x.eval (envOf d.shape σ m) = w c ∧ m.reg (Fin.ofNat 32 cur) = σ.inp + w c ∧
      m.reg (Fin.ofNat 32 fin) = σ.inp + w e ∧ c < e ∧ e ≤ σ.len ∧ e ≤ c + 32 := by
  have hcur := cur_of_A hpc hs hA
  rw [beLOf_spec hbe] at hcur
  obtain ⟨c, e, h1, h2, hlt, hle, h32⟩ := hcur
  refine ⟨c, e, ?_, h1, h2, hlt, hle, h32⟩
  have h := reg_eval hm hc32
  rw [inpIdx_spec hx, h1] at h
  simp only [Sym.eval, BinOp.eval, env_base3] at h
  simp at h
  bv_omega

/-- An obligation of a `.beL` loop head's leaf: the read at the cursor. -/
def curOblL (d : CutData) (o : Oblig) : Bool :=
  d.site.isNone && match beLOf (budgetAt d.pc).2 with
    | some (cur, _, _) => decide (cur < 32) && match inpIdx d.shape.S cur with
      | some x => o == .inBounds 3 0 x 1 1
      | none => false
    | none => false

theorem curObl_holdsL {d : CutData} {σ : Sig} {m : Machine} (hpc : d.pc ≠ entry)
    (hA : (mkCut d).A σ m) (hm : Match (envOf d.shape σ m) d.shape.S m) {o : Oblig}
    (h : curOblL d o = true) : o.holds (envOf d.shape σ m) := by
  unfold curOblL at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨hs, h⟩ := h
  split at h
  case h_2 => cases h
  next cur fin lo hbe =>
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc32, h⟩ := h
  split at h
  case h_2 => cases h
  next x hx =>
  simp only [beq_iff_eq] at h
  subst h
  obtain ⟨c, e, hxc, -, -, hlt, hle, -⟩ := cur_idxL hpc hs hA hm hbe hc32 hx
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  simp only [Oblig.holds, env_size3, hxc, w, BitVec.toNat_ofNat]
  omega

/-- `CoreChk0` and every obligation a read at the `.beL` loop's cursor. -/
def CoreChkL (d : CutData) (l : Leaf) : Bool := CoreChk0 d l && l.obligs.all (curOblL d)

theorem coreChkL_obl {d : CutData} {l : Leaf} (hpc : d.pc ≠ entry)
    (hcut : CutOK vcPlan (mkCut d)) (hck : CoreChkL d l = true) :
    ∀ σ m, (mkCut d).A σ m → (∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) →
      ∀ o ∈ l.obligs, o.holds (envOf d.shape σ m) := by
  intro σ m hA _ o ho
  unfold CoreChkL at hck
  simp only [Bool.and_eq_true, List.all_eq_true] at hck
  obtain ⟨-, hm, -, -⟩ := hcut σ m hA
  exact curObl_holdsL hpc hA hm (hck.2 o ho)

theorem coreChkL_0 {d : CutData} {l : Leaf} (hck : CoreChkL d l = true) : CoreChk0 d l = true := by
  unfold CoreChkL at hck; simp only [Bool.and_eq_true] at hck; exact hck.1

/-! ## Keeping the tuple state -/

/-- The frame words the tuple state names: list cursor `0x70`/`0x68`, payload length `0x30`,
buffer `0x58`/`0x60`, count `0x50`, tuple length `0x48`, the field's consumed length `0x2f8`, the
address `0x78`. -/
def authSlots : List Nat := [0x70, 0x68, 0x30, 0x58, 0x60, 0x50, 0x48, 0x2f8, 0x78]

/-- The leaf keeps `authSlots` and, when `regs`, the field cursor `s6`/`s7`. -/
def authKeep (d : CutData) (l : Leaf) (regs : Bool) : Bool :=
  authSlots.all (fun o => (Loc.slot o).sym l.S == (Loc.slot o).sym d.shape.S) &&
    (!regs || (l.S.reg 22 == d.shape.S.reg 22 && l.S.reg 23 == d.shape.S.reg 23))

theorem authKeep_slot {d : CutData} {l : Leaf} {regs : Bool} (h : authKeep d l regs = true)
    {o : Nat} (ho : o ∈ authSlots) : (Loc.slot o).sym l.S = (Loc.slot o).sym d.shape.S := by
  unfold authKeep at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.1 o ho

theorem authKeep_regs {d : CutData} {l : Leaf} (h : authKeep d l true = true) :
    l.S.reg 22 = d.shape.S.reg 22 ∧ l.S.reg 23 = d.shape.S.reg 23 := by
  unfold authKeep at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_true, Bool.false_or] at h
  exact h.2

theorem auth_load {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {regs : Bool} (h : authKeep d l regs = true) {o : Nat} (ho : o ∈ authSlots) :
    m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8 := by
  have hle : o + 8 ≤ frameBytes := by
    have : o ≤ 0x2f8 := by
      simp only [authSlots, List.mem_cons, List.not_mem_nil, or_false] at ho; omega
    unfold frameBytes; omega
  exact ctx_load C hle (authKeep_slot h ho)

theorem out_keep {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {regs : Bool} (h : authKeep d l regs = true) {n j c hh p : Nat}
    (ho : AuthOut σ m n j c hh p) : AuthOut σ m' n j c hh p :=
  authOut_mono (auth_load C h (by decide)) (auth_load C h (by decide))
    (auth_load C h (by decide)) ho

theorem buf_keep {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {regs : Bool} (h : authKeep d l regs = true) {n r : Nat}
    (hb : AuthBuf σ m n r) : AuthBuf σ m' n r :=
  authBuf_mono (auth_load C h (by decide)) (auth_load C h (by decide))
    (fun _ _ hl => ctx_live C hl) hb

theorem tup_keep {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (h : authKeep d l true = true) {b : Nat} {nx : Bool} (ht : AuthTup σ m b nx) :
    AuthTup σ m' b nx := by
  obtain ⟨c, hh, p, n, j, ht', pt, q, ho, l50, hb, hd, hle, l48, hbq, hqp, r22, r23, hnx⟩ := ht
  obtain ⟨e22, e23⟩ := authKeep_regs h
  refine ⟨c, hh, p, n, j, ht', pt, q, out_keep C h ho, ?_, buf_keep C h hb, hd, hle, ?_, hbq,
    hqp, ?_, ?_, fun hx => ?_⟩
  · rw [auth_load C h (by decide)]; exact l50
  · rw [auth_load C h (by decide)]; exact l48
  · rw [show (22 : Fin 32) = Fin.ofNat 32 22 from rfl, ctx_reg C (by decide) (by decide) e22]
    exact r22
  · rw [show (23 : Fin 32) = Fin.ofNat 32 23 from rfl, ctx_reg C (by decide) (by decide) e23]
    exact r23
  · obtain ⟨k, lk, hk⟩ := hnx hx
    exact ⟨k, by rw [auth_load C h (by decide)]; exact lk, hk⟩

theorem addr_keep {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {regs : Bool} (h : authKeep d l regs = true) (ha : AddrOk σ m) : AddrOk σ m' := by
  obtain ⟨a, la, hle⟩ := ha
  exact ⟨a, by rw [auth_load C h (by decide)]; exact la, hle⟩

theorem end_keep {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {regs : Bool} (h : authKeep d l regs = true) (he : AuthEnd σ m) : AuthEnd σ m' := by
  obtain ⟨c, hh, p, n, j, k, ho, l50, hb, hs, hk, l48, ha⟩ := he
  exact ⟨c, hh, p, n, j, k, out_keep C h ho, by rw [auth_load C h (by decide)]; exact l50,
    buf_keep C h hb, hs, hk, by rw [auth_load C h (by decide)]; exact l48, addr_keep C h ha⟩

/-- The loop heads' `Extra` survives a leaf that keeps the tuple state (the field cursor too but
at the s loop `0x80002868`, whose `AuthEnd` does not name it). -/
theorem loopExtra_keep {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {pc : Nat} (hp : pc = 0x80002574 ∨ pc = 0x80002690 ∨ pc = 0x80002710 ∨ pc = 0x8000279c ∨
      pc = 0x80002868)
    (h : authKeep d l (pc != 0x80002868) = true) (hx : Extra pc σ m) : Extra pc σ m' := by
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true, true_or, or_true,
      bne_iff_ne, ne_eq] at hx h ⊢
  · exact tup_keep C h hx
  · exact ⟨tup_keep C h hx.1, addr_keep C h hx.2⟩
  · exact ⟨tup_keep C h hx.1, addr_keep C h hx.2⟩
  · exact ⟨tup_keep C h hx.1, addr_keep C h hx.2⟩
  · exact end_keep C h hx

/-! ## One loop step -/

/-- The list-bytes location `lo` is the same after the leaf. -/
def locKept (S S' : SState) : Loc → Bool
  | .reg i => decide (i < 32) && S'.reg i == S.reg i
  | .slot o => decide (o + 8 ≤ frameBytes) && (Loc.slot o).sym S' == (Loc.slot o).sym S

theorem locKept_word {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {lo : Loc} (h : locKept d.shape.S l.S lo = true) : lo.word σ m' = lo.word σ m := by
  cases lo with
  | reg i =>
    simp only [locKept, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ctx_reg C h.1 h.1 h.2
  | slot o =>
    simp only [locKept, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ctx_slot C h.1 h.2

/-- A step of a `.beL` loop back to its head: the cursor advances by one byte, the end and the
list bytes are kept, the leaf's condition says cursor and end differed, at most 22 steps. -/
def stepOkL (d : CutData) (l : Leaf) : Bool :=
  d.site.isNone && match beLOf (budgetAt d.pc).2 with
    | some (cur, fin, lo) =>
      decide (cur < 32) && decide (fin < 32) && locKept d.shape.S l.S lo &&
      decide (l.S.steps - d.shape.S.steps ≤ 22) &&
      match inpIdx d.shape.S cur with
      | some x => l.S.reg cur == .bin .add (.ptr 3 1) x && l.S.reg fin == d.shape.S.reg fin &&
          l.conds.contains (.ne (l.S.reg cur) (l.S.reg fin))
      | none => false
    | none => false

/-- A plain cut's `Extra`. -/
theorem extra_of_A {d : CutData} {σ : Sig} {m : Machine} (hpc : d.pc ≠ entry)
    (hs : d.site = none) (hA : (mkCut d).A σ m) : Extra d.pc σ m := by
  simp only [mkCut, if_neg hpc, ACut, hs, reduceCtorEq, false_and, exists_false,
    or_false] at hA
  exact hA.2.2.2.2.2.2.1

/-- The cursor and the budget after one step of a `.beL` loop. -/
theorem step_budgetL {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (hpc : d.pc ≠ entry) (hA : (mkCut d).A σ m)
    (hc : ∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true)
    (hlen : restLen d σ m' ≤ restLen d σ m) (h : stepOkL d l = true) :
    CurOk σ m' (budgetAt d.pc).2 ∧
      budgetOf d σ m' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m := by
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  unfold stepOkL at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨hs, h⟩ := h
  split at h
  case h_2 => cases h
  next cur fin lo hbe =>
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hc32, hf32⟩, hlk⟩, hst⟩, h⟩ := h
  split at h
  case h_2 => cases h
  next x hx =>
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨⟨hl1, hl2⟩, hne⟩ := h
  obtain ⟨c, e, hxc, h1, h2, hlt, hle, h32⟩ := cur_idxL hpc hs hA C.hm hbe hc32 hx
  have hm1 : m'.reg (Fin.ofNat 32 cur) = σ.inp + w (c + 1) := by
    rw [reg_eval C.hm' hc32, hl1]
    simp only [Sym.eval, BinOp.eval, env_base3, hxc, w]
    rw [show BitVec.ofInt 64 1 = 1 from rfl, BitVec.ofNat_add]; bv_omega
  have hm2 : m'.reg (Fin.ofNat 32 fin) = σ.inp + w e := by
    rw [reg_eval C.hm' hf32, hl2, ← reg_eval C.hm hf32, h2]
  have hd := hc _ hne
  simp only [SBool.eval, bne_iff_ne, ne_eq] at hd
  rw [← reg_eval C.hm' hc32, ← reg_eval C.hm' hf32, hm1, hm2] at hd
  have hce : c + 1 ≠ e := fun h' => hd (by rw [h'])
  have htb := beLOf_spec hbe
  have hlo := locKept_word C hlk
  refine ⟨by rw [htb]; exact ⟨c + 1, e, hm1, hm2, by omega, hle, by omega⟩, ?_⟩
  unfold budgetOf
  rw [htb]
  simp only [innerOf]
  rw [hm1, hm2, h1, h2, sub_inp _ (Nat.le_of_lt hlt) (by omega), sub_inp _ (by omega) (by omega),
    hlo]
  omega

/-- One step of a byte loop inside the list loop: its head's assertion again. -/
theorem leaf_beL (d : CutData) (l : Leaf) (hpc : d.pc ≠ entry)
    (hcut : CutOK vcPlan (mkCut d)) (hsrc : SrcOk d = true) (hck : CoreChkL d l = true)
    (hex : l.exit = .at d.pc) (ht : targetOf d.pc = some d) (hat : AtChk d l d = true)
    (hlen : lenFrom d.shape.S l.S (advUse d l) d.rest (srcRest d l) d.rest = true)
    (hst : stepOkL d l = true)
    (hp : d.pc = 0x80002574 ∨ d.pc = 0x80002690 ∨ d.pc = 0x80002710 ∨ d.pc = 0x8000279c ∨
      d.pc = 0x80002868)
    (hk : authKeep d l (d.pc != 0x80002868) = true) : LeafGoal vcPlan (mkCut d) l := by
  have hs : d.site = none := by
    unfold stepOkL at hst
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hst
    exact hst.1
  refine leaf_at_xo d d l hpc hcut hsrc (coreChkL_0 hck) (coreChkL_obl hpc hcut hck) hex ht hat
    fun σ m m' hA hc C => ?_
  have hl : restLen d σ m' ≤ restLen d σ m := lenFrom_sound C hlen
  exact ⟨loopExtra_keep C hp hk (extra_of_A hpc hs hA), step_budgetL C hpc hA hc hl hst⟩

theorem DTF.leaf_80002574_0 :
    LeafGoal DTF.plan DTF.plan.cuts[128]! ((DTF.plan.leaves 0x80002574)[0]!) :=
  leaf_beL (table[128]!) ((leavesAt 0x80002574)[0]!) (by decide) DTF.cut_80002574 (by decide)
    (by decide) (by decide) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem DTF.leaf_80002690_0 :
    LeafGoal DTF.plan DTF.plan.cuts[131]! ((DTF.plan.leaves 0x80002690)[0]!) :=
  leaf_beL (table[131]!) ((leavesAt 0x80002690)[0]!) (by decide) DTF.cut_80002690 (by decide)
    (by decide) (by decide) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem DTF.leaf_80002710_0 :
    LeafGoal DTF.plan DTF.plan.cuts[133]! ((DTF.plan.leaves 0x80002710)[0]!) :=
  leaf_beL (table[133]!) ((leavesAt 0x80002710)[0]!) (by decide) DTF.cut_80002710 (by decide)
    (by decide) (by decide) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem DTF.leaf_8000279c_0 :
    LeafGoal DTF.plan DTF.plan.cuts[135]! ((DTF.plan.leaves 0x8000279c)[0]!) :=
  leaf_beL (table[135]!) ((leavesAt 0x8000279c)[0]!) (by decide) DTF.cut_8000279c (by decide)
    (by decide) (by decide) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem DTF.leaf_80002868_0 :
    LeafGoal DTF.plan DTF.plan.cuts[137]! ((DTF.plan.leaves 0x80002868)[0]!) :=
  leaf_beL (table[137]!) ((leavesAt 0x80002868)[0]!) (by decide) DTF.cut_80002868 (by decide)
    (by decide) (by decide) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)

end ZesuExec.Fn.DTF
