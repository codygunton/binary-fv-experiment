import ZesuExec.Fn.MergeInPlace.Steps

/-!
# `mergeInPlace` copies: the cut facts, the prologue and epilogue, and the semantic steps

Shared by every copy (generic over `Cfg`):

* `revAt_swap`, `items_rev`: a whole element swap of a reversal (`step_swap`) is the next
  reversal state.
* cut facts (`CutOK`'s `WF` and `Match`) for `S0`, `SN`, `SP`, `SC`, `SR`, `SE`.
* `entry_step` (the prologue's stores), `early_post` (a return before the prologue),
  `epi_post` (the epilogue's return).
* the byte comparison: `lex_prefix`, `cmp_ne`, `cmp_all`; one-byte loads `init1_toNat`.
* budgets: `Qf` with `Qf_le`, `Qf_step`.
* the rounds: `round_init`, `mid_of_first`, `mid_empty`, `join_of_mid` (the rotation),
  `join_done`, `last_curr`, `round_of_last`, `done_of_last`.
-/

namespace ZesuExec.Fn.MergeInPlace
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Machine
open ZesuExec.Fn.Rotate (SliceIs revAt rev bytesOf elem_lt addr_ne SliceIs.keep slice_bytesOf)

/-! ## A whole swap of a reversal -/

theorem revAt_swap {lo L i : Nat} (F : Nat → Nat → Byte) (hi : 2 * i + 2 ≤ L) (e o : Nat) :
    revAt lo L (i + 1) 0 F e o =
      if e = lo + i then revAt lo L i 0 F (lo + (L - 1 - i)) o
      else if e = lo + (L - 1 - i) then revAt lo L i 0 F (lo + i) o
      else revAt lo L i 0 F e o := by
  by_cases h1 : e = lo + i
  · subst h1; rw [if_pos rfl]; simp only [revAt]
    rw [if_pos (by omega), if_neg (by omega), show lo + (L - 1 - (lo + i - lo)) = lo + (L - 1 - i) by omega]
  · rw [if_neg h1]
    by_cases h2 : e = lo + (L - 1 - i)
    · subst h2; rw [if_pos rfl]; simp only [revAt]
      rw [if_pos (by omega), if_neg (by omega),
        show lo + (L - 1 - (lo + (L - 1 - i) - lo)) = lo + i by omega]
    · rw [if_neg h2]; simp only [revAt]
      by_cases h : lo ≤ e ∧ e < lo + L ∧ (e - lo < i ∨ L - 1 - (e - lo) < i)
      · rw [if_pos (by omega), if_pos (by omega)]
      · rw [if_neg (by omega), if_neg (by omega)]

/-- `step_swap` on elements `lo + i` and `lo + (L-1-i)` of `revAt … i 0 F`. -/
theorem items_rev {m mh : Machine} {lo L i : Nat} {F : Nat → Nat → Byte} (hi : 2 * i + 2 ≤ L)
    (h : Items m mh fun e o => if e = lo + i then revAt lo L i 0 F (lo + (L - 1 - i)) o
      else if e = lo + (L - 1 - i) then revAt lo L i 0 F (lo + i) o else revAt lo L i 0 F e o) :
    Items m mh (revAt lo L (i + 1) 0 F) :=
  h.congr fun e _ o _ => (revAt_swap F hi e o).symm

/-! ## Register overrides -/

theorem ovL_mem {l : List (Nat × Sym)} {i : Nat} {s : Sym} (h : ovL l i = some s) : (i, s) ∈ l := by
  unfold ovL at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have h1 := List.find?_some hp
  have h2 := List.mem_of_find?_eq_some hp
  simp only [beq_iff_eq] at h1
  rw [← h1]; exact h2

theorem match_ovL {m : Machine} {regs : List (Word × Nat)} {l : List (Nat × Sym)}
    {rs : List Region} {ks : List Write}
    (hov : ∀ p ∈ l, p.2.eval (entryEnv m regs) = m.reg (Fin.ofNat 32 p.1))
    (hpres : ∀ r j, r < rs.length → j < (entryEnv m regs).size r →
      (m.mem ((entryEnv m regs).base r + BitVec.ofNat 64 j)).isSome)
    (hknown : ∀ k ∈ ks, ∀ t < k.n,
      (entryEnv m regs).byte0 k.r (k.off + t) = byteOf (k.v.eval (entryEnv m regs)) t) :
    Match (entryEnv m regs) (entryState (ovL l) rs ks) m :=
  entry_match (fun i _ s hs => by
    have := hov _ (ovL_mem hs)
    rw [this]; congr 1; apply Fin.ext; simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]) hpres hknown

/-! ## Region facts -/

section
variable {c : Cfg} {m : Machine}

theorem frame_align (h : Pre c m) : (frame c m).toNat % 16 = 0 := by
  have := (pre_frame h).1
  have := h.2.1.1
  have := c.fs_align
  omega

theorem frame_ok (h : Pre c m) : RegionOk ((frame c m, c.fs), frameR c.fs) := by
  obtain ⟨hf, hlo, hhi, hsp⟩ := pre_frame h
  refine ⟨by simp [frameR], frame_align h, ?_⟩
  simp [frameR, Machine.writable, Machine.inRange]; unfold Layout.ramLo Layout.ramHi at *; omega

theorem elem_addr (h : Pre c m) {e : Nat} (he : e < bE m) :
    (ptr m + w (32 * e)).toNat = (ptr m).toNat + 32 * e := by
  have := elem_lt (E := 32) he (show 0 < 32 by omega)
  exact toNat_add_ofNat (by have := pre_hfit h; omega)

theorem elem_ok (h : Pre c m) {e : Nat} (he : e < bE m) (R : Region) (hs : R.size = some 32)
    (ha : R.align = 1) : RegionOk ((ptr m + w (32 * e), 32), R) := by
  have hi := pre_items h
  have := elem_lt (E := 32) he (show 31 < 32 by omega)
  refine ⟨by simp [hs], by simp [ha, Nat.mod_one], ?_⟩
  rw [elem_addr h he]
  split <;> simp [Machine.writable, Machine.readable, Machine.inRange] <;>
    unfold Layout.ramLo Layout.ramHi at * <;> omega

theorem items_add {e j : Nat} : ptr m + w (32 * e) + w j = ptr m + w (32 * e + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

end

/-! ## Cut facts -/

theorem cutN_facts {mh : Machine} : Env.WF (envN mh) SN ∧ Match (envN mh) SN mh :=
  ⟨entry_wf (m := mh) [] (by simp) (by simp),
    entry_match (fun _ _ s hs => by simp at hs) (fun r j hr _ => by simp at hr) (by simp)⟩

theorem s0_eval (c : Cfg) (b : Word) : b - w c.fs + BitVec.ofInt 64 (c.fs : Int) = b := by
  rw [BitVec.ofInt_natCast]; exact BitVec.sub_add_cancel b _

theorem cut0_facts {c : Cfg} {m : Machine} (h : Pre c m) :
    Env.WF (env0 c m) (S0 c) ∧ Match (env0 c m) (S0 c) m := by
  have hh := h
  obtain ⟨-, hst, -, hr1, hp1, hr2, hp2, -, -, -, -, -, -, hd12, hd1f, hd2f, -⟩ := hh
  refine ⟨entry_wf (m := m) [((m.reg 11, 16), rangeR), ((m.reg 12, 16), rangeR),
      ((m.reg 2 - w c.fs, c.fs), frameR c.fs)] ?_ ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · exact ⟨by simp [rangeR], by simp [rangeR, Nat.mod_one], by simpa [rangeR] using hr1⟩
    · exact ⟨by simp [rangeR], by simp [rangeR, Nat.mod_one], by simpa [rangeR] using hr2⟩
    · exact frame_ok h
  · simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hd12, hd1f⟩, hd2f, fun _ h => h.elim⟩
  · refine match_ovL ?_ (fun r j hr hj => ?_) (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl) <;> simp [Sym.eval, entryEnv, Env.base]
      exact BitVec.sub_add_cancel _ _
    · simp at hr
      rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
      · simpa [entryEnv, Env.base] using hp1 j (by simpa [entryEnv, Env.size] using hj)
      · simpa [entryEnv, Env.base] using hp2 j (by simpa [entryEnv, Env.size] using hj)
      · simpa [entryEnv, Env.base] using hst.2.2.2 j (by simpa [entryEnv, Env.size] using hj)

/-- An `SP` cut: the frame at `sp` (`s0 = sp + fs`) and the element `e` at register `r`. -/
theorem cutP_facts {c : Cfg} {m mh : Machine} {G : Nat → Nat → Byte} {r e : Nat}
    {extra : List (Nat × Sym)} (h : Pre c m) (hc : Common c m mh) (hs : Items m mh G)
    (he : e < bE m) (hr : mh.reg (Fin.ofNat 32 r) = ptr m + w (32 * e))
    (hx : ∀ p ∈ extra, p.2.eval (envP c r mh) = mh.reg (Fin.ofNat 32 p.1)) :
    Env.WF (envP c r mh) (SP c r extra) ∧ Match (envP c r mh) (SP c r extra) mh := by
  obtain ⟨-, h2, h8, -, -, hpres, -⟩ := hc
  have hfit := pre_hfit h
  have hd := pre_disj h
  refine ⟨?_, ?_⟩
  · have := entry_wf (m := mh) (ov := ovL ([(2, .ptr 0 0), (8, .ptr 0 c.fs), (r, .ptr 1 0)] ++ extra))
      (ks := []) [((mh.reg 2, c.fs), frameR c.fs), ((mh.reg (Fin.ofNat 32 r), 32), elemR)] ?_ ?_
    · exact this
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · rw [h2]; exact frame_ok h
      · rw [hr]; exact elem_ok h he _ rfl rfl
    · rw [List.map_cons, List.map_cons, List.map_nil, List.pairwise_pair, h2, hr]
      unfold Disjoint at hd ⊢
      rw [elem_addr h he]
      have := elem_lt (E := 32) he (show 31 < 32 by omega)
      simp only at hd ⊢
      omega
  · refine match_ovL ?_ (fun k j hk hj => ?_) (by simp)
    · intro p hp
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with (rfl | rfl | rfl) | hp
      · simp [Sym.eval, entryEnv, Env.base]
      · simp only [Sym.eval, entryEnv, Env.base, List.getD_cons_zero, Fin.reduceOfNat]
        rw [h8, h2]; exact s0_eval c _
      · simp [Sym.eval, entryEnv, Env.base]
      · exact hx p hp
    · simp at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simp only [entryEnv, Env.base, Env.size, List.getD_cons_zero] at hj ⊢
        rw [h2]; exact hpres j hj
      · simp only [entryEnv, Env.base, Env.size, List.getD_cons_succ, List.getD_cons_zero] at hj ⊢
        rw [hr, items_add, hs e he j hj]; rfl

/-- An `SC` cut: the bytes at frame offsets `jx ≠ jy`. -/
theorem cutC_facts {c : Cfg} {m mh : Machine} {x y jx jy : Nat} (h : Pre c m) (hc : Common c m mh)
    (hjx : jx < c.fs) (hjy : jy < c.fs) (hne : jx ≠ jy)
    (hx : mh.reg (Fin.ofNat 32 x) = frame c m + w jx) (hy : mh.reg (Fin.ofNat 32 y) = frame c m + w jy) :
    Env.WF (envC x y mh) (SC x y) ∧ Match (envC x y mh) (SC x y) mh := by
  obtain ⟨-, -, -, -, -, hpres, -⟩ := hc
  obtain ⟨hf, hlo, hhi, hsp⟩ := pre_frame h
  have ax := frame_addr h hjx
  have ay := frame_addr h hjy
  refine ⟨?_, ?_⟩
  · have := entry_wf (m := mh) (ov := ovL [(x, .ptr 0 0), (y, .ptr 1 0)]) (ks := [])
      [((mh.reg (Fin.ofNat 32 x), 1), byteR), ((mh.reg (Fin.ofNat 32 y), 1), byteR)] ?_ ?_
    · exact this
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · refine ⟨by simp [byteR], by simp [byteR, Nat.mod_one], ?_⟩
        simp only [byteR, Bool.false_eq_true, if_false]; rw [hx, ax]
        simp [Machine.readable, Machine.inRange]; unfold Layout.ramLo Layout.ramHi at *; omega
      · refine ⟨by simp [byteR], by simp [byteR, Nat.mod_one], ?_⟩
        simp only [byteR, Bool.false_eq_true, if_false]; rw [hy, ay]
        simp [Machine.readable, Machine.inRange]; unfold Layout.ramLo Layout.ramHi at *; omega
    · rw [List.map_cons, List.map_cons, List.map_nil, List.pairwise_pair]
      unfold Disjoint; simp only
      rw [hx, hy, ax, ay]; omega
  · refine match_ovL ?_ (fun k j hk hj => ?_) (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) <;> simp [Sym.eval, entryEnv, Env.base]
    · simp at hk
      have hj0 : j = 0 := by
        rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp [entryEnv, Env.size] at hj <;> omega
      subst hj0
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simp only [entryEnv, Env.base, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        rw [hx]; exact hpres jx hjx
      · simp only [entryEnv, Env.base, List.getD_cons_succ, List.getD_cons_zero,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        rw [hy]; exact hpres jy hjy

/-- An `SR` cut: elements `e₁ ≠ e₂` at registers `lo - 15` and `hi - 16`. -/
theorem cutR_facts {c : Cfg} {m mh : Machine} {G : Nat → Nat → Byte} {lo hi e₁ e₂ : Nat}
    (h : Pre c m) (hs : Items m mh G) (h1 : e₁ < bE m) (h2 : e₂ < bE m) (hne : e₁ ≠ e₂)
    (hlo : mh.reg (Fin.ofNat 32 lo) = ptr m + w (32 * e₁ + 15))
    (hhi : mh.reg (Fin.ofNat 32 hi) = ptr m + w (32 * e₂ + 16)) :
    Env.WF (envR lo hi mh) (SR lo hi) ∧ Match (envR lo hi mh) (SR lo hi) mh := by
  have hfit := pre_hfit h
  have b1 : mh.reg (Fin.ofNat 32 lo) - w 15 = ptr m + w (32 * e₁) := by
    rw [hlo]; apply BitVec.eq_of_toNat_eq
    have := elem_lt (E := 32) h1 (show 15 < 32 by omega)
    rw [BitVec.toNat_sub, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    simp; omega
  have b2 : mh.reg (Fin.ofNat 32 hi) - w 16 = ptr m + w (32 * e₂) := by
    rw [hhi]; apply BitVec.eq_of_toNat_eq
    have := elem_lt (E := 32) h2 (show 16 < 32 by omega)
    rw [BitVec.toNat_sub, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    simp; omega
  refine ⟨?_, ?_⟩
  · have := entry_wf (m := mh) (ov := ovL [(lo, .ptr 0 15), (hi, .ptr 1 16)]) (ks := [])
      [((mh.reg (Fin.ofNat 32 lo) - w 15, 32), elemW), ((mh.reg (Fin.ofNat 32 hi) - w 16, 32), elemW)]
      ?_ ?_
    · exact this
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · rw [b1]; exact elem_ok h h1 _ rfl rfl
      · rw [b2]; exact elem_ok h h2 _ rfl rfl
    · rw [List.map_cons, List.map_cons, List.map_nil, List.pairwise_pair]
      unfold Disjoint; simp only
      rw [b1, b2, elem_addr h h1, elem_addr h h2]
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · left; have := Nat.mul_le_mul_left 32 hl; omega
      · right; have := Nat.mul_le_mul_left 32 hl; omega
  · refine match_ovL ?_ (fun k j hk hj => ?_) (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · simp only [Sym.eval, envR, entryEnv, Env.base, List.getD_cons_zero]
        rw [show BitVec.ofInt 64 15 = w 15 from rfl]; exact BitVec.sub_add_cancel _ _
      · simp only [Sym.eval, envR, entryEnv, Env.base, List.getD_cons_succ, List.getD_cons_zero]
        rw [show BitVec.ofInt 64 16 = w 16 from rfl]; exact BitVec.sub_add_cancel _ _
    · simp at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simp only [envR, entryEnv, Env.base, Env.size, List.getD_cons_zero] at hj ⊢
        rw [b1, items_add, hs e₁ h1 j hj]; rfl
      · simp only [envR, entryEnv, Env.base, Env.size, List.getD_cons_succ, List.getD_cons_zero] at hj ⊢
        rw [b2, items_add, hs e₂ h2 j hj]; rfl

theorem envE_vars (c : Cfg) (m mh : Machine) :
    ∀ i < 32, (envE c m mh).vars i = mh.reg (Fin.ofNat 32 i) := by
  intro i hi; simp [envE, Env.setVars, show ¬ 32 ≤ i by omega, entryEnv]

theorem cutE_facts {c : Cfg} {m mh : Machine} (h : Pre c m) (hc : Common c m mh) :
    Env.WF (envE c m mh) (SE c) ∧ Match (envE c m mh) (SE c) mh := by
  obtain ⟨-, h2, -, -, hsv, hpres, -⟩ := hc
  have hwf := entry_wf (m := mh) (ov := ovL [(2, .ptr 0 0)]) (ks := knownE c)
    [((frame c m, c.fs), frameR c.fs)] (by simp only [List.mem_singleton]; rintro p rfl; exact frame_ok h)
    (by simp)
  refine ⟨⟨hwf.len, hwf.disjoint, hwf.size, hwf.align, hwf.range⟩, ⟨by simp [SE, entryState],
    fun i => ?_, fun r j hr hj => ?_, fun k hk t ht => ?_⟩⟩
  · rw [show (SE c).reg i.val = if i.val = 0 then .lit 0 else
        ((ovL [(2, Sym.ptr 0 0)]) i.val).getD (.var i.val) from entryState_reg _ _ _ i]
    by_cases h0 : i.val = 0
    · simp [h0, Sym.eval, Machine.reg]
    · by_cases e2 : i.val = 2
      · have : i = 2 := Fin.ext e2
        subst this
        simp [ovL, Sym.eval, envE, Env.setVars, entryEnv, Env.base, h2]
      · have : ovL [(2, Sym.ptr 0 0)] i.val = none := by
          have : ((2 : Nat) == i.val) = false := by simpa using Ne.symm e2
          simp [ovL, List.find?, this]
        simp only [h0, this, if_false, Option.getD_none, Sym.eval_var]
        rw [envE_vars c m mh _ i.isLt]
        simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
  · simp [SE, entryState] at hr; subst hr
    have hj' : j < c.fs := by simpa [envE, Env.setVars, entryEnv, Env.size] using hj
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hpres j hj')
    simp [envE, Env.setVars, entryEnv, Env.base, memByte, SE, entryState, Env.byte0, hb]
  · simp only [SE, entryState, knownE, List.mem_map] at hk
    obtain ⟨s, hs, rfl⟩ := hk
    have := hsv s hs t ht
    simp [envE, Env.setVars, entryEnv, Env.byte0, Sym.eval, this]

/-! ## The prologue -/

theorem inW_0 {c : Cfg} {mh : Machine} {a : Word} (h : InWritable (env0 c mh) (S0 c) a) :
    ∃ j < c.fs, a = frame c mh + w j := by
  obtain ⟨k, R, j, hR, hw, hj, rfl⟩ := inW_entry h
  rcases k with _ | _ | _ | k
  · simp at hR; subst hR; simp [rangeR] at hw
  · simp at hR; subst hR; simp [rangeR] at hw
  · exact ⟨j, by simpa using hj, by simp [frame]⟩
  · simp at hR

theorem find_slot (r : Nat) (v : Nat × Nat → Sym) :
    ∀ (L : List (Nat × Nat)), L.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1) →
    ∀ s ∈ L, ∀ t < 8, (L.map fun s => (⟨r, s.1, 8, v s⟩ : Write)).find? (·.covers r (s.1 + t)) =
      some ⟨r, s.1, 8, v s⟩
  | [], _, s, hs, _, _ => absurd hs List.not_mem_nil
  | s' :: L, hd, s, hs, t, ht => by
    rw [List.map_cons, List.find?_cons]
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hd
    rcases List.mem_cons.mp hs with rfl | hs
    · have : (⟨r, s.1, 8, v s⟩ : Write).covers r (s.1 + t) = true := by
        simp [Write.covers]; omega
      rw [this]
    · have hc : (⟨r, s'.1, 8, v s'⟩ : Write).covers r (s.1 + t) = false := by
        have := h1 s hs; simp [Write.covers]; omega
      rw [hc]; exact find_slot r v L h2 s hs t ht

theorem memByte_slot (env : Env) (r : Nat) (v : Nat × Nat → Sym) (L : List (Nat × Nat))
    (hd : L.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1)) {s : Nat × Nat} (hs : s ∈ L)
    {t : Nat} (ht : t < 8) :
    memByte env (L.map fun s => (⟨r, s.1, 8, v s⟩ : Write)) r (s.1 + t) = byteOf ((v s).eval env) t := by
  unfold memByte; rw [find_slot r v L hd s hs t ht]; simp

/-- The entry run to the first loop head: the prologue stores the saved registers in the frame
(region 2); the items are the entry's. -/
theorem entry_step {c : Cfg} {m m' : Machine} {lS : SState} (h : Pre c m)
    (hm : Match (env0 c m) lS m') (hso : SameOutside (InWritable (env0 c m) (S0 c)) m m')
    (hw : lS.mem = c.saved.map fun s => (⟨2, s.1, 8, .var s.2⟩ : Write))
    (hr : lS.regions.length = 3) (hsp : lS.reg 2 = .ptr 2 0) (hs0 : lS.reg 8 = .ptr 2 c.fs)
    (hkeep : keepsB lS c.kept = true) :
    Common c m m' ∧ Items m m' (items m (ptr m)) := by
  have hk := keeps_of hm (entryEnv_vars_lt _ _) hkeep
  have hb2 : (env0 c m).base 2 = frame c m := by simp [env0, entryEnv, Env.base, frame]
  have hmem : ∀ j < c.fs, m'.mem (frame c m + w j) = some (memByte (env0 c m) lS.mem 2 j) := by
    intro j hj
    rw [← hb2]; exact hm.mem 2 j (by omega) (by simpa [env0, entryEnv, Env.size] using hj)
  refine ⟨⟨fun a b hb => ?_, ?_, ?_, fun i hi => ?_, fun s hs t ht => ?_, fun j hj => ?_,
    fun a ha => ?_⟩, ?_⟩
  · rw [hso _ (fun hw => by obtain ⟨j, hj, he⟩ := inW_0 hw; exact rodata_ne_frame h hb hj he)]
    exact h.1 a b hb
  · rw [← hm.regs 2]; show Sym.eval _ (lS.reg 2) = _
    rw [hsp]; simp [Sym.eval, env0, entryEnv, Env.base, frame]
  · rw [← hm.regs 8]; show Sym.eval _ (lS.reg 8) = _
    rw [hs0]
    simp only [Sym.eval_ptr, env0, entryEnv, Env.base, List.getD_cons_succ, List.getD_cons_zero]
    exact s0_eval c _
  · exact hk i hi
  · have hle := c.saved_le s hs
    rw [hmem _ (by omega), hw, memByte_slot _ _ _ _ c.saved_disj hs ht]
    rfl
  · rw [hmem j hj]; rfl
  · apply hso
    intro hw'
    obtain ⟨j, hj, rfl⟩ := inW_0 hw'
    exact ha (in_frame h hj)
  · refine (slice_bytesOf h.2.2.2.2.2.2.2.2.2.2.2.1).keep fun e he o ho => hso _ fun hw' => ?_
    obtain ⟨j, hj, he'⟩ := inW_0 hw'
    exact slice_ne_frame h he ho hj he'

/-- The items of `m'` are `G` on `[0, bE)`: their window. -/
theorem win_items {m m' : Machine} {G : Nat → Nat → Byte} (hs : Items m m' G) {lo : Nat} :
    win (items m' (ptr m)) lo (bE m) = win G lo (bE m) :=
  win_congr fun e _ he => el_congr fun o ho => by
    simp only [items, bytesOf]; rw [hs e he o ho]; rfl

theorem pre_sorted {c : Cfg} {m : Machine} (h : Pre c m) :
    Sorted (c.key m) (X m) ∧ Sorted (c.key m) (Y m) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hx, hy, -⟩ := h
  exact ⟨hx, hy⟩

/-- `X ++ Y` is the whole range. -/
theorem xy_win {c : Cfg} {m : Machine} (h : Pre c m) :
    win (items m (ptr m)) (aS m) (bE m) = X m ++ Y m := by
  obtain ⟨h1, h2, h3⟩ := pre_runs h
  rw [win_split h1 (by omega)]; unfold X Y; rw [h2]

/-- A return before the prologue (`A` or `B` empty): memory untouched. -/
theorem early_post {c : Cfg} {m m' : Machine} {lS : SState} (h : Pre c m)
    (hm : Match (env0 c m) lS m') (hso : SameOutside (InWritable (env0 c m) (S0 c)) m m')
    (hpc : m'.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval (env0 c m))
    (hsp : lS.reg 2 = .ptr 2 c.fs) (hcs : keepsB lS ((calleeSaved.map (·.val)).erase 2) = true)
    (hAB : aS m = aE m ∨ bS m = bE m) : Post c m m' := by
  have hk := keeps_of hm (entryEnv_vars_lt _ _) hcs
  have hout : ∀ a, (∀ j < c.fs, a ≠ frame c m + w j) → m'.mem a = m.mem a :=
    fun a ha => hso a fun hw => by obtain ⟨j, hj, he⟩ := inW_0 hw; exact ha j hj he
  have hs : Items m m' (items m (ptr m)) :=
    (slice_bytesOf h.2.2.2.2.2.2.2.2.2.2.2.1).keep fun e he o ho =>
      hout _ fun j hj => slice_ne_frame h he ho hj
  refine ⟨⟨by rw [hpc]; rfl, fun i hi => ?_⟩, fun a ha => hout a fun j hj he => ha (he ▸ in_frame h hj), ?_⟩
  · by_cases h2 : i.val = 2
    · have : i = 2 := Fin.ext h2
      subst this
      rw [← hm.regs 2]; show Sym.eval _ (lS.reg 2) = _
      rw [hsp]; simp only [Sym.eval_ptr, env0, entryEnv, Env.base, List.getD_cons_succ,
        List.getD_cons_zero]
      exact s0_eval c _
    · have := hk i.val ((List.mem_erase_of_ne h2).mpr (List.mem_map.mpr ⟨i, hi, rfl⟩))
      simpa [Fin.ofNat, Nat.mod_eq_of_lt i.isLt] using this
  · rw [win_items hs, xy_win h]
    have hs := pre_sorted h
    have := inv_done (inv_init hs.1 hs.2) (by
      obtain ⟨h1, h2, h3⟩ := pre_runs h
      rcases hAB with e | e
      · left; exact win_nil (by omega)
      · right; exact win_nil (by omega))
    simpa using this

/-! ## The entry's loads of `A` and `B` -/

section
variable {c : Cfg} {m : Machine}

theorem env0_aS : (Sym.init 0 0 8).eval (env0 c m) = w (aS m) := by
  unfold aS u64; simp only [w, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
theorem env0_aE : (Sym.init 0 8 8).eval (env0 c m) = w (aE m) := by
  unfold aE u64; simp only [w, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
theorem env0_bS : (Sym.init 1 0 8).eval (env0 c m) = w (bS m) := by
  unfold bS u64; simp only [w, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
theorem env0_bE : (Sym.init 1 8 8).eval (env0 c m) = w (bE m) := by
  unfold bE u64; simp only [w, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl

theorem u64_lt (a : Word) (off : Nat) : u64 m a off < 2 ^ 64 := BitVec.isLt _

end

/-! ## The epilogue -/

theorem inW_E {c : Cfg} {m mh : Machine} {a : Word} (h : InWritable (envE c m mh) (SE c) a) :
    ∃ j < c.fs, a = frame c m + w j := by
  obtain ⟨r, R, j, hR, -, hj, rfl⟩ := h
  have hr : r = 0 := by
    rcases Nat.lt_or_ge r 1 with hc | hc
    · omega
    · simp [SE, entryState, List.getElem?_eq_none (show [frameR c.fs].length ≤ r by simp; omega)] at hR
  subst hr
  refine ⟨j, ?_, ?_⟩
  · simpa [envE, Env.setVars, entryEnv, Env.size] using hj
  · simp [envE, Env.setVars, entryEnv, Env.base]

/-- `Returns` registers of the epilogue's leaf: `sp` back, saved registers reloaded, kept ones
untouched. -/
def retRegsB (c : Cfg) (lS : SState) : Bool :=
  lS.reg 2 == .ptr 0 c.fs && calleeSaved.all fun i =>
    i.val == 2 || (c.saved.any (·.2 == i.val) && lS.reg i.val == .var (32 + i.val)) ||
      (c.kept.contains i.val && lS.reg i.val == .var i.val)

/-- The epilogue's return is `Post`. -/
theorem epi_post {c : Cfg} {m mh m' : Machine} {lS : SState} {G : Nat → Nat → Byte}
    (h : Pre c m) (hc : Common c m mh) (hs : Items m mh G)
    (hmg : MergeOf (c.key m) (X m) (Y m) (win G (aS m) (bE m)))
    (hm : Match (envE c m mh) lS m') (hso : SameOutside (InWritable (envE c m mh) (SE c)) mh m')
    (hpc : m'.pc = (Sym.bin .and (.var 33) (.lit 18446744073709551614)).eval (envE c m mh))
    (hregs : retRegsB c lS = true) : Post c m m' := by
  obtain ⟨-, h2, -, hkept, -, -, hout⟩ := hc
  have hv : ∀ i, 32 ≤ i → (envE c m mh).vars i = m.reg (Fin.ofNat 32 (i - 32)) := by
    intro i hi; simp [envE, Env.setVars, hi]
  simp only [retRegsB, Bool.and_eq_true, beq_iff_eq] at hregs
  obtain ⟨hsp, hcs⟩ := hregs
  have hs' : Items m m' G := hs.keep fun e he o ho => hso _ fun hw => by
    obtain ⟨j, hj, he'⟩ := inW_E hw
    exact slice_ne_frame h he ho hj he'
  refine ⟨⟨?_, fun i hi => ?_⟩, fun a ha => ?_, ?_⟩
  · rw [hpc]; simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
    rw [hv 33 (by omega)]; rfl
  · have := List.all_eq_true.mp hcs i hi
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
      List.contains_iff_mem] at this
    rw [← hm.regs i]
    have e : Fin.ofNat 32 i.val = i := Fin.ext (by simp [Fin.ofNat])
    rcases this with (h2' | ⟨-, he⟩) | ⟨hk, he⟩
    · have : i = 2 := Fin.ext h2'
      subst this
      show Sym.eval _ (lS.reg 2) = _
      rw [hsp]
      simp only [Sym.eval_ptr, envE, Env.setVars, entryEnv, Env.base, List.getD_cons_zero]
      unfold frame; rw [BitVec.ofInt_natCast]; exact BitVec.sub_add_cancel _ _
    · rw [he, Sym.eval_var, hv _ (by omega), show 32 + i.val - 32 = i.val by omega, e]
    · rw [he, Sym.eval_var, envE_vars c m mh _ i.isLt, e]
      have := hkept _ hk
      rw [e] at this
      exact this
  · rw [hso a fun hw => by
      obtain ⟨j, hj, rfl⟩ := inW_E hw
      exact ha (in_frame h hj)]
    exact hout a ha
  · rw [win_items hs']; exact hmg

/-! ## The byte comparison -/

theorem lex_prefix (f g : Nat → Byte) : ∀ k n, (∀ j < k, f j = g j) → k ≤ n →
    lexLt ((List.range' 0 n).map f) ((List.range' 0 n).map g) =
      lexLt ((List.range' k (n - k)).map f) ((List.range' k (n - k)).map g)
  | 0, n, _, _ => by simp
  | k + 1, n, hp, hk => by
    rw [lex_prefix f g k n (fun j hj => hp j (by omega)) (by omega),
      show n - k = (n - (k + 1)) + 1 by omega, lex_step, if_pos (hp k (by omega))]

/-- Elements equal on bytes `< k` and different at `k`: the byte decides. -/
theorem cmp_ne {F G : Nat → Nat → Byte} {e e' k : Nat} (hp : ∀ j < k, F e j = G e' j) (hk : k < 32)
    (hne : F e k ≠ G e' k) : lexLt (el F e) (el G e') = decide ((F e k).toNat < (G e' k).toNat) := by
  rw [el_range', el_range', lex_prefix _ _ k 32 hp (by omega),
    show 32 - k = (31 - k) + 1 by omega, lex_step, if_neg hne]

/-- Equal elements: not less. -/
theorem cmp_all {F G : Nat → Nat → Byte} {e e' : Nat} (h : ∀ j < 32, F e j = G e' j) :
    lexLt (el F e) (el G e') = false := by
  rw [el_eq h]; exact lexLt_irrefl _

theorem init1_eval (env : Env) (r off : Nat) :
    (Sym.init r off 1).eval env = w (env.byte0 r off).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [Sym.eval, byteList, ofBytesLE]

theorem byte_word_eq {a b : Byte} : w a.toNat = w b.toNat ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    apply BitVec.eq_of_toNat_eq
    have := a.isLt; have := b.isLt
    omega
  · rintro rfl; rfl

theorem byte_word_ult {a b : Byte} : (w a.toNat).ult (w b.toNat) = decide (a.toNat < b.toNat) := by
  have := a.isLt; have := b.isLt
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## Budgets -/

/-- Register `r` holds `v`, for every pair `(r, v)`. -/
def RegsAre (mh : Machine) : List (Nat × Word) → Prop
  | [] => True
  | (r, v) :: rest => mh.reg (Fin.ofNat 32 r) = v ∧ RegsAre mh rest

theorem RegsAre.get {mh : Machine} : ∀ {L : List (Nat × Word)}, RegsAre mh L →
    ∀ {r : Nat} {v : Word}, (r, v) ∈ L → mh.reg (Fin.ofNat 32 r) = v
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (r', v') :: L, ⟨h1, h2⟩, r, v, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h; exact h1
    · exact RegsAre.get h2 h

/-- Register `r` as a number. -/
def ix (mh : Machine) (r : Nat) : Nat := (mh.reg (Fin.ofNat 32 r)).toNat
/-- Register `a` minus register `b` as a number. -/
def dx (mh : Machine) (a b : Nat) : Nat := (mh.reg (Fin.ofNat 32 a) - mh.reg (Fin.ofNat 32 b)).toNat

/-- The rounds after the one starting at `as`, `R` steps each. -/
def Qf (be as R : Nat) : Nat := (be - as - 1) * R

theorem Qf_le {be as as' R : Nat} (h : as ≤ as') : Qf be as' R ≤ Qf be as R :=
  Nat.mul_le_mul_right _ (by omega)

theorem Qf_step {be as as' R : Nat} (h : as + 1 ≤ as') (h2 : as' < be) :
    Qf be as' R + R ≤ Qf be as R := by
  unfold Qf
  have := Nat.mul_le_mul_right R (show be - as' - 1 + 1 ≤ be - as - 1 by omega)
  rw [Nat.succ_mul] at this; exact this

theorem Qf_entry {be as : Nat} (h : be - as ≤ 16777216) :
    Qf be as (2000 * (be - as) + 400) + (2000 * (be - as) + 400) + 100 ≤ 4611686018427387904 := by
  unfold Qf
  have h1 := Nat.mul_le_mul (show be - as - 1 ≤ 16777216 by omega)
    (show 2000 * (be - as) + 400 ≤ 33554432400 by omega)
  simp only [Nat.reduceMul] at h1
  generalize (be - as - 1) * (2000 * (be - as) + 400) = X at h1 ⊢
  omega

theorem pre_bE {c : Cfg} {m : Machine} (h : Pre c m) : bE m ≤ 16777216 := by
  have := pre_items h; unfold Layout.ramLo Layout.ramHi at this; omega

/-! ## The rounds -/

section
variable {c : Cfg} {m : Machine} {G : Nat → Nat → Byte}

theorem round_init (h : Pre c m) : Round c m (items m (ptr m)) (aS m) (aE m) := by
  obtain ⟨h1, h2, h3⟩ := pre_runs h
  have hs := pre_sorted h
  refine ⟨Nat.le_refl _, h1, by omega, ?_⟩
  rw [win_nil (Nat.le_refl _), show win (items m (ptr m)) (aE m) (bE m) = Y m by unfold Y; rw [h2]]
  exact inv_init hs.1 hs.2

theorem round_sortedA {as ae : Nat} (hR : Round c m G as ae) : Sorted (c.key m) (win G as ae) :=
  hR.2.2.2.2.2.1

theorem round_sortedB {as ae : Nat} (hR : Round c m G as ae) : Sorted (c.key m) (win G ae (bE m)) :=
  hR.2.2.2.2.2.2.1

/-- One run empty: the merge is done. -/
theorem round_done {as ae : Nat} (hR : Round c m G as ae) (h : as = ae ∨ ae = bE m) :
    MergeOf (c.key m) (X m) (Y m) (win G (aS m) (bE m)) := by
  obtain ⟨h1, h2, h3, hinv⟩ := hR
  have := inv_done hinv (by
    rcases h with e | e
    · left; exact win_nil (by omega)
    · right; exact win_nil (by omega))
  rwa [← win_split h1 h2, ← win_split (by omega) h3] at this

theorem first_empty {key : List Byte → List Byte} {v : List Byte} {lo hi : Nat} (h : lo = hi) :
    First key G v lo hi hi 0 := by
  subst h; simpa using first_init (key := key) (G := G) (v := v) (Nat.le_refl lo)

/-- The three reversals of the rotation `[as, mid)` by `ae - as`. -/
def R3 (G : Nat → Nat → Byte) (as ae mid : Nat) : Nat → Nat → Byte :=
  rev as (mid - as) (rev ae (mid - ae) (rev as (ae - as) G))

theorem R3_rot {as ae mid : Nat} (h1 : as ≤ ae) (h2 : ae ≤ mid) :
    R3 G as ae mid = rot as (ae - as) (mid - as) G := by
  have := rev3_rot (lo := as) (a := ae - as) (n := mid - as) G (by omega)
  rwa [show as + (ae - as) = ae by omega, show mid - as - (ae - as) = mid - ae by omega] at this

/-- After `binaryFirst` and the rotation: `B`'s elements below `A[0]` joined the prefix. -/
theorem join_of_mid {as ae mid : Nat} (hM : MidR c m G as ae mid) :
    JoinR c m (R3 G as ae mid) (as + (mid - ae)) mid := by
  obtain ⟨⟨h1, h2, h3, hinv⟩, has, hf1, hf2, hf3, hf4⟩ := hM
  simp only [Nat.add_zero] at hf2 hf4
  rw [R3_rot h2 hf1]
  have hwr := win_rot (lo := as) (a := ae - as) (n := mid - as) G (by omega)
  rw [show as + (mid - as) = mid by omega, show as + (ae - as) = ae by omega] at hwr
  rw [win_split (show as ≤ as + (mid - ae) by omega) (show as + (mid - ae) ≤ mid by omega)] at hwr
  obtain ⟨hw1, hw2⟩ := List.append_inj hwr (by simp only [length_win]; omega)
  have hout1 : win (rot as (ae - as) (mid - as) G) (aS m) as = win G (aS m) as :=
    win_congr fun e _ he => el_rot_out G (by omega)
  have hout2 : win (rot as (ae - as) (mid - as) G) mid (bE m) = win G mid (bE m) :=
    win_congr fun e he _ => el_rot_out G (by omega)
  have ha0 : el (rot as (ae - as) (mid - as) G) (as + (mid - ae)) = el G as := el_eq fun o _ => by
    simp only [rot]; rw [if_pos (by omega)]
    congr 1
    rw [show as + (mid - ae) - as + (ae - as) = mid - as by omega, Nat.mod_self]; rfl
  rw [win_cons has, win_split hf1 hf2] at hinv
  have hB : ∀ b ∈ win G ae mid, ltBy (c.key m) b (el G as) = true := by
    intro b hb; obtain ⟨e, he1, he2, rfl⟩ := mem_win.mp hb; exact hf3 e he1 he2
  have hinv' := inv_first hinv hB
  rw [← win_cons has] at hinv'
  refine ⟨⟨by omega, by omega, hf2, ?_⟩, by omega, fun i hi1 hi2 => ?_⟩
  · rw [win_split (show aS m ≤ as by omega) (show as ≤ as + (mid - ae) by omega), hout1, hw1, hw2,
      hout2]
    exact hinv'
  · rw [ha0, el_rot_out G (by omega)]; exact hf4 i hi1 hi2

theorem last_curr {as ae curr : Nat} (hl : Last (c.key m) G (el G as) as ae curr 0) (has : as < ae) :
    as + 1 ≤ curr := by
  obtain ⟨h1, h2, -, h4⟩ := hl
  rcases Nat.lt_or_ge as curr with h | h
  · omega
  · have := h4 as (by omega) has
    rw [show ltBy (c.key m) (el G as) (el G as) = false from leBy_refl _] at this
    exact absurd this (by simp)

/-- After `binaryLast`: `A`'s elements not above `A[0]` joined the prefix. -/
theorem round_of_last {as ae curr : Nat} (hJ : JoinR c m G as ae)
    (hl : Last (c.key m) G (el G as) as ae curr 0) (hlt : ae < bE m) : Round c m G curr ae := by
  have hc := last_curr hl hJ.2.1
  obtain ⟨⟨h1, h2, h3, hinv⟩, has, hb⟩ := hJ
  obtain ⟨-, hl2, hl3, -⟩ := hl
  simp only [Nat.add_zero] at hl2
  rw [win_cons has, win_split (show as + 1 ≤ curr by omega) hl2, win_cons hlt] at hinv
  have := inv_last (A₁ := win G (as + 1) curr) hinv (fun a ha => by
    obtain ⟨e, he1, he2, rfl⟩ := mem_win.mp ha; exact hl3 e (by omega) he2) (hb ae (Nat.le_refl _) hlt)
  rw [← win_cons hlt, ← win_cons (show as < curr by omega), ← win_split (by omega) (by omega)] at this
  exact ⟨by omega, hl2, h3, this⟩

end

end ZesuExec.Fn.MergeInPlace

