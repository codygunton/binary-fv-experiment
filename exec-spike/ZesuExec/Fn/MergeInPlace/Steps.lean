import ZesuExec.Fn.MergeInPlace.Cuts

/-!
# `mergeInPlace` copies: what a leaf does to memory

* `step_none`: a run with no writable region (`SN`, `SC`) changes no memory.
* `step_copy`: a run from `SP` copies the element at its register into the frame at `d` and
  leaves the frame offsets `keep` (the saved registers, the other copy) alone — checked on the
  leaf's write list by `copyB` and `decide`.
* `step_swap`: a run from `SR` exchanges its two elements (`swapB`).
-/

namespace ZesuExec.Fn.MergeInPlace
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Machine ZesuExec.Fn.Rotate

theorem inW_entry {mh : Machine} {regs : List (Word × Nat)} {ov : Nat → Option Sym}
    {rs : List Region} {ks : List Write} {a : Word}
    (h : InWritable (entryEnv mh regs) (entryState ov rs ks) a) :
    ∃ k R j, rs[k]? = some R ∧ R.writable = true ∧ j < (regs.getD k (0, 0)).2 ∧
      a = (regs.getD k (0, 0)).1 + w j := by
  obtain ⟨k, R, j, hR, hw, hj, rfl⟩ := h
  exact ⟨k, R, j, by simpa [entryState] using hR, hw, by simpa [Env.size, entryEnv] using hj,
    by simp [Env.base, entryEnv]⟩

theorem mem_of_src {env : Env} {S : SState} {m' : Machine} (hm : Match env S m') {k j k' o : Nat}
    (hk : k < S.regions.length) (hj : j < env.size k) (h : memSrc S.mem k j = some (k', o)) :
    m'.mem (env.base k + w j) = some (env.byte0 k' o) := by
  rw [hm.mem k j hk hj, memSrc_sound h]

/-! ## No writable region -/

theorem step_none {c : Cfg} {m mh m' : Machine} {env : Env} {S lS : SState}
    (h : Pre c m) (hc : Common c m mh) (hnw : ∀ a, ¬ InWritable env S a)
    (hm : Match env lS m') (hv : ∀ i < 32, env.vars i = mh.reg (Fin.ofNat 32 i))
    (hso : SameOutside (InWritable env S) mh m')
    (hkeep : keepsB lS ([1, 2, 8] ++ c.kept) = true) :
    Common c m m' ∧ ∀ a, m'.mem a = mh.mem a := by
  have hall : ∀ a, m'.mem a = mh.mem a := fun a => hso a (hnw a)
  refine ⟨common_step h hc (fun a _ _ => hall a) (fun s _ t _ => hall _) (fun j hj => ?_)
    (keeps_of hm hv hkeep), hall⟩
  rw [hall]; exact hc.2.2.2.2.2.2.1 j hj

theorem nw_N {mh : Machine} {a : Word} : ¬ InWritable (envN mh) SN a := by
  intro h; obtain ⟨k, R, j, hR, -⟩ := inW_entry h; simp at hR

theorem nw_C {x y : Nat} {mh : Machine} {a : Word} : ¬ InWritable (envC x y mh) (SC x y) a := by
  intro h
  obtain ⟨k, R, j, hR, hw, -⟩ := inW_entry h
  rcases k with _ | _ | k
  · simp at hR; subst hR; simp [byteR] at hw
  · simp at hR; subst hR; simp [byteR] at hw
  · simp at hR

theorem items_keep {m mh m' : Machine} {G : Nat → Nat → Byte} (hs : Items m mh G)
    (hall : ∀ a, m'.mem a = mh.mem a) : Items m m' G :=
  hs.keep fun _ _ _ _ => hall _

/-! ## A copy into the frame -/

/-- Bytes `[d, d+32)` of region 0 come from region 1; the offsets `keep` are untouched. -/
def copyB (ws : List Write) (d : Nat) (keep : List Nat) : Bool :=
  (List.range 32).all (fun j => memSrc ws 0 (d + j) == some (1, j)) &&
    keep.all fun j => memSrc ws 0 j == some (0, j)

theorem inW_P {c : Cfg} {r : Nat} {extra : List (Nat × Sym)} {mh : Machine} {a : Word}
    (h : InWritable (envP c r mh) (SP c r extra) a) : ∃ j < c.fs, a = mh.reg 2 + w j := by
  obtain ⟨k, R, j, hR, hw, hj, rfl⟩ := inW_entry h
  rcases k with _ | _ | k
  · exact ⟨j, by simpa using hj, by simp⟩
  · simp at hR; subst hR; simp [elemR] at hw
  · simp at hR

theorem step_copy {c : Cfg} {m mh m' : Machine} {G : Nat → Nat → Byte} {r e d : Nat}
    {extra : List (Nat × Sym)} {lS : SState} {keep : List Nat}
    (h : Pre c m) (hc : Common c m mh) (hs : Items m mh G) (he : e < bE m)
    (hr : mh.reg (Fin.ofNat 32 r) = ptr m + w (32 * e))
    (hm : Match (envP c r mh) lS m') (hso : SameOutside (InWritable (envP c r mh) (SP c r extra)) mh m')
    (hlen : lS.regions.length = 2) (hd : d + 32 ≤ c.fs)
    (hsv : ∀ s ∈ c.saved, ∀ t < 8, s.1 + t ∈ keep) (hkl : ∀ j ∈ keep, j < c.fs)
    (hcp : copyB lS.mem d keep = true)
    (hkeep : keepsB lS ([1, 2, 8] ++ c.kept) = true) :
    Common c m m' ∧ Items m m' G ∧
      (∀ j < 32, m'.mem (frame c m + w (d + j)) = some (G e j)) ∧
      (∀ j ∈ keep, m'.mem (frame c m + w j) = mh.mem (frame c m + w j)) := by
  have h2 : mh.reg 2 = frame c m := hc.2.1
  simp only [copyB, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hcp
  obtain ⟨hcopy, hkp⟩ := hcp
  have hb0 : (envP c r mh).base 0 = frame c m := by simp [envP, entryEnv, Env.base, h2]
  have hpres := hc.2.2.2.2.2.2.1
  have hkeepm : ∀ j ∈ keep, m'.mem (frame c m + w j) = mh.mem (frame c m + w j) := by
    intro j hj
    have := mem_of_src hm (by omega) (by simpa [envP, entryEnv, Env.size] using hkl j hj) (hkp j hj)
    rw [hb0] at this; rw [this]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hpres j (hkl j hj))
    simp [envP, entryEnv, Env.byte0, h2, hb]
  have hout : ∀ a, (∀ j < c.fs, a ≠ frame c m + w j) → m'.mem a = mh.mem a := by
    intro a ha; apply hso; intro hw
    obtain ⟨j, hj, rfl⟩ := inW_P hw
    exact ha j hj (by rw [h2])
  refine ⟨common_step h hc (fun a ha _ => hout a ha) (fun s hs t ht => hkeepm _ (hsv s hs t ht))
    (fun j hj => ?_) (keeps_of hm (entryEnv_vars_lt _ _) hkeep), ?_, fun j hj => ?_, hkeepm⟩
  · have := hm.mem 0 j (by omega) (by simpa [envP, entryEnv, Env.size] using hj)
    rw [hb0] at this; rw [this]; rfl
  · exact hs.keep fun e' he' o ho => hout _ fun j hj => slice_ne_frame h he' ho hj
  · have := mem_of_src hm (by omega) (by simp [envP, entryEnv, Env.size]; omega) (hcopy j hj)
    rw [hb0] at this; rw [this]
    have hx := hs e he j hj
    simp only [envP, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero, hr]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hx]; rfl

/-! ## A swap of two elements -/

def swapB (ws : List Write) : Bool :=
  (List.range 32).all fun j => memSrc ws 0 j == some (1, j) && memSrc ws 1 j == some (0, j)

theorem inW_R {lo hi : Nat} {mh : Machine} {a : Word} (h : InWritable (envR lo hi mh) (SR lo hi) a) :
    ∃ j < 32, a = mh.reg (Fin.ofNat 32 lo) - w 15 + w j ∨ a = mh.reg (Fin.ofNat 32 hi) - w 16 + w j := by
  obtain ⟨k, R, j, hR, hw, hj, rfl⟩ := inW_entry h
  rcases k with _ | _ | k
  · exact ⟨j, by simpa using hj, .inl (by simp)⟩
  · exact ⟨j, by simpa using hj, .inr (by simp)⟩
  · simp at hR

/-- Elements `e₁ ≠ e₂` exchanged, nothing else changed. -/
theorem step_swap {c : Cfg} {m mh m' : Machine} {G : Nat → Nat → Byte} {lo hi e₁ e₂ : Nat}
    {lS : SState} (h : Pre c m) (hc : Common c m mh) (hs : Items m mh G)
    (h1 : aS m ≤ e₁) (h1' : e₁ < bE m) (h2 : aS m ≤ e₂) (h2' : e₂ < bE m) (hne : e₁ ≠ e₂)
    (hlo : mh.reg (Fin.ofNat 32 lo) = ptr m + w (32 * e₁ + 15))
    (hhi : mh.reg (Fin.ofNat 32 hi) = ptr m + w (32 * e₂ + 16))
    (hm : Match (envR lo hi mh) lS m') (hso : SameOutside (InWritable (envR lo hi mh) (SR lo hi)) mh m')
    (hlen : lS.regions.length = 2) (hsw : swapB lS.mem = true)
    (hkeep : keepsB lS ([1, 2, 8] ++ c.kept) = true) :
    Common c m m' ∧ Items m m' fun e o =>
      if e = e₁ then G e₂ o else if e = e₂ then G e₁ o else G e o := by
  have hfit := pre_hfit h
  have hb0 : (envR lo hi mh).base 0 = ptr m + w (32 * e₁) := by
    simp only [envR, entryEnv, Env.base, List.getD_cons_zero, hlo]
    apply BitVec.eq_of_toNat_eq
    have := elem_lt (E := 32) h1' (show 15 < 32 by omega)
    rw [BitVec.toNat_sub, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    simp; omega
  have hb1 : (envR lo hi mh).base 1 = ptr m + w (32 * e₂) := by
    simp only [envR, entryEnv, Env.base, List.getD_cons_succ, List.getD_cons_zero, hhi]
    apply BitVec.eq_of_toNat_eq
    have := elem_lt (E := 32) h2' (show 16 < 32 by omega)
    rw [BitVec.toNat_sub, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    simp; omega
  have hadd : ∀ e j, ptr m + w (32 * e) + w j = ptr m + w (32 * e + j) := by
    intro e j; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hb0r : mh.reg (Fin.ofNat 32 lo) - w 15 = ptr m + w (32 * e₁) := hb0
  have hb1r : mh.reg (Fin.ofNat 32 hi) - w 16 = ptr m + w (32 * e₂) := hb1
  simp only [swapB, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hsw
  have hw1 : ∀ j < 32, m'.mem (ptr m + w (32 * e₁ + j)) = some (G e₂ j) := by
    intro j hj
    have := mem_of_src hm (by omega) (by simp [envR, entryEnv, Env.size]; omega) (hsw j hj).1
    rw [hb0, hadd] at this; rw [this]
    simp only [Env.byte0]
    have hb1' : (envR lo hi mh).mem0 1 j = (mh.mem (ptr m + w (32 * e₂ + j))).getD 0 := by
      rw [← hadd, ← hb1]; rfl
    rw [hb1', hs e₂ h2' j hj]; rfl
  have hw2 : ∀ j < 32, m'.mem (ptr m + w (32 * e₂ + j)) = some (G e₁ j) := by
    intro j hj
    have := mem_of_src hm (by omega) (by simp [envR, entryEnv, Env.size]; omega) (hsw j hj).2
    rw [hb1, hadd] at this; rw [this]
    simp only [Env.byte0]
    have hb0' : (envR lo hi mh).mem0 0 j = (mh.mem (ptr m + w (32 * e₁ + j))).getD 0 := by
      rw [← hadd, ← hb0]; rfl
    rw [hb0', hs e₁ h1' j hj]; rfl
  have hout : ∀ a, (∀ j < 32, a ≠ ptr m + w (32 * e₁ + j)) → (∀ j < 32, a ≠ ptr m + w (32 * e₂ + j)) →
      m'.mem a = mh.mem a := by
    intro a ha1 ha2; apply hso; intro hw
    obtain ⟨j, hj, hq | hq⟩ := inW_R hw
    · apply ha1 j hj; rw [hq, hb0r, hadd]
    · apply ha2 j hj; rw [hq, hb1r, hadd]
  refine ⟨common_step h hc (fun a ha hi => hout a (fun j hj hq => hi ⟨e₁, j, h1, h1', hj, hq⟩)
      (fun j hj hq => hi ⟨e₂, j, h2, h2', hj, hq⟩))
    (fun s hs t ht => hout _ (fun j hj hq => slice_ne_frame h h1' hj (by have := c.saved_le s hs; omega) hq.symm)
      (fun j hj hq => slice_ne_frame h h2' hj (by have := c.saved_le s hs; omega) hq.symm))
    (fun j hj => by
      rw [hout _ (fun j' hj' hq => slice_ne_frame h h1' hj' hj hq.symm)
        (fun j' hj' hq => slice_ne_frame h h2' hj' hj hq.symm)]
      exact hc.2.2.2.2.2.2.1 j hj)
    (keeps_of hm (entryEnv_vars_lt _ _) hkeep), ?_⟩
  intro e he o ho
  dsimp only
  by_cases c1 : e = e₁
  · subst c1; rw [if_pos rfl]; exact hw1 o ho
  · rw [if_neg c1]
    by_cases c2 : e = e₂
    · subst c2; rw [if_pos rfl]; exact hw2 o ho
    · rw [if_neg c2, hout _ (fun j hj => addr_ne hfit he h1' ho hj (by omega))
        (fun j hj => addr_ne hfit he h2' ho hj (by omega))]
      exact hs e he o ho

end ZesuExec.Fn.MergeInPlace
