import ZesuExec.Fn.F2.Lemmas

namespace ZesuExec.Fn.F2
open ZesuExec ZesuExec.Sym ZesuExec.Machine

sym_run runE := run zesuImage [loopHead1, loopHead2] 100 entry S0
sym_run runL1 := run zesuImage [loopHead1, loopHead2] 100 loopHead1 SL
sym_run runL2 := run zesuImage [loopHead1, loopHead2] 100 loopHead2 SL

set_option linter.unusedSimpArgs false

set_option hygiene false in
/-- A word computed from the first input byte, as a `Nat` equation. -/
macro "f2_word" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [↓eval_and_sext_init, Sym.eval, BinOp.eval, hb0]
  simp [BitVec.toNat_and, BitVec.toNat_add, Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide : 256 < 2 ^ 64))]
  try simp only [land_255, land_127]
  omega))

set_option hygiene false in
/-- `decode` of the input under the leaf's facts on the first byte and the length. -/
macro "f2_decode" : tactic => `(tactic| (
  rw [input_cons m (by omega)]
  simp (disch := omega) only [decode, checkedPayload, if_pos, if_neg, List.length_drop,
    bytesOf_length]))

set_option hygiene false in
/-- The obligations of a return leaf: the first byte is in bounds, the return is aligned. -/
macro "f2_obligs" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Oblig.holds, hs1]
  first | exact hal1 | exact ⟨by simp [Sym.eval]; omega, hal1⟩))

def envE (m : Machine) : Env := entryEnv m ((shape m).map (·.1))

theorem f2_spec : Spec zesuImage entry bound Pre Post := by
  intro m hpc ⟨hro, ⟨hal, hlo, hhi, hfp⟩, hra, hrd, hinp, hwr, hal8, hout, hd1, hd2, hd3⟩
  have hsp : (m.reg 2 - 16).toNat = (m.reg 2).toNat - 16 := by
    have h16 : (16 : Word).toNat = 16 := rfl
    rw [BitVec.toNat_sub, h16]; unfold Layout.ramLo at hlo; omega
  have hwf : Env.WF (envE m) S0 := by
    refine entry_wf (shape m) ?_ ?_
    · simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl)
      · refine ⟨by simp [frameR], by simp [frameR]; omega, ?_⟩
        simp [frameR, Machine.writable, Machine.inRange]
        simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
      · exact ⟨by simp [inputR], by simp [inputR, Nat.mod_one], by simpa [inputR] using hrd⟩
      · exact ⟨by simp [outR], by simpa [outR] using hal8, by simpa [outR] using hwr⟩
    · unfold Fn.Disjoint at hd1 hd2 hd3
      simp only [hsp] at hd1 hd2 hd3
      simp only [shape, shapeOf, List.map_cons, List.map_nil, List.pairwise_cons,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, Fn.Disjoint, hsp]
      exact ⟨⟨by omega, by omega⟩, by omega, fun _ h => h.elim⟩
  have hm : Match (envE m) S0 m := by
    refine entry_match (fun i hi s hs => ?_) (fun r j hr hj => ?_) (by simp)
    · simp only [ov] at hs
      by_cases h2 : i.val = 2
      · simp only [h2, if_true, Option.some.injEq] at hs
        subst hs
        have : i = 2 := Fin.ext h2
        subst this
        simp [Sym.eval, Env.base, entryEnv, shape, shapeOf, BitVec.sub_add_cancel]
      by_cases h11 : i.val = 11
      · simp [h11] at hs
        subst hs
        have : i = 11 := Fin.ext h11
        subst this
        simp [Sym.eval, Env.base, entryEnv, shape, shapeOf]
      by_cases h10 : i.val = 10
      · simp [h10] at hs
        subst hs
        have : i = 10 := Fin.ext h10
        subst this
        simp [Sym.eval, Env.base, entryEnv, shape, shapeOf]
      simp [h2, h11, h10] at hs
    · simp only [regionsR, List.length_cons, List.length_nil] at hr
      have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      rcases hr3 with rfl | rfl | rfl
      · exact hfp j (by simpa [Env.size, entryEnv, shape, shapeOf] using hj)
      · exact hinp j (by simpa [Env.size, entryEnv, shape, shapeOf] using hj)
      · exact hout j (by simpa [Env.size, entryEnv, shape, shapeOf] using hj)
  have hfit : ∀ p ∈ shape m, p.1.1.toNat + p.1.2 < 2 ^ 64 := by
    simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false]
    simp [Machine.readable, Machine.writable, Machine.inRange, Layout.rodataLo, Layout.rodataHi,
      Layout.inputLo, Layout.inputHi, Layout.ramLo, Layout.ramHi] at hrd hwr hhi
    rintro p (rfl | rfl | rfl) <;> simp <;> omega
  have hso : ∀ m', SameOutside (InWritable (envE m) S0) m m' →
      SameOutside (fun a => InRange (m.reg 10) 40 a ∨ InRange (m.reg 2 - 16) 16 a) m m' := by
    intro m' hfr
    refine SameOutside.mono hfr fun a ha => ?_
    obtain ⟨p, hp, hw, hin⟩ := inWritable_entry (shape := shape m) ha hfit
    simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact .inr hin
    · simp [inputR] at hw
    · exact .inl hin
  have hvE : ∀ i : Fin 32, i.val ∈ [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
      (envE m).vars i.val = m.reg i := fun i _ => entryEnv_var m _ i
  have hbE : ∀ j < 40, (envE m).byte0 2 j = (bytesOf m (m.reg 10) 40).getD j 0 := fun j hj => by
    rw [bytesOf_getD _ _ _ _ hj]; rfl
  have hb0 : (envE m).byte0 1 0 = firstByte m := by
    simp [envE, entryEnv, Env.byte0, shape, shapeOf, firstByte]
  have hv12 : (envE m).vars 12 = m.reg 12 := rfl
  have hv1 : (envE m).vars 1 = m.reg 1 := rfl
  have hsp2 : (envE m).base 0 + BitVec.ofInt 64 16 = m.reg 2 := by
    simp [Env.base, envE, entryEnv, shape, shapeOf, BitVec.sub_add_cancel]
  have hret : ∀ m' (l : SState), Match (envE m) l m' →
      m'.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval (envE m) →
      savedOK l (.var 8) = true → Returns m m' := fun m' l hm' hpc hok =>
    returns_of hm' hpc hv1 hok hsp2 rfl hvE
  have hal1 : ((Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval (envE m)).toNat % 4 = 0 := by
    simpa [Sym.eval, BinOp.eval, notOne] using hra
  have hx : (firstByte m).toNat < 256 := (firstByte m).isLt
  have hs1 : (envE m).size 1 = (m.reg 12).toNat := rfl
  have hb2 : (envE m).base 2 = m.reg 10 := by simp [envE, entryEnv, Env.base, shape, shapeOf]
  have hs2 : (envE m).size 2 = 40 := rfl
  have hp1 : ∀ k : Nat, (Sym.ptr 1 k).eval (envE m) = m.reg 11 + BitVec.ofNat 64 k := fun k => by
    simp [Sym.eval, envE, entryEnv, Env.base, shape, shapeOf]
  have hlen : ∀ (l : SState), l.regions = regionsR → l.regions.length = 3 := fun l h => by
    rw [h]; rfl
  refine run_reaches runE hwf hm hpc hro fun l hl hc => ?_
  simp only [runE_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc
    simp only [SBool.eval] at hc
    try simp only [eval_and_sext_init, eval_sext_init] at hc
    simp only [Sym.eval, BinOp.eval, sext_and_255, sext_slt_zero, ofBytes1, hb0, hv12] at hc
    simp [BitVec.ult, bne, BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_eq,
      Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide : 256 < 2 ^ 64))] at hc
    try simp only [land_255, land_127] at hc
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by
      rw [hc]; rfl
    exact post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_err hm' rfl hb2 hs2 (by decide) hdec)
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by f2_decode
    exact post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_err hm' rfl hb2 hs2 (by decide) hdec)
  case _ => sorry
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by f2_decode
    exact post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_err hm' rfl hb2 hs2 (by decide) hdec)
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .success true 1 ((firstByte m).toNat - 192) := by f2_decode
    refine post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_succ (p := (.ptr 1 1)) (l := (.bin .and (.bin .add (.bin .and (.sext 8 (.init 1 0 1)) (.lit 255)) (.lit 64)) (.lit 255))) (f := (.lit 1)) (c := (.bin .add (.bin .and (.bin .add (.bin .and (.sext 8 (.init 1 0 1)) (.lit 255)) (.lit 64)) (.lit 255)) (.lit 1))) hm' rfl hb2 hs2
        (by decide) (by simp [Sym.eval]) hbE hdec ?_ (by f2_word) (by f2_word))
    rw [input_head m (by omega)]
    have : firstByte m ≠ 128 := fun h => by rw [h] at hc; simp at hc
    simp [Sym.eval, envE, entryEnv, Env.base, shape, shapeOf]
    exact fun h => absurd h this
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by f2_decode
    exact post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_err hm' rfl hb2 hs2 (by decide) hdec)
  case _ => sorry
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by f2_decode
    exact post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_err hm' rfl hb2 hs2 (by decide) hdec)
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .success false 1 ((firstByte m).toNat - 128) := by f2_decode
    refine post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_succ (p := (.ptr 1 1)) (l := (.bin .and (.bin .and (.sext 8 (.init 1 0 1)) (.lit 255)) (.lit 127))) (f := (.lit 0)) (c := (.bin .add (.bin .and (.bin .and (.sext 8 (.init 1 0 1)) (.lit 255)) (.lit 127)) (.lit 1))) hm' rfl hb2 hs2
        (by decide) (by simp [Sym.eval]) hbE hdec ?_ (by f2_word) (by f2_word))
    rw [input_head m (by omega)]
    have : firstByte m ≠ 128 := fun h => by rw [h] at hc; simp at hc
    simp [Sym.eval, envE, entryEnv, Env.base, shape, shapeOf]
    exact fun h => absurd h this
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .success false 1 0 := by f2_decode
    refine post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_succ (p := (.lit 1)) (l := (.lit 0)) (f := (.lit 0)) (c := (.lit 1)) hm' rfl hb2 hs2
        (by decide) (by simp [Sym.eval]) hbE hdec ?_ (by f2_word) (by f2_word))
    rw [input_head m (by omega)]
    have : firstByte m = 128 := BitVec.eq_of_toNat_eq (by simp; omega)
    simp [this, Sym.eval]
  case _ =>
    obtain ⟨hl0, hx1⟩ := hc
    refine ⟨?_, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Oblig.holds, hs1]
      exact ⟨by simp [Sym.eval]; omega, hal1⟩
    · have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .success false 0 1 := by
        rw [input_cons m (by omega)]
        simp (disch := omega) only [decode, checkedPayload, if_pos, if_neg]
      refine post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
        (bytes_succ (p := .ptr 1 0) (l := .lit 1) (f := .lit 0) (c := .lit 1) hm' rfl hb2 hs2
          (by decide) (by simp [Sym.eval]) hbE hdec ?_ rfl rfl)
      rw [input_head m (by omega)]
      have : firstByte m ≠ 128 := fun h => by rw [h] at hx1; simp at hx1
      simp [Sym.eval, envE, entryEnv, Env.base, shape, shapeOf]
      exact fun h => absurd h this
