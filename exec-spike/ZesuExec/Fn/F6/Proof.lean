import ZesuExec.Fn.F6.Lemmas
import ZesuExec.Fn.F6.Runs

/-!
# F6 proof: `f6_spec : Spec zesuImage 0x800d5cb8 2178 Pre Post`

One theorem per cut, from the last return point back to the entry: `after18` .. `after9`, the
loops `loop9` .. `loop11`, the skip fields `skip_step` (fields 0..7) and `after8`, the outer item
`after0`, the entry `f6_spec`. Each takes the machine-level state at its cut (`DSt`/`NSt` plus
registers, frame words and the walk position) and runs its `sym_run` from a fresh symbolic state.
-/

namespace ZesuExec.Fn.F6
open ZesuExec ZesuExec.Sym ZesuExec.Machine

set_option linter.unusedSimpArgs false

/-! ## Helpers -/

/-- The loop variable at cuts that are not loop heads. -/
def c0 : Word := 0

/-- The 8 frame bytes at `off` hold `v`. -/
def FW (m mh : Machine) (off v : Nat) : Prop :=
  ∀ t < 8, mh.mem (frB m + BitVec.ofNat 64 (off + t)) = some (byteOf (BitVec.ofNat 64 v) t)

/-- The words a success leaf stores into the result. -/
def wsOf (lS : SState) : List Sym :=
  (List.range 9).map fun q => ((F2.wview lS.mem 1 (8 * q)).map (·.1)).getD (.lit 0)

/-- A tag word stored as `cat (bytes 1) _ 1` (the tag byte stored and read back in one run). -/
def tag1 : Sym → Bool
  | .cat (.bytes (.lit 1) 0 1) _ 1 => true
  | _ => false

/-- `succ_exit` with the words read off the leaf. -/
theorem succ_exit' {m mh mf : Machine} (n : Nums m) (hc : Fr m mh) {c : Word}
    {x : Nat → Option Sym} {lS : SState} (hm' : Match (envC m mh c) lS mf)
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh mf)
    (hex : mf.pc = retT.eval (envC m mh c)) (hk : succOK lS (wsOf lS) = true)
    {vals : List Nat} (hw : walk (inputOf m) = some vals)
    (h0 : ((wsOf lS).getD 0 (.lit 0)).eval (envC m mh c) = BitVec.ofNat 64 (vals.getD 0 0))
    (h1 : ((wsOf lS).getD 1 (.lit 0)).eval (envC m mh c) = BitVec.ofNat 64 (vals.getD 1 0))
    (h2 : ((wsOf lS).getD 2 (.lit 0)).eval (envC m mh c) = BitVec.ofNat 64 (vals.getD 2 0))
    (h3 : OptSym (envC m mh c) ((wsOf lS).getD 3 (.lit 0)) ((wsOf lS).getD 4 (.lit 0)) vals[3]?)
    (h4 : OptSym (envC m mh c) ((wsOf lS).getD 5 (.lit 0)) ((wsOf lS).getD 6 (.lit 0)) vals[4]?)
    (h5 : OptSym (envC m mh c) ((wsOf lS).getD 7 (.lit 0)) ((wsOf lS).getD 8 (.lit 0)) vals[5]?) :
    Post m mf :=
  succ_exit n hc hm' hfr hex hk hw h0 h1 h2 h3 h4 h5

theorem tag1_eval {s : Sym} (h : tag1 s = true) (env : Env) : byteOf (s.eval env) 0 = 1 := by
  match s, h with
  | .cat (.bytes (.lit 1) 0 1) hi 1, _ =>
    simp only [Sym.eval]
    rw [byteOf_cat1]
    decide

theorem fw_eval {m mh : Machine} {c : Word} {off v : Nat} (h : FW m mh off v) :
    (Sym.init 0 off 8).eval (envC m mh c) = BitVec.ofNat 64 v :=
  init_word fun t ht => byte0_of (h t ht)

theorem tag_eval {m mh : Machine} {c : Word} {off : Nat}
    (h : mh.mem (frB m + BitVec.ofNat 64 off) = some 1) :
    byteOf ((Sym.init 0 off 8).eval (envC m mh c)) 0 = 1 := by
  rw [byteOf_init (by decide) (by decide)]; exact byte0_of h

theorem var_eval {m mh : Machine} {c : Word} (i : Fin 32) :
    (Sym.var i.val).eval (envC m mh c) = mh.reg i := (envC_facts m mh c).v i

theorem nout_of {m mh : Machine} {c : Word} {roff o r : Nat} (hs : NSt m mh roff o r) :
    NOut (envC m mh c) roff (sl m o r) := by
  obtain ⟨old, h⟩ := hs.res
  exact ⟨old, fun j hj => byte0_of (h j hj)⟩

/-- `fieldWalk` at an integer field is nextUint64's case split. -/
theorem fw_next {k : Kind} {later : List Kind} {rem : List Byte} {vals : List Nat} (hne : rem ≠ [])
    (hk : k.isInt = true) :
    fieldWalk (k :: later) rem vals = match F3.nextUint64 rem with
      | none => none
      | some (v, c) => fieldWalk later (rem.drop (c % 2 ^ 64)) (vals ++ [v.toNat]) := by
  cases hd : F2.decode rem with
  | error =>
    rw [fw_err hne hd]; simp [F3.nextUint64, hd]
  | success b h p =>
    rw [fw_ok hne hd, hk, if_pos rfl]
    simp only [F3.nextUint64, hd]
    cases b
    · dsimp only
      by_cases hp : p ≤ 8
      · rw [if_neg (by simp; omega), if_pos hp]
        have := F3.bigEndian_lt8 (l := (rem.drop h).take p) (by simp; omega)
        simp [Nat.mod_eq_of_lt this]
      · rw [if_pos (by simp; omega), if_neg hp]
    · simp

theorem xN_ok {m mh : Machine} {c : Word} : ∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 8 → i.val ≠ 9 →
    ∀ s, xN i.val = some s → s.eval (envC m mh c) = mh.reg i := by
  intro i _ _ _ s hs; simp [xN] at hs

theorem x18_ok {m mh : Machine} {c : Word} (r23 : mh.reg 23 = BitVec.ofNat 64 noneConst)
    (r24 : mh.reg 24 = frB m + BitVec.ofNat 64 160) (r18 : mh.reg 18 = frB m + BitVec.ofNat 64 232) :
    ∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 8 → i.val ≠ 9 →
    ∀ s, x18 i.val = some s → s.eval (envC m mh c) = mh.reg i := by
  have ef := envC_facts m mh c
  intro i _ _ _ s hs
  simp only [x18] at hs
  by_cases h23 : i.val = 23
  · simp only [h23, if_true, Option.some.injEq] at hs; subst hs
    rw [show i = 23 from Fin.ext h23, r23]; rfl
  by_cases h24 : i.val = 24
  · simp only [h24, if_true, Option.some.injEq] at hs; simp at hs; subst hs
    rw [show i = 24 from Fin.ext h24, r24]; simp [Sym.eval, ef.b0]
  by_cases h18 : i.val = 18
  · simp only [h18, if_true, Option.some.injEq] at hs; simp at hs; subst hs
    rw [show i = 18 from Fin.ext h18, r18]; simp [Sym.eval, ef.b0]
  simp [h23, h24, h18] at hs

theorem x16_ok {m mh : Machine} {c : Word} (r23 : mh.reg 23 = BitVec.ofNat 64 noneConst)
    (r24 : mh.reg 24 = frB m + BitVec.ofNat 64 160) :
    ∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 8 → i.val ≠ 9 →
    ∀ s, x16 i.val = some s → s.eval (envC m mh c) = mh.reg i := by
  have ef := envC_facts m mh c
  intro i _ _ _ s hs
  simp only [x16] at hs
  by_cases h23 : i.val = 23
  · simp only [h23, if_true, Option.some.injEq] at hs; subst hs
    rw [show i = 23 from Fin.ext h23, r23]; rfl
  by_cases h24 : i.val = 24
  · simp only [h24, if_true, Option.some.injEq] at hs; simp at hs; subst hs
    rw [show i = 24 from Fin.ext h24, r24]; simp [Sym.eval, ef.b0]
  simp [h23, h24] at hs

theorem x15_ok {m mh : Machine} {c : Word} (r23 : mh.reg 23 = BitVec.ofNat 64 noneConst) :
    ∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 8 → i.val ≠ 9 →
    ∀ s, x15 i.val = some s → s.eval (envC m mh c) = mh.reg i := by
  intro i _ _ _ s hs
  simp only [x15] at hs
  by_cases h23 : i.val = 23
  · simp only [h23, if_true, Option.some.injEq] at hs; subst hs
    rw [show i = 23 from Fin.ext h23, r23]; rfl
  simp [h23] at hs

set_option hygiene false in
/-- A leaf's conditions as hypotheses. -/
macro "conds" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    SBool.eval] at hcs))

/-! ## Field 18 (`0x800d6254`, after the third nextUint64) -/

theorem after18 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r v0 v1 v2 v3 v4 : Nat}
    (hs : NSt m mh 248 o r) (hpc : mh.pc.toNat = ret18)
    (r23 : mh.reg 23 = BitVec.ofNat 64 noneConst) (r24 : mh.reg 24 = frB m + BitVec.ofNat 64 160)
    (r18 : mh.reg 18 = frB m + BitVec.ofNat 64 232)
    (r21 : mh.reg 21 = BitVec.ofNat 64 v0) (r22 : mh.reg 22 = BitVec.ofNat 64 v1)
    (r20 : mh.reg 20 = BitVec.ofNat 64 v2)
    (w160 : FW m mh 160 v3) (t168 : mh.mem (frB m + BitVec.ofNat 64 168) = some 1)
    (w232 : FW m mh 232 v4) (t240 : mh.mem (frB m + BitVec.ofNat 64 240) = some 1)
    (hr : 0 < r) (hw : walk (inputOf m) = fieldWalk [.optInt] (sl m o r) [v0, v1, v2, v3, v4]) :
    Reaches zesuImage 37 (Post m) mh := by
  have hN := nout_of (c := c0) hs
  have hne : sl m o r ≠ [] := fun h => by rw [sl_nil hs.fit] at h; omega
  rw [fw_next hne rfl] at hw
  refine cut_reaches (c := c0) n e hs.fr run18 (x18_ok r23 r24 r18) hpc fun l hl hcs => ?_
  simp only [run18_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · conds
    cases hn : F3.nextUint64 (sl m o r) with
    | some vc =>
      obtain ⟨v, c⟩ := vc
      exfalso; simp [(nout_ok hN hn).1, Sym.eval_lit] at hcs
    | none =>
      rw [hn] at hw
      refine ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr => ?_⟩
      exact Reaches.done (err_exit n hs.fr hm' hfr hex (by decide) (by decide) (by decide)
        (nout_err hN hn) hw)
  · cases hn : F3.nextUint64 (sl m o r) with
    | none => conds; exfalso; simp [nout_err hN hn, Sym.eval_lit] at hcs
    | some vc =>
      obtain ⟨v, c⟩ := vc
      rw [hn] at hw
      simp only [fieldWalk] at hw
      have ho := nout_ok hN hn
      refine ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr => ?_⟩
      refine Reaches.done (succ_exit' n hs.fr hm' hfr hex (by decide) hw ?_ ?_ ?_ ?_ ?_ ?_)
      · exact (var_eval 21).trans r21
      · exact (var_eval 22).trans r22
      · exact (var_eval 20).trans r20
      · exact ⟨tag_eval t168, fun k hk => by cases hk; exact fw_eval w160⟩
      · exact ⟨tag_eval t240, fun k hk => by cases hk; exact fw_eval w232⟩
      · refine ⟨tag1_eval (by decide) _, fun k hk => ?_⟩
        cases hk
        show (Sym.init 0 248 8).eval _ = _
        rw [ho.2]; simp

theorem opt_none {env : Env} {vs ts : Sym} (h : ts = .lit 0) : OptSym env vs ts none := by
  subst h; exact ⟨by simp [Sym.eval], fun k hk => by cases hk⟩

/-! ## Frame bytes across a leaf and a call -/

theorem mb_none {env : Env} {ws : List Write} {r j : Nat} (h : F2.wview ws r j = none) :
    memByte env ws r j = env.byte0 r j := by
  rw [F2.memByte_wview, h]

theorem mb_some {env : Env} {ws : List Write} {r j k : Nat} {v : Sym}
    (h : F2.wview ws r j = some (v, k)) : memByte env ws r j = byteOf (v.eval env) k := by
  rw [F2.memByte_wview, h]

/-- A frame word the leaf did not write survives into `m2`. -/
theorem fw_keep {m mh m2 : Machine} {c : Word} {ws : List Write} {off v : Nat}
    (hm2 : ∀ t < 8, m2.mem (frB m + BitVec.ofNat 64 (off + t)) =
      some (memByte (envC m mh c) ws 0 (off + t)))
    (hnw : ∀ t < 8, F2.wview ws 0 (off + t) = none) (h : FW m mh off v) : FW m m2 off v := by
  intro t ht
  rw [hm2 t ht, mb_none (hnw t ht), (envC_facts m mh c).by0, (envC_facts m mh c).b0, h t ht]; rfl

theorem tag_keep {m mh m2 : Machine} {c : Word} {ws : List Write} {off : Nat}
    (hm2 : m2.mem (frB m + BitVec.ofNat 64 off) = some (memByte (envC m mh c) ws 0 off))
    (hnw : F2.wview ws 0 off = none) (h : mh.mem (frB m + BitVec.ofNat 64 off) = some 1) :
    m2.mem (frB m + BitVec.ofNat 64 off) = some 1 := by
  rw [hm2, mb_none hnw, (envC_facts m mh c).by0, (envC_facts m mh c).b0, h]; rfl

/-- A frame word the leaf wrote. -/
theorem fw_write {m mh m2 : Machine} {c : Word} {ws : List Write} {off v : Nat} {s : Sym}
    (hm2 : ∀ t < 8, m2.mem (frB m + BitVec.ofNat 64 (off + t)) =
      some (memByte (envC m mh c) ws 0 (off + t)))
    (hw : ∀ t < 8, F2.wview ws 0 (off + t) = some (s, t))
    (hs : s.eval (envC m mh c) = BitVec.ofNat 64 v) : FW m m2 off v := by
  intro t ht
  rw [hm2 t ht, mb_some (hw t ht), hs]

theorem tag_write {m mh m2 : Machine} {c : Word} {ws : List Write} {off : Nat}
    (hm2 : m2.mem (frB m + BitVec.ofNat 64 off) = some (memByte (envC m mh c) ws 0 off))
    (hw : F2.wview ws 0 off = some (.lit 1, 0)) :
    m2.mem (frB m + BitVec.ofNat 64 off) = some 1 := by
  rw [hm2, mb_some hw]; rfl

/-- nextUint64's success: the consumed length fits the slice. -/
theorem next_le {rem : List Byte} {v : Word} {c : Nat} (hn : F3.nextUint64 rem = some (v, c)) :
    c % 2 ^ 64 ≤ rem.length := by
  unfold F3.nextUint64 at hn
  split at hn
  · next b h p hd =>
    split at hn
    · cases hn; exact (F3.decode_success hd).2.1
    · cases hn
  · cases hn

theorem reg_eval {m mh mf : Machine} {c : Word} {lS : SState} (hm' : Match (envC m mh c) lS mf)
    (i : Fin 32) : mf.reg i = (lS.reg i.val).eval (envC m mh c) := (hm'.regs i).symm

/-! ## Field 17 (`0x800d6220`, after the second nextUint64) -/

theorem after17 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r v0 v1 v2 v3 : Nat}
    (hs : NSt m mh 216 o r) (hpc : mh.pc.toNat = ret17)
    (r23 : mh.reg 23 = BitVec.ofNat 64 noneConst) (r24 : mh.reg 24 = frB m + BitVec.ofNat 64 160)
    (r21 : mh.reg 21 = BitVec.ofNat 64 v0) (r22 : mh.reg 22 = BitVec.ofNat 64 v1)
    (r20 : mh.reg 20 = BitVec.ofNat 64 v2)
    (w160 : FW m mh 160 v3) (t168 : mh.mem (frB m + BitVec.ofNat 64 168) = some 1)
    (hr : 0 < r) (hw : walk (inputOf m) = fieldWalk [.optInt, .optInt] (sl m o r) [v0, v1, v2, v3]) :
    Reaches zesuImage (13 + 160 + 37) (Post m) mh := by
  have hN := nout_of (c := c0) hs
  have ef := envC_facts m mh c0
  obtain ⟨old, hslc⟩ := hs.slc
  have hS : SOut (envC m mh c0) (m.reg 11 + BitVec.ofNat 64 o) (BitVec.ofNat 64 r) (sl m o r) :=
    ⟨old, fun j hj => byte0_of (hslc j hj)⟩
  have hne : sl m o r ≠ [] := fun h => by rw [sl_nil hs.fit] at h; omega
  have hr64 : r < 2 ^ 64 := by have := hs.fit; have := n.inHi; unfold Layout.inputHi at this; omega
  rw [fw_next hne rfl] at hw
  refine cut_reaches (c := c0) n e hs.fr run17 (x16_ok r23 r24) hpc fun l hl hcs => ?_
  simp only [run17_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · conds
    cases hn : F3.nextUint64 (sl m o r) with
    | some vc =>
      obtain ⟨v, c⟩ := vc
      exfalso; simp [(nout_ok hN hn).1, Sym.eval_lit] at hcs
    | none =>
      rw [hn] at hw
      refine ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr => ?_⟩
      exact Reaches.done (err_exit n hs.fr hm' hfr hex (by decide) (by decide) (by decide)
        (nout_err hN hn) hw)
  all_goals
    conds
    obtain ⟨v, c, hn⟩ : ∃ v c, F3.nextUint64 (sl m o r) = some (v, c) := by
      cases hn : F3.nextUint64 (sl m o r) with
      | none => exfalso; simp [nout_err hN hn, Sym.eval_lit] at hcs
      | some vc => exact ⟨vc.1, vc.2, rfl⟩
    simp only [hn] at hw
    have ho := nout_ok hN hn
    have hso := sout_ok hS hn
    have hc := next_le hn
    rw [sl_length m hs.fit] at hc
    rw [sl_drop] at hw
    obtain ⟨-, h56⟩ := hcs
    rw [hso.2, adv_len hr64 hc] at h56
  · -- success: nothing left after field 17
    simp only [Sym.eval_lit, beq_iff_eq] at h56
    have hr0 : r - c % 2 ^ 64 = 0 := by
      have := (len_eq (r := r - c % 2 ^ 64) (x := 0) (by omega)).mp h56; simpa using this
    rw [hr0, (sl_nil (by have := hs.fit; omega)).mpr rfl] at hw
    simp only [fw_nil, Kind.required, Bool.false_eq_true, if_false] at hw
    refine ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr => ?_⟩
    refine Reaches.done (succ_exit' n hs.fr hm' hfr hex (by decide) hw ?_ ?_ ?_ ?_ ?_ ?_)
    · exact (var_eval 21).trans r21
    · exact (var_eval 22).trans r22
    · exact (var_eval 20).trans r20
    · exact ⟨tag_eval t168, fun k hk => by cases hk; exact fw_eval w160⟩
    · refine ⟨tag1_eval (by decide) _, fun k hk => ?_⟩
      cases hk
      show (Sym.init 0 216 8).eval _ = _
      rw [ho.2]; simp
    · exact opt_none rfl
  · -- the third nextUint64
    simp only [Sym.eval_lit, bne_iff_ne, ne_eq] at h56
    have hr0 : r - c % 2 ^ 64 ≠ 0 := fun h0 => h56 (by rw [h0])
    refine ⟨by simp, by decide, fun m1 hm1 hex hfr => ?_⟩
    refine (call_n (B := 37) n e hs.fr hm1 hfr (by decide) hex (roff := 248) (o := o + c % 2 ^ 64)
      (r := r - c % 2 ^ 64) (ret := ret18) (by decide) (by decide) (by decide)
      (by have := hs.fit; omega) rfl (by decide) (by decide) rfl rfl
      (fun t ht => ?_) (fun t ht => ?_) fun m2 hs2 hpc2 hregs hmem => ?_).mono
      (by decide) fun _ h => h
    · rw [mb_none (by revert t; decide), byte0_of (hslc t (by omega))]
      simp only [F3.sliceByte, hn, if_pos ht]
      rw [adv_ptr]
    · rw [mb_none (by revert t; decide), show 56 + t = 48 + (8 + t) by omega,
        byte0_of (hslc (8 + t) (by omega))]
      simp only [F3.sliceByte, hn, if_neg (show ¬ 8 + t < 8 by omega)]
      rw [show 8 + t - 8 = t by omega, adv_len hr64 hc]
    refine after18 n e hs2 hpc2 ?_ ?_ ?_ ?_ ?_ ?_ (fw_keep (fun t ht => hmem _ (by omega) (by omega))
      (by decide) w160) (tag_keep (hmem _ (by decide) (by decide)) (by decide) t168)
      (fw_write (s := .init 0 216 8) (fun t ht => hmem _ (by omega) (by omega)) (by decide)
        (ho.2.trans (by simp)))
      (tag_write (hmem _ (by decide) (by decide)) (by decide)) (by omega) hw
    · rw [hregs 23 (by decide)]; rfl
    · rw [hregs 24 (by decide)]; show (Sym.ptr 0 160).eval _ = _; simp [Sym.eval, ef.b0]
    · rw [hregs 18 (by decide)]; show (Sym.ptr 0 232).eval _ = _; simp [Sym.eval, ef.b0]
    · rw [hregs 21 (by decide)]; exact (var_eval 21).trans r21
    · rw [hregs 22 (by decide)]; exact (var_eval 22).trans r22
    · rw [hregs 20 (by decide)]; exact (var_eval 20).trans r20

/-! ## Field 16 (`0x800d619c`, the optional skip after the base fee) -/

theorem cond_len {r x : Nat} (hr : r < 2 ^ 64)
    (h : (BitVec.ofNat 64 r == BitVec.ofNat 64 x) = true) : r = x % 2 ^ 64 :=
  (len_eq hr).mp (by simpa using h)

theorem cond_len' {r x : Nat} (hr : r < 2 ^ 64)
    (h : (BitVec.ofNat 64 r != BitVec.ofNat 64 x) = true) : r ≠ x % 2 ^ 64 :=
  fun h' => by rw [← (len_eq hr).mpr h'] at h; simp at h

theorem DSt.r64 {m mh : Machine} (n : Nums m) {off o r : Nat} (hs : DSt m mh off o r) :
    r < 2 ^ 64 := by
  have := hs.fit; have := n.inHi; unfold Layout.inputHi at this; omega

theorem after16 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r v0 v1 v2 v3 : Nat}
    (hs : DSt m mh 176 o r) (hpc : mh.pc.toNat = ret16)
    (r19 : mh.reg 19 = m.reg 11 + BitVec.ofNat 64 o) (r18 : mh.reg 18 = BitVec.ofNat 64 r)
    (r23 : mh.reg 23 = BitVec.ofNat 64 noneConst) (r24 : mh.reg 24 = frB m + BitVec.ofNat 64 160)
    (r21 : mh.reg 21 = BitVec.ofNat 64 v0) (r22 : mh.reg 22 = BitVec.ofNat 64 v1)
    (r20 : mh.reg 20 = BitVec.ofNat 64 v2)
    (w160 : FW m mh 160 v3) (t168 : mh.mem (frB m + BitVec.ofNat 64 168) = some 1)
    (hr : 0 < r)
    (hw : walk (inputOf m) = fieldWalk [.optSkip, .optInt, .optInt] (sl m o r) [v0, v1, v2, v3]) :
    Reaches zesuImage (12 + 160 + (13 + 160 + 37)) (Post m) mh := by
  have hO : Out (envC m mh c0) 176 (m.reg 11 + BitVec.ofNat 64 o) (sl m o r) := out_of hs.out
  have ef := envC_facts m mh c0
  have hne : sl m o r ≠ [] := fun h => by rw [sl_nil hs.fit] at h; omega
  have hr64 := hs.r64 n
  have v18 : (Sym.var 18).eval (envC m mh c0) = BitVec.ofNat 64 r := (var_eval 18).trans r18
  refine cut_reaches (c := c0) n e hs.fr run16 (x16_ok r23 r24) hpc fun l hl hcs => ?_
  simp only [run16_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  cases hd : F2.decode (sl m o r) with
  | error =>
    have hst := out_err hO hd
    rw [fw_err hne hd] at hw
    rcases hl with rfl | rfl | rfl
    · conds; exfalso; simp [hst, Sym.eval_lit] at hcs
    · conds; exfalso; simp [hst, Sym.eval_lit] at hcs
    · exact ⟨by simp, by decide, fun m' hm' hex hfr =>
        (memcpy_exit n e hs.fr hm' hfr hex (by decide) hw).mono (by decide) fun _ h => h⟩
  | success b h p =>
    obtain ⟨hst, -, -, hcw, -⟩ := out_ok hO hd
    have hcw' : (Sym.init 0 200 8).eval (envC m mh c0) = BitVec.ofNat 64 (h + p) := hcw
    have hc := (F3.decode_success hd).2.1
    rw [sl_length m hs.fit] at hc
    rw [fw_ok hne hd] at hw
    simp only [Kind.isInt, Bool.false_eq_true, if_false, sl_drop] at hw
    rcases hl with rfl | rfl | rfl
    · -- the second nextUint64
      conds
      obtain ⟨-, h1⟩ := hcs
      rw [v18, hcw'] at h1
      have hrc := cond_len' hr64 h1
      refine ⟨by simp, by decide, fun m1 hm1 hex hfr => ?_⟩
      refine (call_n (B := 13 + 160 + 37) n e hs.fr hm1 hfr (by decide) hex (roff := 216)
        (o := o + (h + p) % 2 ^ 64) (r := r - (h + p) % 2 ^ 64) (ret := ret17) (by decide)
        (by decide) (by decide) (by have := hs.fit; omega) rfl (by decide) (by decide) rfl rfl
        (fun t ht => ?_) (fun t ht => ?_) fun m2 hs2 hpc2 hregs hmem => ?_).mono
        (by decide) fun _ h => h
      · rw [mb_some (v := .bin .add (.var 19) (.init 0 200 8)) (k := t) (by revert t; decide)]
        show byteOf ((Sym.var 19).eval _ + (Sym.init 0 200 8).eval _) t = _
        have v19 : (Sym.var 19).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 o :=
          (var_eval 19).trans r19
        rw [v19, hcw', adv_ptr]
      · rw [mb_some (v := .bin .sub (.var 18) (.init 0 200 8)) (k := t) (by revert t; decide)]
        show byteOf ((Sym.var 18).eval _ - (Sym.init 0 200 8).eval _) t = _
        rw [v18, hcw', adv_len hr64 hc]
      refine after17 n e hs2 hpc2 ?_ ?_ ?_ ?_ ?_ (fw_keep (fun t ht => hmem _ (by omega) (by omega))
        (by decide) w160) (tag_keep (hmem _ (by decide) (by decide)) (by decide) t168)
        (by omega) hw
      · rw [hregs 23 (by decide)]; rfl
      · rw [hregs 24 (by decide)]; show (Sym.ptr 0 160).eval _ = _; simp [Sym.eval, ef.b0, r24]
      · rw [hregs 21 (by decide)]; exact (var_eval 21).trans r21
      · rw [hregs 22 (by decide)]; exact (var_eval 22).trans r22
      · rw [hregs 20 (by decide)]; exact (var_eval 20).trans r20
    · -- success: nothing left after field 16
      conds
      obtain ⟨-, h1⟩ := hcs
      rw [v18, hcw'] at h1
      have hrc := cond_len hr64 h1
      rw [show r - (h + p) % 2 ^ 64 = 0 by omega, (sl_nil (by have := hs.fit; omega)).mpr rfl] at hw
      simp only [fw_nil, Kind.required, Bool.false_eq_true, if_false] at hw
      refine ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr => ?_⟩
      refine Reaches.done (succ_exit' n hs.fr hm' hfr hex (by decide) hw ?_ ?_ ?_ ?_ ?_ ?_)
      · exact (var_eval 21).trans r21
      · exact (var_eval 22).trans r22
      · exact (var_eval 20).trans r20
      · exact ⟨tag_eval t168, fun k hk => by cases hk; exact fw_eval w160⟩
      · exact opt_none rfl
      · exact opt_none rfl
    · conds; exfalso; simp [hst, Sym.eval_lit] at hcs

/-! ## Field 15 (`0x800d6160`, after the first nextUint64: the base fee) -/

theorem after15 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r v0 v1 v2 : Nat}
    (hs : NSt m mh 144 o r) (hpc : mh.pc.toNat = ret15)
    (r23 : mh.reg 23 = BitVec.ofNat 64 noneConst)
    (r21 : mh.reg 21 = BitVec.ofNat 64 v0) (r22 : mh.reg 22 = BitVec.ofNat 64 v1)
    (r20 : mh.reg 20 = BitVec.ofNat 64 v2) (hr : 0 < r)
    (hw : walk (inputOf m) =
      fieldWalk [.optInt, .optSkip, .optInt, .optInt] (sl m o r) [v0, v1, v2]) :
    Reaches zesuImage (15 + 75 + (12 + 160 + (13 + 160 + 37))) (Post m) mh := by
  have hN := nout_of (c := c0) hs
  have ef := envC_facts m mh c0
  obtain ⟨old, hslc⟩ := hs.slc
  have hS : SOut (envC m mh c0) (m.reg 11 + BitVec.ofNat 64 o) (BitVec.ofNat 64 r) (sl m o r) :=
    ⟨old, fun j hj => byte0_of (hslc j hj)⟩
  have hne : sl m o r ≠ [] := fun h => by rw [sl_nil hs.fit] at h; omega
  have hr64 : r < 2 ^ 64 := by have := hs.fit; have := n.inHi; unfold Layout.inputHi at this; omega
  rw [fw_next hne rfl] at hw
  refine cut_reaches (c := c0) n e hs.fr run15 (x15_ok r23) hpc fun l hl hcs => ?_
  simp only [run15_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · conds
    cases hn : F3.nextUint64 (sl m o r) with
    | some vc =>
      obtain ⟨v, c⟩ := vc
      exfalso; simp [(nout_ok hN hn).1, Sym.eval_lit] at hcs
    | none =>
      rw [hn] at hw
      refine ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr => ?_⟩
      exact Reaches.done (err_exit n hs.fr hm' hfr hex (by decide) (by decide) (by decide)
        (nout_err hN hn) hw)
  all_goals
    conds
    obtain ⟨v, c, hn⟩ : ∃ v c, F3.nextUint64 (sl m o r) = some (v, c) := by
      cases hn : F3.nextUint64 (sl m o r) with
      | none => exfalso; simp [nout_err hN hn, Sym.eval_lit] at hcs
      | some vc => exact ⟨vc.1, vc.2, rfl⟩
    simp only [hn] at hw
    have ho := nout_ok hN hn
    have hso := sout_ok hS hn
    have hc := next_le hn
    rw [sl_length m hs.fit] at hc
    rw [sl_drop] at hw
    obtain ⟨-, h56⟩ := hcs
    rw [hso.2, adv_len hr64 hc] at h56
  · -- success: nothing left after field 15
    simp only [Sym.eval_lit, beq_iff_eq] at h56
    have hr0 : r - c % 2 ^ 64 = 0 := by
      have := (len_eq (r := r - c % 2 ^ 64) (x := 0) (by omega)).mp h56; simpa using this
    rw [hr0, (sl_nil (by have := hs.fit; omega)).mpr rfl] at hw
    simp only [fw_nil, Kind.required, Bool.false_eq_true, if_false] at hw
    refine ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr => ?_⟩
    refine Reaches.done (succ_exit' n hs.fr hm' hfr hex (by decide) hw ?_ ?_ ?_ ?_ ?_ ?_)
    · exact (var_eval 21).trans r21
    · exact (var_eval 22).trans r22
    · exact (var_eval 20).trans r20
    · refine ⟨tag1_eval (by decide) _, fun k hk => ?_⟩
      cases hk
      show (Sym.init 0 144 8).eval _ = _
      rw [ho.2]; simp
    · exact opt_none rfl
    · exact opt_none rfl
  · -- decodeItem for field 16
    simp only [Sym.eval_lit, bne_iff_ne, ne_eq] at h56
    have hr0 : r - c % 2 ^ 64 ≠ 0 := fun h0 => h56 (by rw [h0])
    have h48 : (Sym.init 0 48 8).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 (o + c % 2 ^ 64) := by
      rw [hso.1, adv_ptr]
    have h56' : (Sym.init 0 56 8).eval (envC m mh c0) = BitVec.ofNat 64 (r - c % 2 ^ 64) := by
      rw [hso.2, adv_len hr64 hc]
    refine ⟨by simp, by decide, fun m1 hm1 hex hfr => ?_⟩
    refine (call_d (B := 12 + 160 + (13 + 160 + 37)) n e hs.fr hm1 hfr (by decide) hex (off := 176)
      (o := o + c % 2 ^ 64) (r := r - c % 2 ^ 64) (ret := ret16) (by decide) (by decide)
      (by have := hs.fit; omega) rfl (by decide) (by decide)
      (by show (Sym.ptr 0 176).eval _ = _; simp [Sym.eval, ef.b0]) h48 h56'
      fun m2 hs2 hpc2 hregs hmem => ?_).mono (by decide) fun _ h => h
    refine after16 n e hs2 hpc2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fw_write (s := .init 0 144 8) (fun t ht => hmem _ (by omega) (by omega)) (by decide)
        (ho.2.trans (by simp)))
      (tag_write (hmem _ (by decide) (by decide)) (by decide)) (by omega) hw
    · rw [hregs 19 (by decide)]; exact h48
    · rw [hregs 18 (by decide)]; exact h56'
    · rw [hregs 23 (by decide)]; rfl
    · rw [hregs 24 (by decide)]; show (Sym.ptr 0 160).eval _ = _; simp [Sym.eval, ef.b0]
    · rw [hregs 21 (by decide)]; exact (var_eval 21).trans r21
    · rw [hregs 22 (by decide)]; exact (var_eval 22).trans r22
    · rw [hregs 20 (by decide)]; exact (var_eval 20).trans r20

/-! ## Fields 12..14 (optional skips at `0x800d60b8`, `0x800d60f0`, `0x800d611c`) -/

/-- The state after decodeItem for an optional skip field `k` (12..14): outcome at 104,
the slice in `s3, s2`, the three required values in `s5, s6, s4`. -/
structure OSt (m mh : Machine) (k o r v0 v1 v2 : Nat) : Prop where
  d : DSt m mh 104 o r
  r19 : mh.reg 19 = m.reg 11 + BitVec.ofNat 64 o
  r18 : mh.reg 18 = BitVec.ofNat 64 r
  r21 : mh.reg 21 = BitVec.ofNat 64 v0
  r22 : mh.reg 22 = BitVec.ofNat 64 v1
  r20 : mh.reg 20 = BitVec.ofNat 64 v2
  pos : 0 < r
  wk : walk (inputOf m) = fieldWalk (schedule.drop k) (sl m o r) [v0, v1, v2]

/-- The decoded optional skip: its outcome words and the walk after it. -/
theorem OSt.step {m mh : Machine} {k o r v0 v1 v2 : Nat} (hs : OSt m mh k o r v0 v1 v2)
    (hk : schedule[k]? = some .optSkip) :
    (F2.decode (sl m o r) = .error ∧ F6.walk (inputOf m) = none ∧
      (Sym.init 0 136 2).eval (envC m mh c0) = BitVec.ofNat 64 4) ∨
    ∃ h p, (Sym.init 0 136 2).eval (envC m mh c0) = BitVec.ofNat 64 0 ∧
      (Sym.init 0 128 8).eval (envC m mh c0) = BitVec.ofNat 64 (h + p) ∧
      (h + p) % 2 ^ 64 ≤ r ∧
      walk (inputOf m) = fieldWalk (schedule.drop (k + 1)) (sl m (o + (h + p) % 2 ^ 64)
        (r - (h + p) % 2 ^ 64)) [v0, v1, v2] := by
  have hO : Out (envC m mh c0) 104 (m.reg 11 + BitVec.ofNat 64 o) (sl m o r) := out_of hs.d.out
  have hne : sl m o r ≠ [] := fun h => by rw [sl_nil hs.d.fit] at h; have := hs.pos; omega
  have hw := hs.wk
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hk).1,
    (List.getElem?_eq_some_iff.mp hk).2] at hw
  cases hd : F2.decode (sl m o r) with
  | error => exact .inl ⟨rfl, by rw [hw, fw_err hne hd], out_err hO hd⟩
  | success b h p =>
    obtain ⟨hst, -, -, hcw, -⟩ := out_ok hO hd
    have hc := (F3.decode_success hd).2.1
    rw [sl_length m hs.d.fit] at hc
    rw [fw_ok hne hd] at hw
    simp only [Kind.isInt, Bool.false_eq_true, if_false, sl_drop] at hw
    exact .inr ⟨h, p, hst, hcw, hc, hw⟩

theorem after14 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r v0 v1 v2 : Nat}
    (hs : OSt m mh 14 o r v0 v1 v2) (hpc : mh.pc.toNat = ret14) :
    Reaches zesuImage (14 + 160 + (15 + 75 + (12 + 160 + (13 + 160 + 37)))) (Post m) mh := by
  have ef := envC_facts m mh c0
  have hr64 := hs.d.r64 n
  have v18 : (Sym.var 18).eval (envC m mh c0) = BitVec.ofNat 64 r := (var_eval 18).trans hs.r18
  have v19 : (Sym.var 19).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 o :=
    (var_eval 19).trans hs.r19
  refine cut_reaches (c := c0) n e hs.d.fr run14 xN_ok hpc fun l hl hcs => ?_
  simp only [run14_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hs.step rfl with ⟨hd, hw, hst⟩ | ⟨h, p, hst, hcw, hc, hw⟩
  · rcases hl with rfl | rfl | rfl
    · exact ⟨by simp, by decide, fun m' hm' hex hfr =>
        (memcpy_exit n e hs.d.fr hm' hfr hex (by decide) hw).mono (by decide) fun _ h => h⟩
    all_goals conds; exfalso; simp [hst, Sym.eval_lit] at hcs
  rcases hl with rfl | rfl | rfl
  · conds; exfalso; simp [hst, Sym.eval_lit] at hcs
  · -- the first nextUint64
    conds
    obtain ⟨-, h1⟩ := hcs
    rw [v18, hcw] at h1
    have hrc := cond_len' hr64 h1
    refine ⟨by simp, by decide, fun m1 hm1 hex hfr => ?_⟩
    refine (call_n (B := 15 + 75 + (12 + 160 + (13 + 160 + 37))) n e hs.d.fr hm1 hfr (by decide)
      hex (roff := 144) (o := o + (h + p) % 2 ^ 64) (r := r - (h + p) % 2 ^ 64) (ret := ret15)
      (by decide) (by decide) (by decide) (by have := hs.d.fit; omega) rfl (by decide) (by decide)
      rfl rfl (fun t ht => ?_) (fun t ht => ?_) fun m2 hs2 hpc2 hregs hmem => ?_).mono
      (by decide) fun _ h => h
    · rw [mb_some (v := .bin .add (.var 19) (.init 0 128 8)) (k := t) (by revert t; decide)]
      show byteOf ((Sym.var 19).eval _ + (Sym.init 0 128 8).eval _) t = _
      rw [v19, hcw, adv_ptr]
    · rw [mb_some (v := .bin .sub (.var 18) (.init 0 128 8)) (k := t) (by revert t; decide)]
      show byteOf ((Sym.var 18).eval _ - (Sym.init 0 128 8).eval _) t = _
      rw [v18, hcw, adv_len hr64 hc]
    refine after15 n e hs2 hpc2 ?_ ?_ ?_ ?_ (by omega) hw
    · rw [hregs 23 (by decide)]; rfl
    · rw [hregs 21 (by decide)]; exact (var_eval 21).trans hs.r21
    · rw [hregs 22 (by decide)]; exact (var_eval 22).trans hs.r22
    · rw [hregs 20 (by decide)]; exact (var_eval 20).trans hs.r20
  · -- success: nothing left after field 14
    conds
    obtain ⟨-, h1⟩ := hcs
    rw [v18, hcw] at h1
    have hrc := cond_len hr64 h1
    rw [show r - (h + p) % 2 ^ 64 = 0 by omega, (sl_nil (by have := hs.d.fit; omega)).mpr rfl] at hw
    simp only [schedule, List.drop, fw_nil, Kind.required, Bool.false_eq_true, if_false] at hw
    refine ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr => ?_⟩
    refine Reaches.done (succ_exit' n hs.d.fr hm' hfr hex (by decide) hw ?_ ?_ ?_ ?_ ?_ ?_)
    · exact (var_eval 21).trans hs.r21
    · exact (var_eval 22).trans hs.r22
    · exact (var_eval 20).trans hs.r20
    · exact opt_none rfl
    · exact opt_none rfl
    · exact opt_none rfl

/-- Fields 12 and 13: the missing-field success, the error tail, or the next decodeItem. -/
theorem opt_skip {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {k o r v0 v1 v2 : Nat}
    (hs : OSt m mh k o r v0 v1 v2) (hk : schedule[k]? = some .optSkip)
    (hk1 : (schedule.drop (k + 1)).head?.map Kind.required = some false)
    {pc ret : Nat} {ls : List Leaf} (hrun : run zesuImage cuts 400 pc (SC xN) = some ls)
    (hpc : mh.pc.toNat = pc) (hls : ∀ l ∈ ls,
      (l.exit = .at Layout.memcpyEntry ∧ l.conds = [.ne (.init 0 136 2) (.lit 0)] ∧
        memcpyOK l.S = true ∧ l.S.steps = 20 ∧ l.obligs = []) ∨
      (l.exit = .ret retT ∧
        l.conds = [.eq (.init 0 136 2) (.lit 0), .eq (.var 18) (.init 0 128 8)] ∧
        succOK l.S [.var 21, .var 22, .var 20, .lit 0, .lit 0, .lit 0, .lit 0, .lit 0, .lit 0] = true ∧
        l.S.steps = 27 ∧ l.obligs = [.aligned retT 4]) ∨
      (l.exit = .call F2.entry ret ∧
        l.conds = [.eq (.init 0 136 2) (.lit 0), .ne (.var 18) (.init 0 128 8)] ∧
        keepOK l.S = true ∧ l.S.steps = 11 ∧ l.obligs = [] ∧ l.S.reg 1 = .lit ret ∧
        l.S.reg 10 = .ptr 0 104 ∧ l.S.reg 11 = .bin .add (.var 19) (.init 0 128 8) ∧
        l.S.reg 12 = .bin .sub (.var 18) (.init 0 128 8) ∧ l.S.reg 19 = l.S.reg 11 ∧
        l.S.reg 18 = l.S.reg 12 ∧ l.S.reg 21 = .var 21 ∧ l.S.reg 22 = .var 22 ∧
        l.S.reg 20 = .var 20))
    (hra : (BitVec.ofNat 64 ret &&& ~~~(1 : Word)).toNat % 4 = 0)
    (hrp : (BitVec.ofNat 64 ret &&& ~~~(1 : Word)).toNat = ret) {B : Nat}
    (K : ∀ mh' o' r', OSt m mh' (k + 1) o' r' v0 v1 v2 → mh'.pc.toNat = ret →
      Reaches zesuImage B (Post m) mh') :
    Reaches zesuImage (11 + 75 + B) (Post m) mh := by
  have hr64 := hs.d.r64 n
  have v18 : (Sym.var 18).eval (envC m mh c0) = BitVec.ofNat 64 r := (var_eval 18).trans hs.r18
  have v19 : (Sym.var 19).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 o :=
    (var_eval 19).trans hs.r19
  refine cut_reaches (c := c0) n e hs.d.fr hrun xN_ok hpc fun l hl hcs => ?_
  rcases hls l hl with ⟨hex0, hc0, hk0, hst0, hob0⟩ | ⟨hex0, hc0, hk0, hst0, hob0⟩ |
    ⟨hex0, hc0, hk0, hst0, hob0, g1, g10, g11, g12, g19, g18, g21, g22, g20⟩ <;> rw [hc0] at hcs
  · conds
    rcases hs.step hk with ⟨hd, hw, hst⟩ | ⟨h, p, hst, -⟩
    · exact ⟨by simp [hob0], by omega, fun m' hm' hex hfr =>
        (memcpy_exit n e hs.d.fr hm' hfr (by rw [hex0] at hex; exact hex) hk0 hw).mono
          (by omega) fun _ h => h⟩
    · exfalso; simp [hst, Sym.eval_lit] at hcs
  · conds
    rcases hs.step hk with ⟨hd, hw, hst⟩ | ⟨h, p, hst, hcw, hc, hw⟩
    · exfalso; simp [hst, Sym.eval_lit] at hcs
    obtain ⟨-, h1⟩ := hcs
    rw [v18, hcw] at h1
    have hrc := cond_len hr64 h1
    rw [show r - (h + p) % 2 ^ 64 = 0 by omega, (sl_nil (by have := hs.d.fit; omega)).mpr rfl] at hw
    have hw' : walk (inputOf m) = some [v0, v1, v2] := by
      rw [hw]
      cases hd' : schedule.drop (k + 1) with
      | nil => rfl
      | cons k' later =>
        rw [hd'] at hk1
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hk1
        simp [fw_nil, hk1]
    refine ⟨by simp [hob0, retT_aligned e mh c0], by omega, fun m' hm' hex hfr => ?_⟩
    rw [hex0] at hex
    refine Reaches.done (succ_exit n hs.d.fr hm' hfr hex hk0 hw' ?_ ?_ ?_ (opt_none rfl)
      (opt_none rfl) (opt_none rfl))
    · exact (var_eval 21).trans hs.r21
    · exact (var_eval 22).trans hs.r22
    · exact (var_eval 20).trans hs.r20
  · conds
    rcases hs.step hk with ⟨hd, hw, hst⟩ | ⟨h, p, hst, hcw, hc, hw⟩
    · exfalso; simp [hst, Sym.eval_lit] at hcs
    obtain ⟨-, h1⟩ := hcs
    rw [v18, hcw] at h1
    have hrc := cond_len' hr64 h1
    have e11 : (l.S.reg 11).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 (o + (h + p) % 2 ^ 64) := by
      rw [g11]; show (Sym.var 19).eval _ + (Sym.init 0 128 8).eval _ = _; rw [v19, hcw, adv_ptr]
    have e12 : (l.S.reg 12).eval (envC m mh c0) = BitVec.ofNat 64 (r - (h + p) % 2 ^ 64) := by
      rw [g12]; show (Sym.var 18).eval _ - (Sym.init 0 128 8).eval _ = _; rw [v18, hcw, adv_len hr64 hc]
    refine ⟨by simp [hob0], by omega, fun m1 hm1 hex hfr => ?_⟩
    rw [hex0] at hex
    rw [hst0, show 11 + 75 + B - 11 = 75 + B by omega]
    refine call_d n e hs.d.fr hm1 hfr hk0 hex (off := 104) (by decide) (by decide)
      (by have := hs.d.fit; omega) g1 hra hrp
      (by rw [g10]; simp [Sym.eval, (envC_facts m mh c0).b0]) e11 e12
      fun m2 hs2 hpc2 hregs _ => K m2 _ _ ⟨hs2, ?_, ?_, ?_, ?_, ?_, by omega, hw⟩ hpc2
    · rw [hregs 19 (by decide)]; show (l.S.reg 19).eval _ = _; rw [g19]; exact e11
    · rw [hregs 18 (by decide)]; show (l.S.reg 18).eval _ = _; rw [g18]; exact e12
    · rw [hregs 21 (by decide)]; show (l.S.reg 21).eval _ = _; rw [g21]
      exact (var_eval 21).trans hs.r21
    · rw [hregs 22 (by decide)]; show (l.S.reg 22).eval _ = _; rw [g22]
      exact (var_eval 22).trans hs.r22
    · rw [hregs 20 (by decide)]; show (l.S.reg 20).eval _ = _; rw [g20]
      exact (var_eval 20).trans hs.r20

theorem after13 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r v0 v1 v2 : Nat}
    (hs : OSt m mh 13 o r v0 v1 v2) (hpc : mh.pc.toNat = ret13) :
    Reaches zesuImage (11 + 75 + (14 + 160 + (15 + 75 + (12 + 160 + (13 + 160 + 37))))) (Post m) mh :=
  opt_skip n e hs rfl rfl run13 hpc (by decide) (by decide) (by decide)
    fun _ _ _ hs' hpc' => after14 n e hs' hpc'

theorem after12 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r v0 v1 v2 : Nat}
    (hs : OSt m mh 12 o r v0 v1 v2) (hpc : mh.pc.toNat = ret12) :
    Reaches zesuImage (11 + 75 + (11 + 75 + (14 + 160 + (15 + 75 + (12 + 160 + (13 + 160 + 37))))))
      (Post m) mh :=
  opt_skip n e hs rfl rfl run12 hpc (by decide) (by decide) (by decide)
    fun _ _ _ hs' hpc' => after13 n e hs' hpc'

/-! ## The three byte loops (`0x800d5f88`, `0x800d5fec`, `0x800d6054`) -/

def curL : Sym := .bin .add (.ptr 2 1) (.var 32)
def accL (acc : Nat) : Sym := .bin .or (.bin .sll (.var acc) (.lit 8)) (.initx 2 0 (.var 32) 1 1)

/-- The loop head after `j` of the `p` payload bytes at input offset `o + h`; `mh0` is the
machine at the loop entry, which the loop changes only in `a1`, `a3` and the accumulator. -/
structure LInv (m mh0 mh : Machine) (acc : Fin 32) (lh o h p j : Nat) : Prop where
  pc : mh.pc.toNat = lh
  regs : ∀ i : Fin 32, i.val ≠ 11 → i.val ≠ 13 → i ≠ acc → mh.reg i = mh0.reg i
  mem : mh.mem = mh0.mem
  fr : Fr m mh0
  fit : o + h + p ≤ (m.reg 12).toNat
  p8 : p ≤ 8
  jp : j < p
  acc : mh.reg acc = BitVec.ofNat 64 (F2.bigEndian (sl m (o + h) j))
  cur : mh.reg 11 = m.reg 11 + BitVec.ofNat 64 (o + h + j)
  last : mh.reg 12 = m.reg 11 + BitVec.ofNat 64 (o + h + p)

theorem LInv.frm {m mh0 mh : Machine} {acc : Fin 32} {lh o h p j : Nat}
    (hI : LInv m mh0 mh acc lh o h p j) (hacc : acc.val = 20 ∨ acc.val = 21 ∨ acc.val = 22) :
    Fr m mh := by
  have hc := hI.fr
  have g : ∀ i : Fin 32, i.val ∈ [2, 8, 9, 25, 26, 27] → mh.reg i = mh0.reg i := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact hI.regs i (by omega) (by omega) (fun h' => by subst h'; omega)
  refine ⟨(g 2 (by decide)).trans hc.r2, (g 8 (by decide)).trans hc.r8, (g 9 (by decide)).trans hc.r9,
    fun i hi => ?_, ?_, ?_, ?_⟩
  · have : i.val ∈ [2, 8, 9, 25, 26, 27] := by
      simp only [calleeVars, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega
    exact (g i this).trans (hc.rk i hi)
  · rw [hI.mem]; exact hc.saved
  · rw [hI.mem]; exact hc.pres
  · intro a ha; rw [hI.mem]; exact hc.so a ha

theorem sl_succ (m : Machine) {a j : Nat} (hj : a + j < (m.reg 12).toNat) :
    sl m a (j + 1) = sl m a j ++ [(m.mem (m.reg 11 + BitVec.ofNat 64 (a + j))).getD 0] := by
  unfold sl
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem (by rw [inputOf_length]; omega)]
  simp [F2.bytesOf]

theorem LInv.byte {m mh0 mh : Machine} (n : Nums m) {acc : Fin 32} {lh o h p j : Nat}
    (hI : LInv m mh0 mh acc lh o h p j) (c : Word) :
    (envC m mh c).byte0 2 (o + h + j) = (m.mem (m.reg 11 + BitVec.ofNat 64 (o + h + j))).getD 0 := by
  have ef := envC_facts m mh c
  rw [ef.by0, ef.b2, hI.mem, hI.fr.inMem n (by have := hI.fit; have := hI.jp; omega)]

theorem LInv.acc_eval {m mh0 mh : Machine} (n : Nums m) {acc : Fin 32} {lh o h p j : Nat}
    (hI : LInv m mh0 mh acc lh o h p j) :
    (accL acc.val).eval (envC m mh (BitVec.ofNat 64 (o + h + j))) =
      BitVec.ofNat 64 (F2.bigEndian (sl m (o + h) (j + 1))) := by
  have ef := envC_facts m mh (BitVec.ofNat 64 (o + h + j))
  have hfit := hI.fit; have hjp := hI.jp; have hp8 := hI.p8
  have hlen := n.inHi; unfold Layout.inputHi at hlen
  have hhj : (BitVec.ofNat 64 (o + h + j)).toNat = o + h + j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [sl_succ m (by omega), F2.bigEndian_append]
  have hlt : F2.bigEndian (sl m (o + h) j) < 2 ^ 56 := by
    refine Nat.lt_of_lt_of_le (F2.bigEndian_lt _) ?_
    have : (sl m (o + h) j).length ≤ 7 := by rw [sl_length m (by omega)]; omega
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) this) (by decide)
  simp only [accL, Sym.eval, BinOp.eval, F2.ofBytes1, ef.v32]
  rw [show (envC m mh (BitVec.ofNat 64 (o + h + j))).vars acc.val = mh.reg acc from ef.v acc,
    hI.acc, hhj]
  try simp only [Nat.reduceMod, Nat.reducePow]
  rw [Nat.zero_add, Nat.one_mul, hI.byte n, show o + h + j = o + h + j from rfl]
  exact F2.shl_or _ _ hlt

theorem cur_eval {m mh : Machine} {a : Nat} :
    curL.eval (envC m mh (BitVec.ofNat 64 a)) = m.reg 11 + BitVec.ofNat 64 (a + 1) := by
  have ef := envC_facts m mh (BitVec.ofNat 64 a)
  simp only [curL, Sym.eval, BinOp.eval, ef.b2, ef.v32]
  rw [show BitVec.ofInt 64 1 = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat]
  congr 2; omega

theorem xL_ok {m mh : Machine} {a : Nat} (h11 : mh.reg 11 = m.reg 11 + BitVec.ofNat 64 a) :
    ∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 8 → i.val ≠ 9 →
    ∀ s, xL i.val = some s → s.eval (envC m mh (BitVec.ofNat 64 a)) = mh.reg i := by
  have ef := envC_facts m mh (BitVec.ofNat 64 a)
  intro i _ _ _ s hs
  simp only [xL] at hs
  by_cases h : i.val = 11
  · simp only [h, if_true, Option.some.injEq] at hs; subst hs
    rw [show i = 11 from Fin.ext h, h11]
    simp [Sym.eval, BinOp.eval, ef.b2, ef.v32]
  · simp [h] at hs

/-- A back edge: the loop head again, one byte further. -/
abbrev BackOK (acc lh : Nat) (l : Leaf) : Prop :=
  l.exit = .at lh ∧ l.conds = [.ne curL (.var 12)] ∧ l.obligs = [.inBounds 2 0 (.var 32) 1 1] ∧
    l.S.steps = 5 ∧ l.S.mem = [] ∧ l.S.regions = regionsR ∧ l.S.reg 11 = curL ∧
    l.S.reg acc = accL acc ∧ ∀ i < 32, i ≠ 11 → i ≠ 13 → i ≠ acc → l.S.reg i = (SC xL).reg i

theorem add_small_inj {a : Word} {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63)
    (h : a + BitVec.ofNat 64 x = a + BitVec.ofNat 64 y) : x = y := by
  have := congrArg BitVec.toNat h
  simp [BitVec.toNat_add] at this
  have := a.isLt
  omega

/-- The loop from byte `j` on: back edges by the generic step, the exit by `hexit`. -/
theorem loop_gen {m : Machine} (n : Nums m) (e : Entry m) {acc : Fin 32}
    (hacc : acc.val = 20 ∨ acc.val = 21 ∨ acc.val = 22) {lh : Nat} {ls : List Leaf}
    (hrun : run zesuImage cuts 400 lh (SC xL) = some ls)
    (hls : ∀ l ∈ ls, BackOK acc.val lh l ∨ (l.exit ≠ .at lh ∧ l.conds.head? = some (.eq curL (.var 12))))
    {mh0 : Machine} {o h p : Nat} {E : Nat} (hE : 5 ≤ E)
    (hexit : ∀ j mh, LInv m mh0 mh acc lh o h p j → j + 1 = p → ∀ l ∈ ls, l.exit ≠ .at lh →
      (∀ c ∈ l.conds, c.eval (envC m mh (BitVec.ofNat 64 (o + h + j))) = true) →
      (∀ ob ∈ l.obligs, ob.holds (envC m mh (BitVec.ofNat 64 (o + h + j)))) ∧ l.S.steps ≤ E ∧
      ∀ m', Match (envC m mh (BitVec.ofNat 64 (o + h + j))) l.S m' →
        ExitOk (envC m mh (BitVec.ofNat 64 (o + h + j))) l.exit m' →
        SameOutside (InWritable (envC m mh (BitVec.ofNat 64 (o + h + j))) (SC xL)) mh m' →
        Reaches zesuImage (E - l.S.steps) (Post m) m') :
    ∀ μ j mh, j + μ + 1 = p → LInv m mh0 mh acc lh o h p j →
      Reaches zesuImage (μ * 5 + E) (Post m) mh := by
  intro μ
  induction μ with
  | zero =>
    intro j mh hj hI
    have hc := hI.frm hacc
    refine cut_reaches n e hc hrun (xL_ok hI.cur) hI.pc fun l hl hcs => ?_
    rcases hls l hl with ⟨hex0, hc0, -⟩ | ⟨hne, hhd⟩
    · exfalso
      rw [hc0] at hcs
      have := hcs _ (List.mem_singleton_self _)
      have v12 : (Sym.var 12).eval (envC m mh (BitVec.ofNat 64 (o + h + j))) =
          m.reg 11 + BitVec.ofNat 64 (o + h + p) := (var_eval 12).trans hI.last
      simp only [SBool.eval, cur_eval, v12, bne_iff_ne, ne_eq] at this
      exact this (by rw [show o + h + j + 1 = o + h + p by omega])
    · have := hexit j mh hI (by omega) l hl hne hcs
      simpa using this
  | succ μ ih =>
    intro j mh hj hI
    have hc := hI.frm hacc
    have hfit := hI.fit; have hjp := hI.jp; have hp8 := hI.p8
    have hlen := n.inHi; unfold Layout.inputHi at hlen
    refine cut_reaches n e hc hrun (xL_ok hI.cur) hI.pc fun l hl hcs => ?_
    rcases hls l hl with ⟨hex0, hc0, hob, hst, hmem, hreg, h11, hac, hrs⟩ | ⟨hne, hhd⟩
    · have hacc' := hI.acc_eval n
      refine ⟨?_, by rw [hst]; omega, fun m' hm' hex hfr => ?_⟩
      · rw [hob]
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Oblig.holds, Sym.eval,
          (envC_facts m mh _).v32, (envC_facts m mh _).s2]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      have hm'' : m'.mem = mh.mem :=
        F2.mem_eq_of_nowrite hm' hfr hmem (by rw [hreg]; rfl) (hc.init n e _)
      have g : ∀ i : Fin 32, m'.reg i = (l.S.reg i.val).eval (envC m mh (BitVec.ofNat 64 (o + h + j))) :=
        fun i => (hm'.regs i).symm
      rw [hst, show (μ + 1) * 5 + E - 5 = μ * 5 + E by rw [Nat.succ_mul]; omega]
      refine ih (j + 1) m' (by omega) ⟨by rw [hex0] at hex; exact hex, fun i h1 h2 h3 => ?_,
        hm''.trans hI.mem, hI.fr, hfit, hp8, by omega, ?_, ?_, ?_⟩
      · rw [g i, hrs i.val i.isLt h1 h2 (fun h' => h3 (Fin.ext h')),
          (Fr.match (c := BitVec.ofNat 64 (o + h + j)) n e hc (xL_ok hI.cur)).regs i]
        exact hI.regs i h1 h2 h3
      · rw [g acc, hac, hacc']
      · rw [g 11]; show (l.S.reg 11).eval _ = _
        rw [h11, cur_eval, show o + h + j + 1 = o + h + (j + 1) by omega]
      · rw [g 12]; show (l.S.reg 12).eval _ = _
        rw [hrs 12 (by decide) (by decide) (by decide) (by omega)]
        exact ((Fr.match n e hc (xL_ok hI.cur)).regs 12).trans hI.last
    · have hcs1 := hcs _ (List.mem_of_mem_head? hhd)
      have v12 : (Sym.var 12).eval (envC m mh (BitVec.ofNat 64 (o + h + j))) =
          m.reg 11 + BitVec.ofNat 64 (o + h + p) := (var_eval 12).trans hI.last
      simp only [SBool.eval, cur_eval, v12, beq_iff_eq] at hcs1
      have := add_small_inj (x := o + h + j + 1) (y := o + h + p) (by omega) (by omega) hcs1
      omega

/-! ## The required integers (fields 9..11, outcome at 280) -/

theorem sl_payload (m : Machine) {o r h p : Nat} (hhp : h + p ≤ r) :
    ((sl m o r).drop h).take p = sl m (o + h) p := by
  simp only [sl, List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by omega)]

/-- decodeItem's outcome for a required integer field, and the walk after it. -/
theorem int_step {m mh : Machine} {o r : Nat} {later : List Kind} {vals : List Nat}
    (hs : DSt m mh 280 o r) (hw : walk (inputOf m) = fieldWalk (.reqInt :: later) (sl m o r) vals) :
    (walk (inputOf m) = none ∧ (Sym.init 0 312 2).eval (envC m mh c0) = BitVec.ofNat 64 4) ∨
    ∃ b h p, (Sym.init 0 312 2).eval (envC m mh c0) = BitVec.ofNat 64 0 ∧
      (Sym.bin .and (.init 0 296 1) (.lit 1)).eval (envC m mh c0) =
        BitVec.ofNat 64 (if b then 1 else 0) ∧
      (Sym.init 0 288 8).eval (envC m mh c0) = BitVec.ofNat 64 p ∧
      (Sym.init 0 304 8).eval (envC m mh c0) = BitVec.ofNat 64 (h + p) ∧ p < 2 ^ 64 ∧
      (b = true ∨ 8 < p → walk (inputOf m) = none) ∧
      (b = false → p ≤ 8 → h + p ≤ r ∧
        (0 < p → (Sym.init 0 280 8).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 (o + h)) ∧
        walk (inputOf m) = fieldWalk later (sl m (o + (h + p)) (r - (h + p)))
          (vals ++ [F2.bigEndian (sl m (o + h) p)])) := by
  have hO : Out (envC m mh c0) 280 (m.reg 11 + BitVec.ofNat 64 o) (sl m o r) := out_of hs.out
  cases hd : F2.decode (sl m o r) with
  | error =>
    refine .inl ⟨?_, out_err hO hd⟩
    rw [hw]
    by_cases hne : sl m o r = []
    · rw [hne]; rfl
    · exact fw_err hne hd
  | success b h p =>
    have hne : sl m o r ≠ [] := fun h' => by rw [h'] at hd; simp [F2.decode] at hd
    obtain ⟨hh9, hc, h128, hp64⟩ := F3.decode_success hd
    rw [sl_length m hs.fit] at hc
    obtain ⟨hst, hfl, hpl, hcw, hptr⟩ := out_ok hO hd
    rw [fw_ok hne hd] at hw
    simp only [Kind.isInt, if_true] at hw
    refine .inr ⟨b, h, p, hst, hfl, hpl, hcw, hp64, fun hb => ?_, fun hb hp8 => ?_⟩
    · rw [hw, if_pos (by rcases hb with rfl | hb <;> simp [*])]
    · subst hb
      rw [Nat.mod_eq_of_lt (show h + p < 2 ^ 64 by omega)] at hc hw
      rw [if_neg (by simp; omega), sl_drop, sl_payload m hc] at hw
      refine ⟨hc, fun hp0 => ?_, hw⟩
      rw [hptr, if_neg (fun h' => by have := h128 h'; omega), ofNat_add_ofNat]

/-- The call of decodeItem for field 12 (from field 11 or its loop): `after12`. -/
theorem to12 {m mh m1 : Machine} (n : Nums m) (e : Entry m) (hc : Fr m mh) {c : Word}
    {x : Nat → Option Sym} {lS : SState} (hm1 : Match (envC m mh c) lS m1)
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh m1) (hk : keepOK lS = true)
    (hex : m1.pc.toNat = F2.entry) {o r v0 v1 v2 : Nat} (hor : o + r ≤ (m.reg 12).toNat)
    (hr : 0 < r) (g1 : lS.reg 1 = .lit ret12) (g10 : lS.reg 10 = .ptr 0 104)
    (g11 : (lS.reg 11).eval (envC m mh c) = m.reg 11 + BitVec.ofNat 64 o)
    (g12 : (lS.reg 12).eval (envC m mh c) = BitVec.ofNat 64 r)
    (g19 : lS.reg 19 = lS.reg 11) (g18 : lS.reg 18 = lS.reg 12)
    (g21 : (lS.reg 21).eval (envC m mh c) = BitVec.ofNat 64 v0)
    (g22 : (lS.reg 22).eval (envC m mh c) = BitVec.ofNat 64 v1)
    (g20 : (lS.reg 20).eval (envC m mh c) = BitVec.ofNat 64 v2)
    (hw : walk (inputOf m) = fieldWalk (schedule.drop 12) (sl m o r) [v0, v1, v2]) :
    Reaches zesuImage (75 + 818) (Post m) m1 := by
  refine call_d n e hc hm1 hfr hk hex (off := 104) (by decide) (by decide) hor g1 (by decide)
    (by decide) (by rw [g10]; simp [Sym.eval, (envC_facts m mh c).b0]) g11 g12
    fun m2 hs2 hpc2 hregs _ => (after12 n e ⟨hs2, ?_, ?_, ?_, ?_, ?_, hr, hw⟩ hpc2).mono
      (by decide) fun _ h => h
  · rw [hregs 19 (by decide)]; show (lS.reg 19).eval _ = _; rw [g19]; exact g11
  · rw [hregs 18 (by decide)]; show (lS.reg 18).eval _ = _; rw [g18]; exact g12
  · exact (hregs 21 (by decide)).trans g21
  · exact (hregs 22 (by decide)).trans g22
  · exact (hregs 20 (by decide)).trans g20

theorem ult8 {p : Nat} (hp : p < 2 ^ 64) :
    (BitVec.ofNat 64 8).ult (BitVec.ofNat 64 p) = decide (8 < p) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt hp]

theorem beq0 {p : Nat} (hp : p < 2 ^ 64) :
    (BitVec.ofNat 64 p == BitVec.ofNat 64 0) = decide (p = 0) := by
  by_cases h : p = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 p ≠ BitVec.ofNat 64 0 := fun h' => by
      have := congrArg BitVec.toNat h'; simp [Nat.mod_eq_of_lt hp] at this; omega
    simp [this, h]

theorem flag0 (b : Bool) : (BitVec.ofNat 64 (if b then 1 else 0) == BitVec.ofNat 64 0) = !b := by
  cases b <;> rfl

theorem adv_len' {r x : Nat} (hr : r < 2 ^ 64) (hx : x ≤ r) :
    BitVec.ofNat 64 r - BitVec.ofNat 64 x = BitVec.ofNat 64 (r - x) := by
  rw [adv_len hr (by rw [Nat.mod_eq_of_lt (by omega)]; omega), Nat.mod_eq_of_lt (by omega)]

theorem bigEndian_sl0 (m : Machine) (a : Nat) : F2.bigEndian (sl m a 0) = 0 := by
  simp [sl, F2.bigEndian]

set_option hygiene false in
/-- The conditions of an integer field's leaf as Boolean facts. -/
macro "iconds" : tactic => `(tactic| (
  conds
  simp only [hst, hfl, hpl, Sym.eval_lit, ult8 hp64, beq0 hp64, flag0, Bool.not_not,
    Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, beq_self_eq_true,
    Bool.true_and, Bool.and_true] at hcs))

set_option maxHeartbeats 400000 in
theorem after11 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r v0 v1 : Nat}
    (hs : DSt m mh 280 o r) (hpc : mh.pc.toNat = ret11)
    (r19 : mh.reg 19 = m.reg 11 + BitVec.ofNat 64 o) (r18 : mh.reg 18 = BitVec.ofNat 64 r)
    (r21 : mh.reg 21 = BitVec.ofNat 64 v0) (r22 : mh.reg 22 = BitVec.ofNat 64 v1)
    (hw : walk (inputOf m) = fieldWalk (schedule.drop 11) (sl m o r) [v0, v1]) :
    Reaches zesuImage 955 (Post m) mh := by
  have ef := envC_facts m mh c0
  have hr64 := hs.r64 n
  have hfit := hs.fit
  have hlen := n.inHi; unfold Layout.inputHi at hlen
  have v18 : (Sym.var 18).eval (envC m mh c0) = BitVec.ofNat 64 r := (var_eval 18).trans r18
  have v19 : (Sym.var 19).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 o :=
    (var_eval 19).trans r19
  have v21 : (Sym.var 21).eval (envC m mh c0) = BitVec.ofNat 64 v0 := (var_eval 21).trans r21
  have v22 : (Sym.var 22).eval (envC m mh c0) = BitVec.ofNat 64 v1 := (var_eval 22).trans r22
  refine cut_reaches (c := c0) n e hs.fr run11 xN_ok hpc fun l hl hcs => ?_
  simp only [run11_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases int_step hs hw with ⟨hwn, hst⟩ | ⟨b, h, p, hst, hfl, hpl, hcw, hp64, hbad, hok⟩
  · rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr =>
        Reaches.done (err_exit (v := .lit 3) n hs.fr hm' hfr hex (by decide) (by decide)
          (by decide) rfl hwn)⟩
    all_goals conds; exfalso; simp [hst, Sym.eval_lit] at hcs
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · conds; exfalso; simp [hst, Sym.eval_lit] at hcs
  · -- a list
    iconds
    have hb : b = true := by cases b <;> simp_all
    exact ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr =>
      Reaches.done (err_exit (v := .lit 3) n hs.fr hm' hfr hex (by decide) (by decide) (by decide)
        rfl (hbad (.inl hb)))⟩
  · -- more than 8 payload bytes
    iconds
    exact ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr =>
      Reaches.done (err_exit (v := .lit 3) n hs.fr hm' hfr hex (by decide) (by decide) (by decide)
        rfl (hbad (.inr hcs.2.2)))⟩
  · -- empty payload, more fields: decodeItem for field 12
    iconds
    obtain ⟨-, hb', -, hp0, h1⟩ := hcs
    subst hp0
    obtain ⟨hhp, -, hw'⟩ := hok hb' (by omega)
    rw [v18, hcw] at h1
    have hrc := cond_len' hr64 h1
    rw [Nat.mod_eq_of_lt (by omega)] at hrc
    rw [bigEndian_sl0] at hw'
    refine ⟨by simp, by decide, fun m1 hm1 hex hfr => ?_⟩
    refine (to12 n e hs.fr hm1 hfr (by decide) hex (o := o + (h + 0)) (r := r - (h + 0))
      (by omega) (by omega) rfl rfl ?_ ?_ rfl rfl v21 v22 rfl hw').mono (by decide) fun _ h => h
    · show (Sym.var 19).eval _ + (Sym.init 0 304 8).eval _ = _
      rw [v19, hcw, ofNat_add_ofNat]
    · show (Sym.var 18).eval _ - (Sym.init 0 304 8).eval _ = _
      rw [v18, hcw, adv_len' hr64 (by omega)]
  · -- empty payload, nothing left: success
    iconds
    obtain ⟨-, hb', -, hp0, h1⟩ := hcs
    subst hp0
    obtain ⟨hhp, -, hw'⟩ := hok hb' (by omega)
    rw [v18, hcw] at h1
    have hrc := cond_len hr64 h1
    rw [Nat.mod_eq_of_lt (by omega)] at hrc
    rw [bigEndian_sl0, show r - (h + 0) = 0 by omega, (sl_nil (by omega)).mpr rfl] at hw'
    simp only [schedule, List.drop, fw_nil, Kind.required, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] at hw'
    refine ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr => ?_⟩
    exact Reaches.done (succ_exit' n hs.fr hm' hfr hex (by decide) hw' v21 v22 rfl (opt_none rfl)
      (opt_none rfl) (opt_none rfl))
  · -- the byte loop
    iconds
    obtain ⟨-, hb', hp8, hp0⟩ := hcs
    have hp0' : p ≠ 0 := fun h0 => by subst h0; simp at hp0
    have hp8' : p ≤ 8 := by omega
    obtain ⟨hhp, hptr, hw'⟩ := hok hb' hp8'
    refine ⟨by simp, by decide, fun m' hm' hex hfr => ?_⟩
    obtain ⟨hc', -, -⟩ := Fr.of_leaf n e hs.fr hm' hfr (by decide)
    have g := reg_eval hm'
    have hI : LInv m m' m' 20 loop11 o h p 0 := by
      refine ⟨hex, fun _ _ _ _ => rfl, rfl, hc', by omega, hp8', by omega, ?_, ?_, ?_⟩
      · rw [g 20]; show (Sym.lit 0).eval _ = _; rw [bigEndian_sl0]; rfl
      · rw [g 11]; show (Sym.init 0 280 8).eval _ = _; rw [hptr (by omega)]; rfl
      · rw [g 12]; show (Sym.init 0 280 8).eval _ + (Sym.init 0 288 8).eval _ = _
        rw [hptr (by omega), hpl, ofNat_add_ofNat]
    -- the loop's machine at entry
    have m18 : m'.reg 18 = BitVec.ofNat 64 r := (g 18).trans v18
    have m19 : m'.reg 19 = m.reg 11 + BitVec.ofNat 64 o := (g 19).trans v19
    have m10 : m'.reg 10 = BitVec.ofNat 64 (h + p) := (g 10).trans hcw
    have m21 : m'.reg 21 = BitVec.ofNat 64 v0 := (g 21).trans v21
    have m22 : m'.reg 22 = BitVec.ofNat 64 v1 := (g 22).trans v22
    refine (loop_gen n e (acc := 20) (by decide) runL11 (by decide) (mh0 := m') (E := 14 + 75 + 818)
      (by omega) (fun j mh2 hI2 hj l2 hl2 hne hcs => ?_) (p - 1) 0 m' (by omega) hI).mono
      (by show _ ≤ 955 - 13; omega) fun _ h => h
    have w : ∀ i : Fin 32, i.val ≠ 11 → i.val ≠ 13 → i ≠ 20 →
        (Sym.var i.val).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) = m'.reg i :=
      fun i h1 h2 h3 => (var_eval i).trans (hI2.regs i h1 h2 h3)
    have w18 : (Sym.var 18).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) = BitVec.ofNat 64 r :=
      (w 18 (by decide) (by decide) (by decide)).trans m18
    have w19 : (Sym.var 19).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) =
        m.reg 11 + BitVec.ofNat 64 o := (w 19 (by decide) (by decide) (by decide)).trans m19
    have w10 : (Sym.var 10).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) =
        BitVec.ofNat 64 (h + p) := (w 10 (by decide) (by decide) (by decide)).trans m10
    have w21 : (Sym.var 21).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) = BitVec.ofNat 64 v0 :=
      (w 21 (by decide) (by decide) (by decide)).trans m21
    have w22 : (Sym.var 22).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) = BitVec.ofNat 64 v1 :=
      (w 22 (by decide) (by decide) (by decide)).trans m22
    have wacc := hI2.acc_eval n
    rw [show j + 1 = p from hj] at wacc
    have hob : Oblig.holds (envC m mh2 (BitVec.ofNat 64 (o + h + j))) (.inBounds 2 0 (.var 32) 1 1) := by
      simp only [Oblig.holds, Sym.eval, (envC_facts m mh2 _).v32, (envC_facts m mh2 _).s2]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    simp only [runL11_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl2
    rcases hl2 with rfl | rfl | rfl
    · exact absurd rfl hne
    · -- more fields: decodeItem for field 12
      conds
      obtain ⟨-, h1⟩ := hcs
      rw [w18, w10] at h1
      have hrc := cond_len' hr64 h1
      rw [Nat.mod_eq_of_lt (by omega)] at hrc
      refine ⟨by simpa using hob, by decide, fun m1 hm1 hex1 hfr1 => ?_⟩
      refine (to12 n e (hI2.frm (by decide)) hm1 hfr1 (by decide) hex1 (o := o + (h + p))
        (r := r - (h + p)) (by omega) (by omega) rfl rfl ?_ ?_ rfl rfl w21 w22 wacc hw').mono
        (by decide) fun _ h => h
      · show (Sym.var 19).eval _ + (Sym.var 10).eval _ = _
        rw [w19, w10, ofNat_add_ofNat]
      · show (Sym.var 18).eval _ - (Sym.var 10).eval _ = _
        rw [w18, w10, adv_len' hr64 (by omega)]
    · -- nothing left: success
      conds
      obtain ⟨-, h1⟩ := hcs
      rw [w18, w10] at h1
      have hrc := cond_len hr64 h1
      rw [Nat.mod_eq_of_lt (by omega)] at hrc
      rw [show r - (h + p) = 0 by omega, (sl_nil (by omega)).mpr rfl] at hw'
      simp only [schedule, List.drop, fw_nil, Kind.required, Bool.false_eq_true, if_false,
        List.cons_append, List.nil_append] at hw'
      refine ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hob, retT_aligned e mh2 _⟩, by decide, fun m' hm' hex hfr => ?_⟩
      exact Reaches.done (succ_exit' n (hI2.frm (by decide)) hm' hfr hex (by decide) hw' w21 w22
        wacc (opt_none rfl) (opt_none rfl) (opt_none rfl))

/-- The call of decodeItem for field 11 (from field 10 or its loop): `after11`. -/
theorem to11 {m mh m1 : Machine} (n : Nums m) (e : Entry m) (hc : Fr m mh) {c : Word}
    {x : Nat → Option Sym} {lS : SState} (hm1 : Match (envC m mh c) lS m1)
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh m1) (hk : keepOK lS = true)
    (hex : m1.pc.toNat = F2.entry) {o r v0 v1 : Nat} (hor : o + r ≤ (m.reg 12).toNat)
    (g1 : lS.reg 1 = .lit ret11) (g10 : lS.reg 10 = .ptr 0 280)
    (g11 : (lS.reg 11).eval (envC m mh c) = m.reg 11 + BitVec.ofNat 64 o)
    (g12 : (lS.reg 12).eval (envC m mh c) = BitVec.ofNat 64 r)
    (g19 : lS.reg 19 = lS.reg 11) (g18 : lS.reg 18 = lS.reg 12)
    (g21 : (lS.reg 21).eval (envC m mh c) = BitVec.ofNat 64 v0)
    (g22 : (lS.reg 22).eval (envC m mh c) = BitVec.ofNat 64 v1)
    (hw : walk (inputOf m) = fieldWalk (schedule.drop 11) (sl m o r) [v0, v1]) :
    Reaches zesuImage (75 + 955) (Post m) m1 := by
  refine call_d n e hc hm1 hfr hk hex (off := 280) (by decide) (by decide) hor g1 (by decide)
    (by decide) (by rw [g10]; simp [Sym.eval, (envC_facts m mh c).b0]) g11 g12
    fun m2 hs2 hpc2 hregs _ => after11 n e hs2 hpc2 ?_ ?_ ?_ ?_ hw
  · rw [hregs 19 (by decide)]; show (lS.reg 19).eval _ = _; rw [g19]; exact g11
  · rw [hregs 18 (by decide)]; show (lS.reg 18).eval _ = _; rw [g18]; exact g12
  · exact (hregs 21 (by decide)).trans g21
  · exact (hregs 22 (by decide)).trans g22

set_option maxHeartbeats 400000 in
theorem after10 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r v0 : Nat}
    (hs : DSt m mh 280 o r) (hpc : mh.pc.toNat = ret10)
    (r18 : mh.reg 18 = m.reg 11 + BitVec.ofNat 64 o) (r20 : mh.reg 20 = BitVec.ofNat 64 r)
    (r21 : mh.reg 21 = BitVec.ofNat 64 v0)
    (hw : walk (inputOf m) = fieldWalk (schedule.drop 10) (sl m o r) [v0]) :
    Reaches zesuImage 1091 (Post m) mh := by
  have hr64 := hs.r64 n
  have hfit := hs.fit
  have hlen := n.inHi; unfold Layout.inputHi at hlen
  have v18 : (Sym.var 18).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 o :=
    (var_eval 18).trans r18
  have v20 : (Sym.var 20).eval (envC m mh c0) = BitVec.ofNat 64 r := (var_eval 20).trans r20
  have v21 : (Sym.var 21).eval (envC m mh c0) = BitVec.ofNat 64 v0 := (var_eval 21).trans r21
  refine cut_reaches (c := c0) n e hs.fr run10 xN_ok hpc fun l hl hcs => ?_
  simp only [run10_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases int_step hs hw with ⟨hwn, hst⟩ | ⟨b, h, p, hst, hfl, hpl, hcw, hp64, hbad, hok⟩
  · rcases hl with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr =>
        Reaches.done (err_exit (v := .lit 3) n hs.fr hm' hfr hex (by decide) (by decide)
          (by decide) rfl hwn)⟩
    all_goals conds; exfalso; simp [hst, Sym.eval_lit] at hcs
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · conds; exfalso; simp [hst, Sym.eval_lit] at hcs
  · -- a list
    iconds
    have hb : b = true := by cases b <;> simp_all
    exact ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr =>
      Reaches.done (err_exit (v := .lit 3) n hs.fr hm' hfr hex (by decide) (by decide) (by decide)
        rfl (hbad (.inl hb)))⟩
  · -- more than 8 payload bytes
    iconds
    exact ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr =>
      Reaches.done (err_exit (v := .lit 3) n hs.fr hm' hfr hex (by decide) (by decide) (by decide)
        rfl (hbad (.inr hcs.2.2)))⟩
  · -- empty payload: decodeItem for field 11
    iconds
    obtain ⟨-, hb', -, hp0⟩ := hcs
    subst hp0
    obtain ⟨hhp, -, hw'⟩ := hok hb' (by omega)
    rw [bigEndian_sl0] at hw'
    refine ⟨by simp, by decide, fun m1 hm1 hex hfr => ?_⟩
    refine (to11 n e hs.fr hm1 hfr (by decide) hex (o := o + (h + 0)) (r := r - (h + 0))
      (by omega) rfl rfl ?_ ?_ rfl rfl v21 rfl hw').mono (by decide) fun _ h => h
    · show (Sym.var 18).eval _ + (Sym.init 0 304 8).eval _ = _
      rw [v18, hcw, ofNat_add_ofNat]
    · show (Sym.var 20).eval _ - (Sym.init 0 304 8).eval _ = _
      rw [v20, hcw, adv_len' hr64 (by omega)]
  · -- the byte loop
    iconds
    obtain ⟨-, hb', hp8, hp0⟩ := hcs
    have hp0' : p ≠ 0 := fun h0 => by subst h0; simp at hp0
    have hp8' : p ≤ 8 := by omega
    obtain ⟨hhp, hptr, hw'⟩ := hok hb' hp8'
    refine ⟨by simp, by decide, fun m' hm' hex hfr => ?_⟩
    obtain ⟨hc', -, -⟩ := Fr.of_leaf n e hs.fr hm' hfr (by decide)
    have g := reg_eval hm'
    have hI : LInv m m' m' 22 loop10 o h p 0 := by
      refine ⟨hex, fun _ _ _ _ => rfl, rfl, hc', by omega, hp8', by omega, ?_, ?_, ?_⟩
      · rw [g 22]; show (Sym.lit 0).eval _ = _; rw [bigEndian_sl0]; rfl
      · rw [g 11]; show (Sym.init 0 280 8).eval _ = _; rw [hptr (by omega)]; rfl
      · rw [g 12]; show (Sym.init 0 280 8).eval _ + (Sym.init 0 288 8).eval _ = _
        rw [hptr (by omega), hpl, ofNat_add_ofNat]
    have m18 : m'.reg 18 = m.reg 11 + BitVec.ofNat 64 o := (g 18).trans v18
    have m20 : m'.reg 20 = BitVec.ofNat 64 r := (g 20).trans v20
    have m10 : m'.reg 10 = BitVec.ofNat 64 (h + p) := (g 10).trans hcw
    have m21 : m'.reg 21 = BitVec.ofNat 64 v0 := (g 21).trans v21
    refine (loop_gen n e (acc := 22) (by decide) runL10 (by decide) (mh0 := m') (E := 13 + 75 + 955)
      (by omega) (fun j mh2 hI2 hj l2 hl2 hne hcs => ?_) (p - 1) 0 m' (by omega) hI).mono
      (by show _ ≤ 1091 - 13; omega) fun _ h => h
    have w : ∀ i : Fin 32, i.val ≠ 11 → i.val ≠ 13 → i ≠ 22 →
        (Sym.var i.val).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) = m'.reg i :=
      fun i h1 h2 h3 => (var_eval i).trans (hI2.regs i h1 h2 h3)
    have w18 : (Sym.var 18).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) =
        m.reg 11 + BitVec.ofNat 64 o := (w 18 (by decide) (by decide) (by decide)).trans m18
    have w20 : (Sym.var 20).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) = BitVec.ofNat 64 r :=
      (w 20 (by decide) (by decide) (by decide)).trans m20
    have w10 : (Sym.var 10).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) =
        BitVec.ofNat 64 (h + p) := (w 10 (by decide) (by decide) (by decide)).trans m10
    have w21 : (Sym.var 21).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) = BitVec.ofNat 64 v0 :=
      (w 21 (by decide) (by decide) (by decide)).trans m21
    have wacc := hI2.acc_eval n
    rw [show j + 1 = p from hj] at wacc
    have hob : Oblig.holds (envC m mh2 (BitVec.ofNat 64 (o + h + j))) (.inBounds 2 0 (.var 32) 1 1) := by
      simp only [Oblig.holds, Sym.eval, (envC_facts m mh2 _).v32, (envC_facts m mh2 _).s2]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    simp only [runL10_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl2
    rcases hl2 with rfl | rfl
    · exact absurd rfl hne
    · refine ⟨by simpa using hob, by decide, fun m1 hm1 hex1 hfr1 => ?_⟩
      refine (to11 n e (hI2.frm (by decide)) hm1 hfr1 (by decide) hex1 (o := o + (h + p))
        (r := r - (h + p)) (by omega) rfl rfl ?_ ?_ rfl rfl w21 wacc hw').mono
        (by decide) fun _ h => h
      · show (Sym.var 18).eval _ + (Sym.var 10).eval _ = _
        rw [w18, w10, ofNat_add_ofNat]
      · show (Sym.var 20).eval _ - (Sym.var 10).eval _ = _
        rw [w20, w10, adv_len' hr64 (by omega)]

/-- The call of decodeItem for field 10 (from field 9 or its loop): `after10`. -/
theorem to10 {m mh m1 : Machine} (n : Nums m) (e : Entry m) (hc : Fr m mh) {c : Word}
    {x : Nat → Option Sym} {lS : SState} (hm1 : Match (envC m mh c) lS m1)
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh m1) (hk : keepOK lS = true)
    (hex : m1.pc.toNat = F2.entry) {o r v0 : Nat} (hor : o + r ≤ (m.reg 12).toNat)
    (g1 : lS.reg 1 = .lit ret10) (g10 : lS.reg 10 = .ptr 0 280)
    (g11 : (lS.reg 11).eval (envC m mh c) = m.reg 11 + BitVec.ofNat 64 o)
    (g12 : (lS.reg 12).eval (envC m mh c) = BitVec.ofNat 64 r)
    (g18 : lS.reg 18 = lS.reg 11) (g20 : lS.reg 20 = lS.reg 12)
    (g21 : (lS.reg 21).eval (envC m mh c) = BitVec.ofNat 64 v0)
    (hw : walk (inputOf m) = fieldWalk (schedule.drop 10) (sl m o r) [v0]) :
    Reaches zesuImage (75 + 1091) (Post m) m1 := by
  refine call_d n e hc hm1 hfr hk hex (off := 280) (by decide) (by decide) hor g1 (by decide)
    (by decide) (by rw [g10]; simp [Sym.eval, (envC_facts m mh c).b0]) g11 g12
    fun m2 hs2 hpc2 hregs _ => after10 n e hs2 hpc2 ?_ ?_ ?_ hw
  · rw [hregs 18 (by decide)]; show (lS.reg 18).eval _ = _; rw [g18]; exact g11
  · rw [hregs 20 (by decide)]; show (lS.reg 20).eval _ = _; rw [g20]; exact g12
  · exact (hregs 21 (by decide)).trans g21

set_option maxHeartbeats 400000 in
theorem after9 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r : Nat}
    (hs : DSt m mh 280 o r) (hpc : mh.pc.toNat = ret9)
    (r18 : mh.reg 18 = m.reg 11 + BitVec.ofNat 64 o) (r19 : mh.reg 19 = BitVec.ofNat 64 r)
    (hw : walk (inputOf m) = fieldWalk (schedule.drop 9) (sl m o r) []) :
    Reaches zesuImage 1226 (Post m) mh := by
  have hr64 := hs.r64 n
  have hfit := hs.fit
  have hlen := n.inHi; unfold Layout.inputHi at hlen
  have v18 : (Sym.var 18).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 o :=
    (var_eval 18).trans r18
  have v19 : (Sym.var 19).eval (envC m mh c0) = BitVec.ofNat 64 r := (var_eval 19).trans r19
  refine cut_reaches (c := c0) n e hs.fr run9 xN_ok hpc fun l hl hcs => ?_
  simp only [run9_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases int_step hs hw with ⟨hwn, hst⟩ | ⟨b, h, p, hst, hfl, hpl, hcw, hp64, hbad, hok⟩
  · rcases hl with rfl | rfl | rfl | rfl | rfl
    all_goals try (conds; exfalso; simp [hst, Sym.eval_lit] at hcs; done)
    exact ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr =>
      Reaches.done (err_exit (v := .lit 3) n hs.fr hm' hfr hex (by decide) (by decide)
        (by decide) rfl hwn)⟩
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · -- a list
    iconds
    have hb : b = true := by cases b <;> simp_all
    exact ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr =>
      Reaches.done (err_exit (v := .lit 3) n hs.fr hm' hfr hex (by decide) (by decide) (by decide)
        rfl (hbad (.inl hb)))⟩
  · -- more than 8 payload bytes
    iconds
    exact ⟨by simpa using retT_aligned e mh c0, by decide, fun m' hm' hex hfr =>
      Reaches.done (err_exit (v := .lit 3) n hs.fr hm' hfr hex (by decide) (by decide) (by decide)
        rfl (hbad (.inr hcs.2.2)))⟩
  · -- empty payload: decodeItem for field 10
    iconds
    obtain ⟨-, hb', -, hp0⟩ := hcs
    subst hp0
    obtain ⟨hhp, -, hw'⟩ := hok hb' (by omega)
    rw [bigEndian_sl0] at hw'
    refine ⟨by simp, by decide, fun m1 hm1 hex hfr => ?_⟩
    refine (to10 n e hs.fr hm1 hfr (by decide) hex (o := o + (h + 0)) (r := r - (h + 0))
      (by omega) rfl rfl ?_ ?_ rfl rfl rfl hw').mono (by decide) fun _ h => h
    · show (Sym.var 18).eval _ + (Sym.init 0 304 8).eval _ = _
      rw [v18, hcw, ofNat_add_ofNat]
    · show (Sym.var 19).eval _ - (Sym.init 0 304 8).eval _ = _
      rw [v19, hcw, adv_len' hr64 (by omega)]
  · -- the byte loop
    iconds
    obtain ⟨-, hb', hp8, hp0⟩ := hcs
    have hp0' : p ≠ 0 := fun h0 => by subst h0; simp at hp0
    have hp8' : p ≤ 8 := by omega
    obtain ⟨hhp, hptr, hw'⟩ := hok hb' hp8'
    refine ⟨by simp, by decide, fun m' hm' hex hfr => ?_⟩
    obtain ⟨hc', -, -⟩ := Fr.of_leaf n e hs.fr hm' hfr (by decide)
    have g := reg_eval hm'
    have hI : LInv m m' m' 21 loop9 o h p 0 := by
      refine ⟨hex, fun _ _ _ _ => rfl, rfl, hc', by omega, hp8', by omega, ?_, ?_, ?_⟩
      · rw [g 21]; show (Sym.lit 0).eval _ = _; rw [bigEndian_sl0]; rfl
      · rw [g 11]; show (Sym.init 0 280 8).eval _ = _; rw [hptr (by omega)]; rfl
      · rw [g 12]; show (Sym.init 0 280 8).eval _ + (Sym.init 0 288 8).eval _ = _
        rw [hptr (by omega), hpl, ofNat_add_ofNat]
    have m18 : m'.reg 18 = m.reg 11 + BitVec.ofNat 64 o := (g 18).trans v18
    have m19 : m'.reg 19 = BitVec.ofNat 64 r := (g 19).trans v19
    have m10 : m'.reg 10 = BitVec.ofNat 64 (h + p) := (g 10).trans hcw
    refine (loop_gen n e (acc := 21) (by decide) runL9 (by decide) (mh0 := m') (E := 12 + 75 + 1091)
      (by omega) (fun j mh2 hI2 hj l2 hl2 hne hcs => ?_) (p - 1) 0 m' (by omega) hI).mono
      (by show _ ≤ 1226 - 13; omega) fun _ h => h
    have w : ∀ i : Fin 32, i.val ≠ 11 → i.val ≠ 13 → i ≠ 21 →
        (Sym.var i.val).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) = m'.reg i :=
      fun i h1 h2 h3 => (var_eval i).trans (hI2.regs i h1 h2 h3)
    have w18 : (Sym.var 18).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) =
        m.reg 11 + BitVec.ofNat 64 o := (w 18 (by decide) (by decide) (by decide)).trans m18
    have w19 : (Sym.var 19).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) = BitVec.ofNat 64 r :=
      (w 19 (by decide) (by decide) (by decide)).trans m19
    have w10 : (Sym.var 10).eval (envC m mh2 (BitVec.ofNat 64 (o + h + j))) =
        BitVec.ofNat 64 (h + p) := (w 10 (by decide) (by decide) (by decide)).trans m10
    have wacc := hI2.acc_eval n
    rw [show j + 1 = p from hj] at wacc
    have hob : Oblig.holds (envC m mh2 (BitVec.ofNat 64 (o + h + j))) (.inBounds 2 0 (.var 32) 1 1) := by
      simp only [Oblig.holds, Sym.eval, (envC_facts m mh2 _).v32, (envC_facts m mh2 _).s2]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    simp only [runL9_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl2
    rcases hl2 with rfl | rfl
    · exact absurd rfl hne
    · refine ⟨by simpa using hob, by decide, fun m1 hm1 hex1 hfr1 => ?_⟩
      refine (to10 n e (hI2.frm (by decide)) hm1 hfr1 (by decide) hex1 (o := o + (h + p))
        (r := r - (h + p)) (by omega) rfl rfl ?_ ?_ rfl rfl wacc hw').mono
        (by decide) fun _ h => h
      · show (Sym.var 18).eval _ + (Sym.var 10).eval _ = _
        rw [w18, w10, ofNat_add_ofNat]
      · show (Sym.var 19).eval _ - (Sym.var 10).eval _ = _
        rw [w19, w10, adv_len' hr64 (by omega)]
  · conds; exfalso; simp [hst, Sym.eval_lit] at hcs

/-! ## The required skips (fields 0..8, outcome at 64) -/

/-- The state after decodeItem for required skip field `k`: outcome at 64, the slice start in
`s3` and its length in `rR`. -/
structure SSt (m mh : Machine) (k : Nat) (rR : Fin 32) (o r : Nat) : Prop where
  d : DSt m mh 64 o r
  r19 : mh.reg 19 = m.reg 11 + BitVec.ofNat 64 o
  rr : mh.reg rR = BitVec.ofNat 64 r
  pos : 0 < r
  wk : walk (inputOf m) = fieldWalk (schedule.drop k) (sl m o r) []

theorem SSt.step {m mh : Machine} {k : Nat} {rR : Fin 32} {o r : Nat} (hs : SSt m mh k rR o r)
    (hk : schedule[k]? = some .reqSkip) :
    (F6.walk (inputOf m) = none ∧ (Sym.init 0 96 2).eval (envC m mh c0) = BitVec.ofNat 64 4) ∨
    ∃ h p, (Sym.init 0 96 2).eval (envC m mh c0) = BitVec.ofNat 64 0 ∧
      (Sym.init 0 88 8).eval (envC m mh c0) = BitVec.ofNat 64 (h + p) ∧
      (h + p) % 2 ^ 64 ≤ r ∧
      F6.walk (inputOf m) = fieldWalk (schedule.drop (k + 1)) (sl m (o + (h + p) % 2 ^ 64)
        (r - (h + p) % 2 ^ 64)) [] := by
  have hO : Out (envC m mh c0) 64 (m.reg 11 + BitVec.ofNat 64 o) (sl m o r) := out_of hs.d.out
  have hne : sl m o r ≠ [] := fun h => by rw [sl_nil hs.d.fit] at h; have := hs.pos; omega
  have hw := hs.wk
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hk).1,
    (List.getElem?_eq_some_iff.mp hk).2] at hw
  cases hd : F2.decode (sl m o r) with
  | error => exact .inl ⟨by rw [hw, fw_err hne hd], out_err hO hd⟩
  | success b h p =>
    obtain ⟨hst, -, -, hcw, -⟩ := out_ok hO hd
    have hc := (F3.decode_success hd).2.1
    rw [sl_length m hs.d.fit] at hc
    rw [fw_ok hne hd] at hw
    simp only [Kind.isInt, Bool.false_eq_true, if_false, sl_drop] at hw
    exact .inr ⟨h, p, hst, hcw, hc, hw⟩

/-- Fields 0..7: the error tail, the missing-field tail, or the next decodeItem. -/
theorem skip_req {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {k o r : Nat}
    {rR' : Fin 32} (hs : SSt m mh k 18 o r) (hk : schedule[k]? = some .reqSkip)
    (hk1 : (schedule.drop (k + 1)).head?.map Kind.required = some true) (hR : rR' ∈ calleeSaved)
    {pc ret : Nat} {ls : List Leaf} (hrun : run zesuImage cuts 400 pc (SC xN) = some ls)
    (hpc : mh.pc.toNat = pc) (hls : ∀ l ∈ ls,
      (l.exit = .at Layout.memcpyEntry ∧ l.conds = [.ne (.init 0 96 2) (.lit 0)] ∧
        memcpyOK l.S = true ∧ l.S.steps = 20 ∧ l.obligs = []) ∨
      (l.exit = .at Layout.memcpyEntry ∧
        l.conds = [.eq (.init 0 96 2) (.lit 0), .eq (.var 18) (.init 0 88 8)] ∧
        memcpyOK l.S = true ∧ l.S.steps = 21 ∧ l.obligs = []) ∨
      (l.exit = .call F2.entry ret ∧
        l.conds = [.eq (.init 0 96 2) (.lit 0), .ne (.var 18) (.init 0 88 8)] ∧
        keepOK l.S = true ∧ l.S.steps = 11 ∧ l.obligs = [] ∧ l.S.reg 1 = .lit ret ∧
        l.S.reg 10 = .ptr 0 64 ∧ l.S.reg 11 = .bin .add (.var 19) (.init 0 88 8) ∧
        l.S.reg 12 = .bin .sub (.var 18) (.init 0 88 8) ∧ l.S.reg 19 = l.S.reg 11 ∧
        l.S.reg rR'.val = l.S.reg 12))
    (hra : (BitVec.ofNat 64 ret &&& ~~~(1 : Word)).toNat % 4 = 0)
    (hrp : (BitVec.ofNat 64 ret &&& ~~~(1 : Word)).toNat = ret) {B : Nat}
    (K : ∀ mh' o' r', SSt m mh' (k + 1) rR' o' r' → mh'.pc.toNat = ret →
      Reaches zesuImage B (Post m) mh') :
    Reaches zesuImage (11 + 75 + B) (Post m) mh := by
  have hr64 := hs.d.r64 n
  have v18 : (Sym.var 18).eval (envC m mh c0) = BitVec.ofNat 64 r := (var_eval 18).trans hs.rr
  have v19 : (Sym.var 19).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 o :=
    (var_eval 19).trans hs.r19
  refine cut_reaches (c := c0) n e hs.d.fr hrun xN_ok hpc fun l hl hcs => ?_
  rcases hls l hl with ⟨hex0, hc0, hk0, hst0, hob0⟩ | ⟨hex0, hc0, hk0, hst0, hob0⟩ |
    ⟨hex0, hc0, hk0, hst0, hob0, g1, g10, g11, g12, g19, gR⟩ <;> rw [hc0] at hcs
  · conds
    rcases hs.step hk with ⟨hw, hst⟩ | ⟨h, p, hst, -⟩
    · exact ⟨by simp [hob0], by omega, fun m' hm' hex hfr =>
        (memcpy_exit n e hs.d.fr hm' hfr (by rw [hex0] at hex; exact hex) hk0 hw).mono
          (by omega) fun _ h => h⟩
    · exfalso; simp [hst, Sym.eval_lit] at hcs
  · conds
    rcases hs.step hk with ⟨hd, hst⟩ | ⟨h, p, hst, hcw, hc, hw⟩
    · exfalso; simp [hst, Sym.eval_lit] at hcs
    obtain ⟨-, h1⟩ := hcs
    rw [v18, hcw] at h1
    have hrc := cond_len hr64 h1
    rw [show r - (h + p) % 2 ^ 64 = 0 by omega, (sl_nil (by have := hs.d.fit; omega)).mpr rfl] at hw
    have hw' : walk (inputOf m) = none := by
      rw [hw]
      cases hd' : schedule.drop (k + 1) with
      | nil => rw [hd'] at hk1; simp at hk1
      | cons k' later =>
        rw [hd'] at hk1
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hk1
        simp [fw_nil, hk1]
    exact ⟨by simp [hob0], by omega, fun m' hm' hex hfr =>
      (memcpy_exit n e hs.d.fr hm' hfr (by rw [hex0] at hex; exact hex) hk0 hw').mono
        (by omega) fun _ h => h⟩
  · conds
    rcases hs.step hk with ⟨hd, hst⟩ | ⟨h, p, hst, hcw, hc, hw⟩
    · exfalso; simp [hst, Sym.eval_lit] at hcs
    obtain ⟨-, h1⟩ := hcs
    rw [v18, hcw] at h1
    have hrc := cond_len' hr64 h1
    have e11 : (l.S.reg 11).eval (envC m mh c0) =
        m.reg 11 + BitVec.ofNat 64 (o + (h + p) % 2 ^ 64) := by
      rw [g11]; show (Sym.var 19).eval _ + (Sym.init 0 88 8).eval _ = _; rw [v19, hcw, adv_ptr]
    have e12 : (l.S.reg 12).eval (envC m mh c0) = BitVec.ofNat 64 (r - (h + p) % 2 ^ 64) := by
      rw [g12]; show (Sym.var 18).eval _ - (Sym.init 0 88 8).eval _ = _
      rw [v18, hcw, adv_len hr64 hc]
    refine ⟨by simp [hob0], by omega, fun m1 hm1 hex hfr => ?_⟩
    rw [hex0] at hex
    rw [hst0, show 11 + 75 + B - 11 = 75 + B by omega]
    refine call_d n e hs.d.fr hm1 hfr hk0 hex (off := 64) (by decide) (by decide)
      (by have := hs.d.fit; omega) g1 hra hrp
      (by rw [g10]; simp [Sym.eval, (envC_facts m mh c0).b0]) e11 e12
      fun m2 hs2 hpc2 hregs _ => K m2 _ _ ⟨hs2, ?_, ?_, by omega, hw⟩ hpc2
    · rw [hregs 19 (by decide)]; show (l.S.reg 19).eval _ = _; rw [g19]; exact e11
    · rw [hregs rR' hR, gR]; exact e12

set_option maxHeartbeats 400000 in
theorem after8 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r : Nat}
    (hs : SSt m mh 8 20 o r) (hpc : mh.pc.toNat = 0x800d5ef4) :
    Reaches zesuImage 1311 (Post m) mh := by
  have ef := envC_facts m mh c0
  have hr64 := hs.d.r64 n
  have v20 : (Sym.var 20).eval (envC m mh c0) = BitVec.ofNat 64 r := (var_eval 20).trans hs.rr
  have v19 : (Sym.var 19).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 o :=
    (var_eval 19).trans hs.r19
  refine cut_reaches (c := c0) n e hs.d.fr runS8 xN_ok hpc fun l hl hcs => ?_
  simp only [runS8_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · conds
    rcases hs.step rfl with ⟨hw, hst⟩ | ⟨h, p, hst, -⟩
    · exact ⟨by simp, by decide, fun m' hm' hex hfr =>
        (memcpy_exit n e hs.d.fr hm' hfr hex (by decide) hw).mono (by decide) fun _ h => h⟩
    · exfalso; simp [hst, Sym.eval_lit] at hcs
  · conds
    rcases hs.step rfl with ⟨hd, hst⟩ | ⟨h, p, hst, hcw, hc, hw⟩
    · exfalso; simp [hst, Sym.eval_lit] at hcs
    have e11 : (Sym.bin .add (.var 19) (.init 0 88 8)).eval (envC m mh c0) =
        m.reg 11 + BitVec.ofNat 64 (o + (h + p) % 2 ^ 64) := by
      show (Sym.var 19).eval _ + (Sym.init 0 88 8).eval _ = _; rw [v19, hcw, adv_ptr]
    have e12 : (Sym.bin .sub (.var 20) (.init 0 88 8)).eval (envC m mh c0) =
        BitVec.ofNat 64 (r - (h + p) % 2 ^ 64) := by
      show (Sym.var 20).eval _ - (Sym.init 0 88 8).eval _ = _; rw [v20, hcw, adv_len hr64 hc]
    refine ⟨by simp, by decide, fun m1 hm1 hex hfr => ?_⟩
    refine (call_d (B := 1226) n e hs.d.fr hm1 hfr (by decide) hex (off := 280)
      (o := o + (h + p) % 2 ^ 64) (r := r - (h + p) % 2 ^ 64) (ret := ret9) (by decide)
      (by decide) (by have := hs.d.fit; omega) rfl (by decide) (by decide)
      (by show (Sym.ptr 0 280).eval _ = _; simp [Sym.eval, ef.b0]) e11 e12
      fun m2 hs2 hpc2 hregs _ => after9 n e hs2 hpc2 ?_ ?_ hw).mono (by decide) fun _ h => h
    · rw [hregs 18 (by decide)]; exact e11
    · rw [hregs 19 (by decide)]; exact e12

theorem after7 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r : Nat}
    (hs : SSt m mh 7 18 o r) (hpc : mh.pc.toNat = 0x800d5ec8) :
    Reaches zesuImage (11 + 75 + 1311) (Post m) mh :=
  skip_req (rR' := 20) n e hs rfl rfl (by decide) runS7 hpc (by decide) (by decide) (by decide)
    fun _ _ _ hs' hpc' => after8 n e hs' hpc'

theorem after6 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r : Nat}
    (hs : SSt m mh 6 18 o r) (hpc : mh.pc.toNat = 0x800d5e9c) :
    Reaches zesuImage (11 + 75 + (11 + 75 + 1311)) (Post m) mh :=
  skip_req (rR' := 18) n e hs rfl rfl (by decide) runS6 hpc (by decide) (by decide) (by decide)
    fun _ _ _ hs' hpc' => after7 n e hs' hpc'

theorem after5 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r : Nat}
    (hs : SSt m mh 5 18 o r) (hpc : mh.pc.toNat = 0x800d5e70) :
    Reaches zesuImage 1569 (Post m) mh :=
  skip_req (rR' := 18) n e hs rfl rfl (by decide) runS5 hpc (by decide) (by decide) (by decide)
    fun _ _ _ hs' hpc' => after6 n e hs' hpc'

theorem after4 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r : Nat}
    (hs : SSt m mh 4 18 o r) (hpc : mh.pc.toNat = 0x800d5e44) :
    Reaches zesuImage (11 + 75 + 1569) (Post m) mh :=
  skip_req (rR' := 18) n e hs rfl rfl (by decide) runS4 hpc (by decide) (by decide) (by decide)
    fun _ _ _ hs' hpc' => after5 n e hs' hpc'

theorem after3 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r : Nat}
    (hs : SSt m mh 3 18 o r) (hpc : mh.pc.toNat = 0x800d5e18) :
    Reaches zesuImage 1741 (Post m) mh :=
  skip_req (rR' := 18) n e hs rfl rfl (by decide) runS3 hpc (by decide) (by decide) (by decide)
    fun _ _ _ hs' hpc' => after4 n e hs' hpc'

theorem after2 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r : Nat}
    (hs : SSt m mh 2 18 o r) (hpc : mh.pc.toNat = 0x800d5dec) :
    Reaches zesuImage (11 + 75 + 1741) (Post m) mh :=
  skip_req (rR' := 18) n e hs rfl rfl (by decide) runS2 hpc (by decide) (by decide) (by decide)
    fun _ _ _ hs' hpc' => after3 n e hs' hpc'

theorem after1 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r : Nat}
    (hs : SSt m mh 1 18 o r) (hpc : mh.pc.toNat = 0x800d5dc0) :
    Reaches zesuImage 1913 (Post m) mh :=
  skip_req (rR' := 18) n e hs rfl rfl (by decide) runS1 hpc (by decide) (by decide) (by decide)
    fun _ _ _ hs' hpc' => after2 n e hs' hpc'

theorem afterF0 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine} {o r : Nat}
    (hs : SSt m mh 0 18 o r) (hpc : mh.pc.toNat = 0x800d5d38) :
    Reaches zesuImage 1999 (Post m) mh :=
  (skip_req (rR' := 18) n e hs rfl rfl (by decide) runS0 hpc (by decide) (by decide) (by decide)
    fun _ _ _ hs' hpc' => after1 n e hs' hpc').mono (by decide) fun _ h => h

/-! ## The outer list (`0x800d5cf8`) -/

theorem sl_all (m : Machine) : sl m 0 (m.reg 12).toNat = inputOf m := by
  rw [sl, List.drop_zero, List.take_of_length_le (Nat.le_of_eq (inputOf_length m))]

set_option maxHeartbeats 400000 in
theorem after0 {m : Machine} (n : Nums m) (e : Entry m) {mh : Machine}
    (hs : DSt m mh 8 0 (m.reg 12).toNat) (hpc : mh.pc.toNat = ret0) :
    Reaches zesuImage 2087 (Post m) mh := by
  have ef := envC_facts m mh c0
  have hO : Out (envC m mh c0) 8 (m.reg 11 + BitVec.ofNat 64 0) (sl m 0 (m.reg 12).toNat) :=
    out_of hs.out
  rw [sl_all] at hO
  have hfits := e.fits (inputOf m) (F3.bytesAt_bytesOf e.inP) (inputOf_length m)
  refine cut_reaches (c := c0) n e hs.fr run0 xN_ok hpc fun l hl hcs => ?_
  simp only [run0_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  cases hd : F2.decode (inputOf m) with
  | error =>
    have hst := out_err hO hd
    have hw := walk_outer_err (.inl hd)
    rcases hl with rfl | rfl | rfl | rfl
    all_goals try (conds; exfalso; simp [hst, Sym.eval_lit] at hcs; done)
    exact ⟨by simp, by decide, fun m' hm' hex hfr =>
      (memcpy_exit n e hs.fr hm' hfr hex (by decide) hw).mono (by decide) fun _ h => h⟩
  | success b h p =>
    obtain ⟨hst, hfl, hpl, -, hptr⟩ := out_ok hO hd
    have hfl' : (Sym.bin .and (.init 0 24 1) (.lit 1)).eval (envC m mh c0) =
        BitVec.ofNat 64 (if b then 1 else 0) := hfl
    have hpl' : (Sym.init 0 16 8).eval (envC m mh c0) = BitVec.ofNat 64 p := hpl
    obtain ⟨hh9, -, h128, hp64⟩ := F3.decode_success hd
    have hfit := decode_fits hfits hd
    rw [inputOf_length] at hfit
    rcases hl with rfl | rfl | rfl | rfl
    · -- not a list
      conds
      obtain ⟨-, h2⟩ := hcs
      rw [hfl', Sym.eval_lit, flag0] at h2
      have hb : b = false := by simpa using h2
      subst hb
      exact ⟨by simp, by decide, fun m' hm' hex hfr =>
        (memcpy_exit n e hs.fr hm' hfr hex (by decide) (walk_outer_err (.inr (.inl ⟨h, p, hd⟩)))).mono
          (by decide) fun _ h => h⟩
    · -- an empty list
      conds
      obtain ⟨-, h2, h3⟩ := hcs
      rw [hfl', Sym.eval_lit] at h2
      rw [hpl', Sym.eval_lit, beq0 hp64] at h3
      have hb' : b = true := by cases b <;> simp_all
      have hp0 : p = 0 := by simpa using h3
      subst hb' hp0
      exact ⟨by simp, by decide, fun m' hm' hex hfr =>
        (memcpy_exit n e hs.fr hm' hfr hex (by decide) (walk_outer_err (.inr (.inr ⟨h, hd⟩)))).mono
          (by decide) fun _ h => h⟩
    · -- field 0
      conds
      obtain ⟨-, h2, h3⟩ := hcs
      rw [hfl', Sym.eval_lit] at h2
      rw [hpl', Sym.eval_lit] at h3
      have hb' : b = true := by cases b <;> simp_all
      have hp0' : p ≠ 0 := fun h0 => by subst h0; simp at h3
      subst hb'
      have hw := walk_outer hd (by omega) (by rw [inputOf_length]; exact hfit)
      have e11 : (Sym.init 0 8 8).eval (envC m mh c0) = m.reg 11 + BitVec.ofNat 64 h := by
        rw [hptr, if_neg (fun h' => hp0' (h128 h')), ofNat_add_ofNat, Nat.zero_add]
      refine ⟨by simp, by decide, fun m1 hm1 hex hfr => ?_⟩
      refine (call_d (B := 1999) n e hs.fr hm1 hfr (by decide) hex (off := 64) (o := h) (r := p)
        (ret := 0x800d5d38) (by decide) (by decide) hfit rfl (by decide) (by decide)
        (by show (Sym.ptr 0 64).eval _ = _; simp [Sym.eval, ef.b0]) e11 hpl
        fun m2 hs2 hpc2 hregs _ => afterF0 n e ⟨hs2, ?_, ?_, by omega, hw⟩ hpc2).mono
        (by decide) fun _ h => h
      · rw [hregs 19 (by decide)]; exact e11
      · rw [hregs 18 (by decide)]; exact hpl
    · conds; exfalso; simp [hst, Sym.eval_lit] at hcs

/-! ## The entry -/

/-- The prologue's leaf: frame registers set, only the frame written. -/
def entryOK (lS : SState) : Bool :=
  lS.reg 2 == .ptr 0 0 && lS.reg 8 == .ptr 0 400 && lS.reg 9 == .ptr 1 0 &&
    calleeVars.all (fun i => lS.reg i == .var i) && lS.mem.all (fun w => w.r == 0) &&
    lS.regions == regionsR

/-- The frame invariant after the prologue. -/
theorem entry_fr {m m1 : Machine} (n : Nums m) (e : Entry m) {lS : SState}
    (hm1 : Match (envC m m c0) lS m1) (hfr : SameOutside (InWritable (envC m m c0) S0) m m1)
    (hp1 : Preserved m m1) (hk : entryOK lS = true)
    (hsv : ∀ k < 10, ∀ t < 8,
      F2.wview lS.mem 0 (392 - 8 * k + t) = some (.var (savedRegs.getD k 0), t)) :
    Fr m m1 := by
  have ef := envC_facts m m c0
  have hk' := hk
  simp only [entryOK, Bool.and_eq_true, beq_iff_eq] at hk'
  obtain ⟨⟨⟨⟨⟨k2, k8⟩, k9⟩, kv⟩, kw⟩, hreg⟩ := hk'
  have g := reg_eval hm1
  have hfm : ∀ j < 400, m1.mem (frB m + BitVec.ofNat 64 j) =
      some (memByte (envC m m c0) lS.mem 0 j) := fun j hj => by
    have := hm1.mem 0 j (by rw [hreg]; decide) (by rw [ef.s0]; exact hj)
    rwa [ef.b0] at this
  refine ⟨?_, ?_, ?_, fun i hi => ?_, fun k hk10 t ht => ?_, fun j hj => hp1.1 _ (e.stack.2.2.2 j hj),
    fun a ha => ?_⟩
  · rw [g 2]; show (lS.reg 2).eval _ = _; rw [k2]; simp [Sym.eval, ef.b0]
  · rw [g 8]; show (lS.reg 8).eval _ = _; rw [k8]; simp [Sym.eval, ef.b0, frB, BitVec.sub_add_cancel]
  · rw [g 9]; show (lS.reg 9).eval _ = _; rw [k9]; simp [Sym.eval, ef.b1]
  · rw [g i, eq_of_beq (List.all_eq_true.mp kv i.val hi)]; exact ef.v i
  · rw [hfm _ (by omega), mb_some (hsv k hk10 t ht)]
    have hlt : savedRegs.getD k 0 < 32 := by revert k; decide
    have hfin : (Fin.ofNat 32 (savedRegs.getD k 0) : Fin 32) = ⟨savedRegs.getD k 0, hlt⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hlt)
    rw [Sym.eval_var, show savedRegs.getD k 0 = (⟨savedRegs.getD k 0, hlt⟩ : Fin 32).val from rfl,
      ef.v, savedVal, hfin]
  · by_cases hw : InWritable (envC m m c0) S0 a
    · rcases n.writable hw with h | h
      · exfalso; apply ha
        unfold InRange at h ⊢
        have h1 := n.fr; have h2 := n.sp512; have h3 := n.spLo; unfold Layout.ramLo at h3
        omega
      · obtain ⟨r, R, j, hR, hwr, hj, rfl⟩ := hw
        have hr := (List.getElem?_eq_some_iff.mp hR).1
        simp only [S0, entryState, regionsR, List.length_cons, List.length_nil] at hr
        have hr1 : r = 1 := by
          rcases Nat.lt_or_ge r 1 with h0 | h0
          · exfalso; apply ha
            have : r = 0 := by omega
            subst this
            rw [ef.b0] at h ⊢; rw [ef.s0] at hj
            unfold InRange at h ⊢
            have h1 := n.fr; have h2 := n.sp512; have h3 := n.spLo; have h4 := n.frj (j := j) (by omega)
            unfold Layout.ramLo at h3
            omega
          · rcases Nat.lt_or_ge r 2 with h1 | h1
            · omega
            · exfalso
              have : r = 2 := by omega
              subst this
              have := (List.getElem?_eq_some_iff.mp hR).2
              simp [S0, entryState, regionsR] at this
              subst this; simp [inputR] at hwr
        subst hr1
        rw [hm1.mem 1 j (by rw [hreg]; decide) hj, memByte_nowrite (fun w hw => by
          have := List.all_eq_true.mp kw w hw; simp only [beq_iff_eq] at this
          simp [Write.covers, this]), ef.by0]
        have := e.resP j (by rw [ef.s1] at hj; exact hj)
        rw [← ef.b1] at this
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp this
        rw [hb]; rfl
    · exact hfr a hw

theorem entry_match {m : Machine} (n : Nums m) (e : Entry m) : Match (envC m m c0) S0 m := by
  have ef := envC_facts m m c0
  refine F2.entry_match_vars (by decide) (fun i hi s hs => ?_) (fun r j hr hj => ?_) (fun w hw => ?_)
  · simp only [ov] at hs
    by_cases e2 : i.val = 2
    · simp only [e2, if_true, Option.some.injEq] at hs; subst hs
      rw [show i = 2 from Fin.ext e2]
      show (Sym.ptr 0 400).eval (envC m m c0) = _
      simp [Sym.eval, ef.b0, frB, BitVec.sub_add_cancel]
    by_cases e10 : i.val = 10
    · simp [e10] at hs; subst hs
      rw [show i = 10 from Fin.ext e10]
      show (Sym.ptr 1 0).eval (envC m m c0) = _
      simp [Sym.eval, ef.b1]
    by_cases e11 : i.val = 11
    · simp [e11] at hs; subst hs
      rw [show i = 11 from Fin.ext e11]
      show (Sym.ptr 2 0).eval (envC m m c0) = _
      simp [Sym.eval, ef.b2]
    simp [e2, e10, e11] at hs
  · show (m.mem ((envC m m c0).base r + BitVec.ofNat 64 j)).isSome
    simp only [regionsR, List.length_cons, List.length_nil] at hr
    have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    change j < (envC m m c0).size r at hj
    rcases hr3 with rfl | rfl | rfl
    · rw [ef.b0]; rw [ef.s0] at hj
      rw [n.fr_stack hj]; exact e.stack.2.2.2 _ (by omega)
    · rw [ef.b1]; rw [ef.s1] at hj; exact e.resP j hj
    · rw [ef.b2]; rw [ef.s2] at hj; exact e.inP j hj
  · simp at hw

theorem f6_spec : Spec zesuImage entry 2178 Pre Post := by
  intro m hpc hpre
  have e := Entry.of_pre hpre
  have n := e.nums
  have ef := envC_facts m m c0
  refine run_reaches' runE (n.wf m c0 ov []) (entry_match n e) hpc e.ro fun l hl hcs => ?_
  simp only [runE_leaves, List.mem_singleton] at hl
  subst hl
  refine ⟨by simp, by decide, fun m1 hm1 hex hfr hp1 => ?_⟩
  have hc1 := entry_fr n e hm1 hfr hp1 (by decide) (by decide)
  have g := reg_eval hm1
  have hlen := n.inHi; unfold Layout.inputHi at hlen
  obtain ⟨hpre1, hpost⟩ := dcall n e hc1 (off := 8) (o := 0) (r := (m.reg 12).toNat) (by decide)
    (by decide) (by omega)
    (by rw [g 10]; show (Sym.ptr 0 8).eval _ = _; simp [Sym.eval, ef.b0])
    (by rw [g 11]; show (Sym.ptr 2 0).eval _ = _; simp [Sym.eval, ef.b2])
    (by rw [g 12]; show (Sym.var 12).eval _ = _; exact (var_eval 12).trans (by simp))
    (by unfold RetAligned; rw [g 1]
        show (BitVec.ofNat 64 ret0 &&& ~~~(1 : Word)).toNat % 4 = 0; decide)
  have hcall := Reaches.preserve (F2.f2_spec m1 (by simpa [F2.entry] using hex) hpre1)
  refine (Reaches.trans (b₂ := 2087) hcall fun m2 ⟨hp, hpr⟩ => ?_).mono (by decide) fun _ h => h
  obtain ⟨hfr2, hpc2, -, hout, -⟩ := hpost m2 hp hpr
  refine after0 n e ⟨hfr2, by simp, hout⟩ ?_
  rw [hpc2, g 1]; show (BitVec.ofNat 64 ret0 &&& ~~~(1 : Word)).toNat = ret0; decide

/--
info: 'ZesuExec.Fn.F6.f6_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f6_spec

end ZesuExec.Fn.F6
