import ZesuExec.Fn.Scratch.AllocVc
import ZesuExec.Sail.Run

/-!
# `scratch_arena.alloc` (`0x800db7a4`) meets `AllocPreS`/`AllocPostS`

Thirteen leaves over the five cuts of `Fn/Scratch/AllocVc.lean`: from the entry, to the request
of a new chunk (null `chunks`) or after the null test; after it, the fast return, and the
request when the bump does not fit (or its result is null, which `Pre` rules out); the four
size choices of the request, each calling the child's `alloc`; after the call, null or the new
chunk; the new chunk's fast return (the other branch is infeasible: `newSize` leaves room).
End theorems `SA.sa_spec` (over `Alloc.contract`) and `SA.sa_sail`; `sa_spec_of` for any
`AllocContract`.
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc
open ZesuExec.Fn.Alloc (wf_regions written_only pres_of)

/-! ## Leaf helpers -/

/-- A byte of region `r` no write of the leaf covers keeps the cut machine's value. -/
theorem byte_kept {env : Env} {S S' : SState} {m m' : Machine} (hm : Match env S m)
    (hS : S.mem = []) (hm' : Match env S' m') (hr : S'.regions = S.regions) {r j : Nat}
    (hrl : r < S.regions.length) (hj : j < env.size r) (hnc : ∀ w ∈ S'.mem, w.covers r j = false) :
    m'.mem (env.base r + BitVec.ofNat 64 j) = m.mem (env.base r + BitVec.ofNat 64 j) := by
  rw [hm'.mem r j (hr ▸ hrl) hj, hm.mem r j hrl hj, hS]
  have : S'.mem.find? (·.covers r j) = none := List.find?_eq_none.mpr fun w hw => by
    simp [hnc w hw]
  simp [memByte, this]

/-- Addresses a leaf wrote lie in the ranges `rs` (region, from, to) it may write. -/
theorem written_sub {env : Env} {S' : SState} {Q : Word → Prop} (rs : List (Nat × Nat × Nat))
    (hw : S'.mem.all (fun w => rs.any (fun q => w.r == q.1 && decide (q.2.1 ≤ w.off) &&
      decide (w.off + w.n ≤ q.2.2))) = true)
    (hq : ∀ q ∈ rs, ∀ j, q.2.1 ≤ j → j < q.2.2 → Q (env.base q.1 + BitVec.ofNat 64 j)) :
    ∀ a, (∃ w ∈ S'.mem, ∃ j, w.off ≤ j ∧ j < w.off + w.n ∧ a = env.base w.r + BitVec.ofNat 64 j) →
      Q a := by
  rintro a ⟨w, hwm, j, hj1, hj2, rfl⟩
  obtain ⟨q, hq', hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hw w hwm)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨hr, h1⟩, h2⟩ := hc
  rw [hr]; exact hq q hq' j (by omega) (by omega)

/-- The value of an initial word or byte of the cut state, from the cut machine. -/
theorem init_val {env : Env} {S : SState} {m : Machine} (hwf : Env.WF env S) (hm : Match env S m)
    {r off n : Nat} {R : Region} (hR : S.regions[r]? = some R) (hb : off + n ≤ env.size r)
    (hrc : readConst S r off n = .init r off n) {v : Word}
    (hv : m.load (env.base r + BitVec.ofNat 64 off) n = some v) : (Sym.init r off n).eval env = v := by
  have := load_cst hwf hm hR hb; rw [hrc, hv] at this; exact (Option.some.inj this).symm

theorem bytes1 (env : Env) (x : Sym) (h : (x.eval env).toNat < 256) :
    (Sym.bytes x 0 1).eval env = x.eval env := by
  apply BitVec.eq_of_toNat_eq
  simp [Sym.eval, byteList, Machine.ofBytesLE, byteOf]
  omega

theorem and63 (v : Word) (h : v.toNat < 64) : v &&& 63 = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (63 : Word).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Bytes the entry machine holds stay present while changes stay in the frame, which is
present. -/
theorem pres_from {e m : Machine} {R : Word → Prop} (hso : SameOutside R e m)
    (hR : ∀ a, R a → (m.mem a).isSome) : ∀ a, (e.mem a).isSome → (m.mem a).isSome := by
  intro a ha
  by_cases h : R a
  · exact hR a h
  · rw [hso a h]; exact ha

theorem fr80_present {e m : Machine} (hp : Present m (e.reg 2 - 80) 80) {a : Word} (h : Fr80 e a) :
    (m.mem a).isSome := by
  unfold Fr80 InRange at h
  generalize e.reg 2 - 80 = b at *
  have := hp (a.toNat - b.toNat) (by omega)
  rwa [show b + BitVec.ofNat 64 (a.toNat - b.toNat) = a by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega] at this

/-- `Heap L` survives changes outside `Priv L` that keep the live blocks present. -/
theorem heap_of {A : AllocContract zesuImage} {L : List (Word × Nat)} {e m : Machine}
    (h : A.Heap L e) {R : Word → Prop} (hso : SameOutside R e m) (hR : ∀ a, R a → ¬ A.Priv L a)
    (hp : ∀ a, (e.mem a).isSome → (m.mem a).isSome) : A.Heap L m :=
  A.heap_frame L e m h (fun a ha => hso a fun hr => hR a hr ha)
    fun b hb j hj => hp _ (((A.live_ok L e h).2 b hb).2 j hj)

/-! ## Entry leaves -/

theorem envE (g : SigA) : (envA shapeAE g g.e).base 0 = g.e.reg 2 - 64 ∧
    (envA shapeAE g g.e).base 1 = g.e.reg 10 ∧ (envA shapeAE g g.e).size 0 = 64 ∧
    (envA shapeAE g g.e).size 1 = 32 := by
  simp [envA, entryEnv, Env.base, Env.size, shapeAE]

/-- What an entry leaf leaves: the prologue's registers and frame, changes in the frame only,
the 80 bytes below `sp` present, and `chunks`. -/
theorem entry_exit {g : SigA} {l : Leaf} {m' : Machine} (hA : AE g g.e)
    (hm' : Match (envA shapeAE g g.e) l.S m') (hr : l.S.regions = SAE.regions)
    (hso : SameOutside (InWritable (envA shapeAE g g.e) SAE) g.e m')
    (hregs : l.S.reg 2 = .ptr 0 0 ∧ l.S.reg 8 = .ptr 0 64 ∧ l.S.reg 9 = .var 11 ∧
      l.S.reg 18 = .var 12 ∧ l.S.reg 19 = .ptr 1 0 ∧
      ∀ i ∈ [22, 23, 24, 25, 26, 27], l.S.reg i = .var i)
    (hrc : ∀ p ∈ savedRegs, readConst l.S 0 p.1 8 = .var p.2.val)
    (hrb : readConst l.S 0 5 1 = .bytes (.bin .and (.var 12) (.lit 63)) 0 1)
    (hw : l.S.mem.all (fun w => [(0, 0, 64)].any (fun q => w.r == q.1 &&
      decide (q.2.1 ≤ w.off) && decide (w.off + w.n ≤ q.2.2))) = true) :
    EntryS g.A g.L g.e ∧ FrRegs g.e m' ∧ FrMem g.e m' ∧ SameOutside (Fr64 g.e) g.e m' ∧
      Present m' (g.e.reg 2 - 80) 80 ∧
      (Sym.init 1 16 8).eval (envA shapeAE g g.e) = chunks g.e := by
  have hcut := SA.cut_800db7a4 g g.e hA
  have hwf : Env.WF (envA shapeAE g g.e) SAE := hcut.1
  have hm : Match (envA shapeAE g g.e) SAE g.e := hcut.2.1
  have E := EntryS.of hA.2.2
  have hwf' := wf_regions hwf hr
  obtain ⟨b0, b1, s0, s1⟩ := envE g
  have hv := envA_var shapeAE g g.e
  obtain ⟨h2, h8, h9, h18, h19, hk⟩ := hregs
  refine ⟨E, ⟨?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, ⟨fun p hp => ?_, ?_⟩, fun a ha => ?_,
    fun j hj => ?_, ?_⟩
  · rw [Match.reg_eq hm' 2 2 rfl, h2]; simp [Sym.eval, b0]
  · rw [Match.reg_eq hm' 8 8 rfl, h8]; simp [Sym.eval, b0]; bv_omega
  · rw [Match.reg_eq hm' 9 9 rfl, h9, Sym.eval_var]; exact hv 11
  · rw [Match.reg_eq hm' 18 18 rfl, h18, Sym.eval_var]; exact hv 12
  · rw [Match.reg_eq hm' 19 19 rfl, h19]; simp [Sym.eval, b1]
  · rw [Match.reg_eq hm' i i.val rfl, hk i.val hi, Sym.eval_var]; exact hv i
  · have hb : p.1 + 8 ≤ 64 := by revert hp; revert p; decide
    have := load_cst hwf' hm' (r := 0) (off := p.1) (n := 8) (R := frame64R) (by rw [hr]; rfl)
      (by rw [s0]; exact hb)
    rw [hrc p hp, b0, Sym.eval_var] at this
    rw [this]; congr 1; exact hv p.2
  · have := load_cst hwf' hm' (r := 0) (off := 5) (n := 1) (R := frame64R) (by rw [hr]; rfl)
      (by rw [s0]; decide)
    have hv12 : (envA shapeAE g g.e).vars 12 = g.e.reg 12 := hv 12
    have hk := E.k64
    rw [hrb, b0] at this
    rw [this, bytes1 _ _ ?_] <;>
      simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval, hv12] <;>
      rw [show BitVec.ofNat 64 63 = (63 : Word) from rfl, and63 _ hk]
    omega
  · have hwo := written_only hm rfl hm' hr hso
    refine hwo a fun hw' => ha ?_
    refine written_sub [(0, 0, 64)] hw (fun q hq j _ hj => ?_) a hw'
    simp only [List.mem_singleton] at hq; subst hq
    obtain ⟨h64, -, -, hlo, hhi⟩ := sp_facts E
    show Fr64 g.e (_ + _); rw [b0]
    unfold Layout.ramHi at hhi
    exact inRange_add (by omega) hj
  · exact pres_of hm' hr hso _ (by simpa using E.stack.2.2.2 j hj)
  · have := word_cst hwf hm (r := 1) (off := 16) (R := arenaR) rfl (by rw [s1]; decide)
    rw [b1, show readConst SAE 1 16 8 = .init 1 16 8 by decide] at this
    rw [← this]; rfl

theorem SA.leaf_800db7a4_0 :
    LeafGoal SA.plan SA.plan.cuts[0]! (SA.plan.leaves 0x800db7a4)[0]! := by
  leaf_intro
  intro g m hA hc
  obtain ⟨rfl, -, hpre⟩ := id hA
  refine ⟨by simp, Nat.le_of_ble_eq_true rfl, fun m' hm' he hso => ?_⟩
  obtain ⟨E, hfr, hfm, hso', hp, hch⟩ := entry_exit hA hm' (by decide) hso
    (by decide) (by decide) (by decide) (by decide)
  have h0 : chunks g.e = 0 := by
    have := hc _ (List.mem_singleton_self _)
    simp only [SBool.eval, Sym.eval_lit, beq_iff_eq] at this
    rw [← hch, this]; rfl
  exact ExitGoal.at_cut rfl ⟨cAS, by simp [SA.plan, saPlan], he,
    ⟨hpre, he, hfr, hfm, fun h => h.1 h0, hso', hp⟩, Nat.le_of_ble_eq_true rfl⟩

theorem SA.leaf_800db7a4_1 :
    LeafGoal SA.plan SA.plan.cuts[0]! (SA.plan.leaves 0x800db7a4)[1]! := by
  leaf_intro
  intro g m hA hc
  obtain ⟨rfl, -, hpre⟩ := id hA
  refine ⟨by simp, Nat.le_of_ble_eq_true rfl, fun m' hm' he hso => ?_⟩
  obtain ⟨E, hfr, hfm, hso', hp, hch⟩ := entry_exit hA hm' (by decide) hso
    (by decide) (by decide) (by decide) (by decide)
  have hne : chunks g.e ≠ 0 := by
    have := hc _ (List.mem_singleton_self _)
    simp only [SBool.eval, Sym.eval_lit, bne_iff_ne, ne_eq] at this
    rw [← hch]; exact this
  exact ExitGoal.at_cut rfl ⟨cAJ, by simp [SA.plan, saPlan], he,
    ⟨hpre, he, hfr, hfm, by rw [Match.reg_eq hm' 10 10 rfl]; exact hch, hne, hso', hp⟩,
    Nat.le_of_ble_eq_true rfl⟩

/-! ## Helpers for the cuts inside the frame -/

def maskS : Sym := .bin .sll (.lit 18446744073709551615) (.var 18)
def padS : Sym := .bin .xor maskS (.lit 18446744073709551615)

theorem eval_align1 (env : Env) (x : Sym) :
    (Sym.bin .and (.bin .add x padS) maskS).eval env = alignUp (x.eval env) (env.vars 18) := by
  simp only [Sym.eval, BinOp.eval, alignUp, maskW, padS, maskS]
  rw [show BitVec.ofNat 64 18446744073709551615 = (-1 : Word) from rfl]

theorem eval_align2 (env : Env) (a b : Sym) :
    (Sym.bin .and (.bin .add a (.bin .add b padS)) maskS).eval env =
      alignUp (b.eval env + a.eval env) (env.vars 18) := by
  have := eval_align1 env (.bin .add b a)
  simp only [Sym.eval, BinOp.eval] at this ⊢
  rw [← this]; congr 1; ac_rfl

/-- The saved registers, read from the frame of a cut state. -/
theorem saved_val {g : SigA} {env : Env} {S : SState} {m : Machine} (hwf : Env.WF env S)
    (hm : Match env S m) (hR0 : S.regions[0]? = some frame64R) (hb0 : env.base 0 = g.e.reg 2 - 64)
    (hs0 : env.size 0 = 64) (hrc : ∀ p ∈ savedRegs, readConst S 0 p.1 8 = .init 0 p.1 8)
    (hfm : FrMem g.e m) : ∀ p ∈ savedRegs, (Sym.init 0 p.1 8).eval env = g.e.reg p.2 := by
  intro p hp
  have hb : p.1 + 8 ≤ 64 := by revert hp; revert p; decide
  exact init_val hwf hm hR0 (by rw [hs0]; exact hb) (hrc p hp) (by rw [hb0]; exact hfm.1 p hp)

/-- A leaf from a cut inside the frame that restores the saved registers returns. -/
theorem returns_in {g : SigA} {env : Env} {S' : SState} {m m' : Machine}
    (hsv : ∀ p ∈ savedRegs, (Sym.init 0 p.1 8).eval env = g.e.reg p.2)
    (hb0 : env.base 0 = g.e.reg 2 - 64) (hfr : FrRegs g.e m) (hv : ∀ i : Fin 32, env.vars i = m.reg i)
    (hm' : Match env S' m')
    (hregs : S'.reg 2 = .ptr 0 64 ∧ (∀ p ∈ savedRegs, S'.reg p.2.val = .init 0 p.1 8) ∧
      ∀ i ∈ [22, 23, 24, 25, 26, 27], S'.reg i = .var i)
    (hpc : m'.pc = (Sym.bin .and (.init 0 56 8) (.lit 18446744073709551614)).eval env) :
    Returns g.e m' := by
  obtain ⟨h2, hs, hk⟩ := hregs
  have sv : ∀ p ∈ savedRegs, m'.reg p.2 = g.e.reg p.2 := fun p hp => by
    rw [Match.reg_eq hm' p.2 p.2.val rfl, hs p hp, hsv p hp]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hpc]; simp only [Sym.eval_bin, Sym.eval_lit, BinOp.eval]
    rw [hsv (0x38, 1) (by decide)]; rfl
  simp only [calleeSaved, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Match.reg_eq hm' 2 2 rfl, h2]; simp [Sym.eval, hb0]; bv_omega
  · exact sv (0x30, 8) (by decide)
  · exact sv (0x28, 9) (by decide)
  · exact sv (0x20, 18) (by decide)
  · exact sv (0x18, 19) (by decide)
  · exact sv (0x10, 20) (by decide)
  · exact sv (8, 21) (by decide)
  all_goals
    rw [Match.reg_eq hm' _ _ rfl, hk _ (by decide), Sym.eval_var, hv]
    exact hfr.2.2.2.2.2 _ (by decide)

/-- The prologue's frame survives a leaf that writes no saved byte and keeps the prologue's
registers. -/
theorem keep_fr {g : SigA} {env : Env} {S S' : SState} {m m' : Machine} (hm : Match env S m)
    (hS : S.mem = []) (hm' : Match env S' m') (hr : S'.regions = S.regions)
    (hR0 : 0 < S.regions.length) (hb0 : env.base 0 = g.e.reg 2 - 64) (hs0 : env.size 0 = 64)
    (hw0 : S'.mem.all (fun w => w.r != 0 || (decide (6 ≤ w.off) && decide (w.off + w.n ≤ 8))) = true)
    (hregs : ∀ i ∈ [2, 8, 9, 18, 19, 22, 23, 24, 25, 26, 27], S'.reg i = S.reg i)
    (hfr : FrRegs g.e m) (hfm : FrMem g.e m) :
    FrRegs g.e m' ∧ FrMem g.e m' := by
  have rk : ∀ i : Fin 32, i.val ∈ [2, 8, 9, 18, 19, 22, 23, 24, 25, 26, 27] → m'.reg i = m.reg i :=
    fun i hi => by rw [Match.reg_eq hm' i i.val rfl, hregs _ hi, ← Match.reg_eq hm i i.val rfl]
  have kept : ∀ j, (j = 5 ∨ (8 ≤ j ∧ j < 64)) →
      m'.mem (g.e.reg 2 - 64 + BitVec.ofNat 64 j) = m.mem (g.e.reg 2 - 64 + BitVec.ofNat 64 j) := by
    intro j hj
    rw [← hb0]
    refine byte_kept hm hS hm' hr hR0 (by rw [hs0]; omega) fun w hw => ?_
    have := List.all_eq_true.mp hw0 w hw
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [Write.covers, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, decide_eq_false_iff_not,
      Nat.not_le, Nat.not_lt]
    omega
  obtain ⟨r2, r8, r9, r18, r19, rk'⟩ := hfr
  refine ⟨⟨by rw [rk 2 (by decide)]; exact r2, by rw [rk 8 (by decide)]; exact r8,
    by rw [rk 9 (by decide)]; exact r9, by rw [rk 18 (by decide)]; exact r18,
    by rw [rk 19 (by decide)]; exact r19, fun i hi => ?_⟩, fun p hp => ?_, ?_⟩
  · rw [rk i (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi ⊢
                 rcases hi with h | h | h | h | h | h <;> simp [h])]
    exact rk' i hi
  · have hb : 8 ≤ p.1 ∧ p.1 + 8 ≤ 64 := by revert hp; revert p; decide
    rw [load_congr fun t ht => ?_]; exact hfm.1 p hp
    rw [show g.e.reg 2 - 64 + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 t =
      g.e.reg 2 - 64 + BitVec.ofNat 64 (p.1 + t) by bv_omega]
    exact kept _ (.inr ⟨by omega, by omega⟩)
  · rw [load_congr fun t ht => ?_]; exact hfm.2
    rw [show g.e.reg 2 - 64 + BitVec.ofNat 64 5 + BitVec.ofNat 64 t =
      g.e.reg 2 - 64 + BitVec.ofNat 64 5 by bv_omega]
    exact kept _ (.inl rfl)

/-- The return target is a valid `jalr` target. -/
theorem ret_ok {g : SigA} {env : Env}
    (hsv : ∀ p ∈ savedRegs, (Sym.init 0 p.1 8).eval env = g.e.reg p.2) (hra : RetAligned g.e) :
    (Oblig.aligned (.bin .and (.init 0 56 8) (.lit 18446744073709551614)) 4).holds env := by
  simp only [Oblig.holds, Sym.eval_bin, Sym.eval_lit, BinOp.eval]
  rw [hsv (0x38, 1) (by decide)]; exact hra

theorem eval_add (env : Env) (a b : Sym) : (Sym.bin .add a b).eval env = a.eval env + b.eval env :=
  rfl

theorem eval_sub (env : Env) (a b : Sym) : (Sym.bin .sub a b).eval env = a.eval env - b.eval env :=
  rfl

theorem fr64_in {A : AllocContract zesuImage} {L : List (Word × Nat)} {e : Machine}
    (E : EntryS A L e) {j : Nat} (hj : j < 64) : Fr64 e (e.reg 2 - 64 + BitVec.ofNat 64 j) := by
  obtain ⟨h64, -, -, hlo, hhi⟩ := sp_facts E
  unfold Layout.ramHi at hhi
  exact inRange_add (by omega) hj

/-- The newest chunk's numbers: no wrap anywhere. -/
theorem chunk_arith {A : AllocContract zesuImage} {L : List (Word × Nat)} {e : Machine}
    (E : EntryS A L e) (hne : chunks e ≠ 0) :
    (chunks e + used e).toNat = (chunks e).toNat + (used e).toNat ∧
    (chunks e + cap e).toNat = (chunks e).toNat + (cap e).toNat ∧
    Layout.ramLo ≤ (chunks e).toNat ∧ (used e).toNat ≤ (cap e).toNat ∧
    (chunks e).toNat + (cap e).toNat ≤ Layout.ramHi ∧ 2 ^ (e.reg 12).toNat ≤ 2 ^ 63 := by
  obtain ⟨hr, -, hu, hc, -⟩ := E.chunk hne
  have hk := E.k64
  unfold RamRange at hr; rw [BitVec.le_def] at hu
  unfold Layout.ramHi Layout.ramLo at *
  have hp : 2 ^ (e.reg 12).toNat ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨?_, ?_, hr.1, hu, hc, hp⟩ <;> (rw [BitVec.toNat_add]; omega)

/-! ## Leaves after the null test -/

theorem j_vals {g : SigA} {m : Machine} (hA : AJ g m) :
    EntryS g.A g.L g.e ∧ (envA shapeAJ g m).base 0 = g.e.reg 2 - 64 ∧
    (envA shapeAJ g m).size 0 = 64 ∧ (envA shapeAJ g m).base 2 = chunks g.e + 8 ∧
    (Sym.ptr 2 (-8)).eval (envA shapeAJ g m) = chunks g.e ∧
    (Sym.init 2 0 8).eval (envA shapeAJ g m) = cap g.e ∧
    (Sym.init 2 8 8).eval (envA shapeAJ g m) = used g.e ∧
    (envA shapeAJ g m).vars 9 = g.e.reg 11 ∧ (envA shapeAJ g m).vars 18 = g.e.reg 12 ∧
    ∀ p ∈ savedRegs, (Sym.init 0 p.1 8).eval (envA shapeAJ g m) = g.e.reg p.2 := by
  have hcut := SA.cut_800db7e4 g m hA
  have hwf : Env.WF (envA shapeAJ g m) SAJ := hcut.1
  have hm : Match (envA shapeAJ g m) SAJ m := hcut.2.1
  obtain ⟨hpre, -, hfr, hfm, h10, hne, hso, -⟩ := hA
  have E := EntryS.of hpre
  have b0 : (envA shapeAJ g m).base 0 = g.e.reg 2 - 64 := by
    rw [← hfr.1]; simp [envA, entryEnv, Env.base, shapeAJ, shapeIn]
  have b2 : (envA shapeAJ g m).base 2 = chunks g.e + 8 := by
    rw [← h10]; simp [envA, entryEnv, Env.base, shapeAJ, shapeIn]
  have s0 : (envA shapeAJ g m).size 0 = 64 := by simp [envA, entryEnv, Env.size, shapeAJ, shapeIn]
  have s2 : (envA shapeAJ g m).size 2 = 16 := by simp [envA, entryEnv, Env.size, shapeAJ, shapeIn]
  have hv := envA_var shapeAJ g m
  have hc : m.load (chunks g.e + 8) 8 = g.e.load (chunks g.e + 8) 8 :=
    load_congr fun t ht => hdr_mem E hne hso (by omega)
  have hu : m.load (chunks g.e + 16) 8 = g.e.load (chunks g.e + 16) 8 :=
    load_congr fun t ht => by
      rw [show chunks g.e + 16 + BitVec.ofNat 64 t = chunks g.e + 8 + BitVec.ofNat 64 (8 + t) by
        bv_omega]
      exact hdr_mem E hne hso (by omega)
  refine ⟨E, b0, s0, b2, by simp [Sym.eval, b2]; bv_omega, ?_, ?_, (hv 9).trans hfr.2.2.1,
    (hv 18).trans hfr.2.2.2.1, saved_val hwf hm rfl b0 s0 (by decide) hfm⟩
  · have hl := load_cst hwf hm (r := 2) (off := 0) (n := 8) (R := capR) rfl (by rw [s2]; decide)
    rw [b2, show readConst SAJ 2 0 8 = .init 2 0 8 by decide,
      show chunks g.e + 8 + BitVec.ofNat 64 0 = chunks g.e + 8 by bv_omega] at hl
    show _ = (g.e.load (chunks g.e + 8) 8).getD 0
    rw [← hc, hl]; rfl
  · have hl := load_cst hwf hm (r := 2) (off := 8) (n := 8) (R := capR) rfl (by rw [s2]; decide)
    rw [b2, show readConst SAJ 2 8 8 = .init 2 8 8 by decide,
      show chunks g.e + 8 + BitVec.ofNat 64 8 = chunks g.e + 16 by bv_omega] at hl
    show _ = (g.e.load (chunks g.e + 16) 8).getD 0
    rw [← hu, hl]; rfl

theorem SA.leaf_800db7e4_0 :
    LeafGoal SA.plan SA.plan.cuts[1]! (SA.plan.leaves 0x800db7e4)[0]! := by
  leaf_intro
  intro g m hA hc
  obtain ⟨E, b0, s0, -, hch, hcap, hused, h9, h18, -⟩ := j_vals hA
  have hcut := SA.cut_800db7e4 g m hA
  refine ⟨by simp, Nat.le_of_ble_eq_true rfl, fun m' hm' he hso => ?_⟩
  have c : SBool.eval (envA shapeAJ g m) (.ltu (.bin .add (.ptr 2 (-8)) (.init 2 0 8))
      (.bin .add (.bin .and (.bin .add (.init 2 8 8) (.bin .add (.ptr 2 (-8)) padS)) maskS)
        (.var 9))) = true := hc _ (List.mem_singleton_self _)
  simp only [SBool.eval, eval_add, eval_align2, Sym.eval_var, hch, hcap, hused, h9, h18] at c
  have hnf : ¬ Fits g.e := fun ⟨_, hle⟩ => by
    rw [BitVec.le_def] at hle; simp only [BitVec.ult, decide_eq_true_eq] at c; omega
  obtain ⟨hpre, -, hfr, hfm, -, -, hso0, hp⟩ := hA
  have hwo := written_only hcut.2.1 rfl hm' (by decide) hso
  obtain ⟨hfr', hfm'⟩ := keep_fr hcut.2.1 rfl hm' (by decide) (by decide) b0 s0 (by decide)
    (by decide) hfr hfm
  refine ExitGoal.at_cut rfl ⟨cAS, by simp [SA.plan, saPlan], he,
    ⟨hpre, he, hfr', hfm', hnf, fun a ha => ?_, fun j hj => pres_of hm' (by decide) hso _ (hp j hj)⟩,
    Nat.le_of_ble_eq_true rfl⟩
  rw [hwo a fun hw' => ha ?_]
  · exact hso0 a ha
  exact written_sub [(0, 0, 64)] (by decide) (fun q hq j _ hj => by
    simp only [List.mem_singleton] at hq; subst hq
    show Fr64 g.e ((envA shapeAJ g m).base 0 + _); rw [b0]; exact fr64_in E hj) a hw'

theorem SA.leaf_800db7e4_2 :
    LeafGoal SA.plan SA.plan.cuts[1]! (SA.plan.leaves 0x800db7e4)[2]! := by
  leaf_intro
  intro g m hA hc
  obtain ⟨E, -, -, -, hch, -, hused, -, h18, -⟩ := j_vals hA
  refine ⟨by simp, Nat.le_of_ble_eq_true rfl, fun m' hm' he hso => ?_⟩
  have c : SBool.eval (envA shapeAJ g m)
      (.eq (.bin .and (.bin .add (.init 2 8 8) (.bin .add (.ptr 2 (-8)) padS)) maskS) (.lit 0)) =
      true := hc _ (by simp [padS, maskS])
  simp only [SBool.eval, eval_align2, hch, hused, h18, Sym.eval_lit, beq_iff_eq] at c
  exfalso
  have hne := hA.2.2.2.2.2.1
  obtain ⟨hx, -, hlo, hu, hc', hp⟩ := chunk_arith E hne
  have hb := (alignUp_bounds (chunks g.e + used g.e) (g.e.reg 12) E.k64
    (by rw [hx]; unfold Layout.ramHi at hc'; omega)).1
  rw [c, hx] at hb; unfold Layout.ramLo at hlo; simp at hb; omega

theorem SA.leaf_800db7e4_1 :
    LeafGoal SA.plan SA.plan.cuts[1]! (SA.plan.leaves 0x800db7e4)[1]! := by
  leaf_intro
  intro g m hA hc
  obtain ⟨E, b0, s0, b2, hch, hcap, hused, h9, h18, hsv⟩ := j_vals hA
  have hcut := SA.cut_800db7e4 g m hA
  refine ⟨?_, Nat.le_of_ble_eq_true rfl, fun m' hm' he hso => ?_⟩
  · simp only [List.mem_singleton, forall_eq]; exact ret_ok hsv E.ra
  have c1 : SBool.eval (envA shapeAJ g m) (.geu (.bin .add (.ptr 2 (-8)) (.init 2 0 8))
      (.bin .add (.bin .and (.bin .add (.init 2 8 8) (.bin .add (.ptr 2 (-8)) padS)) maskS)
        (.var 9))) = true := hc _ (by simp [padS, maskS])
  simp only [SBool.eval, eval_add, eval_align2, Sym.eval_var, hch, hcap, hused, h9, h18] at c1
  have hm'' : Match (envA shapeAJ g m) (saRunJ_leaves[1]!).S m' := hm'
  have hso1 : SameOutside (InWritable (envA shapeAJ g m) SAJ) m m' := hso
  have hwf0 : Env.WF (envA shapeAJ g m) SAJ := hcut.1
  have hm0 : Match (envA shapeAJ g m) SAJ m := hcut.2.1
  obtain ⟨hpre, -, hfr, hfm, -, hne, hso0, hp⟩ := hA
  have hfits : Fits g.e := ⟨hne, by
    rw [BitVec.le_def]; simp only [BitVec.ult, Bool.not_eq_true', decide_eq_false_iff_not] at c1
    omega⟩
  have hr : (saRunJ_leaves[1]!).S.regions = SAJ.regions := by decide
  have hwf' := wf_regions hwf0 hr
  have s2 : (envA shapeAJ g m).size 2 = 16 := by simp [envA, entryEnv, Env.size, shapeAJ, shapeIn]
  have hr10 : m'.reg 10 = (Sym.bin .and (.bin .add (.init 2 8 8) (.bin .add (.ptr 2 (-8)) padS))
      maskS).eval (envA shapeAJ g m) := Match.reg_eq hm' 10 10 rfl
  rw [eval_align2, hch, hused, h18] at hr10
  have hw := word_cst hwf' hm'' (r := 2) (off := 8) (R := capR) rfl (by rw [s2]; decide)
  rw [show readConst (saRunJ_leaves[1]!).S 2 8 8 = .bin .sub (.bin .add
      (.bin .and (.bin .add (.init 2 8 8) (.bin .add (.ptr 2 (-8)) padS)) maskS) (.var 9))
      (.ptr 2 (-8)) by decide, b2,
    show chunks g.e + 8 + BitVec.ofNat 64 8 = chunks g.e + 16 by bv_omega] at hw
  rw [eval_sub, eval_add, eval_align2, hch, hused, h18, Sym.eval_var, h9] at hw
  have E' := E
  obtain ⟨hcr, -, -, -, -, -, hcpriv⟩ := E'.chunk hne
  have hwo := written_only hm0 rfl hm'' hr hso1
  have hso' : SameOutside (fun a => InRange (chunks g.e + 16) 8 a ∨ InRange (g.e.reg 2 - 64) 64 a)
      g.e m' := fun a ha => by
    have hsub := written_sub (env := envA shapeAJ g m) (S' := (saRunJ_leaves[1]!).S)
      (Q := fun a => InRange (chunks g.e + 16) 8 a ∨ InRange (g.e.reg 2 - 64) 64 a)
      [(2, 8, 16), (0, 0, 64)] (by decide) (fun q hq j h1 hj => ?_)
    · rw [hwo a fun hw' => ha (hsub a hw')]
      exact hso0 a fun h => ha (.inr h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> dsimp only at h1 hj ⊢
    · left; show InRange _ 8 ((envA shapeAJ g m).base 2 + _); rw [b2]
      unfold InRange; unfold RamRange Layout.ramHi at hcr
      rw [toNat_add_ofNat (by rw [c8 E hne]; omega), c8 E hne,
        show (chunks g.e + 16).toNat = (chunks g.e).toNat + 16 by rw [BitVec.toNat_add]; simp; omega]
      omega
    · right; show Fr64 g.e ((envA shapeAJ g m).base 0 + _); rw [b0]; exact fr64_in E hj
  show AllocPostS g.A g.L g.e m'
  refine ⟨returns_in hsv b0 hfr (envA_var shapeAJ g m) hm'' (by decide) he, fun _ => ⟨hr10, ?_,
    hso', ?_⟩, fun h => absurd hfits h⟩
  · rw [← hr10] at hw; exact hw
  · refine heap_of E.heap hso' (fun a ha hpv => ?_) fun a ha => pres_of hm'' hr hso1 _
      (pres_from hso0 (fun a h => fr80_present hp (fr64_80 E h)) a ha)
    rcases ha with h | h
    · refine hcpriv a ⟨?_, ?_⟩ hpv <;> unfold InRange at h <;> unfold RamRange Layout.ramHi at hcr <;>
        rw [c8 E hne] <;>
        rw [show (chunks g.e + 16).toNat = (chunks g.e).toNat + 16 by
          rw [BitVec.toNat_add]; simp; omega] at h <;> omega
    · exact E.priv a (.inr (fr64_80 E h)) hpv

/-! ## The request of a new chunk -/

theorem rodata_low {a b : Nat} (h : zesuImage.rodataByte? a = some b) : a < Layout.ramLo := by
  have := zesu_rodata_range h; unfold Layout.rodataHi at this; unfold Layout.ramLo; omega

/-- The saved frame survives byte-for-byte equality at the saved offsets. -/
theorem frMem_congr {e m m2 : Machine} (hfm : FrMem e m)
    (h : ∀ j, (j = 5 ∨ (8 ≤ j ∧ j < 64)) →
      m2.mem (e.reg 2 - 64 + BitVec.ofNat 64 j) = m.mem (e.reg 2 - 64 + BitVec.ofNat 64 j)) :
    FrMem e m2 := by
  refine ⟨fun p hp => ?_, ?_⟩
  · have hb : 8 ≤ p.1 ∧ p.1 + 8 ≤ 64 := by revert hp; revert p; decide
    rw [load_congr fun t ht => ?_]; exact hfm.1 p hp
    rw [show e.reg 2 - 64 + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 t =
      e.reg 2 - 64 + BitVec.ofNat 64 (p.1 + t) by bv_omega]
    exact h _ (.inr ⟨by omega, by omega⟩)
  · rw [load_congr fun t ht => ?_]; exact hfm.2
    rw [show e.reg 2 - 64 + BitVec.ofNat 64 5 + BitVec.ofNat 64 t =
      e.reg 2 - 64 + BitVec.ofNat 64 5 by bv_omega]
    exact h _ (.inl rfl)

/-- The saved bytes are neither the child's memory nor the child's frame. -/
theorem saved_out {A : AllocContract zesuImage} {L : List (Word × Nat)} {e : Machine}
    (E : EntryS A L e) {j : Nat} (hj : j = 5 ∨ (8 ≤ j ∧ j < 64)) :
    ¬ (A.Priv L (e.reg 2 - 64 + BitVec.ofNat 64 j) ∨
      InRange (e.reg 2 - 64 - 16) 16 (e.reg 2 - 64 + BitVec.ofNat 64 j)) := by
  have hin := fr64_in E (j := j) (by omega)
  rintro (h | h)
  · exact E.priv _ (.inr (fr64_80 E hin)) h
  · obtain ⟨h64, -, -, hlo, -⟩ := sp_facts E
    unfold Fr64 at hin; unfold InRange at hin h
    rw [show (e.reg 2 - 64 - 16).toNat = (e.reg 2).toNat - 80 by
      rw [BitVec.toNat_sub, h64]; simp; unfold Layout.ramLo at hlo; omega] at h
    omega

/-- What the cuts with shape `shapeIn` read: the alignment byte, the arena's words, `len`,
`align` and the saved registers. -/
theorem in_vals {g : SigA} {m : Machine} {R : Word → Prop} (hwf : Env.WF (envA shapeIn g m) SAS)
    (hm : Match (envA shapeIn g m) SAS m) (E : EntryS g.A g.L g.e) (hfr : FrRegs g.e m)
    (hfm : FrMem g.e m) (hso : SameOutside R g.e m) (hR : ∀ a, R a → g.A.Priv g.L a ∨ Fr80 g.e a) :
    (envA shapeIn g m).base 0 = g.e.reg 2 - 64 ∧ (envA shapeIn g m).size 0 = 64 ∧
    (envA shapeIn g m).base 1 = g.e.reg 10 ∧
    (Sym.init 0 5 1).eval (envA shapeIn g m) = g.e.reg 12 ∧
    (Sym.init 1 24 8).eval (envA shapeIn g m) = lastSize g.e ∧
    (Sym.init 1 16 8).eval (envA shapeIn g m) = chunks g.e ∧
    (envA shapeIn g m).vars 9 = g.e.reg 11 ∧ (envA shapeIn g m).vars 18 = g.e.reg 12 ∧
    (envA shapeIn g m).vars 20 = m.reg 20 ∧
    ∀ p ∈ savedRegs, (Sym.init 0 p.1 8).eval (envA shapeIn g m) = g.e.reg p.2 := by
  have b0 : (envA shapeIn g m).base 0 = g.e.reg 2 - 64 := by
    rw [← hfr.1]; simp [envA, entryEnv, Env.base, shapeIn]
  have b1 : (envA shapeIn g m).base 1 = g.e.reg 10 := by
    rw [← hfr.2.2.2.2.1]; simp [envA, entryEnv, Env.base, shapeIn]
  have s0 : (envA shapeIn g m).size 0 = 64 := by simp [envA, entryEnv, Env.size, shapeIn]
  have s1 : (envA shapeIn g m).size 1 = 32 := by simp [envA, entryEnv, Env.size, shapeIn]
  have hv := envA_var shapeIn g m
  have cw : ∀ off, off + 8 ≤ 32 → readConst SAS 1 off 8 = .init 1 off 8 →
      (Sym.init 1 off 8).eval (envA shapeIn g m) = word g.e (g.e.reg 10 + BitVec.ofNat 64 off) := by
    intro off hoff hrc
    have hl := load_cst hwf hm (r := 1) (off := off) (n := 8) (R := arenaR) rfl (by rw [s1]; exact hoff)
    have hc : m.load (g.e.reg 10 + BitVec.ofNat 64 off) 8 =
        g.e.load (g.e.reg 10 + BitVec.ofNat 64 off) 8 :=
      load_congr fun t ht => by
        rw [show g.e.reg 10 + BitVec.ofNat 64 off + BitVec.ofNat 64 t =
          g.e.reg 10 + BitVec.ofNat 64 (off + t) by bv_omega]
        exact ctx_mem E hso hR (by omega)
    rw [b1, hrc] at hl
    unfold word; rw [← hc, hl]; rfl
  have hb := init_val hwf hm (r := 0) (off := 5) (n := 1) (R := frame64R) rfl (by rw [s0]; decide)
    (by decide) (v := g.e.reg 12) (by rw [b0]; exact hfm.2)
  exact ⟨b0, s0, b1, hb, cw 24 (by decide) (by decide), cw 16 (by decide) (by decide),
    (hv 9).trans hfr.2.2.1, (hv 18).trans hfr.2.2.2.1, hv 20,
    saved_val hwf hm rfl b0 s0 (by decide) hfm⟩

def needS : Sym := .bin .add (.bin .add (.var 9) (.bin .sll (.lit 1) (.init 0 5 1))) (.lit 23)
def satS : Sym := .bin .or (.bin .sub (.lit 0) (.bin .sltu (.lit 0) (.bin .srl (.init 1 24 8) (.lit 63))))
  (.bin .sll (.init 1 24 8) (.lit 1))

theorem need_eval {env : Env} {e : Machine} (h9 : env.vars 9 = e.reg 11)
    (hb : (Sym.init 0 5 1).eval env = e.reg 12) (hk : (e.reg 12).toNat < 64) :
    needS.eval env = BitVec.ofNat 64 (needN e) := by
  apply BitVec.eq_of_toNat_eq
  simp only [needS, Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval, h9, hb]
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hk,
    Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  unfold needN
  have : 2 ^ (e.reg 12).toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  simp only [Nat.one_mod, Nat.one_mul]
  omega

theorem sat_eval {env : Env} {e : Machine} (hl : (Sym.init 1 24 8).eval env = lastSize e)
    (h : (lastSize e).toNat < 2 ^ 62) :
    satS.eval env = BitVec.ofNat 64 (2 * (lastSize e).toNat) := by
  have h63 : (lastSize e) >>> 63 = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; simp; omega
  simp only [satS, Sym.eval_bin, Sym.eval_lit, BinOp.eval, hl]
  rw [show (BitVec.ofNat 64 63).toNat % 64 = 63 from rfl, h63]
  simp only [BitVec.ult, show (BitVec.ofNat 64 0 : Word) = 0 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-- A leaf from `0x800db820` that calls the child's `alloc` for `sz = newSize` bytes. -/
theorem slow_call {l : Leaf} (sz : Sym) (hex : l.exit = .call 0x80042494 0x800db87c)
    (hob : l.obligs = []) (hst : l.S.steps ≤ 20) (hr : l.S.regions = SAS.regions)
    (hmem : l.S.mem = []) (h1 : l.S.reg 1 = .lit 0x800db87c) (h11 : l.S.reg 11 = sz)
    (h12 : l.S.reg 12 = .lit 3) (h20 : l.S.reg 20 = sz)
    (hk : ∀ i ∈ [2, 8, 9, 18, 19, 22, 23, 24, 25, 26, 27], l.S.reg i = SAS.reg i)
    (hsz : ∀ g m, AS g m → (∀ b ∈ l.conds, b.eval (envA shapeIn g m) = true) →
      sz.eval (envA shapeIn g m) = BitVec.ofNat 64 (newSize g.e)) :
    LeafGoal saPlan cAS l := by
  intro g m hA hc
  have hcut := SA.cut_800db820 g m hA
  have hwf : Env.WF (envA shapeIn g m) SAS := hcut.1
  have hm : Match (envA shapeIn g m) SAS m := hcut.2.1
  have hs := hsz g m hA hc
  obtain ⟨hpre, -, hfr, hfm, hnf, hso0, hp⟩ := hA
  have E := EntryS.of hpre
  refine ⟨by rw [hob]; simp, by show l.S.steps - 0 ≤ 105; omega, fun m' hm0' he hso0' => ?_⟩
  have hm' : Match (envA shapeIn g m) l.S m' := hm0'
  have hso : SameOutside (InWritable (envA shapeIn g m) SAS) m m' := hso0'
  rw [hex] at he ⊢
  have hmm : m'.mem = m.mem := funext fun a =>
    written_only hm rfl hm' hr hso a (by rintro ⟨w, hw, -⟩; rw [hmem] at hw; cases hw)
  have rk : ∀ i : Fin 32, i.val ∈ [2, 8, 9, 18, 19, 22, 23, 24, 25, 26, 27] → m'.reg i = m.reg i :=
    fun i hi => by rw [Match.reg_eq hm' i i.val rfl, hk _ hi, ← Match.reg_eq hm i i.val rfl]
  have r1 : m'.reg 1 = BitVec.ofNat 64 0x800db87c := by rw [Match.reg_eq hm' 1 1 rfl, h1]; rfl
  have r11 : m'.reg 11 = BitVec.ofNat 64 (newSize g.e) := by rw [Match.reg_eq hm' 11 11 rfl, h11, hs]
  have r12 : m'.reg 12 = BitVec.ofNat 64 3 := by rw [Match.reg_eq hm' 12 12 rfl, h12]; rfl
  have r20 : m'.reg 20 = BitVec.ofNat 64 (newSize g.e) := by rw [Match.reg_eq hm' 20 20 rfl, h20, hs]
  have r2 : m'.reg 2 = g.e.reg 2 - 64 := (rk 2 (by decide)).trans hfr.1
  obtain ⟨h64, h80, hal, hlo, hhi⟩ := sp_facts E
  have hN := newSize_lt E; have h24 := newSize_24 g.e
  have n11 : (m'.reg 11).toNat = newSize g.e := by rw [r11, BitVec.toNat_ofNat]; omega
  have hso' : SameOutside (Fr64 g.e) g.e m' := fun a ha => by rw [hmm]; exact hso0 a ha
  have hpm : ∀ a, (g.e.mem a).isSome → (m'.mem a).isSome := fun a ha => by
    rw [hmm]; exact pres_from hso0 (fun a h => fr80_present hp (fr64_80 E h)) a ha
  have hheap : g.A.Heap g.L m' :=
    heap_of E.heap hso' (fun a h => E.priv a (.inr (fr64_80 E h))) hpm
  have hcf : ∀ a, InRange (m'.reg 2 - 16) 16 a → Fr80 g.e a := fun a ha => by
    rw [r2] at ha; unfold InRange at ha; unfold Fr80 InRange
    rw [show (g.e.reg 2 - 64 - 16).toNat = (g.e.reg 2).toNat - 80 by
      rw [BitVec.toNat_sub, h64]; simp; unfold Layout.ramLo at hlo; omega] at ha
    rw [h80]; omega
  have hstk : StackOk m' 16 := ⟨by rw [r2, h64]; omega, by rw [r2, h64]; unfold Layout.ramLo at *; omega,
    by rw [r2, h64]; omega, fun j hj => by
      rw [hmm, r2, show g.e.reg 2 - 64 - BitVec.ofNat 64 16 + BitVec.ofNat 64 j =
        g.e.reg 2 - 80 + BitVec.ofNat 64 j by bv_omega]
      exact hp j (by omega)⟩
  refine ⟨childAlloc, (), by simp [SA.plan, saPlan], he,
    ⟨hheap, by omega, by omega, by rw [r12]; decide, hstk, by unfold RetAligned; rw [r1]; decide,
      fun a ha => E.priv a (.inr (hcf a ha))⟩, fun m'' hpost => ?_⟩
  obtain ⟨⟨hret, hso2, hout⟩, hpres⟩ := hpost
  have cs : ∀ i : Fin 32, i.val ∈ [2, 8, 9, 18, 19, 22, 23, 24, 25, 26, 27] →
      m''.reg i = m.reg i := fun i hi => by
    rw [hret.2 i (by revert hi; revert i; decide), rk i hi]
  have hpc : m''.pc.toNat = 0x800db87c := by rw [hret.1, r1]; decide
  have hso3 : SameOutside (fun a => g.A.Priv g.L a ∨ Fr80 g.e a) g.e m'' := fun a ha => by
    rw [hso2 a fun h => ha (h.elim .inl fun h => .inr (hcf a h)), hmm]
    exact hso0 a fun h => ha (.inr (fr64_80 E h))
  have hro' : RodataLoaded zesuImage m' := ro_of E hso' fun a h => fr80_ram E (fr64_80 E h)
  obtain ⟨r2', r8', r9', r18', r19', rk'⟩ := hfr
  refine ⟨cAR, by simp [SA.plan, saPlan], rfl, hpc, ⟨hpre, hpc, ⟨?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩,
    frMem_congr hfm fun j hj => ?_, hnf, ?_, hso3, fun j hj => hpres.1 _ (by rw [hmm]; exact hp j hj),
    RodataLoaded.preserved hro' hpres fun _ _ hb => rodata_low hb, ?_⟩, by
      show 53 + 32 ≤ 105 - (l.S.steps - 0); omega⟩
  · rw [cs 2 (by decide)]; exact r2'
  · rw [cs 8 (by decide)]; exact r8'
  · rw [cs 9 (by decide)]; exact r9'
  · rw [cs 18 (by decide)]; exact r18'
  · rw [cs 19 (by decide)]; exact r19'
  · rw [cs i (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi ⊢
                 rcases hi with h | h | h | h | h | h <;> simp [h])]
    exact rk' i hi
  · rw [hso2 _ fun h => saved_out E hj (by rw [r2] at h; exact h), hmm]
  · rw [hret.2 20 (by decide), r20]
  · unfold Out; rw [n11] at hout; exact hout

theorem SA.leaf_800db820_0 :
    LeafGoal SA.plan SA.plan.cuts[2]! (SA.plan.leaves 0x800db820)[0]! := by
  leaf_intro
  refine slow_call satS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fun g m hA hc => ?_
  have hcut := SA.cut_800db820 g m hA
  obtain ⟨hpre, -, hfr, hfm, -, hso0, -⟩ := hA
  have E := EntryS.of hpre
  obtain ⟨-, -, -, hb, hl, -, h9, -, -, -⟩ := in_vals hcut.1 hcut.2.1 E hfr hfm hso0
    fun a h => .inr (fr64_80 E h)
  have c1 : SBool.eval (envA shapeIn g m) (.ne (.init 1 24 8) (.lit 0)) = true := hc _ (by simp)
  have c2 : SBool.eval (envA shapeIn g m) (.ltu needS satS) = true := hc _ (by simp [needS, satS])
  simp only [SBool.eval, Sym.eval_lit, hl, bne_iff_ne, ne_eq] at c1
  simp only [SBool.eval, need_eval h9 hb E.k64, sat_eval hl E.last, BitVec.ult,
    decide_eq_true_eq, BitVec.toNat_ofNat] at c2
  have := E.need; have := E.last
  rw [sat_eval hl E.last]; unfold newSize; rw [if_neg fun h => c1 (by rw [h]; rfl)]; congr 1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at c2; omega

theorem SA.leaf_800db820_1 :
    LeafGoal SA.plan SA.plan.cuts[2]! (SA.plan.leaves 0x800db820)[1]! := by
  leaf_intro
  refine slow_call needS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fun g m hA hc => ?_
  have hcut := SA.cut_800db820 g m hA
  obtain ⟨hpre, -, hfr, hfm, -, hso0, -⟩ := hA
  have E := EntryS.of hpre
  obtain ⟨-, -, -, hb, hl, -, h9, -, -, -⟩ := in_vals hcut.1 hcut.2.1 E hfr hfm hso0
    fun a h => .inr (fr64_80 E h)
  have c1 : SBool.eval (envA shapeIn g m) (.ne (.init 1 24 8) (.lit 0)) = true := hc _ (by simp)
  have c2 : SBool.eval (envA shapeIn g m) (.geu needS satS) = true := hc _ (by simp [needS, satS])
  simp only [SBool.eval, Sym.eval_lit, hl, bne_iff_ne, ne_eq] at c1
  simp only [SBool.eval, need_eval h9 hb E.k64, sat_eval hl E.last, BitVec.ult,
    Bool.not_eq_true', decide_eq_false_iff_not, BitVec.toNat_ofNat] at c2
  have := E.need; have := E.last
  rw [need_eval h9 hb E.k64]; unfold newSize; rw [if_neg fun h => c1 (by rw [h]; rfl)]; congr 1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at c2; omega

theorem SA.leaf_800db820_2 :
    LeafGoal SA.plan SA.plan.cuts[2]! (SA.plan.leaves 0x800db820)[2]! := by
  leaf_intro
  refine slow_call needS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fun g m hA hc => ?_
  have hcut := SA.cut_800db820 g m hA
  obtain ⟨hpre, -, hfr, hfm, -, hso0, -⟩ := hA
  have E := EntryS.of hpre
  obtain ⟨-, -, -, hb, hl, -, h9, -, -, -⟩ := in_vals hcut.1 hcut.2.1 E hfr hfm hso0
    fun a h => .inr (fr64_80 E h)
  have c1 : SBool.eval (envA shapeIn g m) (.eq (.init 1 24 8) (.lit 0)) = true := hc _ (by simp)
  have c2 : SBool.eval (envA shapeIn g m) (.geu needS (.lit 4096)) = true :=
    hc _ (by simp [needS])
  simp only [SBool.eval, Sym.eval_lit, hl, beq_iff_eq] at c1
  simp only [SBool.eval, need_eval h9 hb E.k64, Sym.eval_lit, BitVec.ult,
    Bool.not_eq_true', decide_eq_false_iff_not, BitVec.toNat_ofNat] at c2
  have := E.need
  rw [need_eval h9 hb E.k64]; unfold newSize; rw [if_pos (by rw [c1]; rfl)]; congr 1
  rw [Nat.mod_eq_of_lt (by omega)] at c2; omega

theorem SA.leaf_800db820_3 :
    LeafGoal SA.plan SA.plan.cuts[2]! (SA.plan.leaves 0x800db820)[3]! := by
  leaf_intro
  refine slow_call (.lit 4096) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) fun g m hA hc => ?_
  have hcut := SA.cut_800db820 g m hA
  obtain ⟨hpre, -, hfr, hfm, -, hso0, -⟩ := hA
  have E := EntryS.of hpre
  obtain ⟨-, -, -, hb, hl, -, h9, -, -, -⟩ := in_vals hcut.1 hcut.2.1 E hfr hfm hso0
    fun a h => .inr (fr64_80 E h)
  have c1 : SBool.eval (envA shapeIn g m) (.eq (.init 1 24 8) (.lit 0)) = true := hc _ (by simp)
  have c2 : SBool.eval (envA shapeIn g m) (.ltu needS (.lit 4096)) = true :=
    hc _ (by simp [needS])
  simp only [SBool.eval, Sym.eval_lit, hl, beq_iff_eq] at c1
  simp only [SBool.eval, need_eval h9 hb E.k64, Sym.eval_lit, BitVec.ult,
    decide_eq_true_eq, BitVec.toNat_ofNat] at c2
  have := E.need
  unfold newSize; rw [if_pos (by rw [c1]; rfl), Sym.eval_lit]; congr 1
  rw [Nat.mod_eq_of_lt (by omega)] at c2; omega

/-! ## After the child's `alloc` -/

theorem heap_memeq {A : AllocContract zesuImage} {L : List (Word × Nat)} {m m' : Machine}
    (h : A.Heap L m) (hmm : m'.mem = m.mem) : A.Heap L m' :=
  A.heap_frame L m m' h (fun a _ => by rw [hmm]) fun b hb j hj => by
    rw [hmm]; exact ((A.live_ok L m h).2 b hb).2 j hj

theorem SA.leaf_800db87c_0 :
    LeafGoal SA.plan SA.plan.cuts[3]! (SA.plan.leaves 0x800db87c)[0]! := by
  leaf_intro
  intro g m hA hc
  have hcut := SA.cut_800db87c g m hA
  have hwf : Env.WF (envA shapeIn g m) SAS := hcut.1
  have hm : Match (envA shapeIn g m) SAS m := hcut.2.1
  obtain ⟨hpre, -, hfr, hfm, hnf, -, hso0, -, -, hout⟩ := hA
  have E := EntryS.of hpre
  obtain ⟨b0, -, -, -, -, -, -, -, -, hsv⟩ := in_vals hwf hm E hfr hfm hso0 fun a h => h
  refine ⟨?_, Nat.le_of_ble_eq_true rfl, fun m' hm0' he hso => ?_⟩
  · simp only [List.mem_singleton, forall_eq]; exact ret_ok hsv E.ra
  have hm' : Match (envA shapeIn g m) (saRunR_leaves[0]!).S m' := hm0'
  have hmm : m'.mem = m.mem := funext fun a =>
    written_only hm rfl hm' (by decide) hso a (by
      rintro ⟨w, hw, -⟩; rw [show (saRunR_leaves[0]!).S.mem = [] by decide] at hw; cases hw)
  have h0 : m.reg 10 = 0 := by
    have := hc _ (List.mem_singleton_self _)
    simp only [SBool.eval, Sym.eval_var, Sym.eval_lit, beq_iff_eq] at this
    rw [← envA_var shapeIn g m 10]; exact this
  obtain ⟨-, hheap⟩ | ⟨hne, -⟩ := hout
  · show AllocPostS g.A g.L g.e m'
    refine ⟨returns_in hsv b0 hfr (envA_var shapeIn g m) hm' (by decide) he,
      fun h => absurd h hnf, fun _ => ⟨fun a ha => ?_, .inl ⟨?_, heap_memeq hheap hmm⟩⟩⟩
    · rw [hmm]; exact hso0 a fun h => ha (h.elim .inl fun h => .inr (.inl h))
    · rw [Match.reg_eq hm' 10 10 rfl]; rfl
  · exact absurd h0 hne

theorem SA.leaf_800db87c_1 :
    LeafGoal SA.plan SA.plan.cuts[3]! (SA.plan.leaves 0x800db87c)[1]! := by
  leaf_intro
  intro g m hA hc
  have hcut := SA.cut_800db87c g m hA
  have hm : Match (envA shapeIn g m) SAS m := hcut.2.1
  refine ⟨by simp, Nat.le_of_ble_eq_true rfl, fun m' hm0' he hso => ?_⟩
  have hm' : Match (envA shapeIn g m) (saRunR_leaves[1]!).S m' := hm0'
  have hmm : m'.mem = m.mem := funext fun a =>
    written_only hm rfl hm' (by decide) hso a (by
      rintro ⟨w, hw, -⟩; rw [show (saRunR_leaves[1]!).S.mem = [] by decide] at hw; cases hw)
  have hrr : ∀ i : Fin 32, m'.reg i = m.reg i := fun i => by
    rw [Match.reg_eq hm' i i.val rfl, show (saRunR_leaves[1]!).S.reg i.val = SAS.reg i.val by
      revert i; decide, ← Match.reg_eq hm i i.val rfl]
  have hne : m.reg 10 ≠ 0 := by
    have := hc _ (List.mem_singleton_self _)
    simp only [SBool.eval, Sym.eval_var, Sym.eval_lit, bne_iff_ne, ne_eq] at this
    rw [← envA_var shapeIn g m 10]; exact this
  obtain ⟨hpre, -, ⟨r2, r8, r9, r18, r19, rk⟩, hfm, hnf, h20, hso0, hp, hro, hout⟩ := hA
  have hl : ∀ a n, m'.load a n = m.load a n := fun a n => load_same hmm a n
  refine ExitGoal.at_cut rfl ⟨cAN, by simp [SA.plan, saPlan], he, ⟨hpre, he,
    ⟨by rw [hrr]; exact r2, by rw [hrr]; exact r8, by rw [hrr]; exact r9, by rw [hrr]; exact r18,
      by rw [hrr]; exact r19, fun i hi => by rw [hrr]; exact rk i hi⟩,
    ⟨fun p hp => by rw [hl]; exact hfm.1 p hp, by rw [hl]; exact hfm.2⟩, hnf, by rw [hrr]; exact h20,
    fun a ha => by rw [hmm]; exact hso0 a ha, fun j hj => by rw [hmm]; exact hp j hj,
    fun a b h => by rw [hmm]; exact hro a b h, by rw [hrr]; exact hne, ?_⟩,
    Nat.le_of_ble_eq_true rfl⟩
  obtain ⟨h0, -⟩ | ⟨-, hheap, hbr, hbp, hbpv, hpl⟩ := hout
  · exact absurd h0 hne
  refine .inr ⟨by rw [hrr]; exact hne, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hrr]
  · exact heap_memeq hheap hmm
  · exact hbr
  · intro j hj; rw [hmm]; exact hbp j hj
  · exact hbpv
  · exact hpl

/-! ## The new chunk -/

/-- What the cut after the call's null test reads. -/
theorem n_vals {g : SigA} {m : Machine} (hA : AN g m) :
    EntryS g.A g.L g.e ∧ (envA shapeAN g m).base 0 = g.e.reg 2 - 64 ∧
    (envA shapeAN g m).size 0 = 64 ∧ (envA shapeAN g m).base 1 = g.e.reg 10 ∧
    (envA shapeAN g m).base 2 = m.reg 10 ∧
    (Sym.init 1 16 8).eval (envA shapeAN g m) = chunks g.e ∧
    (envA shapeAN g m).vars 9 = g.e.reg 11 ∧ (envA shapeAN g m).vars 18 = g.e.reg 12 ∧
    (envA shapeAN g m).vars 20 = BitVec.ofNat 64 (newSize g.e) ∧
    ∀ p ∈ savedRegs, (Sym.init 0 p.1 8).eval (envA shapeAN g m) = g.e.reg p.2 := by
  have hcut := SA.cut_800db880 g m hA
  have hwf : Env.WF (envA shapeAN g m) SAN := hcut.1
  have hm : Match (envA shapeAN g m) SAN m := hcut.2.1
  obtain ⟨hpre, -, hfr, hfm, -, h20, hso, -⟩ := hA
  have E := EntryS.of hpre
  have b0 : (envA shapeAN g m).base 0 = g.e.reg 2 - 64 := by
    rw [← hfr.1]; simp [envA, entryEnv, Env.base, shapeAN, shapeIn]
  have b1 : (envA shapeAN g m).base 1 = g.e.reg 10 := by
    rw [← hfr.2.2.2.2.1]; simp [envA, entryEnv, Env.base, shapeAN, shapeIn]
  have s0 : (envA shapeAN g m).size 0 = 64 := by simp [envA, entryEnv, Env.size, shapeAN, shapeIn]
  have s1 : (envA shapeAN g m).size 1 = 32 := by simp [envA, entryEnv, Env.size, shapeAN, shapeIn]
  have hv := envA_var shapeAN g m
  have hl := load_cst hwf hm (r := 1) (off := 16) (n := 8) (R := arenaR) rfl (by rw [s1]; decide)
  have hc : m.load (g.e.reg 10 + BitVec.ofNat 64 16) 8 = g.e.load (g.e.reg 10 + BitVec.ofNat 64 16) 8 :=
    load_congr fun t ht => by
      rw [show g.e.reg 10 + BitVec.ofNat 64 16 + BitVec.ofNat 64 t =
        g.e.reg 10 + BitVec.ofNat 64 (16 + t) by bv_omega]
      exact ctx_mem E hso (fun a h => h) (by omega)
  rw [b1, show readConst SAN 1 16 8 = .init 1 16 8 by decide] at hl
  refine ⟨E, b0, s0, b1, by simp [envA, entryEnv, Env.base, shapeAN, shapeIn], ?_,
    (hv 9).trans hfr.2.2.1, (hv 18).trans hfr.2.2.2.1, (hv 20).trans h20,
    saved_val hwf hm rfl b0 s0 (by decide) hfm⟩
  show _ = (g.e.load (g.e.reg 10 + BitVec.ofNat 64 16) 8).getD 0
  rw [← hc, hl]; rfl

theorem SA.leaf_800db880_1 :
    LeafGoal SA.plan SA.plan.cuts[4]! (SA.plan.leaves 0x800db880)[1]! := by
  leaf_intro
  intro g m hA hc
  obtain ⟨E, -, -, -, b2, -, h9, h18, h20, -⟩ := n_vals hA
  refine ⟨fun o ho => ?_, Nat.le_of_ble_eq_true rfl, fun m' _ _ _ => ?_⟩ <;> exfalso <;>
  · have c : SBool.eval (envA shapeAN g m) (.ltu (.bin .add (.ptr 2 0) (.var 20))
        (.bin .add (.bin .and (.bin .add (.ptr 2 24) padS) maskS) (.var 9))) = true :=
      hc _ (by simp [padS, maskS])
    simp only [SBool.eval, eval_add, eval_align1, Sym.eval_var, Sym.eval_ptr, b2, h9, h18, h20,
      BitVec.ult, decide_eq_true_eq] at c
    clear hc
    obtain ⟨-, -, -, -, -, -, -, -, -, hne0, hout⟩ := hA
    obtain ⟨h0, -⟩ | ⟨hne, -, hbr, -, -, -⟩ := hout
    · exact hne0 h0
    have hN := newSize_lt E; have hng := newSize_ge g.e; have hk := E.k64
    unfold RamRange Layout.ramHi at hbr
    have hb24 : (m.reg 10 + BitVec.ofInt 64 24).toNat = (m.reg 10).toNat + 24 := by
      rw [BitVec.toNat_add]; simp; have := newSize_24 g.e; omega
    have hK : 2 ^ (g.e.reg 12).toNat ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    have hb := alignUp_bounds (m.reg 10 + BitVec.ofInt 64 24) (g.e.reg 12) hk (by rw [hb24]; omega)
    rw [hb24] at hb
    have hn := E.need; unfold needN at hn hng
    rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, BitVec.toNat_add,
      BitVec.toNat_add (alignUp _ _), BitVec.toNat_ofNat] at c
    rw [Nat.mod_eq_of_lt (a := newSize g.e) (by omega),
      Nat.mod_eq_of_lt (a := (m.reg 10).toNat + newSize g.e) (by omega),
      Nat.mod_eq_of_lt (a := (alignUp (m.reg 10 + BitVec.ofInt 64 24) (g.e.reg 12)).toNat +
        (g.e.reg 11).toNat) (by omega)] at c
    omega

theorem SA.leaf_800db880_0 :
    LeafGoal SA.plan SA.plan.cuts[4]! (SA.plan.leaves 0x800db880)[0]! := by
  leaf_intro
  intro g m hA _
  obtain ⟨E, b0, -, b1, b2, hch, h9, h18, h20, hsv⟩ := n_vals hA
  have hcut := SA.cut_800db880 g m hA
  have hwf : Env.WF (envA shapeAN g m) SAN := hcut.1
  have hm : Match (envA shapeAN g m) SAN m := hcut.2.1
  refine ⟨?_, Nat.le_of_ble_eq_true rfl, fun m' hm0' he hso0' => ?_⟩
  · simp only [List.mem_singleton, forall_eq]; exact ret_ok hsv E.ra
  have hm' : Match (envA shapeAN g m) (saRunN_leaves[0]!).S m' := hm0'
  have hso : SameOutside (InWritable (envA shapeAN g m) SAN) m m' := hso0'
  have hr : (saRunN_leaves[0]!).S.regions = SAN.regions := by decide
  have hwf' := wf_regions hwf hr
  obtain ⟨hpre, -, hfr, hfm, hnf, -, hso1, -, -, hne, hout⟩ := hA
  obtain ⟨h0, -⟩ | ⟨-, hheap, hbr, -, hbpv, hpl⟩ := hout
  · exact absurd h0 hne
  have s1 : (envA shapeAN g m).size 1 = 32 := by simp [envA, entryEnv, Env.size, shapeAN, shapeIn]
  have s2 : (envA shapeAN g m).size 2 = 24 := by simp [envA, entryEnv, Env.size, shapeAN, shapeIn]
  have h24 := newSize_24 g.e
  have hcr := E.ctxRam
  unfold RamRange Layout.ramHi at hbr hcr
  have wd : ∀ r off R, (saRunN_leaves[0]!).S.regions[r]? = some R →
      off + 8 ≤ (envA shapeAN g m).size r →
      word m' ((envA shapeAN g m).base r + BitVec.ofNat 64 off) =
        (readConst (saRunN_leaves[0]!).S r off 8).eval (envA shapeAN g m) :=
    fun r off R hR hb => word_cst hwf' hm' hR hb
  have hr10 : m'.reg 10 = (Sym.bin .and (.bin .add (.ptr 2 24) padS) maskS).eval (envA shapeAN g m) :=
    Match.reg_eq hm' 10 10 rfl
  rw [eval_align1, Sym.eval_ptr, b2, h18, show BitVec.ofInt 64 24 = (24 : Word) from rfl] at hr10
  have hwo := written_only hm rfl hm' hr hso
  have hw : ∀ a, (∃ w ∈ (saRunN_leaves[0]!).S.mem, ∃ j, w.off ≤ j ∧ j < w.off + w.n ∧
      a = (envA shapeAN g m).base w.r + BitVec.ofNat 64 j) →
      InRange (m.reg 10) (newSize g.e) a ∨ InRange (g.e.reg 10 + 16) 16 a ∨ Fr80 g.e a :=
    written_sub [(2, 0, 24), (1, 16, 32), (0, 0, 64)] (by decide) fun q hq j h1 hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> dsimp only at h1 hj ⊢
      · left; rw [b2]; exact inRange_add (by omega) (by omega)
      · right; left; rw [b1]; unfold InRange
        rw [toNat_add_ofNat (by omega),
          show (g.e.reg 10 + 16).toNat = (g.e.reg 10).toNat + 16 by rw [BitVec.toNat_add]; simp; omega]
        omega
      · right; right; rw [b0]; exact fr64_80 E (fr64_in E hj)
  have hctx : ∀ a, InRange (g.e.reg 10 + 16) 16 a → InRange (g.e.reg 10) 32 a := fun a h => by
    unfold InRange at *
    rw [show (g.e.reg 10 + 16).toNat = (g.e.reg 10).toNat + 16 by
      rw [BitVec.toNat_add]; simp; omega] at h
    omega
  show AllocPostS g.A g.L g.e m'
  refine ⟨returns_in hsv b0 hfr (envA_var shapeAN g m) hm' (by decide) he, fun h => absurd h hnf,
    fun _ => ⟨fun a ha => ?_, .inr ⟨m.reg 10, hne, ?_, hbr, hbpv, ?_, ?_, ?_, ?_, hr10, ?_⟩⟩⟩
  · rw [hwo a fun h => ?_]
    · exact hso1 a fun h => ha (h.elim .inl fun h => .inr (.inl h))
    rcases hw a h with h | h | h
    · exact ha (.inl (hbpv a h))
    · exact ha (.inr (.inr h))
    · exact ha (.inr (.inl h))
  · refine g.A.heap_frame _ m m' hheap (fun a ha => hwo a fun h => ?_) fun b hb j hj =>
      pres_of hm' hr hso _ (((g.A.live_ok _ m hheap).2 b hb).2 j hj)
    rcases hw a h with h | h | h
    · exact g.A.priv_not_live _ a ha ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h⟩
    · exact E.priv a (.inl (hctx a h)) (hpl a ha)
    · exact E.priv a (.inr h) (hpl a ha)
  · have := wd 1 16 arenaR rfl (by rw [s1]; decide)
    rw [b1, show readConst (saRunN_leaves[0]!).S 1 16 8 = .ptr 2 0 by decide] at this
    show word m' (g.e.reg 10 + BitVec.ofNat 64 16) = _
    rw [this]; simp [Sym.eval, b2]
  · have := wd 1 24 arenaR rfl (by rw [s1]; decide)
    rw [b1, show readConst (saRunN_leaves[0]!).S 1 24 8 = .var 20 by decide, Sym.eval_var, h20] at this
    exact this
  · have := wd 2 0 hdrR rfl (by rw [s2]; decide)
    rw [b2, show readConst (saRunN_leaves[0]!).S 2 0 8 = .init 1 16 8 by decide, hch,
      show m.reg 10 + BitVec.ofNat 64 0 = m.reg 10 by bv_omega] at this
    exact this
  · have := wd 2 8 hdrR rfl (by rw [s2]; decide)
    rw [b2, show readConst (saRunN_leaves[0]!).S 2 8 8 = .var 20 by decide, Sym.eval_var, h20] at this
    exact this
  · have := wd 2 16 hdrR rfl (by rw [s2]; decide)
    rw [b2, show readConst (saRunN_leaves[0]!).S 2 16 8 = .bin .sub (.bin .add
      (.bin .and (.bin .add (.ptr 2 24) padS) maskS) (.var 9)) (.ptr 2 0) by decide,
      eval_sub, eval_add, eval_align1, Sym.eval_ptr, Sym.eval_ptr, Sym.eval_var, b2, h9, h18,
      show BitVec.ofInt 64 24 = (24 : Word) from rfl, ← hr10] at this
    show word m' (m.reg 10 + BitVec.ofNat 64 16) = _
    rw [this]; simp

zesu_assemble SA

/-- `scratch_arena.alloc` meets its contract for any child allocator meeting `AllocContract`. -/
theorem sa_spec_of (A : AllocContract zesuImage) (L : List (Word × Nat)) :
    Spec zesuImage allocEntryS 133 (AllocPreS A L) (AllocPostS A L) := fun m hpc hpre => by
  obtain ⟨k, m', hk, hr, hq⟩ := SA.reach cAE (by simp [SA.plan, saPlan]) ⟨A, L, m⟩ m ⟨rfl, hpc, hpre⟩
  exact ⟨k, m', hk, hr, hq⟩

/-- `scratch_arena.alloc` over the proved `alt_fl_alloc` (`Alloc.contract`). -/
theorem SA.sa_spec (L : List (Word × Nat)) :
    Spec zesuImage allocEntryS 133 (AllocPreS Alloc.contract L) (AllocPostS Alloc.contract L) :=
  sa_spec_of Alloc.contract L

theorem SA.sa_sail {L : List (Word × Nat)} {m : Machine} {s : BinaryFv.RiscV.State}
    (h : SailLink.Rel zesuImage m s) (hpc : m.pc.toNat = allocEntryS)
    (hpre : AllocPreS Alloc.contract L m) :
    SailLink.SailReaches zesuImage 133
      (fun s' => ∃ m', SailLink.Rel zesuImage m' s' ∧ AllocPostS Alloc.contract L m m') s :=
  SailLink.sail_reaches h (SA.sa_spec L m hpc hpre)

end ZesuExec.Fn.Scratch
