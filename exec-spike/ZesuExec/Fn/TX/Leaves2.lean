import ZesuExec.Fn.TX.Keys

/-!
# TX: leaves of the cuts after `ensureTotalCapacity`, `toOwnedSlice`, the allocator calls,
`memcpy` and the entry store (programme plan S6 step 6, second hand)

Cuts `0x800001f8`, `0x8000025c`, `0x80000340`, `0x800003d4`, `0x80000400`, `0x8000042c`,
`0x80000460`, `0x800004a0`. Error exits after a failed allocation are `allocationFailure`
(`oom_err`): the outer item is a nonempty list and `rest` is past it.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## What a callee may write, seen from `rest` -/

/-- TX's stack, the scratch word or the allocator's memory. -/
def Rcls (σ : Sig) (a : Word) : Prop :=
  InRange (σ.sl stackBytes) stackBytes a ∨ InRange scratch 8 a ∨ σ.A.Priv σ.g.L a

/-- `rest` survives a call that writes only `Rcls` bytes. -/
theorem rest_keep2 {σ : Sig} {mc m : Machine} (hpre : Pre σ.A σ.g σ.m) {R : Word → Prop}
    (hso : SameOutside R mc m) (hR : ∀ a, R a → Rcls σ a) :
    m.load σ.rest 8 = mc.load σ.rest 8 ∧ m.load (σ.rest + 8) 8 = mc.load (σ.rest + 8) 8 := by
  have hfit := pre_fit hpre ((σ.rest, 16), restR) (by simp [shapeFull])
  have h2 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have d9 : Apart (σ.sl stackBytes) stackBytes σ.rest 16 :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have d33 : Apart scratch 8 σ.rest 16 :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at d9 d33
  have key : ∀ t < 16, m.mem (σ.rest + BitVec.ofNat 64 t) = mc.mem (σ.rest + BitVec.ofNat 64 t) :=
    fun t ht => hso _ fun hr => by
      have hin : InRange σ.rest 16 (σ.rest + BitVec.ofNat 64 t) := by
        simp only [InRange]; rw [toNat_add_ofNat (by simp at hfit; omega)]; omega
      rcases hR _ hr with h | h | h
      · simp only [InRange] at h hin
        rw [h2] at h d9; omega
      · simp only [InRange] at h hin
        simp only [scratch, Layout.extraParams, BitVec.toNat_ofNat] at h d33; omega
      · exact owned_not_priv hpre (.inr (.inl hin)) h
  refine ⟨load_congr fun t ht => key t (by omega), load_congr fun t ht => ?_⟩
  rw [show σ.rest + 8 + BitVec.ofNat 64 t = σ.rest + BitVec.ofNat 64 (8 + t) by bv_omega]
  exact key _ (by omega)

/-- `OuterOk` survives such a call. -/
theorem outerOk_keep {σ : Sig} {mc m : Machine} {o : Obs} (hpre : Pre σ.A σ.g σ.m)
    {R : Word → Prop} (hso : SameOutside R mc m) (hR : ∀ a, R a → Rcls σ a)
    (hok : OuterOk σ mc o) : OuterOk σ m o := by
  obtain ⟨k0, k8⟩ := rest_keep2 hpre hso hR
  exact ⟨hok.1, hok.2.1, k0.trans hok.2.2.1, k8.trans hok.2.2.2.1, hok.2.2.2.2⟩

/-! ## Allocation failures -/

/-- An error exit inside a nonempty outer list: `allocationFailure`, `rest` past the item. -/
theorem oom_err {σ : Sig} {m : Machine} {o : Obs} {L X : List (Word × Nat)} (hcm : Common σ m)
    (hok : OuterOk σ m o) (hp : 0 < o.p) (hlive : Live σ m L X) : ErrOk σ m := by
  obtain ⟨hdec, hle, hr0, hr8, -⟩ := hok
  have hlen : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hcons : itemConsumed o.h o.p = o.h + o.p := Nat.mod_eq_of_lt (by omega)
  refine ⟨hcm, ⟨L, X, hlive⟩, .allocationFailure, o.h + o.p, .inr rfl,
    ⟨o.h, o.p, hdec, hp, hcons.symm⟩, hr0, ?_⟩
  rw [hr8, w_len]

/-- `var i` of an `envB` environment is register `i`. -/
theorem envB_var (σ : Sig) (m : Machine) (i : Fin 32) :
    (Sym.var i.val).eval (envB σ m) = m.reg i := by
  simp [Sym.eval, envB, entryEnv]

/-! ## `0x800001f8`: after `ensureTotalCapacity` -/

/-- `ensureTotalCapacity` returned a nonzero code: OutOfMemory, the heap unchanged. -/
theorem f1_oom {A : AllocAssumptions zesuImage} {L : List (Word × Nat)} {items : List Byte}
    {mc m : Machine} (h : F1.Post A L items mc m) (hne : m.reg 10 ≠ 0) : A.Heap L m := by
  obtain ⟨-, -, h⟩ := h
  split at h
  · exact absurd h.1 hne
  · rcases h with h | h
    · exact absurd h.1 hne
    · exact h.2.2.1

/-- What `ensureTotalCapacity` may write is in `Rcls`. -/
theorem f1_rcls {σ : Sig} {mc : Machine} {o : Obs} {k : Kobs} {L : List (Word × Nat)}
    (hIE : InEntry σ mc o k L) (hKL : KList σ mc k k.keys.length)
    (hhdr : mc.reg 10 = σ.sl 0x118) {a : Word}
    (h : InRange (mc.reg 10) 24 a ∨ InRange (mc.reg 2 - 128) 128 a ∨
      InRange (BitVec.ofNat 64 Layout.extraParams) 8 a ∨ σ.A.Priv L a ∨
      (0 < (F1.wordAt mc (mc.reg 10 + 16)).toNat ∧
        InRange (F1.wordAt mc (mc.reg 10)) ((F1.wordAt mc (mc.reg 10 + 16)).toNat * F1.elemBytes) a)) :
    Rcls σ a := by
  have hc := hIE.1
  have hpre := hc.2.1
  have hlive := hIE.2.2.2.2.1
  obtain ⟨⟨hH0, -, hH16⟩, -⟩ := hKL
  rw [hhdr, show mc.reg 2 - 128 = σ.sl 704 from sp_sub hc 128] at h
  rcases h with h | h | h | h | ⟨hc0, h⟩
  · exact .inl (sl_in_stack hpre (by decide) (by decide) h)
  · exact .inl (sl_in_stack hpre (by decide) (by decide) h)
  · exact .inr (.inl h)
  · exact .inr (.inr (priv_sub hpre hlive h))
  · rw [f1w hH16] at hc0 h
    rw [f1w hH0] at h
    exact .inr (.inr ((hlive.2.2 (k.kq, keySize * k.kc.toNat) (by simp [EX, KX, hc0])).2.2 a
      (by simpa [Nat.mul_comm, keySize, F1.elemBytes] using h)))

theorem TX.leaf_800001f8_0 :
    LeafGoal TX.plan TX.plan.cuts[8]! ((TX.plan.leaves 0x800001f8)[0]!) := by
  show LeafGoal TX.plan cut1f8 (run1f8_leaves[0]!)
  have hcs : (run1f8_leaves[0]!).conds = [SBool.ne (Sym.bin BinOp.srl
      (Sym.bin BinOp.sll (Sym.var 10) (Sym.lit 48)) (Sym.lit 48)) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envB_ok (ret_1f8 hA).1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_) (fun σ m hA hc => ?_)
  · have : (run1f8_leaves[0]!).S.steps - SBody.steps = 22 := by decide
    show _ ≤ 32 * (afterEntry m + keysLeft m) + 439; simp only [cut1f8, mkCut] at *; omega
  have hcm := (ret_1f8 hA).1
  obtain ⟨mc, x, ⟨o, k, kh', hIE, -, -, hKL, -, -, ha⟩, hpost, -⟩ := hA
  have h1 : SBool.eval (envB σ m) (SBool.ne (Sym.bin BinOp.srl
      (Sym.bin BinOp.sll (Sym.var 10) (Sym.lit 48)) (Sym.lit 48)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  have hne : m.reg 10 ≠ 0 := by
    intro h0
    have hv : (envB σ m).vars 10 = 0 := h0
    simp only [SBool.eval, Sym.eval, hv] at h1
    exact absurd h1 (by decide)
  have hlive := hIE.2.2.2.2.1
  have hhdr : mc.reg 10 = σ.sl 0x118 := ha.arg 0 (by simp)
  have hok := outerOk_keep hIE.1.2.1 hpost.2.1 (fun a h => f1_rcls hIE hKL hhdr h) hIE.2.1
  exact oom_err hcm hok (by have := hIE.2.2.1.2.2.1; omega)
    ⟨f1_oom hpost hne, hlive.2.1, hlive.2.2⟩

/-! ## `0x8000025c`: after `toOwnedSlice` of the keys -/

/-- An initial frame read of `n` bytes at `S - k + off`. -/
theorem frame_init_n {σ : Sig} {m : Machine} (hpre : Pre σ.A σ.g σ.m) {k off n : Nat}
    (hk : off + n ≤ k) (hk' : k ≤ 576) {v : Word} (h : m.load (σ.sl k + w off) n = some v) :
    (Sym.init 0 (576 - k + off) n).eval (envB σ m) = v := by
  apply init_eval_load (regs := shapeOf σ) (r := 0) (by simp [shapeOf])
  · rwa [show σ.sl k + w off = ((shapeOf σ)[0]'(by simp [shapeOf])).1 +
      BitVec.ofNat 64 (576 - k + off) by
      simp only [shapeOf, List.getElem_cons_zero, Sig.sl, w, frameBytes]; bv_omega] at h
  · have := (entry_nums hpre).1
    simp only [shapeOf, List.getElem_cons_zero]
    rw [sl_toNat hpre (by decide)]
    unfold Layout.ramLo frameBytes at *; omega

/-- `toOwnedSlice` reported an error: OutOfMemory on a nonempty list, the heap unchanged. -/
theorem f4_oom' {eb : Nat} {A : AllocAssumptions zesuImage} {L : List (Word × Nat)}
    {items : List Byte} {empty : Word} {mc m : Machine}
    (h : ToOwned.Post eb A L items empty mc m) (hne : m.load (mc.reg 10 + 16) 2 ≠ some 0) :
    A.Heap L m ∧ (ToOwned.listLen mc).toNat ≠ 0 := by
  obtain ⟨-, -, h⟩ := h
  split at h
  · exact absurd h.2.1.2.2.1 hne
  · rename_i hn
    rcases h with ⟨_, -, -, -, -, hri, -⟩ | h
    · exact absurd hri.2.2.1 hne
    · exact ⟨h.2.2.1, hn⟩

theorem f4_oom {eb : Nat} {A : AllocAssumptions zesuImage} {L : List (Word × Nat)}
    {items : List Byte} {empty : Word} {mc m : Machine}
    (h : ToOwned.Post eb A L items empty mc m) (hne : m.load (mc.reg 10 + 16) 2 ≠ some 0) :
    A.Heap L m := (f4_oom' h hne).1

/-- What `toOwnedSlice` of the keys may write is in `Rcls`. -/
theorem f4_rcls {σ : Sig} {mc : Machine} {o : Obs} {k : Kobs} {L : List (Word × Nat)}
    (hIE : InEntry σ mc o k L) (hKL : KList σ mc k k.keys.length)
    (hres : mc.reg 10 = σ.sl 0xb8) (hhdr : mc.reg 11 = σ.sl 0x118) {a : Word}
    (h : InRange (mc.reg 10) 24 a ∨ InRange (mc.reg 11) 24 a ∨ InRange (mc.reg 2 - 112) 112 a ∨
      InRange ToOwned.scratch 8 a ∨ σ.A.Priv L a ∨ (0 < (ToOwned.listCap mc).toNat ∧
        InRange (ToOwned.listPtr mc) ((ToOwned.listCap mc).toNat * F4.elemBytes) a)) :
    Rcls σ a := by
  have hc := hIE.1
  have hpre := hc.2.1
  have hlive := hIE.2.2.2.2.1
  obtain ⟨⟨hH0, -, hH16⟩, -⟩ := hKL
  simp only [ToOwned.listPtr, ToOwned.listCap, hhdr, hres, f4w hH0, f4w hH16,
    show mc.reg 2 - 112 = σ.sl 688 from sp_sub hc 112] at h
  rcases h with h | h | h | h | h | ⟨hc0, h⟩
  · exact .inl (sl_in_stack hpre (by decide) (by decide) h)
  · exact .inl (sl_in_stack hpre (by decide) (by decide) h)
  · exact .inl (sl_in_stack hpre (by decide) (by decide) h)
  · exact .inr (.inl h)
  · exact .inr (.inr (priv_sub hpre hlive h))
  · exact .inr (.inr ((hlive.2.2 (k.kq, keySize * k.kc.toNat) (by simp [EX, KX, hc0])).2.2 a
      (by simpa [Nat.mul_comm, keySize, F4.elemBytes] using h)))

theorem TX.leaf_8000025c_0 :
    LeafGoal TX.plan TX.plan.cuts[10]! ((TX.plan.leaves 0x8000025c)[0]!) := by
  show LeafGoal TX.plan cut25c (run25c_leaves[0]!)
  have hcs : (run25c_leaves[0]!).conds = [SBool.ne (Sym.init 0 408 2) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envB_ok (ret_25c hA).1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_) (fun σ m hA hc => ?_)
  · have : (run25c_leaves[0]!).S.steps - SBody.steps = 21 := by decide
    show _ ≤ bTail m 539; unfold bTail; simp only [cut25c, mkCut] at *; omega
  have hcm := (ret_25c hA).1
  obtain ⟨mc, x, ⟨o, k, hIE, -, -, hKL, ha⟩, hpost, -⟩ := hA
  have h1 : SBool.eval (envB σ m) (SBool.ne (Sym.init 0 408 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  have hres : mc.reg 10 = σ.sl 0xb8 := ha.arg 0 (by simp)
  have hhdr : mc.reg 11 = σ.sl 0x118 := ha.arg 1 (by simp)
  have hne : m.load (mc.reg 10 + 16) 2 ≠ some 0 := by
    intro h0
    rw [hres, show (16 : Word) = w 16 from rfl] at h0
    simp only [SBool.eval] at h1
    rw [show (408 : Nat) = 576 - 0xb8 + 16 from rfl, frame_init_n hcm.2.1 (by decide) (by decide) h0]
      at h1
    simp [Sym.eval] at h1
  have hlive := hIE.2.2.2.2.1
  have hok := outerOk_keep hIE.1.2.1 hpost.2.1 (fun a h => f4_rcls hIE hKL hres hhdr h) hIE.2.1
  exact oom_err hcm hok (by have := hIE.2.2.1.2.2.1; omega)
    ⟨f4_oom hpost hne, hlive.2.1, hlive.2.2⟩


/-! ## `0x800003d4`: after `alloc` -/

theorem TX.leaf_800003d4_1 :
    LeafGoal TX.plan TX.plan.cuts[12]! ((TX.plan.leaves 0x800003d4)[1]!) := by
  show LeafGoal TX.plan cut3d4 (run3d4_leaves[1]!)
  have hcs : (run3d4_leaves[1]!).conds = [SBool.eq (Sym.var 10) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envB_ok (A3d4_common hA)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_) (fun σ m hA hc => ?_)
  · have : (run3d4_leaves[1]!).S.steps - SBody.steps = 22 := by decide
    show _ ≤ bTail m 389; unfold bTail; simp only [cut3d4, mkCut] at *; omega
  have hcm := A3d4_common hA
  obtain ⟨mc, L, ⟨o, k, kp', hED, -, -, -⟩, ⟨hret, hso, hcase⟩, -⟩ := hA
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.var 10) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  have h0 : m.reg 10 = 0 := by
    simp only [SBool.eval, Sym.eval, beq_iff_eq] at h1; exact h1
  have hpre := hED.1.2.1
  have hlive := hED.2.2.2.2.1
  have hheap : σ.A.Heap L m := by
    rcases hcase with ⟨-, h⟩ | ⟨hne, -⟩
    · exact h
    · exact absurd h0 hne
  have hR : ∀ a, (σ.A.Priv L a ∨ InRange (mc.reg 2 - 16) 16 a) → Rcls σ a := fun a h => by
    rcases h with h | h
    · exact .inr (.inr (priv_sub hpre hlive h))
    · rw [show mc.reg 2 - 16 = σ.sl 592 from sp_sub hED.1 16] at h
      exact .inl (sl_in_stack hpre (by decide) (by decide) h)
  exact oom_err hcm (outerOk_keep hpre hso hR hED.2.1) (by have := hED.2.2.1.2.2.1; omega)
    ⟨hheap, hlive.2.1, hlive.2.2⟩

/-! ## `0x80000340`: after `remap` -/

/-- `s6` is `0` at the `remap` call and callee-saved: the branch on `s6 ≠ 0` is dead. -/
theorem TX.leaf_80000340_0 :
    LeafGoal TX.plan TX.plan.cuts[11]! ((TX.plan.leaves 0x80000340)[0]!) := by
  show LeafGoal TX.plan cut340 (run340_leaves[0]!)
  have hcs : (run340_leaves[0]!).conds =
      [SBool.eq (Sym.var 10) (Sym.lit 0), SBool.ne (Sym.var 22) (Sym.lit 0)] := by decide
  intro σ m hA hc
  exfalso
  have h2 : SBool.eval (envB σ m) (SBool.ne (Sym.var 22) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  obtain ⟨mc, _, ⟨o, k, L, kp', -, -, -, h22, -⟩, ⟨hret, -⟩, -⟩ := hA
  have h0 : (envB σ m).vars 22 = 0 := (hret.2 22 (by decide)).trans h22
  simp only [SBool.eval, Sym.eval, h0] at h2
  exact absurd h2 (by decide)

/-! ## `0x800004a0`: after `toOwnedSlice` of the entries -/

/-- A walked outer payload with an entry is not empty. -/
theorem p_pos {σ : Sig} {o : Obs} (hw : OuterWalked (pl σ o) o.p o.done) (hne : o.done ≠ []) :
    0 < o.p := by
  rcases Nat.eq_zero_or_pos o.p with h0 | h
  · exfalso
    have hpl : pl σ o = [] := by simp [pl, itemPayload, h0]
    have := hw.2.1
    rw [hpl] at this
    simp [entriesWalk] at this
    exact hne this
  · exact h

/-- What `toOwnedSlice` of the entries may write is in `Rcls`. -/
theorem f5_rcls {σ : Sig} {mc : Machine} {o : Obs} {L : List (Word × Nat)}
    (hc : Common σ mc) (hEL : EList σ mc o o.done.length) (hlive : Live σ mc L (EX o))
    (hres : mc.reg 10 = σ.sl 0x88) (hhdr : mc.reg 11 = σ.sl 0x1c0) {a : Word}
    (h : InRange (mc.reg 10) 24 a ∨ InRange (mc.reg 11) 24 a ∨ InRange (mc.reg 2 - 112) 112 a ∨
      InRange ToOwned.scratch 8 a ∨ σ.A.Priv L a ∨ (0 < (ToOwned.listCap mc).toNat ∧
        InRange (ToOwned.listPtr mc) ((ToOwned.listCap mc).toNat * F5.elemBytes) a)) :
    Rcls σ a := by
  have hpre := hc.2.1
  obtain ⟨⟨hH0, -, hH16⟩, -⟩ := hEL
  simp only [ToOwned.listPtr, ToOwned.listCap, hhdr, hres, f4w hH0, f4w hH16,
    show mc.reg 2 - 112 = σ.sl 688 from sp_sub hc 112] at h
  rcases h with h | h | h | h | h | ⟨hc0, h⟩
  · exact .inl (sl_in_stack hpre (by decide) (by decide) h)
  · exact .inl (sl_in_stack hpre (by decide) (by decide) h)
  · exact .inl (sl_in_stack hpre (by decide) (by decide) h)
  · exact .inr (.inl h)
  · exact .inr (.inr (priv_sub hpre hlive h))
  · exact .inr (.inr ((hlive.2.2 (o.ep, entrySize * o.ec.toNat) (by simp [EX, hc0])).2.2 a
      (by simpa [Nat.mul_comm, entrySize, F5.elemBytes] using h)))

theorem TX.leaf_800004a0_1 :
    LeafGoal TX.plan TX.plan.cuts[16]! ((TX.plan.leaves 0x800004a0)[1]!) := by
  show LeafGoal TX.plan cut4a0 (run4a0_leaves[1]!)
  have hcs : (run4a0_leaves[1]!).conds = [SBool.ne (Sym.init 0 456 2) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envB_ok (ret_4a0 hA).1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_) (fun σ m hA hc => ?_)
  · have : (run4a0_leaves[1]!).S.steps - SBody.steps = 21 := by decide
    show _ ≤ 23; simp only [cut4a0, mkCut] at *; omega
  have hcm := (ret_4a0 hA).1
  obtain ⟨mc, x, ⟨o, hc0, hok, hip, hEL, hlive, -, ha⟩, hpost, -⟩ := hA
  have h1 : SBool.eval (envB σ m) (SBool.ne (Sym.init 0 456 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  have hres : mc.reg 10 = σ.sl 0x88 := ha.arg 0 (by simp)
  have hhdr : mc.reg 11 = σ.sl 0x1c0 := ha.arg 1 (by simp)
  have hne : m.load (mc.reg 10 + 16) 2 ≠ some 0 := by
    intro h0
    rw [hres, show (16 : Word) = w 16 from rfl] at h0
    simp only [SBool.eval] at h1
    rw [show (456 : Nat) = 576 - 0x88 + 16 from rfl, frame_init_n hcm.2.1 (by decide) (by decide) h0]
      at h1
    simp [Sym.eval] at h1
  obtain ⟨hheap, hn⟩ := f4_oom' hpost hne
  have hdone : o.done ≠ [] := by
    intro hd
    apply hn
    obtain ⟨⟨-, hH8, -⟩, -⟩ := hEL
    simp only [ToOwned.listLen, hhdr]
    rw [f4w hH8, hd]; rfl
  have hw := hok.2.2.2.2
  rw [hip] at hw
  exact oom_err hcm (outerOk_keep hc0.2.1 hpost.2.1 (fun a h => f5_rcls hc0 hEL hlive hres hhdr h) hok)
    (p_pos hw hdone) ⟨hheap, hlive.2.1, hlive.2.2⟩

/-! ## A finished entry's facts across a change that misses them -/

theorem bytes_congr {m m' : Machine} {a : Word} {bs : List Byte} (h : BytesAt m a bs)
    (hs : ∀ t < bs.length, m'.mem (a + BitVec.ofNat 64 t) = m.mem (a + BitVec.ofNat 64 t)) :
    BytesAt m' a bs := fun i hi => (hs i hi).trans (h i hi)

theorem hdr_congr {m m' : Machine} {a p n c : Word} (h : F1.HeaderIs m a p n c)
    (hs : ∀ t < 24, m'.mem (a + BitVec.ofNat 64 t) = m.mem (a + BitVec.ofNat 64 t)) :
    F1.HeaderIs m' a p n c := by
  obtain ⟨h0, h8, h16⟩ := h
  refine ⟨(load_congr fun t ht => hs t (by omega)).trans h0, ?_, ?_⟩
  · rw [load_congr (m := m) fun t ht => by
      rw [show a + 8 + BitVec.ofNat 64 t = a + BitVec.ofNat 64 (8 + t) by bv_omega]
      exact hs _ (by omega)]
    exact h8
  · rw [load_congr (m := m) fun t ht => by
      rw [show a + 16 + BitVec.ofNat 64 t = a + BitVec.ofNat 64 (16 + t) by bv_omega]
      exact hs _ (by omega)]
    exact h16

/-- The bytes `EntryDone` reads: `rest`, four frame slots and TX's live blocks. -/
structure EDSame (σ : Sig) (o : Obs) (k : Kobs) (kp' : Word) (mc m : Machine) : Prop where
  rest : ∀ t < 16, m.mem (σ.rest + BitVec.ofNat 64 t) = mc.mem (σ.rest + BitVec.ofNat 64 t)
  slot : ∀ kn ∈ ([(0x1f0, 8), (0x1c0, 24), (0x158, 20), (0xa0, 20)] : List (Nat × Nat)),
    ∀ t < kn.2, m.mem (σ.sl kn.1 + BitVec.ofNat 64 t) = mc.mem (σ.sl kn.1 + BitVec.ofNat 64 t)
  blk : ∀ b ∈ EX o ++ KD k kp', ∀ t < b.2,
    m.mem (b.1 + BitVec.ofNat 64 t) = mc.mem (b.1 + BitVec.ofNat 64 t)

/-- `EntryDone` carries over to a machine that keeps its bytes, its registers and the heap. -/
theorem ed_congr {σ : Sig} {mc m : Machine} {o : Obs} {k : Kobs} {L X : List (Word × Nat)}
    {kp' : Word} (h : EntryDone σ mc o k L kp' X) (hcm : Common σ m) (hheap : σ.A.Heap L m)
    (hr : ∀ i ∈ ([20, 21, 26] : List (Fin 32)), m.reg i = mc.reg i)
    (hs : EDSame σ o k kp' mc m) : EntryDone σ m o k L kp' X := by
  obtain ⟨-, hok, ⟨r20, r21, hi, hmag⟩, hEL, hlive, ⟨hd, hle, r26⟩, ⟨had, hal, hA⟩, hkl, hkw,
    hram, hkb, hkeys, hB⟩ := h
  have l0 := hs.slot (0x1f0, 8) (by simp)
  have l1 := hs.slot (0x1c0, 24) (by simp)
  have l2 := hs.slot (0x158, 20) (by simp)
  have l3 := hs.slot (0xa0, 20) (by simp)
  obtain ⟨hH, hle', hp0, hc0, hc32, hram', hil, hbytes, hz⟩ := hEL
  have h20 : ∀ t < (itemPayload (ent σ o k) k.ah 20).length, t < 20 := fun t ht => by
    simp only [itemPayload, List.length_take] at ht; omega
  have hA' : BytesAt m (σ.sl 0x158) (itemPayload (ent σ o k) k.ah 20) :=
    bytes_congr hA fun t ht => l2 t (h20 t ht)
  have hB' : BytesAt m (σ.sl 0xa0) (itemPayload (ent σ o k) k.ah 20) :=
    bytes_congr hB fun t ht => l3 t (h20 t ht)
  refine ⟨hcm, ⟨hok.1, hok.2.1, ?_, ?_, hok.2.2.2.2⟩,
    ⟨(hr 20 (by decide)).trans r20, (hr 21 (by decide)).trans r21, hi,
      (load_congr fun t ht => l0 t ht).trans hmag⟩,
    ⟨hdr_congr hH l1, hle', hp0, hc0, hc32, hram', hil, ?_, fun x hx => ?_⟩,
    ⟨hheap, hlive.2.1, hlive.2.2⟩, ⟨hd, hle, (hr 26 (by decide)).trans r26⟩,
    ⟨had, hal, hA'⟩, hkl, hkw, hram, ?_, hkeys, hB'⟩
  · rw [load_congr fun t ht => hs.rest t (by omega)]; exact hok.2.2.1
  · rw [load_congr (m := mc) fun t ht => by
      rw [show σ.rest + 8 + BitVec.ofNat 64 t = σ.rest + BitVec.ofNat 64 (8 + t) by bv_omega]
      exact hs.rest _ (by omega)]
    exact hok.2.2.2.1
  · rcases Nat.eq_zero_or_pos o.ec.toNat with he | he
    · have : o.done = [] := List.eq_nil_of_length_eq_zero (by omega)
      have : o.is = [] := List.eq_nil_of_length_eq_zero (by rw [hil, this]; rfl)
      intro i hi; simp [entriesBytes, *] at hi
    · have hlen := entriesBytes_length o.done o.is hil fun x hx => ⟨(hz x hx).1, (hz x hx).2.1⟩
      refine bytes_congr hbytes fun t ht => hs.blk (o.ep, entrySize * o.ec.toNat)
        (by simp [EX, he]) t ?_
      rw [hlen] at ht
      exact Nat.lt_of_lt_of_le ht (Nat.mul_le_mul_left _ hle')
  · obtain ⟨hpad, haddr, hkl', hkram, hkb'⟩ := hz x hx
    refine ⟨hpad, haddr, hkl', hkram, ?_⟩
    by_cases hk : x.1.keys = []
    · rw [hk]; intro i hi; simp at hi
    · exact bytes_congr hkb' fun t ht => hs.blk _ (by
        simp only [EX, List.mem_append]; exact .inl (.inr (mem_keysBlocks hx hk))) t
        (by rw [flatten_length _ hkl'] at ht; exact ht)
  · by_cases hk : k.keys = []
    · rw [hk]; intro i hi; simp at hi
    · exact bytes_congr hkb fun t ht => hs.blk (kp', keySize * k.keys.length)
        (by simp [KD, hk]) t (by rw [flatten_length _ hkeys] at ht; exact ht)

end ZesuExec.Fn.TX
