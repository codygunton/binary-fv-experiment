import ZesuExec.Fn.TX.Calls
import ZesuExec.Fn.TX.Store

/-!
# TX: leaves of the cuts after `ensureTotalCapacity`, `toOwnedSlice`, the allocator calls,
`memcpy` and the entry store (programme plan S6 step 6, second hand)

Cuts `0x800001f8`, `0x8000025c`, `0x80000340`, `0x800003d4`, `0x80000400`, `0x8000042c`,
`0x80000460`, `0x800004a0`. Error exits after a failed allocation are `allocationFailure`
(`oom_err`): the outer item is a nonempty list and `rest` is past it.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## What a leaf with writes keeps -/

/-- `Common` survives a step that keeps `sp`, `s0`, `s1`, `s2`, `s3` and changes only TX's own
or the allocator's memory outside the save area. -/
theorem common_keep {σ : Sig} {m m' : Machine} (hc : Common σ m)
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19] : List (Fin 32)), m'.reg i = m.reg i)
    (hp : Preserved m m') {R : Word → Prop} (hso : SameOutside R m m')
    (hR : ∀ a, R a → (Owned σ a ∨ σ.A.Priv σ.g.L a) ∧ ¬ InRange (σ.sl 104) 104 a) :
    Common σ m' := by
  obtain ⟨hpc, hpre, hro, r2, r8, r9, r18, r19, hsv, hst, hres, hrest, hscr, hfr⟩ := hc
  refine ⟨hpc, hpre, RodataLoaded.preserved hro hp fun _ _ hb => F1.zesu_rodata_low hb,
    (hr 2 (by decide)).trans r2, (hr 8 (by decide)).trans r8, (hr 9 (by decide)).trans r9,
    (hr 18 (by decide)).trans r18, (hr 19 (by decide)).trans r19, fun k hk => ?_,
    Present.of_preserved hst hp, Present.of_preserved hres hp, Present.of_preserved hrest hp,
    Present.of_preserved hscr hp, frame_trans hfr hso fun a h => (hR a h).1⟩
  rw [load_congr fun t ht => hso _ fun h => (hR _ h).2 ?_]
  · exact hsv k hk
  · have h1 := sl_toNat hpre (k := 104) (by decide)
    have h2 := sl_toNat hpre (k := 8 * (k + 1)) (by unfold stackBytes; omega)
    simp only [InRange, h1]
    rw [toNat_add_ofNat (by rw [h2]; omega), h2]
    omega

/-- A byte no write of the leaf covers keeps its value at the cut. -/
theorem byte_keep {env : Env} {S' : SState} {m m' : Machine} (hm' : Match env S' m') {r j : Nat}
    (hr : r < S'.regions.length) (hj : j < env.size r)
    (hnc : ∀ w ∈ S'.mem, w.covers r j = false)
    (h0 : some (env.mem0 r j) = m.mem (env.base r + BitVec.ofNat 64 j)) :
    m'.mem (env.base r + BitVec.ofNat 64 j) = m.mem (env.base r + BitVec.ofNat 64 j) := by
  rw [hm'.mem r j hr hj, ← h0]
  have : S'.mem.find? (·.covers r j) = none := List.find?_eq_none.mpr fun w hw => by
    simp [hnc w hw]
  simp [memByte, this, Env.byte0]

/-- A leaf over the base regions whose writes miss the save area (frame offsets `≥ 472`). -/
theorem save_keep {σ : Sig} {m m' : Machine} {env : Env} {S' : SState} (hc : Common σ m)
    (he : BaseEnv σ m env) (hm' : Match env S' m') (hr0 : 0 < S'.regions.length)
    (hno : S'.mem.all (fun w => w.r != 0 || decide (w.off + w.n ≤ 472)) = true) {a : Word}
    (ha : InRange (σ.sl 104) 104 a) : m'.mem a = m.mem a := by
  have hpre := hc.2.1
  have h1 := sl_toNat hpre (k := 104) (by decide)
  have h576 := sl_toNat hpre (k := 576) (by decide)
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  simp only [InRange, h1] at ha
  have hb : env.base 0 = σ.sl frameBytes := by rw [he.base]; rfl
  have hs : env.size 0 = frameBytes := by rw [he.size]; rfl
  obtain ⟨j, hj1, hj2, rfl⟩ : ∃ j, 472 ≤ j ∧ j < 576 ∧ a = env.base 0 + BitVec.ofNat 64 j := by
    refine ⟨a.toNat - (σ.S.toNat - 576), by omega, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [hb, toNat_add_ofNat (by unfold frameBytes; omega)]
    unfold frameBytes; rw [h576]; omega
  refine byte_keep hm' hr0 (by rw [hs]; exact hj2) (fun w hw => ?_) ?_
  · have := List.all_eq_true.mp hno w hw
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    simp only [Write.covers, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      decide_eq_false_iff_not, Nat.not_le, Nat.not_lt]
    omega
  · rw [he.mem0, he.base]
    exact mem0_entry (common_present hc 0 j (by decide) (by simpa [envB, entryEnv, Env.size,
      shapeOf, frameBytes] using hj2))

/-- A leaf of a cut over the base regions (`BaseEnv`) whose writes miss the save area: the
machine at its end is `Common`, keeps TX's live list and preserves present bytes. -/
theorem base_leaf {σ : Sig} {m m' : Machine} {env : Env} {S S' : SState} {L X : List (Word × Nat)}
    (hc : Common σ m) (hlive : Live σ m L X) (he : BaseEnv σ m env) (hwf : Env.WF env S)
    (hS : S.regions = baseRegions) (hm' : Match env S' m') (hS' : S'.regions = baseRegions)
    (hfr : SameOutside (InWritable env S) m m')
    (hno : S'.mem.all (fun w => w.r != 0 || decide (w.off + w.n ≤ 472)) = true)
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19] : List (Fin 32)), m'.reg i = m.reg i) :
    Common σ m' ∧ Live σ m' L X ∧ Preserved m m' := by
  have hpre := hc.2.1
  have hp : Preserved m m' :=
    F1.preserved_of_leaf hwf hm' (by rw [hS, hS']; exact Nat.le_refl _) hfr
  have hown : ∀ a, InWritable env S a → Owned σ a := fun a h => he.owned hpre hS h
  have hso : SameOutside (fun a => InWritable env S a ∧ m'.mem a ≠ m.mem a) m m' := fun a ha => by
    by_cases hw : InWritable env S a
    · exact Classical.byContradiction fun hne => ha ⟨hw, hne⟩
    · exact hfr a hw
  refine ⟨common_keep hc hr hp hso fun a ⟨hw, hne⟩ => ⟨.inl (hown a hw), fun hs =>
      hne (save_keep hc he hm' (by rw [hS']; decide) hno hs)⟩,
    ⟨σ.A.heap_frame' L m m' hlive.1
      (fun a ha => hfr a fun hw => owned_not_priv hpre (hown a hw) (priv_sub hpre hlive ha)) hp,
     hlive.2.1, hlive.2.2⟩, hp⟩

/-! ## `decodeItem`'s outcome words -/

/-- A list item does not start with `0x80`. -/
theorem list_head {input : List Byte} {h q : Nat} (hd : F2.decode input = .success true h q) :
    input.head? ≠ some 128 := by
  cases input with
  | nil => simp
  | cons x rest =>
    intro hx
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    simp [F2.decode] at hd

/-- The payload pointer (bytes `0..7`) of a list outcome. -/
theorem dec_ptr {p : Word} {input before : List Byte} {hh q : Nat}
    (hd : F2.decode input = .success true hh q) :
    ofBytesLE (((F2.result40 p input before).drop 0).take 8) = p + BitVec.ofNat 64 hh := by
  show ofBytesLE [F2.resultByte p input before 0, F2.resultByte p input before 1,
    F2.resultByte p input before 2, F2.resultByte p input before 3,
    F2.resultByte p input before 4, F2.resultByte p input before 5,
    F2.resultByte p input before 6, F2.resultByte p input before 7] = _
  simp only [F2.resultByte, hd, F2.successByte, if_neg (list_head hd)]
  exact ofBytesLE_bytes8 _

/-- The consumed count (bytes `24..31`) of a successful outcome. -/
theorem dec_cons {p : Word} {input before : List Byte} {b : Bool} {hh q : Nat}
    (hd : F2.decode input = .success b hh q) :
    ofBytesLE (((F2.result40 p input before).drop 24).take 8) = BitVec.ofNat 64 (hh + q) := by
  show ofBytesLE [F2.resultByte p input before 24, F2.resultByte p input before 25,
    F2.resultByte p input before 26, F2.resultByte p input before 27,
    F2.resultByte p input before 28, F2.resultByte p input before 29,
    F2.resultByte p input before 30, F2.resultByte p input before 31] = _
  simp only [F2.resultByte, hd, F2.successByte]
  exact ofBytesLE_bytes8 _

/-! ## Reading written words back -/

/-- A frame word at the end of a leaf over the base regions. -/
theorem frame_word {σ : Sig} {m m' : Machine} {env : Env} {S' : SState} (he : BaseEnv σ m env)
    (hwf : Env.WF env S') (hm' : Match env S' m') (hS' : S'.regions = baseRegions) {k : Nat}
    (hk : 8 ≤ k) (hk' : k ≤ 576) :
    m'.load (σ.sl k) 8 = some ((readConst S' 0 (576 - k) 8).eval env) := by
  have := load_cst hwf hm' (r := 0) (R := frameR) (off := 576 - k) (n := 8) (by rw [hS']; rfl)
    (by rw [he.size]; simp [envB, entryEnv, Env.size, shapeOf, frameBytes]; omega)
  rwa [he.base, show (envB σ m).base 0 + BitVec.ofNat 64 (576 - k) = σ.sl k by
    simp only [envB, entryEnv, Env.base, shapeOf, List.getD_cons_zero, Sig.sl, w, frameBytes]
    bv_omega] at this

/-- A word of `rest` at the end of a leaf over the base regions. -/
theorem rest_word {σ : Sig} {m m' : Machine} {env : Env} {S' : SState} (he : BaseEnv σ m env)
    (hwf : Env.WF env S') (hm' : Match env S' m') (hS' : S'.regions = baseRegions) {off : Nat}
    (hoff : off = 0 ∨ off = 8) :
    m'.load (σ.rest + BitVec.ofNat 64 off) 8 = some ((readConst S' 2 off 8).eval env) := by
  have := load_cst hwf hm' (r := 2) (R := restR) (off := off) (n := 8) (by rw [hS']; rfl)
    (by rw [he.size]; simp [envB, entryEnv, Env.size, shapeOf]; omega)
  rwa [he.base] at this

/-- A range of the allocator's memory is apart from a range without any of it. -/
theorem apart_of_priv {P : Word → Prop} {p q : Word} {n k : Nat} (hn : 0 < n) (hk : 0 < k)
    (hp : ∀ a, InRange p n a → P a) (hq : ∀ a, InRange q k a → ¬ P a) : Apart p n q k := by
  unfold Apart
  refine Classical.byContradiction fun h => ?_
  rcases Nat.le_total p.toNat q.toNat with hle | hle
  · exact hq q ⟨Nat.le_refl _, by omega⟩ (hp q ⟨hle, by omega⟩)
  · exact hq p ⟨hle, by omega⟩ (hp p ⟨Nat.le_refl _, by omega⟩)

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
  · budget_auto
  have hcm := (ret_1f8 hA).1
  obtain ⟨mc, x, ⟨o, k, kh', hIE, -, -, hKL, -, -, ha⟩, ⟨hpost, -⟩, -⟩ := hA
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
  · budget_auto
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
  · budget_auto
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
  obtain ⟨mc, _, ⟨o, k, L, kp', -, -, -, -, h22, -⟩, ⟨hret, -⟩, -⟩ := hA
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
  · budget_auto
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

/-- `EntryDone` carries over to a machine that keeps its bytes and registers, with the live list
the new machine has. -/
theorem ed_congr' {σ : Sig} {mc m : Machine} {o : Obs} {k : Kobs} {L X L' X' : List (Word × Nat)}
    {kp' : Word} (h : EntryDone σ mc o k L kp' X) (hcm : Common σ m)
    (hl : Live σ m L' (EX o ++ KD k kp' ++ X'))
    (hr : ∀ i ∈ ([20, 21, 26] : List (Fin 32)), m.reg i = mc.reg i)
    (hs : EDSame σ o k kp' mc m) : EntryDone σ m o k L' kp' X' := by
  obtain ⟨-, hok, ⟨r20, r21, hi, hmag⟩, hEL, -, ⟨hd, hle, r26⟩, ⟨had, hal, hA⟩, hkl, hkw,
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
    hl, ⟨hd, hle, (hr 26 (by decide)).trans r26⟩,
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

/-- `EntryDone` carries over to a machine that keeps its bytes, its registers and the heap. -/
theorem ed_congr {σ : Sig} {mc m : Machine} {o : Obs} {k : Kobs} {L X : List (Word × Nat)}
    {kp' : Word} (h : EntryDone σ mc o k L kp' X) (hcm : Common σ m) (hheap : σ.A.Heap L m)
    (hr : ∀ i ∈ ([20, 21, 26] : List (Fin 32)), m.reg i = mc.reg i)
    (hs : EDSame σ o k kp' mc m) : EntryDone σ m o k L kp' X :=
  ed_congr' h hcm ⟨hheap, h.2.2.2.2.1.2.1, h.2.2.2.2.1.2.2⟩ hr hs

/-- Blocks in different parts of TX's live blocks do not meet. -/
theorem live_apart {σ : Sig} {m : Machine} {L Y1 Y2 : List (Word × Nat)}
    (hlive : Live σ m L (Y1 ++ Y2)) {b c : Word × Nat} (hb : b ∈ Y1) (hc : c ∈ Y2) :
    b.1.toNat + b.2 ≤ c.1.toNat ∨ c.1.toNat + c.2 ≤ b.1.toNat := by
  have hp := (σ.A.live_ok L m hlive.1).1
  rw [hlive.2.1.pairwise_iff (fun h => h.symm), List.pairwise_append, List.pairwise_append] at hp
  exact hp.2.1.2.2 b hb c hc

theorem in_self {a : Word} {n t : Nat} (hfit : a.toNat + n < 2 ^ 64) (ht : t < n) :
    InRange a n (a + BitVec.ofNat 64 t) := by
  simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega

/-- A callee that writes only free stack bytes, the scratch word, the allocator's memory or
other live blocks `Y` keeps what `EntryDone` reads. -/
theorem edsame_of {σ : Sig} {mc m : Machine} {o : Obs} {k : Kobs} {kp' : Word}
    {L Y : List (Word × Nat)} (hpre : Pre σ.A σ.g σ.m)
    (hlive : Live σ mc L (EX o ++ KD k kp' ++ Y)) {R : Word → Prop} (hso : SameOutside R mc m)
    (hR : ∀ a, R a → (InRange (σ.sl stackBytes) stackBytes a ∧
        ∀ kn ∈ ([(0x1f0, 8), (0x1c0, 24), (0x158, 20), (0xa0, 20)] : List (Nat × Nat)),
          ¬ InRange (σ.sl kn.1) kn.2 a) ∨
      InRange scratch 8 a ∨ σ.A.Priv L a ∨ ∃ c ∈ Y, InRange c.1 c.2 a) :
    EDSame σ o k kp' mc m := by
  have hblkP : ∀ c ∈ EX o ++ KD k kp' ++ Y, ∀ a, InRange c.1 c.2 a → σ.A.Priv σ.g.L a :=
    fun c hc a h => (hlive.2.2 c hc).2.2 a h
  have hlo := (entry_nums hpre).1
  refine ⟨fun t ht => hso _ fun hr => ?_, fun kn hkn t ht => hso _ fun hr => ?_,
    fun b hb t ht => hso _ fun hr => ?_⟩
  · have hfit := pre_fit hpre ((σ.rest, 16), restR) (by simp [shapeFull])
    have hin : InRange σ.rest 16 (σ.rest + BitVec.ofNat 64 t) := in_self (by simpa using hfit) ht
    have hown : Owned σ (σ.rest + BitVec.ofNat 64 t) := .inr (.inl hin)
    rcases hR _ hr with ⟨hs, -⟩ | h | h | ⟨c, hc, h⟩
    · have h2 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
      have d9 : Apart (σ.sl stackBytes) stackBytes σ.rest 16 :=
        hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      unfold Apart at d9; simp only [InRange] at hs hin; rw [h2] at hs d9; omega
    · have d33 : Apart scratch 8 σ.rest 16 :=
        hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      unfold Apart at d33; simp only [InRange] at h hin
      simp only [scratch, Layout.extraParams, BitVec.toNat_ofNat] at h d33; omega
    · exact owned_not_priv hpre hown (priv_sub hpre hlive h)
    · exact owned_not_priv hpre hown (hblkP c (by simp [hc]) _ h)
  · have hk : kn.1 ≤ 576 ∧ kn.2 ≤ kn.1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
      rcases hkn with rfl | rfl | rfl | rfl <;> decide
    have h3 := sl_toNat hpre (k := kn.1) (by unfold stackBytes; omega)
    have hin : InRange (σ.sl kn.1) kn.2 (σ.sl kn.1 + BitVec.ofNat 64 t) :=
      in_self (by rw [h3]; unfold Layout.ramLo at hlo; omega) ht
    have hst := sl_in_stack hpre (by unfold stackBytes; omega) hk.2 hin
    rcases hR _ hr with ⟨-, hs⟩ | h | h | ⟨c, hc, h⟩
    · exact hs kn hkn hin
    · exact scratch_not_stack hpre h hst
    · exact stack_not_priv hpre hst (priv_sub hpre hlive h)
    · exact stack_not_priv hpre hst (hblkP c (by simp [hc]) _ h)
  · have hram := (hlive.2.2 b (by simp only [List.mem_append] at hb ⊢; exact .inl hb)).2.1
    unfold RamRange Layout.ramHi at hram
    have hin : InRange b.1 b.2 (b.1 + BitVec.ofNat 64 t) := in_self (by omega) ht
    have hP := hblkP b (by simp only [List.mem_append] at hb ⊢; exact .inl hb) _ hin
    rcases hR _ hr with ⟨hs, -⟩ | h | h | ⟨c, hc, h⟩
    · exact stack_not_priv hpre hs hP
    · exact owned_not_priv hpre (.inr (.inr (.inr h))) hP
    · exact σ.A.priv_not_live L _ h ⟨b, hlive.2.1.symm.subset (by
        simp only [List.mem_append] at hb ⊢; exact .inr (.inl hb)), hin⟩
    · have := live_apart hlive hb hc
      simp only [InRange] at hin h; omega

/-! ## `0x80000400`: after `memcpy` -/

/-- `Growing` carries over when its registers and spill slots are kept. -/
theorem growing_keep {σ : Sig} {mc m : Machine} {o : Obs} {k : Kobs} {kp' : Word}
    (h : Growing σ mc o k kp') (hr : ∀ i ∈ ([23, 25] : List (Fin 32)), m.reg i = mc.reg i)
    (hs : ∀ j ∈ ([0x200, 0x1f8, 0x210, 0x208, 0x218, 0x220] : List Nat), ∀ t < 8,
      m.mem (σ.sl j + BitVec.ofNat 64 t) = mc.mem (σ.sl j + BitVec.ofNat 64 t)) :
    Growing σ m o k kp' := by
  obtain ⟨h0, h23, h25, s1, s2, s3, s4, s5, s6⟩ := h
  have l : ∀ j ∈ ([0x200, 0x1f8, 0x210, 0x208, 0x218, 0x220] : List Nat),
      m.load (σ.sl j) 8 = mc.load (σ.sl j) 8 := fun j hj => load_congr (hs j hj)
  exact ⟨h0, (hr 23 (by decide)).trans h23, (hr 25 (by decide)).trans h25,
    (l _ (by simp)).trans s1, (l _ (by simp)).trans s2,
    (l _ (by simp)).trans s3, (l _ (by simp)).trans s4, (l _ (by simp)).trans s5,
    (l _ (by simp)).trans s6⟩

/-- After `memcpy` of an empty list into the new block: `Allocated` again. -/
theorem ret400_empty {σ : Sig} {m : Machine} (h : ARet memcpyC (unit Site3fc) σ m)
    (h27 : m.reg 27 = 0) :
    ∃ o k L kp' p'', Allocated σ m o k L kp' p'' ∧ o.ec.toNat = 0 ∧ o.done = [] := by
  obtain ⟨hcm, -, -⟩ := ret_400 h
  obtain ⟨mc, _, ⟨o, k, L, kp', p'', ⟨hED, hG, r22, r24, hp0, hpres⟩, h27c, ha⟩, hmc, hp⟩ := h
  have hpre := hcm.2.1
  have hreg := memcpy_reg hmc
  have hec : o.ec.toNat = 0 := by rw [← h27c, ← hreg 27, h27]; rfl
  have hdone : o.done = [] := List.eq_nil_of_length_eq_zero (by rw [hG.1, hec])
  have h12 : mc.reg 12 = w (entrySize * o.done.length) := ha.arg 2 (by simp)
  have hn : (mc.reg 12).toNat = 0 := by
    rw [h12, hdone]; rfl
  have hout : ∀ a, ¬ InRange scratch 8 a → m.mem a = mc.mem a := fun a hs =>
    memcpy_out hmc (by simp only [InRange, hn]; omega) hs
  have hso : SameOutside (fun a => InRange scratch 8 a) mc m := fun a ha => hout a ha
  have hlive := hED.2.2.2.2.1
  have hheap : σ.A.Heap L m := σ.A.heap_frame' L mc m hlive.1 (fun a ha => hout a fun hs =>
    owned_not_priv hpre (.inr (.inr (.inr hs))) (priv_sub hpre hlive ha)) (memcpy_preserved hmc)
  have hED' := ed_congr hED hcm hheap (fun i _ => hreg i)
    (edsame_of hpre hlive hso fun a h => .inr (.inl h))
  have hG' := growing_keep hG (fun i _ => hreg i) fun j hj t ht => hout _ fun hs => by
    have hk : j ≤ 576 ∧ 8 ≤ j := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 := sl_toNat hpre (k := j) (by unfold stackBytes; omega)
    have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
    exact scratch_not_stack hpre hs (sl_in_stack hpre (k := j) (n := 8)
      (by unfold stackBytes; omega) hk.2 (in_self (by rw [h3]; omega) ht))
  exact ⟨o, k, L, kp', p'', ⟨hED', hG', (hreg 22).trans r22, (hreg 24).trans r24, hp0,
    Present.of_preserved hpres (memcpy_preserved hmc)⟩, hec, hdone⟩

/-- `Common` depends on memory and five registers. -/
theorem common_congr {σ : Sig} {m m' : Machine} (h : Common σ m) (hmem : m'.mem = m.mem)
    (hr : ∀ i : Fin 32, m'.reg i = m.reg i) : Common σ m' := by
  obtain ⟨rm, pcm, mm⟩ := m
  obtain ⟨r', pc', mm'⟩ := m'
  simp only at hmem; subst hmem
  obtain ⟨hpc, hpre, hro, h2, h8, h9, h18, h19, hsv, hst, hres, hrest, hscr, hfr⟩ := h
  exact ⟨hpc, hpre, hro, (hr 2).trans h2, (hr 8).trans h8, (hr 9).trans h9, (hr 18).trans h18,
    (hr 19).trans h19, hsv, hst, hres, hrest, hscr, hfr⟩

/-- `Allocated` across a step that changes neither memory nor registers. -/
theorem alloc_congr {σ : Sig} {m m' : Machine} {o : Obs} {k : Kobs} {L : List (Word × Nat)}
    {kp' p'' : Word} (h : Allocated σ m o k L kp' p'') (hmem : m'.mem = m.mem)
    (hr : ∀ i : Fin 32, m'.reg i = m.reg i) : Allocated σ m' o k L kp' p'' := by
  obtain ⟨hED, hG, r22, r24, hp0, hpres⟩ := h
  have hm : ∀ a, m'.mem a = m.mem a := fun a => by rw [hmem]
  have hheap : σ.A.Heap L m' := σ.A.heap_frame' L m m' hED.2.2.2.2.1.1 (fun a _ => hm a)
    ⟨fun a h => by rw [hm]; exact h, fun a _ => hm a⟩
  refine ⟨ed_congr hED (common_congr hED.1 hmem hr) hheap (fun i _ => hr i)
    ⟨fun t _ => hm _, fun _ _ t _ => hm _, fun _ _ t _ => hm _⟩,
    growing_keep hG (fun i _ => hr i) (fun _ _ t _ => hm _), (hr 22).trans r22,
    (hr 24).trans r24, hp0, fun j hj => by rw [hm]; exact hpres j hj⟩

theorem TX.leaf_80000400_0 :
    LeafGoal TX.plan TX.plan.cuts[13]! ((TX.plan.leaves 0x80000400)[0]!) := by
  show LeafGoal TX.plan cut400 (run400_leaves[0]!)
  have hcs : (run400_leaves[0]!).conds = [SBool.eq (Sym.var 27) (Sym.lit 0)] := by decide
  intro σ m hA hc
  have hsteps : (run400_leaves[0]!).S.steps - cut400.S.steps = 1 := by decide
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run400_leaves[0]!).exit = .at 0x8000042c := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x8000042c at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SSpill) m m' at hfr
  obtain ⟨hcm, -, hsp⟩ := ret_400 hA
  obtain ⟨-, hm, -⟩ := spill_cut hcm hsp
  have hmem := mem_same_nowrite hcm rfl hm' (by decide) (by decide) hfr
  have hS : ∀ i : Fin 32, (run400_leaves[0]!).S.reg i.val = SSpill.reg i.val := by decide
  have hregs : ∀ i : Fin 32, m'.reg i = m.reg i := fun i => by
    rw [Match.reg_eq hm' i i.val rfl, hS i, ← Match.reg_eq hm i i.val rfl]
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.var 27) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  have h27 : m.reg 27 = 0 := by simp only [SBool.eval, Sym.eval, beq_iff_eq] at h1; exact h1
  obtain ⟨o, k, L, kp', p'', hAl, hec, hdone⟩ := ret400_empty hA h27
  have hAl' : Allocated σ m' o k L kp' p'' := alloc_congr hAl hmem hregs
  refine ExitGoal.at_cut rfl ⟨cut42c, by simp [TX.plan, vcPlan], hex,
    .inl ⟨hex, o, k, L, kp', p'', ⟨hAl', by rw [hdone]; intro i hi; simp [entriesBytes] at hi⟩,
      hec⟩, ?_⟩
  show bTail m' 324 ≤ bTail m 377 - _
  rw [hsteps]; unfold bTail afterEntry; rw [hregs 21, hregs 26]; omega

end ZesuExec.Fn.TX
