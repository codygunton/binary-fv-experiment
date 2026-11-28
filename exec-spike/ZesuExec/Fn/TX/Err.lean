import ZesuExec.Fn.TX.Facts

/-!
# TX: error-exit leaves (programme plan S6 step 6)

The error exit `+0x4a8` writes `res = {0, 0, 3}` and returns through the epilogue. `err_leaf`
reduces such a leaf to its semantic part: the machine at the cut is `Common`, has TX's live list,
and the error class with its consumed count is allowed (`OutcomeAllowed`) with `rest` advanced by
that count. `decodeItem`'s outcome bytes in a frame slot (`f2_result`, `init_slot`) decide the
class from the leaf's conditions.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Bytes of frame slots -/

theorem bytes_of_present {m : Machine} {a : Word} {n : Nat} (h : Present m a n) :
    ∃ bs : List Byte, bs.length = n ∧ BytesAt m a bs := by
  refine ⟨(List.range n).map fun j => (m.mem (a + BitVec.ofNat 64 j)).getD 0, by simp, ?_⟩
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h i hi)
  simp [hb]

/-- An initial frame read at a slot holding `bs`. -/
theorem init_slot {σ : Sig} {m : Machine} {env : Env} (he : BaseEnv σ m env) (hpre : Pre σ.A σ.g σ.m)
    {k : Nat} (hk : k ≤ frameBytes) {bs : List Byte} (hb : BytesAt m (σ.sl k) bs) {off n : Nat}
    (hn : off + n ≤ bs.length) (hk' : bs.length ≤ k) :
    (Sym.init 0 (frameBytes - k + off) n).eval env = ofBytesLE ((bs.drop off).take n) := by
  rw [he.init]
  simp only [Sym.eval]
  congr 1
  have hS := sl_toNat hpre (k := k) (by unfold frameBytes stackBytes at *; omega)
  have hS0 := sl_toNat hpre (k := frameBytes) (by decide)
  have hlo := (entry_nums hpre).1
  induction n generalizing off with
  | zero => simp [byteList]
  | succ n ih =>
    rw [show (bs.drop off).take (n + 1) = bs[off]'(by omega) :: (bs.drop (off + 1)).take n by
      rw [List.drop_eq_getElem_cons (by omega)]; rfl]
    simp only [byteList]
    congr 1
    · simp only [Env.byte0, envB, entryEnv, shapeOf, List.getD_cons_zero]
      rw [show σ.sl frameBytes + BitVec.ofNat 64 (frameBytes - k + off) = σ.sl k + BitVec.ofNat 64 off by
        simp only [Sig.sl, w]; unfold frameBytes at *; bv_omega, hb off (by omega)]
      rfl
    · rw [show frameBytes - k + off + 1 = frameBytes - k + (off + 1) by omega]
      exact ih (by omega)

/-- `decodeItem`'s answer at its call from TX, for the window `bytes` at `inp + off`. -/
theorem f2_result {σ : Sig} {mc m : Machine} (hc : Common σ mc) {k : Nat}
    (hout : mc.reg 10 = σ.sl k) (hk : 40 ≤ k) (hk' : k ≤ frameBytes) {off : Nat}
    (hin : mc.reg 11 = σ.inp + w off) (hlen : off + (mc.reg 12).toNat ≤ σ.len)
    (hpost : F2.Post mc m) :
    ∃ before : List Byte, before.length = 40 ∧ BytesAt m (σ.sl k)
      (F2.result40 (σ.inp + w off) ((σ.input.drop off).take (mc.reg 12).toNat) before) := by
  obtain ⟨before, hl, hb⟩ := bytes_of_present (m := mc) (a := σ.sl k) (n := 40) fun j hj =>
    stack_present' hc (k := k) (j := j) (by omega) (by unfold frameBytes stackBytes at *; omega)
  refine ⟨before, hl, ?_⟩
  have hpre := hc.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinB, hilen, -⟩ := hpre
  have := hpost.2.2 ((σ.input.drop off).take (mc.reg 12).toNat) before ?_ ?_ (by rwa [hout]) hl
  · rwa [hout, hin] at this
  · intro i hi
    simp only [List.length_take, List.length_drop, Sig.input] at hi
    have hil : σ.input.length = σ.len := hilen
    simp only [Sig.len, Sig.rest, Sig.input] at hil hlen ⊢
    have hlt : off + i < σ.len := by simp only [Sig.len, Sig.rest]; omega
    rw [hin, show σ.inp + w off + BitVec.ofNat 64 i = σ.inp + BitVec.ofNat 64 (off + i) by
      simp only [w]; bv_omega, input_same hc hlt]
    simp only [List.getElem_take, List.getElem_drop]
    exact hinB (off + i) (by omega)
  · simp only [List.length_take, List.length_drop, Sig.len, Sig.rest] at hlen ⊢
    have : σ.input.length = (wordAt σ.m (σ.m.reg 12 + 8)).toNat := hilen
    simp only [Sig.input] at this ⊢; omega

/-! ## The error exit as a leaf -/

/-- The semantic part of an error-exit leaf at a machine `m` of the cut. -/
def ErrOk (σ : Sig) (m : Machine) : Prop :=
  Common σ m ∧ (∃ L X, Live σ m L X) ∧ ∃ (cls : OutcomeClass) (cnt : Nat),
    (cls = .invalidInput ∨ cls = .allocationFailure) ∧ OutcomeAllowed σ.input cls cnt ∧
    m.load σ.rest 8 = some (σ.inp + w cnt) ∧
    m.load (σ.rest + 8) 8 = some (wordAt σ.m (σ.rest + 8) - w cnt)

/-- An error-exit leaf of a cut whose state has the base regions and an `envB`-like env. -/
theorem err_leaf {c : Cut Sig} {l : Leaf} (hS : c.S.regions = baseRegions)
    (he : ∀ σ m, c.A σ m → BaseEnv σ m (c.env σ m) ∧ Env.WF (c.env σ m) c.S)
    (hexit : l.exit = .ret retTarget) (hobl : l.obligs = [.aligned retTarget 4])
    (hS'reg : l.S.regions = baseRegions)
    (hsave : ∀ k < 13, l.S.reg (savedReg k).val = .init 0 (576 - 8 * (k + 1)) 8)
    (hsp : l.S.reg 2 = .ptr 0 576) (hmem : l.S.mem = errWrites)
    (hbud : ∀ σ m, c.A σ m → l.S.steps - c.S.steps ≤ c.budget σ m)
    (hsem : ∀ σ m, c.A σ m → (∀ b ∈ l.conds, b.eval (c.env σ m) = true) → ErrOk σ m) :
    LeafGoal TX.plan c l := by
  intro σ m hA hc
  obtain ⟨hbe, hwf⟩ := he σ m hA
  obtain ⟨hcm, ⟨L, X, hlive⟩, cls, cnt, hcls, hall, hr0, hr8⟩ := hsem σ m hA hc
  refine ⟨?_, hbud σ m hA, fun m' hm' hex hfr => ?_⟩
  · rw [hobl]; intro o ho; simp only [List.mem_singleton] at ho; subst ho
    show (retTarget.eval (c.env σ m)).toNat % 4 = 0
    have := saved_eval hcm hbe (k := 0) (by decide)
    simp only [retTarget, Sym.eval, BinOp.eval] at this ⊢
    rw [this]; exact hcm.2.1.2.2.1
  · rw [hexit] at hex ⊢
    exact error_post hcm hlive hbe hwf hS hm' hS'reg hfr hsave hsp hex hmem hcls hall hr0 hr8

/-- A cut whose env is `envB` and whose state is an `entryState` over the base regions. -/
theorem envB_ok {σ : Sig} {m : Machine} {ov : Nat → Option Sym} {ks : List Write}
    (hc : Common σ m) : BaseEnv σ m (envB σ m) ∧ Env.WF (envB σ m) (entryState ov baseRegions ks) :=
  ⟨BaseEnv.ofB σ m, pre_wf hc.2.1 m ov ks⟩
/-! ## Calls that change only TX's stack -/

/-- `Live` survives a call that changes only bytes outside the allocator's memory. -/
theorem live_keep {σ : Sig} {mc m : Machine} {L X : List (Word × Nat)} (hpre : Pre σ.A σ.g σ.m)
    (hlive : Live σ mc L X) {R : Word → Prop} (hso : SameOutside R mc m) (hp : Preserved mc m)
    (hR : ∀ a, R a → InRange (σ.sl stackBytes) stackBytes a) : Live σ m L X :=
  ⟨σ.A.heap_frame' L mc m hlive.1
    (fun a ha => hso a fun hr => stack_not_priv hpre (hR a hr) (priv_sub hpre hlive ha)) hp,
   hlive.2.1, hlive.2.2⟩

/-- `rest` is not on TX's stack. -/
theorem rest_keep {σ : Sig} {mc m : Machine} (hpre : Pre σ.A σ.g σ.m) {R : Word → Prop}
    (hso : SameOutside R mc m) (hR : ∀ a, R a → InRange (σ.sl stackBytes) stackBytes a) :
    m.load σ.rest 8 = mc.load σ.rest 8 ∧ m.load (σ.rest + 8) 8 = mc.load (σ.rest + 8) 8 := by
  have hfit := pre_fit hpre ((σ.rest, 16), restR) (by simp [shapeFull])
  have h2 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have d9 : Apart (σ.sl stackBytes) stackBytes σ.rest 16 :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at d9
  have key : ∀ t < 16, m.mem (σ.rest + BitVec.ofNat 64 t) = mc.mem (σ.rest + BitVec.ofNat 64 t) :=
    fun t ht => hso _ fun hr => by
      have := hR _ hr
      simp only [InRange] at this
      rw [toNat_add_ofNat (by simp at hfit; omega)] at this
      rw [h2] at this d9; omega
  refine ⟨load_congr fun t ht => key t (by omega), load_congr fun t ht => ?_⟩
  rw [show σ.rest + 8 + BitVec.ofNat 64 t = σ.rest + BitVec.ofNat 64 (8 + t) by bv_omega]
  exact key _ (by omega)

/-- `decodeItem`'s frame: the outcome slot `S - k` and the 16 bytes below the call's `sp`. -/
theorem f2_frame {σ : Sig} {mc : Machine} (hc : Common σ mc) {k : Nat} (hout : mc.reg 10 = σ.sl k)
    (hk : 40 ≤ k) (hk' : k ≤ frameBytes) :
    ∀ a, (InRange (mc.reg 10) 40 a ∨ InRange (mc.reg 2 - 16) 16 a) →
      InRange (σ.sl stackBytes) stackBytes a := by
  intro a h
  have hpre := hc.2.1
  rw [hout, show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at h
  rcases h with h | h
  · exact sl_in_stack hpre (by unfold frameBytes stackBytes at *; omega) hk h
  · exact sl_in_stack hpre (by decide) (by decide) h

/-- At `0x80000068`: the outer `decodeItem` returned its outcome for the whole input. -/
theorem ret068 {σ : Sig} {m : Machine} (h : ARet f2C (unit Site064) σ m) :
    Common σ m ∧ (∃ L, Live σ m L []) ∧ m.load σ.rest 8 = some σ.inp ∧
      m.load (σ.rest + 8) 8 = some (w σ.len) ∧
      ∃ before : List Byte, before.length = 40 ∧
        BytesAt m (σ.sl 0x1e8) (F2.result40 σ.inp σ.input before) := by
  have hcm := A068_common h
  obtain ⟨mc, _, hs, hpost, hp⟩ := h
  obtain ⟨hc, ⟨L, hlive⟩, hr0, hr8, -, -, -, ha⟩ := hs
  have hpre := hc.2.1
  have hout : mc.reg 10 = σ.sl 0x1e8 := ha.arg 0 (by simp)
  have hin : mc.reg 11 = σ.inp := ha.arg 1 (by simp)
  have hlen : mc.reg 12 = w σ.len := ha.arg 2 (by simp)
  have hR := f2_frame hc hout (by decide) (by decide)
  obtain ⟨k0, k8⟩ := rest_keep hpre hpost.2.1 hR
  have hl : (mc.reg 12).toNat = σ.len := by
    rw [hlen]; simp only [w, Sig.len, BitVec.toNat_ofNat]; omega
  obtain ⟨before, hbl, hb⟩ := f2_result hc hout (by decide) (by decide) (off := 0)
    (by rw [hin]; simp [w]) (by omega) hpost
  have hil : σ.input.length = σ.len := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hcm, ⟨L, live_keep hpre hlive hpost.2.1 hp hR⟩, k0.trans hr0, k8.trans hr8, before, hbl,
    ?_⟩
  rwa [hl, List.drop_zero, List.take_of_length_le (by omega),
    show σ.inp + w 0 = σ.inp by simp [w]] at hb

/-- Bytes `32, 33` (the error halfword) and `16` (the `isList` byte) of an outcome. -/
theorem result40_err (p : Word) (input before : List Byte) :
    ((F2.result40 p input before).drop 32).take 2 =
      [F2.resultByte p input before 32, F2.resultByte p input before 33] := rfl

theorem result40_list (p : Word) (input before : List Byte) :
    ((F2.result40 p input before).drop 16).take 1 = [F2.resultByte p input before 16] := rfl

/-- The error halfword of an outcome is zero iff `decodeItem` succeeded. -/
theorem err_half {p : Word} {input before : List Byte} :
    ofBytesLE [F2.resultByte p input before 32, F2.resultByte p input before 33] = 0 ↔
      F2.decode input ≠ .error := by
  unfold F2.resultByte
  cases F2.decode input <;> simp [F2.errorByte, F2.successByte] <;> decide

/-- The `isList` byte of a successful outcome. -/
theorem list_byte {p : Word} {input before : List Byte} {b : Bool} {h q : Nat}
    (hd : F2.decode input = .success b h q) :
    ofBytesLE [F2.resultByte p input before 16] &&& 1#64 = if b then 1#64 else 0#64 := by
  unfold F2.resultByte; rw [hd]; cases b <;> simp [F2.successByte] <;> decide

theorem len_word {σ : Sig} : wordAt σ.m (σ.rest + 8) - w 0 = w σ.len := by
  simp [w, Sig.len]

theorem TX.leaf_80000068_0 :
    LeafGoal TX.plan TX.plan.cuts[1]! ((TX.plan.leaves 0x80000068)[0]!) := by
  show LeafGoal TX.plan cut068 (run068_leaves[0]!)
  have hcs : (run068_leaves[0]!).conds = [SBool.ne (Sym.init 0 120 2) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envB_ok (A068_common hA)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_) (fun σ m hA hc => ?_)
  · budget_auto
  obtain ⟨hcm, ⟨L, hlive⟩, hr0, hr8, before, hbl, hb⟩ := ret068 hA
  have h1 : SBool.eval (envB σ m) (SBool.ne (Sym.init 0 120 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  simp only [SBool.eval] at h1
  rw [show (120 : Nat) = frameBytes - 0x1e8 + 32 from rfl,
    init_slot (BaseEnv.ofB σ m) hcm.2.1 (by decide) hb (by simp [F2.result40])
      (by simp [F2.result40]), result40_err] at h1
  have hdec : F2.decode σ.input = .error := by
    cases hd : F2.decode σ.input with
    | error => rfl
    | success b h q =>
      rw [err_half.mpr (by rw [hd]; simp)] at h1; simp [Sym.eval] at h1
  refine ⟨hcm, ⟨L, [], hlive⟩, .invalidInput, 0, .inl rfl,
    ⟨⟨none, by simp [candidate, walk, hdec]⟩, by simp [candidate, walk, hdec, candidateConsumed]⟩,
    by simpa [w] using hr0, by rw [len_word]; exact hr8⟩

theorem TX.leaf_80000068_1 :
    LeafGoal TX.plan TX.plan.cuts[1]! ((TX.plan.leaves 0x80000068)[1]!) := by
  show LeafGoal TX.plan cut068 (run068_leaves[1]!)
  have hcs : (run068_leaves[1]!).conds = [SBool.eq (Sym.init 0 120 2) (Sym.lit 0),
      SBool.eq (Sym.bin BinOp.and (Sym.init 0 104 1) (Sym.lit 1)) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envB_ok (A068_common hA)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_) (fun σ m hA hc => ?_)
  · budget_auto
  obtain ⟨hcm, ⟨L, hlive⟩, hr0, hr8, before, hbl, hb⟩ := ret068 hA
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 120 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m)
      (SBool.eq (Sym.bin BinOp.and (Sym.init 0 104 1) (Sym.lit 1)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  simp only [SBool.eval] at h1 h2
  replace h2 : ((Sym.init 0 104 1).eval (envB σ m) &&& 1#64 == 0#64) = true := h2
  rw [show (120 : Nat) = frameBytes - 0x1e8 + 32 from rfl,
    init_slot (BaseEnv.ofB σ m) hcm.2.1 (by decide) hb (by simp [F2.result40])
      (by simp [F2.result40]), result40_err] at h1
  rw [show (104 : Nat) = frameBytes - 0x1e8 + 16 from rfl,
    init_slot (BaseEnv.ofB σ m) hcm.2.1 (by decide) hb (by simp [F2.result40])
      (by simp [F2.result40]), result40_list] at h2
  have hne : F2.decode σ.input ≠ .error := err_half.mp (by simpa using h1)
  have hdec : ∃ h q, F2.decode σ.input = .success false h q := by
    cases hd : F2.decode σ.input with
    | error => exact absurd hd hne
    | success b h q =>
      rw [list_byte hd] at h2
      cases b
      · exact ⟨h, q, rfl⟩
      · simp at h2
  obtain ⟨h, q, hd⟩ := hdec
  refine ⟨hcm, ⟨L, [], hlive⟩, .invalidInput, 0, .inl rfl,
    ⟨⟨none, by simp [candidate, walk, hd]⟩, by simp [candidate, walk, hd, candidateConsumed]⟩,
    by simpa [w] using hr0, by rw [len_word]; exact hr8⟩

end ZesuExec.Fn.TX
