import ZesuExec.Fn.TX.Err

/-!
# TX: error exits inside the outer walk (programme plan S6 step 6)

Once the outer item is a list, every later rejection makes `candidate` reject with `rest`
advanced past the outer item (`outer_err`): the walk of the remaining window is `none`, so by
`OuterWalked` the walk of the whole payload is `none`.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Outcome bytes in a frame slot -/

theorem slot_val {σ : Sig} {m : Machine} {env : Env} (he : BaseEnv σ m env)
    (hpre : Pre σ.A σ.g σ.m) {k : Nat} (hk : 40 ≤ k) (hk' : k ≤ frameBytes) {p : Word}
    {input before : List Byte} (hb : BytesAt m (σ.sl k) (F2.result40 p input before))
    {off n : Nat} (hn : off + n ≤ 40) :
    (Sym.init 0 (frameBytes - k + off) n).eval env =
      ofBytesLE (((F2.result40 p input before).drop off).take n) :=
  init_slot he hpre hk' hb (by simp [F2.result40]; omega) (by simp [F2.result40]; omega)

/-- A nonzero error halfword: `decodeItem` failed. -/
theorem dec_err {p : Word} {input before : List Byte}
    (h : (ofBytesLE ((((F2.result40 p input before).drop 32).take 2)) != 0#64) = true) :
    F2.decode input = .error := by
  rw [result40_err] at h
  cases hd : F2.decode input with
  | error => rfl
  | success b hh q => rw [err_half.mpr (by rw [hd]; simp)] at h; simp at h

/-- A zero error halfword: `decodeItem` succeeded, a list iff the `isList` bit is set. -/
theorem dec_ok {p : Word} {input before : List Byte}
    (h : (ofBytesLE ((((F2.result40 p input before).drop 32).take 2)) == 0#64) = true) :
    ∃ b hh q, F2.decode input = .success b hh q ∧
      ofBytesLE (((F2.result40 p input before).drop 16).take 1) &&& 1#64 =
        if b then 1#64 else 0#64 := by
  rw [result40_err] at h
  have hne : F2.decode input ≠ .error := err_half.mp (by simpa using h)
  cases hd : F2.decode input with
  | error => exact absurd hd hne
  | success b hh q => exact ⟨b, hh, q, rfl, by rw [result40_list, list_byte hd]⟩

/-! ## The walk -/

theorem w_len {σ : Sig} : w σ.len = wordAt σ.m (σ.rest + 8) := by simp [w, Sig.len]

/-- The walk of a nonempty window whose first item is not a list rejects. -/
theorem entries_none_head {win : List Byte} (hne : win ≠ [])
    (h : ∀ hh q, F2.decode win ≠ .success true hh q) :
    (entriesWalk win.length win).2 = none := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.length_cons, entriesWalk]
  all_goals (split <;> first | rfl | (rename_i hh q hd; exact absurd hd (h hh q)))

/-- The window `win σ o` in input coordinates. -/
theorem win_eq (σ : Sig) (o : Obs) :
    win σ o = (σ.input.drop (o.h + o.i)).take (o.p - o.i) := by
  simp only [win, pl, itemPayload, List.drop_take, List.drop_drop, Nat.add_comm]

theorem win_ne {σ : Sig} {m : Machine} {o : Obs} (hok : OuterOk σ m o) (hi : o.i < o.p)
    (hpre : Pre σ.A σ.g σ.m) : win σ o ≠ [] := by
  have hil : σ.input.length = σ.len := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [win_eq]
  intro he
  have := congrArg List.length he
  simp only [List.length_take, List.length_drop, List.length_nil, Sig.input] at this hil
  have := hok.2.1
  omega

/-- A rejection after the outer item: `rest` is past it, the class is `invalidInput`. -/
theorem outer_err {σ : Sig} {m : Machine} {o : Obs} {L X : List (Word × Nat)} (hcm : Common σ m)
    (hok : OuterOk σ m o) (hlive : Live σ m L X)
    (hnone : (entriesWalk (win σ o).length (win σ o)).2 = none) : ErrOk σ m := by
  obtain ⟨hdec, hle, hr0, hr8, hw⟩ := hok
  have hpl : (entriesWalk (pl σ o).length (pl σ o)).2 = none := by
    rw [hw.2.1]; simp only [win] at hnone; rw [hnone]; rfl
  have hlen : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hcons : itemConsumed o.h o.p = o.h + o.p := Nat.mod_eq_of_lt (by omega)
  have hcand : candidate σ.input = .rejected (some (o.h + o.p)) := by
    simp only [candidate, walk, hdec]
    simp only [pl] at hpl
    rw [hpl, hcons]
  refine ⟨hcm, ⟨L, _, hlive⟩, .invalidInput, o.h + o.p, .inl rfl, ⟨⟨_, hcand⟩, by rw [hcand]; rfl⟩,
    hr0, ?_⟩
  rw [hr8, w_len]
/-! ## Calls that change only TX's stack: what they keep -/

/-- Bytes of the allocator's memory survive a stack-only call. -/
theorem bytes_keep_priv {σ : Sig} {mc m : Machine} {R : Word → Prop} (hpre : Pre σ.A σ.g σ.m)
    (hso : SameOutside R mc m) (hR : ∀ x, R x → InRange (σ.sl stackBytes) stackBytes x)
    {a : Word} {bs : List Byte} (h : BytesAt mc a bs)
    (hp : ∀ i < bs.length, σ.A.Priv σ.g.L (a + BitVec.ofNat 64 i)) : BytesAt m a bs :=
  fun i hi => (hso _ fun hr => stack_not_priv hpre (hR _ hr) (hp i hi)).trans (h i hi)

/-- The bytes of a block of TX's live list are the allocator's. -/
theorem block_priv {σ : Sig} {m : Machine} {L X : List (Word × Nat)} (hlive : Live σ m L X)
    {p : Word} {n : Nat} (hb : (p, n) ∈ X) (hram : RamRange p n) {len : Nat} (hlen : len ≤ n) :
    ∀ i < len, σ.A.Priv σ.g.L (p + BitVec.ofNat 64 i) := fun i hi =>
  (hlive.2.2 _ hb).2.2 _ (by
    unfold RamRange Layout.ramHi at hram
    simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega)

theorem entriesBytes_length : ∀ (es : List EntryValue) (is : List EntryImage),
    is.length = es.length →
    (∀ x ∈ List.zip es is, x.2.padding.length = 4 ∧ x.1.address.length = 20) →
    (entriesBytes es is).length = entrySize * es.length
  | [], _, _, _ => by simp [entriesBytes]
  | _ :: _, [], h, _ => by simp at h
  | e :: es, i :: is, h, hz => by
    have ih := entriesBytes_length es is (by simpa using h) fun x hx => hz x (by simp [hx])
    have he := hz (e, i) (by simp)
    simp only [entriesBytes, List.zipWith_cons_cons, List.flatten_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [entryBytes, wordBytes, he.1, he.2, entrySize]; omega

theorem flatten_length (keys : List (List Byte)) (h : ∀ y ∈ keys, y.length = keySize) :
    keys.flatten.length = keySize * keys.length := by
  induction keys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h y (by simp), ih fun z hz => h z (by simp [hz])]; simp [keySize]; omega

theorem mem_keysBlocks {es : List EntryValue} {is : List EntryImage} {x : EntryValue × EntryImage}
    (hx : x ∈ List.zip es is) (hk : x.1.keys ≠ []) :
    (x.2.keysPtr, keySize * x.1.keys.length) ∈ keysBlocks es is :=
  List.mem_filterMap.mpr ⟨x, hx, by simp [hk]⟩

/-- A 24-byte header at `S - k` survives a call whose frame misses it. -/
theorem hdr_keep {σ : Sig} {mc m : Machine} {R : Word → Prop} (hpre : Pre σ.A σ.g σ.m)
    (hso : SameOutside R mc m) {k : Nat} (hk : 24 ≤ k) (hk' : k ≤ 576)
    (hR : ∀ x, R x → ¬ InRange (σ.sl k) 24 x) {p n c : Word} (h : F1.HeaderIs mc (σ.sl k) p n c) :
    F1.HeaderIs m (σ.sl k) p n c := by
  have h3 := sl_toNat hpre (k := k) (by unfold stackBytes; omega)
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  have key : ∀ t < 24, m.mem (σ.sl k + BitVec.ofNat 64 t) = mc.mem (σ.sl k + BitVec.ofNat 64 t) :=
    fun t ht => hso _ fun hr => hR _ hr (by
      simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega)
  obtain ⟨h0, h8, h16⟩ := h
  refine ⟨(load_congr fun t ht => key t (by omega)).trans h0, ?_, ?_⟩
  · rw [load_congr (m := mc) fun t ht => by
      rw [show σ.sl k + 8 + BitVec.ofNat 64 t = σ.sl k + BitVec.ofNat 64 (8 + t) by bv_omega]
      exact key _ (by omega)]
    exact h8
  · rw [load_congr (m := mc) fun t ht => by
      rw [show σ.sl k + 16 + BitVec.ofNat 64 t = σ.sl k + BitVec.ofNat 64 (16 + t) by bv_omega]
      exact key _ (by omega)]
    exact h16

/-- The entries list survives a stack-only call that misses its header. -/
theorem elist_keep {σ : Sig} {mc m : Machine} {o : Obs} {n : Nat} {L X : List (Word × Nat)}
    {R : Word → Prop} (hpre : Pre σ.A σ.g σ.m) (hel : EList σ mc o n) (hlive : Live σ mc L X)
    (hsub : ∀ b ∈ EX o, b ∈ X) (hso : SameOutside R mc m)
    (hR : ∀ x, R x → InRange (σ.sl stackBytes) stackBytes x)
    (hhdr : ∀ x, R x → ¬ InRange (σ.sl 0x1c0) 24 x) : EList σ m o n := by
  obtain ⟨hH, hle, hp0, hc0, hc32, hram, hil, hbytes, hz⟩ := hel
  refine ⟨hdr_keep hpre hso (by decide) (by decide) hhdr hH, hle, hp0, hc0, hc32, hram, hil, ?_,
    fun x hx => ?_⟩
  · rcases Nat.eq_zero_or_pos o.ec.toNat with he | he
    · have : o.done = [] := List.eq_nil_of_length_eq_zero (by omega)
      have : o.is = [] := List.eq_nil_of_length_eq_zero (by rw [hil, this]; rfl)
      intro i hi; simp [entriesBytes, *] at hi
    · have hlen := entriesBytes_length o.done o.is hil fun x hx => ⟨(hz x hx).1, (hz x hx).2.1⟩
      refine bytes_keep_priv hpre hso hR hbytes
        (block_priv hlive (hsub _ (by simp [EX, he])) (hram he) (len := (entriesBytes o.done o.is).length)
          (by rw [hlen]; exact Nat.mul_le_mul_left _ hle))
  · obtain ⟨hpad, haddr, hkl, hkram, hkb⟩ := hz x hx
    refine ⟨hpad, haddr, hkl, hkram, ?_⟩
    by_cases hk : x.1.keys = []
    · rw [hk]; intro i hi; simp at hi
    · exact bytes_keep_priv hpre hso hR hkb
        (block_priv hlive (hsub _ (by simp only [EX, List.mem_append]; exact .inr (mem_keysBlocks hx hk)))
          (hkram hk) (by rw [flatten_length _ hkl]; exact Nat.le_refl _))

/-- The frame word at `S - j` survives a `decodeItem` call with its outcome at `S - k`. -/
theorem f2_slot_keep {σ : Sig} {mc m : Machine} (hc : Common σ mc) {k : Nat}
    (hout : mc.reg 10 = σ.sl k) (hk : 40 ≤ k) (hk' : k ≤ 576)
    (hso : SameOutside (fun a => InRange (mc.reg 10) 40 a ∨ InRange (mc.reg 2 - 16) 16 a) mc m)
    {j : Nat} (hj : 8 ≤ j) (hj' : j ≤ 576) (hd : k + 8 ≤ j ∨ j + 40 ≤ k) {v : Word}
    (h : mc.load (σ.sl j) 8 = some v) : m.load (σ.sl j) 8 = some v := by
  have hpre := hc.2.1
  refine frame_keep hpre hso hj' hj (fun a hr hin => ?_) h
  rw [hout, show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at hr
  have h1 := sl_toNat hpre (k := k) (by unfold stackBytes; omega)
  have h2 := sl_toNat hpre (k := 592) (by decide)
  have h3 := sl_toNat hpre (k := j) (by unfold stackBytes; omega)
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  simp only [InRange, h1, h2, h3] at hr hin; omega

/-- `decodeItem` with its outcome at `S - k` (`k ≤ 0x1a8`) misses the entries list header. -/
theorem f2_hdr {σ : Sig} {mc : Machine} (hc : Common σ mc) {k : Nat} (hout : mc.reg 10 = σ.sl k)
    (hk : 40 ≤ k) (hk' : k ≤ 0x1a8) :
    ∀ x, (InRange (mc.reg 10) 40 x ∨ InRange (mc.reg 2 - 16) 16 x) →
      ¬ InRange (σ.sl 0x1c0) 24 x := by
  intro x hr hin
  have hpre := hc.2.1
  rw [hout, show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at hr
  have h1 := sl_toNat hpre (k := k) (by unfold stackBytes; omega)
  have h2 := sl_toNat hpre (k := 592) (by decide)
  have h3 := sl_toNat hpre (k := 0x1c0) (by decide)
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  simp only [InRange, h1, h2, h3] at hr hin; omega

/-- `OuterState` survives a `decodeItem` call with its outcome at `S - k` (`k ≤ 0x1a8`). -/
theorem outer_keep {σ : Sig} {mc m : Machine} {o : Obs} {L : List (Word × Nat)}
    (hs : OuterState σ mc o L) (hcm : Common σ m) {k : Nat} (hout : mc.reg 10 = σ.sl k)
    (hk : 40 ≤ k) (hk' : k ≤ 0x1a8) (hpost : F2.Post mc m) (hp : Preserved mc m) :
    OuterState σ m o L := by
  obtain ⟨hc, hok, ⟨r20, r21, hi, hmag⟩, ⟨r24, r25, r27⟩, hel, hlive⟩ := hs
  have hpre := hc.2.1
  have hR := f2_frame hc hout hk (by unfold frameBytes; omega)
  obtain ⟨k0, k8⟩ := rest_keep hpre hpost.2.1 hR
  have hs : ∀ i ∈ calleeSaved, m.reg i = mc.reg i := hpost.1.2
  refine ⟨hcm, ⟨hok.1, hok.2.1, k0.trans hok.2.2.1, k8.trans hok.2.2.2.1, hok.2.2.2.2⟩,
    ⟨(hs 20 (by decide)).trans r20, (hs 21 (by decide)).trans r21, hi,
      f2_slot_keep hc hout hk (by omega) hpost.2.1 (by decide) (by decide) (by omega) hmag⟩,
    ⟨(hs 24 (by decide)).trans r24, (hs 25 (by decide)).trans r25, (hs 27 (by decide)).trans r27⟩,
    elist_keep hpre hel hlive (fun b hb => hb) hpost.2.1 hR (f2_hdr hc hout hk hk'),
    live_keep hpre hlive hpost.2.1 hp hR⟩

/-! ## `0x800000d8`: after the entry's `decodeItem` -/
/-! ## `0x800000d8`: after the entry's `decodeItem` -/

theorem ret0d8 {σ : Sig} {m : Machine} (h : ARet f2C (unit Site0d4) σ m) :
    Common σ m ∧ ∃ o L, OuterState σ m o L ∧ ∃ before : List Byte,
      BytesAt m (σ.sl 0x1a8) (F2.result40 (curPtr σ o) (win σ o) before) := by
  have hcm := A0d8_common h
  obtain ⟨mc, _, ⟨o, L, hs, ha⟩, hpost, hp⟩ := h
  obtain ⟨hc, hok, hregs, hcon, hel, hlive⟩ := hs
  have hpre := hc.2.1
  have hout : mc.reg 10 = σ.sl 0x1a8 := ha.arg 0 (by simp)
  have hin : mc.reg 11 = curPtr σ o := ha.arg 1 (by simp)
  have hlen : mc.reg 12 = w (o.p - o.i) := ha.arg 2 (by simp)
  have hR := f2_frame hc hout (by decide) (by decide)
  obtain ⟨k0, k8⟩ := rest_keep hpre hpost.2.1 hR
  have hle := hok.2.1
  have hi := hregs.2.2.1
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hl : (mc.reg 12).toNat = o.p - o.i := by
    rw [hlen]; simp only [w, BitVec.toNat_ofNat]; omega
  obtain ⟨before, -, hb⟩ := f2_result hc hout (by decide) (by decide) (off := o.h + o.i)
    (by rw [hin]; rfl) (by omega) hpost
  have hw : (σ.input.drop (o.h + o.i)).take (mc.reg 12).toNat = win σ o := by rw [hl, win_eq]
  rw [hw, show σ.inp + w (o.h + o.i) = curPtr σ o from rfl] at hb
  exact ⟨hcm, o, L, outer_keep ⟨hc, hok, hregs, hcon, hel, hlive⟩ hcm hout (by decide) (by decide)
    hpost hp, before, hb⟩
theorem TX.leaf_800000d8_0 :
    LeafGoal TX.plan TX.plan.cuts[3]! ((TX.plan.leaves 0x800000d8)[0]!) := by
  show LeafGoal TX.plan cut0d8 (run0d8_leaves[0]!)
  have hcs : (run0d8_leaves[0]!).conds = [SBool.ne (Sym.init 0 184 2) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envB_ok (A0d8_common hA)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_) (fun σ m hA hc => ?_)
  · have : (run0d8_leaves[0]!).S.steps - SBody.steps = 21 := by decide
    show _ ≤ 32 * outerLeft m + 220; simp only [cut0d8, mkCut] at *; omega
  obtain ⟨hcm, o, L, hs, before, hb⟩ := ret0d8 hA
  have h1 : SBool.eval (envB σ m) (SBool.ne (Sym.init 0 184 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  simp only [SBool.eval] at h1
  rw [show (184 : Nat) = frameBytes - 0x1a8 + 32 from rfl,
    slot_val (BaseEnv.ofB σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h1
  have hdec := dec_err (by simpa [Sym.eval] using h1)
  exact outer_err hcm hs.2.1 hs.2.2.2.2.2 (entries_none_head (win_ne hs.2.1 hs.2.2.1.2.2.1 hcm.2.1)
    fun hh q h => by rw [hdec] at h; cases h)

theorem TX.leaf_800000d8_1 :
    LeafGoal TX.plan TX.plan.cuts[3]! ((TX.plan.leaves 0x800000d8)[1]!) := by
  show LeafGoal TX.plan cut0d8 (run0d8_leaves[1]!)
  have hcs : (run0d8_leaves[1]!).conds = [SBool.eq (Sym.init 0 184 2) (Sym.lit 0),
      SBool.eq (Sym.bin BinOp.and (Sym.init 0 168 1) (Sym.lit 1)) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envB_ok (A0d8_common hA)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_) (fun σ m hA hc => ?_)
  · have : (run0d8_leaves[1]!).S.steps - SBody.steps = 24 := by decide
    show _ ≤ 32 * outerLeft m + 220; simp only [cut0d8, mkCut] at *; omega
  obtain ⟨hcm, o, L, hs, before, hb⟩ := ret0d8 hA
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 184 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m)
      (SBool.eq (Sym.bin BinOp.and (Sym.init 0 168 1) (Sym.lit 1)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  simp only [SBool.eval] at h1 h2
  replace h2 : ((Sym.init 0 168 1).eval (envB σ m) &&& 1#64 == 0#64) = true := h2
  rw [show (184 : Nat) = frameBytes - 0x1a8 + 32 from rfl,
    slot_val (BaseEnv.ofB σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h1
  rw [show (168 : Nat) = frameBytes - 0x1a8 + 16 from rfl,
    slot_val (BaseEnv.ofB σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h2
  obtain ⟨b, hh, q, hd, hl⟩ := dec_ok (by simpa [Sym.eval] using h1)
  rw [hl] at h2
  cases b
  · exact outer_err hcm hs.2.1 hs.2.2.2.2.2 (entries_none_head (win_ne hs.2.1 hs.2.2.1.2.2.1 hcm.2.1)
      fun hh' q' h => by rw [hd] at h; cases h)
  · simp at h2

end ZesuExec.Fn.TX
