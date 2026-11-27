import ZesuExec.Fn.F4.Regions
import ZesuExec.Fn.F0.Proof

/-!
# Lemmas shared by the F4 and F5 proofs (`toOwnedSlice` for element size `eb`)

`Entry eb A L items m` names the facts of `ToOwned.Pre`. The entry environment `env0 m`, its
extensions `EnvOk`, the invariant `Inv` (changes stay in `Allowed`, bytes survive), and the
calls `alloc`, `free` and `memcpy` as reusable steps whose continuation is the next run.
-/

namespace ZesuExec.Fn.ToOwned
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-- The entry facts of `Pre`, with names. -/
structure Entry (eb : Nat) (A : AllocAssumptions zesuImage) (L : List (Word × Nat))
    (items : List Byte) (m : Machine) : Prop where
  ro : RodataLoaded zesuImage m
  stack : StackOk m 112
  ra : RetAligned m
  resRam : RamRange (m.reg 10) 24
  resAl : (m.reg 10).toNat % 8 = 0
  resP : Present m (m.reg 10) 24
  hdrRam : RamRange (m.reg 11) 24
  hdrAl : (m.reg 11).toNat % 8 = 0
  hdr : HeaderIs m (m.reg 11) (listPtr m) (listLen m) (listCap m)
  nc : (listLen m).toNat ≤ (listCap m).toNat
  itemsLen : items.length = (listLen m).toNat * eb
  p0 : 0 < (listPtr m).toNat
  buf : 0 < (listCap m).toNat →
    RamRange (listPtr m) ((listCap m).toNat * eb) ∧ (listPtr m, (listCap m).toNat * eb) ∈ L
  items : BytesAt m (listPtr m) items
  aoRam : RamRange (m.reg 12) 16
  aoAl : (m.reg 12).toNat % 8 = 0
  aoCtx : (m.load (m.reg 12) 8).isSome
  aoVt : m.load (m.reg 12 + 8) 8 = some (BitVec.ofNat 64 vtable)
  scr : Present m scratch 8
  heap : A.Heap L m
  d_rh : Apart (m.reg 10) 24 (m.reg 11) 24
  d_ra : Apart (m.reg 10) 24 (m.reg 12) 16
  d_rs : Apart (m.reg 10) 24 (m.reg 2 - 112) 112
  d_rx : Apart (m.reg 10) 24 scratch 8
  d_ha : Apart (m.reg 11) 24 (m.reg 12) 16
  d_hs : Apart (m.reg 11) 24 (m.reg 2 - 112) 112
  d_hx : Apart (m.reg 11) 24 scratch 8
  d_as : Apart (m.reg 12) 16 (m.reg 2 - 112) 112
  d_ax : Apart (m.reg 12) 16 scratch 8
  d_sx : Apart (m.reg 2 - 112) 112 scratch 8
  dbuf : 0 < (listCap m).toNat →
    Apart (listPtr m) ((listCap m).toNat * eb) (m.reg 10) 24 ∧
    Apart (listPtr m) ((listCap m).toNat * eb) (m.reg 11) 24 ∧
    Apart (listPtr m) ((listCap m).toNat * eb) (m.reg 12) 16 ∧
    Apart (listPtr m) ((listCap m).toNat * eb) (m.reg 2 - 112) 112 ∧
    Apart (listPtr m) ((listCap m).toNat * eb) scratch 8
  priv : ∀ a, InRange (m.reg 10) 24 a ∨ InRange (m.reg 11) 24 a ∨ InRange (m.reg 12) 16 a ∨
    InRange (m.reg 2 - 112) 112 a ∨ InRange scratch 8 a → ¬ A.Priv L a

theorem Entry.of_pre {eb : Nat} {A : AllocAssumptions zesuImage} {L : List (Word × Nat)}
    {items : List Byte} {m : Machine} (h : Pre eb A L items m) : Entry eb A L items m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩

theorem present_of_load {m : Machine} {a v : Word} {n : Nat} (h : m.load a n = some v)
    (hn : n ≤ 8) : ∀ t < n, (m.mem (a + BitVec.ofNat 64 t)).isSome := by
  intro t ht; rw [load_bytes h hn t ht]; rfl

/-- Every rodata byte of the image lies below RAM. -/
theorem zesu_rodata_low {a b : Nat} (h : zesuImage.rodataByte? a = some b) : a < Layout.ramLo := by
  have := (zesu_rodata_range h).2; unfold Layout.rodataHi at this; unfold Layout.ramLo; omega

theorem scratch_toNat (j : Nat) (hj : j < 8) :
    (scratch + BitVec.ofNat 64 j).toNat = Layout.extraParams + j := by
  simp [scratch, Layout.extraParams]; omega

/-- The bytes of a region no write of `S` overlaps in `[lo, hi)` are the initial ones. -/
theorem bytes_kept {env : Env} {S : SState} {mf : Machine} {r lo hi : Nat} (hm : Match env S mf)
    (hr : r < S.regions.length)
    (hnw : S.mem.all (fun w => !(w.r == r && decide (w.off < hi) && decide (lo < w.off + w.n))) = true) :
    ∀ j, lo ≤ j → j < hi → j < env.size r →
      mf.mem (env.base r + BitVec.ofNat 64 j) = some (env.byte0 r j) := by
  intro j h1 h2 hj
  rw [hm.mem r j hr hj]
  have : S.mem.find? (·.covers r j) = none := List.find?_eq_none.mpr fun w hw => by
    have := List.all_eq_true.mp hnw w hw
    simp only [Write.covers, Bool.not_eq_true', Bool.and_eq_false_imp, beq_iff_eq,
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.and_eq_true] at this ⊢
    intro hr'; exact this ⟨hr'.1.1, by omega⟩ (by omega)
  simp [memByte, this]

section
variable {eb : Nat} {A : AllocAssumptions zesuImage} {L : List (Word × Nat)} {items : List Byte}
  {m : Machine}

/-- The entry environment. -/
abbrev env0 (m : Machine) : Env := entryEnv m ((shape m).map (·.1))

theorem Entry.sp (E : Entry eb A L items m) : (m.reg 2).toNat ≥ Layout.ramLo + 112 ∧
    (m.reg 2).toNat ≤ Layout.ramHi ∧ (m.reg 2).toNat % 16 = 0 :=
  ⟨E.stack.2.1, E.stack.2.2.1, E.stack.1⟩

theorem sp96 (E : Entry eb A L items m) : (m.reg 2 - 96).toNat = (m.reg 2).toNat - 96 := by
  have := E.sp.1; unfold Layout.ramLo at this
  rw [BitVec.toNat_sub]; simp; omega

theorem sp112 (E : Entry eb A L items m) : (m.reg 2 - 112).toNat = (m.reg 2).toNat - 112 := by
  have := E.sp.1; unfold Layout.ramLo at this
  rw [BitVec.toNat_sub]; simp; omega

theorem Entry.wf (E : Entry eb A L items m) : Env.WF (env0 m) S0 := by
  obtain ⟨hlo, hhi, hal⟩ := E.sp
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  have h96 := sp96 E; have h112 := sp112 E
  have := E.resRam; have := E.hdrRam; have := E.aoRam
  have := E.d_rh; have := E.d_ra; have := E.d_rs; have := E.d_ha; have := E.d_hs; have := E.d_as
  simp only [RamRange, Apart, Layout.ramLo, Layout.ramHi, h112] at *
  refine entry_wf (shape m) ?_ ?_
  · simp only [shape, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;>
      simp [RegionOk, frameR, resultR, headerR, allocObjR, Machine.writable, Machine.readable,
        Machine.inRange, Layout.ramLo, Layout.ramHi, Layout.rodataLo, Layout.rodataHi,
        Layout.inputLo, Layout.inputHi, E.resAl, E.hdrAl, E.aoAl] <;> omega
  · simp [shape, Fn.Disjoint]; omega

theorem Entry.match (E : Entry eb A L items m) : Match (env0 m) S0 m := by
  obtain ⟨hlo, hhi, hal⟩ := E.sp
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  obtain ⟨hp, hn, hc⟩ := E.hdr
  refine entry_match (fun i hi s hs => ?_) (fun r j hr hj => ?_) ?_
  · simp only [ov] at hs
    split at hs
    · next h => cases hs; have : i = 2 := Fin.ext h; subst this
                simp [Sym.eval, Env.base, entryEnv, shape, BitVec.sub_add_cancel]
    · split at hs
      · next h => cases hs; have : i = 10 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shape]
      · split at hs
        · next h => cases hs; have : i = 11 := Fin.ext h; subst this
                    simp [Sym.eval, Env.base, entryEnv, shape]
        · split at hs
          · next h => cases hs; have : i = 12 := Fin.ext h; subst this
                      simp [Sym.eval, Env.base, entryEnv, shape]
          · simp at hs
  · simp only [List.length_cons, List.length_nil] at hr
    have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr' with rfl | rfl | rfl | rfl <;> simp [Env.size, Env.base, entryEnv, shape] at hj ⊢
    · have := E.stack.2.2.2 (16 + j) (by omega)
      rwa [show m.reg 2 - BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 + j) = m.reg 2 - 96 + BitVec.ofNat 64 j by
        bv_omega] at this
    · exact E.resP j hj
    · rcases (show j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) by omega) with h | h | h
      · exact present_of_load hp (by decide) j h
      · have := present_of_load hn (by decide) (j - 8) (by omega)
        rwa [show m.reg 11 + 8 + BitVec.ofNat 64 (j - 8) = m.reg 11 + BitVec.ofNat 64 j by
          bv_omega] at this
      · have := present_of_load hc (by decide) (j - 16) (by omega)
        rwa [show m.reg 11 + 16 + BitVec.ofNat 64 (j - 16) = m.reg 11 + BitVec.ofNat 64 j by
          bv_omega] at this
    · rcases (show j < 8 ∨ (8 ≤ j ∧ j < 16) by omega) with h | h
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp E.aoCtx
        exact present_of_load hv (by decide) j h
      · have := present_of_load E.aoVt (by decide) (j - 8) (by omega)
        rwa [show m.reg 12 + 8 + BitVec.ofNat 64 (j - 8) = m.reg 12 + BitVec.ofNat 64 j by
          bv_omega] at this
  · intro k hk t ht
    simp [known] at hk; subst hk
    have := load_bytes E.aoVt (by decide) t ht
    rw [show m.reg 12 + 8 + BitVec.ofNat 64 t = m.reg 12 + BitVec.ofNat 64 (8 + t) by bv_omega] at this
    simp [Env.byte0, entryEnv, shape, this, Sym.eval]

theorem Entry.cap (E : Entry eb A L items m) : (Sym.init 2 16 8).eval (env0 m) = listCap m := by
  have := E.hdrRam; unfold RamRange Layout.ramHi at this
  exact init_eval_load (by simp [shape]) (by simpa [shape] using E.hdr.2.2) (by simp [shape]; omega)

theorem Entry.len (E : Entry eb A L items m) : (Sym.init 2 8 8).eval (env0 m) = listLen m := by
  have := E.hdrRam; unfold RamRange Layout.ramHi at this
  exact init_eval_load (by simp [shape]) (by simpa [shape] using E.hdr.2.1) (by simp [shape]; omega)

theorem Entry.ptr (E : Entry eb A L items m) : (Sym.init 2 0 8).eval (env0 m) = listPtr m := by
  have := E.hdrRam; unfold RamRange Layout.ramHi at this
  exact init_eval_load (by simp [shape]) (by simpa [shape] using E.hdr.1) (by simp [shape]; omega)

theorem Entry.ctx (E : Entry eb A L items m) :
    (Sym.init 3 0 8).eval (env0 m) = wordAt m (m.reg 12) := by
  have := E.aoRam; unfold RamRange Layout.ramHi at this
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp E.aoCtx
  have : wordAt m (m.reg 12) = v := by simp [wordAt, hv]
  rw [this]
  exact init_eval_load (by simp [shape]) (by simpa [shape] using hv) (by simp [shape]; omega)

/-- An environment that extends the entry environment (`env0` with fresh variables). -/
structure EnvOk (m : Machine) (env : Env) : Prop where
  vars : ∀ i : Fin 32, env.vars i.val = m.reg i
  base0 : env.base 0 = m.reg 2 - 96
  size0 : env.size 0 = 96
  base1 : env.base 1 = m.reg 10
  size1 : env.size 1 = 24
  mem1 : ∀ j, env.mem0 1 j = (m.mem (m.reg 10 + BitVec.ofNat 64 j)).getD 0
  base2 : env.base 2 = m.reg 11
  size2 : env.size 2 = 24
  mem2 : ∀ j, env.mem0 2 j = (m.mem (m.reg 11 + BitVec.ofNat 64 j)).getD 0
  mem3 : ∀ j, env.mem0 3 j = (m.mem (m.reg 12 + BitVec.ofNat 64 j)).getD 0
  base3 : env.base 3 = m.reg 12
  size3 : env.size 3 = 16
  len : env.regions.length = 4

theorem envOk0 (m : Machine) : EnvOk m (env0 m) where
  vars i := by simp [entryEnv]
  base0 := by simp [entryEnv, Env.base, shape]
  size0 := by simp [entryEnv, Env.size, shape]
  base1 := by simp [entryEnv, Env.base, shape]
  size1 := by simp [entryEnv, Env.size, shape]
  mem1 j := by simp [entryEnv, shape]
  base2 := by simp [entryEnv, Env.base, shape]
  size2 := by simp [entryEnv, Env.size, shape]
  mem2 j := by simp [entryEnv, shape]
  mem3 j := by simp [entryEnv, shape]
  base3 := by simp [entryEnv, Env.base, shape]
  size3 := by simp [entryEnv, Env.size, shape]
  len := by simp [entryEnv, shape]

theorem EnvOk.setVars {env : Env} (h : EnvOk m env) {F : Nat} (hF : 32 ≤ F)
    (f : Nat → Word) : EnvOk m (env.setVars F f) where
  vars i := by simp [Env.setVars, show ¬ F ≤ i.val by omega, h.vars i]
  base0 := h.base0
  size0 := h.size0
  base1 := h.base1
  size1 := h.size1
  mem1 := h.mem1
  base2 := h.base2
  size2 := h.size2
  mem2 := h.mem2
  mem3 := h.mem3
  base3 := h.base3
  size3 := h.size3
  len := h.len

theorem EnvOk.init_eq {env : Env} (he : EnvOk m env) (r off n : Nat) (hr : r = 2 ∨ r = 3) :
    (Sym.init r off n).eval env = (Sym.init r off n).eval (env0 m) := by
  have : env.byte0 r = (env0 m).byte0 r := by
    funext j; simp only [Env.byte0]
    rcases hr with rfl | rfl
    · rw [he.mem2]; simp [entryEnv, shape]
    · rw [he.mem3]; simp [entryEnv, shape]
  simp only [Sym.eval, this]

/-- A run that never wrote the header leaves it as at entry. -/
theorem Entry.header_same (E : Entry eb A L items m) {env : Env} {S : SState} {mf : Machine}
    (he : EnvOk m env) (hm : Match env S mf) (hr : 2 < S.regions.length)
    (hnw : S.mem.all (fun w => w.r != 2) = true) :
    HeaderIs mf (m.reg 11) (listPtr m) (listLen m) (listCap m) := by
  have hsame := region_same (m := m) hm hr hnw (by
    intro j hj
    rw [he.size2] at hj
    rw [he.mem2, he.base2]
    obtain ⟨hp, hn, hc⟩ := E.hdr
    rcases (show j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) by omega) with h | h | h
    · rw [load_bytes hp (by decide) j h]; rfl
    · have := load_bytes hn (by decide) (j - 8) (by omega)
      rw [show m.reg 11 + 8 + BitVec.ofNat 64 (j - 8) = m.reg 11 + BitVec.ofNat 64 j by bv_omega] at this
      rw [this]; rfl
    · have := load_bytes hc (by decide) (j - 16) (by omega)
      rw [show m.reg 11 + 16 + BitVec.ofNat 64 (j - 16) = m.reg 11 + BitVec.ofNat 64 j by bv_omega] at this
      rw [this]; rfl)
  rw [he.base2, he.size2] at hsame
  obtain ⟨hp, hn, hc⟩ := E.hdr
  have h0 : mf.load (m.reg 11) 8 = m.load (m.reg 11) 8 :=
    load_congr fun t ht => hsame t (by omega)
  have h8 : mf.load (m.reg 11 + 8) 8 = m.load (m.reg 11 + 8) 8 := load_congr fun t ht => by
    rw [show m.reg 11 + 8 + BitVec.ofNat 64 t = m.reg 11 + BitVec.ofNat 64 (8 + t) by bv_omega]
    exact hsame (8 + t) (by omega)
  have h16 : mf.load (m.reg 11 + 16) 8 = m.load (m.reg 11 + 16) 8 := load_congr fun t ht => by
    rw [show m.reg 11 + 16 + BitVec.ofNat 64 t = m.reg 11 + BitVec.ofNat 64 (16 + t) by bv_omega]
    exact hsame (16 + t) (by omega)
  exact ⟨h0 ▸ hp, h8 ▸ hn, h16 ▸ hc⟩

/-- Result bytes `[lo, hi)` no write of the final state touched are as at entry. -/
theorem Entry.result_same (E : Entry eb A L items m) {env : Env} {S : SState} {mf : Machine}
    {lo hi : Nat} (he : EnvOk m env) (hm : Match env S mf) (hr : 1 < S.regions.length)
    (hhi : hi ≤ 24)
    (hnw : S.mem.all (fun w => !(w.r == 1 && decide (w.off < hi) && decide (lo < w.off + w.n))) = true) :
    SameBytes m mf (m.reg 10) lo hi := by
  intro j h1 h2
  have := bytes_kept hm hr hnw j h1 h2 (by rw [he.size1]; omega)
  rw [he.base1] at this; rw [this]
  simp only [Env.byte0]; rw [he.mem1]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (E.resP j (by omega))
  rw [hb]; rfl

/-- Loading from a region at the end of a run. -/
theorem region_load {env : Env} {S : SState} {mf : Machine} {r : Nat} {R : Region}
    (hwf : Env.WF env S) (hm : Match env S mf) (hR : S.regions[r]? = some R)
    (off n : Nat) (_hal : off % n = 0) (_hra : R.align % n = 0) (hb : off + n ≤ env.size r) :
    mf.load (env.base r + BitVec.ofNat 64 off) n = some ((readConst S r off n).eval env) :=
  load_cst hwf hm hR hb

/-- What the function may change (`Post`'s frame). -/
def Allowed (eb : Nat) (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m : Machine)
    (a : Word) : Prop :=
  InRange (m.reg 10) 24 a ∨ InRange (m.reg 11) 24 a ∨ InRange (m.reg 2 - 112) 112 a ∨
    InRange scratch 8 a ∨ A.Priv L a ∨
    (0 < (listCap m).toNat ∧ InRange (listPtr m) ((listCap m).toNat * eb) a)

/-- What holds of every machine along the run: changes stay in `Allowed`, bytes survive. -/
def Inv (eb : Nat) (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m mk : Machine) : Prop :=
  SameOutside (Allowed eb A L m) m mk ∧ Preserved m mk

theorem Inv.refl : Inv eb A L m m := ⟨fun _ _ => rfl, Preserved.refl m⟩

theorem Inv.ro (E : Entry eb A L items m) {mk : Machine} (h : Inv eb A L m mk) :
    RodataLoaded zesuImage mk :=
  RodataLoaded.preserved E.ro h.2 fun _ _ hb => zesu_rodata_low hb

theorem Inv.step {mk mf : Machine} {R : Word → Prop} (h : Inv eb A L m mk)
    (hfr : SameOutside R mk mf) (hR : ∀ a, R a → Allowed eb A L m a) (hp : Preserved mk mf) :
    Inv eb A L m mf :=
  ⟨fun a ha => (hfr a fun hr => ha (hR a hr)).trans (h.1 a ha), h.2.trans hp⟩

/-- F4's and F5's own writes: frame, result, header. -/
def Own (m : Machine) (a : Word) : Prop :=
  InRange (m.reg 2 - 96) 96 a ∨ InRange (m.reg 10) 24 a ∨ InRange (m.reg 11) 24 a

theorem Entry.regionAddr (E : Entry eb A L items m) {env : Env} (he : EnvOk m env) {r j : Nat}
    (hr : r < 4) (hj : j < env.size r) :
    InRange (m.reg 2 - 96) 96 (env.base r + BitVec.ofNat 64 j) ∨
      InRange (m.reg 10) 24 (env.base r + BitVec.ofNat 64 j) ∨
      InRange (m.reg 11) 24 (env.base r + BitVec.ofNat 64 j) ∨
      InRange (m.reg 12) 16 (env.base r + BitVec.ofNat 64 j) := by
  have hsp := E.sp; have hr' := E.resRam; have hh := E.hdrRam; have ha := E.aoRam
  unfold Layout.ramLo Layout.ramHi at hsp; unfold RamRange Layout.ramHi at hr' hh ha
  have h96 := sp96 E
  rcases r with _ | _ | _ | _ | r
  · rw [he.size0] at hj; rw [he.base0]
    refine .inl ?_; simp only [InRange, h96]; rw [toNat_add_ofNat (by omega), h96]; omega
  · rw [he.size1] at hj; rw [he.base1]
    refine .inr (.inl ?_); simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  · rw [he.size2] at hj; rw [he.base2]
    refine .inr (.inr (.inl ?_)); simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  · rw [he.size3] at hj; rw [he.base3]
    refine .inr (.inr (.inr ?_)); simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  · omega

/-- The writable regions of the runs are the frame, the result and the header. -/
theorem Entry.inWritable2 (E : Entry eb A L items m) {env : Env} {S : SState} (he : EnvOk m env)
    (hS : S.regions = [frameR, resultR, headerR, allocObjR]) {a : Word} (h : InWritable env S a) :
    Own m a := by
  obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := h
  rw [hS] at hR
  have hsp := E.sp; have hr' := E.resRam; have hh := E.hdrRam
  unfold Layout.ramLo Layout.ramHi at hsp; unfold RamRange Layout.ramHi at hr' hh
  have h96 := sp96 E
  rcases r with _ | _ | _ | _ | r <;> simp at hR <;> subst hR
  · rw [he.size0] at hj; rw [he.base0]
    refine .inl ?_; simp only [InRange, h96]; rw [toNat_add_ofNat (by omega), h96]; omega
  · rw [he.size1] at hj; rw [he.base1]
    refine .inr (.inl ?_); simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  · rw [he.size2] at hj; rw [he.base2]
    refine .inr (.inr ?_); simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  · simp [allocObjR] at hw

theorem frame_sub_stack {a : Word} (E : Entry eb A L items m)
    (h : InRange (m.reg 2 - 96) 96 a) : InRange (m.reg 2 - 112) 112 a := by
  have h96 := sp96 E; have h112 := sp112 E
  simp only [InRange, h96, h112] at h ⊢; omega

theorem Entry.ownAllowed (E : Entry eb A L items m) {a : Word} (h : Own m a) : Allowed eb A L m a := by
  rcases h with h | h | h
  · exact .inr (.inr (.inl (frame_sub_stack E h)))
  · exact .inl h
  · exact .inr (.inl h)

theorem Entry.inWritable' (E : Entry eb A L items m) {env : Env} {S : SState} (he : EnvOk m env)
    (hS : S.regions = [frameR, resultR, headerR, allocObjR]) {a : Word} (h : InWritable env S a) :
    Allowed eb A L m a :=
  E.ownAllowed (E.inWritable2 he hS h)

theorem Entry.ownNotPriv (E : Entry eb A L items m) {a : Word} (h : Own m a) : ¬ A.Priv L a := by
  apply E.priv
  rcases h with h | h | h
  · exact .inr (.inr (.inr (.inl (frame_sub_stack E h))))
  · exact .inl h
  · exact .inr (.inl h)

theorem Entry.scratchNotOwn (E : Entry eb A L items m) {j : Nat} (hj : j < 8)
    (h : Own m (scratch + BitVec.ofNat 64 j)) : False := by
  have hs := scratch_toNat j hj
  have d1 := E.d_rx; have d2 := E.d_hx; have d3 := E.d_sx
  have h96 := sp96 E; have h112 := sp112 E
  simp only [Own, Apart, InRange, hs, h96, h112] at d1 d2 d3 h
  simp [scratch, Layout.extraParams] at d1 d2 d3 h
  omega

theorem Entry.oldNotOwn (E : Entry eb A L items m) (hc0 : 0 < (listCap m).toNat)
    {a : Word} (hin : InRange (listPtr m) ((listCap m).toNat * eb) a) (h : Own m a) : False := by
  obtain ⟨dr, dh, -, ds, -⟩ := E.dbuf hc0
  have h96 := sp96 E; have h112 := sp112 E
  simp only [Own, Apart, InRange, h96, h112] at dr dh ds hin h
  omega

/-- The callee frame below the function's frame avoids every region of the runs. -/
theorem Entry.calleeApart (E : Entry eb A L items m) {env : Env} (he : EnvOk m env) :
    ∀ r j, r < 4 → j < env.size r → ¬ InRange (m.reg 2 - 112) 16 (env.base r + BitVec.ofNat 64 j) := by
  intro r j hr hj hin
  have d1 := E.d_rs; have d2 := E.d_hs; have d3 := E.d_as
  have h96 := sp96 E; have h112 := sp112 E; have := E.sp.1; unfold Layout.ramLo at this
  rcases E.regionAddr he hr hj with h | h | h | h <;>
    simp only [Apart, InRange, h96, h112] at d1 d2 d3 hin h <;> omega

/-- A region address is never the allocator's. -/
theorem Entry.regionNotPriv (E : Entry eb A L items m) {env : Env} (he : EnvOk m env) {r j : Nat}
    (hr : r < 4) (hj : j < env.size r) : ¬ A.Priv L (env.base r + BitVec.ofNat 64 j) := by
  apply E.priv
  rcases E.regionAddr he hr hj with h | h | h | h
  · exact .inr (.inr (.inr (.inl (frame_sub_stack E h))))
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))

/-- A region address is not in the old buffer. -/
theorem Entry.regionNotOld (E : Entry eb A L items m) {env : Env} (he : EnvOk m env) {r j : Nat}
    (hc0 : 0 < (listCap m).toNat) (hr : r < 4) (hj : j < env.size r) :
    ¬ InRange (listPtr m) ((listCap m).toNat * eb) (env.base r + BitVec.ofNat 64 j) := by
  intro hin
  obtain ⟨dr, dh, da, ds, -⟩ := E.dbuf hc0
  have h96 := sp96 E; have h112 := sp112 E
  rcases E.regionAddr he hr hj with h | h | h | h <;>
    simp only [Apart, InRange, h96, h112] at dr dh da ds hin h <;> omega

theorem Entry.regionNotScratch (E : Entry eb A L items m) {env : Env} (he : EnvOk m env) {r j : Nat}
    (hr : r < 4) (hj : j < env.size r) :
    ¬ InRange scratch 8 (env.base r + BitVec.ofNat 64 j) := by
  intro hin
  have d1 := E.d_rx; have d2 := E.d_hx; have d3 := E.d_ax; have d4 := E.d_sx
  have h96 := sp96 E; have h112 := sp112 E
  rcases E.regionAddr he hr hj with h | h | h | h <;>
    simp only [Apart, InRange, h96, h112, scratch, Layout.extraParams, BitVec.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow] at d1 d2 d3 d4 hin h <;> omega

/-- The stack bytes a callee uses are present. -/
theorem Entry.calleeStack (E : Entry eb A L items m) {mk : Machine} (hp : Preserved m mk)
    (hsp : mk.reg 2 = m.reg 2 - 96) : StackOk mk 16 := by
  have hs := E.stack; have h96 := sp96 E
  unfold StackOk at hs ⊢
  rw [hsp, h96]
  refine ⟨by omega, by omega, by omega, fun j hj => ?_⟩
  have := hp.1 _ (hs.2.2.2 j (by omega))
  rwa [show m.reg 2 - BitVec.ofNat 64 112 + BitVec.ofNat 64 j =
    m.reg 2 - 96 - BitVec.ofNat 64 16 + BitVec.ofNat 64 j by bv_omega] at this

theorem Entry.calleeFree (E : Entry eb A L items m) {mk : Machine} {L' : List (Word × Nat)}
    (hL : ∀ a, A.Priv L' a → A.Priv L a) (hsp : mk.reg 2 = m.reg 2 - 96) :
    CalleeFrameFree (A.Priv L') mk := by
  intro a ha hp
  apply E.priv a _ (hL a hp)
  refine .inr (.inr (.inr (.inl ?_)))
  have h96 := sp96 E; have h112 := sp112 E
  have : (mk.reg 2 - 16).toNat = (m.reg 2).toNat - 112 := by
    rw [hsp, BitVec.toNat_sub, h96]; have := E.sp.1; unfold Layout.ramLo at this; simp; omega
  simp only [InRange, this, h112] at ha ⊢; omega

theorem calleeAllowed {a : Word}
    (h : InRange (m.reg 2 - 112) 16 a) : Allowed eb A L m a :=
  .inr (.inr (.inl ⟨h.1, by have := h.2; omega⟩))

theorem Entry.itemsOld (E : Entry eb A L items m) {i : Nat} (hi : i < items.length) :
    0 < (listCap m).toNat ∧ InRange (listPtr m) ((listCap m).toNat * eb) (listPtr m + BitVec.ofNat 64 i) := by
  have hlen := E.itemsLen; have hnc := E.nc
  have hc : 0 < (listCap m).toNat := by
    rw [hlen] at hi
    rcases Nat.eq_zero_or_pos (listCap m).toNat with h | h
    · rw [show (listLen m).toNat = 0 by omega] at hi; simp at hi
    · exact h
  refine ⟨hc, ?_⟩
  have := (E.buf hc).1; unfold RamRange Layout.ramHi at this
  have h' : items.length ≤ (listCap m).toNat * eb := by
    rw [hlen]; exact Nat.mul_le_mul_right _ hnc
  simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega

/-- The old buffer is not the allocator's and not a callee frame. -/
theorem Entry.oldSafe (E : Entry eb A L items m) (hc : 0 < (listCap m).toNat) {x : Word}
    (hx : InRange (listPtr m) ((listCap m).toNat * eb) x) :
    ¬ A.Priv L x ∧ ¬ InRange (m.reg 2 - 112) 16 x := by
  refine ⟨fun hp => A.priv_not_live L x hp ⟨_, (E.buf hc).2, hx⟩, fun h => ?_⟩
  obtain ⟨-, -, -, ds, -⟩ := E.dbuf hc
  have h112 := sp112 E
  simp only [Apart, InRange, h112] at ds h hx; omega

/-- The scratch word is neither the allocator's nor a callee frame. -/
theorem Entry.scratchSafe (E : Entry eb A L items m) {j : Nat} (hj : j < 8) :
    ¬ A.Priv L (scratch + BitVec.ofNat 64 j) ∧
      ¬ InRange (m.reg 2 - 112) 16 (scratch + BitVec.ofNat 64 j) := by
  have hs := scratch_toNat j hj
  have hin : InRange scratch 8 (scratch + BitVec.ofNat 64 j) := by
    simp only [InRange]; rw [hs]; simp [scratch, Layout.extraParams]; omega
  refine ⟨E.priv _ (.inr (.inr (.inr (.inr hin)))), fun h => ?_⟩
  have d := E.d_sx; have h112 := sp112 E
  simp only [InRange] at h; rw [hs, h112] at h
  simp only [Apart, h112, scratch, Layout.extraParams, BitVec.toNat_ofNat, Nat.reduceMod,
    Nat.reducePow] at d h; omega


/-! ## Calls -/

/-- The allocator's answer, as `alloc_spec` states it for a request of `g` bytes. -/
def AllocOut (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (g : Nat) (m2 : Machine) : Prop :=
  (m2.reg 10 = 0 ∧ A.Heap L m2) ∨
  (m2.reg 10 ≠ 0 ∧ A.Heap (L ++ [(m2.reg 10, g)]) m2 ∧ RamRange (m2.reg 10) g ∧ Present m2 (m2.reg 10) g ∧
    (∀ a, InRange (m2.reg 10) g a → A.Priv L a) ∧ (∀ a, A.Priv (L ++ [(m2.reg 10, g)]) a → A.Priv L a))

/-- The four regions of every run. -/
abbrev Regs4 (S : SState) : Prop := S.regions = [frameR, resultR, headerR, allocObjR]

/-- A call of `alloc(ctx, sz, align, ret)` and the return from it. -/
theorem alloc_step (E : Entry eb A L items m) {env : Env} {S Sl : SState} {mk mc : Machine}
    {b F sz : Nat} {Q : Machine → Prop}
    (he : EnvOk m env) (hS : Regs4 S) (hSl : Regs4 Sl) (hmc : Match env Sl mc) (hwf : Env.WF env S)
    (hex : mc.pc.toNat = allocEntry) (hfr : SameOutside (InWritable env S) mk mc) (hp : Preserved mk mc)
    (hinv : Inv eb A L m mk) (hheap : A.Heap L mk) (hscr : ScratchSame m mk)
    (hitems : BytesAt mk (listPtr m) items) (hwfB : Sl.wfB F = true)
    (g11 : (mc.reg 11).toNat = sz) (hsz : 0 < sz ∧ sz < 2 ^ 63) (g12 : (mc.reg 12).toNat ≤ 3)
    (hra : RetAligned mc) (g2 : mc.reg 2 = m.reg 2 - 96)
    (k : ∀ m2, Match (env.setVars F fun i => m2.reg (Fin.ofNat 32 i)) (Sl.override (callOv Sl F none)) m2 →
      Env.WF (env.setVars F fun i => m2.reg (Fin.ofNat 32 i)) (Sl.override (callOv Sl F none)) →
      Returns mc m2 → Inv eb A L m m2 → ScratchSame m m2 → BytesAt m2 (listPtr m) items →
      AllocOut A L sz m2 → Reaches zesuImage b Q m2) :
    Reaches zesuImage (53 + b) Q mc := by
  have own : ∀ a, InWritable env S a → Own m a := fun a h => E.inWritable2 he hS h
  have hheapc : A.Heap L mc := A.heap_frame L mk mc hheap fun a ha => hfr a fun hw =>
    E.ownNotPriv (own a hw) ha
  have hpre : A.Heap L mc ∧ 0 < (mc.reg 11).toNat ∧ (mc.reg 11).toNat < 2 ^ 63 ∧
      (mc.reg 12).toNat ≤ 3 ∧ StackOk mc 16 ∧ RetAligned mc ∧ CalleeFrameFree (A.Priv L) mc :=
    ⟨hheapc, by omega, by omega, g12, E.calleeStack (hinv.2.trans hp) g2, hra,
      E.calleeFree (fun _ h => h) g2⟩
  have hcall := Reaches.preserve (A.alloc_spec L mc (by simpa [allocEntry] using hex) hpre)
  refine Reaches.trans hcall fun m2 hpost => ?_
  obtain ⟨⟨hret, hfrA, hout⟩, hp2⟩ := hpost
  rw [g11] at hout
  have hcf : mc.reg 2 - 16 = m.reg 2 - 112 := by rw [g2]; bv_omega
  rw [hcf] at hfrA
  have hframe : ∀ r j, r < Sl.regions.length → j < env.size r →
      m2.mem (env.base r + BitVec.ofNat 64 j) = mc.mem (env.base r + BitVec.ofNat 64 j) := by
    intro r j hr hj
    have hr4 : r < 4 := by rw [hSl] at hr; simpa using hr
    refine hfrA _ fun h => ?_
    rcases h with h | h
    · exact E.regionNotPriv he hr4 hj h
    · exact E.calleeApart he r j hr4 hj h
  obtain ⟨hm2, hwf2⟩ := after_call_ov (F := F) (a0 := none) hmc (hwf.congr (hSl.trans hS.symm)) hwfB
    hret (fun s h => by simp at h) hframe
  have hinv2 : Inv eb A L m m2 := by
    refine (hinv.step hfr (fun a h => E.inWritable' he hS h) hp).step hfrA ?_ hp2
    intro a h
    rcases h with h | h
    · exact .inr (.inr (.inr (.inr (.inl h))))
    · exact calleeAllowed h
  have hsame : ∀ x, ¬ A.Priv L x → ¬ InRange (m.reg 2 - 112) 16 x → ¬ Own m x →
      m2.mem x = mk.mem x :=
    fun x h1 h2 h3 => (hfrA x fun h => h.elim h1 h2).trans (hfr x fun hw => h3 (own x hw))
  refine k m2 hm2 hwf2 hret hinv2 (fun j hj => ?_) (fun i hi => ?_) hout
  · obtain ⟨h1, h2⟩ := E.scratchSafe hj
    rw [hsame _ h1 h2 (E.scratchNotOwn hj)]; exact hscr j hj
  · obtain ⟨hc, hin⟩ := E.itemsOld hi
    obtain ⟨h1, h2⟩ := E.oldSafe hc hin
    rw [hsame _ h1 h2 (E.oldNotOwn hc hin)]; exact hitems i hi

/-- A call of `free(ctx, p, c * eb, align, ret)` on the old buffer and the return from it. -/
theorem free_step (E : Entry eb A L items m) {env : Env} {S Sl : SState} {mk mc : Machine}
    {b F : Nat} {L' : List (Word × Nat)} {Q : Machine → Prop} (heb : 0 < eb)
    (he : EnvOk m env) (hS : Regs4 S) (hSl : Regs4 Sl) (hmc : Match env Sl mc) (hwf : Env.WF env S)
    (hex : mc.pc.toNat = freeEntry) (hfr : SameOutside (InWritable env S) mk mc) (hp : Preserved mk mc)
    (hinv : Inv eb A L m mk) (hc0 : 0 < (listCap m).toNat) (hheap : A.Heap L' mk)
    (hpriv : ∀ a, A.Priv L' a → A.Priv L a)
    (hmem : (listPtr m, (listCap m).toNat * eb) ∈ L') (hwfB : Sl.wfB F = true)
    (g11 : mc.reg 11 = listPtr m) (g12 : (mc.reg 12).toNat = (listCap m).toNat * eb)
    (g13 : (mc.reg 13).toNat ≤ 3) (hra : RetAligned mc) (g2 : mc.reg 2 = m.reg 2 - 96)
    (k : ∀ m2, Match (env.setVars F fun i => m2.reg (Fin.ofNat 32 i)) (Sl.override (callOv Sl F none)) m2 →
      Env.WF (env.setVars F fun i => m2.reg (Fin.ofNat 32 i)) (Sl.override (callOv Sl F none)) →
      Returns mc m2 → Inv eb A L m m2 →
      A.Heap (L'.erase (listPtr m, (listCap m).toNat * eb)) m2 →
      (∀ a, A.Priv (L'.erase (listPtr m, (listCap m).toNat * eb)) a →
        A.Priv L a ∨ InRange (listPtr m) ((listCap m).toNat * eb) a) →
      (∀ x, ¬ A.Priv L' x → ¬ InRange (listPtr m) ((listCap m).toNat * eb) x →
        ¬ InRange (m.reg 2 - 112) 16 x → ¬ Own m x → m2.mem x = mk.mem x) →
      Reaches zesuImage b Q m2) :
    Reaches zesuImage (42 + b) Q mc := by
  have own : ∀ a, InWritable env S a → Own m a := fun a h => E.inWritable2 he hS h
  have hcR := (E.buf hc0).1; unfold RamRange Layout.ramHi at hcR
  have hheapc : A.Heap L' mc := A.heap_frame L' mk mc hheap fun a ha => hfr a fun hw =>
    E.ownNotPriv (own a hw) (hpriv a ha)
  have hpre : A.Heap L' mc ∧ (mc.reg 11, (mc.reg 12).toNat) ∈ L' ∧ 0 < (mc.reg 12).toNat ∧
      (mc.reg 12).toNat < 2 ^ 63 ∧ (mc.reg 13).toNat ≤ 3 ∧ StackOk mc 16 ∧ RetAligned mc ∧
      CalleeFrameFree (A.Priv L') mc := by
    refine ⟨hheapc, ?_, ?_, ?_, g13, E.calleeStack (hinv.2.trans hp) g2, hra, E.calleeFree hpriv g2⟩
    · rw [g11, g12]; exact hmem
    · rw [g12]; exact Nat.mul_pos hc0 heb
    · rw [g12]; omega
  have hcall := Reaches.preserve (A.free_spec L' mc (by simpa [freeEntry] using hex) hpre)
  refine Reaches.trans hcall fun m2 hpost => ?_
  obtain ⟨⟨hret, hfrF, hheap2, hpriv2⟩, hp2⟩ := hpost
  rw [g11, g12] at hfrF hheap2 hpriv2
  have hcf : mc.reg 2 - 16 = m.reg 2 - 112 := by rw [g2]; bv_omega
  rw [hcf] at hfrF
  have hframe : ∀ r j, r < Sl.regions.length → j < env.size r →
      m2.mem (env.base r + BitVec.ofNat 64 j) = mc.mem (env.base r + BitVec.ofNat 64 j) := by
    intro r j hr hj
    have hr4 : r < 4 := by rw [hSl] at hr; simpa using hr
    refine hfrF _ fun h => ?_
    rcases h with h | h | h
    · exact E.regionNotPriv he hr4 hj (hpriv _ h)
    · exact E.regionNotOld he hc0 hr4 hj h
    · exact E.calleeApart he r j hr4 hj h
  obtain ⟨hm2, hwf2⟩ := after_call_ov (F := F) (a0 := none) hmc (hwf.congr (hSl.trans hS.symm)) hwfB
    hret (fun s h => by simp at h) hframe
  have hinv2 : Inv eb A L m m2 := by
    refine (hinv.step hfr (fun a h => E.inWritable' he hS h) hp).step hfrF ?_ hp2
    intro a h
    rcases h with h | h | h
    · exact .inr (.inr (.inr (.inr (.inl (hpriv a h)))))
    · exact .inr (.inr (.inr (.inr (.inr ⟨hc0, h⟩))))
    · exact calleeAllowed h
  refine k m2 hm2 hwf2 hret hinv2 hheap2 (fun a h => (hpriv2 a h).imp_left (hpriv a)) fun x h1 h2 h3 h4 => ?_
  exact (hfrF x fun h => h.elim h1 fun h => h.elim h2 h3).trans (hfr x fun hw => h4 (own x hw))

/-- The `memcpy` call of the success path: the items go to the new block `p'`, the byte count
to the scratch word. -/
theorem copy_step (E : Entry eb A L items m) {env : Env} {S Sl : SState} {m2 mc : Machine} {b : Nat}
    {p' : Word} {Q : Machine → Prop} (heb : 0 < eb)
    (he : EnvOk m env) (hS : Regs4 S) (hSl : Regs4 Sl) (hwf : Env.WF env S) (hmc : Match env Sl mc)
    (hex : mc.pc.toNat = Layout.memcpyEntry) (hfr : SameOutside (InWritable env S) m2 mc)
    (hp : Preserved m2 mc) (hinv : Inv eb A L m m2) (hn0 : 0 < (listLen m).toNat)
    (hitemsP : BytesAt m2 (listPtr m) items)
    (hheap : A.Heap (L ++ [(p', (listLen m).toNat * eb)]) m2)
    (hram' : RamRange p' ((listLen m).toNat * eb))
    (hpres' : Present m2 p' ((listLen m).toNat * eb))
    (hblk : ∀ a, InRange p' ((listLen m).toNat * eb) a → A.Priv L a)
    (hpriv : ∀ a, A.Priv (L ++ [(p', (listLen m).toNat * eb)]) a → A.Priv L a)
    (g10 : mc.reg 10 = p') (g11 : mc.reg 11 = listPtr m)
    (g12 : mc.reg 12 = BitVec.ofNat 64 ((listLen m).toNat * eb)) (hra : RetAligned mc)
    (k : ∀ m3, Match env Sl m3 → Env.WF env Sl → m3.pc = (mc.reg 1 &&& ~~~(1 : Word)) →
      Inv eb A L m m3 → BytesAt m3 p' items →
      BytesAt m3 scratch (wordBytes (BitVec.ofNat 64 ((listLen m).toNat * eb))) →
      A.Heap (L ++ [(p', (listLen m).toNat * eb)]) m3 → Reaches zesuImage b Q m3) :
    Reaches zesuImage (3 + b) Q mc := by
  have own : ∀ a, InWritable env S a → Own m a := fun a h => E.inWritable2 he hS h
  have hnc := E.nc; have hlen := E.itemsLen
  have hc0 : 0 < (listCap m).toNat := by omega
  obtain ⟨hbR, hbL⟩ := E.buf hc0
  have hb := hbR; unfold RamRange Layout.ramHi Layout.ramLo at hb
  have hram := hram'; unfold RamRange Layout.ramHi Layout.ramLo at hram
  have hle : (listLen m).toNat * eb ≤ (listCap m).toNat * eb := Nat.mul_le_mul_right _ hnc
  have hpos : 0 < (listLen m).toNat * eb := Nat.mul_pos hn0 heb
  have hn32 : (listLen m).toNat * eb < 2 ^ 64 := by omega
  have r12 : (mc.reg 12).toNat = (listLen m).toNat * eb := by
    rw [g12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32]
  have hp2 := hinv.2.trans hp
  have hinP : ∀ i, i < items.length → InRange (listPtr m) ((listCap m).toNat * eb)
      (listPtr m + BitVec.ofNat 64 i) := fun i hi => (E.itemsOld hi).2
  have hitemsC : BytesAt mc (listPtr m) items := fun i hi => by
    rw [hfr _ fun hw => E.oldNotOwn hc0 (hinP i hi) (own _ hw)]; exact hitemsP i hi
  have hne : p' ≠ listPtr m := by
    intro e
    have hpr := hblk p' ⟨Nat.le_refl _, by omega⟩
    rw [e] at hpr
    exact A.priv_not_live L _ hpr ⟨_, hbL, by
      simp only [InRange]; have := Nat.mul_pos hc0 heb; omega⟩
  have hscrC : Present mc scratch 8 := fun j hj => hp2.1 _ (E.scr j hj)
  have hdom : ziskMemcpyDomain mc = true := by
    unfold ziskMemcpyDomain
    rw [g10, g11, g12]
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨⟨⟨hra, by decide⟩, ?_⟩, .inr ?_⟩
    · unfold Machine.present
      exact readBytes_isSome_of fun t ht => by
        have := hscrC t ht
        rwa [show scratch + BitVec.ofNat 64 t = BitVec.ofNat 64 (Layout.extraParams + t) by
          simp only [scratch]; bv_omega] at this
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · simp only [Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi, Layout.rodataLo,
          Layout.rodataHi, Layout.inputLo, Layout.inputHi, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq]; omega
      · unfold Machine.present
        exact readBytes_isSome_of fun t ht => by
          rw [ofNat_toNat_add, hitemsC t (by rw [hlen]; exact ht)]; rfl
      · simp only [Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi, Bool.and_eq_true,
          decide_eq_true_eq]; omega
      · unfold Machine.present
        exact readBytes_isSome_of fun t ht => by
          rw [ofNat_toNat_add]; exact hp.1 _ (hpres' t ht)
  have hcall := Reaches.preserve (memcpy_spec zesuImage mc (by simpa using hex) hdom)
  refine Reaches.trans hcall fun m3 hpost => ?_
  obtain ⟨hz, hp3⟩ := hpost
  have hz : ziskMemcpy mc = some m3 := hz
  have hdst : ∀ x, InRange (mc.reg 10) (mc.reg 12).toNat x → A.Priv L x := by
    intro x hx; rw [g10, r12] at hx; exact hblk x hx
  have hout : ∀ x, ¬ (InRange (mc.reg 10) (mc.reg 12).toNat x ∨ InRange scratch 8 x) →
      m3.mem x = mc.mem x :=
    fun x hx => memcpy_out hz (fun h => hx (.inl h)) (fun h => hx (.inr h))
  have hm3 : Match env Sl m3 := Match.congr_machine hmc (memcpy_reg hz) fun r j hr hj => by
    have hr4 : r < 4 := by rw [hSl] at hr; simpa using hr
    exact hout _ fun h => h.elim (fun h => E.regionNotPriv he hr4 hj (hdst _ h))
      (fun h => E.regionNotScratch he hr4 hj h)
  have hinv3 : Inv eb A L m m3 := by
    refine (hinv.step hfr (fun a h => E.inWritable' he hS h) hp).step (R := fun x =>
      InRange (mc.reg 10) (mc.reg 12).toNat x ∨ InRange scratch 8 x)
      (fun x hx => hout x hx) (fun x h => ?_) (memcpy_preserved hz)
    rcases h with h | h
    · exact .inr (.inr (.inr (.inr (.inl (hdst x h)))))
    · exact .inr (.inr (.inr (.inl h)))
  refine k m3 hm3 (hwf.congr (hSl.trans hS.symm)) (memcpy_eq hz ▸ rfl) hinv3 ?_ ?_ ?_
  · -- the items, copied
    intro i hi
    have hi' : i < (mc.reg 12).toNat := by rw [r12, ← hlen]; exact hi
    have hne' : mc.reg 10 ≠ mc.reg 11 := by rw [g10, g11]; exact hne
    have := memcpy_dst hz hi' hne'
      (by rw [g10, r12]; omega)
      (by rw [g11, r12]; omega)
      (by rw [g11]; intro h; obtain ⟨-, -, -, -, d⟩ := E.dbuf hc0
          have hin := hinP i hi
          simp only [Apart, InRange, scratch, Layout.extraParams, BitVec.toNat_ofNat, Nat.reduceMod,
            Nat.reducePow] at d h hin; omega)
    rw [g10, g11] at this
    rw [this]; exact hitemsC i hi
  · -- the byte count
    intro i hi
    have hi8 : i < 8 := by simpa [wordBytes] using hi
    have hin : InRange scratch 8 (scratch + BitVec.ofNat 64 i) := by
      simp only [InRange]; rw [scratch_toNat i hi8]; simp [scratch, Layout.extraParams]; omega
    have hsp := (E.scratchSafe hi8).1
    rw [show scratch = BitVec.ofNat 64 Layout.extraParams from rfl] at hsp hin ⊢
    rw [memcpy_scratch hz hi8 fun h => hsp (hdst _ h), g12]
    simp [wordBytes]
  · -- the heap
    refine A.heap_frame _ m2 m3 hheap fun a ha => ?_
    rw [hout a fun h => ?_, hfr a fun hw => E.ownNotPriv (own a hw) (hpriv a ha)]
    rcases h with h | h
    · exact A.priv_not_live _ a ha ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by
        rw [g10, r12] at h; exact h⟩
    · exact E.priv a (.inr (.inr (.inr (.inr h)))) (hpriv a ha)

/-- The `remap` call (F0, returns null) from the entry and the return from it. -/
theorem remap_step (E : Entry eb A L items m) {Sl : SState} {mc : Machine} {b : Nat}
    {Q : Machine → Prop} (hSl : Regs4 Sl) (hmc : Match (env0 m) Sl mc)
    (hex : mc.pc.toNat = F0.entry) (hfr : SameOutside (InWritable (env0 m) S0) m mc)
    (hp : Preserved m mc) (hwfB : Sl.wfB 100 = true) (hra : RetAligned mc)
    (g2 : mc.reg 2 = m.reg 2 - 96)
    (k : ∀ m2, Match ((env0 m).setVars 100 fun i => m2.reg (Fin.ofNat 32 i))
        (Sl.override (callOv Sl 100 (some (.lit 0)))) m2 →
      Env.WF ((env0 m).setVars 100 fun i => m2.reg (Fin.ofNat 32 i))
        (Sl.override (callOv Sl 100 (some (.lit 0)))) →
      Returns mc m2 → Inv eb A L m m2 → A.Heap L m2 → ScratchSame m m2 →
      BytesAt m2 (listPtr m) items → Reaches zesuImage b Q m2) :
    Reaches zesuImage (9 + b) Q mc := by
  have own : ∀ a, InWritable (env0 m) S0 a → Own m a :=
    fun a h => E.inWritable2 (envOk0 m) rfl h
  have hinv1 : Inv eb A L m mc := Inv.refl.step hfr (fun a h => E.inWritable' (envOk0 m) rfl h) hp
  have hpre : F0.Pre mc := ⟨hinv1.ro E, E.calleeStack hp g2, hra⟩
  have hcall := Reaches.preserve (F0.f0_spec mc (by simpa [F0.entry] using hex) hpre)
  refine Reaches.trans hcall fun m2 hpost => ?_
  obtain ⟨⟨hret, ha0, hfrR⟩, hp2⟩ := hpost
  have hcf : mc.reg 2 - 16 = m.reg 2 - 112 := by rw [g2]; bv_omega
  rw [hcf] at hfrR
  obtain ⟨hm2, hwf2⟩ := after_call_ov (F := 100) (a0 := some (.lit 0)) hmc (E.wf.congr hSl)
    hwfB hret (fun s h => by cases h; rw [ha0]; rfl)
    (fun r j hr hj => hfrR _ (E.calleeApart (envOk0 m) r j (by rw [hSl] at hr; simpa using hr) hj))
  have hsame : ∀ x, ¬ InRange (m.reg 2 - 112) 16 x → ¬ Own m x → m2.mem x = m.mem x :=
    fun x h1 h2 => (hfrR x h1).trans (hfr x fun hw => h2 (own x hw))
  refine k m2 hm2 hwf2 hret (hinv1.step hfrR (fun a h => calleeAllowed h) hp2) ?_ ?_ ?_
  · exact A.heap_frame L m m2 E.heap fun a ha => hsame a
      (fun h => E.priv a (.inr (.inr (.inr (.inl ⟨h.1, by have := h.2; omega⟩)))) ha)
      (fun h => E.ownNotPriv h ha)
  · intro j hj
    exact hsame _ (E.scratchSafe hj).2 (E.scratchNotOwn hj)
  · intro i hi
    obtain ⟨hc, hin⟩ := E.itemsOld hi
    obtain ⟨-, h2⟩ := E.oldSafe hc hin
    rw [hsame _ h2 (E.oldNotOwn hc hin)]; exact E.items i hi

/-- A `ret` leaf: the function returns, and its changes stay in `Allowed`. -/
theorem ret_leaf (E : Entry eb A L items m) {env : Env} {S Sf : SState} {mk mf : Machine}
    (he : EnvOk m env) (hS : Regs4 S) (hmf : Match env Sf mf)
    (hregs : (calleeSaved.filter (· ≠ 2)).all (fun i => Sf.reg i.val == .var i.val) = true)
    (hsp2 : Sf.reg 2 = .ptr 0 96)
    (hex : mf.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env)
    (hinv : Inv eb A L m mk) (hfr : SameOutside (InWritable env S) mk mf) (hp : Preserved mk mf) :
    Returns m mf ∧ Inv eb A L m mf :=
  ⟨returns_leaf hmf he.vars hregs
    (by rw [hsp2]; show env.base 0 + BitVec.ofInt 64 96 = m.reg 2
        rw [he.base0]; simp [BitVec.sub_add_cancel]) hex,
   hinv.step hfr (fun a h => E.inWritable' he hS h) hp⟩

/-- The return obligation of a `ret` leaf. -/
theorem ret_oblig (E : Entry eb A L items m) {env : Env} (he : EnvOk m env) :
    Oblig.holds env (.aligned (.bin .and (.var 1) (.lit 18446744073709551614)) 4) := by
  simpa [Oblig.holds, Sym.eval, BinOp.eval, show env.vars 1 = m.reg 1 from he.vars 1] using E.ra


/-! ## Bounds and final loads -/

theorem Entry.capBound (E : Entry eb A L items m) : (listCap m).toNat * eb < 2 ^ 32 := by
  rcases Nat.eq_zero_or_pos (listCap m).toNat with h | h
  · rw [h]; simp
  · have := (E.buf h).1; unfold RamRange Layout.ramHi at this; omega

theorem Entry.lenBound (E : Entry eb A L items m) : (listLen m).toNat * eb < 2 ^ 32 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ E.nc) E.capBound

theorem hdr_load {env : Env} {S : SState} {mf : Machine} (he : EnvOk m env) (hwf : Env.WF env S)
    (hm : Match env S mf) (hS : Regs4 S) (off : Nat) (hoff : off % 8 = 0 ∧ off + 8 ≤ 24) :
    mf.load (m.reg 11 + BitVec.ofNat 64 off) 8 = some ((readConst S 2 off 8).eval env) := by
  rw [← he.base2]
  exact load_cst hwf hm (R := headerR) (by rw [hS]; rfl) (by rw [he.size2]; exact hoff.2)

theorem res_load {env : Env} {S : SState} {mf : Machine} (he : EnvOk m env) (hwf : Env.WF env S)
    (hm : Match env S mf) (hS : Regs4 S) (off n : Nat) (hoff : off % n = 0 ∧ 8 % n = 0 ∧ off + n ≤ 24) :
    mf.load (m.reg 10 + BitVec.ofNat 64 off) n = some ((readConst S 1 off n).eval env) := by
  rw [← he.base1]
  exact load_cst hwf hm (R := resultR) (by rw [hS]; rfl) (by rw [he.size1]; exact hoff.2.2)

theorem HeaderIs.of_loads {mf : Machine} {hdr p n c : Word}
    (h0 : mf.load (hdr + BitVec.ofNat 64 0) 8 = some p) (h8 : mf.load (hdr + BitVec.ofNat 64 8) 8 = some n)
    (h16 : mf.load (hdr + BitVec.ofNat 64 16) 8 = some c) : HeaderIs mf hdr p n c := by
  refine ⟨?_, h8, h16⟩
  rwa [show hdr + BitVec.ofNat 64 0 = hdr by simp] at h0

theorem ResultImage.of_loads {m mf : Machine} {res p n : Word}
    (h0 : mf.load (res + BitVec.ofNat 64 0) 8 = some p) (h8 : mf.load (res + BitVec.ofNat 64 8) 8 = some n)
    (h16 : mf.load (res + BitVec.ofNat 64 16) 2 = some 0) (hk : SameBytes m mf res 18 24) :
    ResultImage m mf res p n := by
  refine ⟨?_, h8, h16, hk⟩
  rwa [show res + BitVec.ofNat 64 0 = res by simp] at h0


theorem eval_bytes2_0 (env : Env) : (Sym.bytes (.lit 0) 0 2).eval env = 0 := by
  show ofBytesLE (byteList (byteOf (BitVec.ofNat 64 0)) 0 2) = 0; decide

theorem eval_bytes2_2 (env : Env) : (Sym.bytes (.lit 2) 0 2).eval env = 2 := by
  show ofBytesLE (byteList (byteOf (BitVec.ofNat 64 2)) 0 2) = 2; decide


/-! ## The three outcomes at a `ret` leaf -/

/-- The bytes `[18, 24)` of the result (padding after the error code) are never written. -/
abbrev PadKept (Sf : SState) : Prop :=
  Sf.mem.all (fun w => !(w.r == 1 && decide (w.off < 24) && decide (18 < w.off + w.n))) = true

/-- A `ret` leaf of the success path: the result holds the new block `p'` and the length, the
header the old pointer with length and capacity 0. -/
theorem success_post (E : Entry eb A L items m) {env : Env} {S Sf : SState} {mk mf : Machine}
    {p' : Word} {e : Nat}
    (he : EnvOk m env) (hS : Regs4 S) (hSf : Regs4 Sf) (hwf : Env.WF env Sf) (hmf : Match env Sf mf)
    (hregs : (calleeSaved.filter (· ≠ 2)).all (fun i => Sf.reg i.val == .var i.val) = true)
    (hsp2 : Sf.reg 2 = .ptr 0 96)
    (hex : mf.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env)
    (h20 : readConst Sf 2 0 8 = .init 2 0 8) (h28 : readConst Sf 2 8 8 = .lit 0)
    (h216 : readConst Sf 2 16 8 = .lit 0) (h10 : (readConst Sf 1 0 8).eval env = p')
    (h18 : readConst Sf 1 8 8 = .init 2 8 8) (h116 : readConst Sf 1 16 2 = .bytes (.lit 0) 0 2)
    (hpad : PadKept Sf)
    (hinv : Inv eb A L m mk) (hfr : SameOutside (InWritable env S) mk mf) (hp : Preserved mk mf)
    (hn0 : 0 < (listLen m).toNat) (hp'0 : 0 < p'.toNat)
    (hp'ram : RamRange p' ((listLen m).toNat * eb))
    (hitems : BytesAt mk p' items)
    (hscr : BytesAt mk scratch (wordBytes (BitVec.ofNat 64 ((listLen m).toNat * eb))))
    (hheap : A.Heap (L.erase (listPtr m, (listCap m).toNat * eb) ++ [(p', (listLen m).toNat * eb)]) mk)
    (hpriv : ∀ a, A.Priv (L.erase (listPtr m, (listCap m).toNat * eb) ++ [(p', (listLen m).toNat * eb)]) a →
        A.Priv L a ∨ InRange (listPtr m) ((listCap m).toNat * eb) a)
    (hblk : ∀ a, InRange p' ((listLen m).toNat * eb) a → A.Priv L a) :
    Post eb A L items (BitVec.ofNat 64 e) m mf := by
  obtain ⟨hret, hinvf⟩ := ret_leaf E he hS hmf hregs hsp2 hex hinv hfr hp
  have own : ∀ a, InWritable env S a → Own m a := fun a h => E.inWritable2 he hS h
  have hc0 : 0 < (listCap m).toNat := by have := E.nc; omega
  have hn' : ¬ (listLen m).toNat = 0 := by omega
  refine ⟨hret, hinvf.1, ?_⟩
  show if (listLen m).toNat = 0 then _ else _
  rw [if_neg hn']
  refine .inl ⟨p', hp'0, hp'ram, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hfr _ fun hw => ?_]
    · exact hitems i hi
    · have hlen := E.itemsLen; have hb := E.lenBound
      have hram := hp'ram; unfold RamRange Layout.ramHi at hram
      have hin : InRange p' ((listLen m).toNat * eb) (p' + BitVec.ofNat 64 i) := by
        simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
      exact E.ownNotPriv (own _ hw) (hblk _ hin)
  · refine HeaderIs.of_loads ?_ ?_ ?_
    · rw [hdr_load he hwf hmf hSf 0 (by decide), h20, he.init_eq _ _ _ (.inl rfl), E.ptr]
    · rw [hdr_load he hwf hmf hSf 8 (by decide), h28]; rfl
    · rw [hdr_load he hwf hmf hSf 16 (by decide), h216]; rfl
  · refine ResultImage.of_loads ?_ ?_ ?_ (E.result_same he hmf (by rw [hSf]; decide) (by decide) hpad)
    · rw [res_load he hwf hmf hSf 0 8 (by decide), h10]
    · rw [res_load he hwf hmf hSf 8 8 (by decide), h18, he.init_eq _ _ _ (.inl rfl), E.len]
    · rw [res_load he hwf hmf hSf 16 2 (by decide), h116, eval_bytes2_0]
  · refine A.heap_frame _ mk mf hheap fun a ha => hfr a fun hw => ?_
    rcases hpriv a ha with h | h
    · exact E.ownNotPriv (own a hw) h
    · exact E.oldNotOwn hc0 h (own a hw)
  · intro i hi
    rw [hfr _ fun hw => E.scratchNotOwn (by simpa [wordBytes] using hi) (own _ hw)]
    exact hscr i hi

/-- A `ret` leaf of OutOfMemory: error code 2, the list and the heap unchanged. -/
theorem oom_post (E : Entry eb A L items m) {env : Env} {S Sf : SState} {mk mf : Machine} {e : Nat}
    (he : EnvOk m env) (hS : Regs4 S) (hSf : Regs4 Sf) (hwf : Env.WF env Sf) (hmf : Match env Sf mf)
    (hregs : (calleeSaved.filter (· ≠ 2)).all (fun i => Sf.reg i.val == .var i.val) = true)
    (hsp2 : Sf.reg 2 = .ptr 0 96)
    (hex : mf.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env)
    (hnw : Sf.mem.all (fun w => w.r != 2) = true)
    (hlow : Sf.mem.all (fun w => !(w.r == 1 && decide (w.off < 16) && decide (0 < w.off + w.n))) = true)
    (h116 : readConst Sf 1 16 2 = .bytes (.lit 2) 0 2) (hpad : PadKept Sf)
    (hinv : Inv eb A L m mk) (hfr : SameOutside (InWritable env S) mk mf) (hp : Preserved mk mf)
    (hn0 : 0 < (listLen m).toNat) (hheap : A.Heap L mk) (hscr : ScratchSame m mk) :
    Post eb A L items (BitVec.ofNat 64 e) m mf := by
  obtain ⟨hret, hinvf⟩ := ret_leaf E he hS hmf hregs hsp2 hex hinv hfr hp
  have own : ∀ a, InWritable env S a → Own m a := fun a h => E.inWritable2 he hS h
  have hn' : ¬ (listLen m).toNat = 0 := by omega
  refine ⟨hret, hinvf.1, ?_⟩
  show if (listLen m).toNat = 0 then _ else _
  rw [if_neg hn']
  refine .inr ⟨E.header_same he hmf (by rw [hSf]; decide) hnw,
    ⟨E.result_same he hmf (by rw [hSf]; decide) (by decide) hlow, ?_,
      E.result_same he hmf (by rw [hSf]; decide) (by decide) hpad⟩,
    A.heap_frame L mk mf hheap fun a ha => hfr a fun hw => E.ownNotPriv (own a hw) ha,
    fun j hj => ?_⟩
  · show mf.load (m.reg 10 + BitVec.ofNat 64 16) 2 = _
    rw [res_load he hwf hmf hSf 16 2 (by decide), h116, eval_bytes2_2]
  · rw [hfr _ fun hw => E.scratchNotOwn hj (own _ hw)]; exact hscr j hj

/-- A `ret` leaf of length 0: the list becomes `arrayListEmpty e`, the result is `{p, 0}`. -/
theorem empty_post (E : Entry eb A L items m) {env : Env} {S Sf : SState} {mk mf : Machine} {e : Nat}
    (he : EnvOk m env) (hS : Regs4 S) (hSf : Regs4 Sf) (hwf : Env.WF env Sf) (hmf : Match env Sf mf)
    (hregs : (calleeSaved.filter (· ≠ 2)).all (fun i => Sf.reg i.val == .var i.val) = true)
    (hsp2 : Sf.reg 2 = .ptr 0 96)
    (hex : mf.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env)
    (h20 : readConst Sf 2 0 8 = .lit e) (h28 : readConst Sf 2 8 8 = .lit 0)
    (h216 : readConst Sf 2 16 8 = .lit 0) (h10 : readConst Sf 1 0 8 = .init 2 0 8)
    (h18 : readConst Sf 1 8 8 = .lit 0) (h116 : readConst Sf 1 16 2 = .bytes (.lit 0) 0 2)
    (hpad : PadKept Sf)
    (hinv : Inv eb A L m mk) (hfr : SameOutside (InWritable env S) mk mf) (hp : Preserved mk mf)
    (hn : (listLen m).toNat = 0)
    (hheap : A.Heap (if 0 < (listCap m).toNat then L.erase (listPtr m, (listCap m).toNat * eb) else L) mk)
    (hpriv : ∀ a, A.Priv (if 0 < (listCap m).toNat then L.erase (listPtr m, (listCap m).toNat * eb) else L) a →
        A.Priv L a ∨ (0 < (listCap m).toNat ∧ InRange (listPtr m) ((listCap m).toNat * eb) a))
    (hscr : ScratchSame m mk) :
    Post eb A L items (BitVec.ofNat 64 e) m mf := by
  obtain ⟨hret, hinvf⟩ := ret_leaf E he hS hmf hregs hsp2 hex hinv hfr hp
  have own : ∀ a, InWritable env S a → Own m a := fun a h => E.inWritable2 he hS h
  refine ⟨hret, hinvf.1, ?_⟩
  show if (listLen m).toNat = 0 then _ else _
  rw [if_pos hn]
  refine ⟨?_, ?_, ?_, fun j hj => ?_⟩
  · refine HeaderIs.of_loads ?_ ?_ ?_
    · rw [hdr_load he hwf hmf hSf 0 (by decide), h20]; rfl
    · rw [hdr_load he hwf hmf hSf 8 (by decide), h28]; rfl
    · rw [hdr_load he hwf hmf hSf 16 (by decide), h216]; rfl
  · refine ResultImage.of_loads ?_ ?_ ?_ (E.result_same he hmf (by rw [hSf]; decide) (by decide) hpad)
    · rw [res_load he hwf hmf hSf 0 8 (by decide), h10, he.init_eq _ _ _ (.inl rfl), E.ptr]
    · rw [res_load he hwf hmf hSf 8 8 (by decide), h18]; rfl
    · rw [res_load he hwf hmf hSf 16 2 (by decide), h116, eval_bytes2_0]
  · refine A.heap_frame _ mk mf hheap fun a ha => hfr a fun hw => ?_
    rcases hpriv a ha with h | ⟨hc0, h⟩
    · exact E.ownNotPriv (own a hw) h
    · exact E.oldNotOwn hc0 h (own a hw)
  · rw [hfr _ fun hw => E.scratchNotOwn hj (own _ hw)]; exact hscr j hj

end

end ZesuExec.Fn.ToOwned
