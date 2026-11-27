import ZesuExec.Fn.F1.Runs
import ZesuExec.Fn.F0.Proof

/-!
# F1 proof: `ensureTotalCapacity` against its contract

Paths (own steps + callee bounds): no growth (29); capacity 0: `alloc`, then OutOfMemory
(112) or `memcpy` and return (123); capacity > 0: `remap` (F0, returns null), `alloc`, then
OutOfMemory (137) or `memcpy`, `free` and return (197).
-/

namespace ZesuExec.Fn.F1
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-- The entry facts of `Pre`, with names. -/
structure Entry (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (items : List Byte)
    (m : Machine) : Prop where
  ro : RodataLoaded zesuImage m
  stack : StackOk m 128
  ra : RetAligned m
  hdrRam : RamRange (m.reg 10) 24
  hdrAl : (m.reg 10).toNat % 8 = 0
  hdr : HeaderIs m (m.reg 10) (wordAt m (m.reg 10)) (wordAt m (m.reg 10 + 8)) (wordAt m (m.reg 10 + 16))
  nc : (wordAt m (m.reg 10 + 8)).toNat ≤ (wordAt m (m.reg 10 + 16)).toNat
  itemsLen : items.length = (wordAt m (m.reg 10 + 8)).toNat * elemBytes
  p0 : 0 < (wordAt m (m.reg 10)).toNat
  buf : 0 < (wordAt m (m.reg 10 + 16)).toNat →
    RamRange (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) ∧
    (wordAt m (m.reg 10), (wordAt m (m.reg 10 + 16)).toNat * elemBytes) ∈ L
  items : BytesAt m (wordAt m (m.reg 10)) items
  aoRam : RamRange (m.reg 11) 16
  aoAl : (m.reg 11).toNat % 8 = 0
  aoCtx : (m.load (m.reg 11) 8).isSome
  aoVt : m.load (m.reg 11 + 8) 8 = some (BitVec.ofNat 64 vtable)
  req : (m.reg 12).toNat < 2 ^ 32
  scratch : Present m (BitVec.ofNat 64 Layout.extraParams) 8
  heap : A.Heap L m
  d1 : Apart (m.reg 10) 24 (m.reg 11) 16
  d2 : Apart (m.reg 10) 24 (m.reg 2 - 128) 128
  d3 : Apart (m.reg 11) 16 (m.reg 2 - 128) 128
  d4 : Apart (m.reg 10) 24 (BitVec.ofNat 64 Layout.extraParams) 8
  d5 : Apart (m.reg 11) 16 (BitVec.ofNat 64 Layout.extraParams) 8
  d6 : Apart (m.reg 2 - 128) 128 (BitVec.ofNat 64 Layout.extraParams) 8
  dbuf : 0 < (wordAt m (m.reg 10 + 16)).toNat →
    Apart (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) (m.reg 10) 24 ∧
    Apart (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) (m.reg 11) 16 ∧
    Apart (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) (m.reg 2 - 128) 128 ∧
    Apart (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes)
      (BitVec.ofNat 64 Layout.extraParams) 8
  priv : ∀ a, InRange (m.reg 10) 24 a ∨ InRange (m.reg 11) 16 a ∨ InRange (m.reg 2 - 128) 128 a ∨
    InRange (BitVec.ofNat 64 Layout.extraParams) 8 a → ¬ A.Priv L a

theorem Entry.of_pre {A : AllocAssumptions zesuImage} {L : List (Word × Nat)} {items : List Byte}
    {m : Machine} (h : Pre A L items m) : Entry A L items m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26⟩

theorem grown_lt (v : Word) (h : v.toNat < 2^32) : (v >>> 1 + v + 2).toNat = grown v.toNat := by
  have h1 : (v >>> 1).toNat = v.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_add, h1, grown]
  simp; omega

theorem g_or (v : Word) (h : v.toNat < 2^32) :
    ((-if (v >>> 1 + v + 2).ult v = true then (1 : Word) else 0) ||| (v >>> 1 + v + 2)) =
      BitVec.ofNat 64 (grown v.toNat) := by
  have hg := grown_lt v h
  have hnot : (v >>> 1 + v + 2).ult v = false := by
    simp only [BitVec.ult, hg, grown]; simp; omega
  rw [hnot]
  have : (-(0 : Word)) = 0 := by decide
  have h0 : ∀ x : Word, 0 ||| x = x := by intro x; ext i; simp
  simp only [Bool.false_eq_true, if_false, this, h0]
  apply BitVec.eq_of_toNat_eq; rw [hg]; simp [grown]; omega

section
variable {A : AllocAssumptions zesuImage} {L : List (Word × Nat)} {items : List Byte}
  {m : Machine}

/-- The entry environment. -/
abbrev env0 (m : Machine) : Env := entryEnv m ((shape m).map (·.1))

theorem Entry.sp (E : Entry A L items m) : (m.reg 2).toNat ≥ Layout.ramLo + 128 ∧
    (m.reg 2).toNat ≤ Layout.ramHi ∧ (m.reg 2).toNat % 16 = 0 :=
  ⟨E.stack.2.1, E.stack.2.2.1, E.stack.1⟩

theorem sub_toNat {x : Word} {k : Nat} (h : k ≤ x.toNat) (hk : k < 2 ^ 64) :
    (x - BitVec.ofNat 64 k).toNat = x.toNat - k := by
  rw [BitVec.toNat_sub]; simp [Nat.mod_eq_of_lt hk]; omega

theorem Entry.wf (E : Entry A L items m) : Env.WF (env0 m) S0 := by
  obtain ⟨hlo, hhi, hal⟩ := E.sp
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  have h112 : (m.reg 2 - 112).toNat = (m.reg 2).toNat - 112 := by
    rw [BitVec.toNat_sub]; simp; omega
  have h128 : (m.reg 2 - 128).toNat = (m.reg 2).toNat - 128 := by
    rw [BitVec.toNat_sub]; simp; omega
  have := E.hdrRam; have := E.aoRam; have d2 := E.d2; have d3 := E.d3; have d1 := E.d1
  simp only [RamRange, Apart, Layout.ramLo, Layout.ramHi, h128] at *
  refine entry_wf (shape m) ?_ ?_
  · simp only [shape, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;>
      simp [RegionOk, frameR, headerR, allocObjR, Machine.writable, Machine.readable,
        Machine.inRange, Layout.ramLo, Layout.ramHi, Layout.rodataLo, Layout.rodataHi,
        Layout.inputLo, Layout.inputHi, h112, E.hdrAl, E.aoAl] <;> omega
  · simp [shape, Fn.Disjoint, h112]; omega

theorem present_of_load {m : Machine} {a v : Word} {n : Nat} (h : m.load a n = some v)
    (hn : n ≤ 8) : ∀ t < n, (m.mem (a + BitVec.ofNat 64 t)).isSome := by
  intro t ht; rw [load_bytes h hn t ht]; rfl

theorem add_add_ofNat (a : Word) (i j : Nat) :
    a + BitVec.ofNat 64 i + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp

theorem Entry.match (E : Entry A L items m) : Match (env0 m) S0 m := by
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
        · simp at hs
  · simp only [List.length_cons, List.length_nil] at hr
    have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr' with rfl | rfl | rfl <;> simp [Env.size, Env.base, entryEnv, shape] at hj ⊢
    · have := E.stack.2.2.2 (16 + j) (by omega)
      rwa [show m.reg 2 - BitVec.ofNat 64 128 + BitVec.ofNat 64 (16 + j) = m.reg 2 - 112 + BitVec.ofNat 64 j by
        bv_omega] at this
    · rcases (show j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) by omega) with h | h | h
      · exact present_of_load hp (by decide) j h
      · have := present_of_load hn (by decide) (j - 8) (by omega)
        rwa [show m.reg 10 + 8 + BitVec.ofNat 64 (j - 8) = m.reg 10 + BitVec.ofNat 64 j by
          bv_omega] at this
      · have := present_of_load hc (by decide) (j - 16) (by omega)
        rwa [show m.reg 10 + 16 + BitVec.ofNat 64 (j - 16) = m.reg 10 + BitVec.ofNat 64 j by
          bv_omega] at this
    · rcases (show j < 8 ∨ (8 ≤ j ∧ j < 16) by omega) with h | h
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp E.aoCtx
        exact present_of_load hv (by decide) j h
      · have := present_of_load E.aoVt (by decide) (j - 8) (by omega)
        rwa [show m.reg 11 + 8 + BitVec.ofNat 64 (j - 8) = m.reg 11 + BitVec.ofNat 64 j by
          bv_omega] at this
  · intro k hk t ht
    simp [known] at hk; subst hk
    have := load_bytes E.aoVt (by decide) t ht
    rw [show m.reg 11 + 8 + BitVec.ofNat 64 t = m.reg 11 + BitVec.ofNat 64 (8 + t) by bv_omega] at this
    simp [Env.byte0, entryEnv, shape, this, Sym.eval]

theorem g_or' (v : Word) (h : v.toNat < 2^32) :
    ((-if BitVec.ult (v >>> 1 + v + BitVec.ofNat 64 2) v = true then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) |||
      (v >>> 1 + v + BitVec.ofNat 64 2)) = BitVec.ofNat 64 (grown v.toNat) := g_or v h

theorem grown_toNat (v : Word) (h : v.toNat < 2 ^ 32) :
    (BitVec.ofNat 64 (grown v.toNat)).toNat = grown v.toNat := by
  simp only [BitVec.toNat_ofNat, grown]; omega

theorem grown_shl5 (v : Word) (h : v.toNat < 2 ^ 32) :
    BitVec.ofNat 64 (grown v.toNat) <<< 5 = BitVec.ofNat 64 (grown v.toNat * elemBytes) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, grown_toNat v h, Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat, grown, elemBytes] <;> omega

theorem grown_srl59 (v : Word) (h : v.toNat < 2 ^ 32) :
    BitVec.ofNat 64 (grown v.toNat) >>> 59 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, grown_toNat v h, Nat.shiftRight_eq_div_pow]
  simp [grown]; omega

theorem grown_bytes_ne (v : Word) (h : v.toNat < 2 ^ 32) :
    BitVec.ofNat 64 (grown v.toNat * elemBytes) ≠ 0 := by
  intro e; have := congrArg BitVec.toNat e; simp [grown, elemBytes] at this; omega

theorem Entry.vars (_E : Entry A L items m) (i : Fin 32) : (env0 m).vars i.val = m.reg i := by
  simp [entryEnv]

theorem Entry.cap (E : Entry A L items m) :
    (Sym.init 1 16 8).eval (env0 m) = wordAt m (m.reg 10 + 16) := by
  have := E.hdrRam; unfold RamRange Layout.ramHi at this
  exact init_eval_load (by simp [shape]) (by simpa [shape] using E.hdr.2.2) (by simp [shape]; omega)

theorem Entry.ptr (E : Entry A L items m) :
    (Sym.init 1 0 8).eval (env0 m) = wordAt m (m.reg 10) := by
  have := E.hdrRam; unfold RamRange Layout.ramHi at this
  exact init_eval_load (by simp [shape]) (by simpa [shape] using E.hdr.1) (by simp [shape]; omega)

/-- The memory a run of F1's own code may change at entry. -/
theorem Entry.inWritable (E : Entry A L items m) {a : Word} (h : InWritable (env0 m) S0 a) :
    InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a := by
  have := E.hdrRam; have := E.aoRam; have := E.sp
  unfold RamRange Layout.ramHi Layout.ramLo at *
  obtain ⟨p, hp, hw, hin⟩ := inWritable_entry h (by
    simp only [shape, List.mem_cons, List.mem_nil_iff, or_false]
    have h112 : (m.reg 2 - 112).toNat = (m.reg 2).toNat - 112 := by
      rw [BitVec.toNat_sub]; simp; omega
    rintro p (rfl | rfl | rfl) <;> simp [h112] <;> omega)
  simp only [shape, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact .inl hin
  · exact .inr hin
  · simp [allocObjR] at hw

/-- An environment that extends the entry environment (`env0` with fresh variables). -/
structure EnvOk (m : Machine) (env : Env) : Prop where
  vars : ∀ i : Fin 32, env.vars i.val = m.reg i
  base0 : env.base 0 = m.reg 2 - 112
  base1 : env.base 1 = m.reg 10
  size1 : env.size 1 = 24
  mem1 : ∀ j, env.mem0 1 j = (m.mem (m.reg 10 + BitVec.ofNat 64 j)).getD 0
  size0 : env.size 0 = 112
  base2 : env.base 2 = m.reg 11
  size2 : env.size 2 = 16
  len : env.regions.length = 3

theorem envOk0 (m : Machine) : EnvOk m (env0 m) where
  vars i := by simp [entryEnv]
  base0 := by simp [entryEnv, Env.base, shape]
  base1 := by simp [entryEnv, Env.base, shape]
  size1 := by simp [entryEnv, Env.size, shape]
  mem1 j := by simp [entryEnv, shape]
  size0 := by simp [entryEnv, Env.size, shape]
  base2 := by simp [entryEnv, Env.base, shape]
  size2 := by simp [entryEnv, Env.size, shape]
  len := by simp [entryEnv, shape]

theorem EnvOk.setVars {m : Machine} {env : Env} (h : EnvOk m env) {F : Nat} (hF : 32 ≤ F)
    (f : Nat → Word) : EnvOk m (env.setVars F f) where
  vars i := by simp [Env.setVars, show ¬ F ≤ i.val by omega, h.vars i]
  base0 := h.base0
  base1 := h.base1
  size1 := h.size1
  mem1 := h.mem1
  size0 := h.size0
  base2 := h.base2
  size2 := h.size2
  len := h.len

/-- A run that never wrote the header leaves it as at entry. -/
theorem Entry.header_same (E : Entry A L items m) {env : Env} {S : SState} {mf : Machine}
    (he : EnvOk m env) (hm : Match env S mf) (hr : 1 < S.regions.length)
    (hnw : S.mem.all (fun w => w.r != 1) = true) :
    HeaderIs mf (m.reg 10) (wordAt m (m.reg 10)) (wordAt m (m.reg 10 + 8))
      (wordAt m (m.reg 10 + 16)) := by
  have hsame := region_same (m := m) hm hr hnw (by
    intro j hj
    rw [he.size1] at hj
    rw [he.mem1, he.base1]
    obtain ⟨hp, hn, hc⟩ := E.hdr
    rcases (show j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) by omega) with h | h | h
    · rw [load_bytes hp (by decide) j h]; rfl
    · have := load_bytes hn (by decide) (j - 8) (by omega)
      rw [show m.reg 10 + 8 + BitVec.ofNat 64 (j - 8) = m.reg 10 + BitVec.ofNat 64 j by bv_omega] at this
      rw [this]; rfl
    · have := load_bytes hc (by decide) (j - 16) (by omega)
      rw [show m.reg 10 + 16 + BitVec.ofNat 64 (j - 16) = m.reg 10 + BitVec.ofNat 64 j by bv_omega] at this
      rw [this]; rfl)
  rw [he.base1, he.size1] at hsame
  obtain ⟨hp, hn, hc⟩ := E.hdr
  have h0 : mf.load (m.reg 10) 8 = m.load (m.reg 10) 8 :=
    load_congr fun t ht => hsame t (by omega)
  have h8 : mf.load (m.reg 10 + 8) 8 = m.load (m.reg 10 + 8) 8 := load_congr fun t ht => by
    rw [show m.reg 10 + 8 + BitVec.ofNat 64 t = m.reg 10 + BitVec.ofNat 64 (8 + t) by bv_omega]
    exact hsame (8 + t) (by omega)
  have h16 : mf.load (m.reg 10 + 16) 8 = m.load (m.reg 10 + 16) 8 := load_congr fun t ht => by
    rw [show m.reg 10 + 16 + BitVec.ofNat 64 t = m.reg 10 + BitVec.ofNat 64 (16 + t) by bv_omega]
    exact hsame (16 + t) (by omega)
  exact ⟨h0 ▸ hp, h8 ▸ hn, h16 ▸ hc⟩

theorem frame_sub_stack {m : Machine} {a : Word} (hlo : 128 ≤ (m.reg 2).toNat)
    (h : InRange (m.reg 2 - 112) 112 a) : InRange (m.reg 2 - 128) 128 a := by
  have h112 : (m.reg 2 - 112).toNat = (m.reg 2).toNat - 112 := by
    rw [BitVec.toNat_sub]; simp; omega
  have h128 : (m.reg 2 - 128).toNat = (m.reg 2).toNat - 128 := by
    rw [BitVec.toNat_sub]; simp; omega
  simp only [InRange, h112, h128] at h ⊢; omega

theorem Entry.ownNotPriv (E : Entry A L items m) {a : Word}
    (h : InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a) : ¬ A.Priv L a := by
  apply E.priv
  rcases h with h | h
  · exact .inr (.inr (.inl (frame_sub_stack (by have := E.sp.1; unfold Layout.ramLo at this; omega) h)))
  · exact .inl h

theorem Entry.scratchNotOwn (E : Entry A L items m) {j : Nat} (hj : j < 8)
    (h : InRange (m.reg 2 - 112) 112 (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j) ∨
      InRange (m.reg 10) 24 (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j)) : False := by
  have hs : (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j).toNat = Layout.extraParams + j := by
    simp [Layout.extraParams]; omega
  have d4 := E.d4; have d6 := E.d6; have hsp := E.sp
  have h128 : (m.reg 2 - 128).toNat = (m.reg 2).toNat - 128 := by
    rw [BitVec.toNat_sub]; simp; unfold Layout.ramLo at hsp; omega
  have h112 : (m.reg 2 - 112).toNat = (m.reg 2).toNat - 112 := by
    rw [BitVec.toNat_sub]; simp; unfold Layout.ramLo at hsp; omega
  simp only [Apart, InRange, hs, h128, h112] at d4 d6 h
  simp [Layout.extraParams] at d4 d6 h hs
  omega

/-- What F1 may change. -/
def Allowed (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m : Machine) (a : Word) : Prop :=
  InRange (m.reg 10) 24 a ∨ InRange (m.reg 2 - 128) 128 a ∨
    InRange (BitVec.ofNat 64 Layout.extraParams) 8 a ∨ A.Priv L a ∨
    (0 < (wordAt m (m.reg 10 + 16)).toNat ∧
      InRange (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) a)

theorem zesu_rodata_low {a b : Nat} (h : zesuImage.rodataByte? a = some b) : a < Layout.ramLo := by
  simp [zesuImage, Image.rodataByte?, Gen.rodata_801136d8, RoSeg.byte?] at h
  have := (List.getElem?_eq_some_iff.mp h.2).1; simp at this; unfold Layout.ramLo; omega

/-- What holds of every machine along F1's run: changes stay in `Allowed`, bytes survive. -/
def Inv (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m mk : Machine) : Prop :=
  SameOutside (Allowed A L m) m mk ∧ Preserved m mk

theorem Inv.refl : Inv A L m m := ⟨fun _ _ => rfl, Preserved.refl m⟩

theorem Inv.ro (E : Entry A L items m) {mk : Machine} (h : Inv A L m mk) :
    RodataLoaded zesuImage mk :=
  RodataLoaded.preserved E.ro h.2 fun _ _ hb => zesu_rodata_low hb

theorem Inv.step {mk mf : Machine} {R : Word → Prop} (h : Inv A L m mk)
    (hfr : SameOutside R mk mf) (hR : ∀ a, R a → Allowed A L m a) (hp : Preserved mk mf) :
    Inv A L m mf :=
  ⟨fun a ha => (hfr a fun hr => ha (hR a hr)).trans (h.1 a ha), h.2.trans hp⟩

theorem sp112 (E : Entry A L items m) : (m.reg 2 - 112).toNat = (m.reg 2).toNat - 112 := by
  have := E.sp.1; unfold Layout.ramLo at this
  rw [BitVec.toNat_sub]; simp; omega

theorem sp128 (E : Entry A L items m) : (m.reg 2 - 128).toNat = (m.reg 2).toNat - 128 := by
  have := E.sp.1; unfold Layout.ramLo at this
  rw [BitVec.toNat_sub]; simp; omega

/-- The writable regions of F1's runs are the frame and the header. -/
theorem Entry.inWritable' (E : Entry A L items m) {env : Env} {S : SState} (he : EnvOk m env)
    (hS : S.regions = [frameR, headerR, allocObjR]) {a : Word} (h : InWritable env S a) :
    Allowed A L m a := by
  obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := h
  rw [hS] at hR
  have hsp := E.sp; have hh := E.hdrRam
  unfold Layout.ramLo Layout.ramHi at hsp; unfold RamRange Layout.ramHi at hh
  have h112 := sp112 E; have h128 := sp128 E
  rcases r with _ | _ | _ | r <;> simp at hR <;> subst hR
  · rw [he.size0] at hj; rw [he.base0]
    refine .inr (.inl ?_)
    simp only [InRange, h128]; rw [toNat_add_ofNat (by omega), h112]; omega
  · rw [he.size1] at hj; rw [he.base1]
    refine .inl ?_
    simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  · simp [allocObjR] at hw

theorem Entry.inWritable2 (E : Entry A L items m) {env : Env} {S : SState} (he : EnvOk m env)
    (hS : S.regions = [frameR, headerR, allocObjR]) {a : Word} (h : InWritable env S a) :
    InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a := by
  obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := h
  rw [hS] at hR
  have hsp := E.sp; have hh := E.hdrRam
  unfold Layout.ramLo Layout.ramHi at hsp; unfold RamRange Layout.ramHi at hh
  have h112 := sp112 E
  rcases r with _ | _ | _ | r <;> simp at hR <;> subst hR
  · rw [he.size0] at hj; rw [he.base0]
    refine .inl ?_
    simp only [InRange, h112]; rw [toNat_add_ofNat (by omega), h112]; omega
  · rw [he.size1] at hj; rw [he.base1]
    refine .inr ?_
    simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  · simp [allocObjR] at hw

theorem Entry.oldNotOwn (E : Entry A L items m) (hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat)
    {a : Word} (hin : InRange (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) a)
    (h : InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a) : False := by
  obtain ⟨dh, -, ds, -⟩ := E.dbuf hc0
  have h112 := sp112 E; have h128 := sp128 E
  simp only [Apart, InRange, h112, h128] at dh ds hin h
  omega

/-- The callee frame below F1's frame avoids every region of F1's runs. -/
theorem Entry.calleeApart (E : Entry A L items m) {env : Env} (he : EnvOk m env) :
    ∀ r j, r < 3 → j < env.size r → ¬ InRange (m.reg 2 - 128) 16 (env.base r + BitVec.ofNat 64 j) := by
  intro r j hr hj
  have hsp := E.sp; have hh := E.hdrRam; have ha := E.aoRam; have d2 := E.d2; have d3 := E.d3
  unfold Layout.ramLo Layout.ramHi at hsp; unfold RamRange Layout.ramHi at hh ha
  have h112 := sp112 E; have h128 := sp128 E
  simp only [Apart, h128] at d2 d3
  rcases r with _ | _ | _ | r
  · rw [he.size0] at hj; rw [he.base0]
    simp only [InRange, h128]; rw [toNat_add_ofNat (by omega), h112]; omega
  · rw [he.size1] at hj; rw [he.base1]
    simp only [InRange, h128]; rw [toNat_add_ofNat (by omega)]; omega
  · rw [he.size2] at hj; rw [he.base2]
    simp only [InRange, h128]; rw [toNat_add_ofNat (by omega)]; omega
  · omega

theorem Entry.len (E : Entry A L items m) :
    (Sym.init 1 8 8).eval (env0 m) = wordAt m (m.reg 10 + 8) := by
  have := E.hdrRam; unfold RamRange Layout.ramHi at this
  exact init_eval_load (by simp [shape]) (by simpa [shape] using E.hdr.2.1) (by simp [shape]; omega)

theorem EnvOk.init_eq {env : Env} (he : EnvOk m env) (off n : Nat) :
    (Sym.init 1 off n).eval env = (Sym.init 1 off n).eval (env0 m) := by
  have : env.byte0 1 = (env0 m).byte0 1 := by
    funext j; simp only [Env.byte0]; rw [he.mem1]; simp [entryEnv, shape]
  simp only [Sym.eval, this]

/-- Loading a word of the header at the end of a run. -/
theorem header_load {env : Env} {S : SState} {mf : Machine} (he : EnvOk m env)
    (hwf : Env.WF env S) (hm : Match env S mf) (hS : S.regions = [frameR, headerR, allocObjR])
    (off : Nat) (hoff : off % 8 = 0 ∧ off + 8 ≤ 24) :
    mf.load (m.reg 10 + BitVec.ofNat 64 off) 8 = some ((readConst S 1 off 8).eval env) := by
  rw [← he.base1]
  exact load_cst hwf hm (R := headerR) (by rw [hS]; rfl) hoff.1 (by decide)
    (by rw [he.size1]; exact hoff.2)

/-- The end of the growing path: the header holds the new pointer, the old length and the grown
capacity; the new block holds the items; the scratch word holds the copied byte count. -/
theorem stage4b (E : Entry A L items m) {env : Env} {m4 : Machine} {p' : Word}
    (he : EnvOk m env) (hm : Match env S4b m4) (hwf : Env.WF env S4b)
    (hpc : m4.pc.toNat = 0x800cb5a8) (hinv : Inv A L m m4)
    (hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat)
    (hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat)
    (hv310 : env.vars 310 = p') (hv122 : env.vars 122 = BitVec.ofNat 64 (grown (m.reg 12).toNat))
    (hp'0 : 0 < p'.toNat) (hp'ram : RamRange p' (grown (m.reg 12).toNat * elemBytes))
    (hitems : BytesAt m4 p' items)
    (hscr : BytesAt m4 (BitVec.ofNat 64 Layout.extraParams)
      (wordBytes (BitVec.ofNat 64 ((wordAt m (m.reg 10 + 8)).toNat * elemBytes))))
    (hheap : A.Heap ((L.erase (wordAt m (m.reg 10), (wordAt m (m.reg 10 + 16)).toNat * elemBytes)) ++
      [(p', grown (m.reg 12).toNat * elemBytes)]) m4)
    (hpriv : ∀ a, A.Priv ((L.erase (wordAt m (m.reg 10), (wordAt m (m.reg 10 + 16)).toNat * elemBytes)) ++
      [(p', grown (m.reg 12).toNat * elemBytes)]) a →
        A.Priv L a ∨ InRange (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) a)
    (hblk : ∀ a, InRange p' (grown (m.reg 12).toNat * elemBytes) a → A.Priv L a) :
    Reaches zesuImage 17 (Post A L items m) m4 := by
  refine run_reaches' run4b hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run4b_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  subst hl
  have hv1 : env.vars 1 = m.reg 1 := he.vars 1
  refine ⟨fun o ho => ?_, by decide, fun mf hmf hex hfr hp => Reaches.done ?_⟩
  · simp at ho; subst ho; simpa [Oblig.holds, Sym.eval, BinOp.eval, hv1] using E.ra
  have hwf' : Env.WF env (run4b_leaves[0]!).S := hwf.congr (by decide)
  have hS : (run4b_leaves[0]!).S.regions = [frameR, headerR, allocObjR] := by decide
  have own : ∀ a, InWritable env S4b a → InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 he (by decide) h
  have hret : Returns m mf := returns_leaf hmf he.vars (by decide)
    (by show env.base 0 + BitVec.ofInt 64 112 = m.reg 2
        rw [he.base0]; simp [BitVec.sub_add_cancel]) hex
  have hlt' : ¬ (m.reg 12).toNat ≤ (wordAt m (m.reg 10 + 16)).toNat := by omega
  refine ⟨hret, (hinv.step hfr (fun a h => E.inWritable' he (by decide) h) hp).1, ?_⟩
  simp only [hlt', if_false]
  refine .inl ⟨by rw [← hmf.regs 10]; rfl, p', ⟨?_, ?_, ?_⟩, hp'0, hp'ram, ?_, ?_, ?_⟩
  · have := header_load he hwf' hmf hS 0 (by decide)
    rw [show m.reg 10 + BitVec.ofNat 64 0 = m.reg 10 by simp] at this
    rw [this]; show some (env.vars 310) = _; rw [hv310]
  · have := header_load he hwf' hmf hS 8 (by decide)
    show mf.load (m.reg 10 + BitVec.ofNat 64 8) 8 = _
    rw [this]; show some ((Sym.init 1 8 8).eval env) = _
    rw [he.init_eq, E.len]
  · have := header_load he hwf' hmf hS 16 (by decide)
    show mf.load (m.reg 10 + BitVec.ofNat 64 16) 8 = _
    rw [this]; show some (env.vars 122) = _; rw [hv122]
  · intro i hi
    rw [hfr _ fun hw => ?_]
    · exact hitems i hi
    · have hlen := E.itemsLen; have hnc := E.nc
      have hram := hp'ram; unfold RamRange Layout.ramHi at hram
      simp only [elemBytes, grown] at hlen hram hi ⊢
      have hin : InRange p' (((m.reg 12).toNat + (m.reg 12).toNat / 2 + 2) * 32) (p' + BitVec.ofNat 64 i) := by
        simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
      exact E.ownNotPriv (own _ hw) (hblk _ (by simpa only [grown, elemBytes] using hin))
  · simp only [hc0, if_true]
    refine A.heap_frame _ m4 mf hheap fun a ha => hfr a fun hw => ?_
    rcases hpriv a ha with h | h
    · exact E.ownNotPriv (own a hw) h
    · exact E.oldNotOwn hc0 h (own a hw)
  · intro i hi
    rw [hfr _ fun hw => E.scratchNotOwn (by simpa [wordBytes] using hi) (own _ hw)]
    exact hscr i hi

/-- The end of the growing path from capacity 0: the header holds the new pointer, the old length and the grown
capacity; the new block holds the items; the scratch word holds the copied byte count. -/
theorem stage3a (E : Entry A L items m) {env : Env} {m4 : Machine} {p' : Word}
    (he : EnvOk m env) (hm : Match env S3a m4) (hwf : Env.WF env S3a)
    (hpc : m4.pc.toNat = 0x800cb588) (hinv : Inv A L m m4)
    (hc0 : (wordAt m (m.reg 10 + 16)).toNat = 0)
    (hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat)
    (hv310 : env.vars 210 = p') (hv122 : env.vars 222 = BitVec.ofNat 64 (grown (m.reg 12).toNat))
    (hp'0 : 0 < p'.toNat) (hp'ram : RamRange p' (grown (m.reg 12).toNat * elemBytes))
    (hitems : BytesAt m4 p' items)
    (hscr : BytesAt m4 (BitVec.ofNat 64 Layout.extraParams)
      (wordBytes (BitVec.ofNat 64 ((wordAt m (m.reg 10 + 8)).toNat * elemBytes))))
    (hheap : A.Heap (L ++ [(p', grown (m.reg 12).toNat * elemBytes)]) m4)
    (hpriv : ∀ a, A.Priv (L ++ [(p', grown (m.reg 12).toNat * elemBytes)]) a → A.Priv L a)
    (hblk : ∀ a, InRange p' (grown (m.reg 12).toNat * elemBytes) a → A.Priv L a) :
    Reaches zesuImage 18 (Post A L items m) m4 := by
  refine run_reaches' run3a hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run3a_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl.symm with rfl | rfl
  · exfalso; sym_simp at hc; rw [he.init_eq, E.cap] at hc; simp [hc0] at hc
    exact hc (BitVec.eq_of_toNat_eq (by simpa using hc0))
  have hv1 : env.vars 1 = m.reg 1 := he.vars 1
  refine ⟨fun o ho => ?_, by decide, fun mf hmf hex hfr hp => Reaches.done ?_⟩
  · simp at ho; subst ho; simpa [Oblig.holds, Sym.eval, BinOp.eval, hv1] using E.ra
  have hwf' : Env.WF env (run3a_leaves[0]!).S := hwf.congr (by decide)
  have hS : (run3a_leaves[0]!).S.regions = [frameR, headerR, allocObjR] := by decide
  have own : ∀ a, InWritable env S3a a → InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 he (by decide) h
  have hret : Returns m mf := returns_leaf hmf he.vars (by decide)
    (by show env.base 0 + BitVec.ofInt 64 112 = m.reg 2
        rw [he.base0]; simp [BitVec.sub_add_cancel]) hex
  have hlt' : ¬ (m.reg 12).toNat ≤ (wordAt m (m.reg 10 + 16)).toNat := by omega
  refine ⟨hret, (hinv.step hfr (fun a h => E.inWritable' he (by decide) h) hp).1, ?_⟩
  simp only [hlt', if_false]
  refine .inl ⟨by rw [← hmf.regs 10]; rfl, p', ⟨?_, ?_, ?_⟩, hp'0, hp'ram, ?_, ?_, ?_⟩
  · have := header_load he hwf' hmf hS 0 (by decide)
    rw [show m.reg 10 + BitVec.ofNat 64 0 = m.reg 10 by simp] at this
    rw [this]; show some (env.vars 210) = _; rw [hv310]
  · have := header_load he hwf' hmf hS 8 (by decide)
    show mf.load (m.reg 10 + BitVec.ofNat 64 8) 8 = _
    rw [this]; show some ((Sym.init 1 8 8).eval env) = _
    rw [he.init_eq, E.len]
  · have := header_load he hwf' hmf hS 16 (by decide)
    show mf.load (m.reg 10 + BitVec.ofNat 64 16) 8 = _
    rw [this]; show some (env.vars 222) = _; rw [hv122]
  · intro i hi
    rw [hfr _ fun hw => ?_]
    · exact hitems i hi
    · have hlen := E.itemsLen; have hnc := E.nc
      have hram := hp'ram; unfold RamRange Layout.ramHi at hram
      simp only [elemBytes, grown] at hlen hram hi ⊢
      have hin : InRange p' (((m.reg 12).toNat + (m.reg 12).toNat / 2 + 2) * 32) (p' + BitVec.ofNat 64 i) := by
        simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
      exact E.ownNotPriv (own _ hw) (hblk _ (by simpa only [grown, elemBytes] using hin))
  · simp only [hc0, Nat.lt_irrefl, if_false]
    exact A.heap_frame _ m4 mf hheap fun a ha => hfr a fun hw => E.ownNotPriv (own a hw) (hpriv a ha)
  · intro i hi
    rw [hfr _ fun hw => E.scratchNotOwn (by simpa [wordBytes] using hi) (own _ hw)]
    exact hscr i hi

theorem Entry.regionAddr (E : Entry A L items m) {env : Env} (he : EnvOk m env) {r j : Nat}
    (hr : r < 3) (hj : j < env.size r) :
    InRange (m.reg 2 - 112) 112 (env.base r + BitVec.ofNat 64 j) ∨
      InRange (m.reg 10) 24 (env.base r + BitVec.ofNat 64 j) ∨
      InRange (m.reg 11) 16 (env.base r + BitVec.ofNat 64 j) := by
  have hsp := E.sp; have hh := E.hdrRam; have ha := E.aoRam
  unfold Layout.ramLo Layout.ramHi at hsp; unfold RamRange Layout.ramHi at hh ha
  have h112 := sp112 E
  rcases r with _ | _ | _ | r
  · rw [he.size0] at hj; rw [he.base0]
    refine .inl ?_; simp only [InRange, h112]; rw [toNat_add_ofNat (by omega), h112]; omega
  · rw [he.size1] at hj; rw [he.base1]
    refine .inr (.inl ?_); simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  · rw [he.size2] at hj; rw [he.base2]
    refine .inr (.inr ?_); simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  · omega

/-- A region address is never the allocator's. -/
theorem Entry.regionNotPriv (E : Entry A L items m) {env : Env} (he : EnvOk m env) {r j : Nat}
    (hr : r < 3) (hj : j < env.size r) : ¬ A.Priv L (env.base r + BitVec.ofNat 64 j) := by
  apply E.priv
  rcases E.regionAddr he hr hj with h | h | h
  · exact .inr (.inr (.inl (frame_sub_stack (by have := E.sp.1; unfold Layout.ramLo at this; omega) h)))
  · exact .inl h
  · exact .inr (.inl h)

/-- A region address is not in the old buffer. -/
theorem Entry.regionNotOld (E : Entry A L items m) {env : Env} (he : EnvOk m env) {r j : Nat}
    (hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat) (hr : r < 3) (hj : j < env.size r) :
    ¬ InRange (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes)
      (env.base r + BitVec.ofNat 64 j) := by
  intro hin
  obtain ⟨dh, da, ds, -⟩ := E.dbuf hc0
  have h112 := sp112 E; have h128 := sp128 E
  rcases E.regionAddr he hr hj with h | h | h <;>
    simp only [Apart, InRange, h112, h128] at dh da ds hin h <;> omega

/-- The stack bytes an allocator callee uses are present. -/
theorem Entry.calleeStack (E : Entry A L items m) {mk : Machine} (hp : Preserved m mk)
    (hsp : mk.reg 2 = m.reg 2 - 112) : StackOk mk 16 := by
  have hs := E.stack; have h112 := sp112 E
  unfold StackOk at hs ⊢
  rw [hsp, h112]
  refine ⟨by omega, by omega, by omega, fun j hj => ?_⟩
  have := hp.1 _ (hs.2.2.2 j (by omega))
  rwa [show m.reg 2 - BitVec.ofNat 64 128 + BitVec.ofNat 64 j =
    m.reg 2 - 112 - BitVec.ofNat 64 16 + BitVec.ofNat 64 j by bv_omega] at this

theorem Entry.calleeFree (E : Entry A L items m) {mk : Machine} {L' : List (Word × Nat)}
    (hL : ∀ a, A.Priv L' a → A.Priv L a) (hsp : mk.reg 2 = m.reg 2 - 112) :
    CalleeFrameFree (A.Priv L') mk := by
  intro a ha hp
  apply E.priv a _ (hL a hp)
  refine .inr (.inr (.inl ?_))
  have h112 := sp112 E; have h128 := sp128 E
  have : (mk.reg 2 - 16).toNat = (m.reg 2).toNat - 128 := by
    rw [hsp, BitVec.toNat_sub, h112]; have := E.sp.1; unfold Layout.ramLo at this; simp; omega
  simp only [InRange, this, h128] at ha ⊢; omega

/-- After `memcpy` on the path with old capacity: `free` the old buffer, then `stage4b`. -/
theorem stage3b (E : Entry A L items m) {env : Env} {m3 : Machine} {p' : Word}
    (he : EnvOk m env) (hm : Match env S3b m3) (hwf : Env.WF env S3b)
    (hpc : m3.pc.toNat = 0x800cb588) (hinv : Inv A L m m3)
    (hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat)
    (hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat)
    (hv310 : env.vars 310 = p') (hv122 : env.vars 122 = BitVec.ofNat 64 (grown (m.reg 12).toNat))
    (hp'0 : 0 < p'.toNat) (hp'ram : RamRange p' (grown (m.reg 12).toNat * elemBytes))
    (hitems : BytesAt m3 p' items)
    (hscr : BytesAt m3 (BitVec.ofNat 64 Layout.extraParams)
      (wordBytes (BitVec.ofNat 64 ((wordAt m (m.reg 10 + 8)).toNat * elemBytes))))
    (hheap : A.Heap (L ++ [(p', grown (m.reg 12).toNat * elemBytes)]) m3)
    (hpriv : ∀ a, A.Priv (L ++ [(p', grown (m.reg 12).toNat * elemBytes)]) a → A.Priv L a)
    (hblk : ∀ a, InRange p' (grown (m.reg 12).toNat * elemBytes) a → A.Priv L a) :
    Reaches zesuImage 67 (Post A L items m) m3 := by
  refine run_reaches' run3b hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run3b_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl
  · exfalso; sym_simp at hc; rw [he.init_eq, E.cap] at hc
    simp only [beq_iff_eq] at hc; rw [hc] at hc0; simp at hc0
  refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
  have own : ∀ a, InWritable env S3b a → InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 he (by decide) h
  -- the call's arguments
  obtain ⟨hbufR, hbufL⟩ := E.buf hc0
  have hcR := hbufR; unfold RamRange Layout.ramHi at hcR
  have r11 : mc.reg 11 = wordAt m (m.reg 10) := by
    rw [← hmc.regs 11]; show (Sym.init 1 0 8).eval env = _; rw [he.init_eq, E.ptr]
  have r12 : (mc.reg 12).toNat = (wordAt m (m.reg 10 + 16)).toNat * elemBytes := by
    rw [← hmc.regs 12]
    show ((Sym.bin .sll (Sym.init 1 16 8) (Sym.lit 5)).eval env).toNat = _
    simp only [Sym.eval_bin, BinOp.eval, Sym.eval_lit]
    rw [he.init_eq, E.cap, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [elemBytes, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at hcR ⊢; omega
  have r13 : mc.reg 13 = 0 := by rw [← hmc.regs 13]; rfl
  have r1 : mc.reg 1 = BitVec.ofNat 64 0x800cb5a8 := by rw [← hmc.regs 1]; rfl
  have r2 : mc.reg 2 = m.reg 2 - 112 := by
    rw [← hmc.regs 2]; show env.base 0 + BitVec.ofInt 64 0 = _; rw [he.base0]; simp
  generalize hL3 : L ++ [(p', grown (m.reg 12).toNat * elemBytes)] = L3 at hheap hpriv
  have hheapc : A.Heap L3 mc := A.heap_frame L3 m3 mc hheap fun a ha => hfr a fun hw =>
    E.ownNotPriv (own a hw) (hpriv a ha)
  have hpre : A.Heap L3 mc ∧ (mc.reg 11, (mc.reg 12).toNat) ∈ L3 ∧ 0 < (mc.reg 12).toNat ∧
      (mc.reg 12).toNat < 2 ^ 63 ∧ (mc.reg 13).toNat ≤ 3 ∧ StackOk mc 16 ∧ RetAligned mc ∧
      CalleeFrameFree (A.Priv L3) mc := by
    refine ⟨hheapc, ?_, ?_, ?_, by rw [r13]; decide, E.calleeStack ((hinv.2.trans hp)) r2,
      by unfold RetAligned; rw [r1]; decide, E.calleeFree hpriv r2⟩
    · rw [r11, r12, ← hL3]; exact List.mem_append_left _ hbufL
    · rw [r12]; simp only [elemBytes]; omega
    · rw [r12]; simp only [elemBytes] at hcR ⊢; omega
  have hcall := Reaches.preserve (A.free_spec L3 mc (by simpa [freeEntry] using hex) hpre)
  refine Reaches.mono (b := 42 + 17) (Reaches.trans hcall fun m4 hpost => ?_) (by decide) fun _ h => h
  obtain ⟨⟨hret, hfrF, hheap4, hpriv4⟩, hp4⟩ := hpost
  rw [r11, r12] at hfrF hheap4 hpriv4
  have hcf : mc.reg 2 - 16 = m.reg 2 - 128 := by rw [r2]; bv_omega
  rw [hcf] at hfrF
  -- the old and new blocks are apart
  have hlive := (A.live_ok L3 m3 hheap).1
  have hapart : ∀ a, InRange p' (grown (m.reg 12).toNat * elemBytes) a →
      ¬ InRange (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) a := by
    intro a h1 h2
    rw [← hL3] at hlive
    have := (List.pairwise_append.mp hlive).2.2 _ hbufL _ (List.mem_singleton_self _)
    simp only [InRange] at h1 h2 this; omega
  have hframe : ∀ r j, r < (run3b_leaves[1]!).S.regions.length → j < env.size r →
      m4.mem (env.base r + BitVec.ofNat 64 j) = mc.mem (env.base r + BitVec.ofNat 64 j) := by
    intro r j hr hj
    have hr3 : r < 3 := by simpa using hr
    refine hfrF _ fun h => ?_
    rcases h with h | h | h
    · exact E.regionNotPriv he hr3 hj (hpriv _ h)
    · exact E.regionNotOld he hc0 hr3 hj h
    · exact E.calleeApart he r j hr3 hj h
  obtain ⟨hm4, hwf4⟩ := after_call_ov (F := 400) (a0 := none) hmc (hwf.congr (by decide)) (by decide)
    hret (fun s h => by simp at h) hframe
  have hinv4 : Inv A L m m4 := by
    refine (hinv.step hfr (fun a h => E.inWritable' he (by decide) h) hp).step hfrF ?_ hp4
    intro a h
    rcases h with h | h | h
    · exact .inr (.inr (.inr (.inl (hpriv a h))))
    · exact .inr (.inr (.inr (.inr ⟨hc0, h⟩)))
    · refine .inr (.inl ?_)
      have h128 := sp128 E
      simp only [InRange, h128] at h ⊢; omega
  have hpc4 : m4.pc.toNat = 0x800cb5a8 := by rw [hret.1, r1]; decide
  have hL : L3.erase (wordAt m (m.reg 10), (wordAt m (m.reg 10 + 16)).toNat * elemBytes) =
      L.erase (wordAt m (m.reg 10), (wordAt m (m.reg 10 + 16)).toNat * elemBytes) ++
        [(p', grown (m.reg 12).toNat * elemBytes)] := by
    rw [← hL3]; exact List.erase_append_left _ hbufL
  rw [hL] at hheap4 hpriv4
  refine stage4b E (he.setVars (by decide) _) hm4 hwf4 hpc4 hinv4 hc0 hlt
    (by simp [Env.setVars, hv310]) (by simp [Env.setVars, hv122]) hp'0 hp'ram ?_ ?_ hheap4 ?_ hblk
  · intro i hi
    have hin : InRange p' (grown (m.reg 12).toNat * elemBytes) (p' + BitVec.ofNat 64 i) := by
      have hlen := E.itemsLen; have hnc := E.nc; have hram := hp'ram
      unfold RamRange Layout.ramHi at hram
      simp only [elemBytes, grown] at hlen hram hi ⊢
      simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
    have hpl : ¬ A.Priv L3 (p' + BitVec.ofNat 64 i) := fun hp =>
      A.priv_not_live L3 _ hp ⟨_, by rw [← hL3]; exact List.mem_append_right _ (List.mem_singleton_self _), hin⟩
    rw [hfrF _ fun h => ?_, hfr _ fun hw => E.ownNotPriv (own _ hw) (hblk _ hin)]
    · exact hitems i hi
    · rcases h with h | h | h
      · exact hpl h
      · exact hapart _ hin h
      · exact E.priv _ (.inr (.inr (.inl ⟨h.1, by have := h.2; omega⟩))) (hblk _ hin)
  · intro i hi
    have hi8 : i < 8 := by simpa [wordBytes] using hi
    have hs : (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 i).toNat = Layout.extraParams + i := by
      simp [Layout.extraParams]; omega
    rw [hfrF _ fun h => ?_, hfr _ fun hw => E.scratchNotOwn hi8 (own _ hw)]
    · exact hscr i hi
    · rcases h with h | h | h
      · exact E.priv _ (.inr (.inr (.inr ⟨by rw [hs]; simp [Layout.extraParams],
          by rw [hs]; simp [Layout.extraParams]; omega⟩))) (hpriv _ h)
      · obtain ⟨-, -, -, d⟩ := E.dbuf hc0
        simp only [Apart, InRange, hs] at d h; simp [Layout.extraParams] at d h; omega
      · have d := E.d6; have h128 := sp128 E
        simp only [Apart, InRange, hs, h128] at d h; simp [Layout.extraParams] at d h; omega
  · intro a h
    rcases hpriv4 a h with h | h
    · exact .inl (hpriv a h)
    · exact .inr h

set_option hygiene false in
/-- A path that needs the grown capacity to overflow `2^59` is infeasible. -/
macro "f1_overflow" : tactic => `(tactic| (
  sym_simp at hc; simp only [E.cap] at hc; simp only [entryEnv, Fin.ofNat] at hc
  simp at hc; simp only [g_or' _ hreq, grown_srl59 _ hreq] at hc; simp at hc))

theorem stage0_test (E : Entry A L items m) (hpc : m.pc.toNat = entry) :
    Reaches zesuImage 197 (Post A L items m) m := by
  refine run_reaches run0 E.wf E.match hpc E.ro ?_
  intro l hl hc
  simp only [run0_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  have hreq := E.req
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- no growth: return 0
    sym_simp at hc
    simp only [E.cap] at hc
    refine ⟨fun o ho => ?_, by decide, fun mf hm hex hfr => Reaches.done ?_⟩
    · simp at ho; subst ho; simpa [Oblig.holds, Sym.eval, BinOp.eval, entryEnv] using E.ra
    have hret : Returns m mf := returns_leaf hm (envOk0 m).vars (by decide)
      (by simp [SState.reg, Sym.eval, entryEnv, Env.base, shape, BitVec.sub_add_cancel]) hex
    have hfr' : SameOutside (Allowed A L m) m mf := SameOutside.mono hfr fun a ha => by
      rcases E.inWritable ha with h | h
      · exact .inr (.inl (frame_sub_stack (by have := E.sp.1; unfold Layout.ramLo at this; omega) h))
      · exact .inl h
    have hle : (m.reg 12).toNat ≤ (wordAt m (m.reg 10 + 16)).toNat := by
      simp [BitVec.ult, entryEnv] at hc ⊢; omega
    refine ⟨hret, hfr', ?_⟩
    simp only [hle, if_true]
    refine ⟨by rw [← hm.regs 10]; rfl, E.header_same (envOk0 m) hm (by decide) (by decide),
      A.heap_frame L m mf E.heap fun a hp => hfr a fun hw => ?_, fun j hj => hfr _ fun hw => ?_⟩
    · exact E.ownNotPriv (E.inWritable hw) hp
    · exact E.scratchNotOwn hj (E.inWritable hw)
  · exfalso
    sym_simp at hc
    simp only [E.cap] at hc
    simp only [entryEnv, Fin.ofNat] at hc
    simp at hc
    simp only [g_or' _ hreq, grown_shl5 _ hreq] at hc
    exact grown_bytes_ne _ hreq hc.2.2.2
  · sorry
  · exfalso; f1_overflow
  · sorry
  -- leaves 5-7: the growth overflowed, impossible below 2^32
  all_goals (exfalso; f1_overflow)

end

end ZesuExec.Fn.F1
