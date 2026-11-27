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
  have := zesu_rodata_range h; unfold Layout.rodataHi at this; unfold Layout.ramLo; omega

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

/-- The allocator's answer, as `alloc_spec` states it for F1's request. -/
def AllocOut (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (g : Nat) (m2 : Machine) : Prop :=
  (m2.reg 10 = 0 ∧ A.Heap L m2) ∨
  (m2.reg 10 ≠ 0 ∧ A.Heap (L ++ [(m2.reg 10, g)]) m2 ∧ RamRange (m2.reg 10) g ∧ Present m2 (m2.reg 10) g ∧
    (∀ a, InRange (m2.reg 10) g a → A.Priv L a) ∧ (∀ a, A.Priv (L ++ [(m2.reg 10, g)]) a → A.Priv L a))

/-- OutOfMemory: return 2 with the list unchanged. -/
theorem oom_post (E : Entry A L items m) {env : Env} {S Sf : SState} {mk mf : Machine}
    (he : EnvOk m env) (hS : S.regions = [frameR, headerR, allocObjR])
    (hmf : Match env Sf mf) (hr : 1 < Sf.regions.length) (hnw : Sf.mem.all (fun w => w.r != 1) = true)
    (hregs : (calleeSaved.filter (· ≠ 2)).all (fun i => Sf.reg i.val == .var i.val) = true)
    (hsp2 : Sf.reg 2 = .ptr 0 112) (ha0 : Sf.reg 10 = .lit 2)
    (hex : mf.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env)
    (hinv : Inv A L m mk) (hfr : SameOutside (InWritable env S) mk mf) (hp : Preserved mk mf)
    (hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat)
    (hheap : A.Heap L mk) (hscr : ScratchSame m mk) : Post A L items m mf := by
  have own : ∀ a, InWritable env S a → InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 he hS h
  have hret : Returns m mf := returns_leaf hmf he.vars hregs
    (by rw [hsp2]; show env.base 0 + BitVec.ofInt 64 112 = m.reg 2
        rw [he.base0]; simp [BitVec.sub_add_cancel]) hex
  have hlt' : ¬ (m.reg 12).toNat ≤ (wordAt m (m.reg 10 + 16)).toNat := by omega
  refine ⟨hret, (hinv.step hfr (fun a h => E.inWritable' he hS h) hp).1, ?_⟩
  simp only [hlt', if_false]
  refine .inr ⟨by rw [← hmf.regs 10]; show Sym.eval env (Sf.reg 10) = 2; rw [ha0]; rfl,
    E.header_same he hmf hr hnw,
    A.heap_frame L mk mf hheap fun a ha => hfr a fun hw => E.ownNotPriv (own a hw) ha,
    fun j hj => ?_⟩
  rw [hfr _ fun hw => E.scratchNotOwn hj (own _ hw)]; exact hscr j hj

theorem Entry.regionNotScratch (E : Entry A L items m) {env : Env} (he : EnvOk m env) {r j : Nat}
    (hr : r < 3) (hj : j < env.size r) :
    ¬ InRange (BitVec.ofNat 64 Layout.extraParams) 8 (env.base r + BitVec.ofNat 64 j) := by
  intro hin
  have d4 := E.d4; have d5 := E.d5; have d6 := E.d6
  have h112 := sp112 E; have h128 := sp128 E
  rcases E.regionAddr he hr hj with h | h | h <;>
    simp only [Apart, InRange, h112, h128, Layout.extraParams, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow] at d4 d5 d6 hin h <;> omega

/-- The `memcpy` call of both growing paths and the return from it: `k` continues at
`0x800cb588` with the items in the new block and the byte count in the scratch word. -/
theorem copy_step (E : Entry A L items m) {env : Env} {S Sl : SState} {m2 mc : Machine} {b : Nat}
    {iP : Nat}
    (he : EnvOk m env) (hm : Match env S m2) (hwf : Env.WF env S) (hmc : Match env Sl mc)
    (hex : mc.pc.toNat = Layout.memcpyEntry) (hfr : SameOutside (InWritable env S) m2 mc)
    (hp : Preserved m2 mc) (hinv : Inv A L m m2)
    (hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat ∨ (wordAt m (m.reg 10 + 8)).toNat = 0)
    (hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat)
    (hvP : env.vars iP = m2.reg 10)
    (hitemsP : BytesAt m2 (wordAt m (m.reg 10)) items)
    (hne : m2.reg 10 ≠ 0)
    (hheap : A.Heap (L ++ [(m2.reg 10, grown (m.reg 12).toNat * elemBytes)]) m2)
    (hram' : RamRange (m2.reg 10) (grown (m.reg 12).toNat * elemBytes))
    (hpres' : Present m2 (m2.reg 10) (grown (m.reg 12).toNat * elemBytes))
    (hblk : ∀ a, InRange (m2.reg 10) (grown (m.reg 12).toNat * elemBytes) a → A.Priv L a)
    (hpriv : ∀ a, A.Priv (L ++ [(m2.reg 10, grown (m.reg 12).toNat * elemBytes)]) a → A.Priv L a)
    (hS : S.regions = [frameR, headerR, allocObjR]) (hSl : Sl.regions = [frameR, headerR, allocObjR])
    (r10 : Sl.reg 10 = .var iP) (r11 : Sl.reg 11 = .init 1 0 8)
    (r12 : Sl.reg 12 = .bin .sll (.init 1 8 8) (.lit 5)) (r1 : Sl.reg 1 = .lit 0x800cb588)
    (k : ∀ m3, Match env Sl m3 → Env.WF env Sl → m3.pc.toNat = 0x800cb588 → Inv A L m m3 →
      BytesAt m3 (m2.reg 10) items →
      BytesAt m3 (BitVec.ofNat 64 Layout.extraParams)
        (wordBytes (BitVec.ofNat 64 ((wordAt m (m.reg 10 + 8)).toNat * elemBytes))) →
      A.Heap (L ++ [(m2.reg 10, grown (m.reg 12).toNat * elemBytes)]) m3 →
      Reaches zesuImage b (Post A L items m) m3) :
    Reaches zesuImage (3 + b) (Post A L items m) mc := by
  have own : ∀ a, InWritable env S a → InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 he hS h
  have hnc := E.nc; have hlen := E.itemsLen
  have hram := hram'; unfold RamRange Layout.ramHi at hram
  -- the call's arguments
  have g10 : mc.reg 10 = m2.reg 10 := by
    rw [← hmc.regs 10]; show Sym.eval env (Sl.reg 10) = _; rw [r10]; exact hvP
  have g11 : mc.reg 11 = wordAt m (m.reg 10) := by
    rw [← hmc.regs 11]; show Sym.eval env (Sl.reg 11) = _; rw [r11, he.init_eq, E.ptr]
  have hn32 : (wordAt m (m.reg 10 + 8)).toNat * elemBytes < 2 ^ 64 := by
    simp only [elemBytes, grown] at hram ⊢; omega
  have g12 : mc.reg 12 = BitVec.ofNat 64 ((wordAt m (m.reg 10 + 8)).toNat * elemBytes) := by
    rw [← hmc.regs 12]; show Sym.eval env (Sl.reg 12) = _; rw [r12]
    show BinOp.eval .sll ((Sym.init 1 8 8).eval env) (BitVec.ofNat 64 5) = _
    rw [he.init_eq, E.len]
    apply BitVec.eq_of_toNat_eq
    simp only [BinOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, elemBytes] at hn32 ⊢
    all_goals omega
  have g1 : mc.reg 1 = BitVec.ofNat 64 0x800cb588 := by
    rw [← hmc.regs 1]; show Sym.eval env (Sl.reg 1) = _; rw [r1]; rfl
  have hp2 := hinv.2.trans hp
  -- facts about the old buffer when there is something to copy
  have hcpos : ∀ i, i < items.length → 0 < (wordAt m (m.reg 10 + 16)).toNat := by
    intro i hi; rw [hlen] at hi; simp only [elemBytes] at hi; omega
  have hinP : ∀ i, i < items.length → InRange (wordAt m (m.reg 10))
      ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) (wordAt m (m.reg 10) + BitVec.ofNat 64 i) := by
    intro i hi
    have := (E.buf (hcpos i hi)).1; unfold RamRange Layout.ramHi at this
    have h' : items.length ≤ (wordAt m (m.reg 10 + 16)).toNat * elemBytes := by
      rw [hlen]; exact Nat.mul_le_mul_right _ hnc
    simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  have hitemsC : BytesAt mc (wordAt m (m.reg 10)) items := fun i hi => by
    rw [hfr _ fun hw => E.oldNotOwn (hcpos i hi) (hinP i hi) (own _ hw)]; exact hitemsP i hi
  have hblkPriv : ∀ i, i < (wordAt m (m.reg 10 + 8)).toNat * elemBytes →
      A.Priv L (m2.reg 10 + BitVec.ofNat 64 i) := by
    intro i hi
    apply hblk
    simp only [elemBytes, grown] at hi hram ⊢
    simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
  have hpP : m2.reg 10 ≠ wordAt m (m.reg 10) ∨ (wordAt m (m.reg 10 + 8)).toNat = 0 := by
    by_cases hn0 : (wordAt m (m.reg 10 + 8)).toNat = 0
    · exact .inr hn0
    · refine .inl fun e => ?_
      have h0 : 0 < items.length := by rw [hlen]; simp only [elemBytes]; omega
      have hpr := hblkPriv 0 (by simp only [elemBytes]; omega)
      rw [e] at hpr
      exact A.priv_not_live L _ hpr ⟨_, (E.buf (hcpos 0 h0)).2, by simpa using hinP 0 h0⟩
  have hscrC : Present mc (BitVec.ofNat 64 Layout.extraParams) 8 := fun j hj => hp2.1 _ (E.scratch j hj)
  have hdom : ziskMemcpyDomain mc = true := by
    unfold ziskMemcpyDomain
    rw [g1, g10, g11, g12]
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨⟨⟨by decide, by decide⟩, ?_⟩, ?_⟩
    · unfold Machine.present
      exact readBytes_isSome_of fun t ht => by
        have := hscrC t ht
        rwa [show BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 t =
          BitVec.ofNat 64 (Layout.extraParams + t) by bv_omega] at this
    · by_cases hn0 : (wordAt m (m.reg 10 + 8)).toNat = 0
      · left; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32, hn0, Nat.zero_mul]
      · right
        have hc : 0 < (wordAt m (m.reg 10 + 16)).toNat := by omega
        have hb := (E.buf hc).1; unfold RamRange Layout.ramHi Layout.ramLo at hb
        have hle : (wordAt m (m.reg 10 + 8)).toNat * elemBytes ≤ (wordAt m (m.reg 10 + 16)).toNat * elemBytes :=
          Nat.mul_le_mul_right _ hnc
        have hle2 : (wordAt m (m.reg 10 + 8)).toNat * elemBytes ≤ grown (m.reg 12).toNat * elemBytes := by
          apply Nat.mul_le_mul_right; simp only [grown]; omega
        have hram2 := hram'; unfold RamRange Layout.ramHi Layout.ramLo at hram2
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32]
        simp only [elemBytes] at hle hle2 hb hram2 hpres' ⊢
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · simp only [Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi, Layout.rodataLo,
            Layout.rodataHi, Layout.inputLo, Layout.inputHi, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq]; omega
        · unfold Machine.present
          exact readBytes_isSome_of fun t ht => by
            rw [ofNat_toNat_add, hitemsC t (by rw [hlen]; simpa only [elemBytes] using ht)]; rfl
        · simp only [Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi, Bool.and_eq_true,
            decide_eq_true_eq]; omega
        · unfold Machine.present
          exact readBytes_isSome_of fun t ht => by
            rw [ofNat_toNat_add]; exact hp.1 _ (hpres' t (by omega))
  have hcall := Reaches.preserve (memcpy_spec zesuImage mc (by simpa using hex) hdom)
  refine Reaches.trans hcall fun m3 hpost => ?_
  obtain ⟨hz, hp3⟩ := hpost
  have hz : ziskMemcpy mc = some m3 := hz
  have hdst : ∀ x, InRange (mc.reg 10) (mc.reg 12).toNat x → A.Priv L x := by
    intro x hx
    rw [g10, g12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32] at hx
    apply hblk
    simp only [elemBytes, grown] at hx hram ⊢
    simp only [InRange] at hx ⊢; omega
  have hscrP : ∀ x, InRange (BitVec.ofNat 64 Layout.extraParams) 8 x → ¬ A.Priv L x :=
    fun x hx => E.priv x (.inr (.inr (.inr hx)))
  have hout : ∀ x, ¬ (InRange (mc.reg 10) (mc.reg 12).toNat x ∨
      InRange (BitVec.ofNat 64 Layout.extraParams) 8 x) → m3.mem x = mc.mem x :=
    fun x hx => memcpy_out hz (fun h => hx (.inl h)) (fun h => hx (.inr h))
  have hm3 : Match env Sl m3 := Match.congr_machine hmc (memcpy_reg hz) fun r j hr hj => by
    have hr3 : r < 3 := by rw [hSl] at hr; simpa using hr
    exact hout _ fun h => h.elim (fun h => E.regionNotPriv he hr3 hj (hdst _ h))
      (fun h => E.regionNotScratch he hr3 hj h)
  have hpc3 : m3.pc.toNat = 0x800cb588 := by rw [memcpy_eq hz]; simp only [g1]; decide
  have hinv3 : Inv A L m m3 := by
    refine (hinv.step hfr (fun a h => E.inWritable' he hS h) hp).step (R := fun x =>
      InRange (mc.reg 10) (mc.reg 12).toNat x ∨ InRange (BitVec.ofNat 64 Layout.extraParams) 8 x)
      (fun x hx => hout x hx) (fun x h => ?_) (memcpy_preserved hz)
    rcases h with h | h
    · exact .inr (.inr (.inr (.inl (hdst x h))))
    · exact .inr (.inr (.inl h))
  refine k m3 hm3 (hwf.congr (hSl.trans hS.symm)) hpc3 hinv3 ?_ ?_ ?_
  · -- the items, copied
    intro i hi
    have hi' : i < (mc.reg 12).toNat := by
      rw [g12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32, ← hlen]; exact hi
    have hne' : mc.reg 10 ≠ mc.reg 11 := by
      rw [g10, g11]
      rcases hpP with h | h
      · exact h
      · rw [hlen, h] at hi; simp at hi
    have hb := (E.buf (hcpos i hi)).1; unfold RamRange Layout.ramHi at hb
    have hle : (wordAt m (m.reg 10 + 8)).toNat * elemBytes ≤ (wordAt m (m.reg 10 + 16)).toNat * elemBytes :=
      Nat.mul_le_mul_right _ hnc
    have hg : (wordAt m (m.reg 10 + 8)).toNat * elemBytes ≤ grown (m.reg 12).toNat * elemBytes := by
      apply Nat.mul_le_mul_right; simp only [grown]; omega
    have := memcpy_dst hz hi' hne'
      (by rw [g10, g12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32]; omega)
      (by rw [g11, g12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32]; omega)
      (by rw [g11]; intro h; obtain ⟨-, -, -, d⟩ := E.dbuf (hcpos i hi)
          have hin := hinP i hi
          simp only [Apart, InRange, Layout.extraParams, BitVec.toNat_ofNat, Nat.reduceMod,
            Nat.reducePow] at d h hin; omega)
    rw [g10, g11] at this
    rw [this]; exact hitemsC i hi
  · -- the byte count
    intro i hi
    have hi8 : i < 8 := by simpa [wordBytes] using hi
    have hs : (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 i).toNat = Layout.extraParams + i := by
      simp [Layout.extraParams]; omega
    have hin : InRange (BitVec.ofNat 64 Layout.extraParams) 8
        (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 i) := by
      simp only [InRange]; rw [hs]; simp [Layout.extraParams]; omega
    rw [memcpy_scratch hz hi8 fun h => hscrP _ hin (hdst _ h), g12]
    simp [wordBytes, hi8]
  · -- the heap
    refine A.heap_frame _ m2 m3 hheap fun a ha => ?_
    rw [hout a fun h => ?_, hfr a fun hw => E.ownNotPriv (own a hw) (hpriv a ha)]
    rcases h with h | h
    · exact A.priv_not_live _ a ha ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by
        rw [g10, g12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32] at h
        have hg : (wordAt m (m.reg 10 + 8)).toNat * elemBytes ≤ grown (m.reg 12).toNat * elemBytes := by
          apply Nat.mul_le_mul_right; simp only [grown]; omega
        simp only [InRange] at h ⊢; omega⟩
    · exact hscrP a h (hpriv a ha)

/-- After `alloc` on the path with old capacity: OutOfMemory, or `memcpy` then `stage3b`. -/
theorem stage2b (E : Entry A L items m) {env : Env} {m2 : Machine}
    (he : EnvOk m env) (hm : Match env S2b m2) (hwf : Env.WF env S2b)
    (hpc : m2.pc.toNat = 0x800cb55c) (hinv : Inv A L m m2)
    (hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat)
    (hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat)
    (hv310 : env.vars 310 = m2.reg 10) (hv122 : env.vars 122 = BitVec.ofNat 64 (grown (m.reg 12).toNat))
    (hitemsP : BytesAt m2 (wordAt m (m.reg 10)) items) (hscr : ScratchSame m m2)
    (hout : AllocOut A L (grown (m.reg 12).toNat * elemBytes) m2) :
    Reaches zesuImage 78 (Post A L items m) m2 := by
  refine run_reaches' run2b hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run2b_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl.symm with rfl | rfl
  · -- null: OutOfMemory
    sym_simp at hc; simp only [beq_iff_eq, hv310] at hc
    have hheap : A.Heap L m2 := by
      rcases hout with ⟨-, h⟩ | ⟨hne, -⟩
      · exact h
      · exact absurd hc hne
    refine ⟨fun o ho => ?_, by decide, fun mf hmf hex hfr hp => Reaches.done ?_⟩
    · simp at ho; subst ho; simpa [Oblig.holds, Sym.eval, BinOp.eval, show env.vars 1 = m.reg 1 from he.vars 1] using E.ra
    exact oom_post E he (by decide) hmf (by decide) (by decide) (by decide) rfl rfl hex hinv hfr hp hlt hheap hscr
  · -- a block: copy the items with `memcpy`, then free the old buffer
    sym_simp at hc; simp only [bne_iff_ne, ne_eq, hv310] at hc
    obtain ⟨hne, hheap, hram', hpres', hblk, hpriv⟩ := hout.resolve_left fun h => hc h.1
    refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
    exact copy_step E he hm hwf hmc hex hfr hp hinv (.inl hc0) hlt hv310 hitemsP hne hheap hram'
      hpres' hblk hpriv (by decide) (by decide) rfl rfl rfl rfl
      (fun m3 hm3 hwf3 hpc3 hinv3 hitems3 hscr3 hheap3 =>
        stage3b E he hm3 hwf3 hpc3 hinv3 hc0 hlt hv310 hv122 (by
          have : (m2.reg 10).toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq (by simpa using e))
          omega) hram' hitems3 hscr3 hheap3 hpriv hblk)

/-- After `alloc` on the path from capacity 0: OutOfMemory, or `memcpy` then `stage3a`. -/
theorem stage2a (E : Entry A L items m) {env : Env} {m2 : Machine}
    (he : EnvOk m env) (hm : Match env S2a m2) (hwf : Env.WF env S2a)
    (hpc : m2.pc.toNat = 0x800cb55c) (hinv : Inv A L m m2)
    (hc0 : (wordAt m (m.reg 10 + 16)).toNat = 0)
    (hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat)
    (hv310 : env.vars 210 = m2.reg 10) (hv122 : env.vars 222 = BitVec.ofNat 64 (grown (m.reg 12).toNat))
    (hitemsP : BytesAt m2 (wordAt m (m.reg 10)) items) (hscr : ScratchSame m m2)
    (hout : AllocOut A L (grown (m.reg 12).toNat * elemBytes) m2) :
    Reaches zesuImage 103 (Post A L items m) m2 := by
  refine run_reaches' run2a hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run2a_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl.symm with rfl | rfl
  · -- null: OutOfMemory
    sym_simp at hc; simp only [beq_iff_eq, hv310] at hc
    have hheap : A.Heap L m2 := by
      rcases hout with ⟨-, h⟩ | ⟨hne, -⟩
      · exact h
      · exact absurd hc hne
    refine ⟨fun o ho => ?_, by decide, fun mf hmf hex hfr hp => Reaches.done ?_⟩
    · simp at ho; subst ho; simpa [Oblig.holds, Sym.eval, BinOp.eval, show env.vars 1 = m.reg 1 from he.vars 1] using E.ra
    exact oom_post E he (by decide) hmf (by decide) (by decide) (by decide) rfl rfl hex hinv hfr hp hlt hheap hscr
  · -- a block: copy the items with `memcpy`, then free the old buffer
    sym_simp at hc; simp only [bne_iff_ne, ne_eq, hv310] at hc
    obtain ⟨hne, hheap, hram', hpres', hblk, hpriv⟩ := hout.resolve_left fun h => hc h.1
    refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
    refine Reaches.mono (b := 3 + 18) ?_ (by decide) fun _ h => h
    exact copy_step E he hm hwf hmc hex hfr hp hinv (.inr (by have := E.nc; omega)) hlt hv310 hitemsP hne hheap hram'
      hpres' hblk hpriv (by decide) (by decide) rfl rfl rfl rfl
      (fun m3 hm3 hwf3 hpc3 hinv3 hitems3 hscr3 hheap3 =>
        stage3a E he hm3 hwf3 hpc3 hinv3 hc0 hlt hv310 hv122 (by
          have : (m2.reg 10).toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq (by simpa using e))
          omega) hram' hitems3 hscr3 hheap3 hpriv hblk)

theorem Entry.itemsOld (E : Entry A L items m) {i : Nat} (hi : i < items.length) :
    0 < (wordAt m (m.reg 10 + 16)).toNat ∧ InRange (wordAt m (m.reg 10))
      ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) (wordAt m (m.reg 10) + BitVec.ofNat 64 i) := by
  have hlen := E.itemsLen; have hnc := E.nc
  have hc : 0 < (wordAt m (m.reg 10 + 16)).toNat := by
    rw [hlen] at hi; simp only [elemBytes] at hi; omega
  refine ⟨hc, ?_⟩
  have := (E.buf hc).1; unfold RamRange Layout.ramHi at this
  have h' : items.length ≤ (wordAt m (m.reg 10 + 16)).toNat * elemBytes := by
    rw [hlen]; exact Nat.mul_le_mul_right _ hnc
  simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega

/-- The old buffer is not the allocator's and not a callee frame. -/
theorem Entry.oldSafe (E : Entry A L items m) (hc : 0 < (wordAt m (m.reg 10 + 16)).toNat) {x : Word}
    (hx : InRange (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) x) :
    ¬ A.Priv L x ∧ ¬ InRange (m.reg 2 - 128) 16 x := by
  refine ⟨fun hp => A.priv_not_live L x hp ⟨_, (E.buf hc).2, hx⟩, fun h => ?_⟩
  obtain ⟨-, -, ds, -⟩ := E.dbuf hc
  have h128 := sp128 E
  simp only [Apart, InRange, h128] at ds h hx; omega

/-- The `alloc` call of both paths and the return from it. -/
theorem alloc_step (E : Entry A L items m) {env : Env} {S Sl : SState} {mk mc : Machine} {b F : Nat}
    (he : EnvOk m env) (hS : S.regions = [frameR, headerR, allocObjR])
    (hSl : Sl.regions = [frameR, headerR, allocObjR]) (hmc : Match env Sl mc) (hwf : Env.WF env S)
    (hex : mc.pc.toNat = allocEntry) (hfr : SameOutside (InWritable env S) mk mc) (hp : Preserved mk mc)
    (hinv : Inv A L m mk) (hheap : A.Heap L mk) (hscr : ScratchSame m mk)
    (hitems : BytesAt mk (wordAt m (m.reg 10)) items) (hF : 32 ≤ F) (hwfB : Sl.wfB F = true)
    (r11 : (mc.reg 11).toNat = grown (m.reg 12).toNat * elemBytes) (r12 : Sl.reg 12 = .lit 0)
    (r1 : Sl.reg 1 = .lit 0x800cb55c) (r2 : Sl.reg 2 = .ptr 0 0)
    (k : ∀ m2, Match (env.setVars F fun i => m2.reg (Fin.ofNat 32 i)) (Sl.override (callOv Sl F none)) m2 →
      Env.WF (env.setVars F fun i => m2.reg (Fin.ofNat 32 i)) (Sl.override (callOv Sl F none)) →
      m2.pc.toNat = 0x800cb55c → Inv A L m m2 → ScratchSame m m2 →
      BytesAt m2 (wordAt m (m.reg 10)) items →
      AllocOut A L (grown (m.reg 12).toNat * elemBytes) m2 → Returns mc m2 →
      Reaches zesuImage b (Post A L items m) m2) :
    Reaches zesuImage (53 + b) (Post A L items m) mc := by
  have own : ∀ a, InWritable env S a → InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 he hS h
  have g2 : mc.reg 2 = m.reg 2 - 112 := by
    rw [← hmc.regs 2]; show Sym.eval env (Sl.reg 2) = _; rw [r2]
    show env.base 0 + BitVec.ofInt 64 0 = _; rw [he.base0]; simp
  have g1 : mc.reg 1 = BitVec.ofNat 64 0x800cb55c := by
    rw [← hmc.regs 1]; show Sym.eval env (Sl.reg 1) = _; rw [r1]; rfl
  have g12 : mc.reg 12 = 0 := by
    rw [← hmc.regs 12]; show Sym.eval env (Sl.reg 12) = _; rw [r12]; rfl
  have hheapc : A.Heap L mc := A.heap_frame L mk mc hheap fun a ha => hfr a fun hw =>
    E.ownNotPriv (own a hw) ha
  have hreq := E.req
  have hpre : A.Heap L mc ∧ 0 < (mc.reg 11).toNat ∧ (mc.reg 11).toNat < 2 ^ 63 ∧
      (mc.reg 12).toNat ≤ 3 ∧ StackOk mc 16 ∧ RetAligned mc ∧ CalleeFrameFree (A.Priv L) mc := by
    refine ⟨hheapc, ?_, ?_, by rw [g12]; decide, E.calleeStack (hinv.2.trans hp) g2,
      by unfold RetAligned; rw [g1]; decide, E.calleeFree (fun _ h => h) g2⟩
    · rw [r11]; simp only [grown, elemBytes]; omega
    · rw [r11]; simp only [grown, elemBytes]; omega
  have hcall := Reaches.preserve (A.alloc_spec L mc (by simpa [allocEntry] using hex) hpre)
  refine Reaches.trans hcall fun m2 hpost => ?_
  obtain ⟨⟨hret, hfrA, hout⟩, hp2⟩ := hpost
  rw [r11] at hout
  have hcf : mc.reg 2 - 16 = m.reg 2 - 128 := by rw [g2]; bv_omega
  rw [hcf] at hfrA
  have hframe : ∀ r j, r < Sl.regions.length → j < env.size r →
      m2.mem (env.base r + BitVec.ofNat 64 j) = mc.mem (env.base r + BitVec.ofNat 64 j) := by
    intro r j hr hj
    have hr3 : r < 3 := by rw [hSl] at hr; simpa using hr
    refine hfrA _ fun h => ?_
    rcases h with h | h
    · exact E.regionNotPriv he hr3 hj h
    · exact E.calleeApart he r j hr3 hj h
  obtain ⟨hm2, hwf2⟩ := after_call_ov (F := F) (a0 := none) hmc (hwf.congr (hSl.trans hS.symm)) hwfB
    hret (fun s h => by simp at h) hframe
  have hinv2 : Inv A L m m2 := by
    refine (hinv.step hfr (fun a h => E.inWritable' he hS h) hp).step hfrA ?_ hp2
    intro a h
    rcases h with h | h
    · exact .inr (.inr (.inr (.inl h)))
    · refine .inr (.inl ?_)
      have h128 := sp128 E
      simp only [InRange, h128] at h ⊢; omega
  have hpc2 : m2.pc.toNat = 0x800cb55c := by rw [hret.1, g1]; decide
  have hsame : ∀ x, ¬ A.Priv L x → ¬ InRange (m.reg 2 - 128) 16 x → ¬ (InRange (m.reg 2 - 112) 112 x ∨
      InRange (m.reg 10) 24 x) → m2.mem x = mk.mem x := fun x h1 h2 h3 =>
    (hfrA x fun h => h.elim h1 h2).trans (hfr x fun hw => h3 (own x hw))
  refine k m2 hm2 hwf2 hpc2 hinv2 (fun j hj => ?_) (fun i hi => ?_) hout hret
  · have hs : (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j).toNat = Layout.extraParams + j := by
      simp [Layout.extraParams]; omega
    have hin : InRange (BitVec.ofNat 64 Layout.extraParams) 8
        (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j) := by
      simp only [InRange]; rw [hs]; simp [Layout.extraParams]; omega
    rw [hsame _ (E.priv _ (.inr (.inr (.inr hin)))) (fun h => by
        have d := E.d6; have h128 := sp128 E
        simp only [InRange] at h; rw [hs, h128] at h
        simp only [Apart, h128, Layout.extraParams, BitVec.toNat_ofNat, Nat.reduceMod,
          Nat.reducePow] at d h; omega)
      (fun h => E.scratchNotOwn hj h)]
    exact hscr j hj
  · obtain ⟨hc, hin⟩ := E.itemsOld hi
    obtain ⟨h1, h2⟩ := E.oldSafe hc hin
    rw [hsame _ h1 h2 (E.oldNotOwn hc hin)]; exact hitems i hi

theorem sll5_eval {env : Env} {v : Word} {i : Nat} (h : env.vars i = BitVec.ofNat 64 (grown v.toNat))
    (hv : v.toNat < 2 ^ 32) :
    ((Sym.bin .sll (.var i) (.lit 5)).eval env).toNat = grown v.toNat * elemBytes := by
  show (BinOp.eval .sll (env.vars i) (BitVec.ofNat 64 5)).toNat = _
  rw [h]; simp only [BinOp.eval, BitVec.toNat_ofNat, Nat.reduceMod]
  have := grown_shl5 v hv
  rw [this]; simp only [BitVec.toNat_ofNat, grown, elemBytes]; omega

/-- After `remap` (which returned null): `alloc`, then `stage2b`. -/
theorem stage1 (E : Entry A L items m) {env : Env} {m2 : Machine}
    (he : EnvOk m env) (hm : Match env S1 m2) (hwf : Env.WF env S1)
    (hpc : m2.pc.toNat = 0x800cb4f8) (hinv : Inv A L m m2)
    (hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat)
    (hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat)
    (hv120 : env.vars 120 = 0) (hv122 : env.vars 122 = BitVec.ofNat 64 (grown (m.reg 12).toNat))
    (hheap : A.Heap L m2) (hscr : ScratchSame m m2) (hitems : BytesAt m2 (wordAt m (m.reg 10)) items) :
    Reaches zesuImage 148 (Post A L items m) m2 := by
  have hreq := E.req
  refine run_reaches' run1 hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run1_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exfalso
    have h2 : (SBool.eq (.bin .sll (.var 122) (.lit 5)) (.lit 0)).eval env = true := hc _ (by simp)
    simp only [SBool.eval, beq_iff_eq] at h2
    have h := congrArg BitVec.toNat h2
    rw [sll5_eval (i := 122) hv122 hreq] at h
    simp only [Sym.eval_lit, grown, elemBytes, BitVec.toNat_ofNat, Nat.zero_mod] at h; omega
  · refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
    refine Reaches.mono (b := 53 + 78) ?_ (by decide) (fun _ h => h)
    refine alloc_step (F := 300) E he (by decide) (by decide) hmc hwf (by simpa using hex) hfr hp hinv
      hheap hscr hitems (by decide) (by decide)
      (by rw [← hmc.regs 11]; exact sll5_eval hv122 hreq) rfl rfl rfl
      fun m2' hm2 hwf2 hpc2 hinv2 hscr2 hitems2 hout _ => ?_
    exact stage2b E (he.setVars (by decide) _) hm2 hwf2 hpc2 hinv2 hc0 hlt
      (by simp [Env.setVars]) (by simp [Env.setVars, hv122]) hitems2 hscr2 hout
  · exfalso; sym_simp at hc; simp only [bne_iff_ne, ne_eq, hv120] at hc; exact hc rfl

set_option hygiene false in
/-- A path that needs the grown capacity to overflow `2^59` is infeasible. -/
macro "f1_overflow" : tactic => `(tactic| (
  sym_simp at hc; simp only [E.cap] at hc; simp only [entryEnv, Fin.ofNat] at hc
  simp at hc; simp only [g_or' _ hreq, grown_srl59 _ hreq] at hc; simp at hc))

/-- From the entry: no growth, or `alloc` (capacity 0), or `remap` (capacity > 0). -/
theorem stage0 (E : Entry A L items m) (hpc : m.pc.toNat = entry) :
    Reaches zesuImage 197 (Post A L items m) m := by
  refine run_reaches' run0 E.wf E.match hpc E.ro ?_
  intro l hl hc
  simp only [run0_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  have hreq := E.req
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- no growth: return 0
    sym_simp at hc
    simp only [E.cap] at hc
    refine ⟨fun o ho => ?_, by decide, fun mf hm hex hfr _ => Reaches.done ?_⟩
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
  · -- capacity 0: `alloc`
    have hc2 := hc
    sym_simp at hc2; simp only [E.cap] at hc2; simp only [entryEnv, Fin.ofNat] at hc2; simp at hc2
    have hc0 : (wordAt m (m.reg 10 + 16)).toNat = 0 := by simp [hc2.2.1]
    have hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat := by
      have := hc2.1; simp [BitVec.ult] at this; simpa using this
    refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
    have h22 : mc.reg 22 = BitVec.ofNat 64 (grown (m.reg 12).toNat) := by
      rw [Match.reg_eq hmc 22 22 rfl]
      simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
      simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
      simp [entryEnv]
      exact g_or' _ hreq
    have h11 : mc.reg 11 = BitVec.ofNat 64 (grown (m.reg 12).toNat * elemBytes) := by
      rw [Match.reg_eq hmc 11 11 rfl]
      simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
      simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
      simp [entryEnv]
      simp only [g_or' _ hreq, grown_shl5 _ hreq]
    have r11 : (mc.reg 11).toNat = grown (m.reg 12).toNat * elemBytes := by
      rw [h11, BitVec.toNat_ofNat]; simp only [grown, elemBytes]; omega
    refine Reaches.mono (b := 53 + 103) ?_ (by decide) (fun _ h => h)
    refine alloc_step (F := 200) E (envOk0 m) (by decide) (by decide) hmc E.wf (by simpa using hex)
      hfr hp Inv.refl E.heap (fun _ _ => rfl) E.items (by decide) (by decide) r11 rfl rfl rfl
      fun m2 hm2 hwf2 hpc2 hinv2 hscr2 hitems2 hout hret => ?_
    exact stage2a E ((envOk0 m).setVars (by decide) _) hm2 hwf2 hpc2 hinv2 hc0 hlt
      (by simp [Env.setVars]) (by simp [Env.setVars]; rw [hret.2 22 (by decide), h22]) hitems2 hscr2 hout
  · exfalso; f1_overflow
  · -- capacity > 0: `remap` (F0) first
    have hc2 := hc
    sym_simp at hc2; simp only [E.cap] at hc2; simp only [entryEnv, Fin.ofNat] at hc2; simp at hc2
    have hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat := by
      have := hc2.2.1
      refine Nat.pos_of_ne_zero fun h => this ?_
      apply BitVec.eq_of_toNat_eq; simpa using h
    have hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat := by
      have := hc2.1; simp [BitVec.ult] at this; simpa using this
    refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
    have own : ∀ a, InWritable (env0 m) S0 a → InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
      fun a h => E.inWritable2 (envOk0 m) (by decide) h
    have h22 : mc.reg 22 = BitVec.ofNat 64 (grown (m.reg 12).toNat) := by
      rw [Match.reg_eq hmc 22 22 rfl]
      simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
      simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
      simp [entryEnv]
      exact g_or' _ hreq
    have h20 : mc.reg 20 = 0 := by
      rw [Match.reg_eq hmc 20 20 rfl]
      simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
      simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
      simp [entryEnv]
      simp only [g_or' _ hreq, grown_srl59 _ hreq] <;> rfl
    have g2 : mc.reg 2 = m.reg 2 - 112 := by
      rw [Match.reg_eq hmc 2 2 rfl]; show (env0 m).base 0 + BitVec.ofInt 64 0 = _
      rw [(envOk0 m).base0]; simp
    have g1 : mc.reg 1 = BitVec.ofNat 64 0x800cb4f8 := by rw [Match.reg_eq hmc 1 1 rfl]; rfl
    have hinv1 : Inv A L m mc := Inv.refl.step hfr (fun a h => E.inWritable' (envOk0 m) (by decide) h) hp
    have hpre : F0.Pre mc := ⟨hinv1.ro E, E.calleeStack hp g2, by unfold RetAligned; rw [g1]; decide⟩
    have hcall := Reaches.preserve (F0.f0_spec mc (by simpa [F0.entry] using hex) hpre)
    refine Reaches.mono (b := 9 + 148) (Reaches.trans hcall fun m2 hpost => ?_) (by decide) fun _ h => h
    obtain ⟨⟨hret, ha0, hfrR⟩, hp2⟩ := hpost
    have hcf : mc.reg 2 - 16 = m.reg 2 - 128 := by rw [g2]; bv_omega
    rw [hcf] at hfrR
    obtain ⟨hm2, hwf2⟩ := after_call_ov (F := 100) (a0 := some (.lit 0)) hmc (E.wf.congr (by decide))
      (by decide) hret (fun s h => by cases h; rw [ha0]; rfl)
      (fun r j hr hj => hfrR _ (E.calleeApart (envOk0 m) r j (by simpa using hr) hj))
    have hsame : ∀ x, ¬ InRange (m.reg 2 - 128) 16 x →
        ¬ (InRange (m.reg 2 - 112) 112 x ∨ InRange (m.reg 10) 24 x) → m2.mem x = m.mem x :=
      fun x h1 h2 => (hfrR x h1).trans (hfr x fun hw => h2 (own x hw))
    refine stage1 E ((envOk0 m).setVars (by decide) _) hm2 hwf2
      (by rw [hret.1, g1]; decide) ?_ hc0 hlt
      (by simp [Env.setVars]; rw [hret.2 20 (by decide), h20]; rfl)
      (by simp [Env.setVars]; rw [hret.2 22 (by decide), h22]) ?_ ?_ ?_
    · refine hinv1.step hfrR (fun a h => .inr (.inl ?_)) hp2
      have h128 := sp128 E
      simp only [InRange, h128] at h ⊢; omega
    · refine A.heap_frame L m m2 E.heap fun a ha => hsame a (fun h => ?_) (fun h => E.ownNotPriv h ha)
      exact E.priv a (.inr (.inr (.inl ⟨h.1, by have := h.2; omega⟩))) ha
    · intro j hj
      have hs : (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j).toNat = Layout.extraParams + j := by
        simp [Layout.extraParams]; omega
      refine hsame _ (fun h => ?_) (E.scratchNotOwn hj)
      have d := E.d6; have h128 := sp128 E
      simp only [InRange] at h; rw [hs, h128] at h
      simp only [Apart, h128, Layout.extraParams, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at d h
      omega
    · intro i hi
      obtain ⟨hc, hin⟩ := E.itemsOld hi
      obtain ⟨-, h2⟩ := E.oldSafe hc hin
      rw [hsame _ h2 (E.oldNotOwn hc hin)]; exact E.items i hi
  -- leaves 5-7: the growth overflowed, impossible below 2^32
  all_goals (exfalso; f1_overflow)

end

/-- F1 meets its contract, given the allocator's assumed contracts. -/
theorem f1_spec (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (items : List Byte) :
    Spec zesuImage entry bound (Pre A L items) (Post A L items) :=
  fun _ hpc hpre => stage0 (Entry.of_pre hpre) hpc

/--
info: 'ZesuExec.Fn.F1.f1_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f1_spec

end ZesuExec.Fn.F1
