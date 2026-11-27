import ZesuExec.Fn.F1.Regions
import ZesuExec.Fn.Stage
import ZesuExec.Fn.F0.Proof

/-!
# F1: entry facts, environments and the call steps its plan's leaves share

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
  mem2 : ∀ j, env.mem0 2 j = (m.mem (m.reg 11 + BitVec.ofNat 64 j)).getD 0

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
  mem2 j := by simp [entryEnv, shape]

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
  mem2 := h.mem2

theorem EnvOk.regions {m : Machine} {env : Env} (h : EnvOk m env) :
    env.regions = (shape m).map (·.1) := by
  have hl := h.len; have b0 := h.base0; have b1 := h.base1; have b2 := h.base2
  have s0 := h.size0; have s1 := h.size1; have s2 := h.size2
  obtain ⟨vars, regions, mem0⟩ := env
  match regions, hl with
  | [a, b, c], _ =>
    simp only [Env.base, Env.size] at b0 b1 b2 s0 s1 s2
    simp only [shape, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    exact ⟨Prod.ext b0 s0, Prod.ext b1 s1, Prod.ext b2 s2⟩

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
  exact load_cst hwf hm (R := headerR) (by rw [hS]; rfl) (by rw [he.size1]; exact hoff.2)

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

/-- The `memcpy` call after `alloc` and the return from it, split for `ExitGoal`: `memcpy`'s
precondition, and at `0x800cb588` the items in the new block and the byte count in the scratch
word. -/
theorem copy_call (E : Entry A L items m) {env : Env} {S Sl : SState} {m2 mc : Machine}
    {iP : Nat}
    (he : EnvOk m env) (hwf : Env.WF env S) (hmc : Match env Sl mc)
    (hfr : SameOutside (InWritable env S) m2 mc)
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
    (r12 : Sl.reg 12 = .bin .sll (.init 1 8 8) (.lit 5)) (r1 : Sl.reg 1 = .lit 0x800cb588) :
    MemcpyPre mc ∧ ∀ m3, MemcpyPost mc m3 →
      Match env Sl m3 ∧ Env.WF env Sl ∧ m3.pc.toNat = 0x800cb588 ∧ Inv A L m m3 ∧
      BytesAt m3 (m2.reg 10) items ∧
      BytesAt m3 (BitVec.ofNat 64 Layout.extraParams)
        (wordBytes (BitVec.ofNat 64 ((wordAt m (m.reg 10 + 8)).toNat * elemBytes))) ∧
      A.Heap (L ++ [(m2.reg 10, grown (m.reg 12).toNat * elemBytes)]) m3 := by
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
  refine ⟨hdom, fun m3 hz => ?_⟩
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
  refine ⟨hm3, hwf.congr (hSl.trans hS.symm), hpc3, hinv3, ?_, ?_, ?_⟩
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

theorem sll5_eval {env : Env} {v : Word} {i : Nat} (h : env.vars i = BitVec.ofNat 64 (grown v.toNat))
    (hv : v.toNat < 2 ^ 32) :
    ((Sym.bin .sll (.var i) (.lit 5)).eval env).toNat = grown v.toNat * elemBytes := by
  show (BinOp.eval .sll (env.vars i) (BitVec.ofNat 64 5)).toNat = _
  rw [h]; simp only [BinOp.eval, BitVec.toNat_ofNat, Nat.reduceMod]
  have := grown_shl5 v hv
  rw [this]; simp only [BitVec.toNat_ofNat, grown, elemBytes]; omega

set_option hygiene false in
/-- A path that needs the grown capacity to overflow `2^59` is infeasible. -/
macro "f1_overflow" : tactic => `(tactic| (
  sym_simp at hc; simp only [E.cap] at hc; simp only [entryEnv, Fin.ofNat] at hc
  simp at hc; simp only [g_or' _ hreq, grown_srl59 _ hreq] at hc; simp at hc))

end
end ZesuExec.Fn.F1
