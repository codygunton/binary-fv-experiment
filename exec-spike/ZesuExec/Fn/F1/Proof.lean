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

theorem envOk0 (m : Machine) : EnvOk m (env0 m) where
  vars i := by simp [entryEnv]
  base0 := by simp [entryEnv, Env.base, shape]
  base1 := by simp [entryEnv, Env.base, shape]
  size1 := by simp [entryEnv, Env.size, shape]
  mem1 j := by simp [entryEnv, shape]

theorem EnvOk.setVars {m : Machine} {env : Env} (h : EnvOk m env) {F : Nat} (hF : 32 ≤ F)
    (f : Nat → Word) : EnvOk m (env.setVars F f) where
  vars i := by simp [Env.setVars, show ¬ F ≤ i.val by omega, h.vars i]
  base0 := h.base0
  base1 := h.base1
  size1 := h.size1
  mem1 := h.mem1

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
