import ZesuExec.Fn.F3.Lemmas

/-!
# F3 proof: `f3_spec : Spec zesuImage 0x800d6274 160 Pre Post`

Runs: from the entry to the call of `rlp.decodeItem` (`runE`, 17 steps); decodeItem by
`F2.f2_spec` (75); from the return point (`runR`: three error returns, the empty-payload return,
the loop entry, at most 26 steps); the loop over the payload bytes (`runL`: back edge 5, exit
20). The state after the call is described on the machine (`CallState`) and re-entered as a
fresh symbolic state, as is the loop head (`Inv`).
-/

namespace ZesuExec.Fn.F3
open ZesuExec ZesuExec.Sym ZesuExec.Machine

sym_run runE := run zesuImage [retPc, loopHead] 100 entry S0
sym_run runR := run zesuImage [retPc, loopHead] 100 retPc SR
sym_run runL := run zesuImage [retPc, loopHead] 100 loopHead SL

set_option linter.unusedSimpArgs false

/-! ## Facts from `Pre` -/

/-- The entry facts of `Pre`, with names. -/
structure Entry (m : Machine) : Prop where
  ro : RodataLoaded zesuImage m
  stack : StackOk m 112
  ra : RetAligned m
  resW : Machine.writable (m.reg 10).toNat 16 = true
  resA : (m.reg 10).toNat % 8 = 0
  resP : ∀ j < 16, (m.mem (m.reg 10 + BitVec.ofNat 64 j)).isSome
  slW : Machine.writable (m.reg 11).toNat 16 = true
  slA : (m.reg 11).toNat % 8 = 0
  slP : ∀ j < 16, (m.mem (m.reg 11 + BitVec.ofNat 64 j)).isSome
  inR : Machine.readable (wordAt m (m.reg 11)).toNat (wordAt m (m.reg 11 + 8)).toNat = true
  inP : ∀ j < (wordAt m (m.reg 11 + 8)).toNat,
    (m.mem (wordAt m (m.reg 11) + BitVec.ofNat 64 j)).isSome
  d1 : Disjoint (wordAt m (m.reg 11), (wordAt m (m.reg 11 + 8)).toNat) (m.reg 10, 16)
  d2 : Disjoint (wordAt m (m.reg 11), (wordAt m (m.reg 11 + 8)).toNat) (m.reg 11, 16)
  d3 : Disjoint (wordAt m (m.reg 11), (wordAt m (m.reg 11 + 8)).toNat) (m.reg 2 - 112, 112)
  d4 : Disjoint (m.reg 10, 16) (m.reg 11, 16)
  d5 : Disjoint (m.reg 10, 16) (m.reg 2 - 112, 112)
  d6 : Disjoint (m.reg 11, 16) (m.reg 2 - 112, 112)

theorem Entry.of_pre {m : Machine} (h : Pre m) : Entry m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- Stack addresses as numbers. -/
theorem Entry.sp {m : Machine} (e : Entry m) {k : Nat} (hk : k ≤ 112) :
    (m.reg 2 - BitVec.ofNat 64 k).toNat = (m.reg 2).toNat - k := by
  have := e.stack.2.1
  unfold Layout.ramLo at this
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem Entry.sp112 {m : Machine} (e : Entry m) : (m.reg 2 - 112).toNat = (m.reg 2).toNat - 112 :=
  e.sp (k := 112) (by decide)

theorem Entry.sp96 {m : Machine} (e : Entry m) : (m.reg 2 - 96).toNat = (m.reg 2).toNat - 96 :=
  e.sp (k := 96) (by decide)

theorem Entry.ram {m : Machine} (e : Entry m) :
    Layout.ramLo + 112 ≤ (m.reg 2).toNat ∧ (m.reg 2).toNat ≤ Layout.ramHi ∧ (m.reg 2).toNat % 16 = 0 :=
  ⟨e.stack.2.1, e.stack.2.2.1, e.stack.1⟩

theorem Entry.slLoad {m : Machine} (e : Entry m) (k : Nat) (hk : k = 0 ∨ k = 8) :
    m.load (m.reg 11 + BitVec.ofNat 64 k) 8 = some (wordAt m (m.reg 11 + BitVec.ofNat 64 k)) := by
  have hw := e.slW
  simp [Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi] at hw
  have ha : (m.reg 11 + BitVec.ofNat 64 k).toNat = (m.reg 11).toNat + k := toNat_add_ofNat (by omega)
  obtain ⟨v, hv⟩ := load_some (m := m) (a := m.reg 11 + BitVec.ofNat 64 k) (n := 8)
    (by rw [ha]; have := e.slA; omega)
    (by rw [ha]; simp [Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi]; omega)
    (fun t ht => by
      rw [ofNat_add_ofNat]; exact e.slP (k + t) (by omega))
  simp [wordAt, hv]

theorem Entry.wf {m : Machine} (e : Entry m) (mh : Machine) (ov : Nat → Option Sym) (ks : List Write) :
    Env.WF (entryEnv mh ((shape m).map (·.1))) (entryState ov regionsR ks) := by
  have h96 := e.sp96
  have h112 := e.sp112
  obtain ⟨hlo, hhi, hal⟩ := e.ram
  have hrw := e.resW; have hsw := e.slW; have hrd := e.inR
  have hd1 := e.d1; have hd2 := e.d2; have hd3 := e.d3; have hd4 := e.d4; have hd5 := e.d5
  have hd6 := e.d6
  unfold Fn.Disjoint at hd1 hd2 hd3 hd4 hd5 hd6
  simp only [h112] at hd1 hd2 hd3 hd4 hd5 hd6
  refine entry_wf (shape m) ?_ ?_
  · simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl)
    · refine ⟨by simp [frameR], by simp [frameR, h96]; omega, ?_⟩
      simp [frameR, Machine.writable, Machine.inRange, h96]
      simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
    · exact ⟨by simp [sliceR], by simpa [sliceR] using e.slA, by simpa [sliceR] using hsw⟩
    · exact ⟨by simp [resR], by simpa [resR] using e.resA, by simpa [resR] using hrw⟩
    · exact ⟨by simp [inputR], by simp [inputR, Nat.mod_one], by simpa [inputR] using hrd⟩
  · simp only [shape, shapeOf, List.map_cons, List.map_nil, List.pairwise_cons,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true, Fn.Disjoint, h96]
    simp [Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi] at hrw hsw
    refine ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, ?_⟩
    intro _ h; exact h.elim

theorem Entry.fit {m : Machine} (e : Entry m) : ∀ p ∈ shape m, p.1.1.toNat + p.1.2 < 2 ^ 64 := by
  have h96 := e.sp96
  obtain ⟨hlo, hhi, -⟩ := e.ram
  have hrw := e.resW; have hsw := e.slW; have hrd := e.inR
  simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false]
  simp [Machine.readable, Machine.writable, Machine.inRange, Layout.rodataLo, Layout.rodataHi,
    Layout.inputLo, Layout.inputHi, Layout.ramLo, Layout.ramHi] at hrd hsw hrw hlo hhi
  rintro p (rfl | rfl | rfl | rfl) <;> simp [h96] <;> omega

/-- The writable regions are the frame, the slice and the result. -/
theorem Entry.writable {m mh : Machine} (e : Entry m) {ov : Nat → Option Sym} {ks : List Write}
    {a : Word} (ha : InWritable (entryEnv mh ((shape m).map (·.1))) (entryState ov regionsR ks) a) :
    InRange (m.reg 10) 16 a ∨ InRange (m.reg 11) 16 a ∨ InRange (m.reg 2 - 112) 112 a := by
  obtain ⟨p, hp, hw, hin⟩ := inWritable_entry (shape := shape m) ha e.fit
  simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · right; right
    simp only [InRange, e.sp96, e.sp112] at hin ⊢; omega
  · exact .inr (.inl hin)
  · exact .inl hin
  · simp [inputR] at hw

/-- Two region addresses are equal when their sums are, without wrap. -/
theorem addr_eq {a b : Word} {i j : Nat} (ha : a.toNat + i < 2 ^ 64) (hb : b.toNat + j < 2 ^ 64)
    (h : a.toNat + i = b.toNat + j) : a + BitVec.ofNat 64 i = b + BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_add_ofNat ha, toNat_add_ofNat hb, h]

def envE (m : Machine) : Env := entryEnv m ((shape m).map (·.1))

theorem envE_facts (m : Machine) :
    (envE m).base 0 = m.reg 2 - 96 ∧ (envE m).base 1 = m.reg 11 ∧ (envE m).base 2 = m.reg 10 ∧
    (envE m).base 3 = wordAt m (m.reg 11) ∧ (envE m).size 0 = 96 ∧ (envE m).size 1 = 16 ∧
    (envE m).size 2 = 16 ∧ (envE m).size 3 = (wordAt m (m.reg 11 + 8)).toNat := by
  simp [envE, Env.base, Env.size, entryEnv, shape, shapeOf]

/-- Frame byte `k` is stack byte `16 + k` of `StackOk m 112`. -/
theorem Entry.frameP {m : Machine} (e : Entry m) {k : Nat} (hk : k < 96) :
    (m.mem (m.reg 2 - 96 + BitVec.ofNat 64 k)).isSome := by
  have h := e.stack.2.2.2 (16 + k) (by omega)
  obtain ⟨hlo, hhi, -⟩ := e.ram
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  rwa [addr_eq (a := m.reg 2 - BitVec.ofNat 64 112) (b := m.reg 2 - 96) (i := 16 + k) (j := k)
    (by rw [e.sp (by decide)]; omega) (by rw [e.sp96]; omega)
    (by rw [e.sp (by decide), e.sp96]; omega)] at h

theorem Entry.match0 {m : Machine} (e : Entry m) : Match (envE m) S0 m := by
  obtain ⟨hb0, hb1, hb2, hb3, hs0, hs1, hs2, hs3⟩ := envE_facts m
  refine entry_match (fun i hi s hs => ?_) (fun r j hr hj => ?_) ?_
  · simp only [ov] at hs
    by_cases h2 : i.val = 2
    · simp only [h2, if_true, Option.some.injEq] at hs
      subst hs
      have : i = 2 := Fin.ext h2
      subst this
      show (Sym.ptr 0 96).eval (envE m) = _
      simp [Sym.eval, hb0, BitVec.sub_add_cancel]
    by_cases h11 : i.val = 11
    · simp [h11] at hs
      subst hs
      have : i = 11 := Fin.ext h11
      subst this
      show (Sym.ptr 1 0).eval (envE m) = _
      simp [Sym.eval, hb1]
    by_cases h10 : i.val = 10
    · simp [h10] at hs
      subst hs
      have : i = 10 := Fin.ext h10
      subst this
      show (Sym.ptr 2 0).eval (envE m) = _
      simp [Sym.eval, hb2]
    simp [h2, h11, h10] at hs
  · show (m.mem ((envE m).base r + BitVec.ofNat 64 j)).isSome
    simp only [regionsR, List.length_cons, List.length_nil] at hr
    have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    change j < (envE m).size r at hj
    rcases hr4 with rfl | rfl | rfl | rfl
    · rw [hb0]; rw [hs0] at hj; exact e.frameP hj
    · rw [hb1]; rw [hs1] at hj; exact e.slP j hj
    · rw [hb2]; rw [hs2] at hj; exact e.resP j hj
    · rw [hb3]; rw [hs3] at hj; exact e.inP j hj
  · intro w hw t ht
    simp only [List.mem_singleton] at hw
    subst hw
    have hl := load_bytes (e.slLoad 0 (.inl rfl)) (by decide) t ht
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hl
    change ((m.mem ((envE m).base 1 + BitVec.ofNat 64 (0 + t))).getD 0) = _
    rw [hb1, Nat.zero_add, hl]
    simp only [Option.getD_some, Sym.eval]
    rw [show (entryEnv m ((shape m).map (·.1))).base 3 = wordAt m (m.reg 11) from hb3]
    simp

end ZesuExec.Fn.F3
