import ZesuExec.Fn.F3.Lemmas
import ZesuExec.Vc.Tactics
import ZesuExec.Vc.RunWith

/-!
# F3 proof: `f3_spec : Spec zesuImage 0x800d6274 160 Pre Post`

Runs: from the entry through the call of `rlp.decodeItem` to the returns and the loop head
(`runW`, `runWith` with decodeItem's `Summary`: three error returns, the empty-payload return,
the loop entry, at most 118 steps of which 75 are decodeItem's bound); the loop over the payload
bytes (`runL`: back edge 5, exit 20). The call is discharged by `F2.f2_spec` in `CallHyp`, which
also records the machine after the call (`CallState`); the leaves after the call read
decodeItem's outcome through `CallFact`. The loop head is re-entered as a fresh symbolic state
(`Inv`). The return address of the call is not a cut point (programme plan S5 probe 2).
-/

namespace ZesuExec.Fn.F3
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-- `rlp.decodeItem` (F2): at most `F2.bound` instructions; writes the 40-byte outcome `a0`
points to. -/
def decodeItemSum : Summary := ⟨F2.bound, abiClobbers, none, [(10, 40)]⟩

def sums (t : Nat) : Option Summary := if t = F2.entry then some decodeItemSum else none

/-- What the callee leaves outside the caller's regions: decodeItem's frame below F3's. -/
def X (m : Machine) : Word → Prop := InRange (m.reg 2 - 112) 112

sym_runw runW := runWith zesuImage sums [loopHead] 64 100 entry S0
sym_run runL := run zesuImage [loopHead] 100 loopHead SL

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

/-! ## The call of `rlp.decodeItem` -/

theorem rodata_lt : ∀ a b, zesuImage.rodataByte? a = some b → a < Layout.ramLo := by
  intro a b h
  have := zesu_rodata_range h; unfold Layout.rodataHi at this; unfold Layout.ramLo; omega

def calleeVars : List Nat := [21, 22, 23, 24, 25, 26, 27]

/-- The leaf of `runE` at the call. -/
abbrev CallLeaf (lS : SState) : Prop :=
  lS.reg 1 = .lit 0x800d62b8 ∧ lS.reg 2 = .ptr 0 0 ∧ lS.reg 8 = .ptr 0 96 ∧
  lS.reg 9 = .ptr 2 0 ∧ lS.reg 10 = .ptr 0 8 ∧ lS.reg 11 = .ptr 3 0 ∧ lS.reg 12 = .init 1 8 8 ∧
  lS.reg 18 = .ptr 1 0 ∧ lS.reg 19 = .ptr 3 0 ∧ lS.reg 20 = .init 1 8 8 ∧
  (∀ i ∈ calleeVars, lS.reg i = .var i) ∧
  lS.mem = [⟨0, 48, 8, .var 20⟩, ⟨0, 56, 8, .var 19⟩, ⟨0, 64, 8, .var 18⟩, ⟨0, 72, 8, .var 9⟩,
    ⟨0, 80, 8, .var 8⟩, ⟨0, 88, 8, .var 1⟩] ∧ lS.regions = regionsR

theorem callsW₁ : ∀ l ∈ runW_leaves, ∀ c ∈ l.calls, CallLeaf c.S ∧ c.target = F2.entry ∧
    c.ret = retPc ∧ c.conds = [] ∧ c.prevWr = [] := by decide

theorem callsW₂ : ∀ l ∈ runW_leaves, ∀ c ∈ l.calls, c.wr = [(0, 8, 40)] ∧ c.F = 64 ∧
    c.bound = F2.bound ∧ c.result = none ∧ c.S.okB 64 [] = true ∧ c.keptB = true := by decide

/-- The one summarised call on every path of `runW`: its state is the legacy call leaf's. -/
theorem callsW : ∀ l ∈ runW_leaves, ∀ c ∈ l.calls, CallLeaf c.S ∧ c.target = F2.entry ∧
    c.ret = retPc ∧ c.conds = [] ∧ c.prevWr = [] ∧ c.wr = [(0, 8, 40)] ∧ c.F = 64 ∧
    c.bound = F2.bound ∧ c.result = none ∧ c.S.okB 64 [] = true ∧ c.keptB = true :=
  fun l hl c hc =>
    let ⟨a1, a2, a3, a4, a5⟩ := callsW₁ l hl c hc
    let ⟨b1, b2, b3, b4, b5, b6⟩ := callsW₂ l hl c hc
    ⟨a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, b6⟩

theorem len_eval {m : Machine} (e : Entry m) :
    (Sym.init 1 8 8).eval (envE m) = wordAt m (m.reg 11 + 8) := by
  have hsw := e.slW
  simp only [Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi, Bool.and_eq_true,
    decide_eq_true_eq] at hsw
  have hl : m.load (m.reg 11 + BitVec.ofNat 64 8) 8 = some (wordAt m (m.reg 11 + 8)) :=
    e.slLoad 8 (.inr rfl)
  have h1 : 1 < ((shape m).map (·.1)).length := by simp [shape, shapeOf]
  have hreg : (((shape m).map (·.1))[1]'h1).1 = m.reg 11 := by simp [shape, shapeOf]
  have := init_eval_load (regs := (shape m).map (·.1)) (r := 1) (off := 8) (n := 8) h1
    (by rw [hreg]; exact hl) (by rw [hreg]; omega)
  unfold envE; exact this

/-- Registers at the call. -/
theorem call_regs {m m1 : Machine} (e : Entry m) {lS : SState} (hm1 : Match (envE m) lS m1)
    (hok : CallLeaf lS) :
    m1.reg 1 = BitVec.ofNat 64 0x800d62b8 ∧ m1.reg 2 = m.reg 2 - 96 ∧ m1.reg 8 = m.reg 2 ∧
    m1.reg 9 = m.reg 10 ∧ m1.reg 10 = m.reg 2 - 96 + BitVec.ofNat 64 8 ∧
    m1.reg 11 = wordAt m (m.reg 11) ∧ m1.reg 12 = wordAt m (m.reg 11 + 8) ∧
    m1.reg 18 = m.reg 11 ∧ m1.reg 19 = wordAt m (m.reg 11) ∧ m1.reg 20 = wordAt m (m.reg 11 + 8) ∧
    ∀ i : Fin 32, i.val ∈ calleeVars → m1.reg i = m.reg i := by
  obtain ⟨r1, r2, r8, r9, r10, r11, r12, r18, r19, r20, rv, -⟩ := hok
  obtain ⟨hb0, hb1, hb2, hb3, -⟩ := envE_facts m
  have g : ∀ i : Fin 32, m1.reg i = (lS.reg i.val).eval (envE m) := fun i => (hm1.regs i).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [g 1]; show (lS.reg 1).eval _ = _; rw [r1]; rfl
  · rw [g 2]; show (lS.reg 2).eval _ = _; rw [r2]; simp [Sym.eval, hb0]
  · rw [g 8]; show (lS.reg 8).eval _ = _; rw [r8]; simp [Sym.eval, hb0, BitVec.sub_add_cancel]
  · rw [g 9]; show (lS.reg 9).eval _ = _; rw [r9]; simp [Sym.eval, hb2]
  · rw [g 10]; show (lS.reg 10).eval _ = _; rw [r10]; simp [Sym.eval, hb0]
  · rw [g 11]; show (lS.reg 11).eval _ = _; rw [r11]; simp [Sym.eval, hb3]
  · rw [g 12]; show (lS.reg 12).eval _ = _; rw [r12]; exact len_eval e
  · rw [g 18]; show (lS.reg 18).eval _ = _; rw [r18]; simp [Sym.eval, hb1]
  · rw [g 19]; show (lS.reg 19).eval _ = _; rw [r19]; simp [Sym.eval, hb3]
  · rw [g 20]; show (lS.reg 20).eval _ = _; rw [r20]; exact len_eval e
  · rw [g i, rv i.val hi]; exact entryEnv_var m _ i

theorem Entry.inputFit {m : Machine} (e : Entry m) :
    (wordAt m (m.reg 11)).toNat + (wordAt m (m.reg 11 + 8)).toNat < 2 ^ 64 := by
  have := e.fit _ (show ((wordAt m (m.reg 11), (wordAt m (m.reg 11 + 8)).toNat), inputR) ∈ shape m
    by simp [shape, shapeOf])
  simpa using this

/-- decodeItem's precondition at the call. -/
theorem pre_call {m m1 : Machine} (e : Entry m) {lS : SState} (hm1 : Match (envE m) lS m1)
    (hok : CallLeaf lS) (hp1 : Preserved m m1) : F2.Pre m1 := by
  obtain ⟨r1, r2, -, -, r10, r11, r12, -⟩ := call_regs e hm1 hok
  have h96 := e.sp96
  have h112 := e.sp112
  obtain ⟨hlo, hhi, hal⟩ := e.ram
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  have hout : (m1.reg 10).toNat = (m.reg 2).toNat - 88 := by
    rw [r10, toNat_add_ofNat (by rw [h96]; omega), h96]; omega
  have hfr : (m1.reg 2 - 16).toNat = (m.reg 2).toNat - 112 := by
    rw [r2, BitVec.toNat_sub, h96]; simp; omega
  have hd3 := e.d3
  unfold Fn.Disjoint at hd3; simp only [h112] at hd3
  have hfit := e.inputFit
  refine ⟨RodataLoaded.preserved e.ro hp1 rodata_lt, ⟨?_, ?_, ?_, fun j hj => ?_⟩, ?_, ?_, fun j hj => ?_, ?_, ?_,
    fun j hj => ?_, ?_, ?_, ?_⟩
  · rw [r2, h96]; omega
  · rw [r2, h96]; unfold Layout.ramLo; omega
  · rw [r2, h96]; unfold Layout.ramHi; omega
  · apply hp1.1
    have := e.stack.2.2.2 j (by omega)
    rwa [addr_eq (a := m.reg 2 - BitVec.ofNat 64 112) (b := m1.reg 2 - BitVec.ofNat 64 16)
      (i := j) (j := j) (by rw [e.sp (by decide)]; omega)
      (by rw [r2]; rw [show (m.reg 2 - 96 - BitVec.ofNat 64 16).toNat = (m.reg 2).toNat - 112 by
        rw [BitVec.toNat_sub, h96]; simp; omega]; omega)
      (by rw [e.sp (by decide), r2, show (m.reg 2 - 96 - BitVec.ofNat 64 16).toNat =
        (m.reg 2).toNat - 112 by rw [BitVec.toNat_sub, h96]; simp; omega])] at this
  · unfold RetAligned; rw [r1]; decide
  · rw [r11, r12]; exact e.inR
  · rw [r11]; rw [r12] at hj; exact hp1.1 _ (e.inP j hj)
  · simp [Machine.writable, Machine.inRange, hout, Layout.ramLo, Layout.ramHi]; omega
  · rw [hout]; omega
  · apply hp1.1
    have := e.frameP (k := 8 + j) (by omega)
    rwa [addr_eq (a := m.reg 2 - 96) (b := m1.reg 10) (i := 8 + j) (j := j)
      (by rw [h96]; omega) (by rw [hout]; omega) (by rw [h96, hout]; omega)] at this
  · unfold Fn.Disjoint; simp only [r11, r12, hout]; omega
  · unfold Fn.Disjoint; simp only [r11, r12, hfr]; omega
  · unfold Fn.Disjoint; simp only [hout, hfr]; omega

/-- The caller's register saved at frame offset `off`. -/
def savedOf (m : Machine) (off : Nat) : Word :=
  if off = 88 then m.reg 1 else if off = 80 then m.reg 8 else if off = 72 then m.reg 9
  else if off = 64 then m.reg 18 else if off = 56 then m.reg 19 else m.reg 20

/-- The input bytes. -/
abbrev inputOf (m : Machine) : List Byte :=
  F2.bytesOf m (wordAt m (m.reg 11)) (wordAt m (m.reg 11 + 8)).toNat

/-- The machine after decodeItem returned: registers, the saved frame words, decodeItem's
outcome at frame offset 8, the frame present, memory outside the stack as at entry. -/
def CallState (m mh : Machine) : Prop :=
  (∀ i : Fin 32, i.val ∈ calleeVars → mh.reg i = m.reg i) ∧
  mh.reg 2 = m.reg 2 - 96 ∧ mh.reg 8 = m.reg 2 ∧ mh.reg 9 = m.reg 10 ∧ mh.reg 18 = m.reg 11 ∧
  mh.reg 19 = wordAt m (m.reg 11) ∧ mh.reg 20 = wordAt m (m.reg 11 + 8) ∧
  (∀ w ∈ knownR, ∀ t < 8,
    mh.mem (m.reg 2 - 96 + BitVec.ofNat 64 (w.off + t)) = some (byteOf (savedOf m w.off) t)) ∧
  (∃ before : List Byte, before.length = 40 ∧ ∀ k < 40,
    mh.mem (m.reg 2 - 96 + BitVec.ofNat 64 (8 + k)) =
      some (F2.resultByte (wordAt m (m.reg 11)) (inputOf m) before k)) ∧
  (∀ k < 96, (mh.mem (m.reg 2 - 96 + BitVec.ofNat 64 k)).isSome) ∧
  SameOutside (InRange (m.reg 2 - 112) 112) m mh

theorem Entry.init {m : Machine} (e : Entry m) :
    ∀ r j, r < regionsR.length → j < (envE m).size r →
      m.mem ((envE m).base r + BitVec.ofNat 64 j) = some ((envE m).byte0 r j) := by
  intro r j hr hj
  rw [e.match0.mem r j hr hj]
  rfl

theorem bytesOf_congr {m m' : Machine} {a : Word} {n : Nat}
    (h : ∀ j < n, m'.mem (a + BitVec.ofNat 64 j) = m.mem (a + BitVec.ofNat 64 j)) :
    F2.bytesOf m' a n = F2.bytesOf m a n := by
  unfold F2.bytesOf
  apply List.map_congr_left
  intro j hj
  rw [h j (List.mem_range.mp hj)]

/-- Memory after a leaf differs from the start only inside written regions, which `R` covers, and
inside `X ⊆ R`. -/
theorem so_of_leafW {env : Env} {S lS : SState} {m m' : Machine} {R X : Word → Prop}
    (hfr : SameOutside (FootW env S X) m m') (hX : ∀ a, X a → R a) (hm' : Match env lS m')
    (hreg : lS.regions = S.regions)
    (hinit : ∀ r j, r < S.regions.length → j < env.size r → lS.mem.all (·.r != r) = true →
      m.mem (env.base r + BitVec.ofNat 64 j) = some (env.byte0 r j))
    (hR : ∀ r j, r < S.regions.length → j < env.size r → lS.mem.all (·.r != r) = false →
      R (env.base r + BitVec.ofNat 64 j)) :
    SameOutside R m m' := by
  intro a ha
  by_cases hw : InWritable env S a
  · obtain ⟨r, R', j, hR', -, hj, rfl⟩ := hw
    have hr := (List.getElem?_eq_some_iff.mp hR').1
    by_cases hn : lS.mem.all (·.r != r) = true
    · rw [F2.match_nowrite hm' (by rw [hreg]; exact hr) hn hj, hinit r j hr hj hn]
    · exact absurd (hR r j hr hj (by simpa using hn)) ha
  · exact hfr a fun h => h.elim hw fun hx => ha (hX a hx)

/-- From the call leaf over decodeItem's contract to the return point. -/
theorem call_state {m m1 m2 : Machine} (e : Entry m) {lS : SState} (hm1 : Match (envE m) lS m1)
    (hok : CallLeaf lS) (hfr1 : SameOutside (FootW (envE m) S0 (X m)) m m1) (hp1 : Preserved m m1)
    (hpost : F2.Post m1 m2) (hp2 : Preserved m1 m2) :
    CallState m m2 ∧ m2.pc.toNat = retPc := by
  obtain ⟨r1, r2, r8, r9, r10, r11, r12, r18, r19, r20, rv⟩ := call_regs e hm1 hok
  obtain ⟨hret, hso2, hres⟩ := hpost
  have hmem := hok.2.2.2.2.2.2.2.2.2.2.2.1
  have hreg := hok.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hb0, hb1, hb2, hb3, hs0, hs1, hs2, hs3⟩ := envE_facts m
  have h96 := e.sp96
  have h112 := e.sp112
  obtain ⟨hlo, hhi, hal⟩ := e.ram
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  have hout : (m1.reg 10).toNat = (m.reg 2).toNat - 88 := by
    rw [r10, toNat_add_ofNat (by rw [h96]; omega), h96]; omega
  have hfr : (m1.reg 2 - 16).toNat = (m.reg 2).toNat - 112 := by
    rw [r2, BitVec.toNat_sub, h96]; simp; omega
  -- m → m1: only the frame changed
  have hso1 : SameOutside (InRange (m.reg 2 - 112) 112) m m1 := by
    refine so_of_leafW hfr1 (fun _ h => h) hm1 hreg (fun r j hr hj _ => e.init r j hr hj)
      fun r j hr hj hn => ?_
    rw [hmem] at hn
    simp only [S0, entryState, regionsR, List.length_cons, List.length_nil] at hr
    have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr4 with rfl | rfl | rfl | rfl
    · rw [hs0] at hj; rw [hb0]
      unfold InRange; rw [toNat_add_ofNat (by rw [h96]; omega), h96, h112]; omega
    all_goals simp at hn
  -- m1 → m2: decodeItem wrote its outcome and its frame
  have hso12 : ∀ a, ¬ InRange (m.reg 2 - 112) 112 a → m2.mem a = m1.mem a := by
    intro a ha
    refine hso2 a fun h => ha ?_
    simp only [InRange, h112] at ha ⊢
    rcases h with h | h <;> simp only [InRange, hout, hfr] at h <;> omega
  -- the input is the same in m1
  have hin1 : F2.bytesOf m1 (wordAt m (m.reg 11)) (wordAt m (m.reg 11 + 8)).toNat = inputOf m := by
    apply bytesOf_congr
    intro j hj
    apply hso1
    have hd3 := e.d3
    have hfit := e.inputFit
    unfold Fn.Disjoint at hd3
    simp only [InRange, h112] at hd3 ⊢
    rw [toNat_add_ofNat (by omega)]; omega
  refine ⟨⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun w hw t ht => ?_, ?_, fun k hk => ?_, ?_⟩, ?_⟩
  · have hcs : i ∈ calleeSaved := by
      simp only [calleeVars, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
      omega
    rw [hret.2 i hcs]; exact rv i hi
  · rw [hret.2 2 (by decide), r2]
  · rw [hret.2 8 (by decide), r8]
  · rw [hret.2 9 (by decide), r9]
  · rw [hret.2 18 (by decide), r18]
  · rw [hret.2 19 (by decide), r19]
  · rw [hret.2 20 (by decide), r20]
  · -- saved words: outside decodeItem's writes, as the leaf stored them
    have hm0 : ∀ j < 96, m1.mem (m.reg 2 - 96 + BitVec.ofNat 64 j) =
        some (memByte (envE m) lS.mem 0 j) := fun j hj => by
      have := hm1.mem 0 j (by rw [hreg]; decide) (by rw [hs0]; exact hj)
      rwa [hb0] at this
    have hm2 : ∀ j, 48 ≤ j → j < 96 →
        m2.mem (m.reg 2 - 96 + BitVec.ofNat 64 j) = m1.mem (m.reg 2 - 96 + BitVec.ofNat 64 j) := by
      intro j h1 h2
      apply hso2
      rintro (h | h) <;> simp only [InRange, hout, hfr] at h <;>
        rw [toNat_add_ofNat (by rw [h96]; omega), h96] at h <;> omega
    simp only [knownR, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
      rw [hm2 _ (by omega) (by omega), hm0 _ (by omega), hmem] <;>
      simp [memByte_cons, Write.covers, savedOf, Sym.eval, envE, entryEnv] <;>
      simp (disch := omega) only [if_pos, if_neg, Nat.add_sub_cancel_left] <;>
      intro h <;> omega
  · -- decodeItem's outcome
    have hb := hres (inputOf m) (F2.bytesOf m1 (m1.reg 10) 40)
      (by rw [r11, ← hin1]; exact bytesAt_bytesOf fun j hj => hp1.1 _ (by
        exact e.inP j hj))
      (by rw [r12]; simp [F2.bytesOf])
      (bytesAt_bytesOf fun j hj => hp1.1 _ (by
        have := e.frameP (k := 8 + j) (by omega)
        rwa [addr_eq (a := m.reg 2 - 96) (b := m1.reg 10) (i := 8 + j) (j := j)
          (by rw [h96]; omega) (by rw [hout]; omega) (by rw [h96, hout]; omega)] at this))
      (by simp [F2.bytesOf])
    refine ⟨F2.bytesOf m1 (m1.reg 10) 40, by simp [F2.bytesOf], fun k hk => ?_⟩
    have := hb k (by simp [F2.result40]; exact hk)
    rw [addr_eq (a := m.reg 2 - 96) (b := m1.reg 10) (i := 8 + k) (j := k)
      (by rw [h96]; omega) (by rw [hout]; omega) (by rw [h96, hout]; omega), this, r11]
    simp [F2.result40]
  · exact hp2.1 _ (hp1.1 _ (e.frameP hk))
  · intro a ha
    rw [hso12 a ha, hso1 a ha]
  · rw [hret.1, r1]; decide

/-! ## The state after the call, as a symbolic state -/

/-- Environment at the return point and the loop head: `var 32 = c`, `var 33 .. var 38` the
caller's `ra, s0 .. s4`. -/
def envR (m mh : Machine) (c : Word) : Env :=
  (entryEnv mh ((shape m).map (·.1))).setVars 32
    fun k => if k = 0 then c else savedOf m (96 - 8 * k)

theorem envR_facts (m mh : Machine) (c : Word) :
    (envR m mh c).base 0 = m.reg 2 - 96 ∧ (envR m mh c).base 1 = m.reg 11 ∧
    (envR m mh c).base 2 = m.reg 10 ∧ (envR m mh c).base 3 = wordAt m (m.reg 11) ∧
    (envR m mh c).size 0 = 96 ∧ (envR m mh c).size 1 = 16 ∧ (envR m mh c).size 2 = 16 ∧
    (envR m mh c).size 3 = (wordAt m (m.reg 11 + 8)).toNat ∧ (envR m mh c).vars 32 = c ∧
    (∀ i : Fin 32, (envR m mh c).vars i.val = mh.reg i) ∧
    (∀ r j, (envR m mh c).byte0 r j = (mh.mem ((envR m mh c).base r + BitVec.ofNat 64 j)).getD 0) := by
  have hv : ∀ i : Fin 32, (envR m mh c).vars i.val = mh.reg i := fun i => by
    simp only [envR, Env.setVars]
    rw [if_neg (by omega)]
    exact entryEnv_var mh _ i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hv, fun r j => rfl⟩
  all_goals simp [envR, Env.setVars, Env.base, Env.size, entryEnv, shape, shapeOf]

theorem Entry.notStack {m : Machine} (e : Entry m) {a : Word} {n j : Nat}
    (hd : Disjoint (a, n) (m.reg 2 - 112, 112)) (hfit : a.toNat + n < 2 ^ 64) (hj : j < n) :
    ¬ InRange (m.reg 2 - 112) 112 (a + BitVec.ofNat 64 j) := by
  unfold Fn.Disjoint at hd
  simp only [e.sp112] at hd
  unfold InRange; rw [e.sp112, toNat_add_ofNat (by omega)]; omega

theorem Entry.resFit {m : Machine} (e : Entry m) : (m.reg 10).toNat + 16 < 2 ^ 64 := by
  have := e.resW; simp [Machine.writable, Machine.inRange, Layout.ramHi] at this; omega

theorem Entry.slFit {m : Machine} (e : Entry m) : (m.reg 11).toNat + 16 < 2 ^ 64 := by
  have := e.slW; simp [Machine.writable, Machine.inRange, Layout.ramHi] at this; omega

theorem CallState.init {m mh : Machine} (e : Entry m) (hc : CallState m mh) (c : Word) :
    ∀ r j, r < regionsR.length → j < (envR m mh c).size r →
      mh.mem ((envR m mh c).base r + BitVec.ofNat 64 j) = some ((envR m mh c).byte0 r j) := by
  obtain ⟨hb0, hb1, hb2, hb3, hs0, hs1, hs2, hs3, -, -, hby⟩ := envR_facts m mh c
  obtain ⟨-, -, -, -, -, -, -, -, -, hpres, hso⟩ := hc
  intro r j hr hj
  rw [hby]
  suffices h : (mh.mem ((envR m mh c).base r + BitVec.ofNat 64 j)).isSome by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    rw [hx]; rfl
  simp only [regionsR, List.length_cons, List.length_nil] at hr
  have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr4 with rfl | rfl | rfl | rfl
  · rw [hb0]; rw [hs0] at hj; exact hpres j hj
  · rw [hb1]; rw [hs1] at hj
    rw [hso _ (e.notStack e.d6 e.slFit hj)]; exact e.slP j hj
  · rw [hb2]; rw [hs2] at hj
    rw [hso _ (e.notStack e.d5 e.resFit hj)]; exact e.resP j hj
  · rw [hb3]; rw [hs3] at hj
    rw [hso _ (e.notStack e.d3 e.inputFit hj)]; exact e.inP j hj

theorem CallState.match {m mh : Machine} (e : Entry m) (hc : CallState m mh) {c : Word}
    {ov : Nat → Option Sym} (hov : ∀ i, i ≠ 12 → ov i = ovR i)
    (h12 : ∀ s, ov 12 = some s → s.eval (envR m mh c) = mh.reg 12) :
    Match (envR m mh c) (entryState ov regionsR knownR) mh := by
  have hinit := hc.init e c
  obtain ⟨hb0, hb1, hb2, hb3, -, -, -, -, -, -, hby⟩ := envR_facts m mh c
  obtain ⟨-, r2, r8, r9, r18, r19, -, hsaved, -⟩ := hc
  refine F2.entry_match_vars (by decide) (fun i hi s hs => ?_)
    (fun r j hr hj => Option.isSome_iff_exists.mpr ⟨_, hinit r j hr hj⟩) (fun w hw t ht => ?_)
  · by_cases h12' : i.val = 12
    · have : i = 12 := Fin.ext h12'
      subst this; exact h12 s hs
    rw [hov _ h12'] at hs
    simp only [ovR] at hs
    by_cases e2 : i.val = 2
    · simp only [e2, if_true, Option.some.injEq] at hs; subst hs
      have : i = 2 := Fin.ext e2
      subst this
      show (Sym.ptr 0 0).eval (envR m mh c) = _
      simp [Sym.eval, hb0, r2]
    by_cases e8 : i.val = 8
    · simp [e8] at hs; subst hs
      have : i = 8 := Fin.ext e8
      subst this
      show (Sym.ptr 0 96).eval (envR m mh c) = _
      simp [Sym.eval, hb0, r8, BitVec.sub_add_cancel]
    by_cases e9 : i.val = 9
    · simp [e9] at hs; subst hs
      have : i = 9 := Fin.ext e9
      subst this
      show (Sym.ptr 2 0).eval (envR m mh c) = _
      simp [Sym.eval, hb2, r9]
    by_cases e18 : i.val = 18
    · simp [e18] at hs; subst hs
      have : i = 18 := Fin.ext e18
      subst this
      show (Sym.ptr 1 0).eval (envR m mh c) = _
      simp [Sym.eval, hb1, r18]
    by_cases e19 : i.val = 19
    · simp [e19] at hs; subst hs
      have : i = 19 := Fin.ext e19
      subst this
      show (Sym.ptr 3 0).eval (envR m mh c) = _
      simp [Sym.eval, hb3, r19]
    simp [e2, e8, e9, e18, e19] at hs
  · have hb0' : (entryEnv mh ((shape m).map (·.1))).base 0 = m.reg 2 - 96 := hb0
    show (mh.mem ((entryEnv mh ((shape m).map (·.1))).base w.r + BitVec.ofNat 64 (w.off + t))).getD 0 = _
    have hw' := hw
    simp only [knownR, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at ht ⊢ <;>
      rw [hb0', hsaved _ hw t ht] <;> simp [Sym.eval, Env.setVars, savedOf]

/-! ## Returns -/

def retT : Sym := .bin .and (.var 33) (.lit 18446744073709551614)

/-- Callee-saved registers at a return leaf: `sp = ptr 0 96`, `s0 .. s4` reloaded from the
frame, `s5 .. s11` their own variables. -/
def savedOK (lS : SState) : Bool :=
  lS.reg 2 == .ptr 0 96 && lS.reg 8 == .var 34 && lS.reg 9 == .var 35 && lS.reg 18 == .var 36 &&
    lS.reg 19 == .var 37 && lS.reg 20 == .var 38 && calleeVars.all fun i => lS.reg i == .var i

theorem ret_returns {m mh mf : Machine} (hc : CallState m mh) {c : Word} {lS : SState}
    (hm' : Match (envR m mh c) lS mf) (hex : mf.pc = retT.eval (envR m mh c))
    (hsv : savedOK lS = true) : Returns m mf := by
  obtain ⟨hb0, -, -, -, -, -, -, -, -, hv, -⟩ := envR_facts m mh c
  have hk := hc.1
  unfold savedOK at hsv
  simp only [Bool.and_eq_true, beq_iff_eq] at hsv
  obtain ⟨⟨⟨⟨⟨⟨e2, e8⟩, e9⟩, e18⟩, e19⟩, e20⟩, eall⟩ := hsv
  have ev : ∀ k ∈ calleeVars, lS.reg k = .var k :=
    fun k hk' => eq_of_beq (List.all_eq_true.mp eall k hk')
  have hvar : ∀ k, (Sym.var (32 + k)).eval (envR m mh c) = if k = 0 then c else savedOf m (96 - 8 * k) := by
    intro k; simp [Sym.eval, envR, Env.setVars]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hex]
    simp only [retT, Sym.eval, BinOp.eval, F2.notOne]
    have := hvar 1; simp only [Sym.eval] at this; rw [this]; rfl
  · rw [← hm'.regs i]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show (lS.reg 2).eval _ = _; rw [e2]; simp [Sym.eval, hb0, BitVec.sub_add_cancel]
    · show (lS.reg 8).eval _ = _; rw [e8]; exact (hvar 2).trans (by simp [savedOf])
    · show (lS.reg 9).eval _ = _; rw [e9]; exact (hvar 3).trans (by simp [savedOf])
    · show (lS.reg 18).eval _ = _; rw [e18]; exact (hvar 4).trans (by simp [savedOf])
    · show (lS.reg 19).eval _ = _; rw [e19]; exact (hvar 5).trans (by simp [savedOf])
    · show (lS.reg 20).eval _ = _; rw [e20]; exact (hvar 6).trans (by simp [savedOf])
    all_goals
      rw [ev _ (by decide)]
      exact (hv _).trans (hk _ (by decide))

theorem post_of {m mf : Machine} (hret : Returns m mf)
    (hso : SameOutside (fun a => InRange (m.reg 10) 16 a ∨ InRange (m.reg 11) 16 a ∨
      InRange (m.reg 2 - 112) 112 a) m mf)
    (hres : ∀ j < 16, mf.mem (m.reg 10 + BitVec.ofNat 64 j) =
      some (resultByte (inputOf m) ((m.mem (m.reg 10 + BitVec.ofNat 64 j)).getD 0) j))
    (hsl : ∀ j < 16, mf.mem (m.reg 11 + BitVec.ofNat 64 j) =
      some (sliceByte (wordAt m (m.reg 11)) (wordAt m (m.reg 11 + 8)) (inputOf m)
        ((m.mem (m.reg 11 + BitVec.ofNat 64 j)).getD 0) j)) : Post m mf := by
  refine ⟨hret, hso, fun input hi hl => ?_⟩
  have : input = inputOf m := by rw [F2.eq_bytesOf hi, hl]
  subst this
  exact ⟨hres, hsl⟩

/-- Memory after a return leaf, outside the result and the slice. -/
theorem ret_so {m mh mf : Machine} (e : Entry m) (hc : CallState m mh) {c : Word}
    {ov : Nat → Option Sym}
    (hfr : SameOutside (InWritable (envR m mh c) (entryState ov regionsR knownR)) mh mf) :
    SameOutside (fun a => InRange (m.reg 10) 16 a ∨ InRange (m.reg 11) 16 a ∨
      InRange (m.reg 2 - 112) 112 a) m mf := by
  intro a ha
  have hso := hc.2.2.2.2.2.2.2.2.2.2
  rw [hfr a fun h => ha (e.writable (mh := mh) (ov := ov) (ks := knownR) h)]
  exact hso a fun h => ha (.inr (.inr h))

/-- What a leaf after the call knows about its environment `env`, `mh` being the machine right
after decodeItem returned: the region bases and sizes, the result and slice bytes as at entry,
decodeItem's outcome as in `mh`. -/
structure RetEnv (m mh : Machine) (env : Env) : Prop where
  b0 : env.base 0 = m.reg 2 - 96
  b1 : env.base 1 = m.reg 11
  b2 : env.base 2 = m.reg 10
  b3 : env.base 3 = wordAt m (m.reg 11)
  s0 : env.size 0 = 96
  s1 : env.size 1 = 16
  s2 : env.size 2 = 16
  s3 : env.size 3 = (wordAt m (m.reg 11 + 8)).toNat
  kept : ∀ r j, (r = 1 ∨ r = 2) → j < 16 →
    env.byte0 r j = (m.mem (env.base r + BitVec.ofNat 64 j)).getD 0
  out : ∀ k < 40, env.byte0 0 (8 + k) = (mh.mem (m.reg 2 - 96 + BitVec.ofNat 64 (8 + k))).getD 0
  call : CallState m mh

theorem CallState.retEnv {m mh : Machine} (e : Entry m) (hc : CallState m mh) (c : Word) :
    RetEnv m mh (envR m mh c) := by
  obtain ⟨hb0, hb1, hb2, hb3, hs0, hs1, hs2, hs3, -, -, hby⟩ := envR_facts m mh c
  have hso := hc.2.2.2.2.2.2.2.2.2.2
  refine ⟨hb0, hb1, hb2, hb3, hs0, hs1, hs2, hs3, fun r j hr hj => ?_,
    fun k _ => by rw [hby, hb0], hc⟩
  rw [hby]
  rcases hr with rfl | rfl
  · rw [hb1, hso _ (e.notStack e.d6 e.slFit hj)]
  · rw [hb2, hso _ (e.notStack e.d5 e.resFit hj)]

/-- A region's byte after a leaf, through the leaf's view of it. -/
theorem leaf_byte {env : Env} {mf : Machine} {lS : SState} (hm' : Match env lS mf)
    (hreg : lS.regions = regionsR) {r n : Nat} {v : Nat → Option (Sym × Nat)}
    (hv : viewOK lS.mem r n v = true) (hr : r < 4) {j : Nat} (hj : j < n)
    (hjs : j < env.size r) :
    mf.mem (env.base r + BitVec.ofNat 64 j) = some (match v j with
      | some (s, k) => byteOf (s.eval env) k
      | none => env.byte0 r j) := by
  rw [hm'.mem r j (by rw [hreg]; exact hr) hjs, memByte_view hv hj]; rfl

theorem res_err {m mh mf : Machine} {env : Env} {lS : SState} (he : RetEnv m mh env)
    (hm' : Match env lS mf) (hreg : lS.regions = regionsR)
    (hv : viewOK lS.mem 2 16 (twoWords (.lit 0) (.lit 3)) = true)
    (hn : nextUint64 (inputOf m) = none) :
    ∀ j < 16, mf.mem (m.reg 10 + BitVec.ofNat 64 j) =
      some (resultByte (inputOf m) ((m.mem (m.reg 10 + BitVec.ofNat 64 j)).getD 0) j) := by
  intro j hj
  have := leaf_byte hm' hreg hv (by decide) hj (by rw [he.s2]; exact hj)
  rw [he.b2] at this
  rw [this, resultByte, hn]
  unfold twoWords
  by_cases h8 : j < 8
  · simp [h8, Sym.eval, Nat.mod_eq_of_lt h8]
  · simp only [h8, if_false, Sym.eval]
    congr 2; omega

theorem res_ok {m mh mf : Machine} {env : Env} {lS : SState} (he : RetEnv m mh env)
    (hm' : Match env lS mf) (hreg : lS.regions = regionsR) {a : Sym} {v : Word}
    {n : Nat} (hv : viewOK lS.mem 2 16 (wordTag a) = true) (ha : a.eval env = v)
    (hs : nextUint64 (inputOf m) = some (v, n)) :
    ∀ j < 16, mf.mem (m.reg 10 + BitVec.ofNat 64 j) =
      some (resultByte (inputOf m) ((m.mem (m.reg 10 + BitVec.ofNat 64 j)).getD 0) j) := by
  intro j hj
  have := leaf_byte hm' hreg hv (by decide) hj (by rw [he.s2]; exact hj)
  rw [he.kept 2 j (.inr rfl) hj, he.b2] at this
  rw [this, resultByte, hs]
  unfold wordTag
  by_cases h8 : j < 8
  · simp [h8, ha]
  · by_cases h10 : j < 10
    · simp [h8, h10, Sym.eval]
    · simp [h8, h10]

theorem sl_kept {m mh mf : Machine} {env : Env} {lS : SState} (he : RetEnv m mh env)
    (hm' : Match env lS mf) (hreg : lS.regions = regionsR)
    (hv : viewOK lS.mem 1 16 (fun _ => none) = true) (hn : nextUint64 (inputOf m) = none) :
    ∀ j < 16, mf.mem (m.reg 11 + BitVec.ofNat 64 j) =
      some (sliceByte (wordAt m (m.reg 11)) (wordAt m (m.reg 11 + 8)) (inputOf m)
        ((m.mem (m.reg 11 + BitVec.ofNat 64 j)).getD 0) j) := by
  intro j hj
  have := leaf_byte hm' hreg hv (by decide) hj (by rw [he.s1]; exact hj)
  rw [he.kept 1 j (.inl rfl) hj, he.b1] at this
  rw [this, sliceByte, hn]

theorem sl_ok {m mh mf : Machine} {env : Env} {lS : SState} (he : RetEnv m mh env)
    (hm' : Match env lS mf) (hreg : lS.regions = regionsR) {p q : Sym} {v : Word} {n : Nat}
    (hv : viewOK lS.mem 1 16 (twoWords p q) = true)
    (hp : p.eval env = wordAt m (m.reg 11) + BitVec.ofNat 64 n)
    (hq : q.eval env = wordAt m (m.reg 11 + 8) - BitVec.ofNat 64 n)
    (hs : nextUint64 (inputOf m) = some (v, n)) :
    ∀ j < 16, mf.mem (m.reg 11 + BitVec.ofNat 64 j) =
      some (sliceByte (wordAt m (m.reg 11)) (wordAt m (m.reg 11 + 8)) (inputOf m)
        ((m.mem (m.reg 11 + BitVec.ofNat 64 j)).getD 0) j) := by
  intro j hj
  have := leaf_byte hm' hreg hv (by decide) hj (by rw [he.s1]; exact hj)
  rw [he.b1] at this
  rw [this, sliceByte, hs]
  unfold twoWords
  by_cases h8 : j < 8
  · simp [h8, hp]
  · simp [h8, hq]

/-! ## decodeItem's outcome, read back -/

theorem outcome_bytes {m mh : Machine} {env : Env} (he : RetEnv m mh env) :
    ∃ before : List Byte, ∀ k < 40, env.byte0 0 (8 + k) =
      F2.resultByte (wordAt m (m.reg 11)) (inputOf m) before k := by
  obtain ⟨before, -, hb⟩ := he.call.2.2.2.2.2.2.2.2.1
  exact ⟨before, fun k hk => by rw [he.out k hk, hb k hk]; rfl⟩

theorem init_word {env : Env} {off : Nat} {w : Word} (h : ∀ t < 8, env.byte0 0 (off + t) = byteOf w t) :
    (Sym.init 0 off 8).eval env = w := by
  simp only [Sym.eval]
  exact word_of_bytes h

theorem outcome_err {m mh : Machine} {env : Env} (he : RetEnv m mh env)
    (hd : F2.decode (inputOf m) = .error) :
    (Sym.init 0 40 2).eval env = BitVec.ofNat 64 4 := by
  obtain ⟨before, hb⟩ := outcome_bytes he
  have h0 := hb 32 (by decide)
  have h1 := hb 33 (by decide)
  simp only [F2.resultByte, hd, F2.errorByte] at h0 h1
  simp only [Sym.eval, byteList]
  rw [show 40 = 8 + 32 from rfl, h0, show 40 + 1 = 8 + 33 from rfl, h1]
  decide

theorem outcome_ok {m mh : Machine} {env : Env} (he : RetEnv m mh env) {b : Bool} {h p : Nat}
    (hd : F2.decode (inputOf m) = .success b h p) :
    (Sym.init 0 40 2).eval env = BitVec.ofNat 64 0 ∧
    (Sym.bin .and (.init 0 24 1) (.lit 1)).eval env = BitVec.ofNat 64 (if b then 1 else 0) ∧
    (Sym.init 0 16 8).eval env = BitVec.ofNat 64 p ∧
    (Sym.init 0 32 8).eval env = BitVec.ofNat 64 (h + p) ∧
    (Sym.init 0 8 8).eval env =
      (if (inputOf m).head? = some 128 then 1 else wordAt m (m.reg 11) + BitVec.ofNat 64 h) := by
  obtain ⟨before, hb⟩ := outcome_bytes he
  have hr : ∀ k < 40, env.byte0 0 (8 + k) = F2.successByte
      (if (inputOf m).head? = some 128 then 1 else wordAt m (m.reg 11) + BitVec.ofNat 64 h)
      (BitVec.ofNat 64 p) (BitVec.ofNat 64 (h + p)) b before k := fun k hk => by
    rw [hb k hk, F2.resultByte, hd]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h0 := hr 32 (by decide)
    have h1 := hr 33 (by decide)
    simp [F2.successByte] at h0 h1
    simp only [Sym.eval, byteList]
    rw [show 40 = 8 + 32 from rfl, h0, show 40 + 1 = 8 + 33 from rfl, h1]
    decide
  · have h0 := hr 16 (by decide)
    simp [F2.successByte] at h0
    simp only [Sym.eval, byteList, BinOp.eval]
    rw [show 24 = 8 + 16 from rfl, h0]
    cases b <;> decide
  · exact init_word fun t ht => by
      rw [show 16 + t = 8 + (8 + t) by omega, hr _ (by omega)]
      simp only [F2.successByte]
      rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega
  · exact init_word fun t ht => by
      rw [show 32 + t = 8 + (24 + t) by omega, hr _ (by omega)]
      simp only [F2.successByte]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]; congr 1; omega
  · exact init_word fun t ht => by
      rw [show 8 + t = 8 + t from rfl, hr _ (by omega)]
      simp only [F2.successByte]
      rw [if_pos (by omega)]

/-! ## Leaves that keep the call state -/

/-- Registers a leaf keeps in the shape of `SR`. -/
abbrev KeepRegs (lS : SState) : Prop :=
  lS.reg 2 = .ptr 0 0 ∧ lS.reg 8 = .ptr 0 96 ∧ lS.reg 9 = .ptr 2 0 ∧ lS.reg 18 = .ptr 1 0 ∧
  lS.reg 19 = .ptr 3 0 ∧ lS.reg 20 = .var 20 ∧ ∀ i ∈ calleeVars, lS.reg i = .var i

theorem CallState.of_leaf {m mh mf : Machine} (hc : CallState m mh) {c : Word} {lS : SState}
    (hm' : Match (envR m mh c) lS mf) (hk : KeepRegs lS) (hmem : mf.mem = mh.mem) :
    CallState m mf := by
  obtain ⟨hb0, hb1, hb2, hb3, -, -, -, -, -, hv, -⟩ := envR_facts m mh c
  obtain ⟨k2, k8, k9, k18, k19, k20, kv⟩ := hk
  obtain ⟨hcv, -, r8, -, -, -, r20, hsaved, hout, hpres, hso⟩ := hc
  have g : ∀ i : Fin 32, mf.reg i = (lS.reg i.val).eval (envR m mh c) := fun i => (hm'.regs i).symm
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g i, kv _ hi]; exact (hv i).trans (hcv i hi)
  · rw [g 2]; show (lS.reg 2).eval _ = _; rw [k2]; simp [Sym.eval, hb0]
  · rw [g 8]; show (lS.reg 8).eval _ = _; rw [k8]; simp [Sym.eval, hb0, BitVec.sub_add_cancel]
  · rw [g 9]; show (lS.reg 9).eval _ = _; rw [k9]; simp [Sym.eval, hb2]
  · rw [g 18]; show (lS.reg 18).eval _ = _; rw [k18]; simp [Sym.eval, hb1]
  · rw [g 19]; show (lS.reg 19).eval _ = _; rw [k19]; simp [Sym.eval, hb3]
  · rw [g 20]; show (lS.reg 20).eval _ = _; rw [k20]; exact (hv 20).trans r20
  · rw [hmem]; exact hsaved
  · rw [hmem]; exact hout
  · rw [hmem]; exact hpres
  · intro a ha; rw [hmem]; exact hso a ha

/-! ## The loop over the payload bytes -/

def accSym : Sym := .bin .or (.bin .sll (.var 11) (.lit 8)) (.initx 3 0 (.var 32) 1 1)
def curSym : Sym := .bin .add (.ptr 3 1) (.var 32)

abbrev BackOK (l : Leaf) : Prop :=
  l.exit = .at loopHead ∧ l.conds = [.ne curSym (.var 13)] ∧
  l.obligs = [.inBounds 3 0 (.var 32) 1 1] ∧ l.S.steps = 5 ∧ l.S.mem = [] ∧
  l.S.regions = regionsR ∧ KeepRegs l.S ∧ l.S.reg 10 = .var 10 ∧ l.S.reg 11 = accSym ∧
  l.S.reg 12 = curSym ∧ l.S.reg 13 = .var 13

abbrev ExitOK (l : Leaf) : Prop :=
  l.exit = .ret retT ∧ l.conds = [.eq curSym (.var 13)] ∧
  l.obligs = [.inBounds 3 0 (.var 32) 1 1, .aligned retT 4] ∧ l.S.steps = 20 ∧
  l.S.regions = regionsR ∧ savedOK l.S = true ∧ viewOK l.S.mem 2 16 (wordTag accSym) = true ∧
  viewOK l.S.mem 1 16 (twoWords (.bin .add (.ptr 3 0) (.var 10)) (.bin .sub (.var 20) (.var 10))) = true

theorem leavesL : ∀ l ∈ runL_leaves, BackOK l ∨ ExitOK l := by decide

/-- Loop head after `j` of the `p` payload bytes at input offset `h`. -/
def Inv (m : Machine) (h p j : Nat) (mh : Machine) : Prop :=
  CallState m mh ∧ mh.pc.toNat = loopHead ∧ F2.decode (inputOf m) = .success false h p ∧
  1 ≤ p ∧ p ≤ 8 ∧ j < p ∧ h + p ≤ (wordAt m (m.reg 11 + 8)).toNat ∧
  mh.reg 10 = BitVec.ofNat 64 (h + p) ∧
  mh.reg 11 = BitVec.ofNat 64 (F2.bigEndian (((inputOf m).drop h).take j)) ∧
  mh.reg 12 = wordAt m (m.reg 11) + BitVec.ofNat 64 (h + j) ∧
  mh.reg 13 = wordAt m (m.reg 11) + BitVec.ofNat 64 (h + p)

theorem nextUint64_ok {m : Machine} {h p : Nat} (hd : F2.decode (inputOf m) = .success false h p)
    (hp : p ≤ 8) : nextUint64 (inputOf m) =
      some (BitVec.ofNat 64 (F2.bigEndian (((inputOf m).drop h).take p)), h + p) := by
  simp only [nextUint64, hd, if_pos hp]

theorem Entry.ro_of {m mh : Machine} (e : Entry m) (hso : SameOutside (InRange (m.reg 2 - 112) 112) m mh) :
    RodataLoaded zesuImage mh := by
  intro a b hab
  have ha := rodata_lt a b hab
  obtain ⟨hlo, -, -⟩ := e.ram
  unfold Layout.ramLo at ha hlo
  rw [hso _ (by
    unfold InRange; rw [e.sp112, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)]
  exact e.ro a b hab

/-- Two cursor words are equal only at the same small offset. -/
theorem add_small_inj {a : Word} {x y : Nat} (hx : x < 64) (hy : y < 64)
    (h : a + BitVec.ofNat 64 x = a + BitVec.ofNat 64 y) : x = y := by
  have := congrArg BitVec.toNat h
  simp [BitVec.toNat_add] at this
  have := a.isLt
  omega

theorem loop_step {m : Machine} (e : Entry m) {h p j : Nat} {mh : Machine} {b : Nat}
    (hI : Inv m h p j mh) (hb : 20 ≤ b)
    (hnext : j + 1 < p → ∀ mh', Inv m h p (j + 1) mh' → Reaches zesuImage (b - 5) (Post m) mh') :
    Reaches zesuImage b (Post m) mh := by
  have hI' := hI
  obtain ⟨hc, hpc, hd, hp1, hp8, hjp, hhp, r10, r11, r12, r13⟩ := hI'
  obtain ⟨hb0, hb1, hb2, hb3, hs0, hs1, hs2, hs3, hv32, hv, hby⟩ :=
    envR_facts m mh (BitVec.ofNat 64 (h + j))
  have hh9 := (decode_success hd).1
  have hfit := e.inputFit
  have hm : Match (envR m mh (BitVec.ofNat 64 (h + j))) SL mh :=
    hc.match e (ov := ovL) (fun i hi => by simp [ovL, hi])
      (fun s hs => by
        simp only [ovL, if_true, Option.some.injEq] at hs; subst hs
        simp only [Sym.eval, BinOp.eval, hb3, hv32, r12]; simp)
  have hwf : Env.WF (envR m mh (BitVec.ofNat 64 (h + j))) SL := F2.setVars_wf (e.wf mh ovL knownR) _ _
  have hso := hc.2.2.2.2.2.2.2.2.2.2
  have hv11 : (envR m mh (BitVec.ofNat 64 (h + j))).vars 11 = mh.reg 11 := hv 11
  have hv10 : (envR m mh (BitVec.ofNat 64 (h + j))).vars 10 = mh.reg 10 := hv 10
  have hv13 : (envR m mh (BitVec.ofNat 64 (h + j))).vars 13 = mh.reg 13 := hv 13
  have hv20 : (envR m mh (BitVec.ofNat 64 (h + j))).vars 20 = wordAt m (m.reg 11 + 8) :=
    (hv 20).trans hc.2.2.2.2.2.2.1
  have hlen : (inputOf m).length = (wordAt m (m.reg 11 + 8)).toNat := by simp [F2.bytesOf]
  have hdl : j < ((inputOf m).drop h).length := by rw [List.length_drop, hlen]; omega
  have hhj : (BitVec.ofNat 64 (h + j)).toNat = h + j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbyte : (envR m mh (BitVec.ofNat 64 (h + j))).byte0 3 (0 + 1 * (h + j)) =
      ((inputOf m).drop h)[j] := by
    rw [hby, hb3, Nat.zero_add, Nat.one_mul, hso _ (e.notStack e.d3 hfit (by omega))]
    simp [F2.bytesOf, Nat.add_comm, show h + j < (wordAt m (m.reg 11 + 8)).toNat by omega]
  have hacc : accSym.eval (envR m mh (BitVec.ofNat 64 (h + j))) =
      BitVec.ofNat 64 (F2.bigEndian (((inputOf m).drop h).take (j + 1))) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hdl, Option.toList_some, F2.bigEndian_append]
    have hlt : F2.bigEndian (((inputOf m).drop h).take j) < 2 ^ 56 := by
      refine Nat.lt_of_lt_of_le (F2.bigEndian_lt _) ?_
      have : (((inputOf m).drop h).take j).length ≤ 7 := by simp; omega
      exact Nat.le_trans (Nat.pow_le_pow_right (by decide) this) (by decide)
    simp only [accSym, Sym.eval, BinOp.eval, F2.ofBytes1, hv11, r11, hv32, hhj]
    try simp only [Nat.reduceMod, Nat.reducePow]
    rw [hbyte]
    exact F2.shl_or _ _ hlt
  have hcur : curSym.eval (envR m mh (BitVec.ofNat 64 (h + j))) =
      wordAt m (m.reg 11) + BitVec.ofNat 64 (h + j + 1) := by
    simp only [curSym, Sym.eval, BinOp.eval, hb3, hv32]
    rw [show BitVec.ofInt 64 1 = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat]
    congr 2; omega
  refine run_reaches runL hwf hm hpc (e.ro_of hso) fun l hl hcs => ?_
  rcases leavesL l hl with
    ⟨hex, hcd, hob, hst, hmem, hreg, hk, l10, l11, l12, l13⟩ |
    ⟨hex, hcd, hob, hst, hreg, hsv, hvr, hvs⟩
  · -- back edge
    rw [hcd] at hcs
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, SBool.eval, hcur] at hcs
    simp only [Sym.eval, hv13, r13, bne_iff_ne, ne_eq] at hcs
    have hne : j + 1 ≠ p := fun h' => hcs (by rw [show h + j + 1 = h + p by omega])
    refine ⟨?_, by rw [hst]; show 5 - 0 ≤ b; omega, fun m' hm' hex' hfr => ?_⟩
    · rw [hob]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Oblig.holds, Sym.eval, hv32,
        hs3, hhj]
      omega
    · have hm'' : m'.mem = mh.mem :=
        F2.mem_eq_of_nowrite hm' hfr hmem (by rw [hreg]; rfl) (hc.init e _)
      rw [hst]
      refine hnext (by omega) m' ⟨hc.of_leaf hm' hk hm'', ?_, hd, hp1, hp8, by omega, hhp, ?_, ?_, ?_, ?_⟩
      · rw [hex] at hex'; exact hex'
      · rw [← hm'.regs 10]; show (l.S.reg 10).eval _ = _; rw [l10]; exact hv10.trans r10
      · rw [← hm'.regs 11]; show (l.S.reg 11).eval _ = _; rw [l11]; exact hacc
      · rw [← hm'.regs 12]; show (l.S.reg 12).eval _ = _; rw [l12, hcur, Nat.add_assoc]
      · rw [← hm'.regs 13]; show (l.S.reg 13).eval _ = _; rw [l13]; exact hv13.trans r13
  · -- exit
    rw [hcd] at hcs
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, SBool.eval, hcur] at hcs
    simp only [Sym.eval, hv13, r13, beq_iff_eq] at hcs
    have hjp' : j + 1 = p := by have := add_small_inj (by omega) (by omega) hcs; omega
    refine ⟨?_, by show l.S.steps - 0 ≤ b; omega, fun m' hm' hex' hfr => ?_⟩
    · rw [hob]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Oblig.holds]
      refine ⟨?_, ?_⟩
      · simp only [Sym.eval, hv32, hs3, hhj]; omega
      · simpa [retT, Sym.eval, BinOp.eval, F2.notOne, Env.setVars, envR, savedOf] using e.ra
    · rw [hex] at hex'
      have hs := nextUint64_ok hd hp8
      refine Reaches.done (post_of (ret_returns hc hm' hex' hsv) (ret_so e hc hfr)
        (res_ok (hc.retEnv e _) hm' hreg hvr (hacc.trans (by rw [hjp'])) hs)
        (sl_ok (hc.retEnv e _) hm' hreg hvs ?_ ?_ hs))
      · simp only [Sym.eval, BinOp.eval, hb3, hv10, r10]; simp
      · simp only [Sym.eval, BinOp.eval, hv20, hv10, r10]

theorem loop_reaches {m : Machine} (e : Entry m) {h p : Nat} :
    ∀ μ j mh, j + μ + 1 = p → Inv m h p j mh → Reaches zesuImage (μ * 5 + 20) (Post m) mh := by
  intro μ
  induction μ with
  | zero =>
    intro j mh hj hI
    exact loop_step e hI (by omega) fun h' => absurd h' (by omega)
  | succ μ ih =>
    intro j mh hj hI
    refine loop_step e hI (by omega) fun _ mh' hI' => ?_
    rw [show (μ + 1) * 5 + 20 - 5 = μ * 5 + 20 by omega]
    exact ih (j + 1) mh' (by omega) hI'

/-! ## From the return point -/

set_option hygiene false in
/-- A leaf's conditions as facts about the outcome words. -/
macro "f3_conds" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    SBool.eval] at hcs
  try simp only [hst] at hcs
  try simp only [hfl] at hcs
  try simp only [hpl] at hcs
  simp only [Sym.eval] at hcs
  try simp [BitVec.ult, bne, BitVec.toNat_eq] at hcs))

/-- `Post`'s frame from a leaf's: the writable regions are the result, the slice and the frame;
decodeItem's frame is the rest of the 112 stack bytes. -/
theorem ret_soW {m mf : Machine} (e : Entry m)
    (hfr : SameOutside (FootW (envE m) S0 (X m)) m mf) :
    SameOutside (fun a => InRange (m.reg 10) 16 a ∨ InRange (m.reg 11) 16 a ∨
      InRange (m.reg 2 - 112) 112 a) m mf :=
  fun a ha => hfr a fun h => ha (h.elim (fun hw => e.writable (mh := m) hw) fun hx => .inr (.inr hx))

/-- A return leaf after the call. -/
theorem ret_leafW {m mh mf : Machine} (e : Entry m) {env' : Env} {lS : SState} {b : Nat}
    (he : RetEnv m mh env') (hv : ∀ i : Fin 32, env'.vars i.val = m.reg i) (hm' : Match env' lS mf)
    (hregs : (calleeSaved.filter (· ≠ 2)).all (fun i => lS.reg i.val == .var i.val) = true)
    (hsp : lS.reg 2 = .ptr 0 96)
    (hex : mf.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env')
    (hfr : SameOutside (FootW (envE m) S0 (X m)) m mf)
    (hres : ∀ j < 16, mf.mem (m.reg 10 + BitVec.ofNat 64 j) =
      some (resultByte (inputOf m) ((m.mem (m.reg 10 + BitVec.ofNat 64 j)).getD 0) j))
    (hsl : ∀ j < 16, mf.mem (m.reg 11 + BitVec.ofNat 64 j) =
      some (sliceByte (wordAt m (m.reg 11)) (wordAt m (m.reg 11 + 8)) (inputOf m)
        ((m.mem (m.reg 11 + BitVec.ofNat 64 j)).getD 0) j)) :
    Reaches zesuImage b (Post m) mf :=
  Reaches.done (post_of (returns_leaf hm' hv hregs
    (by rw [hsp]; simp [Sym.eval, he.b0, BitVec.sub_add_cancel]) hex) (ret_soW e hfr) hres hsl)

/-- The calls' facts give every leaf after the call its environment: the entry environment with
decodeItem's outcome as in the machine `mh` right after the call. -/
theorem envW {m : Machine} {l : LeafW} (hl : l ∈ runW_leaves) {env' : Env}
    (hf : ∀ c ∈ l.calls,
      CallFact zesuImage (X m) (fun _ _ m₂ => CallState m m₂) (envE m) 64 env' l.wr c) :
    ∃ mh, RetEnv m mh env' := by
  have hlw : ∀ l ∈ runW_leaves, l.wr = [(0, 8, 40)] ∧ 0 < l.calls.length := by decide
  obtain ⟨hw, hlen⟩ := hlw l hl
  obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos hlen
  obtain ⟨-, -, -, -, hp, hcw, hF, -⟩ := callsW l hl c hc
  obtain ⟨env₁, m₁, m₂, hag1, -, -, hcs, rest, hwr, hag2⟩ := hf c hc
  rw [hw, hp, hcw] at hwr
  have hr0 : rest = [] := by simpa using hwr
  rw [hp] at hag1
  rw [hF, hcw, hr0] at hag2
  obtain ⟨hb0, hb1, hb2, hb3, hs0, hs1, hs2, hs3⟩ := envE_facts m
  have hreg : env'.regions = (envE m).regions := hag2.regions.trans hag1.regions
  have hb : ∀ r, env'.base r = (envE m).base r := fun r => by simp [Env.base, hreg]
  have hs : ∀ r, env'.size r = (envE m).size r := fun r => by simp [Env.size, hreg]
  have hmem : ∀ r j, env'.byte0 r j = if Ranges.covers [(0, 8, 40)] r j then
      (m₂.mem ((envE m).base r + BitVec.ofNat 64 j)).getD 0 else (envE m).byte0 r j := by
    intro r j
    rw [Env.byte0, hag2.mem0 r j rfl]
    simp only [Env.havoc, hag1.base]
    split
    · rfl
    · rw [hag1.mem0 r j rfl]; rfl
  refine ⟨m₂, by rw [hb, hb0], by rw [hb, hb1], by rw [hb, hb2], by rw [hb, hb3],
    by rw [hs, hs0], by rw [hs, hs1], by rw [hs, hs2], by rw [hs, hs3], fun r j hr hj => ?_,
    fun k hk => ?_, hcs⟩
  · rw [hmem, if_neg (by rcases hr with rfl | rfl <;> simp [Ranges.covers]), hb]; rfl
  · rw [hmem, if_pos (by simp [Ranges.covers]; omega), hb0]

/-- The machine at the loop entry leaf keeps the call state. -/
theorem CallState.of_leafW {m mh mf : Machine} (e : Entry m) {env' : Env} {lS : SState}
    (he : RetEnv m mh env') (hag : Env.Agree (envE m) env' 64 [(0, 8, 40)])
    (hm' : Match env' lS mf) (hfr : SameOutside (FootW (envE m) S0 (X m)) m mf)
    (hk : lS.reg 2 = .ptr 0 0 ∧ lS.reg 8 = .ptr 0 96 ∧ lS.reg 9 = .ptr 2 0 ∧
      lS.reg 18 = .ptr 1 0 ∧ lS.reg 19 = .ptr 3 0 ∧ lS.reg 20 = .init 1 8 8 ∧
      ∀ i ∈ calleeVars, lS.reg i = .var i)
    (hmem : lS.mem = [⟨0, 48, 8, .var 20⟩, ⟨0, 56, 8, .var 19⟩, ⟨0, 64, 8, .var 18⟩,
      ⟨0, 72, 8, .var 9⟩, ⟨0, 80, 8, .var 8⟩, ⟨0, 88, 8, .var 1⟩])
    (hreg : lS.regions = regionsR) : CallState m mf := by
  have hv : ∀ i : Fin 32, env'.vars i.val = m.reg i := fun i =>
    (hag.vars i.val (by omega)).trans (entryEnv_var m _ i)
  have g : ∀ i : Fin 32, mf.reg i = (lS.reg i.val).eval env' := fun i => (hm'.regs i).symm
  obtain ⟨k2, k8, k9, k18, k19, k20, kv⟩ := hk
  have h96 := e.sp96
  have h112 := e.sp112
  obtain ⟨hlo, hhi, -⟩ := e.ram
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  have hm0 : ∀ j < 96, mf.mem (m.reg 2 - 96 + BitVec.ofNat 64 j) =
      some (memByte env' lS.mem 0 j) := fun j hj => by
    have := hm'.mem 0 j (by rw [hreg]; decide) (by rw [he.s0]; exact hj)
    rwa [he.b0] at this
  have hv1 : env'.vars 1 = m.reg 1 := hv 1
  have hv8 : env'.vars 8 = m.reg 8 := hv 8
  have hv9 : env'.vars 9 = m.reg 9 := hv 9
  have hv18 : env'.vars 18 = m.reg 18 := hv 18
  have hv19 : env'.vars 19 = m.reg 19 := hv 19
  have hv20 : env'.vars 20 = m.reg 20 := hv 20
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun w hw t ht => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [g i, kv _ hi]; exact hv i
  · rw [g 2]; show (lS.reg 2).eval _ = _; rw [k2]; simp [Sym.eval, he.b0]
  · rw [g 8]; show (lS.reg 8).eval _ = _; rw [k8]; simp [Sym.eval, he.b0, BitVec.sub_add_cancel]
  · rw [g 9]; show (lS.reg 9).eval _ = _; rw [k9]; simp [Sym.eval, he.b2]
  · rw [g 18]; show (lS.reg 18).eval _ = _; rw [k18]; simp [Sym.eval, he.b1]
  · rw [g 19]; show (lS.reg 19).eval _ = _; rw [k19]; simp [Sym.eval, he.b3]
  · rw [g 20]; show (lS.reg 20).eval _ = _; rw [k20, Sym.eval_agree hag _ (by decide)]
    exact len_eval e
  · simp only [knownR, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at ht ⊢ <;>
      rw [hm0 _ (by omega), hmem] <;>
      simp [memByte_cons, Write.covers, savedOf, Sym.eval, hv1, hv8, hv9, hv18, hv19, hv20] <;>
      simp (disch := omega) only [if_pos, if_neg, Nat.add_sub_cancel_left] <;>
      intro h <;> omega
  · obtain ⟨before, hbl, hbb⟩ := he.call.2.2.2.2.2.2.2.2.1
    refine ⟨before, hbl, fun k hk => ?_⟩
    rw [hm0 _ (by omega)]
    have hnone : memByte env' lS.mem 0 (8 + k) = env'.byte0 0 (8 + k) := by
      rw [hmem]; unfold memByte
      rw [List.find?_eq_none.mpr (by
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Write.covers] <;> omega)]
    rw [hnone, he.out k hk, hbb k hk]; rfl
  · rw [hm0 _ hk]; rfl
  · have hfr' : SameOutside (FootW env' S0 (X m)) m mf := fun a ha => hfr a fun h =>
      ha (h.elim (fun hw => .inl (InWritable.of_regions (env' := envE m)
        (hag.regions.symm) rfl hw)) .inr)
    refine so_of_leafW hfr' (fun _ h => h) hm' (by rw [hreg]; rfl)
      (fun r j hr hj hn => ?_) (fun r j hr hj hn => ?_)
    · have hr0 : r ≠ 0 := by rintro rfl; rw [hmem] at hn; simp at hn
      have hcov : Ranges.covers [(0, 8, 40)] r j = false := by simp [Ranges.covers]; omega
      rw [Env.byte0, hag.mem0 r j hcov, hag.base]
      exact e.init r j hr (by rwa [← hag.size])
    · have hr0 : r = 0 := by
        simp only [S0, entryState, regionsR, List.length_cons, List.length_nil] at hr
        rw [hmem] at hn
        rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with h | h | h | h <;>
          subst h <;> simp at hn ⊢
      subst hr0
      rw [he.s0] at hj; rw [he.b0]
      unfold InRange; rw [toNat_add_ofNat (by rw [h96]; omega), h96, h112]; omega

/-- decodeItem's footprint lies in the 112 stack bytes below the entry `sp`, outside the frame
bytes `0 .. 7` and `48 .. 95`. -/
theorem callee_fp {m m1 : Machine} (e : Entry m) (r2 : m1.reg 2 = m.reg 2 - 96)
    (r10 : m1.reg 10 = m.reg 2 - 96 + BitVec.ofNat 64 8) {a : Word}
    (h : InRange (m1.reg 10) 40 a ∨ InRange (m1.reg 2 - 16) 16 a) :
    (m.reg 2).toNat - 112 ≤ a.toNat ∧ a.toNat < (m.reg 2).toNat - 48 ∧
      ¬ ((m.reg 2).toNat - 96 ≤ a.toNat ∧ a.toNat < (m.reg 2).toNat - 88) := by
  have h96 := e.sp96
  obtain ⟨hlo, hhi, -⟩ := e.ram
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  have hout : (m1.reg 10).toNat = (m.reg 2).toNat - 88 := by
    rw [r10, toNat_add_ofNat (by rw [h96]; omega), h96]; omega
  have hfr : (m1.reg 2 - 16).toNat = (m.reg 2).toNat - 112 := by
    rw [r2, BitVec.toNat_sub, h96]; simp; omega
  rcases h with h | h <;> simp only [InRange, hout, hfr] at h <;> omega

/-! ## The leaves of `runW` after the call -/

theorem leavesW {m : Machine} (e : Entry m) : ∀ l ∈ runW_leaves, ∀ env',
    Env.Agree (envE m) env' 64 l.wr → (∀ c ∈ l.leaf.conds, c.eval env' = true) →
    (∀ o ∈ l.leaf.obligs, o.holds env') ∧ l.leaf.S.steps - S0.steps ≤ bound ∧
    ((∀ c ∈ l.calls,
        CallFact zesuImage (X m) (fun _ _ m₂ => CallState m m₂) (envE m) 64 env' l.wr c) →
      ∀ m', Match env' l.leaf.S m' → ExitOk env' l.leaf.exit m' →
        SameOutside (FootW (envE m) S0 (X m)) m m' →
        Reaches zesuImage (bound - (l.leaf.S.steps - S0.steps)) (Post m) m') := by
  intro l hl env' hag hcs
  have hl0 := hl
  have hv : ∀ i : Fin 32, env'.vars i.val = m.reg i := fun i =>
    (hag.vars i.val (by omega)).trans (entryEnv_var m _ i)
  have hv1 : env'.vars 1 = m.reg 1 := hv 1
  have hal : ((Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env').toNat % 4 = 0 := by
    have := e.ra; unfold RetAligned at this
    simpa [Sym.eval, BinOp.eval, F2.notOne, hv1] using this
  have hlen : (inputOf m).length = (wordAt m (m.reg 11 + 8)).toNat := by simp [F2.bytesOf]
  have hfit := e.inputFit
  have hok1 : ∀ l ∈ runW_leaves, (Sym.init 1 8 8).okB 64 l.wr = true := by decide
  have hlenE : (Sym.init 1 8 8).eval env' = wordAt m (m.reg 11 + 8) := by
    rw [Sym.eval_agree hag _ (hok1 l hl)]
    exact len_eval e
  simp only [runW_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · -- status error: decodeItem failed
    refine ⟨by simpa [Oblig.holds] using hal, by decide, fun hf m' hm' hex hfr => ?_⟩
    obtain ⟨mh, he⟩ := envW hl0 hf
    rcases hd : F2.decode (inputOf m) with _ | ⟨b, h, p⟩
    · have hn : nextUint64 (inputOf m) = none := by simp [nextUint64, hd]
      exact ret_leafW e he hv hm' (by decide) rfl hex hfr (res_err he hm' rfl (by decide) hn)
        (sl_kept he hm' rfl (by decide) hn)
    · have hst := (outcome_ok he hd).1
      first | leaf_infeasible | (exfalso; f3_conds)
  · -- a list item
    refine ⟨by simpa [Oblig.holds] using hal, by decide, fun hf m' hm' hex hfr => ?_⟩
    obtain ⟨mh, he⟩ := envW hl0 hf
    rcases hd : F2.decode (inputOf m) with _ | ⟨b, h, p⟩
    · have hst := outcome_err he hd
      first | leaf_infeasible | (exfalso; f3_conds)
    · obtain ⟨hst, hfl, -⟩ := outcome_ok he hd
      cases b
      · first | leaf_infeasible | (exfalso; f3_conds)
      · have hn : nextUint64 (inputOf m) = none := by simp [nextUint64, hd]
        exact ret_leafW e he hv hm' (by decide) rfl hex hfr (res_err he hm' rfl (by decide) hn)
          (sl_kept he hm' rfl (by decide) hn)
  · -- empty payload
    refine ⟨by simpa [Oblig.holds] using hal, by decide, fun hf m' hm' hex hfr => ?_⟩
    obtain ⟨mh, he⟩ := envW hl0 hf
    rcases hd : F2.decode (inputOf m) with _ | ⟨b, h, p⟩
    · have hst := outcome_err he hd
      first | leaf_infeasible | (exfalso; f3_conds)
    · obtain ⟨hst, hfl, hpl, hcons, -⟩ := outcome_ok he hd
      obtain ⟨-, -, -, hp64⟩ := decode_success hd
      have hcw : (Sym.init 0 32 8).eval env' = BitVec.ofNat 64 (h + p) := hcons
      cases b
      · f3_conds
        simp only [Nat.mod_eq_of_lt hp64] at hcs
        have hp0 : p = 0 := by omega
        subst hp0
        have hs := nextUint64_ok hd (by decide)
        refine ret_leafW e he hv hm' (by decide) rfl hex hfr
          (res_ok he hm' rfl (a := .lit 0) (by decide) (by simp [Sym.eval, F2.bigEndian]) hs)
          (sl_ok he hm' rfl (p := .bin .add (.ptr 3 0) (.init 0 32 8))
            (q := .bin .sub (.init 1 8 8) (.init 0 32 8)) (by decide) ?_ ?_ hs)
        · show (Sym.ptr 3 0).eval _ + (Sym.init 0 32 8).eval _ = _
          rw [hcw]; simp [Sym.eval, he.b3]
        · show (Sym.init 1 8 8).eval _ - (Sym.init 0 32 8).eval _ = _
          rw [hcw, hlenE]
      · first | leaf_infeasible | (exfalso; f3_conds)
  · -- loop entry
    refine ⟨by simp, by decide, fun hf m' hm' hex hfr => ?_⟩
    obtain ⟨mh, he⟩ := envW hl0 hf
    rcases hd : F2.decode (inputOf m) with _ | ⟨b, h, p⟩
    · have hst := outcome_err he hd
      first | leaf_infeasible | (exfalso; f3_conds)
    · obtain ⟨hst, hfl, hpl, hcons, hptr⟩ := outcome_ok he hd
      obtain ⟨hh9, hhp, h128, hp64⟩ := decode_success hd
      rw [hlen] at hhp
      have hcw : (Sym.init 0 32 8).eval env' = BitVec.ofNat 64 (h + p) := hcons
      cases b
      · f3_conds
        simp only [Nat.mod_eq_of_lt hp64] at hcs
        have hp8 : p ≤ 8 := by omega
        have hp0 : p ≠ 0 := by omega
        have hhead : ¬ (inputOf m).head? = some 128 := fun h' => hp0 (h128 h')
        have hI : Inv m h p 0 m' := by
          refine ⟨CallState.of_leafW e he hag hm' hfr (by decide) rfl rfl, hex, hd, by omega, hp8,
            by omega, by rw [Nat.mod_eq_of_lt (by omega)] at hhp; exact hhp, ?_, ?_, ?_, ?_⟩
          · rw [← hm'.regs 10]; exact hcw
          · rw [← hm'.regs 11]; show (Sym.lit 0).eval _ = _; simp [Sym.eval, F2.bigEndian]
          · rw [← hm'.regs 12]
            show (Sym.init 0 8 8).eval env' = _
            rw [hptr, if_neg hhead]; rfl
          · rw [← hm'.regs 13]
            show (Sym.init 0 8 8).eval env' + (Sym.init 0 16 8).eval env' = _
            rw [hptr, if_neg hhead, hpl, ofNat_add_ofNat]
        exact (loop_reaches e (p - 1) 0 m' (by omega) hI).mono
          (by show _ ≤ bound - (105 - 0); unfold bound; omega) fun _ h => h
      · first | leaf_infeasible | (exfalso; f3_conds)
  · -- more than 8 payload bytes
    refine ⟨by simpa [Oblig.holds] using hal, by decide, fun hf m' hm' hex hfr => ?_⟩
    obtain ⟨mh, he⟩ := envW hl0 hf
    rcases hd : F2.decode (inputOf m) with _ | ⟨b, h, p⟩
    · have hst := outcome_err he hd
      first | leaf_infeasible | (exfalso; f3_conds)
    · obtain ⟨hst, hfl, hpl, -⟩ := outcome_ok he hd
      obtain ⟨-, -, -, hp64⟩ := decode_success hd
      cases b
      · f3_conds
        simp only [Nat.mod_eq_of_lt hp64] at hcs
        have hn : nextUint64 (inputOf m) = none := by
          have h8 : 8 < p := by omega
          simp [nextUint64, hd]; omega
        exact ret_leafW e he hv hm' (by decide) rfl hex hfr (res_err he hm' rfl (by decide) hn)
          (sl_kept he hm' rfl (by decide) hn)
      · first | leaf_infeasible | (exfalso; f3_conds)

/-! ## The end theorem -/

theorem f3_spec : Spec zesuImage entry bound Pre Post := by
  intro m hpc hpre
  have e := Entry.of_pre hpre
  refine runWith_reaches (X := X m) (Qc := fun _ _ m₂ => CallState m m₂) runW ?_
    (e.wf m ov [⟨1, 0, 8, .ptr 3 0⟩]) e.match0 hpc e.ro (leavesW e)
  -- the call: decodeItem by `F2.f2_spec`
  intro l hl c hc env₁ m₁ k hag1 _ _ hm1 hpc1 hrun hfr1
  obtain ⟨hok, ht, hr, -, hp, hcw, -, hb, hres, hokS, hov⟩ := callsW l hl c hc
  rw [hp] at hag1
  have hm1E : Match (envE m) c.S m₁ := Match.agree hag1.symm hokS hm1
  have hp1 := hrun.preserved
  obtain ⟨k₂, m₂, hk₂, hr₂, hpost, hp2⟩ :=
    Reaches.preserve (F2.f2_spec m₁ (by rw [hpc1, ht]) (pre_call e hm1E hok hp1))
  obtain ⟨hcs2, hpc2⟩ := call_state e hm1E hok hfr1 hp1 hpost hp2
  obtain ⟨-, r2, -, -, r10, -⟩ := call_regs e hm1E hok
  have h96 := e.sp96
  have h112 := e.sp112
  obtain ⟨hlo, hhi, -⟩ := e.ram
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  have hreg : c.S.regions = regionsR := hok.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hb0, hb1, hb2, hb3, hs0, hs1, hs2, hs3⟩ := envE_facts m
  refine ⟨k₂, m₂, (by rw [hb]; exact hk₂), hr₂, ⟨(by rw [hr]; exact hpc2),
    CallRec.keep_of_returns hov hpost.1, (fun v hv => by rw [hres] at hv; cases hv),
    (fun r j hrl hj hcov => ?_), (fun r j _ hj hcov => ?_), (fun a ha => ?_),
    (fun a b _ _ hab => e.ro_of hcs2.2.2.2.2.2.2.2.2.2.2 a b hab)⟩, hcs2⟩
  · -- bytes outside the outcome: decodeItem writes only its outcome and its own frame
    rw [hag1.base]
    show m₂.mem ((envE m).base r + BitVec.ofNat 64 j) = m₁.mem ((envE m).base r + BitVec.ofNat 64 j)
    refine hpost.2.1 _ fun h => ?_
    have fp := callee_fp e r2 r10 h
    rw [hreg] at hrl
    simp only [regionsR, List.length_cons, List.length_nil] at hrl
    rw [hag1.size] at hj
    change j < (envE m).size r at hj
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [hs0] at hj; rw [hb0, toNat_add_ofNat (by rw [h96]; omega), h96] at fp
      rw [hcw] at hcov; simp [Ranges.covers] at hcov
      omega
    · rw [hs1] at hj; rw [hb1] at fp
      have := e.notStack e.d6 e.slFit hj
      unfold InRange at this; rw [h112] at this; omega
    · rw [hs2] at hj; rw [hb2] at fp
      have := e.notStack e.d5 e.resFit hj
      unfold InRange at this; rw [h112] at this; omega
    · rw [hs3] at hj; rw [hb3] at fp
      have := e.notStack e.d3 e.inputFit hj
      unfold InRange at this; rw [h112] at this; omega
  · -- the outcome bytes are present after the call
    rw [hcw] at hcov; simp [Ranges.covers] at hcov
    obtain ⟨⟨rfl, h8⟩, h48⟩ := hcov
    rw [hag1.base]
    show (m₂.mem ((envE m).base 0 + BitVec.ofNat 64 j)).isSome = true
    rw [hb0]
    exact hcs2.2.2.2.2.2.2.2.2.2.1 j (by omega)
  · -- decodeItem's footprint is inside the 112 stack bytes
    refine hpost.2.1 a fun h => ha (.inr ?_)
    have fp := callee_fp e r2 r10 h
    unfold X InRange; rw [h112]; omega

/--
info: 'ZesuExec.Fn.F3.f3_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f3_spec

end ZesuExec.Fn.F3
