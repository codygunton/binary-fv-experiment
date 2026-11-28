import ZesuExec.Fn.MergeInPlace.Win
import ZesuExec.Fn.MergeInPlace.Bytes
import ZesuExec.Vc.Goals

/-!
# `mergeInPlace` copies: cut states, `Common`, and the step lemmas shared by every copy

Cut states (regions in order):

* `S0 c`: the entry; `A` (16 bytes at `a1`), `B` (at `a2`), the frame.
* `SN`: no region (a run that only computes).
* `SP c r extra`: the frame (`sp`, `s0`) and one read-only element at register `r` (a
  search's probe or value, copied into the frame).
* `SC x y`: one read-only byte at each of `x` and `y` (the byte comparison of two frame copies).
* `SR lo hi`: two writable elements at `lo - 15` and `hi - 16` (a swap of the inlined
  `mem.rotate`; the compiled loop addresses an element pair by these biased pointers).
* `SE c`: the frame with the saved registers as `known` words `var (32 + r)` (the epilogue).

`Common c m mh` is what every cut after the prologue keeps; `State c m mh G` adds the items.
The step lemmas turn a leaf's `Match` into these: `step_ro` (no write outside the frame),
`step_copy` (an element copied into the frame), `step_swap` (two elements exchanged),
`entry_step` (the prologue), `epi_post` (the return).
-/

namespace ZesuExec.Fn.MergeInPlace
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Machine ZesuExec.Fn.Rotate

/-- `n` as a word. -/
abbrev w (n : Nat) : Word := BitVec.ofNat 64 n

/-- Register overrides from a list. -/
def ovL (l : List (Nat × Sym)) (i : Nat) : Option Sym := (l.find? (·.1 == i)).map (·.2)

def frameR (fs : Nat) : Region := ⟨some fs, 16, true⟩
def elemR : Region := ⟨some 32, 1, false⟩
def elemW : Region := ⟨some 32, 1, true⟩
def rangeR : Region := ⟨some 16, 1, false⟩
def byteR : Region := ⟨some 1, 1, false⟩

/-! ## Cut states and environments -/

def S0 (c : Cfg) : SState :=
  entryState (ovL [(11, .ptr 0 0), (12, .ptr 1 0), (2, .ptr 2 c.fs)]) [rangeR, rangeR, frameR c.fs] []
def SN : SState := entryState (fun _ => none) [] []
def SP (c : Cfg) (r : Nat) (extra : List (Nat × Sym)) : SState :=
  entryState (ovL ([(2, .ptr 0 0), (8, .ptr 0 c.fs), (r, .ptr 1 0)] ++ extra)) [frameR c.fs, elemR] []
def SC (x y : Nat) : SState := entryState (ovL [(x, .ptr 0 0), (y, .ptr 1 0)]) [byteR, byteR] []
def SR (lo hi : Nat) : SState := entryState (ovL [(lo, .ptr 0 15), (hi, .ptr 1 16)]) [elemW, elemW] []
def knownE (c : Cfg) : List Write := c.saved.map fun s => ⟨0, s.1, 8, .var (32 + s.2)⟩
def SE (c : Cfg) : SState := entryState (ovL [(2, .ptr 0 0)]) [frameR c.fs] (knownE c)

def env0 (c : Cfg) (mh : Machine) : Env :=
  entryEnv mh [(mh.reg 11, 16), (mh.reg 12, 16), (mh.reg 2 - w c.fs, c.fs)]
def envN (mh : Machine) : Env := entryEnv mh []
def envP (c : Cfg) (r : Nat) (mh : Machine) : Env :=
  entryEnv mh [(mh.reg 2, c.fs), (mh.reg (Fin.ofNat 32 r), 32)]
def envC (x y : Nat) (mh : Machine) : Env :=
  entryEnv mh [(mh.reg (Fin.ofNat 32 x), 1), (mh.reg (Fin.ofNat 32 y), 1)]
def envR (lo hi : Nat) (mh : Machine) : Env :=
  entryEnv mh [(mh.reg (Fin.ofNat 32 lo) - w 15, 32), (mh.reg (Fin.ofNat 32 hi) - w 16, 32)]
def envE (c : Cfg) (m mh : Machine) : Env :=
  (entryEnv mh [(frame c m, c.fs)]).setVars 32 fun k => m.reg (Fin.ofNat 32 k)

/-! ## What every cut keeps -/

section
variable (c : Cfg)

/-- `sp` and `s0` as the prologue sets them, `ra` and the kept registers unchanged, the saved
registers in their slots, the frame present, memory changed only in the output range and the
frame, rodata loaded. -/
def Common (m mh : Machine) : Prop :=
  RodataLoaded zesuImage mh ∧ mh.reg 2 = frame c m ∧ mh.reg 8 = m.reg 2 ∧ mh.reg 1 = m.reg 1 ∧
  (∀ i ∈ c.kept, mh.reg (Fin.ofNat 32 i) = m.reg (Fin.ofNat 32 i)) ∧
  (∀ s ∈ c.saved, ∀ t < 8, mh.mem (frame c m + w (s.1 + t)) =
    some (byteOf (m.reg (Fin.ofNat 32 s.2)) t)) ∧
  (∀ j < c.fs, (mh.mem (frame c m + w j)).isSome) ∧
  SameOutside (Writes c m) m mh

/-- The inputs as lists. -/
def X (m : Machine) : List (List Byte) := win (items m (ptr m)) (aS m) (aE m)
def Y (m : Machine) : List (List Byte) := win (items m (ptr m)) (bS m) (bE m)

/-- A round of the outer loop: the prefix `[aS, as)` done, the runs `[as, ae)` and `[ae, bE)`
left (`Inv`). -/
def Round (m : Machine) (G : Nat → Nat → Byte) (as ae : Nat) : Prop :=
  aS m ≤ as ∧ as ≤ ae ∧ ae ≤ bE m ∧
    Inv (c.key m) (X m) (Y m) (win G (aS m) as) (win G as ae) (win G ae (bE m))

/-- After `binaryFirst`: `[ae, mid)` below `A[0]`, `[mid, bE)` not. -/
def MidR (m : Machine) (G : Nat → Nat → Byte) (as ae mid : Nat) : Prop :=
  Round c m G as ae ∧ as < ae ∧ First (c.key m) G (el G as) ae (bE m) mid 0

/-- After the rotation (`as`, `ae` the new `A`): no element of `B` below `A[0]`. -/
def JoinR (m : Machine) (G : Nat → Nat → Byte) (as ae : Nat) : Prop :=
  Round c m G as ae ∧ as < ae ∧ ∀ i, ae ≤ i → i < bE m → ltBy (c.key m) (el G i) (el G as) = false

end

/-! ## Facts from `Pre` -/

section
variable {c : Cfg} {m : Machine}

theorem pre_items (h : Pre c m) : Layout.ramLo ≤ (ptr m).toNat ∧ (ptr m).toNat + 32 * bE m ≤ Layout.ramHi := by
  have := h.2.2.2.2.2.2.2.2.2.2.1
  simp [Machine.writable, Machine.inRange] at this; exact ⟨this.1, this.2⟩

theorem pre_hfit (h : Pre c m) : (ptr m).toNat + 32 * bE m < 2 ^ 64 := by
  have := (pre_items h).2; unfold Layout.ramHi at this; omega

theorem pre_frame (h : Pre c m) : (frame c m).toNat = (m.reg 2).toNat - c.fs ∧
    Layout.ramLo ≤ (frame c m).toNat ∧ (m.reg 2).toNat ≤ Layout.ramHi ∧
    Layout.ramLo + c.fs ≤ (m.reg 2).toNat := by
  obtain ⟨-, ⟨-, hlo, hhi, -⟩, -⟩ := h
  unfold frame
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢
  have : (m.reg 2).toNat < 2 ^ 64 := (m.reg 2).isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem pre_runs (h : Pre c m) : aS m ≤ aE m ∧ aE m = bS m ∧ bS m ≤ bE m :=
  ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1⟩

theorem pre_disj (h : Pre c m) : Disjoint (ptr m, 32 * bE m) (frame c m, c.fs) :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem slice_addr32 {n e o : Nat} {p : Word} (hfit : p.toNat + 32 * n < 2 ^ 64) (he : e < n)
    (ho : o < 32) : (p + w (32 * e + o)).toNat = p.toNat + (32 * e + o) := by
  have := elem_lt (E := 32) he ho
  exact toNat_add_ofNat (by omega)

/-- An element of the output range is written only inside it. -/
theorem in_out (h : Pre c m) {e o : Nat} (he1 : aS m ≤ e) (he : e < bE m) (ho : o < 32) :
    Writes c m (ptr m + w (32 * e + o)) := by
  left
  have hfit := pre_hfit h
  have := elem_lt (E := 32) he ho
  unfold InRange
  rw [slice_addr32 hfit he ho, toNat_add_ofNat (by omega)]
  omega

theorem frame_addr (h : Pre c m) {j : Nat} (hj : j < c.fs) :
    (frame c m + w j).toNat = (frame c m).toNat + j := by
  obtain ⟨hf, hlo, hhi, hsp⟩ := pre_frame h
  exact toNat_add_ofNat (by unfold Layout.ramHi at hhi; omega)

theorem in_frame (h : Pre c m) {j : Nat} (hj : j < c.fs) : Writes c m (frame c m + w j) := by
  right; unfold InRange; rw [frame_addr h hj]; omega

/-- A slice address is not a frame address. -/
theorem slice_ne_frame (h : Pre c m) {e o j : Nat} (he : e < bE m) (ho : o < 32) (hj : j < c.fs) :
    ptr m + w (32 * e + o) ≠ frame c m + w j := by
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [slice_addr32 (pre_hfit h) he ho, frame_addr h hj] at h1
  have hd := pre_disj h
  unfold Disjoint at hd; simp only at hd
  have := elem_lt (E := 32) he ho
  omega

theorem rodata_not_items (h : Pre c m) {a b : Nat} (hb : zesuImage.rodataByte? a = some b) {e o : Nat}
    (he : e < bE m) (ho : o < 32) : BitVec.ofNat 64 a ≠ ptr m + w (32 * e + o) := by
  intro heq
  have := zesu_rodata_range hb
  have hr := (pre_items h).1
  have h1 := congrArg BitVec.toNat heq
  rw [slice_addr32 (pre_hfit h) he ho, BitVec.toNat_ofNat] at h1
  unfold Layout.rodataHi at this; unfold Layout.ramLo at hr
  rw [Nat.mod_eq_of_lt (by omega)] at h1
  omega

theorem rodata_ne_frame (h : Pre c m) {a b : Nat} (hb : zesuImage.rodataByte? a = some b) {j : Nat}
    (hj : j < c.fs) : BitVec.ofNat 64 a ≠ frame c m + w j := by
  intro he
  have := zesu_rodata_range hb
  obtain ⟨hf, hlo, hhi, hsp⟩ := pre_frame h
  have h2 := congrArg BitVec.toNat he
  unfold Layout.rodataHi at this; unfold Layout.ramLo at hlo
  rw [frame_addr h hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
  omega

end

/-! ## Registers a leaf leaves as they were -/

/-- The registers of `l` that `S` leaves as their own variable. -/
def keepsB (S : SState) (l : List Nat) : Bool := l.all fun i => decide (i < 32) && S.reg i == .var i

theorem keeps_of {env : Env} {S : SState} {mh m' : Machine} (hm : Match env S m')
    (hv : ∀ i < 32, env.vars i = mh.reg (Fin.ofNat 32 i)) {l : List Nat}
    (h : keepsB S l = true) : ∀ i ∈ l, m'.reg (Fin.ofNat 32 i) = mh.reg (Fin.ofNat 32 i) := by
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  rw [← hm.regs (Fin.ofNat 32 i)]
  simp only [Fin.ofNat, Nat.mod_eq_of_lt this.1, this.2, Sym.eval_var]
  have := hv i this.1
  simp only [Fin.ofNat, Nat.mod_eq_of_lt (show i < 32 from by omega)] at this
  exact this

theorem entryEnv_vars_lt (mh : Machine) (rs : List (Word × Nat)) :
    ∀ i < 32, (entryEnv mh rs).vars i = mh.reg (Fin.ofNat 32 i) := fun _ _ => rfl

/-- A register of a leaf's machine as its symbolic value, with a literal index. -/
theorem reg_at {env : Env} {S : SState} {m' : Machine} (hm : Match env S m') (r : Nat)
    (hr : r < 32 := by decide) : m'.reg (Fin.ofNat 32 r) = (S.reg r).eval env := by
  rw [← hm.regs (Fin.ofNat 32 r)]; simp [Fin.ofNat, Nat.mod_eq_of_lt hr]

/-! ## `Common` and the items across a leaf -/

/-- The items as a byte function hold `G`. -/
abbrev Items (m mh : Machine) (G : Nat → Nat → Byte) : Prop := SliceIs 32 (bE m) (ptr m) mh G

theorem common_step {c : Cfg} {m mh m' : Machine} (h : Pre c m) (hc : Common c m mh)
    (hso : ∀ a, (∀ j < c.fs, a ≠ frame c m + w j) →
      ¬ (∃ e o, aS m ≤ e ∧ e < bE m ∧ o < 32 ∧ a = ptr m + w (32 * e + o)) → m'.mem a = mh.mem a)
    (hfr : ∀ s ∈ c.saved, ∀ t < 8, m'.mem (frame c m + w (s.1 + t)) = mh.mem (frame c m + w (s.1 + t)))
    (hpres : ∀ j < c.fs, (m'.mem (frame c m + w j)).isSome)
    (hk : ∀ i ∈ [1, 2, 8] ++ c.kept, m'.reg (Fin.ofNat 32 i) = mh.reg (Fin.ofNat 32 i)) :
    Common c m m' := by
  obtain ⟨hro, h2, h8, h1, hkept, hsv, -, hout⟩ := hc
  refine ⟨fun a b hb => ?_, ?_, ?_, ?_, fun i hi => ?_, fun s hs t ht => ?_, hpres,
    fun a ha => ?_⟩
  · rw [hso _ (fun j hj => rodata_ne_frame h hb hj) (fun ⟨e, o, _, he, ho, hq⟩ =>
      rodata_not_items h hb he ho hq)]
    exact hro a b hb
  · rw [← h2]; exact hk 2 (by simp)
  · rw [← h8]; exact hk 8 (by simp)
  · rw [← h1]; exact hk 1 (by simp)
  · rw [← hkept i hi]; exact hk i (by simp [hi])
  · rw [hfr s hs t ht]; exact hsv s hs t ht
  · have hw : ∀ j < c.fs, a ≠ frame c m + w j := fun j hj he => ha (he ▸ in_frame h hj)
    have hi : ¬ (∃ e o, aS m ≤ e ∧ e < bE m ∧ o < 32 ∧ a = ptr m + w (32 * e + o)) :=
      fun ⟨e, o, h1, he, ho, hq⟩ => ha (hq ▸ in_out h h1 he ho)
    rw [hso a hw hi]; exact hout a ha

end ZesuExec.Fn.MergeInPlace
