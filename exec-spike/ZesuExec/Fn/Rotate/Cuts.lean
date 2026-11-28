import ZesuExec.Fn.Rotate.Spec
import ZesuExec.Fn.Stage
import ZesuExec.Vc.Goals

/-!
# `std.mem.rotate` copies: cut states, assertions and leaf lemmas shared by every copy

Every copy has the map's eight cut points in the same roles: the entry, for each of the three
reversals an outer loop head (one element pair per iteration) and an inner loop head (one byte
per iteration), and the epilogue join. Only the registers differ, so the assertions take the
copy's register equations as a list (`RegsAre`) and everything else is stated here once:

* cut states: `S0` (entry; region 0 = the frame), `SO` (outer heads; no region: the run only
  computes addresses), `SI lo hi` (inner heads; regions 0 and 1 = the byte at `lo` and the byte
  at `hi`, so the swap's stores are constant-offset stores), `SE` (epilogue; the frame with the
  saved registers as `known` words `var (32 + r)`).
* assertions: `OuterA`, `InnerA`, `EpiA` over `Pre`, `Common` and `SliceIs … (revAt …)`; the
  phase `Ph` picks the reversed range and the state it starts from (`G0`, `G1`, `G2`).
* leaf lemmas: `inner_step` (one byte swapped: `revAt … k` to `revAt … (k+1)`), `outer_step` (no
  store), `entry_step` (the prologue's stores), `epi_post` (the return is `Post`), and the cut
  lemmas `cutO_ok`, `cutI_ok`, `cutE_ok`, `cut0_ok`.
-/

namespace ZesuExec.Fn.Rotate
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Machine

/-- `n` as a word. -/
abbrev w (n : Nat) : Word := BitVec.ofNat 64 n

/-- Register `r` holds `v`, for every pair `(r, v)`. -/
def RegsAre (mh : Machine) : List (Nat × Word) → Prop
  | [] => True
  | (r, v) :: rest => mh.reg (Fin.ofNat 32 r) = v ∧ RegsAre mh rest

/-! ## Cut states and environments -/

def frameR (fs : Nat) : Region := ⟨some fs, 16, true⟩
def byteR : Region := ⟨some 1, 1, true⟩

def S0 (c : Cfg) : SState :=
  entryState (fun i => if i = 2 then some (.ptr 0 c.fs) else none) [frameR c.fs] []
def SO : SState := entryState (fun _ => none) [] []
def ovI (lo hi : Nat) (i : Nat) : Option Sym :=
  if i = lo then some (.ptr 0 0) else if i = hi then some (.ptr 1 0) else none
def SI (lo hi : Nat) : SState := entryState (ovI lo hi) [byteR, byteR] []
def knownE (c : Cfg) : List Write := c.saved.map fun s => ⟨0, s.1, 8, .var (32 + s.2)⟩
def SE (c : Cfg) : SState :=
  entryState (fun i => if i = 2 then some (.ptr 0 0) else none) [frameR c.fs] (knownE c)

def env0 (c : Cfg) (mh : Machine) : Env := entryEnv mh [(mh.reg 2 - w c.fs, c.fs)]
def envO (mh : Machine) : Env := entryEnv mh []
def envI (lo hi : Nat) (mh : Machine) : Env :=
  entryEnv mh [(mh.reg (Fin.ofNat 32 lo), 1), (mh.reg (Fin.ofNat 32 hi), 1)]
def envE (c : Cfg) (m mh : Machine) : Env :=
  (entryEnv mh [(frame c m, c.fs)]).setVars 32 fun k => m.reg (Fin.ofNat 32 k)

/-! ## The three reversals -/

inductive Ph | one | two | three

/-- First element of the reversed range. -/
def Ph.lo : Ph → Machine → Nat
  | .one, _ => 0
  | .two, m => amt m
  | .three, _ => 0

/-- Length of the reversed range. -/
def Ph.L : Ph → Machine → Nat
  | .one, m => amt m
  | .two, m => len m - amt m
  | .three, m => len m

/-- The slice when the reversal starts. -/
def Ph.G (c : Cfg) : Ph → Machine → Nat → Nat → Byte
  | .one => G0 c
  | .two => G1 c
  | .three => G2 c

/-! ## Assertions -/

section
variable (c : Cfg)

/-- An outer loop head of reversal `φ` before swap `i`. -/
def OuterA (φ : Ph) (pc : Nat) (eqs : Machine → Nat → List (Nat × Word)) (m mh : Machine) : Prop :=
  Pre c m ∧ mh.pc.toNat = pc ∧ Common c m mh ∧ ∃ i, 2 * i + 2 ≤ φ.L m ∧
    SliceIs c.E (len m) (ptr m) mh (revAt (φ.lo m) (φ.L m) i 0 (φ.G c m)) ∧ RegsAre mh (eqs m i)

/-- An inner loop head of reversal `φ` before byte `k` of swap `i`: `lo` and `hi` point at that
byte of elements `lo + i` and `lo + L - 1 - i`. -/
def InnerA (φ : Ph) (pc lo hi : Nat) (eqs : Machine → Nat → Nat → List (Nat × Word))
    (m mh : Machine) : Prop :=
  Pre c m ∧ mh.pc.toNat = pc ∧ Common c m mh ∧ ∃ i k, 2 * i + 2 ≤ φ.L m ∧ k < c.E ∧
    SliceIs c.E (len m) (ptr m) mh (revAt (φ.lo m) (φ.L m) i k (φ.G c m)) ∧
    mh.reg (Fin.ofNat 32 lo) = ptr m + w (c.E * (φ.lo m + i) + k) ∧
    mh.reg (Fin.ofNat 32 hi) = ptr m + w (c.E * (φ.lo m + (φ.L m - 1 - i)) + k) ∧
    RegsAre mh (eqs m i k)

/-- The epilogue: the three reversals done. -/
def EpiA (pc : Nat) (m mh : Machine) : Prop :=
  Pre c m ∧ mh.pc.toNat = pc ∧ Common c m mh ∧ SliceIs c.E (len m) (ptr m) mh (G3 c m)

end

/-! ## Facts from `Pre` -/

section
variable {c : Cfg} {m : Machine}

theorem pre_ram (h : Pre c m) : Layout.ramLo ≤ (ptr m).toNat ∧
    (ptr m).toNat + c.E * len m ≤ Layout.ramHi := by
  have := h.2.2.2.2.1
  simp [Machine.writable, Machine.inRange] at this; exact ⟨this.1, this.2⟩

theorem pre_hfit (h : Pre c m) : (ptr m).toNat + c.E * len m < 2 ^ 64 := by
  have := (pre_ram h).2; unfold Layout.ramHi at this; omega

theorem Ph.lo_L_le (φ : Ph) (h : Pre c m) : φ.lo m + φ.L m ≤ len m := by
  have := h.2.2.2.1
  cases φ <;> simp only [Ph.lo, Ph.L] <;> omega

theorem slice_addr {E n e o : Nat} {p : Word} (hfit : p.toNat + E * n < 2 ^ 64) (he : e < n)
    (ho : o < E) : (p + w (E * e + o)).toNat = p.toNat + (E * e + o) := by
  have := elem_lt he ho
  exact toNat_add_ofNat (by omega)

/-- A slice address is in the slice. -/
theorem in_slice (h : Pre c m) {e o : Nat} (he : e < len m) (ho : o < c.E) :
    InRange (ptr m) (c.E * len m) (ptr m + w (c.E * e + o)) := by
  have := elem_lt he ho
  unfold InRange; rw [slice_addr (pre_hfit h) he ho]; omega

/-- The slice lies in RAM, rodata below it. -/
theorem rodata_not_slice (h : Pre c m) {a b : Nat} (hb : zesuImage.rodataByte? a = some b) :
    ¬ InRange (ptr m) (c.E * len m) (BitVec.ofNat 64 a) := by
  have := zesu_rodata_range hb
  have := (pre_ram h).1
  unfold InRange Layout.rodataHi at *; unfold Layout.ramLo at *
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem frame_not_slice (h : Pre c m) {t : Nat} (ht : t < c.fs) :
    ¬ InRange (ptr m) (c.E * len m) (frame c m + w t) := by
  obtain ⟨hf, hlo, hhi, hsp⟩ := pre_frame h
  have hd := h.2.2.2.2.2.2
  unfold Disjoint at hd; simp only at hd
  unfold InRange
  rw [toNat_add_ofNat (b := frame c m) (j := t) (by unfold Layout.ramHi at hhi; omega)]
  omega

end

/-! ## `Common` across a step that writes only in the slice -/

theorem common_step {c : Cfg} {m mh m' : Machine} (h : Pre c m) (hc : Common c m mh)
    (hso : SameOutside (InRange (ptr m) (c.E * len m)) mh m')
    (hk : ∀ i ∈ [1, 2, 8] ++ c.kept, m'.reg (Fin.ofNat 32 i) = mh.reg (Fin.ofNat 32 i)) :
    Common c m m' := by
  obtain ⟨hro, h2, h8, h1, hkept, hsv, hpres, hout⟩ := hc
  refine ⟨fun a b hb => ?_, ?_, ?_, ?_, fun i hi => ?_, fun s hs t ht => ?_, fun j hj => ?_,
    fun a ha => ?_⟩
  · rw [hso _ (rodata_not_slice h hb)]; exact hro a b hb
  · rw [← h2]; exact hk 2 (by simp)
  · rw [← h8]; exact hk 8 (by simp)
  · rw [← h1]; exact hk 1 (by simp)
  · rw [← hkept i hi]; exact hk i (by simp [hi])
  · rw [← hsv s hs t ht]
    exact hso _ (frame_not_slice h (by have := c.saved_le s hs; omega))
  · rw [hso _ (frame_not_slice h hj)]; exact hpres j hj
  · rw [hso _ (fun hs => ha (.inl hs))]; exact hout a ha

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

theorem envE_vars (c : Cfg) (m mh : Machine) :
    ∀ i < 32, (envE c m mh).vars i = mh.reg (Fin.ofNat 32 i) := by
  intro i hi; simp [envE, Env.setVars, show ¬ 32 ≤ i by omega, entryEnv]

/-! ## Writable addresses of the cut states -/

theorem size_one_entry {mh : Machine} {rs : List (Word × Nat)} {r j : Nat}
    (hj : j < (entryEnv mh rs).size r) (h1 : ∀ p ∈ rs, p.2 = 1) : j = 0 := by
  simp only [Env.size, entryEnv, List.getD_eq_getElem?_getD] at hj
  cases hr : rs[r]? with
  | none => rw [hr] at hj; simp at hj
  | some p =>
    rw [hr] at hj
    have := h1 p (List.mem_of_getElem? hr)
    simp at hj; omega

theorem inW_I {lo hi : Nat} {mh : Machine} {a : Word} (h : InWritable (envI lo hi mh) (SI lo hi) a) :
    a = mh.reg (Fin.ofNat 32 lo) ∨ a = mh.reg (Fin.ofNat 32 hi) := by
  obtain ⟨r, R, j, hR, -, hj, rfl⟩ := h
  have hj0 : j = 0 := size_one_entry hj (by simp)
  subst hj0
  have hr : r < 2 := by
    rcases Nat.lt_or_ge r 2 with hc | hc
    · exact hc
    · simp [SI, entryState, List.getElem?_eq_none (show [byteR, byteR].length ≤ r by simp; omega)] at hR
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · left; simp [envI, entryEnv, Env.base]
  · right; simp [envI, entryEnv, Env.base]

theorem not_inW_O {mh : Machine} {a : Word} : ¬ InWritable (envO mh) SO a := by
  rintro ⟨r, R, j, hR, -⟩
  simp [SO, entryState] at hR

theorem inW_E {c : Cfg} {m mh : Machine} {a : Word} (h : InWritable (envE c m mh) (SE c) a) :
    ∃ j < c.fs, a = frame c m + w j := by
  obtain ⟨r, R, j, hR, -, hj, rfl⟩ := h
  have hr : r = 0 := by
    rcases Nat.lt_or_ge r 1 with hc | hc
    · omega
    · simp [SE, entryState, List.getElem?_eq_none (show [frameR c.fs].length ≤ r by simp; omega)] at hR
  subst hr
  refine ⟨j, ?_, ?_⟩
  · simpa [envE, Env.setVars, entryEnv, Env.size] using hj
  · simp [envE, Env.setVars, entryEnv, Env.base]

theorem inW_0 {c : Cfg} {mh : Machine} {a : Word} (h : InWritable (env0 c mh) (S0 c) a) :
    ∃ j < c.fs, a = mh.reg 2 - w c.fs + w j := by
  obtain ⟨r, R, j, hR, -, hj, rfl⟩ := h
  have hr : r = 0 := by
    rcases Nat.lt_or_ge r 1 with hc | hc
    · omega
    · simp [S0, entryState, List.getElem?_eq_none (show [frameR c.fs].length ≤ r by simp; omega)] at hR
  subst hr
  refine ⟨j, ?_, ?_⟩
  · simpa [env0, entryEnv, Env.size] using hj
  · simp [env0, entryEnv, Env.base]

/-! ## The byte swap of an inner loop -/

/-- The swap's two stores: the byte at `lo` gets the byte at `hi` and back. -/
def swapW : List Write := [⟨1, 0, 1, .init 0 0 1⟩, ⟨0, 0, 1, .init 1 0 1⟩]

theorem swap_mem {lo hi : Nat} {mh m' : Machine} {lS : SState} (hm : Match (envI lo hi mh) lS m')
    (hr : lS.regions.length = 2) (hw : lS.mem = swapW) :
    m'.mem (mh.reg (Fin.ofNat 32 lo)) = some ((mh.mem (mh.reg (Fin.ofNat 32 hi))).getD 0) ∧
    m'.mem (mh.reg (Fin.ofNat 32 hi)) = some ((mh.mem (mh.reg (Fin.ofNat 32 lo))).getD 0) := by
  have h0 := hm.mem 0 0 (by omega) (by simp [envI, entryEnv, Env.size])
  have h1 := hm.mem 1 0 (by omega) (by simp [envI, entryEnv, Env.size])
  rw [hw] at h0 h1
  have hb : ∀ b : Byte, byteOf (ofBytesLE [b]) 0 = b := fun b => byteOf_ofBytesLE [b] (by simp) 0 (by simp)
  simp [memByte, swapW, Write.covers, Sym.eval, byteList, hb, envI, entryEnv, Env.base, Env.byte0] at h0 h1
  exact ⟨h0, h1⟩

/-- One byte of swap `i` of reversal `φ`: the slice moves to `revAt … (k+1)`, `Common` holds. -/
theorem inner_step {c : Cfg} {φ : Ph} {lo hi : Nat} {m mh m' : Machine} {lS : SState} {i k : Nat}
    (h : Pre c m) (hc : Common c m mh) (hi2 : 2 * i + 2 ≤ φ.L m) (hk : k < c.E)
    (hs : SliceIs c.E (len m) (ptr m) mh (revAt (φ.lo m) (φ.L m) i k (φ.G c m)))
    (hlo : mh.reg (Fin.ofNat 32 lo) = ptr m + w (c.E * (φ.lo m + i) + k))
    (hhi : mh.reg (Fin.ofNat 32 hi) = ptr m + w (c.E * (φ.lo m + (φ.L m - 1 - i)) + k))
    (hm : Match (envI lo hi mh) lS m') (hr : lS.regions.length = 2) (hw : lS.mem = swapW)
    (hso : SameOutside (InWritable (envI lo hi mh) (SI lo hi)) mh m')
    (hkeep : keepsB lS ([1, 2, 8] ++ c.kept) = true) :
    Common c m m' ∧ SliceIs c.E (len m) (ptr m) m' (revAt (φ.lo m) (φ.L m) i (k + 1) (φ.G c m)) := by
  have hfit := pre_hfit h
  have hL := φ.lo_L_le h
  have hrest : ∀ a, a ≠ ptr m + w (c.E * (φ.lo m + i) + k) →
      a ≠ ptr m + w (c.E * (φ.lo m + (φ.L m - 1 - i)) + k) → m'.mem a = mh.mem a := by
    intro a h1 h2
    apply hso
    intro hw'
    rcases inW_I hw' with rfl | rfl
    · exact h1 hlo
    · exact h2 hhi
  obtain ⟨hs1, hs2⟩ := swap_mem hm hr hw
  rw [hlo, hhi] at hs1 hs2
  have e1 := hs (φ.lo m + i) (by omega) k hk
  have e2 := hs (φ.lo m + (φ.L m - 1 - i)) (by omega) k hk
  refine ⟨common_step h hc (fun a ha => ?_) (keeps_of hm (entryEnv_vars_lt _ _) hkeep), ?_⟩
  · apply hrest
    · rintro rfl; exact ha (in_slice h (by omega) hk)
    · rintro rfl; exact ha (in_slice h (by omega) hk)
  · refine slice_revAt_succ hfit hs hL hi2 hk ?_ ?_ hrest
    · rw [hs1, e2]; rfl
    · rw [hs2, e1]; rfl

/-- A run with no region: memory unchanged. -/
theorem outer_step {c : Cfg} {m mh m' : Machine} {lS : SState} {G : Nat → Nat → Byte}
    (h : Pre c m) (hc : Common c m mh) (hs : SliceIs c.E (len m) (ptr m) mh G)
    (hm : Match (envO mh) lS m') (hso : SameOutside (InWritable (envO mh) SO) mh m')
    (hkeep : keepsB lS ([1, 2, 8] ++ c.kept) = true) :
    Common c m m' ∧ SliceIs c.E (len m) (ptr m) m' G :=
  ⟨common_step h hc (fun a _ => hso a not_inW_O) (keeps_of hm (entryEnv_vars_lt _ _) hkeep),
    hs.keep fun _ _ _ _ => hso _ not_inW_O⟩

/-! ## Reversal ends -/

theorem slice_next {E n lo L i : Nat} {p : Word} {mh : Machine} {G : Nat → Nat → Byte}
    (hs : SliceIs E n p mh (revAt lo L i E G)) (hi : 2 * i + 2 ≤ L) :
    SliceIs E n p mh (revAt lo L (i + 1) 0 G) :=
  hs.congr fun _ _ _ ho => revAt_next G hi ho

theorem slice_end {E n lo L i : Nat} {p : Word} {mh : Machine} {G : Nat → Nat → Byte}
    (hs : SliceIs E n p mh (revAt lo L i E G)) (hi : 2 * i + 2 ≤ L) (he : i + 1 = L / 2) :
    SliceIs E n p mh (rev lo L G) := by
  have := slice_next hs hi
  rw [he, revAt_full] at this; exact this

/-! ## Frame addresses -/

section
variable {c : Cfg} {m : Machine}

theorem frame_addr (h : Pre c m) {j : Nat} (hj : j < c.fs) :
    (frame c m + w j).toNat = (frame c m).toNat + j := by
  obtain ⟨hf, hlo, hhi, hsp⟩ := pre_frame h
  exact toNat_add_ofNat (by unfold Layout.ramHi at hhi; omega)

theorem in_frame (h : Pre c m) {j : Nat} (hj : j < c.fs) : InRange (frame c m) c.fs (frame c m + w j) := by
  unfold InRange; rw [frame_addr h hj]; omega

theorem slice_ne_frame (h : Pre c m) {e o j : Nat} (he : e < len m) (ho : o < c.E) (hj : j < c.fs) :
    ptr m + w (c.E * e + o) ≠ frame c m + w j :=
  fun heq => frame_not_slice h hj (heq ▸ in_slice h he ho)

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

/-! ## The prologue and the epilogue -/

theorem find_slot (v : Nat × Nat → Sym) :
    ∀ (L : List (Nat × Nat)), L.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1) →
    ∀ s ∈ L, ∀ t < 8, (L.map fun s => (⟨0, s.1, 8, v s⟩ : Write)).find? (·.covers 0 (s.1 + t)) =
      some ⟨0, s.1, 8, v s⟩
  | [], _, s, hs, _, _ => absurd hs List.not_mem_nil
  | s' :: L, hd, s, hs, t, ht => by
    rw [List.map_cons, List.find?_cons]
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hd
    rcases List.mem_cons.mp hs with rfl | hs
    · have : (⟨0, s.1, 8, v s⟩ : Write).covers 0 (s.1 + t) = true := by
        simp [Write.covers]; omega
      rw [this]
    · have hc : (⟨0, s'.1, 8, v s'⟩ : Write).covers 0 (s.1 + t) = false := by
        have := h1 s hs; simp [Write.covers]; omega
      rw [hc]; exact find_slot v L h2 s hs t ht

theorem memByte_slot (env : Env) (v : Nat × Nat → Sym) (L : List (Nat × Nat))
    (hd : L.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1)) {s : Nat × Nat} (hs : s ∈ L)
    {t : Nat} (ht : t < 8) :
    memByte env (L.map fun s => (⟨0, s.1, 8, v s⟩ : Write)) 0 (s.1 + t) = byteOf ((v s).eval env) t := by
  unfold memByte; rw [find_slot v L hd s hs t ht]; simp

theorem s0_eval (c : Cfg) (b : Word) : b - w c.fs + BitVec.ofInt 64 (c.fs : Int) = b := by
  rw [BitVec.ofInt_natCast]; exact BitVec.sub_add_cancel b _

/-- The entry run: the prologue stores the saved registers; the slice is the entry's. -/
theorem entry_step {c : Cfg} {m m' : Machine} {lS : SState} (h : Pre c m)
    (hm : Match (env0 c m) lS m') (hso : SameOutside (InWritable (env0 c m) (S0 c)) m m')
    (hw : lS.mem = c.saved.map fun s => (⟨0, s.1, 8, .var s.2⟩ : Write))
    (hr : lS.regions.length = 1) (hsp : lS.reg 2 = .ptr 0 0) (hs0 : lS.reg 8 = .ptr 0 c.fs)
    (hkeep : keepsB lS (1 :: c.kept) = true) :
    Common c m m' ∧ SliceIs c.E (len m) (ptr m) m' (G0 c m) := by
  have hfr : ∀ a, InWritable (env0 c m) (S0 c) a → ∃ j < c.fs, a = frame c m + w j :=
    fun a ha => inW_0 ha
  have hk := keeps_of hm (entryEnv_vars_lt _ _) hkeep
  have hb0 : (env0 c m).base 0 = frame c m := by simp [env0, entryEnv, Env.base, frame]
  have hmem : ∀ j < c.fs, m'.mem (frame c m + w j) = some (memByte (env0 c m) lS.mem 0 j) := by
    intro j hj
    rw [← hb0]; exact hm.mem 0 j (by omega) (by simpa [env0, entryEnv, Env.size] using hj)
  refine ⟨⟨fun a b hb => ?_, ?_, ?_, ?_, fun i hi => ?_, fun s hs t ht => ?_, fun j hj => ?_,
    fun a ha => ?_⟩, ?_⟩
  · rw [hso _ (fun hw => by obtain ⟨j, hj, he⟩ := hfr _ hw; exact rodata_ne_frame h hb hj he)]
    exact h.1 a b hb
  · rw [← hm.regs 2]; show Sym.eval _ (lS.reg 2) = _
    rw [hsp]; simp [Sym.eval, env0, entryEnv, Env.base, frame]
  · rw [← hm.regs 8]; show Sym.eval _ (lS.reg 8) = _
    rw [hs0]
    simp only [Sym.eval_ptr, env0, entryEnv, Env.base, List.getD_cons_zero]
    exact s0_eval c _
  · exact hk 1 (by simp)
  · exact hk i (by simp [hi])
  · have hle := c.saved_le s hs
    rw [hmem _ (by omega), hw, memByte_slot _ _ _ c.saved_disj hs ht]
    rfl
  · rw [hmem j hj]; rfl
  · apply hso
    intro hw'
    obtain ⟨j, hj, rfl⟩ := hfr _ hw'
    exact ha (.inr (in_frame h hj))
  · refine (slice_bytesOf h.2.2.2.2.2.1).keep fun e he o ho => hso _ fun hw' => ?_
    obtain ⟨j, hj, he'⟩ := hfr _ hw'
    exact slice_ne_frame h he ho hj he'

/-- `Returns` registers of the epilogue's leaf: `sp` back, saved registers reloaded, kept ones
untouched. -/
def retRegsB (c : Cfg) (lS : SState) : Bool :=
  lS.reg 2 == .ptr 0 c.fs && calleeSaved.all fun i =>
    i.val == 2 || (c.saved.any (·.2 == i.val) && lS.reg i.val == .var (32 + i.val)) ||
      (c.kept.contains i.val && lS.reg i.val == .var i.val)

/-- The epilogue's return is `Post`. -/
theorem epi_post {c : Cfg} {m mh m' : Machine} {lS : SState} (h : Pre c m) (hc : Common c m mh)
    (hs : SliceIs c.E (len m) (ptr m) mh (G3 c m)) (hm : Match (envE c m mh) lS m')
    (hso : SameOutside (InWritable (envE c m mh) (SE c)) mh m')
    (hpc : m'.pc = (Sym.bin .and (.var 33) (.lit 18446744073709551614)).eval (envE c m mh))
    (hregs : retRegsB c lS = true) : Post c m m' := by
  obtain ⟨-, h2, -, -, hkept, -, -, hout⟩ := hc
  have hv : ∀ i, 32 ≤ i → (envE c m mh).vars i = m.reg (Fin.ofNat 32 (i - 32)) := by
    intro i hi; simp [envE, Env.setVars, hi]
  simp only [retRegsB, Bool.and_eq_true, beq_iff_eq] at hregs
  obtain ⟨hsp, hcs⟩ := hregs
  refine ⟨⟨?_, fun i hi => ?_⟩, fun a ha => ?_, post_slice h (hs.keep fun e he o ho => ?_)⟩
  · rw [hpc]; simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
    rw [hv 33 (by omega)]; rfl
  · have := List.all_eq_true.mp hcs i hi
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
      List.contains_iff_mem] at this
    rw [← hm.regs i]
    have e : Fin.ofNat 32 i.val = i := Fin.ext (by simp [Fin.ofNat])
    rcases this with (h2' | ⟨-, he⟩) | ⟨hk, he⟩
    · have : i = 2 := Fin.ext h2'
      subst this
      show Sym.eval _ (lS.reg 2) = _
      rw [hsp]
      simp only [Sym.eval_ptr, envE, Env.setVars, entryEnv, Env.base, List.getD_cons_zero]
      unfold frame; rw [BitVec.ofInt_natCast]; exact BitVec.sub_add_cancel _ _
    · rw [he, Sym.eval_var, hv _ (by omega), show 32 + i.val - 32 = i.val by omega, e]
    · rw [he, Sym.eval_var, envE_vars c m mh _ i.isLt, e]
      have := hkept _ hk
      rw [e] at this
      exact this
  · rw [hso a fun hw => by
      obtain ⟨j, hj, rfl⟩ := inW_E hw
      exact ha (.inr (in_frame h hj))]
    exact hout a ha
  · apply hso
    intro hw
    obtain ⟨j, hj, he'⟩ := inW_E hw
    exact slice_ne_frame h he ho hj he'

/-! ## Cut points -/

theorem cut0_facts {c : Cfg} {m : Machine} (h : Pre c m) :
    Env.WF (env0 c m) (S0 c) ∧ Match (env0 c m) (S0 c) m := by
  obtain ⟨hf, hlo, hhi, hsp⟩ := pre_frame h
  have hal := h.2.1.1
  refine ⟨entry_wf (m := m) [((m.reg 2 - w c.fs, c.fs), frameR c.fs)] ?_ (by simp), ?_⟩
  · simp only [List.mem_singleton]
    rintro p rfl
    refine ⟨by simp [frameR], ?_, ?_⟩
    · show (frame c m).toNat % 16 = 0
      have := c.fs_align; omega
    · show Machine.writable (frame c m).toNat c.fs = true
      simp [Machine.writable, Machine.inRange]; unfold Layout.ramLo Layout.ramHi at *; omega
  · refine entry_match (fun i hi s hs => ?_) (fun r j hr hj => ?_) (by simp)
    · by_cases h2 : i.val = 2
      · simp only [h2, if_true, Option.some.injEq] at hs
        subst hs
        have : i = 2 := Fin.ext h2
        subst this
        simp only [Sym.eval_ptr, entryEnv, Env.base, List.getD_cons_zero]
        exact s0_eval c _
      · simp [h2] at hs
    · simp at hr; subst hr
      have hj' : j < c.fs := by simpa [entryEnv, Env.size] using hj
      simpa [entryEnv, Env.base] using h.2.1.2.2.2 j hj'

theorem cutO_facts {mh : Machine} : Env.WF (envO mh) SO ∧ Match (envO mh) SO mh :=
  ⟨entry_wf (m := mh) [] (by simp) (by simp),
    entry_match (fun _ _ s hs => by simp at hs) (fun r j hr _ => by simp at hr) (by simp)⟩

theorem cutI_facts {c : Cfg} {φ : Ph} {lo hi : Nat} {m mh : Machine} {i k : Nat} {G : Nat → Nat → Byte}
    (h : Pre c m) (hlo32 : lo < 32) (hhi32 : hi < 32)
    (hi2 : 2 * i + 2 ≤ φ.L m) (hk : k < c.E)
    (hs : SliceIs c.E (len m) (ptr m) mh G)
    (hlo : mh.reg (Fin.ofNat 32 lo) = ptr m + w (c.E * (φ.lo m + i) + k))
    (hhi : mh.reg (Fin.ofNat 32 hi) = ptr m + w (c.E * (φ.lo m + (φ.L m - 1 - i)) + k)) :
    Env.WF (envI lo hi mh) (SI lo hi) ∧ Match (envI lo hi mh) (SI lo hi) mh := by
  have hL := φ.lo_L_le h
  have hfit := pre_hfit h
  have hram := pre_ram h
  have a1 := slice_addr hfit (show φ.lo m + i < len m by omega) hk
  have a2 := slice_addr hfit (show φ.lo m + (φ.L m - 1 - i) < len m by omega) hk
  have l1 := elem_lt (show φ.lo m + i < len m by omega) hk
  have l2 := elem_lt (show φ.lo m + (φ.L m - 1 - i) < len m by omega) hk
  have hlt : c.E * (φ.lo m + i) + k + 1 ≤ c.E * (φ.lo m + (φ.L m - 1 - i)) + k := by
    have := Nat.mul_le_mul_left c.E (show φ.lo m + i + 1 ≤ φ.lo m + (φ.L m - 1 - i) by omega)
    rw [Nat.mul_succ] at this; omega
  refine ⟨entry_wf (m := mh) [((mh.reg (Fin.ofNat 32 lo), 1), byteR),
      ((mh.reg (Fin.ofNat 32 hi), 1), byteR)] ?_ ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl)
    · refine ⟨by simp [byteR], by simp [byteR, Nat.mod_one], ?_⟩
      simp only [byteR, if_true]
      rw [hlo]; simp only [Machine.writable, Machine.inRange, a1, Bool.and_eq_true, decide_eq_true_eq]
      unfold Layout.ramLo Layout.ramHi at *; omega
    · refine ⟨by simp [byteR], by simp [byteR, Nat.mod_one], ?_⟩
      simp only [byteR, if_true]
      rw [hhi]; simp only [Machine.writable, Machine.inRange, a2, Bool.and_eq_true, decide_eq_true_eq]
      unfold Layout.ramLo Layout.ramHi at *; omega
  · simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton,
      forall_eq, List.not_mem_nil, List.Pairwise.nil, and_true, Disjoint]
    rw [hlo, hhi, a1, a2]
    refine ⟨.inl ?_, fun _ h => h.elim⟩
    omega
  · refine entry_match (fun r hr s hs => ?_) (fun r j hr hj => ?_) (by simp)
    · simp only [ovI] at hs
      by_cases e1 : r.val = lo
      · rw [if_pos e1, Option.some.injEq] at hs; subst hs
        have : r = Fin.ofNat 32 lo := by apply Fin.ext; simp [Fin.ofNat]; omega
        subst this
        simp [Sym.eval, entryEnv, Env.base]
      · by_cases e2 : r.val = hi
        · rw [if_neg e1, if_pos e2, Option.some.injEq] at hs; subst hs
          have : r = Fin.ofNat 32 hi := by apply Fin.ext; simp [Fin.ofNat]; omega
          subst this
          simp [Sym.eval, entryEnv, Env.base]
        · rw [if_neg e1, if_neg e2] at hs; simp at hs
    · have hj0 : j = 0 := size_one_entry hj (by simp)
      subst hj0
      have hr2 : r = 0 ∨ r = 1 := by simp at hr; omega
      rcases hr2 with rfl | rfl
      · have := hs _ (show φ.lo m + i < len m by omega) k hk
        simp only [entryEnv, Env.base, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        rw [hlo]; simp [this]
      · have := hs _ (show φ.lo m + (φ.L m - 1 - i) < len m by omega) k hk
        simp only [entryEnv, Env.base, List.getD_cons_succ, List.getD_cons_zero, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero]
        rw [hhi]; simp [this]

theorem cutE_facts {c : Cfg} {m mh : Machine} (h : Pre c m) (hc : Common c m mh) :
    Env.WF (envE c m mh) (SE c) ∧ Match (envE c m mh) (SE c) mh := by
  obtain ⟨hf, hlo, hhi, hsp⟩ := pre_frame h
  obtain ⟨-, h2, -, -, -, hsv, hpres, -⟩ := hc
  have hal := h.2.1.1
  have hwf := entry_wf (m := mh) (ov := fun i => if i = 2 then some (.ptr 0 0) else none)
    (ks := knownE c) [((frame c m, c.fs), frameR c.fs)] (by
      simp only [List.mem_singleton]
      rintro p rfl
      refine ⟨by simp [frameR], ?_, ?_⟩
      · show (frame c m).toNat % 16 = 0
        have := c.fs_align; omega
      · show Machine.writable (frame c m).toNat c.fs = true
        simp [Machine.writable, Machine.inRange]; unfold Layout.ramLo Layout.ramHi at *; omega)
    (by simp)
  refine ⟨⟨hwf.len, hwf.disjoint, hwf.size, hwf.align, hwf.range⟩, ⟨by simp [SE, entryState],
    fun i => ?_, fun r j hr hj => ?_, fun k hk t ht => ?_⟩⟩
  · rw [show (SE c).reg i.val = if i.val = 0 then .lit 0 else
        ((fun i => if i = 2 then some (Sym.ptr 0 0) else none) i.val).getD (.var i.val) from
      entryState_reg _ _ _ i]
    by_cases h0 : i.val = 0
    · simp [h0, Sym.eval, Machine.reg]
    · by_cases e2 : i.val = 2
      · have : i = 2 := Fin.ext e2
        subst this
        simp [Sym.eval, envE, Env.setVars, entryEnv, Env.base, h2]
      · simp only [h0, e2, if_false, Option.getD_none, Sym.eval_var]
        rw [envE_vars c m mh _ i.isLt]
        simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
  · simp [SE, entryState] at hr; subst hr
    have hj' : j < c.fs := by simpa [envE, Env.setVars, entryEnv, Env.size] using hj
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hpres j hj')
    simp [envE, Env.setVars, entryEnv, Env.base, memByte, SE, entryState, Env.byte0, hb]
  · simp only [SE, entryState, knownE, List.mem_map] at hk
    obtain ⟨s, hs, rfl⟩ := hk
    have := hsv s hs t ht
    have hr := c.saved_reg s hs
    simp [envE, Env.setVars, entryEnv, Env.byte0, Sym.eval, this]

/-- A register of a leaf's machine as its symbolic value, with a literal index. -/
theorem reg_at {env : Env} {S : SState} {m' : Machine} (hm : Match env S m') (r : Nat)
    (hr : r < 32 := by decide) : m'.reg (Fin.ofNat 32 r) = (S.reg r).eval env := by
  rw [← hm.regs (Fin.ofNat 32 r)]; simp [Fin.ofNat, Nat.mod_eq_of_lt hr]

/-! ## Budgets read off the machine -/

/-- The loop counter in register `r`. -/
def ix (mh : Machine) (r : Nat) : Nat := (mh.reg (Fin.ofNat 32 r)).toNat
/-- The byte index: register `lo` minus the element base in register `base`. -/
def kx (mh : Machine) (lo base : Nat) : Nat :=
  (mh.reg (Fin.ofNat 32 lo) - mh.reg (Fin.ofNat 32 base)).toNat

theorem RegsAre.get {mh : Machine} : ∀ {L : List (Nat × Word)}, RegsAre mh L →
    ∀ {r : Nat} {v : Word}, (r, v) ∈ L → mh.reg (Fin.ofNat 32 r) = v
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (r', v') :: L, ⟨h1, h2⟩, r, v, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h; exact h1
    · exact RegsAre.get h2 h

theorem ix_eq {mh : Machine} {r i : Nat} (h : mh.reg (Fin.ofNat 32 r) = w i) (hi : i < 2 ^ 64) :
    ix mh r = i := by
  unfold ix; rw [h]; simp [Nat.mod_eq_of_lt hi]

theorem kx_eq {mh : Machine} {lo base : Nat} {p : Word} {a b : Nat}
    (hl : mh.reg (Fin.ofNat 32 lo) = p + w a) (hb : mh.reg (Fin.ofNat 32 base) = p + w b)
    (hab : b ≤ a) (ha : p.toNat + a < 2 ^ 64) : kx mh lo base = a - b := by
  unfold kx; rw [hl, hb]
  rw [BitVec.toNat_sub, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
  omega

theorem toNat_sub_ptr {p : Word} {a b : Nat} (hab : b ≤ a) (ha : p.toNat + a < 2 ^ 64) :
    (p + w a - (p + w b)).toNat = a - b := by
  have h1 : (p + w a).toNat = p.toNat + a := toNat_add_ofNat ha
  have h2 : (p + w b).toNat = p.toNat + b := toNat_add_ofNat (by omega)
  rw [BitVec.toNat_sub, h1, h2]; omega

/-- `reg_at` with the bound as a hypothesis (for `simp` with a discharger). -/
theorem reg_of_lt {env : Env} {S : SState} {m' : Machine} (hm : Match env S m') (r : Nat)
    (hr : r < 32) : m'.reg (Fin.ofNat 32 r) = (S.reg r).eval env := reg_at hm r hr

/-- Adding a literal at or above `2^63` is subtracting its negation (`simp` would otherwise
rewrite the 64-bit literal itself). -/
theorem add_big {x : Word} {n : Nat} (h1 : n < 2 ^ 64) (h2 : 2 ^ 63 ≤ n) :
    x + BitVec.ofNat 64 n = x - BitVec.ofNat 64 (2 ^ 64 - n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- Multiplying by a literal at or above `2^63` is multiplying by its negation. -/
theorem mul_big {x : Word} {n : Nat} (h1 : n < 2 ^ 64) (h2 : 2 ^ 63 ≤ n) :
    x * BitVec.ofNat 64 n = - (x * BitVec.ofNat 64 (2 ^ 64 - n)) := by
  rw [← BitVec.mul_neg]; congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem add_neg' (y z : Word) : y + -z = y - z := (BitVec.sub_eq_add_neg y z).symm

/-- A word difference `n - a` without wrap, as `BitVec.toNat_sub` leaves it. -/
theorem wsub_mod {a n : Nat} (h : a ≤ n) (hn : n < 18446744073709551616) :
    (18446744073709551616 - a + n) % 18446744073709551616 = n - a := by
  omega

end ZesuExec.Fn.Rotate
