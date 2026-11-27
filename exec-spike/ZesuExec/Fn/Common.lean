import ZesuExec.Sym.Sound
import ZesuExec.Sym.Tactic
import ZesuExec.Image.Gen
import ZesuExec.Vc.SimpAttr

/-!
# Shared definitions for the function proofs `ZesuExec.Fn.<Id>`

A run of `Sym.run` starts from `entryState ov shape known`: register `i` is `ov i` or the
variable `var i`; the regions are `shape`. `entryEnv m shape` instantiates it at a machine `m`:
`var i` is `m.reg i`, the initial memory is `m.mem`. `entry_match` and `entry_wf` discharge
`run_sound`'s premises from facts about `m`.
-/

namespace ZesuExec.Fn
open ZesuExec.Sym ZesuExec.Machine

/-- `[lo, lo+n)` as a predicate on addresses (no wrap: `lo.toNat + n ≤ 2^64` is the caller's). -/
def InRange (lo : Word) (n : Nat) (a : Word) : Prop := lo.toNat ≤ a.toNat ∧ a.toNat < lo.toNat + n

/-- The return address is a valid `jalr` target. -/
def RetAligned (m : Machine) : Prop := (m.reg 1 &&& ~~~(1 : Word)).toNat % 4 = 0

/-- `n` bytes of stack below `sp` lie in RAM, are present, and `sp` is 16-aligned. -/
def StackOk (m : Machine) (n : Nat) : Prop :=
  (m.reg 2).toNat % 16 = 0 ∧ Layout.ramLo + n ≤ (m.reg 2).toNat ∧ (m.reg 2).toNat ≤ Layout.ramHi ∧
    ∀ j < n, (m.mem (m.reg 2 - BitVec.ofNat 64 n + BitVec.ofNat 64 j)).isSome

/-- (base, size) and the executor's view of one region. -/
abbrev Shape := List ((Word × Nat) × Region)

def entryState (ov : Nat → Option Sym) (shape : List Region) (known : List Write) : SState :=
  ⟨(List.range 32).map fun i => (ov i).getD (.var i), [], known, shape, 0⟩

def entryEnv (m : Machine) (regions : List (Word × Nat)) : Env :=
  ⟨fun i => m.reg (Fin.ofNat 32 i), regions,
    fun r j => (m.mem ((regions.getD r (0, 0)).1 + BitVec.ofNat 64 j)).getD 0⟩

theorem entryState_reg (ov : Nat → Option Sym) (rs : List Region) (ks : List Write) (i : Fin 32) :
    (entryState ov rs ks).reg i.val = if i.val = 0 then .lit 0 else (ov i.val).getD (.var i.val) := by
  unfold SState.reg entryState
  split
  · rfl
  · simp [List.getD_eq_getElem?_getD, i.isLt]

theorem entryEnv_var (m : Machine) (rs : List (Word × Nat)) (i : Fin 32) :
    (entryEnv m rs).vars i.val = m.reg i := by
  simp [entryEnv]

/-- `entryEnv_var` with a `Nat` index, as `Sym.eval_var` leaves it (for `zesu_simp`). -/
@[zesu_simp] theorem entryEnv_vars (m : Machine) (rs : List (Word × Nat)) (i : Nat) :
    (entryEnv m rs).vars i = m.reg (Fin.ofNat 32 i) := rfl

theorem Env.base_of_lt {env : Env} {r : Nat} (h : r < env.regions.length) :
    env.base r = env.regions[r].1 := by
  simp [Env.base, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem Env.size_of_lt {env : Env} {r : Nat} (h : r < env.regions.length) :
    env.size r = env.regions[r].2 := by
  simp [Env.size, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem entry_match {m : Machine} {regs : List (Word × Nat)} {ov : Nat → Option Sym}
    {rs : List Region} {ks : List Write}
    (hov : ∀ i : Fin 32, i.val ≠ 0 → ∀ s, ov i.val = some s → s.eval (entryEnv m regs) = m.reg i)
    (hpres : ∀ r j, r < rs.length → j < (entryEnv m regs).size r →
      (m.mem ((entryEnv m regs).base r + BitVec.ofNat 64 j)).isSome)
    (hknown : ∀ k ∈ ks, ∀ t < k.n,
      (entryEnv m regs).byte0 k.r (k.off + t) = byteOf (k.v.eval (entryEnv m regs)) t) :
    Match (entryEnv m regs) (entryState ov rs ks) m where
  regsLen := by simp [entryState]
  regs i := by
    rw [entryState_reg]
    split
    · next h0 => simp [Sym.eval, Machine.reg, h0]
    · next h0 =>
      cases h : ov i.val with
      | none => simp [Sym.eval, entryEnv_var]
      | some s => simpa using hov i h0 s h
  mem r j hr hj := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hpres r j hr hj)
    simp [memByte, entryState, Env.byte0, Env.base, entryEnv] at hb ⊢
    simp [hb]
  known := by simpa [entryState] using hknown

/-- One region is well placed: size as stated, aligned, inside RAM (writable) or a readable
interval. -/
def RegionOk (p : (Word × Nat) × Region) : Prop :=
  (∀ s, p.2.size = some s → p.1.2 = s) ∧ p.1.1.toNat % p.2.align = 0 ∧
    (if p.2.writable then writable p.1.1.toNat p.1.2 else readable p.1.1.toNat p.1.2) = true

def Disjoint (a b : Word × Nat) : Prop := a.1.toNat + a.2 ≤ b.1.toNat ∨ b.1.toNat + b.2 ≤ a.1.toNat

theorem entry_wf {m : Machine} {ov : Nat → Option Sym} {ks : List Write} (shape : Shape)
    (hok : ∀ p ∈ shape, RegionOk p) (hdisj : (shape.map (·.1)).Pairwise Disjoint) :
    Env.WF (entryEnv m (shape.map (·.1))) (entryState ov (shape.map (·.2)) ks) where
  len := by simp [entryEnv, entryState]
  disjoint r r' j j' hne hj hj' := by
    have hr : r < shape.length := by
      rcases Nat.lt_or_ge r shape.length with h | hc
      · exact h
      · simp [Env.size, entryEnv, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simpa using hc)] at hj
    have hr' : r' < shape.length := by
      rcases Nat.lt_or_ge r' shape.length with h | hc
      · exact h
      · simp [Env.size, entryEnv, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simpa using hc)] at hj'
    have hl : r < (entryEnv m (shape.map (·.1))).regions.length := by simpa [entryEnv] using hr
    have hl' : r' < (entryEnv m (shape.map (·.1))).regions.length := by simpa [entryEnv] using hr'
    rw [Env.size_of_lt hl] at hj
    rw [Env.size_of_lt hl'] at hj'
    rw [Env.base_of_lt hl, Env.base_of_lt hl']
    have hp := List.pairwise_iff_getElem.mp hdisj
    simp only [entryEnv] at hj hj' ⊢
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hp r r' (by simpa using hr) (by simpa using hr') h
      simp only [Disjoint] at this; omega
    · have := hp r' r (by simpa using hr') (by simpa using hr) h
      simp only [Disjoint] at this; omega
  size r R s hR hs := by
    obtain ⟨hr, hR⟩ := List.getElem?_eq_some_iff.mp hR
    simp [entryState] at hr hR
    subst hR
    have hl : r < (entryEnv m (shape.map (·.1))).regions.length := by simpa [entryEnv] using hr
    rw [Env.size_of_lt hl]
    simpa [entryEnv] using (hok _ (List.getElem_mem hr)).1 s hs
  align r R hR := by
    obtain ⟨hr, hR⟩ := List.getElem?_eq_some_iff.mp hR
    simp [entryState] at hr hR
    subst hR
    have hl : r < (entryEnv m (shape.map (·.1))).regions.length := by simpa [entryEnv] using hr
    rw [Env.base_of_lt hl]
    simpa [entryEnv] using (hok _ (List.getElem_mem hr)).2.1
  range r R hR := by
    obtain ⟨hr, hR⟩ := List.getElem?_eq_some_iff.mp hR
    simp [entryState] at hr hR
    subst hR
    have hl : r < (entryEnv m (shape.map (·.1))).regions.length := by simpa [entryEnv] using hr
    rw [Env.base_of_lt hl, Env.size_of_lt hl]
    simpa [entryEnv] using (hok _ (List.getElem_mem hr)).2.2

theorem SameOutside.mono {R R' : Word → Prop} {m m' : Machine} (h : SameOutside R m m')
    (hR : ∀ a, R a → R' a) : SameOutside R' m m' :=
  fun a ha => h a fun hr => ha (hR a hr)

/-- An address in a writable region of the entry state lies in that region's range. -/
theorem inWritable_entry {m : Machine} {ov : Nat → Option Sym} {ks : List Write} {shape : Shape}
    {a : Word} (h : InWritable (entryEnv m (shape.map (·.1))) (entryState ov (shape.map (·.2)) ks) a)
    (hfit : ∀ p ∈ shape, p.1.1.toNat + p.1.2 < 2 ^ 64) :
    ∃ p ∈ shape, p.2.writable = true ∧ InRange p.1.1 p.1.2 a := by
  obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := h
  obtain ⟨hr, hR⟩ := List.getElem?_eq_some_iff.mp hR
  simp [entryState] at hr hR
  subst hR
  have hl : r < (entryEnv m (shape.map (·.1))).regions.length := by simpa [entryEnv] using hr
  rw [Env.size_of_lt hl] at hj
  rw [Env.base_of_lt hl]
  refine ⟨shape[r], List.getElem_mem hr, hw, ?_⟩
  simp only [entryEnv, List.getElem_map] at hj ⊢
  have := hfit _ (List.getElem_mem hr)
  simp only [InRange]
  rw [toNat_add_ofNat (by omega)]
  omega

end ZesuExec.Fn

namespace ZesuExec.Fn

/-- Every rodata byte of the image lies in `[Layout.rodataLo, Layout.rodataHi)`. -/
theorem zesu_rodata_range {a b : Nat} (h : zesuImage.rodataByte? a = some b) :
    Layout.rodataLo ≤ a ∧ a < Layout.rodataHi := by
  obtain ⟨s, hs, hb⟩ := List.exists_of_findSome?_eq_some h
  have hseg : ∀ s ∈ zesuImage.rodata, Layout.rodataLo ≤ s.base ∧ s.base + s.bytes.length ≤ Layout.rodataHi := by
    decide +kernel
  obtain ⟨h1, h2⟩ := hseg s hs
  unfold RoSeg.byte? at hb
  split at hb
  · have := (List.getElem?_eq_some_iff.mp hb).1; omega
  · simp at hb

end ZesuExec.Fn
