import ZesuExec.Fn.Rotate.Model

/-!
# `std.mem.rotate` copies: one contract over the element size (programme plan S16)

`rotate(T, items, amount)` with `a0` = `items.ptr`, `a1` = `items.len`, `a2` = `amount`. A copy
is a `Cfg`: entry, element size `E`, frame size `fs`, the frame slots the prologue saves
(offset, register) and the callee-saved registers the body never writes.

`Pre`: `amount ≤ len` (Zig's slice bound `items[0..amount]`), the `E·len` bytes of the slice are
present and writable, the frame below `sp` is present and does not meet the slice.
`Post`: a return (callee-saved registers kept), memory changed only in the slice and the frame,
and element `e` of the slice holds the entry's element `(e + amount) % len`.
-/

namespace ZesuExec.Fn.Rotate
open ZesuExec ZesuExec.Sym

structure Cfg where
  entry : Nat
  /-- element size in bytes -/
  E : Nat
  /-- frame size -/
  fs : Nat
  /-- (frame offset, register) of each register the prologue saves -/
  saved : List (Nat × Nat)
  /-- callee-saved registers other than `sp`, `s0` and the saved ones; the body never writes
  them -/
  kept : List Nat
  /-- the saved slots lie in the frame, do not overlap, and name registers -/
  saved_le : ∀ s ∈ saved, s.1 + 8 ≤ fs := by decide
  saved_disj : saved.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1) := by decide
  saved_reg : ∀ s ∈ saved, s.2 < 32 := by decide
  fs_align : fs % 16 = 0 := by decide

section
variable (c : Cfg)

def ptr (m : Machine) : Word := m.reg 10
def len (m : Machine) : Nat := (m.reg 11).toNat
def amt (m : Machine) : Nat := (m.reg 12).toNat
def frame (m : Machine) : Word := m.reg 2 - BitVec.ofNat 64 c.fs

def Pre (m : Machine) : Prop :=
  RodataLoaded zesuImage m ∧ StackOk m c.fs ∧ RetAligned m ∧ amt m ≤ len m ∧
  Machine.writable (ptr m).toNat (c.E * len m) = true ∧
  (∀ j < c.E * len m, (m.mem (ptr m + BitVec.ofNat 64 j)).isSome) ∧
  Disjoint (ptr m, c.E * len m) (frame c m, c.fs)

/-- The slice or the frame. -/
def Writes (m : Machine) (a : Word) : Prop :=
  InRange (ptr m) (c.E * len m) a ∨ InRange (frame c m) c.fs a

def Post (m m' : Machine) : Prop :=
  Returns m m' ∧ SameOutside (Writes c m) m m' ∧
  ∀ e < len m, ∀ o < c.E, m'.mem (ptr m + BitVec.ofNat 64 (c.E * e + o)) =
    m.mem (ptr m + BitVec.ofNat 64 (c.E * ((e + amt m) % len m) + o))

/-- Facts every cut after the prologue keeps: `sp` and `s0` as the prologue sets them, `ra` and
the kept registers unchanged, the saved registers in their frame slots, the frame present,
memory changed only in the slice and the frame, rodata loaded. -/
def Common (m mh : Machine) : Prop :=
  RodataLoaded zesuImage mh ∧ mh.reg 2 = frame c m ∧ mh.reg 8 = m.reg 2 ∧ mh.reg 1 = m.reg 1 ∧
  (∀ i ∈ c.kept, mh.reg (Fin.ofNat 32 i) = m.reg (Fin.ofNat 32 i)) ∧
  (∀ s ∈ c.saved, ∀ t < 8, mh.mem (frame c m + BitVec.ofNat 64 (s.1 + t)) =
    some (byteOf (m.reg (Fin.ofNat 32 s.2)) t)) ∧
  (∀ j < c.fs, (mh.mem (frame c m + BitVec.ofNat 64 j)).isSome) ∧
  SameOutside (Writes c m) m mh

/-- The memory states at the loop heads of the three reversals, from the entry bytes. -/
def G0 (m : Machine) : Nat → Nat → Byte := bytesOf c.E (ptr m) m
def G1 (m : Machine) : Nat → Nat → Byte := rev 0 (amt m) (G0 c m)
def G2 (m : Machine) : Nat → Nat → Byte := rev (amt m) (len m - amt m) (G1 c m)
def G3 (m : Machine) : Nat → Nat → Byte := rev 0 (len m) (G2 c m)

end

/-! ## Facts from `Pre` -/

section
variable {c : Cfg} {m : Machine}

theorem pre_fit (h : Pre c m) : (ptr m).toNat + c.E * len m ≤ Layout.ramHi := by
  have := h.2.2.2.2.1
  simp [Machine.writable, Machine.inRange] at this; omega

theorem pre_frame (h : Pre c m) : (frame c m).toNat = (m.reg 2).toNat - c.fs ∧
    Layout.ramLo ≤ (frame c m).toNat ∧ (m.reg 2).toNat ≤ Layout.ramHi ∧
    Layout.ramLo + c.fs ≤ (m.reg 2).toNat := by
  obtain ⟨-, ⟨-, hlo, hhi, -⟩, -⟩ := h
  unfold frame
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢
  have : (m.reg 2).toNat < 2 ^ 64 := (m.reg 2).isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The rotation at the end of the third reversal. -/
theorem post_slice (h : Pre c m) {m' : Machine} (hs : SliceIs c.E (len m) (ptr m) m' (G3 c m)) :
    ∀ e < len m, ∀ o < c.E, m'.mem (ptr m + BitVec.ofNat 64 (c.E * e + o)) =
      m.mem (ptr m + BitVec.ofNat 64 (c.E * ((e + amt m) % len m) + o)) := by
  intro e he o ho
  rw [hs e he o ho]
  simp only [G3, G2, G1]
  rw [rev_rotate _ h.2.2.2.1 he]
  have hlt : (e + amt m) % len m < len m := Nat.mod_lt _ (by omega)
  exact (slice_bytesOf h.2.2.2.2.2.1 _ hlt o ho).symm

end

/-! ## Non-vacuity: a machine satisfying `Pre` -/

/-- RAM bytes the witness holds: `[0xa0000000, 0xa0010000)`. -/
def witnessRam (a : Nat) : Bool := 0xa0000000 ≤ a && a < 0xa0010000

/-- `sp = 0xa0001000`, `ra = 0x80000000`, a slice of `n` elements at `0xa0002000`, `amount = a`;
the image's rodata and the witness RAM present (zero), nothing else. -/
def witness (c : Cfg) (n a : Nat) : Machine where
  regs := fun i =>
    if i.val = 2 then BitVec.ofNat 64 0xa0001000 else if i.val = 1 then BitVec.ofNat 64 0x80000000
    else if i.val = 10 then BitVec.ofNat 64 0xa0002000 else if i.val = 11 then BitVec.ofNat 64 n
    else if i.val = 12 then BitVec.ofNat 64 a else 0
  pc := BitVec.ofNat 64 c.entry
  mem := fun x =>
    match zesuImage.rodataByte? x.toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => if witnessRam x.toNat then some 0 else none

theorem witness_present (c : Cfg) (n a : Nat) {x : Word} (h : witnessRam x.toNat = true) :
    ((witness c n a).mem x).isSome := by
  have hlo : 0xa0000000 ≤ x.toNat := by simp [witnessRam] at h; omega
  have hro : zesuImage.rodataByte? x.toNat = none := by
    cases h' : zesuImage.rodataByte? x.toNat with
    | none => rfl
    | some b => have := zesu_rodata_range h'; unfold Layout.rodataHi at this; omega
  simp only [witness, hro, h, if_true, Option.isSome_some]

theorem witnessRam_of {x : Word} {v : Nat} (hx : x.toNat = v) (h1 : 0xa0000000 ≤ v)
    (h2 : v < 0xa0010000) : witnessRam x.toNat = true := by
  rw [hx]; simp [witnessRam]; omega

/-- `Pre` holds of the witness for a slice of `n ≤ 2` elements (`E ≤ 0x4000`), `a ≤ n`, and any
copy whose frame is at most 4 KiB. -/
theorem pre_witness (c : Cfg) {n a : Nat} (hn : n ≤ 2) (ha : a ≤ n) (hfs : c.fs ≤ 0x1000)
    (hE : c.E ≤ 0x4000) : Pre c (witness c n a) := by
  have r1 : (witness c n a).reg 1 = BitVec.ofNat 64 0x80000000 := rfl
  have r2 : (witness c n a).reg 2 = BitVec.ofNat 64 0xa0001000 := rfl
  have r10 : (witness c n a).reg 10 = BitVec.ofNat 64 0xa0002000 := rfl
  have r11' : (witness c n a).reg 11 = BitVec.ofNat 64 n := rfl
  have r12' : (witness c n a).reg 12 = BitVec.ofNat 64 a := rfl
  have r11 : len (witness c n a) = n := by unfold len; rw [r11']; simp; omega
  have r12 : amt (witness c n a) = a := by unfold amt; rw [r12']; simp; omega
  have hEn : c.E * n ≤ 0x8000 := by
    have := Nat.mul_le_mul hE hn; omega
  have hfs16 := c.fs_align
  have hsp : (BitVec.ofNat 64 0xa0001000 : Word).toNat = 0xa0001000 := rfl
  have hp : (BitVec.ofNat 64 0xa0002000 : Word).toNat = 0xa0002000 := rfl
  have hfr : (BitVec.ofNat 64 0xa0001000 - BitVec.ofNat 64 c.fs : Word).toNat = 0xa0001000 - c.fs := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hsp, BitVec.toNat_ofNat]; omega), hsp,
      BitVec.toNat_ofNat]; omega
  refine ⟨fun x b h => ?_, ⟨by rw [r2, hsp], by rw [r2, hsp]; unfold Layout.ramLo; omega,
    by rw [r2, hsp]; decide, fun j hj => witness_present c n a ?_⟩, ?_,
    by rw [r11, r12]; exact ha, ?_, fun j hj => witness_present c n a ?_, ?_⟩
  · have hx : x < 2 ^ 64 := by
      have := zesu_rodata_range h; unfold Layout.rodataHi at this; omega
    simp [witness, Nat.mod_eq_of_lt hx, h]
  · rw [r2]
    exact witnessRam_of (toNat_add_ofNat (by rw [hfr]; omega)) (by rw [hfr]; omega)
      (by rw [hfr]; omega)
  · unfold RetAligned; rw [r1]; decide
  · rw [r11]; simp only [ptr, r10, hp, Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi]
    simp; omega
  · rw [r11] at hj
    simp only [ptr, r10]
    exact witnessRam_of (toNat_add_ofNat (by rw [hp]; omega)) (by rw [hp]; omega) (by rw [hp]; omega)
  · rw [r11]
    unfold Disjoint frame
    simp only [ptr, r10, r2, hp, hfr]
    omega

end ZesuExec.Fn.Rotate
