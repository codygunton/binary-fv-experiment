import ZesuExec.Fn.Common

/-!
# F0 `alt_fl_alloc.remap` (`0x8004218c`, 9 instructions)

The allocator's `remap` always refuses: it returns null in `a0`. It saves and restores `ra` and
`s0` in a 16-byte frame below `sp`.
-/

namespace ZesuExec.Fn.F0
open ZesuExec

def entry : Nat := 0x8004218c
def bound : Nat := 9

def Pre (m : Machine) : Prop := RodataLoaded zesuImage m ∧ StackOk m 16 ∧ RetAligned m

def Post (m m' : Machine) : Prop :=
  Returns m m' ∧ m'.reg 10 = 0 ∧ SameOutside (InRange (m.reg 2 - 16) 16) m m'

/-- A machine satisfying `Pre`: `sp = 0xa0001000`, the 16 bytes below it zero, `ra = 0x80000000`,
the image's rodata loaded. -/
def witness : Machine where
  regs := fun i => if i.val = 2 then 0xa0001000 else if i.val = 1 then 0x80000000 else 0
  pc := BitVec.ofNat 64 entry
  mem := fun a =>
    match zesuImage.rodataByte? a.toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => if 0xa0000ff0 ≤ a.toNat ∧ a.toNat < 0xa0001000 then some 0 else none

theorem witness_rodata : RodataLoaded zesuImage witness := by
  intro a b h
  have ha : a < 2 ^ 64 := by
    simp [zesuImage, Image.rodataByte?, Gen.rodata_801136d8, RoSeg.byte?] at h
    have := (List.getElem?_eq_some_iff.mp h.2).1
    simp at this; omega
  simp [witness, Nat.mod_eq_of_lt ha, h]

example : ∃ m, Pre m := by
  refine ⟨witness, witness_rodata, ⟨by decide, by decide, by decide, ?_⟩,
    by unfold RetAligned; decide⟩
  intro j hj
  have hr : witness.reg 2 = 0xa0001000 := rfl
  have ha : ((0xa0001000 : Word) - BitVec.ofNat 64 16 + BitVec.ofNat 64 j).toNat =
      0xa0000ff0 + j := by
    simp [BitVec.toNat_add]; omega
  have hro : zesuImage.rodataByte? (0xa0000ff0 + j) = none := by
    simp [zesuImage, Image.rodataByte?, Gen.rodata_801136d8, RoSeg.byte?]
    intro _; omega
  rw [hr]
  simp only [witness]
  rw [ha, hro]
  simp; omega

end ZesuExec.Fn.F0
