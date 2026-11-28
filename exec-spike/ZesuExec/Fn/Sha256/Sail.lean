import ZesuExec.Fn.Sha256.Proof
import ZesuExec.Sail.Run

/-! # `zkvm_sha256` at the Sail level, and a machine satisfying its precondition -/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.SailLink

theorem sha256_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    SailReaches zesuImage (bound (m.reg 11).toNat)
      (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post m m') s :=
  sail_reaches h (sha256_spec _ m hpc ⟨hpre, rfl⟩)

/-- The witness's own bytes: the frame below `sp = 0xa0010000`, `out` at `0xa0020000`, three
input bytes at `0xa0030000`, the bump words and the staging word. -/
def nvByte (a : Nat) : Option Nat :=
  if 0xa000ff20 ≤ a ∧ a < 0xa0010000 then some 0
  else if 0xa0020000 ≤ a ∧ a < 0xa0020020 then some 0
  else if 0xa0030000 ≤ a ∧ a < 0xa0030003 then some (0x61 + (a - 0xa0030000))
  else if bump ≤ a ∧ a < bump + 16 then some 0
  else if Layout.extraParams ≤ a ∧ a < Layout.extraParams + 8 then some 0
  else none

/-- `zkvm_sha256("abc", 3, 0xa0020000)` with rodata loaded. -/
def nvMachine : Machine where
  regs := fun i => if i.val = 2 then 0xa0010000 else if i.val = 1 then 0x80000000
    else if i.val = 10 then 0xa0030000 else if i.val = 11 then 3
    else if i.val = 12 then 0xa0020000 else 0
  pc := BitVec.ofNat 64 entry
  mem := fun a => match nvByte a.toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => match zesuImage.rodataByte? a.toNat with
      | some b => some (BitVec.ofNat 8 b)
      | none => none

theorem nv_ro : RodataLoaded zesuImage nvMachine := by
  intro a b h
  have ha : a < Layout.ramLo := by
    have := (zesu_rodata_range h).2
    unfold Layout.rodataHi at this; unfold Layout.ramLo; omega
  have hlo : Layout.ramLo = 0xa0000000 := rfl
  have hn : nvByte a = none := by
    unfold nvByte bump Layout.extraParams
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  simp only [nvMachine, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), hn, h]

theorem pre_nonvacuous : ∃ m : Machine, m.pc.toNat = entry ∧ Pre m :=
  ⟨nvMachine, by decide +kernel, nv_ro, by unfold StackOk; decide +kernel,
    by unfold RetAligned; decide +kernel, Or.inr (by decide +kernel), by decide +kernel,
    by decide +kernel, by decide +kernel, by unfold Disjoint; decide +kernel,
    Or.inr (by unfold Disjoint; decide +kernel)⟩

end ZesuExec.Fn.Sha256
