import ZesuExec.Fn.SszRoot.SparseProof
import ZesuExec.Sail.Run

/-! # `sparseRoot` at the Sail level, and a machine satisfying its precondition -/

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.SailLink

theorem sparseRoot_sail {m : Machine} {s : BinaryFv.RiscV.State}
    (h : Rel zesuImage m s) (hpc : m.pc.toNat = sparseEntry) (hpre : SparsePre m) :
    SailReaches zesuImage (sparseCost (depthOf m) (lenOf m))
      (fun s' => ∃ m', Rel zesuImage m' s' ∧ SparsePost m m') s :=
  sail_reaches h (sparse_reaches shaSpec m hpc hpre)

/-- The witness's own bytes: the stack `sparseStack 2` below `sp = 0xa0010000`, the result at
`0xa0020000`, three chunks at `0xa0030000`, `zkvm_sha256`'s bump words and the staging word. -/
def nvByte (a : Nat) : Option Nat :=
  if 0xa000fbc0 ≤ a ∧ a < 0xa0010000 then some 0
  else if 0xa0020000 ≤ a ∧ a < 0xa0020020 then some 0
  else if 0xa0030000 ≤ a ∧ a < 0xa0030060 then some (a % 251)
  else if Sha256.bump ≤ a ∧ a < Sha256.bump + 16 then some 0
  else if Layout.extraParams ≤ a ∧ a < Layout.extraParams + 8 then some 0
  else none

/-- `sparseRoot(0xa0020000, 0xa0030000, 3, 2)` with rodata loaded. -/
def nvMachine : Machine where
  regs := fun i => if i.val = 2 then 0xa0010000 else if i.val = 1 then 0x80000000
    else if i.val = 10 then 0xa0020000 else if i.val = 11 then 0xa0030000
    else if i.val = 12 then 3 else if i.val = 13 then 2 else 0
  pc := BitVec.ofNat 64 sparseEntry
  mem := fun a => match nvByte a.toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => match zesuImage.rodataByte? a.toNat with
      | some b => some (BitVec.ofNat 8 b)
      | none => none

theorem nv_ro : RodataLoaded zesuImage nvMachine := by
  intro a b h
  have ha := rodata_lo a b h
  have hlo : Layout.ramLo = 0xa0000000 := rfl
  have hn : nvByte a = none := by
    unfold nvByte Sha256.bump Layout.extraParams
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  simp only [nvMachine, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), hn, h]

theorem pre_nonvacuous : ∃ m : Machine, m.pc.toNat = sparseEntry ∧ SparsePre m :=
  ⟨nvMachine, by decide +kernel, by decide +kernel, nv_ro, by unfold StackOk; decide +kernel,
    by unfold RetAligned; decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by unfold Disjoint; decide +kernel⟩

end ZesuExec.Fn.SszRoot.Sparse
