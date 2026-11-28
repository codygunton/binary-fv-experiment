import ZesuExec.Fn.SszRoot.ProgRec
import ZesuExec.Fn.SszRoot.SparseProof
import ZesuExec.Sail.Run

/-!
# `progressiveRootAt` (`0x80042b2c`): contract, Sail level, a machine satisfying its precondition

`progressiveRootAt_spec`: `prog_spec` with `zkvm_sha256`'s contract discharged by
`Sparse.shaSpec` (`Sha256.sha256_spec 64`) and `sparseRoot`'s by `Sparse.sparseRoot_spec`.
-/

namespace ZesuExec.Fn.SszRoot.Prog
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.SailLink

theorem progressiveRootAt_spec : ProgSpec :=
  prog_spec Sparse.shaSpec Sparse.sparseRoot_spec

theorem progressiveRootAt_sail {m : Machine} {s : BinaryFv.RiscV.State}
    (h : Rel zesuImage m s) (hpc : m.pc.toNat = progEntry) (hpre : ProgPre m) :
    SailReaches zesuImage (progCost (lenOf m) (depthOf m))
      (fun s' => ∃ m', Rel zesuImage m' s' ∧ ProgPost m m') s :=
  sail_reaches h (progressiveRootAt_spec _ _ m hpc ⟨hpre, rfl, rfl⟩)

/-- The witness's own bytes: 4 KiB of stack below `sp = 0xa0010000`, the result at
`0xa0020000`, three chunks at `0xa0030000`, `zkvm_sha256`'s bump words and the staging word. -/
def nvByte (a : Nat) : Option Nat :=
  if 0xa000f000 ≤ a ∧ a < 0xa0010000 then some 0
  else if 0xa0020000 ≤ a ∧ a < 0xa0020020 then some 0
  else if 0xa0030000 ≤ a ∧ a < 0xa0030060 then some (a % 251)
  else if Sha256.bump ≤ a ∧ a < Sha256.bump + 16 then some 0
  else if Layout.extraParams ≤ a ∧ a < Layout.extraParams + 8 then some 0
  else none

/-- `progressiveRootAt(0xa0020000, 0xa0030000, 3, 0)` with rodata loaded. -/
def nvMachine : Machine where
  regs := fun i => if i.val = 2 then 0xa0010000 else if i.val = 1 then 0x80000000
    else if i.val = 10 then 0xa0020000 else if i.val = 11 then 0xa0030000
    else if i.val = 12 then 3 else 0
  pc := BitVec.ofNat 64 progEntry
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

/-- The stack `progressiveRootAt` needs on 3 chunks at depth 0. -/
theorem nv_need : progNeed nvMachine = 0x580 := by
  have h3 : lenOf nvMachine = 3 := rfl
  have h0 : depthOf nvMachine = 0 := rfl
  unfold progNeed
  rw [h3, h0, progStack_ne (by decide), show 3 - 2 ^ 0 = 2 from rfl, progStack_ne (by decide),
    show 2 - 2 ^ 2 = 0 from rfl, progStack, if_pos rfl]
  rfl

theorem nv_fits : progFits (lenOf nvMachine) (depthOf nvMachine) = true := by
  have h3 : lenOf nvMachine = 3 := rfl
  have h0 : depthOf nvMachine = 0 := rfl
  rw [h3, h0, progFits, if_neg (by decide), if_pos (by decide), show 3 - 2 ^ 0 = 2 from rfl,
    progFits, if_neg (by decide), if_pos (by decide), show 2 - 2 ^ 2 = 0 from rfl, progFits,
    if_pos rfl]

theorem pre_nonvacuous : ∃ m : Machine, m.pc.toNat = progEntry ∧ ProgPre m :=
  ⟨nvMachine, by decide +kernel, nv_fits, by
    rw [PreN, nv_need]
    exact ⟨nv_ro, by unfold StackOk; decide +kernel, by unfold RetAligned; decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by unfold Disjoint; decide +kernel⟩⟩

end ZesuExec.Fn.SszRoot.Prog
