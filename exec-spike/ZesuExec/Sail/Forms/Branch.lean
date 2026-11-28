import ZesuExec.Sail.Forms.Common

/-!
# Simulation of the conditional branches

`beq bne blt bltu bgeu`: the generated comparison reads `rs1`, `rs2` and agrees with
`Machine.branch`'s condition; a taken branch is `sim_ctl` (no link), a not-taken one `sim_fall`.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

variable {img : Image} {m m' : Machine} {s : State} {w : Nat}

/-- The generated branch condition, read from a state holding `m`'s registers. -/
theorem bTypeTaken_run {st : State} (h : RegsAgree m st) (rs1 rs2 : Fin 32) (op : bop) :
    Runs (bTypeTaken (rg rs2) (rg rs1) op) st st
      (match op with
        | .BEQ => m.reg rs1 == m.reg rs2
        | .BNE => m.reg rs1 != m.reg rs2
        | .BLT => zopz0zI_s (m.reg rs1) (m.reg rs2)
        | .BGE => zopz0zKzJ_s (m.reg rs1) (m.reg rs2)
        | .BLTU => zopz0zI_u (m.reg rs1) (m.reg rs2)
        | .BGEU => zopz0zKzJ_u (m.reg rs1) (m.reg rs2)) := by
  cases op <;>
    exact Runs.bind (rX_rg_run h rs1) (Runs.bind (rX_rg_run h rs2) rfl)

/-- A branch on condition `c` (as computed by Sail) simulates `Machine.branch m c imm`. -/
theorem sim_branch {rs1 rs2 : Fin 32} {imm : BitVec 13} {op : bop} {c : Bool} {i : Instr}
    (hR : Rel img m s) (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some i)
    (hpc : Layout.textLo ≤ m.pc.toNat ∧ m.pc.toNat < Layout.textHi ∧ m.pc.toNat % 4 = 0)
    (hi : toSail i = .BTYPE (imm, rg rs2, rg rs1, op))
    (hcond : Runs (bTypeTaken (rg rs2) (rg rs1) op) (T s m.pc) (T s m.pc) c)
    (hb : m.branch c imm = some m') (n : Nat) :
    ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  unfold Machine.branch at hb
  cases c
  · simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hb
    subst hb
    refine sim_fall hR hw hd hpc ?_ n
    rw [hi]
    exact execute_BTYPE_notTaken_run _ imm _ _ op hcond
  · simp only [if_true, Machine.jumpTo] at hb
    split at hb
    · rename_i hal
      simp only [Option.some.injEq] at hb
      subst hb
      obtain ⟨z, hz⟩ := T_zca hR m.pc
      have := sim_ctl (rd := ⟨0, by decide⟩) (link := 0) (t := m.pc + Machine.sx imm)
        hR hw hd hpc ?_ n
      · rwa [Machine.setReg_zero] at this
      rw [hi]
      exact execute_BTYPE_taken_run _ imm _ _ op m.pc hcond (T_pc hR m.pc)
        (jump_aligned hal).1 (jump_aligned hal).2 z hz
    · cases hb

theorem sim_beq {rs1 rs2 : Fin 32} {imm : BitVec 13} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.beq rs1 rs2 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  exact sim_branch hR hw hd hpc rfl
    (bTypeTaken_run (RegsAgree.T (m := m) hR.regs m.pc) rs1 rs2 .BEQ) hex n

theorem cond_bne (a b : Word) : (a != b) = (a != b) := rfl
theorem cond_blt (a b : Word) : zopz0zI_s a b = a.slt b := by
  simp [zopz0zI_s, BitVec.slt]
theorem cond_bltu (a b : Word) : zopz0zI_u a b = a.ult b := by
  simp [zopz0zI_u, BitVec.ult, Sail.BitVec.toNatInt]
theorem cond_bgeu (a b : Word) : zopz0zKzJ_u a b = !a.ult b := by
  simp only [zopz0zKzJ_u, BitVec.ult, Sail.BitVec.toNatInt]
  by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega
theorem cond_bge (a b : Word) : zopz0zKzJ_s a b = !a.slt b := by
  simp only [zopz0zKzJ_s, BitVec.slt]
  by_cases h : a.toInt < b.toInt <;> simp [h] <;> omega

theorem sim_bne {rs1 rs2 : Fin 32} {imm : BitVec 13} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.bne rs1 rs2 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  have hcond := bTypeTaken_run (RegsAgree.T (m := m) hR.regs m.pc) rs1 rs2 .BNE
  simp only at hcond
  rw [cond_bne] at hcond
  exact sim_branch hR hw hd hpc rfl hcond hex n

theorem sim_blt {rs1 rs2 : Fin 32} {imm : BitVec 13} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.blt rs1 rs2 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  have hcond := bTypeTaken_run (RegsAgree.T (m := m) hR.regs m.pc) rs1 rs2 .BLT
  simp only at hcond
  rw [cond_blt] at hcond
  exact sim_branch hR hw hd hpc rfl hcond hex n

theorem sim_bltu {rs1 rs2 : Fin 32} {imm : BitVec 13} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.bltu rs1 rs2 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  have hcond := bTypeTaken_run (RegsAgree.T (m := m) hR.regs m.pc) rs1 rs2 .BLTU
  simp only at hcond
  rw [cond_bltu] at hcond
  exact sim_branch hR hw hd hpc rfl hcond hex n

theorem sim_bgeu {rs1 rs2 : Fin 32} {imm : BitVec 13} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.bgeu rs1 rs2 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  have hcond := bTypeTaken_run (RegsAgree.T (m := m) hR.regs m.pc) rs1 rs2 .BGEU
  simp only at hcond
  rw [cond_bgeu] at hcond
  exact sim_branch hR hw hd hpc rfl hcond hex n

theorem sim_bge {rs1 rs2 : Fin 32} {imm : BitVec 13} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.bge rs1 rs2 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  have hcond := bTypeTaken_run (RegsAgree.T (m := m) hR.regs m.pc) rs1 rs2 .BGE
  simp only at hcond
  rw [cond_bge] at hcond
  exact sim_branch hR hw hd hpc rfl hcond hex n

end ZesuExec.SailLink
