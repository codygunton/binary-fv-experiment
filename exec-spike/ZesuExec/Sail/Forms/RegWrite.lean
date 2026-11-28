import ZesuExec.Sail.Forms.Common
import BinaryFv.RiscV.Instruction.Execute.RegisterOp

/-!
# Simulation of the register-writing forms

`lui auipc addi andi xori sltiu slli srli add sub and or sll sltu mul mulhu`: `execute` reads the
source registers, writes `x rd` and falls through; each theorem is `sim_wreg` plus the form's
`execute_*_run` contract and the agreement of Sail's result with `Machine.exec`.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

variable {img : Image} {m m' : Machine} {s : State} {w : Nat}

theorem sim_addi {rd rs1 : Fin 32} {imm : BitVec 12} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.addi rd rs1 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  change Runs (execute_ITYPE imm (rg rs1) (rg rd) .ADDI) _ _ _
  refine execute_ITYPE_run _ _ imm _ _ .ADDI (m.reg rs1)
    (rX_rg_run (RegsAgree.T (m := m) hR.regs m.pc) rs1) ?_
  simpa [iTypeResult, sign_extend_eq] using wX_rg_run (T s m.pc) rd (m.reg rs1 + Machine.sx imm)

/-! ## Agreement of Sail's results with `Machine.exec` -/

theorem ult_bit (a b : Word) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u a b)) = if a.ult b then 1 else 0 := by
  by_cases h : a.toNat < b.toNat <;>
    simp [zopz0zI_u, BitVec.ult, bool_to_bit, bool_bit_forwards, Sail.BitVec.toNatInt, h,
      zero_extend, Sail.BitVec.zeroExtend]

theorem iType_andi (imm : BitVec 12) (v : Word) :
    iTypeResult .ANDI imm v = v &&& Machine.sx imm := by simp [iTypeResult, sign_extend_eq]
theorem iType_xori (imm : BitVec 12) (v : Word) :
    iTypeResult .XORI imm v = v ^^^ Machine.sx imm := by simp [iTypeResult, sign_extend_eq]
theorem iType_sltiu (imm : BitVec 12) (v : Word) :
    iTypeResult .SLTIU imm v = if v.ult (Machine.sx imm) then 1 else 0 := by
  simp only [iTypeResult]; rw [ult_bit, sign_extend_eq]

theorem rType_add (a b : Word) : rTypeResult .ADD a b = a + b := rfl
theorem rType_sub (a b : Word) : rTypeResult .SUB a b = a - b := rfl
theorem rType_and (a b : Word) : rTypeResult .AND a b = a &&& b := rfl
theorem rType_or (a b : Word) : rTypeResult .OR a b = a ||| b := rfl
theorem rType_xor (a b : Word) : rTypeResult .XOR a b = a ^^^ b := rfl
theorem rType_sltu (a b : Word) : rTypeResult .SLTU a b = if a.ult b then 1 else 0 := by
  simp only [rTypeResult]; rw [ult_bit]
theorem rType_sll (a b : Word) : rTypeResult .SLL a b = a <<< (b.toNat % 64) := by
  simp only [rTypeResult, Sail.shift_bits_left, BitVec.shiftLeft_eq']
  rw [extractLsb_field]; simp [LeanRV64DExecutable.Functions.log2_xlen]

theorem shiftI_slli (sh : BitVec 6) (a : Word) : shiftIopResult .SLLI sh a = a <<< sh.toNat := by
  simp only [shiftIopResult, Sail.shift_bits_left, BitVec.shiftLeft_eq']
  rw [extractLsb_field]; simp [LeanRV64DExecutable.Functions.log2_xlen]
theorem shiftI_srli (sh : BitVec 6) (a : Word) : shiftIopResult .SRLI sh a = a >>> sh.toNat := by
  simp only [shiftIopResult, Sail.shift_bits_right, BitVec.ushiftRight_eq']
  rw [extractLsb_field]; simp [LeanRV64DExecutable.Functions.log2_xlen]

theorem mul_low (a b : Word) :
    mulResult { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed } a b = a * b := by
  have h : BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
    rw [BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rw [← h]
  simp only [mulResult, mult_to_bits_half, to_bits_truncate, Sail.get_slice_int]
  rw [extractLsb_field]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, LeanRV64DExecutable.Functions.xlen]
  generalize a.toInt * b.toInt = z
  simp
  omega

theorem mul_high_uu (a b : Word) :
    mulResult { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } a b =
      BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) := by
  have hp : a.toNat * b.toNat < 2 ^ 128 :=
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' a.isLt b.isLt
      _ = 2 ^ 128 := (Nat.pow_add 2 64 64).symm
  simp only [mulResult, mult_to_bits_half, to_bits_truncate, Sail.get_slice_int]
  rw [extractLsb_field]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
    LeanRV64DExecutable.Functions.xlen, Sail.BitVec.toNatInt]
  simp only [Int.ofNat_eq_natCast, ← Int.natCast_mul]
  generalize a.toNat * b.toNat = p at hp ⊢
  simp
  omega

/-! ## The simulation theorems -/

theorem sim_andi {rd rs1 : Fin 32} {imm : BitVec 12} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.andi rd rs1 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  change Runs (execute_ITYPE imm (rg rs1) (rg rd) .ANDI) _ _ _
  refine execute_ITYPE_run _ _ imm _ _ .ANDI (m.reg rs1)
    (rX_rg_run (RegsAgree.T (m := m) hR.regs m.pc) rs1) ?_
  rw [iType_andi]; exact wX_rg_run _ rd _

theorem sim_xori {rd rs1 : Fin 32} {imm : BitVec 12} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.xori rd rs1 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  change Runs (execute_ITYPE imm (rg rs1) (rg rd) .XORI) _ _ _
  refine execute_ITYPE_run _ _ imm _ _ .XORI (m.reg rs1)
    (rX_rg_run (RegsAgree.T (m := m) hR.regs m.pc) rs1) ?_
  rw [iType_xori]; exact wX_rg_run _ rd _

theorem sim_sltiu {rd rs1 : Fin 32} {imm : BitVec 12} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.sltiu rd rs1 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  change Runs (execute_ITYPE imm (rg rs1) (rg rd) .SLTIU) _ _ _
  refine execute_ITYPE_run _ _ imm _ _ .SLTIU (m.reg rs1)
    (rX_rg_run (RegsAgree.T (m := m) hR.regs m.pc) rs1) ?_
  rw [iType_sltiu]; exact wX_rg_run _ rd _

theorem sim_add {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.add rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_RTYPE (rg rs2) (rg rs1) (rg rd) .ADD) _ _ _
  refine execute_RTYPE_run _ _ _ _ _ .ADD (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [rType_add]; exact wX_rg_run _ rd _

theorem sim_sub {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.sub rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_RTYPE (rg rs2) (rg rs1) (rg rd) .SUB) _ _ _
  refine execute_RTYPE_run _ _ _ _ _ .SUB (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [rType_sub]; exact wX_rg_run _ rd _

theorem sim_and {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.and rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_RTYPE (rg rs2) (rg rs1) (rg rd) .AND) _ _ _
  refine execute_RTYPE_run _ _ _ _ _ .AND (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [rType_and]; exact wX_rg_run _ rd _

theorem sim_or {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.or rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_RTYPE (rg rs2) (rg rs1) (rg rd) .OR) _ _ _
  refine execute_RTYPE_run _ _ _ _ _ .OR (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [rType_or]; exact wX_rg_run _ rd _

theorem sim_sll {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.sll rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_RTYPE (rg rs2) (rg rs1) (rg rd) .SLL) _ _ _
  refine execute_RTYPE_run _ _ _ _ _ .SLL (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [rType_sll]; exact wX_rg_run _ rd _

theorem sim_sltu {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.sltu rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_RTYPE (rg rs2) (rg rs1) (rg rd) .SLTU) _ _ _
  refine execute_RTYPE_run _ _ _ _ _ .SLTU (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [rType_sltu]; exact wX_rg_run _ rd _

theorem sim_slli {rd rs1 : Fin 32} {sh : BitVec 6} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.slli rd rs1 sh))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  change Runs (execute_SHIFTIOP sh (rg rs1) (rg rd) .SLLI) _ _ _
  refine execute_SHIFTIOP_run _ _ sh _ _ .SLLI (m.reg rs1)
    (rX_rg_run (RegsAgree.T (m := m) hR.regs m.pc) rs1) ?_
  rw [shiftI_slli]; exact wX_rg_run _ rd _

theorem sim_srli {rd rs1 : Fin 32} {sh : BitVec 6} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.srli rd rs1 sh))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  change Runs (execute_SHIFTIOP sh (rg rs1) (rg rd) .SRLI) _ _ _
  refine execute_SHIFTIOP_run _ _ sh _ _ .SRLI (m.reg rs1)
    (rX_rg_run (RegsAgree.T (m := m) hR.regs m.pc) rs1) ?_
  rw [shiftI_srli]; exact wX_rg_run _ rd _

theorem sim_mul {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.mul rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_MUL (rg rs2) (rg rs1) (rg rd) _) _ _ _
  refine execute_MUL_run _ _ _ _ _ _ (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [mul_low]; exact wX_rg_run _ rd _

theorem sim_mulhu {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.mulhu rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_MUL (rg rs2) (rg rs1) (rg rd) _) _ _ _
  refine execute_MUL_run _ _ _ _ _ _ (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [mul_high_uu]; exact wX_rg_run _ rd _

theorem sim_xor {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.xor rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_RTYPE (rg rs2) (rg rs1) (rg rd) .XOR) _ _ _
  refine execute_RTYPE_run _ _ _ _ _ .XOR (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [rType_xor]; exact wX_rg_run _ rd _

theorem sim_lui {rd : Fin 32} {imm : BitVec 20} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.lui rd imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  change Runs (execute_UTYPE imm (rg rd) .LUI) _ _ _
  refine execute_UTYPE_lui_run _ _ imm _ ?_
  rw [sign_extend_eq]; exact wX_rg_run _ rd _

theorem sim_auipc {rd : Fin 32} {imm : BitVec 20} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.auipc rd imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  change Runs (execute_UTYPE imm (rg rd) .AUIPC) _ _ _
  refine execute_UTYPE_auipc_run _ _ imm _ m.pc (T_pc hR m.pc) ?_
  rw [sign_extend_eq]; exact wX_rg_run _ rd _

end ZesuExec.SailLink
