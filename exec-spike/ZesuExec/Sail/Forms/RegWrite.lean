import ZesuExec.Sail.Forms.Common

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

end ZesuExec.SailLink
