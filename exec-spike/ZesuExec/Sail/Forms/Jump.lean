import ZesuExec.Sail.Forms.Common

/-!
# Simulation of the jumps

`jalr` and `jal` (calls, returns and plain jumps alike): the generated `execute` reads the link
`nextPC = pc + 4`, overwrites `nextPC` with the 4-aligned target and writes the link to `x rd`;
this is `sim_ctl`.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

variable {img : Image} {m m' : Machine} {s : State} {w : Nat}

theorem update0_eq (x : BitVec 64) : Sail.BitVec.update x 0 0#1 = x &&& ~~~(1 : BitVec 64) := by
  ext j hj
  simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', Bool.and_comm]

theorem access1_and_not1 (x : BitVec 64) :
    Sail.BitVec.access (x &&& ~~~(1 : BitVec 64)) 1 = Sail.BitVec.access x 1 := by
  simp [Sail.BitVec.access]

theorem sim_jalr {rd rs1 : Fin 32} {imm : BitVec 12} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.jalr rd rs1 imm))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.jumpTo] at hex
  split at hex
  · rename_i hal
    simp only [Option.some.injEq] at hex
    subst hex
    obtain ⟨z, hz⟩ := T_zca hR m.pc
    have hal1 := (jump_aligned hal).2
    rw [access1_and_not1] at hal1
    refine sim_ctl hR hw hd hpc ?_ n
    change Runs (execute_JALR imm (rg rs1) (rg rd)) _ _ _
    have key := execute_JALR_run (T s m.pc)
      (setX (J s m.pc (Sail.BitVec.update (m.reg rs1 + sign_extend (m := 64) imm) 0 0#1)) rd
        (m.pc + 4))
      imm (rg rs1) (rg rd) (m.pc + 4) (m.reg rs1) (get_next_pc_run _ _ (T_nextPC s m.pc))
      (rX_rg_run (RegsAgree.T (m := m) hR.regs m.pc) rs1) hal1 z hz (wX_rg_run _ rd _)
    rw [update0_eq] at key
    exact key
  · cases hex

end ZesuExec.SailLink
