import ZesuExec.Sail.Forms.RegWrite
import ZesuExec.Sail.Forms.Load
import ZesuExec.Sail.Forms.Store
import ZesuExec.Sail.Forms.Branch
import ZesuExec.Sail.Forms.Jump

/-!
# `sail_step_sim`: every concrete step is a retiring Sail `try_step`

By cases on the decoded form; each case is the form's `sim_<form>` theorem in
`ZesuExec/Sail/Forms/`. All 32 constructors of `Instr` are covered (no `Proved` restriction).
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV (State Runs)
open LeanRV64DExecutable.Functions

theorem sail_step_sim {img : Image} {m m' : Machine} {s : State} (h : Rel img m s)
    (hs : step img m = some m') (n : Nat) :
    ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  have hs' := hs
  unfold step at hs'
  split at hs'
  · split at hs'
    · rename_i w hw
      split at hs'
      · rename_i i hd
        cases i with
        | lui rd imm => exact sim_lui h hw hd hs n
        | auipc rd imm => exact sim_auipc h hw hd hs n
        | jal rd imm => exact sim_jal h hw hd hs n
        | jalr rd rs1 imm => exact sim_jalr h hw hd hs n
        | beq rs1 rs2 imm => exact sim_beq h hw hd hs n
        | bne rs1 rs2 imm => exact sim_bne h hw hd hs n
        | blt rs1 rs2 imm => exact sim_blt h hw hd hs n
        | bltu rs1 rs2 imm => exact sim_bltu h hw hd hs n
        | bgeu rs1 rs2 imm => exact sim_bgeu h hw hd hs n
        | lb rd rs1 imm => exact sim_lb h hw hd hs n
        | lbu rd rs1 imm => exact sim_lbu h hw hd hs n
        | lhu rd rs1 imm => exact sim_lhu h hw hd hs n
        | lw rd rs1 imm => exact sim_lw h hw hd hs n
        | ld rd rs1 imm => exact sim_ld h hw hd hs n
        | sb rs1 rs2 imm => exact sim_sb h hw hd hs n
        | sh rs1 rs2 imm => exact sim_sh h hw hd hs n
        | sw rs1 rs2 imm => exact sim_sw h hw hd hs n
        | sd rs1 rs2 imm => exact sim_sd h hw hd hs n
        | addi rd rs1 imm => exact sim_addi h hw hd hs n
        | andi rd rs1 imm => exact sim_andi h hw hd hs n
        | xori rd rs1 imm => exact sim_xori h hw hd hs n
        | sltiu rd rs1 imm => exact sim_sltiu h hw hd hs n
        | slli rd rs1 sh => exact sim_slli h hw hd hs n
        | srli rd rs1 sh => exact sim_srli h hw hd hs n
        | add rd rs1 rs2 => exact sim_add h hw hd hs n
        | sub rd rs1 rs2 => exact sim_sub h hw hd hs n
        | and rd rs1 rs2 => exact sim_and h hw hd hs n
        | or rd rs1 rs2 => exact sim_or h hw hd hs n
        | sll rd rs1 rs2 => exact sim_sll h hw hd hs n
        | sltu rd rs1 rs2 => exact sim_sltu h hw hd hs n
        | mul rd rs1 rs2 => exact sim_mul h hw hd hs n
        | mulhu rd rs1 rs2 => exact sim_mulhu h hw hd hs n
        | xor rd rs1 rs2 => exact sim_xor h hw hd hs n
        | addiw rd rs1 imm => exact sim_addiw h hw hd hs n
        | bge rs1 rs2 imm => exact sim_bge h hw hd hs n
        | lwu rd rs1 imm => exact sim_lwu h hw hd hs n
        | srliw rd rs1 sh => exact sim_srliw h hw hd hs n
        | subw rd rs1 rs2 => exact sim_subw h hw hd hs n
        | lh rd rs1 imm => exact sim_lh h hw hd hs n
      · cases hs'
    · cases hs'
  · cases hs'

end ZesuExec.SailLink
