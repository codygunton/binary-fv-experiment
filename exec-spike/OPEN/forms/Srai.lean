import ZesuExec.Sail.Forms.Common
import BinaryFv.RiscV.Instruction.Execute.Arithmetic

/-!
# S12 open goal: `srai` (and `sra`, `sraiw`, `sraw`)

Not part of the library (`OPEN/` is outside `ZesuExec`). Plan S12 contingency: the form is left
unsupported and its blocked functions stay blocked.

The generated model defines the arithmetic shift as a rotation
(`sail-riscv-lean/LeanRV64DExecutable/Prelude.lean:381`):

    def shift_bits_right_arith (value : BitVec k_n) (shift : BitVec k_m) : BitVec k_n :=
      BitVec.rotateRight value (BitVec.toNatInt shift)

so `execute (SHIFTIOP (sh, rs1, rd, SRAI))` writes `x[rs1]` rotated right by `sh`, not shifted
arithmetically. The two differ already at `x[rs1] = 1`, `sh = 1` (checked below by `decide`).
`sim_srai` for a `Machine.exec` that implements the RISC-V `srai` (an arithmetic shift, which is
what ZisK and Unicorn execute) is therefore false against this model; making `Machine.exec`
rotate would make the executor unsound against the hardware. The fix is in the model's Lean
prelude (regenerate `sail-riscv-lean` with `shift_bits_right_arith` as `BitVec.sshiftRight`),
outside this stage.
-/

open BinaryFv.RiscV LeanRV64DExecutable.Functions

/-- The model's `srai 1, 1` is `2^63`. -/
example : shiftIopResult .SRAI 1#6 1#64 = 0x8000000000000000#64 := by decide

/-- The model's `sra` has the same rotation. -/
example : rTypeResult .SRA 1#64 1#64 = 0x8000000000000000#64 := by decide

/-- RISC-V `srai 1, 1` is `0`. -/
example : (1#64).sshiftRight 1 = 0#64 := by decide

/-- The goal S12 would add (with `Machine.exec (.srai rd rs1 sh) =
`m.writeReg rd ((m.reg rs1).sshiftRight sh.toNat)`), stated on the model's result function: false
by the examples above. -/
theorem srai_agrees_goal (sh : BitVec 6) (a : BitVec 64) :
    shiftIopResult .SRAI sh a = a.sshiftRight sh.toNat := by
  sorry
