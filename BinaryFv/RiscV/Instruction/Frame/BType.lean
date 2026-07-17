import BinaryFv.RiscV.Logic.StackPointerFrame

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
private theorem rXBitsComparison_preserves_stack_pointer (rs1 rs2 : regidx)
    (comparison : BitVec 64 → BitVec 64 → Bool) :
    PreservesStackPointer (do
      let left ← rX_bits rs1
      let right ← rX_bits rs2
      pure (comparison left right)) := by
  apply preservesStackPointer_bind (rX_bits rs1) _
  · exact rXBits_preserves_stack_pointer rs1
  · intro left
    apply preservesStackPointer_bind (rX_bits rs2) _
    · exact rXBits_preserves_stack_pointer rs2
    · intro right
      exact preservesStackPointer_pure (comparison left right)

private def bTypeCondition (rs2 rs1 : regidx) (op : bop) : SailM Bool := do
  match op with
  | .BEQ => pure ((← rX_bits rs1) == (← rX_bits rs2))
  | .BNE => pure ((← rX_bits rs1) != (← rX_bits rs2))
  | .BLT => pure (zopz0zI_s (← rX_bits rs1) (← rX_bits rs2))
  | .BGE => pure (zopz0zKzJ_s (← rX_bits rs1) (← rX_bits rs2))
  | .BLTU => pure (zopz0zI_u (← rX_bits rs1) (← rX_bits rs2))
  | .BGEU => pure (zopz0zKzJ_u (← rX_bits rs1) (← rX_bits rs2))

private theorem bTypeCondition_preserves_stack_pointer (rs2 rs1 : regidx) (op : bop) :
    PreservesStackPointer (bTypeCondition rs2 rs1 op) := by
  cases op with
  | BEQ =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2
      (fun left right => left == right)
  | BNE =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2
      (fun left right => left != right)
  | BLT =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2 zopz0zI_s
  | BGE =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2 zopz0zKzJ_s
  | BLTU =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2 zopz0zI_u
  | BGEU =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2 zopz0zKzJ_u

private def bTypeOutcome (imm : BitVec 13) (taken : Bool) : SailM ExecutionResult := do
  if taken then
    jump_to ((← Sail.readReg PC) + sign_extend (m := 64) imm)
  else
    pure RETIRE_SUCCESS

private theorem bTypeOutcome_preserves_stack_pointer (imm : BitVec 13) (taken : Bool) :
    PreservesStackPointer (bTypeOutcome imm taken) := by
  unfold bTypeOutcome
  by_cases takenTrue : taken = true
  · rw [if_pos takenTrue]
    apply preservesStackPointer_bind (Sail.readReg PC) _
    · exact readReg_preserves_stack_pointer PC
    · intro pc
      exact jump_to_preserves_stack_pointer (pc + sign_extend (m := 64) imm)
  · rw [if_neg takenTrue]
    exact preservesStackPointer_pure RETIRE_SUCCESS

private theorem execute_BTYPE_factor (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) :
    execute_BTYPE imm rs2 rs1 op = (do
      let taken ← bTypeCondition rs2 rs1 op
      bTypeOutcome imm taken) := by
  rfl

/-- `execute_BTYPE` preserves `x2` across normal and error outcomes for every branch opcode. -/
theorem execute_BTYPE_preserves_stack_pointer (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) :
    PreservesStackPointer (execute_BTYPE imm rs2 rs1 op) := by
  rw [execute_BTYPE_factor]
  apply preservesStackPointer_bind (bTypeCondition rs2 rs1 op) _
  · exact bTypeCondition_preserves_stack_pointer rs2 rs1 op
  · intro taken
    exact bTypeOutcome_preserves_stack_pointer imm taken

end BinaryFv.RiscV
