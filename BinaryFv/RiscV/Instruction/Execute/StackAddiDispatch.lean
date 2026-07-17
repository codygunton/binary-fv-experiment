import BinaryFv.RiscV.Instruction.Execute.StackAddi

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated `execute` dispatcher selects `execute_ITYPE` definitionally. -/
theorem executeITYPEDispatch (immediate : BitVec 12) (rs1 rd : regidx) (op : iop) :
    execute (.ITYPE (immediate, rs1, rd, op)) = execute_ITYPE immediate rs1 rd op := by
  rfl

/-- Lift the classified generated `addi sp, sp, immediate` contract through `execute`. -/
theorem executeStackAddiDispatch (state : State) (immediate : BitVec 12) (value : BitVec 64)
    (stackRead : state.regs.get? x2 = some value) :
    (execute (.ITYPE (immediate, stackPointer, stackPointer, .ADDI))).run state =
      .ok (.Retire_Success ())
        { state with regs := state.regs.insert x2 (value + sign_extend (m := 64) immediate) } := by
  change (execute_ITYPE immediate stackPointer stackPointer .ADDI).run state = _
  exact execute_stack_addi state immediate value stackRead

/-- Package the generated `execute` addi stack adjustment as a `Runs` contract. -/
theorem executeStackAddiDispatchRuns (state : State) (immediate : BitVec 12) (value : BitVec 64)
    (stackRead : state.regs.get? x2 = some value) :
    Runs (execute (.ITYPE (immediate, stackPointer, stackPointer, .ADDI))) state
      { state with regs := state.regs.insert x2 (value + sign_extend (m := 64) immediate) }
      (.Retire_Success ()) := by
  unfold Runs
  exact executeStackAddiDispatch state immediate value stackRead

/-- The generated `execute` addi stack adjustment preserves memory exactly. -/
theorem executeStackAddiDispatchPreservesMemory (state : State) (immediate : BitVec 12)
    (value : BitVec 64) (stackRead : state.regs.get? x2 = some value) :
    (match (execute (.ITYPE (immediate, stackPointer, stackPointer, .ADDI))).run state with
    | .ok _ state' => state'.mem
    | .error _ state' => state'.mem) = state.mem := by
  change (match (execute_ITYPE immediate stackPointer stackPointer .ADDI).run state with
    | .ok _ state' => state'.mem
    | .error _ state' => state'.mem) = state.mem
  exact execute_stack_addi_preserves_memory state immediate value stackRead

/-- The generated `execute` addi stack adjustment writes no register except `x2`. -/
theorem executeStackAddiDispatchRegisterFrame (state : State) (immediate : BitVec 12)
    (value : BitVec 64) :
    RegisterEqualOutside state
      { state with regs := state.regs.insert x2 (value + sign_extend (m := 64) immediate) } x2 :=
  execute_stack_addi_register_frame state immediate value

end BinaryFv.RiscV
