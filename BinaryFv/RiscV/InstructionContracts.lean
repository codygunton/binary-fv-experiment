import BinaryFv.RiscV.Framing
import BinaryFv.RiscV.Stack

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- Generated Sail semantics for a classified `addi sp, sp, immediate` adjustment. -/
theorem execute_stack_addi (state : State) (immediate : BitVec 12) (value : BitVec 64)
    (stackRead : state.regs.get? x2 = some value) :
    (execute_ITYPE immediate stackPointer stackPointer .ADDI).run state =
      .ok (.Retire_Success ())
        { state with regs := state.regs.insert x2 (value + sign_extend (m := 64) immediate) } := by
  have r2Nat : (Sail.BitVec.toNatInt 2#5).toNat = 2 := by decide
  simp [execute_ITYPE, stackPointer, rX_bits, rX, wX_bits, wX, PreSail.readReg,
    PreSail.writeReg, r2Nat, stackRead, EStateM.run, EStateM.bind, EStateM.get,
    EStateM.modifyGet, EStateM.pure, EStateM.instMonad, MonadState.get, MonadState.modifyGet,
    MonadStateOf.get, MonadStateOf.modifyGet, getThe, modify, xreg_write_callback,
    xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names, encdec_reg_forwards,
    encdec_reg_forwards_matches, reg_arch_name_raw_forwards, LeanRV64DExecutable.Functions.not,
    zero_extend, RETIRE_SUCCESS, regval_into_reg, regval_from_reg]

theorem execute_stack_addi_preserves_memory (state : State) (immediate : BitVec 12)
    (value : BitVec 64) (stackRead : state.regs.get? x2 = some value) :
    (match (execute_ITYPE immediate stackPointer stackPointer .ADDI).run state with
    | .ok _ state' => state'.mem
    | .error _ state' => state'.mem) = state.mem := by
  rw [execute_stack_addi state immediate value stackRead]

theorem execute_stack_addi_register_frame (state : State) (immediate : BitVec 12)
    (value : BitVec 64) :
    RegisterEqualOutside state
      { state with regs := state.regs.insert x2 (value + sign_extend (m := 64) immediate) } x2 :=
  writeReg_register_frame state x2 (value + sign_extend (m := 64) immediate)

end BinaryFv.RiscV
