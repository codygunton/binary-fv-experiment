import BinaryFv.RISCV.ExecuteContract

/-!
# Concrete-register `execute` reductions for the helper arithmetic / move instructions

Each theorem reduces the generated `execute` of one register-only instruction in `memcpy`, `memset`,
or `copy_from_slice_impl` to its concrete post-state (a single `regs.insert`), given the source
register value(s).  These mirror `execute_stack_addi` (the `addi sp,sp,imm` reduction) exactly — same
`simp` set, specialized to the helper's concrete register indices.  They are memory- and
platform-independent (a register read and a register write), so no fetch/PMP/PMA hypotheses appear;
the `try_step` packaging supplies those separately.

The `RTYPE (rs2, rs1, rd, ADD)` result is `rs1 + rs2`; the `ITYPE (imm, rs1, rd, ADDI)` result is
`rs1 + sext imm` (a `mv rd, rs1` is `addi rd, rs1, 0`).
-/

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RISCV

/-! ## `addi a5, a5, 1` (memcpy 0x10d30, memset 0x10d50) — `i++` -/

theorem execute_addi_a5_a5_1 (state : State) (kVal : BitVec 64)
    (h15 : state.regs.get? x15 = some kVal) :
    (execute_ITYPE 1#12 (.Regidx 15#5) (.Regidx 15#5) .ADDI).run state =
      .ok (.Retire_Success ())
        { state with regs := state.regs.insert x15 (kVal + sign_extend (m := 64) 1#12) } := by
  have r15Nat : (Sail.BitVec.toNatInt 15#5).toNat = 15 := by decide
  simp [execute_ITYPE, rX_bits, rX, wX_bits, wX, PreSail.readReg, PreSail.writeReg, r15Nat, h15,
    EStateM.run, EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure, EStateM.instMonad,
    MonadState.get, MonadState.modifyGet, MonadStateOf.get, MonadStateOf.modifyGet, getThe, modify,
    xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
    encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
    LeanRV64DExecutable.Functions.not, zero_extend, RETIRE_SUCCESS, regval_into_reg, regval_from_reg]

/-! ## `add a3, a1, a5` (memcpy 0x10d24) — `a3 = src + i` -/

theorem execute_add_a3_a1_a5 (state : State) (srcVal kVal : BitVec 64)
    (h11 : state.regs.get? x11 = some srcVal) (h15 : state.regs.get? x15 = some kVal) :
    (execute_RTYPE (.Regidx 15#5) (.Regidx 11#5) (.Regidx 13#5) .ADD).run state =
      .ok (.Retire_Success ())
        { state with regs := state.regs.insert x13 (srcVal + kVal) } := by
  have r11Nat : (Sail.BitVec.toNatInt 11#5).toNat = 11 := by decide
  have r15Nat : (Sail.BitVec.toNatInt 15#5).toNat = 15 := by decide
  have r13Nat : (Sail.BitVec.toNatInt 13#5).toNat = 13 := by decide
  simp [execute_RTYPE, rX_bits, rX, wX_bits, wX, PreSail.readReg, PreSail.writeReg,
    r11Nat, r15Nat, r13Nat, h11, h15, EStateM.run, EStateM.bind, EStateM.get, EStateM.modifyGet,
    EStateM.pure, EStateM.instMonad, MonadState.get, MonadState.modifyGet, MonadStateOf.get,
    MonadStateOf.modifyGet, getThe, modify, xreg_write_callback, xreg_full_write_callback,
    reg_name_forwards, get_config_use_abi_names, encdec_reg_forwards, encdec_reg_forwards_matches,
    reg_arch_name_raw_forwards, LeanRV64DExecutable.Functions.not, zero_extend, RETIRE_SUCCESS,
    regval_into_reg, regval_from_reg]

/-! ## `add a4, a0, a5` (memcpy 0x10d2c, memset 0x10d48) — `a4 = dst + i` -/

theorem execute_add_a4_a0_a5 (state : State) (dstVal kVal : BitVec 64)
    (h10 : state.regs.get? x10 = some dstVal) (h15 : state.regs.get? x15 = some kVal) :
    (execute_RTYPE (.Regidx 15#5) (.Regidx 10#5) (.Regidx 14#5) .ADD).run state =
      .ok (.Retire_Success ())
        { state with regs := state.regs.insert x14 (dstVal + kVal) } := by
  have r10Nat : (Sail.BitVec.toNatInt 10#5).toNat = 10 := by decide
  have r15Nat : (Sail.BitVec.toNatInt 15#5).toNat = 15 := by decide
  have r14Nat : (Sail.BitVec.toNatInt 14#5).toNat = 14 := by decide
  simp [execute_RTYPE, rX_bits, rX, wX_bits, wX, PreSail.readReg, PreSail.writeReg,
    r10Nat, r15Nat, r14Nat, h10, h15, EStateM.run, EStateM.bind, EStateM.get, EStateM.modifyGet,
    EStateM.pure, EStateM.instMonad, MonadState.get, MonadState.modifyGet, MonadStateOf.get,
    MonadStateOf.modifyGet, getThe, modify, xreg_write_callback, xreg_full_write_callback,
    reg_name_forwards, get_config_use_abi_names, encdec_reg_forwards, encdec_reg_forwards_matches,
    reg_arch_name_raw_forwards, LeanRV64DExecutable.Functions.not, zero_extend, RETIRE_SUCCESS,
    regval_into_reg, regval_from_reg]

end BinaryFv.Keccak
