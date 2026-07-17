import BinaryFv.RiscV.ExecuteContract

/-!
# Concrete-register `execute` reductions for the `copy_from_slice_impl` live path

`copy_from_slice_impl` (0x10c44) checks `dst_len == src_len` and, when equal, renames its arguments
into `memcpy`'s calling convention via three `mv` (`addi rd, rs1, 0`) instructions and tail-calls
`memcpy`.  These reductions give the concrete post-state of each live-path `mv`, mirroring
`execute_stack_addi` (and `HelperArithDispatch`).  The panic branch's two `mv`s (0x10c5c, 0x10c60)
are intentionally omitted — that branch is proved unreachable when `dst_len == src_len`.

`mv rd, rs1` is `addi rd, rs1, 0`, so the written value is `rs1Val + sign_extend (m := 64) 0#12`
(kept in the exact generated form; `+ 0` is discharged by callers when convenient).
-/

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

/-- `mv a4, a1` = `addi a4, a1, 0` at `0x10c44` (save `dst_len` into `a4`). -/
theorem execute_mv_a4_a1 (state : State) (a1Val : BitVec 64)
    (h11 : state.regs.get? x11 = some a1Val) :
    (execute_ITYPE 0#12 (.Regidx 11#5) (.Regidx 14#5) .ADDI).run state =
      .ok (.Retire_Success ())
        { state with regs := state.regs.insert x14 (a1Val + sign_extend (m := 64) 0#12) } := by
  have r11Nat : (Sail.BitVec.toNatInt 11#5).toNat = 11 := by decide
  have r14Nat : (Sail.BitVec.toNatInt 14#5).toNat = 14 := by decide
  simp [execute_ITYPE, rX_bits, rX, wX_bits, wX, PreSail.readReg, PreSail.writeReg, r11Nat, r14Nat,
    h11,
    EStateM.run, EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure, EStateM.instMonad,
    MonadState.get, MonadState.modifyGet, MonadStateOf.get, MonadStateOf.modifyGet, getThe, modify,
    xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
    encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
    LeanRV64DExecutable.Functions.not, zero_extend, RETIRE_SUCCESS, regval_into_reg, regval_from_reg]

/-- `mv a1, a2` = `addi a1, a2, 0` at `0x10c4c` (`a1 = src_ptr` for the memcpy call). -/
theorem execute_mv_a1_a2 (state : State) (a2Val : BitVec 64)
    (h12 : state.regs.get? x12 = some a2Val) :
    (execute_ITYPE 0#12 (.Regidx 12#5) (.Regidx 11#5) .ADDI).run state =
      .ok (.Retire_Success ())
        { state with regs := state.regs.insert x11 (a2Val + sign_extend (m := 64) 0#12) } := by
  have r12Nat : (Sail.BitVec.toNatInt 12#5).toNat = 12 := by decide
  have r11Nat : (Sail.BitVec.toNatInt 11#5).toNat = 11 := by decide
  simp [execute_ITYPE, rX_bits, rX, wX_bits, wX, PreSail.readReg, PreSail.writeReg, r12Nat, r11Nat,
    h12,
    EStateM.run, EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure, EStateM.instMonad,
    MonadState.get, MonadState.modifyGet, MonadStateOf.get, MonadStateOf.modifyGet, getThe, modify,
    xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
    encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
    LeanRV64DExecutable.Functions.not, zero_extend, RETIRE_SUCCESS, regval_into_reg, regval_from_reg]

/-- `mv a2, a4` = `addi a2, a4, 0` at `0x10c50` (`a2 = len` for the memcpy call). -/
theorem execute_mv_a2_a4 (state : State) (a4Val : BitVec 64)
    (h14 : state.regs.get? x14 = some a4Val) :
    (execute_ITYPE 0#12 (.Regidx 14#5) (.Regidx 12#5) .ADDI).run state =
      .ok (.Retire_Success ())
        { state with regs := state.regs.insert x12 (a4Val + sign_extend (m := 64) 0#12) } := by
  have r14Nat : (Sail.BitVec.toNatInt 14#5).toNat = 14 := by decide
  have r12Nat : (Sail.BitVec.toNatInt 12#5).toNat = 12 := by decide
  simp [execute_ITYPE, rX_bits, rX, wX_bits, wX, PreSail.readReg, PreSail.writeReg, r14Nat, r12Nat,
    h14,
    EStateM.run, EStateM.bind, EStateM.get, EStateM.modifyGet, EStateM.pure, EStateM.instMonad,
    MonadState.get, MonadState.modifyGet, MonadStateOf.get, MonadStateOf.modifyGet, getThe, modify,
    xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
    encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
    LeanRV64DExecutable.Functions.not, zero_extend, RETIRE_SUCCESS, regval_into_reg, regval_from_reg]

end BinaryFv.Keccak
