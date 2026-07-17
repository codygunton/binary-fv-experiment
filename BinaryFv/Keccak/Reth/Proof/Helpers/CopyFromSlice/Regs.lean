import BinaryFv.Keccak.Reth.Proof.Helpers.Memcpy
import BinaryFv.Keccak.Reth.Proof.Helpers.CopyFromSliceDispatch
import BinaryFv.RiscV.Instruction.Execute.RegisterOp

/-!
# `copy_from_slice` register read/write reductions
-/

namespace BinaryFv.Keccak
open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Local register read/write reductions for the copy_from_slice live path -/

/-- Writing `t1 = x6` via `wX_bits` inserts `x6 ↦ data` and touches nothing else (mirror of
`wX_bits_x13_run`). -/
theorem wX_bits_x6_run (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 6#5) data) s { s with regs := s.regs.insert x6 data } () := by
  have r6Nat : (Sail.BitVec.toNatInt 6#5).toNat = 6 := by decide
  unfold Runs
  simp [wX_bits, wX, PreSail.writeReg, r6Nat,
    EStateM.run, EStateM.bind, EStateM.modifyGet, EStateM.pure, EStateM.instMonad,
    MonadState.modifyGet, MonadStateOf.modifyGet, modify,
    xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
    encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
    LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg]

/-- Reading `a1 = x11` via `rX_bits`. -/
theorem rX_bits_x11_run (s : State) (v : BitVec 64) (h : s.regs.get? x11 = some v) :
    Runs (rX_bits (.Regidx 11#5)) s s v := by
  have r11 : (Sail.BitVec.toNatInt (11#5)).toNat = 11 := by decide
  unfold Runs
  simp [rX_bits, rX, r11, h, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

/-- Reading `t1 = x6` via `rX_bits`. -/
theorem rX_bits_x6_run (s : State) (v : BitVec 64) (h : s.regs.get? x6 = some v) :
    Runs (rX_bits (.Regidx 6#5)) s s v := by
  have r6 : (Sail.BitVec.toNatInt (6#5)).toNat = 6 := by decide
  unfold Runs
  simp [rX_bits, rX, r6, h, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

/-- The `bne a1, a3` branch condition (`.BNE`, `rs1 = a1 = x11`, `rs2 = a3 = x13`) runs to
`a1 != a3`. -/
theorem bTypeTaken_bne_a1_a3_run (s : State) (a1v a3v : BitVec 64)
    (h11 : s.regs.get? x11 = some a1v) (h13 : s.regs.get? x13 = some a3v) :
    Runs (bTypeTaken (.Regidx 13#5) (.Regidx 11#5) .BNE) s s (a1v != a3v) := by
  unfold bTypeTaken
  refine Runs.bind (rX_bits_x11_run s a1v h11) ?_
  refine Runs.bind (rX_bits_x13_run s a3v h13) ?_
  rfl

/-- `sign_extend` of `0#12` vanishes, so `mv rd, rs1 = addi rd, rs1, 0` writes `rs1` unchanged. -/
theorem add_sext_zero (x : BitVec 64) : x + sign_extend (m := 64) (0#12) = x := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  bv_decide

/-- The `auipc t1, 0x0` immediate is zero: `v + sext(0#20 ++ 0x000#12) = v`. -/
theorem add_auipc_zero (x : BitVec 64) :
    x + sign_extend (m := 64) (0#20 ++ 0x000#12) = x := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  bv_decide

end BinaryFv.Keccak
