import BinaryFv.RiscV.Logic.BlockStep

/-!
# Shared generated-register run lemmas

`rX_x<n>_run` and `wX_x<n>_run` say that the generated Sail register read/write actions run and
retire with the obvious result. Every machine-execution module needs the same handful of them.

They live here for the same reason `decode_run` does: two sibling modules each declared the
`gen_rx_run`/`gen_wx_run` `macro`s, and Lean rejects duplicate macro declarations in one
environment, so `BinaryFv.Zesu` — which imports both siblings — failed to elaborate. The generated
theorems themselves did not collide only because one module happened to mark them `private`.

Declaring the macros once and instantiating the union of the indices the siblings need removes both
the macro collision and roughly forty duplicated proofs, and keeps the siblings independent of each
other so Lake can still compile them concurrently.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

/-- The architectural zero register reads as zero without consulting the register map. -/
theorem rX_x0_run (state : State) :
    Runs (rX_bits (.Regidx 0#5)) state state (0#64) := by
  have index : (Sail.BitVec.toNatInt (0#5)).toNat = 0 := by decide
  unfold Runs rX_bits rX
  simp [index, zero_reg, EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad,
    regval_from_reg]
  rfl

local macro "gen_rx_run" idx:num " ↦ " reg:ident ", " name:ident : command =>
  `(theorem $name (state : State) (value : BitVec 64)
      (stored : state.regs.get? $reg = some value) :
      Runs (rX_bits (.Regidx (BitVec.ofNat 5 $idx))) state state value := by
    have index : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [rX_bits, rX, index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
      EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg])

local macro "gen_wx_run" idx:num " ↦ " reg:ident ", " name:ident : command =>
  `(theorem $name (state : State) (value : BitVec 64) :
      Runs (wX_bits (.Regidx (BitVec.ofNat 5 $idx)) value) state
        { state with regs := state.regs.insert $reg value } () := by
    have index : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [wX_bits, wX, PreSail.writeReg, index, EStateM.run, EStateM.bind, EStateM.modifyGet,
      EStateM.pure, EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet, modify,
      xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
      encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
      LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg])

gen_rx_run 1 ↦ x1, rX_x1_run
gen_rx_run 2 ↦ x2, rX_x2_run
gen_rx_run 5 ↦ x5, rX_x5_run
gen_rx_run 6 ↦ x6, rX_x6_run
gen_rx_run 7 ↦ x7, rX_x7_run
gen_rx_run 8 ↦ x8, rX_x8_run
gen_rx_run 9 ↦ x9, rX_x9_run
gen_rx_run 10 ↦ x10, rX_x10_run
gen_rx_run 11 ↦ x11, rX_x11_run
gen_rx_run 12 ↦ x12, rX_x12_run
gen_rx_run 13 ↦ x13, rX_x13_run
gen_rx_run 14 ↦ x14, rX_x14_run
gen_rx_run 15 ↦ x15, rX_x15_run
gen_rx_run 16 ↦ x16, rX_x16_run
gen_rx_run 17 ↦ x17, rX_x17_run
gen_rx_run 28 ↦ x28, rX_x28_run
gen_rx_run 29 ↦ x29, rX_x29_run
gen_rx_run 30 ↦ x30, rX_x30_run

gen_wx_run 1 ↦ x1, wX_x1_run
gen_wx_run 2 ↦ x2, wX_x2_run
gen_wx_run 5 ↦ x5, wX_x5_run
gen_wx_run 6 ↦ x6, wX_x6_run
gen_wx_run 7 ↦ x7, wX_x7_run
gen_wx_run 8 ↦ x8, wX_x8_run
gen_wx_run 9 ↦ x9, wX_x9_run
gen_wx_run 10 ↦ x10, wX_x10_run
gen_wx_run 11 ↦ x11, wX_x11_run
gen_wx_run 12 ↦ x12, wX_x12_run
gen_wx_run 13 ↦ x13, wX_x13_run
gen_wx_run 14 ↦ x14, wX_x14_run
gen_wx_run 15 ↦ x15, wX_x15_run
gen_wx_run 16 ↦ x16, wX_x16_run
gen_wx_run 17 ↦ x17, wX_x17_run
gen_wx_run 18 ↦ x18, wX_x18_run
gen_wx_run 19 ↦ x19, wX_x19_run
gen_wx_run 21 ↦ x21, wX_x21_run
gen_wx_run 22 ↦ x22, wX_x22_run
gen_wx_run 28 ↦ x28, wX_x28_run
gen_wx_run 29 ↦ x29, wX_x29_run
gen_wx_run 30 ↦ x30, wX_x30_run

end BinaryFv.Zesu.MachineExecution
