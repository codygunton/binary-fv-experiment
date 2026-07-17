import BinaryFv.Keccak.SpecBridge.Lanes
import BinaryFv.Keccak.Reth.Proof.Helpers.Memcpy
import BinaryFv.Keccak.Reth.Proof.XorBlock.Decode
import BinaryFv.Keccak.Reth.Proof.XorBlock.Fetch
import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import Spec.Keccak.Keccak256

/-!
# `xor_block` execute contracts and register reductions
-/

namespace BinaryFv.Keccak.XorBlock
open BinaryFv.Binary
open BinaryFv.Keccak.SpecBridge
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open BinaryFv.Keccak
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Deliverable 1a: the `xor` execute contract

`execute_RTYPE rs2 rs1 rd XOR` computes `rs1 ^^^ rs2`, mirroring `execute_RTYPE_or_run`. -/

theorem execute_RTYPE_xor_run (state sFinal : State) (rs2 rs1 rd : regidx)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (rs1Val ^^^ rs2Val)) state sFinal ()) :
    Runs (execute_RTYPE rs2 rs1 rd .XOR) state sFinal (.Retire_Success ()) := by
  unfold execute_RTYPE
  refine Runs.bind (Runs.bind hrs1 (Runs.bind hrs2 rfl)) ?_
  refine Runs.bind hwrite ?_
  rfl

/-! ## Deliverable 1b: register read/write reductions

The body reads/writes the ABI registers `t0 = x5`, `a0..a7 = x10..x17`.  Each `rX_bits`/`wX_bits`
reduction is the memcpy pattern specialized to the concrete register index, generated uniformly by a
local macro. -/

local macro "gen_reg_lemmas" idx:num " ↦ " reg:ident " , " rname:ident " , " wname:ident : command =>
  `(theorem $rname (s : State) (v : BitVec 64) (h : s.regs.get? $reg = some v) :
      Runs (rX_bits (.Regidx (BitVec.ofNat 5 $idx))) s s v := by
    have rk : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [rX_bits, rX, rk, h, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
      regval_from_reg]

  theorem $wname (s : State) (data : BitVec 64) :
      Runs (wX_bits (.Regidx (BitVec.ofNat 5 $idx)) data) s
        { s with regs := s.regs.insert $reg data } () := by
    have rk : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [wX_bits, wX, PreSail.writeReg, rk, EStateM.run, EStateM.bind, EStateM.modifyGet,
      EStateM.pure, EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet, modify,
      xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
      encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
      LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg])

gen_reg_lemmas 5 ↦ x5 , rX_x5_run , wX_x5_run
gen_reg_lemmas 10 ↦ x10 , rX_x10_run , wX_x10_run
gen_reg_lemmas 11 ↦ x11 , rX_x11_run , wX_x11_run
gen_reg_lemmas 12 ↦ x12 , rX_x12_run , wX_x12_run
gen_reg_lemmas 13 ↦ x13 , rX_x13_run , wX_x13_run
gen_reg_lemmas 14 ↦ x14 , rX_x14_run , wX_x14_run
gen_reg_lemmas 15 ↦ x15 , rX_x15_run , wX_x15_run
gen_reg_lemmas 16 ↦ x16 , rX_x16_run , wX_x16_run
gen_reg_lemmas 17 ↦ x17 , rX_x17_run , wX_x17_run

/-! ## Deliverable 1c: normalizing the generated shift amount

The generated `SLLI` write value is `shift_bits_left x (extractLsb sh (log2_xlen -i 1) 0)`; on RV64
`log2_xlen = 6`, so the shift count is the low 6 bits of the 6-bit immediate `sh` — i.e. `sh` itself.
This normalizes it to the plain `x <<< sh.toNat`. -/

theorem slli_amount (x : BitVec 64) (sh : BitVec 6) :
    Sail.shift_bits_left x
      (Sail.BitVec.extractLsb sh (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
      = x <<< sh.toNat := by
  have hhi : (LeanRV64DExecutable.Functions.log2_xlen -i 1) = 5 := rfl
  rw [hhi]
  unfold Sail.shift_bits_left Sail.BitVec.extractLsb
  bv_decide

end BinaryFv.Keccak.XorBlock
