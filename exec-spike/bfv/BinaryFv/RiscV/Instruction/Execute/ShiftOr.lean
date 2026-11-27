import BinaryFv.RiscV.Logic.Framing

/-!
# Shift-immediate and bitwise-or execution contracts

`Runs`-level execution contracts for the two generated instruction classes the `xor_block` loop
(stage 5) needs beyond the register/immediate ALU contracts already present in
`RegisterOpExecuteContract`:

* `execute_RTYPE` — `OR` (register bitwise-or; the exact analogue of the existing `AND` contract),
* `execute_SHIFTIOP` — `SLLI` (shift-left-immediate).

Following the register-op contracts, the register reads and the destination write are threaded as
`Runs` premises so `rd`/`rs1`/`rs2` stay fully general (this also subsumes the `rd = x0` no-op case).
The result value in each write premise is EXACTLY the expression the generated op computes: for `OR`
the bitwise-or `rs1Val ||| rs2Val`, and for `SLLI` the generated
`Sail.shift_bits_left rs1Val (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)` — i.e. `rs1Val`
left-shifted by the low `log2_xlen` bits of the 6-bit shift amount.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-! ## `execute_RTYPE` (register bitwise-or: `rd := rs1 ||| rs2`) -/

/-- `execute_RTYPE rs2 rs1 rd OR`: reads `rs1` then `rs2`, writes `rd := rs1 ||| rs2`, retires. -/
theorem execute_RTYPE_or_run (state sFinal : State) (rs2 rs1 rd : regidx)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (rs1Val ||| rs2Val)) state sFinal ()) :
    Runs (execute_RTYPE rs2 rs1 rd .OR) state sFinal (.Retire_Success ()) := by
  unfold execute_RTYPE
  refine Runs.bind (Runs.bind hrs1 (Runs.bind hrs2 rfl)) ?_
  refine Runs.bind hwrite ?_
  rfl

/-! ## `execute_SHIFTIOP` (`SLLI`: `rd := shift_bits_left rs1 (extractLsb shamt (log2_xlen-1) 0)`) -/

/-- `execute_SHIFTIOP shamt rs1 rd SLLI`: reads `rs1`, writes
`rd := shift_bits_left rs1 (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)`, retires.  The shift
count is the generated `Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0`, i.e. the low `log2_xlen`
bits of the 6-bit immediate `shamt`. -/
theorem execute_SHIFTIOP_slli_run (state sFinal : State) (shamt : BitVec 6) (rs1 rd : regidx)
    (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd
      (Sail.shift_bits_left rs1Val
        (Sail.BitVec.extractLsb shamt (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
      state sFinal ()) :
    Runs (execute_SHIFTIOP shamt rs1 rd .SLLI) state sFinal (.Retire_Success ()) := by
  unfold execute_SHIFTIOP
  refine Runs.bind (Runs.bind hrs1 rfl) ?_
  refine Runs.bind hwrite ?_
  rfl

end BinaryFv.RiscV
