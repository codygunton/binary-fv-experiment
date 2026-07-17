import BinaryFv.RiscV.Framing

/-!
# Register-only ALU instruction execution contracts

`Runs`-level execution contracts for the generated register-writing ALU instructions used by the
Reth Keccak binary's helper loops and outlined functions:

* `execute_ITYPE` — `ADDI`, `XORI`, `ANDI`, `ORI` (immediate ALU ops; `memcpy`/`memset` use `ADDI`,
  the outlined χ helper uses `XORI`/`ANDI`),
* `execute_RTYPE` — `ADD`, `AND` (the `XOR` case is `Keccak.Contracts.execute_core_xor`),
* `execute_UTYPE` — `AUIPC` (`PC`-relative address formation).

Each is a pure register write `rd := rs1 op operand` with no memory effect.  Following the
control-flow contracts (`ControlFlowStep.execute_JAL_run`), the register reads and the destination
write are threaded as `Runs` premises so `rd`/`rs1`/`rs2` stay fully general.  This also subsumes the
`rd = x0` no-op case: for `rd = x0` the generated `wX_bits x0 _` is a no-op, so the threaded
`wX_bits rd _` premise is satisfied with `sFinal = state`.  The result value in each write premise is
EXACTLY the expression the generated op computes (`sign_extend` is the generated 64-bit sign
extension; the `AUIPC` immediate is `imm ++ 0x000#12` sign-extended, added to `PC`).
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-! ## `execute_ITYPE` (immediate ALU: `rd := rs1 op sign_extend imm`) -/

/-- `execute_ITYPE imm rs1 rd ADDI`: reads `rs1`, writes `rd := rs1 + sign_extend imm`, retires. -/
theorem execute_ITYPE_addi_run (state sFinal : State) (imm : BitVec 12) (rs1 rd : regidx)
    (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (rs1Val + sign_extend (m := 64) imm)) state sFinal ()) :
    Runs (execute_ITYPE imm rs1 rd .ADDI) state sFinal (.Retire_Success ()) := by
  unfold execute_ITYPE
  refine Runs.bind (Runs.bind hrs1 rfl) ?_
  refine Runs.bind hwrite ?_
  rfl

/-- `execute_ITYPE imm rs1 rd XORI`: reads `rs1`, writes `rd := rs1 ^^^ sign_extend imm`, retires.
(The outlined χ `not` is `xori rd, rs1, -1`.) -/
theorem execute_ITYPE_xori_run (state sFinal : State) (imm : BitVec 12) (rs1 rd : regidx)
    (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (rs1Val ^^^ sign_extend (m := 64) imm)) state sFinal ()) :
    Runs (execute_ITYPE imm rs1 rd .XORI) state sFinal (.Retire_Success ()) := by
  unfold execute_ITYPE
  refine Runs.bind (Runs.bind hrs1 rfl) ?_
  refine Runs.bind hwrite ?_
  rfl

/-- `execute_ITYPE imm rs1 rd ANDI`: reads `rs1`, writes `rd := rs1 &&& sign_extend imm`, retires. -/
theorem execute_ITYPE_andi_run (state sFinal : State) (imm : BitVec 12) (rs1 rd : regidx)
    (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (rs1Val &&& sign_extend (m := 64) imm)) state sFinal ()) :
    Runs (execute_ITYPE imm rs1 rd .ANDI) state sFinal (.Retire_Success ()) := by
  unfold execute_ITYPE
  refine Runs.bind (Runs.bind hrs1 rfl) ?_
  refine Runs.bind hwrite ?_
  rfl

/-- `execute_ITYPE imm rs1 rd ORI`: reads `rs1`, writes `rd := rs1 ||| sign_extend imm`, retires. -/
theorem execute_ITYPE_ori_run (state sFinal : State) (imm : BitVec 12) (rs1 rd : regidx)
    (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (rs1Val ||| sign_extend (m := 64) imm)) state sFinal ()) :
    Runs (execute_ITYPE imm rs1 rd .ORI) state sFinal (.Retire_Success ()) := by
  unfold execute_ITYPE
  refine Runs.bind (Runs.bind hrs1 rfl) ?_
  refine Runs.bind hwrite ?_
  rfl

/-! ## `execute_RTYPE` (register ALU: `rd := rs1 op rs2`) -/

/-- `execute_RTYPE rs2 rs1 rd ADD`: reads `rs1` then `rs2`, writes `rd := rs1 + rs2`, retires. -/
theorem execute_RTYPE_add_run (state sFinal : State) (rs2 rs1 rd : regidx)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (rs1Val + rs2Val)) state sFinal ()) :
    Runs (execute_RTYPE rs2 rs1 rd .ADD) state sFinal (.Retire_Success ()) := by
  unfold execute_RTYPE
  refine Runs.bind (Runs.bind hrs1 (Runs.bind hrs2 rfl)) ?_
  refine Runs.bind hwrite ?_
  rfl

/-- `execute_RTYPE rs2 rs1 rd AND`: reads `rs1` then `rs2`, writes `rd := rs1 &&& rs2`, retires. -/
theorem execute_RTYPE_and_run (state sFinal : State) (rs2 rs1 rd : regidx)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (rs1Val &&& rs2Val)) state sFinal ()) :
    Runs (execute_RTYPE rs2 rs1 rd .AND) state sFinal (.Retire_Success ()) := by
  unfold execute_RTYPE
  refine Runs.bind (Runs.bind hrs1 (Runs.bind hrs2 rfl)) ?_
  refine Runs.bind hwrite ?_
  rfl

/-! ## `execute_UTYPE` (`AUIPC`: `rd := PC + sign_extend (imm ++ 0x000)`) -/

/-- `execute_UTYPE imm rd AUIPC`: reads `PC` (via `get_arch_pc`), writes
`rd := PC + sign_extend (imm ++ 0x000#12)`, retires.  The `off` addend is the generated
`sign_extend (m := 64) (imm ++ 0x000#12)`, i.e. the 20-bit immediate shifted left 12 bits and
sign-extended to 64 bits. -/
theorem execute_UTYPE_auipc_run (state sFinal : State) (imm : BitVec 20) (rd : regidx)
    (pcVal : BitVec 64)
    (hpc : Runs (readReg PC) state state pcVal)
    (hwrite : Runs (wX_bits rd (pcVal + sign_extend (m := 64) (imm ++ 0x000#12)))
      state sFinal ()) :
    Runs (execute_UTYPE imm rd .AUIPC) state sFinal (.Retire_Success ()) := by
  unfold execute_UTYPE get_arch_pc
  refine Runs.bind (Runs.bind hpc rfl) ?_
  refine Runs.bind hwrite ?_
  rfl

end BinaryFv.RiscV
