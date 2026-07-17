import BinaryFv.RiscV.Instruction.Execute.ShiftOr

/-!
# Uniform integer execution contracts

The Zesu artifact uses most of RV64I's register-only integer instructions.  Rather than duplicate
one `Runs` proof per mnemonic, this module factors the generated result expressions into small
functions and proves one contract for each generated instruction family.  A caller supplies the
ordinary register-read and register-write runs; the theorem then establishes the exact generated
`execute` action and successful retirement.

Memory, control-flow, and terminal instructions remain in their dedicated contract modules because
their generated semantics have observably different state effects.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated RV64 immediate-integer result for a value already read from `rs1`. -/
def iTypeResult (op : iop) (imm : BitVec 12) (rs1Val : BitVec 64) : BitVec 64 :=
  let immext := sign_extend (m := 64) imm
  match op with
  | .ADDI => rs1Val + immext
  | .SLTI => zero_extend (m := 64) (bool_to_bit (zopz0zI_s rs1Val immext))
  | .SLTIU => zero_extend (m := 64) (bool_to_bit (zopz0zI_u rs1Val immext))
  | .XORI => rs1Val ^^^ immext
  | .ORI => rs1Val ||| immext
  | .ANDI => rs1Val &&& immext

/-- All six generated `execute_ITYPE` cases share one register-read/write contract. -/
theorem execute_ITYPE_run (state sFinal : State) (imm : BitVec 12) (rs1 rd : regidx) (op : iop)
    (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (iTypeResult op imm rs1Val)) state sFinal ()) :
    Runs (execute_ITYPE imm rs1 rd op) state sFinal (.Retire_Success ()) := by
  cases op <;> simp only [iTypeResult] at hwrite
  all_goals
    unfold execute_ITYPE
    refine Runs.bind (Runs.bind hrs1 rfl) ?_
    refine Runs.bind hwrite ?_
    rfl

/-- The generated RV64 register-integer result for values already read from `rs1` and `rs2`. -/
def rTypeResult (op : rop) (rs1Val rs2Val : BitVec 64) : BitVec 64 :=
  match op with
  | .ADD => rs1Val + rs2Val
  | .SUB => rs1Val - rs2Val
  | .SLL => Sail.shift_bits_left rs1Val
      (Sail.BitVec.extractLsb rs2Val (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  | .SLT => zero_extend (m := 64) (bool_to_bit (zopz0zI_s rs1Val rs2Val))
  | .SLTU => zero_extend (m := 64) (bool_to_bit (zopz0zI_u rs1Val rs2Val))
  | .XOR => rs1Val ^^^ rs2Val
  | .SRL => Sail.shift_bits_right rs1Val
      (Sail.BitVec.extractLsb rs2Val (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  | .SRA => shift_bits_right_arith rs1Val
      (Sail.BitVec.extractLsb rs2Val (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  | .OR => rs1Val ||| rs2Val
  | .AND => rs1Val &&& rs2Val

/-- All ten generated `execute_RTYPE` cases share one register-read/write contract. -/
theorem execute_RTYPE_run (state sFinal : State) (rs2 rs1 rd : regidx) (op : rop)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (rTypeResult op rs1Val rs2Val)) state sFinal ()) :
    Runs (execute_RTYPE rs2 rs1 rd op) state sFinal (.Retire_Success ()) := by
  cases op <;> simp only [rTypeResult] at hwrite
  all_goals
    unfold execute_RTYPE
    refine Runs.bind (Runs.bind hrs1 (Runs.bind hrs2 rfl)) ?_
    refine Runs.bind hwrite ?_
    rfl

/-- The generated immediate-shift result for a value already read from `rs1`. -/
def shiftIopResult (op : sop) (shamt : BitVec 6) (rs1Val : BitVec 64) : BitVec 64 :=
  let amount := Sail.BitVec.extractLsb shamt (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0
  match op with
  | .SLLI => Sail.shift_bits_left rs1Val amount
  | .SRLI => Sail.shift_bits_right rs1Val amount
  | .SRAI => shift_bits_right_arith rs1Val amount

/-- All generated immediate shifts share one register-read/write contract. -/
theorem execute_SHIFTIOP_run (state sFinal : State) (shamt : BitVec 6) (rs1 rd : regidx)
    (op : sop) (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (shiftIopResult op shamt rs1Val)) state sFinal ()) :
    Runs (execute_SHIFTIOP shamt rs1 rd op) state sFinal (.Retire_Success ()) := by
  cases op <;> simp only [shiftIopResult] at hwrite
  all_goals
    unfold execute_SHIFTIOP
    refine Runs.bind (Runs.bind hrs1 rfl) ?_
    refine Runs.bind hwrite ?_
    rfl

/-- `lui` writes the sign-extended immediate and retires. -/
theorem execute_UTYPE_lui_run (state sFinal : State) (imm : BitVec 20) (rd : regidx)
    (hwrite : Runs (wX_bits rd (sign_extend (m := 64) (imm ++ 0x000#12))) state sFinal ()) :
    Runs (execute_UTYPE imm rd .LUI) state sFinal (.Retire_Success ()) := by
  unfold execute_UTYPE
  refine Runs.bind (by rfl) ?_
  refine Runs.bind hwrite ?_
  rfl

end BinaryFv.RiscV
