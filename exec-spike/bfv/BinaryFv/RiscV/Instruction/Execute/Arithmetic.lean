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

/-- The generated full-width M-extension multiplication result. -/
def mulResult (op : mul_op) (rs1Val rs2Val : BitVec 64) : BitVec 64 :=
  mult_to_bits_half (l := LeanRV64DExecutable.Functions.xlen) op.signed_rs1 op.signed_rs2
    rs1Val rs2Val op.result_part

/-- Every generated full-width M-extension multiply variant shares one contract. -/
theorem execute_MUL_run (state sFinal : State) (rs2 rs1 rd : regidx) (op : mul_op)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (mulResult op rs1Val rs2Val)) state sFinal ()) :
    Runs (execute_MUL rs2 rs1 rd op) state sFinal (.Retire_Success ()) := by
  have calculated : Runs
      (rX_bits rs1 >>= fun rs1Value =>
        rX_bits rs2 >>= fun rs2Value =>
          wX_bits rd (mulResult op rs1Value rs2Value) >>= fun _ => pure RETIRE_SUCCESS)
      state sFinal (.Retire_Success ()) :=
    Runs.bind hrs1 (Runs.bind hrs2 (Runs.bind hwrite rfl))
  simpa only [execute_MUL, mulResult] using calculated

/-- The generated full-width division result, including the RISC-V divide-by-zero and overflow rules. -/
def divResult (isUnsigned : Bool) (rs1Bits rs2Bits : BitVec 64) : BitVec 64 :=
  let rs1Int := if isUnsigned then Sail.BitVec.toNatInt rs1Bits else BitVec.toInt rs1Bits
  let rs2Int := if isUnsigned then Sail.BitVec.toNatInt rs2Bits else BitVec.toInt rs2Bits
  let quotient := if rs2Int == 0 then -1 else Int.tdiv rs1Int rs2Int
  let quotient := if (LeanRV64DExecutable.Functions.not isUnsigned) && (quotient ≥b (2 ^i
      (LeanRV64DExecutable.Functions.xlen -i 1)))
    then -(2 ^i (LeanRV64DExecutable.Functions.xlen -i 1)) else quotient
  to_bits_truncate (l := 64) quotient

/-- Both generated full-width division variants share one contract. -/
theorem execute_DIV_run (state sFinal : State) (rs2 rs1 rd : regidx) (isUnsigned : Bool)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (divResult isUnsigned rs1Val rs2Val)) state sFinal ()) :
    Runs (execute_DIV rs2 rs1 rd isUnsigned) state sFinal (.Retire_Success ()) := by
  have calculated : Runs
      (rX_bits rs1 >>= fun rs1Value =>
        rX_bits rs2 >>= fun rs2Value =>
          wX_bits rd (divResult isUnsigned rs1Value rs2Value) >>= fun _ => pure RETIRE_SUCCESS)
      state sFinal (.Retire_Success ()) :=
    Runs.bind hrs1 (Runs.bind hrs2 (Runs.bind hwrite rfl))
  simpa only [execute_DIV, divResult] using calculated

/-- The generated full-width remainder result, including the RISC-V divide-by-zero rule. -/
def remResult (isUnsigned : Bool) (rs1Bits rs2Bits : BitVec 64) : BitVec 64 :=
  let rs1Int := if isUnsigned then Sail.BitVec.toNatInt rs1Bits else BitVec.toInt rs1Bits
  let rs2Int := if isUnsigned then Sail.BitVec.toNatInt rs2Bits else BitVec.toInt rs2Bits
  let remainder := if rs2Int == 0 then rs1Int else Int.tmod rs1Int rs2Int
  to_bits_truncate (l := 64) remainder

/-- Both generated full-width remainder variants share one contract. -/
theorem execute_REM_run (state sFinal : State) (rs2 rs1 rd : regidx) (isUnsigned : Bool)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (remResult isUnsigned rs1Val rs2Val)) state sFinal ()) :
    Runs (execute_REM rs2 rs1 rd isUnsigned) state sFinal (.Retire_Success ()) := by
  have calculated : Runs
      (rX_bits rs1 >>= fun rs1Value =>
        rX_bits rs2 >>= fun rs2Value =>
          wX_bits rd (remResult isUnsigned rs1Value rs2Value) >>= fun _ => pure RETIRE_SUCCESS)
      state sFinal (.Retire_Success ()) :=
    Runs.bind hrs1 (Runs.bind hrs2 (Runs.bind hwrite rfl))
  simpa only [execute_REM, remResult] using calculated

/-- Both generated RV64 word division variants, including `divuw`, share this exact contract. -/
theorem execute_DIVW_run (state sFinal : State) (rs2 rs1 rd : regidx) (isUnsigned : Bool)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd
      (let rs1Bits := Sail.BitVec.extractLsb rs1Val 31 0
       let rs2Bits := Sail.BitVec.extractLsb rs2Val 31 0
       let rs1Int := if isUnsigned then Sail.BitVec.toNatInt rs1Bits else BitVec.toInt rs1Bits
       let rs2Int := if isUnsigned then Sail.BitVec.toNatInt rs2Bits else BitVec.toInt rs2Bits
       let quotient := if rs2Int == 0 then -1 else Int.tdiv rs1Int rs2Int
       let quotient := if (LeanRV64DExecutable.Functions.not isUnsigned) &&
           (quotient ≥b (2 ^i 31)) then -(2 ^i 31) else quotient
       sign_extend (m := 64) (to_bits_truncate (l := 32) quotient))) state sFinal ()) :
    Runs (execute_DIVW rs2 rs1 rd isUnsigned) state sFinal (.Retire_Success ()) := by
  have calculated : Runs
      (rX_bits rs1 >>= fun rs1Value =>
        pure (Sail.BitVec.extractLsb rs1Value 31 0) >>= fun rs1Bits =>
          rX_bits rs2 >>= fun rs2Value =>
            pure (Sail.BitVec.extractLsb rs2Value 31 0) >>= fun rs2Bits =>
              wX_bits rd
                (let rs1Int := if isUnsigned then Sail.BitVec.toNatInt rs1Bits else BitVec.toInt rs1Bits
                 let rs2Int := if isUnsigned then Sail.BitVec.toNatInt rs2Bits else BitVec.toInt rs2Bits
                 let quotient := if rs2Int == 0 then -1 else Int.tdiv rs1Int rs2Int
                 let quotient := if (LeanRV64DExecutable.Functions.not isUnsigned) &&
                     (quotient ≥b (2 ^i 31)) then -(2 ^i 31) else quotient
                 sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)) >>= fun _ =>
                  pure RETIRE_SUCCESS)
      state sFinal (.Retire_Success ()) :=
    Runs.bind hrs1 (Runs.bind rfl (Runs.bind hrs2 (Runs.bind rfl (Runs.bind hwrite rfl))))
  simpa only [execute_DIVW] using calculated

/-- Both generated RV64 word remainder variants, including `remuw`, share this exact contract. -/
theorem execute_REMW_run (state sFinal : State) (rs2 rs1 rd : regidx) (isUnsigned : Bool)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd
      (let rs1Bits := Sail.BitVec.extractLsb rs1Val 31 0
       let rs2Bits := Sail.BitVec.extractLsb rs2Val 31 0
       let rs1Int := if isUnsigned then Sail.BitVec.toNatInt rs1Bits else BitVec.toInt rs1Bits
       let rs2Int := if isUnsigned then Sail.BitVec.toNatInt rs2Bits else BitVec.toInt rs2Bits
       let remainder := if rs2Int == 0 then rs1Int else Int.tmod rs1Int rs2Int
       sign_extend (m := 64) (to_bits_truncate (l := 32) remainder))) state sFinal ()) :
    Runs (execute_REMW rs2 rs1 rd isUnsigned) state sFinal (.Retire_Success ()) := by
  have calculated : Runs
      (rX_bits rs1 >>= fun rs1Value =>
        pure (Sail.BitVec.extractLsb rs1Value 31 0) >>= fun rs1Bits =>
          rX_bits rs2 >>= fun rs2Value =>
            pure (Sail.BitVec.extractLsb rs2Value 31 0) >>= fun rs2Bits =>
              wX_bits rd
                (let rs1Int := if isUnsigned then Sail.BitVec.toNatInt rs1Bits else BitVec.toInt rs1Bits
                 let rs2Int := if isUnsigned then Sail.BitVec.toNatInt rs2Bits else BitVec.toInt rs2Bits
                 let remainder := if rs2Int == 0 then rs1Int else Int.tmod rs1Int rs2Int
                 sign_extend (m := 64) (to_bits_truncate (l := 32) remainder)) >>= fun _ =>
                  pure RETIRE_SUCCESS)
      state sFinal (.Retire_Success ()) :=
    Runs.bind hrs1 (Runs.bind rfl (Runs.bind hrs2 (Runs.bind rfl (Runs.bind hwrite rfl))))
  simpa only [execute_REMW] using calculated

/-- The generated `addiw` result: add at XLEN, retain its low word, then sign-extend it. -/
def addiwResult (imm : BitVec 12) (rs1Val : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb (rs1Val + sign_extend (m := 64) imm) 31 0)

/-- `addiw` has the generated word-truncation adapter between its register read and write. -/
theorem execute_ADDIW_run (state sFinal : State) (imm : BitVec 12) (rs1 rd : regidx)
    (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (addiwResult imm rs1Val)) state sFinal ()) :
    Runs (execute_ADDIW imm rs1 rd) state sFinal (.Retire_Success ()) := by
  simp only [addiwResult] at hwrite
  have calculated : Runs
      (rX_bits rs1 >>= fun rs1Val =>
        pure (rs1Val + sign_extend (m := 64) imm) >>= fun result =>
          wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb result 31 0)) >>= fun _ =>
            pure RETIRE_SUCCESS)
      state sFinal (.Retire_Success ()) :=
    Runs.bind hrs1 (Runs.bind rfl (Runs.bind hwrite rfl))
  simpa only [execute_ADDIW] using calculated

/-- The generated RV64 word-register result, sign-extended back to XLEN. -/
def rTypeWResult (op : ropw) (rs1Val rs2Val : BitVec 64) : BitVec 64 :=
  let rs1Word := Sail.BitVec.extractLsb rs1Val 31 0
  let rs2Word := Sail.BitVec.extractLsb rs2Val 31 0
  let result :=
    match op with
    | .ADDW => rs1Word + rs2Word
    | .SUBW => rs1Word - rs2Word
    | .SLLW => Sail.shift_bits_left rs1Word (Sail.BitVec.extractLsb rs2Word 4 0)
    | .SRLW => Sail.shift_bits_right rs1Word (Sail.BitVec.extractLsb rs2Word 4 0)
    | .SRAW => shift_bits_right_arith rs1Word (Sail.BitVec.extractLsb rs2Word 4 0)
  sign_extend (m := 64) result

/- All generated RV64 word-register arithmetic variants share one contract. -/
theorem execute_RTYPEW_run (state sFinal : State) (rs2 rs1 rd : regidx) (op : ropw)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (rTypeWResult op rs1Val rs2Val)) state sFinal ()) :
    Runs (execute_RTYPEW rs2 rs1 rd op) state sFinal (.Retire_Success ()) := by
  cases op <;> simp only [rTypeWResult] at hwrite
  · have calculated : Runs
        (rX_bits rs1 >>= fun rs1Value =>
          pure (Sail.BitVec.extractLsb rs1Value 31 0) >>= fun rs1Word =>
            rX_bits rs2 >>= fun rs2Value =>
              pure (Sail.BitVec.extractLsb rs2Value 31 0) >>= fun rs2Word =>
                wX_bits rd (sign_extend (m := 64) (rs1Word + rs2Word)) >>= fun _ =>
                  pure RETIRE_SUCCESS)
        state sFinal (.Retire_Success ()) :=
      Runs.bind hrs1 (Runs.bind rfl (Runs.bind hrs2 (Runs.bind rfl (Runs.bind hwrite rfl))))
    simpa only [execute_RTYPEW] using calculated
  · have calculated : Runs
        (rX_bits rs1 >>= fun rs1Value =>
          pure (Sail.BitVec.extractLsb rs1Value 31 0) >>= fun rs1Word =>
            rX_bits rs2 >>= fun rs2Value =>
              pure (Sail.BitVec.extractLsb rs2Value 31 0) >>= fun rs2Word =>
                wX_bits rd (sign_extend (m := 64) (rs1Word - rs2Word)) >>= fun _ =>
                  pure RETIRE_SUCCESS)
        state sFinal (.Retire_Success ()) :=
      Runs.bind hrs1 (Runs.bind rfl (Runs.bind hrs2 (Runs.bind rfl (Runs.bind hwrite rfl))))
    simpa only [execute_RTYPEW] using calculated
  · have calculated : Runs
        (rX_bits rs1 >>= fun rs1Value =>
          pure (Sail.BitVec.extractLsb rs1Value 31 0) >>= fun rs1Word =>
            rX_bits rs2 >>= fun rs2Value =>
              pure (Sail.BitVec.extractLsb rs2Value 31 0) >>= fun rs2Word =>
                wX_bits rd (sign_extend (m := 64)
                  (Sail.shift_bits_left rs1Word (Sail.BitVec.extractLsb rs2Word 4 0))) >>= fun _ =>
                    pure RETIRE_SUCCESS)
        state sFinal (.Retire_Success ()) :=
      Runs.bind hrs1 (Runs.bind rfl (Runs.bind hrs2 (Runs.bind rfl (Runs.bind hwrite rfl))))
    simpa only [execute_RTYPEW] using calculated
  · have calculated : Runs
        (rX_bits rs1 >>= fun rs1Value =>
          pure (Sail.BitVec.extractLsb rs1Value 31 0) >>= fun rs1Word =>
            rX_bits rs2 >>= fun rs2Value =>
              pure (Sail.BitVec.extractLsb rs2Value 31 0) >>= fun rs2Word =>
                wX_bits rd (sign_extend (m := 64)
                  (Sail.shift_bits_right rs1Word (Sail.BitVec.extractLsb rs2Word 4 0))) >>= fun _ =>
                    pure RETIRE_SUCCESS)
        state sFinal (.Retire_Success ()) :=
      Runs.bind hrs1 (Runs.bind rfl (Runs.bind hrs2 (Runs.bind rfl (Runs.bind hwrite rfl))))
    simpa only [execute_RTYPEW] using calculated
  · have calculated : Runs
        (rX_bits rs1 >>= fun rs1Value =>
          pure (Sail.BitVec.extractLsb rs1Value 31 0) >>= fun rs1Word =>
            rX_bits rs2 >>= fun rs2Value =>
              pure (Sail.BitVec.extractLsb rs2Value 31 0) >>= fun rs2Word =>
                wX_bits rd (sign_extend (m := 64)
                  (shift_bits_right_arith rs1Word (Sail.BitVec.extractLsb rs2Word 4 0))) >>= fun _ =>
                    pure RETIRE_SUCCESS)
        state sFinal (.Retire_Success ()) :=
      Runs.bind hrs1 (Runs.bind rfl (Runs.bind hrs2 (Runs.bind rfl (Runs.bind hwrite rfl))))
    simpa only [execute_RTYPEW] using calculated

/-- The generated RV64 word immediate-shift result, sign-extended back to XLEN. -/
def shiftIWopResult (op : sopw) (shamt : BitVec 5) (rs1Val : BitVec 64) : BitVec 64 :=
  let rs1Word := Sail.BitVec.extractLsb rs1Val 31 0
  let result :=
    match op with
    | .SLLIW => Sail.shift_bits_left rs1Word shamt
    | .SRLIW => Sail.shift_bits_right rs1Word shamt
    | .SRAIW => shift_bits_right_arith rs1Word shamt
  sign_extend (m := 64) result

/- All generated RV64 word immediate-shift variants share one contract. -/
theorem execute_SHIFTIWOP_run (state sFinal : State) (shamt : BitVec 5) (rs1 rd : regidx)
    (op : sopw) (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (shiftIWopResult op shamt rs1Val)) state sFinal ()) :
    Runs (execute_SHIFTIWOP shamt rs1 rd op) state sFinal (.Retire_Success ()) := by
  cases op <;> simp only [shiftIWopResult] at hwrite
  · have calculated : Runs
        (rX_bits rs1 >>= fun rs1Value =>
          pure (Sail.BitVec.extractLsb rs1Value 31 0) >>= fun rs1Word =>
            wX_bits rd (sign_extend (m := 64) (Sail.shift_bits_left rs1Word shamt)) >>= fun _ =>
              pure RETIRE_SUCCESS)
        state sFinal (.Retire_Success ()) :=
      Runs.bind hrs1 (Runs.bind rfl (Runs.bind hwrite rfl))
    simpa only [execute_SHIFTIWOP] using calculated
  · have calculated : Runs
        (rX_bits rs1 >>= fun rs1Value =>
          pure (Sail.BitVec.extractLsb rs1Value 31 0) >>= fun rs1Word =>
            wX_bits rd (sign_extend (m := 64) (Sail.shift_bits_right rs1Word shamt)) >>= fun _ =>
              pure RETIRE_SUCCESS)
        state sFinal (.Retire_Success ()) :=
      Runs.bind hrs1 (Runs.bind rfl (Runs.bind hwrite rfl))
    simpa only [execute_SHIFTIWOP] using calculated
  · have calculated : Runs
        (rX_bits rs1 >>= fun rs1Value =>
          pure (Sail.BitVec.extractLsb rs1Value 31 0) >>= fun rs1Word =>
            wX_bits rd (sign_extend (m := 64) (shift_bits_right_arith rs1Word shamt)) >>= fun _ =>
              pure RETIRE_SUCCESS)
        state sFinal (.Retire_Success ()) :=
      Runs.bind hrs1 (Runs.bind rfl (Runs.bind hwrite rfl))
    simpa only [execute_SHIFTIWOP] using calculated

end BinaryFv.RiscV
