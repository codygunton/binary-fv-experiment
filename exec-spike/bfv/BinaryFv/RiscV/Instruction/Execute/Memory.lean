import BinaryFv.RiscV.Instruction.Execute.Load

/-!
# Width-polymorphic memory execution contracts

The generated `execute_LOAD` and `execute_STORE` dispatchers differ only in their width, signedness,
and the data-access action they invoke.  These contracts factor that common dispatcher proof so the
remaining Zesu half- and word-width mnemonics use the same kernel-checked path as the existing byte
and double-word memory contracts.  The concrete translation, PMP, MMIO, and byte-ownership facts
remain explicit `vmem_read`/`vmem_write` premises for the artifact-specific proof layer.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open MemoryAccessType
open mem_payload
open Register

/-- A generated assertion with a true condition is a state-preserving successful action. -/
private theorem assertCondition_true_run (s : State) (condition : Bool) (message : String)
    (holds : condition = true) :
    Runs (PreSail.assert condition message) s s () := by
  unfold PreSail.assert Runs
  simp only [holds, ↓reduceIte]
  rfl

/-- Any successful generated virtual-memory load lifts through `execute_LOAD` and retires. -/
theorem execute_LOAD_run (s s' : State) (imm : BitVec 12) (rs1 rd : regidx) (isUnsigned : Bool)
    (width : Nat) (data : BitVec (8 * width))
    (widthFits : (width ≤b LeanRV64DExecutable.Functions.xlen_bytes) = true)
    (hread : Runs (vmem_read rs1 (sign_extend (m := 64) imm) width (Load Data) false false false)
      s s (.Ok data))
    (hwrite : Runs (wX_bits rd (extend_value isUnsigned data)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd isUnsigned width) s s' (.Retire_Success ()) := by
  unfold execute_LOAD
  refine Runs.bind (assertCondition_true_run s _ _ widthFits) ?_
  refine Runs.bind hread ?_
  refine Runs.bind hwrite ?_
  rfl

/-- Any successful generated virtual-memory store lifts through `execute_STORE` and retires. -/
theorem execute_STORE_run (s s' : State) (imm : BitVec 12) (rs2 rs1 : regidx) (width : Nat)
    (data : BitVec 64)
    (widthFits : (width ≤b LeanRV64DExecutable.Functions.xlen_bytes) = true)
    (hdata : Runs (rX_bits rs2) s s data)
    (hwrite : Runs (vmem_write rs1 (sign_extend (m := 64) imm) width
      (BitVec.setWidth (8 * width) (Sail.BitVec.extractLsb data ((width *i 8) -i 1) 0))
      (Store Data) false false false)
      s s' (.Ok true)) :
    Runs (execute_STORE imm rs2 rs1 width) s s' (.Retire_Success ()) := by
  unfold execute_STORE
  refine Runs.bind (assertCondition_true_run s _ _ widthFits) ?_
  refine Runs.bind hdata ?_
  refine Runs.bind (by rfl) ?_
  refine Runs.bind hwrite ?_
  rfl

/-- `lhu` is the unsigned width-two specialization of `execute_LOAD_run`. -/
theorem execute_LOAD_lhu_run (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (data : BitVec 16)
    (hread : Runs (vmem_read rs1 (sign_extend (m := 64) imm) 2 (Load Data) false false false)
      s s (.Ok data))
    (hwrite : Runs (wX_bits rd (extend_value true data)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 2) s s' (.Retire_Success ()) :=
  execute_LOAD_run s s' imm rs1 rd true 2 data (by decide) hread hwrite

/-- `lw` is the signed width-four specialization of `execute_LOAD_run`. -/
theorem execute_LOAD_lw_run (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (data : BitVec 32)
    (hread : Runs (vmem_read rs1 (sign_extend (m := 64) imm) 4 (Load Data) false false false)
      s s (.Ok data))
    (hwrite : Runs (wX_bits rd (extend_value false data)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd false 4) s s' (.Retire_Success ()) :=
  execute_LOAD_run s s' imm rs1 rd false 4 data (by decide) hread hwrite

/-- `sh` is the width-two specialization of `execute_STORE_run`. -/
theorem execute_STORE_half_run (s s' : State) (imm : BitVec 12) (rs2 rs1 : regidx)
    (data : BitVec 64)
    (hdata : Runs (rX_bits rs2) s s data)
    (hwrite : Runs (vmem_write rs1 (sign_extend (m := 64) imm) 2
      (Sail.BitVec.extractLsb data 15 0) (Store Data) false false false) s s' (.Ok true)) :
    Runs (execute_STORE imm rs2 rs1 2) s s' (.Retire_Success ()) :=
  execute_STORE_run s s' imm rs2 rs1 2 data (by decide) hdata (by simpa using hwrite)

/-- `sw` is the width-four specialization of `execute_STORE_run`. -/
theorem execute_STORE_word_run (s s' : State) (imm : BitVec 12) (rs2 rs1 : regidx)
    (data : BitVec 64)
    (hdata : Runs (rX_bits rs2) s s data)
    (hwrite : Runs (vmem_write rs1 (sign_extend (m := 64) imm) 4
      (Sail.BitVec.extractLsb data 31 0) (Store Data) false false false) s s' (.Ok true)) :
    Runs (execute_STORE imm rs2 rs1 4) s s' (.Retire_Success ()) :=
  execute_STORE_run s s' imm rs2 rs1 4 data (by decide) hdata (by simpa using hwrite)

end BinaryFv.RiscV
