import BinaryFv.RiscV.Logic.Framing

/-!
# Control-flow instruction execution contracts

`Runs`-level execution contracts for the generated control-flow instructions `execute_JAL`,
`execute_JALR`, `execute_BTYPE` (taken and not-taken), and the `ret` special case
(`jalr x0, 0(x1)`).  These are the control-flow analogue of `execute_STORE_dword_run`
(`StoreExecuteContract`): they pin the concrete post-state produced by threading `jump_to`
(the `set_next_pc` update of `nextPC`) and the `wX_bits` link write.

The genuine platform checks are abstracted as clean `Runs` preconditions exactly as the store
and fetch contracts do:

* `ext_control_check_pc` reduces to `none` definitionally, so it is discharged internally, not
  hypothesised.
* `currentlyEnabled Ext_Zca` reads `misa`; the alignment precondition `target[1] = 0` forces the
  `jump_to` `if` into its else branch (`false && _ = false`), but the extension read is still
  threaded through the state, so a minimal `Runs (currentlyEnabled Ext_Zca) s s _` premise is kept.
* `update_elp_state rs1` reads `Ext_Zicfilp`; it is threaded as a
  `Runs (update_elp_state rs1) s s ()` premise, a no-op when Zicfilp is disabled (RV64IM config).
* the `wX_bits rd link` register write is threaded as a `Runs (wX_bits rd link) · · ()` premise,
  keeping `rd` fully general; for `rd = x0` it is a proved no-op (`ret`).
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-! ## `RunsME`: a `Runs` calculus for the `SailME` error monad (jump target) -/

/-- A `SailME` action completes normally (no `throw`) from `before` to `after`, returning
`result`.  A file-private copy of the `StoreExecuteContract` calculus, used only to thread
`jump_to`'s `SailME.run` wrapper. -/
private def RunsME {ε α : Type} (action : SailME ε α) (before after : State) (result : α) : Prop :=
  Runs (ExceptT.run action) before after (Except.ok result)

/-- Composing two normally-completing `SailME` actions. -/
private theorem RunsME.bind {ε α β : Type} {first : SailME ε α} {next : α → SailME ε β}
    {before middle after : State} {value : α} {result : β}
    (hFirst : RunsME first before middle value)
    (hNext : RunsME (next value) middle after result) :
    RunsME (first >>= next) before after result := by
  change Runs (ExceptT.run first >>= ExceptT.bindCont next) before after (Except.ok result)
  exact Runs.bind hFirst hNext

/-- A pure `SailME` value leaves the state fixed. -/
private theorem RunsME.pure {ε α : Type} (value : α) (s : State) :
    RunsME (Pure.pure value : SailME ε α) s s value := rfl

/-- Lift a normally-completing ordinary Sail action into `RunsME`. -/
private theorem RunsME.lift {ε α : Type} (action : SailM α) (before after : State) (value : α)
    (hAction : Runs action before after value) :
    RunsME (liftM action : SailME ε α) before after value := by
  change Runs (ExceptT.run (liftM action : SailME ε α)) before after (Except.ok value)
  change Runs (Except.ok <$> action) before after (Except.ok value)
  unfold Runs at hAction ⊢
  simp only [EStateM.run, EStateM.instMonad, EStateM.map] at hAction ⊢
  rw [hAction]

/-- Unwrap the generated `SailME.run` around a normally-completing action. -/
private theorem RunsME.run {α : Type} (action : SailME α α) (before after : State) (result : α)
    (h : RunsME action before after result) :
    Runs (Sail.SailME.run action) before after result := by
  unfold Sail.SailME.run PreSail.PreSailME.run
  refine Runs.bind h ?_
  rfl

/-! ## `set_next_pc` and `jump_to` -/

/-- A satisfied `assert` is a no-op. -/
private theorem assert_true_run (state : State) (message : String) :
    Runs (PreSail.assert true message) state state () := rfl

/-- A pure return leaves the state fixed. -/
private theorem run_pure {α : Type} (s : State) (x : α) : Runs (pure x) s s x := rfl

/-- `set_next_pc target` writes `nextPC ↦ target` and does nothing else. -/
theorem set_next_pc_run (s : State) (target : BitVec 64) :
    Runs (set_next_pc target) s { s with regs := s.regs.insert nextPC target } () := by
  unfold set_next_pc
  exact Runs.bind (writeReg_run s nextPC target) rfl

/-- The generated branch target: with `target` word-aligned (`target[1] = 0`) the alignment assert
holds and the `Ext_Zca` `if` takes its else branch, so `jump_to` writes `nextPC ↦ target` and
retires. -/
theorem jump_to_run (s : State) (target : BitVec 64)
    (halign : Sail.BitVec.access target 0 = 0#1)
    (hbit1 : Sail.BitVec.access target 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) s s zcaEnabled) :
    Runs (jump_to target) s { s with regs := s.regs.insert nextPC target }
      (.Retire_Success ()) := by
  unfold jump_to
  have hassert : (Sail.BitVec.access target 0 == 0#1) = true := by simp [halign]
  have hbit : bit_to_bool (Sail.BitVec.access target 1) = false := by rw [hbit1]; decide
  simp only [ext_control_check_pc, hassert, hbit, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  apply RunsME.run
  refine RunsME.bind (RunsME.pure () s) ?_
  refine RunsME.bind (RunsME.lift _ s s () (assert_true_run s _)) ?_
  refine RunsME.bind (RunsME.lift _ s s zcaEnabled hzca) ?_
  refine RunsME.bind
    (RunsME.lift _ s { s with regs := s.regs.insert nextPC target } ()
      (set_next_pc_run s target)) ?_
  exact RunsME.pure (ExecutionResult.Retire_Success ()) _

/-! ## Bit-0 clearing (`jalr` target) -/

/-- Clearing bit 0 makes the result word-aligned (`target[0] = 0`). -/
private theorem access_update0_bit0 (x : BitVec 64) :
    Sail.BitVec.access (Sail.BitVec.update x 0 0#1) 0 = 0#1 := by
  simp only [Sail.BitVec.access, Sail.BitVec.update, Sail.BitVec.updateSubrange', getElem!_pos,
    Nat.reduceLT]
  bv_decide

/-- Clearing bit 0 leaves bit 1 unchanged. -/
private theorem access_update0_bit1 (x : BitVec 64) :
    Sail.BitVec.access (Sail.BitVec.update x 0 0#1) 1 = Sail.BitVec.access x 1 := by
  simp only [Sail.BitVec.access, Sail.BitVec.update, Sail.BitVec.updateSubrange', getElem!_pos,
    Nat.reduceLT]
  bv_decide

/-! ## `execute_JAL` -/

/-- `execute_JAL imm rd` reads the link address (`nextPC`) and `PC`, jumps to `PC + sext imm`
(writing `nextPC ↦ PC + sext imm`), then writes the link into `rd`. -/
theorem execute_JAL_run (s sFinal : State) (imm : BitVec 21) (rd : regidx)
    (linkVal pcVal : BitVec 64)
    (hlink : Runs (get_next_pc ()) s s linkVal)
    (hpc : Runs (readReg PC) s s pcVal)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) imm) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) imm) 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) s s zcaEnabled)
    (hwrite : Runs (wX_bits rd linkVal)
      { s with regs := s.regs.insert nextPC (pcVal + sign_extend (m := 64) imm) } sFinal ()) :
    Runs (execute_JAL imm rd) s sFinal (.Retire_Success ()) := by
  unfold execute_JAL
  refine Runs.bind hlink ?_
  refine Runs.bind hpc ?_
  refine Runs.bind
    (jump_to_run s (pcVal + sign_extend (m := 64) imm) halign hbit1 zcaEnabled hzca) ?_
  refine Runs.bind hwrite ?_
  rfl

/-! ## `execute_JALR` -/

/-- `execute_JALR imm rs1 rd` updates the ELP state, reads the link address (`nextPC`), forms the
target `(rs1 + sext imm)` with bit 0 cleared, jumps there (writing `nextPC ↦ target`), then writes
the link into `rd`.  `update_elp_state` and the `Ext_Zca` read are threaded as minimal premises. -/
theorem execute_JALR_run (s sFinal : State) (imm : BitVec 12) (rs1 rd : regidx)
    (linkVal rs1Val : BitVec 64)
    (helpElp : Runs (update_elp_state rs1) s s ())
    (hlink : Runs (get_next_pc ()) s s linkVal)
    (hrs1 : Runs (rX_bits rs1) s s rs1Val)
    (hbit1 : Sail.BitVec.access (rs1Val + sign_extend (m := 64) imm) 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) s s zcaEnabled)
    (hwrite : Runs (wX_bits rd linkVal)
      { s with regs :=
        s.regs.insert nextPC (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) }
      sFinal ()) :
    Runs (execute_JALR imm rs1 rd) s sFinal (.Retire_Success ()) := by
  unfold execute_JALR
  refine Runs.bind helpElp ?_
  refine Runs.bind hlink ?_
  refine Runs.bind hrs1 ?_
  refine Runs.bind (run_pure s (rs1Val + sign_extend (m := 64) imm)) ?_
  refine Runs.bind
    (jump_to_run s (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)
      (access_update0_bit0 _) ?halign zcaEnabled hzca) ?_
  case halign => rw [access_update0_bit1]; exact hbit1
  refine Runs.bind hwrite ?_
  rfl

/-! ## `execute_BTYPE` -/

/-- The branch-taken predicate computed by `execute_BTYPE` (structurally identical to the generated
inline condition, so the factoring below is definitional). -/
def bTypeTaken (rs2 rs1 : regidx) (op : bop) : SailM Bool := do
  match op with
  | .BEQ => pure ((← rX_bits rs1) == (← rX_bits rs2))
  | .BNE => pure ((← rX_bits rs1) != (← rX_bits rs2))
  | .BLT => pure (zopz0zI_s (← rX_bits rs1) (← rX_bits rs2))
  | .BGE => pure (zopz0zKzJ_s (← rX_bits rs1) (← rX_bits rs2))
  | .BLTU => pure (zopz0zI_u (← rX_bits rs1) (← rX_bits rs2))
  | .BGEU => pure (zopz0zKzJ_u (← rX_bits rs1) (← rX_bits rs2))

private theorem execute_BTYPE_factor (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) :
    execute_BTYPE imm rs2 rs1 op = (do
      let taken ← bTypeTaken rs2 rs1 op
      if taken then jump_to ((← readReg PC) + sign_extend (m := 64) imm)
      else pure RETIRE_SUCCESS) := rfl

/-- Taken branch: when the comparison holds, `execute_BTYPE` jumps to `PC + sext imm`
(writing `nextPC ↦ PC + sext imm`) and retires. -/
theorem execute_BTYPE_taken_run (s : State) (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
    (pcVal : BitVec 64)
    (hcond : Runs (bTypeTaken rs2 rs1 op) s s true)
    (hpc : Runs (readReg PC) s s pcVal)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) imm) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) imm) 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) s s zcaEnabled) :
    Runs (execute_BTYPE imm rs2 rs1 op) s
      { s with regs := s.regs.insert nextPC (pcVal + sign_extend (m := 64) imm) }
      (.Retire_Success ()) := by
  rw [execute_BTYPE_factor]
  refine Runs.bind hcond ?_
  simp only [if_true]
  refine Runs.bind hpc ?_
  exact jump_to_run s (pcVal + sign_extend (m := 64) imm) halign hbit1 zcaEnabled hzca

/-- Not-taken branch: when the comparison fails, `execute_BTYPE` retires, state unchanged. -/
theorem execute_BTYPE_notTaken_run (s : State) (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
    (hcond : Runs (bTypeTaken rs2 rs1 op) s s false) :
    Runs (execute_BTYPE imm rs2 rs1 op) s s (.Retire_Success ()) := by
  rw [execute_BTYPE_factor]
  refine Runs.bind hcond ?_
  exact run_pure s _

/-! ## `ret` (`jalr x0, 0(rs1)`) -/

/-- Writing register `x0` (`zreg`) is a no-op. -/
private theorem wX_bits_zero_run (s : State) (data : BitVec 64) :
    Runs (wX_bits zreg data) s s () := by
  unfold wX_bits zreg wX
  rfl

/-- `sign_extend` of `0#12` vanishes, so a zero-offset `jalr` targets `rs1` directly. -/
private theorem add_sign_extend_zero (x : BitVec 64) :
    x + sign_extend (m := 64) (0#12) = x := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  bv_decide

/-- `ret` (`jalr x0, 0(rs1)`): jumps to `rs1` with bit 0 cleared, discarding the link write to
`x0`.  With `rs1 = x1` this is the RISC-V `ret` pseudo-instruction. -/
theorem ret_run (s : State) (rs1 : regidx) (linkVal rs1Val : BitVec 64)
    (helpElp : Runs (update_elp_state rs1) s s ())
    (hlink : Runs (get_next_pc ()) s s linkVal)
    (hrs1 : Runs (rX_bits rs1) s s rs1Val)
    (hbit1 : Sail.BitVec.access rs1Val 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) s s zcaEnabled) :
    Runs (execute_JALR 0#12 rs1 zreg) s
      { s with regs := s.regs.insert nextPC (Sail.BitVec.update rs1Val 0 0#1) }
      (.Retire_Success ()) := by
  have hbit1' : Sail.BitVec.access (rs1Val + sign_extend (m := 64) (0#12)) 1 = 0#1 := by
    rw [add_sign_extend_zero]; exact hbit1
  have key := execute_JALR_run s
    { s with regs :=
      s.regs.insert nextPC (Sail.BitVec.update (rs1Val + sign_extend (m := 64) (0#12)) 0 0#1) }
    0#12 rs1 zreg linkVal rs1Val helpElp hlink hrs1 hbit1' zcaEnabled hzca
    (wX_bits_zero_run _ linkVal)
  rw [add_sign_extend_zero] at key
  exact key

end BinaryFv.RiscV
