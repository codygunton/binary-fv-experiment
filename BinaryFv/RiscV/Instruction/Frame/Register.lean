import BinaryFv.RiscV.Logic.Framing
import BinaryFv.RiscV.Analysis.StackFlow
import Lean.Elab.Tactic.Omega

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated integer-register write callback completes normally without changing state. -/
theorem xreg_write_callback_run (state : State) (register : regidx) (data : BitVec 64) :
    (xreg_write_callback register data).run state = .ok () state := by
  rcases register with ⟨index⟩
  simp [xreg_write_callback, xreg_full_write_callback, reg_name_forwards,
    encdec_reg_forwards, encdec_reg_forwards_matches, get_config_use_abi_names,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad,
    LeanRV64DExecutable.Functions.not]

private theorem xreg_write_callback_apply (state : State) (register : regidx) (data : BitVec 64) :
    xreg_write_callback register data state = .ok () state :=
  xreg_write_callback_run state register data

/-- A nonzero architectural integer register. Unlike a bare `regidx`, this finite type records that
the generated read or write has a corresponding `Register` key whose value type is `BitVec 64`. -/
inductive NonzeroXRegister where
  | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15 | r16
  | r17 | r18 | r19 | r20 | r21 | r22 | r23 | r24 | r25 | r26 | r27 | r28 | r29 | r30 | r31

namespace NonzeroXRegister

/-- The generated five-bit index for a nonzero integer register. -/
def index : NonzeroXRegister → regidx
  | .r1 => .Regidx 1#5
  | .r2 => .Regidx 2#5
  | .r3 => .Regidx 3#5
  | .r4 => .Regidx 4#5
  | .r5 => .Regidx 5#5
  | .r6 => .Regidx 6#5
  | .r7 => .Regidx 7#5
  | .r8 => .Regidx 8#5
  | .r9 => .Regidx 9#5
  | .r10 => .Regidx 10#5
  | .r11 => .Regidx 11#5
  | .r12 => .Regidx 12#5
  | .r13 => .Regidx 13#5
  | .r14 => .Regidx 14#5
  | .r15 => .Regidx 15#5
  | .r16 => .Regidx 16#5
  | .r17 => .Regidx 17#5
  | .r18 => .Regidx 18#5
  | .r19 => .Regidx 19#5
  | .r20 => .Regidx 20#5
  | .r21 => .Regidx 21#5
  | .r22 => .Regidx 22#5
  | .r23 => .Regidx 23#5
  | .r24 => .Regidx 24#5
  | .r25 => .Regidx 25#5
  | .r26 => .Regidx 26#5
  | .r27 => .Regidx 27#5
  | .r28 => .Regidx 28#5
  | .r29 => .Regidx 29#5
  | .r30 => .Regidx 30#5
  | .r31 => .Regidx 31#5

/-- The register-map premise for a generated nonzero integer-register read. -/
def Reads (register : NonzeroXRegister) (state : State) (value : BitVec 64) : Prop :=
  match register with
  | .r1 => state.regs.get? x1 = some value
  | .r2 => state.regs.get? x2 = some value
  | .r3 => state.regs.get? x3 = some value
  | .r4 => state.regs.get? x4 = some value
  | .r5 => state.regs.get? x5 = some value
  | .r6 => state.regs.get? x6 = some value
  | .r7 => state.regs.get? x7 = some value
  | .r8 => state.regs.get? x8 = some value
  | .r9 => state.regs.get? x9 = some value
  | .r10 => state.regs.get? x10 = some value
  | .r11 => state.regs.get? x11 = some value
  | .r12 => state.regs.get? x12 = some value
  | .r13 => state.regs.get? x13 = some value
  | .r14 => state.regs.get? x14 = some value
  | .r15 => state.regs.get? x15 = some value
  | .r16 => state.regs.get? x16 = some value
  | .r17 => state.regs.get? x17 = some value
  | .r18 => state.regs.get? x18 = some value
  | .r19 => state.regs.get? x19 = some value
  | .r20 => state.regs.get? x20 = some value
  | .r21 => state.regs.get? x21 = some value
  | .r22 => state.regs.get? x22 = some value
  | .r23 => state.regs.get? x23 = some value
  | .r24 => state.regs.get? x24 = some value
  | .r25 => state.regs.get? x25 = some value
  | .r26 => state.regs.get? x26 = some value
  | .r27 => state.regs.get? x27 = some value
  | .r28 => state.regs.get? x28 = some value
  | .r29 => state.regs.get? x29 = some value
  | .r30 => state.regs.get? x30 = some value
  | .r31 => state.regs.get? x31 = some value

/-- The exact register-map update made by a generated nonzero integer-register write. -/
def AfterWrite (register : NonzeroXRegister) (state : State) (value : BitVec 64) : State :=
  match register with
  | .r1 => { state with regs := state.regs.insert x1 value }
  | .r2 => { state with regs := state.regs.insert x2 value }
  | .r3 => { state with regs := state.regs.insert x3 value }
  | .r4 => { state with regs := state.regs.insert x4 value }
  | .r5 => { state with regs := state.regs.insert x5 value }
  | .r6 => { state with regs := state.regs.insert x6 value }
  | .r7 => { state with regs := state.regs.insert x7 value }
  | .r8 => { state with regs := state.regs.insert x8 value }
  | .r9 => { state with regs := state.regs.insert x9 value }
  | .r10 => { state with regs := state.regs.insert x10 value }
  | .r11 => { state with regs := state.regs.insert x11 value }
  | .r12 => { state with regs := state.regs.insert x12 value }
  | .r13 => { state with regs := state.regs.insert x13 value }
  | .r14 => { state with regs := state.regs.insert x14 value }
  | .r15 => { state with regs := state.regs.insert x15 value }
  | .r16 => { state with regs := state.regs.insert x16 value }
  | .r17 => { state with regs := state.regs.insert x17 value }
  | .r18 => { state with regs := state.regs.insert x18 value }
  | .r19 => { state with regs := state.regs.insert x19 value }
  | .r20 => { state with regs := state.regs.insert x20 value }
  | .r21 => { state with regs := state.regs.insert x21 value }
  | .r22 => { state with regs := state.regs.insert x22 value }
  | .r23 => { state with regs := state.regs.insert x23 value }
  | .r24 => { state with regs := state.regs.insert x24 value }
  | .r25 => { state with regs := state.regs.insert x25 value }
  | .r26 => { state with regs := state.regs.insert x26 value }
  | .r27 => { state with regs := state.regs.insert x27 value }
  | .r28 => { state with regs := state.regs.insert x28 value }
  | .r29 => { state with regs := state.regs.insert x29 value }
  | .r30 => { state with regs := state.regs.insert x30 value }
  | .r31 => { state with regs := state.regs.insert x31 value }

end NonzeroXRegister

local macro "xread_case" idx:num " ↦ " reg:ident ", " name:ident : command =>
  `(private theorem $name (state : State) (value : BitVec 64)
      (stored : state.regs.get? $reg = some value) :
      Runs (rX_bits (.Regidx (BitVec.ofNat 5 $idx))) state state value := by
    have index : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [rX_bits, rX, index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
      EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg])

local macro "xwrite_case" idx:num " ↦ " reg:ident ", " name:ident : command =>
  `(private theorem $name (state : State) (value : BitVec 64) :
      Runs (wX_bits (.Regidx (BitVec.ofNat 5 $idx)) value) state
        { state with regs := state.regs.insert $reg value } () := by
    have index : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp only [wX_bits, wX, index, regval_into_reg, PreSail.writeReg, EStateM.run,
      EStateM.bind, EStateM.modifyGet, EStateM.instMonad, MonadState.modifyGet,
      MonadStateOf.modifyGet, modify]
    rw [if_pos (by decide)]
    exact xreg_write_callback_run _ _ _)

xread_case 1 ↦ x1, rX_bits_run_r1_case
xread_case 2 ↦ x2, rX_bits_run_r2_case
xread_case 3 ↦ x3, rX_bits_run_r3_case
xread_case 4 ↦ x4, rX_bits_run_r4_case
xread_case 5 ↦ x5, rX_bits_run_r5_case
xread_case 6 ↦ x6, rX_bits_run_r6_case
xread_case 7 ↦ x7, rX_bits_run_r7_case
xread_case 8 ↦ x8, rX_bits_run_r8_case
xread_case 9 ↦ x9, rX_bits_run_r9_case
xread_case 10 ↦ x10, rX_bits_run_r10_case
xread_case 11 ↦ x11, rX_bits_run_r11_case
xread_case 12 ↦ x12, rX_bits_run_r12_case
xread_case 13 ↦ x13, rX_bits_run_r13_case
xread_case 14 ↦ x14, rX_bits_run_r14_case
xread_case 15 ↦ x15, rX_bits_run_r15_case
xread_case 16 ↦ x16, rX_bits_run_r16_case
xread_case 17 ↦ x17, rX_bits_run_r17_case
xread_case 18 ↦ x18, rX_bits_run_r18_case
xread_case 19 ↦ x19, rX_bits_run_r19_case
xread_case 20 ↦ x20, rX_bits_run_r20_case
xread_case 21 ↦ x21, rX_bits_run_r21_case
xread_case 22 ↦ x22, rX_bits_run_r22_case
xread_case 23 ↦ x23, rX_bits_run_r23_case
xread_case 24 ↦ x24, rX_bits_run_r24_case
xread_case 25 ↦ x25, rX_bits_run_r25_case
xread_case 26 ↦ x26, rX_bits_run_r26_case
xread_case 27 ↦ x27, rX_bits_run_r27_case
xread_case 28 ↦ x28, rX_bits_run_r28_case
xread_case 29 ↦ x29, rX_bits_run_r29_case
xread_case 30 ↦ x30, rX_bits_run_r30_case
xread_case 31 ↦ x31, rX_bits_run_r31_case

xwrite_case 1 ↦ x1, wX_bits_run_r1_case
xwrite_case 2 ↦ x2, wX_bits_run_r2_case
xwrite_case 3 ↦ x3, wX_bits_run_r3_case
xwrite_case 4 ↦ x4, wX_bits_run_r4_case
xwrite_case 5 ↦ x5, wX_bits_run_r5_case
xwrite_case 6 ↦ x6, wX_bits_run_r6_case
xwrite_case 7 ↦ x7, wX_bits_run_r7_case
xwrite_case 8 ↦ x8, wX_bits_run_r8_case
xwrite_case 9 ↦ x9, wX_bits_run_r9_case
xwrite_case 10 ↦ x10, wX_bits_run_r10_case
xwrite_case 11 ↦ x11, wX_bits_run_r11_case
xwrite_case 12 ↦ x12, wX_bits_run_r12_case
xwrite_case 13 ↦ x13, wX_bits_run_r13_case
xwrite_case 14 ↦ x14, wX_bits_run_r14_case
xwrite_case 15 ↦ x15, wX_bits_run_r15_case
xwrite_case 16 ↦ x16, wX_bits_run_r16_case
xwrite_case 17 ↦ x17, wX_bits_run_r17_case
xwrite_case 18 ↦ x18, wX_bits_run_r18_case
xwrite_case 19 ↦ x19, wX_bits_run_r19_case
xwrite_case 20 ↦ x20, wX_bits_run_r20_case
xwrite_case 21 ↦ x21, wX_bits_run_r21_case
xwrite_case 22 ↦ x22, wX_bits_run_r22_case
xwrite_case 23 ↦ x23, wX_bits_run_r23_case
xwrite_case 24 ↦ x24, wX_bits_run_r24_case
xwrite_case 25 ↦ x25, wX_bits_run_r25_case
xwrite_case 26 ↦ x26, wX_bits_run_r26_case
xwrite_case 27 ↦ x27, wX_bits_run_r27_case
xwrite_case 28 ↦ x28, wX_bits_run_r28_case
xwrite_case 29 ↦ x29, wX_bits_run_r29_case
xwrite_case 30 ↦ x30, wX_bits_run_r30_case
xwrite_case 31 ↦ x31, wX_bits_run_r31_case

/-- One generated integer-register read theorem, parameterized by the architectural register. -/
theorem rX_bits_run_nonzero (register : NonzeroXRegister) (state : State) (value : BitVec 64)
    (stored : register.Reads state value) :
    Runs (rX_bits register.index) state state value := by
  cases register with
  | r1 => exact rX_bits_run_r1_case state value stored
  | r2 => exact rX_bits_run_r2_case state value stored
  | r3 => exact rX_bits_run_r3_case state value stored
  | r4 => exact rX_bits_run_r4_case state value stored
  | r5 => exact rX_bits_run_r5_case state value stored
  | r6 => exact rX_bits_run_r6_case state value stored
  | r7 => exact rX_bits_run_r7_case state value stored
  | r8 => exact rX_bits_run_r8_case state value stored
  | r9 => exact rX_bits_run_r9_case state value stored
  | r10 => exact rX_bits_run_r10_case state value stored
  | r11 => exact rX_bits_run_r11_case state value stored
  | r12 => exact rX_bits_run_r12_case state value stored
  | r13 => exact rX_bits_run_r13_case state value stored
  | r14 => exact rX_bits_run_r14_case state value stored
  | r15 => exact rX_bits_run_r15_case state value stored
  | r16 => exact rX_bits_run_r16_case state value stored
  | r17 => exact rX_bits_run_r17_case state value stored
  | r18 => exact rX_bits_run_r18_case state value stored
  | r19 => exact rX_bits_run_r19_case state value stored
  | r20 => exact rX_bits_run_r20_case state value stored
  | r21 => exact rX_bits_run_r21_case state value stored
  | r22 => exact rX_bits_run_r22_case state value stored
  | r23 => exact rX_bits_run_r23_case state value stored
  | r24 => exact rX_bits_run_r24_case state value stored
  | r25 => exact rX_bits_run_r25_case state value stored
  | r26 => exact rX_bits_run_r26_case state value stored
  | r27 => exact rX_bits_run_r27_case state value stored
  | r28 => exact rX_bits_run_r28_case state value stored
  | r29 => exact rX_bits_run_r29_case state value stored
  | r30 => exact rX_bits_run_r30_case state value stored
  | r31 => exact rX_bits_run_r31_case state value stored

/-- One generated integer-register write theorem, parameterized by the architectural register. -/
theorem wX_bits_run_nonzero (register : NonzeroXRegister) (state : State) (value : BitVec 64) :
    Runs (wX_bits register.index value) state (register.AfterWrite state value) () := by
  cases register with
  | r1 => exact wX_bits_run_r1_case state value
  | r2 => exact wX_bits_run_r2_case state value
  | r3 => exact wX_bits_run_r3_case state value
  | r4 => exact wX_bits_run_r4_case state value
  | r5 => exact wX_bits_run_r5_case state value
  | r6 => exact wX_bits_run_r6_case state value
  | r7 => exact wX_bits_run_r7_case state value
  | r8 => exact wX_bits_run_r8_case state value
  | r9 => exact wX_bits_run_r9_case state value
  | r10 => exact wX_bits_run_r10_case state value
  | r11 => exact wX_bits_run_r11_case state value
  | r12 => exact wX_bits_run_r12_case state value
  | r13 => exact wX_bits_run_r13_case state value
  | r14 => exact wX_bits_run_r14_case state value
  | r15 => exact wX_bits_run_r15_case state value
  | r16 => exact wX_bits_run_r16_case state value
  | r17 => exact wX_bits_run_r17_case state value
  | r18 => exact wX_bits_run_r18_case state value
  | r19 => exact wX_bits_run_r19_case state value
  | r20 => exact wX_bits_run_r20_case state value
  | r21 => exact wX_bits_run_r21_case state value
  | r22 => exact wX_bits_run_r22_case state value
  | r23 => exact wX_bits_run_r23_case state value
  | r24 => exact wX_bits_run_r24_case state value
  | r25 => exact wX_bits_run_r25_case state value
  | r26 => exact wX_bits_run_r26_case state value
  | r27 => exact wX_bits_run_r27_case state value
  | r28 => exact wX_bits_run_r28_case state value
  | r29 => exact wX_bits_run_r29_case state value
  | r30 => exact wX_bits_run_r30_case state value
  | r31 => exact wX_bits_run_r31_case state value

/-- The architectural zero register reads as zero without consulting the register map. -/
theorem rX_bits_run_zero (state : State) :
    Runs (rX_bits (.Regidx 0#5)) state state (0#64) := by
  unfold Runs rX_bits rX
  simp [zero_reg, EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad,
    regval_from_reg]
  rfl

/-- Writes to the architectural zero register are discarded. -/
theorem wX_bits_run_zero (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 0#5) value) state state () := by
  have index : (Sail.BitVec.toNatInt (0#5)).toNat = 0 := rfl
  unfold Runs
  simp only [wX_bits, wX, index, EStateM.run, EStateM.bind, EStateM.instMonad]
  rw [if_neg (by decide)]
  rfl

/-- A generated integer write to any non-stack destination preserves the old `x2` value. -/
theorem wX_bits_preserves_stack_pointer (state : State) (destination : regidx) (data : BitVec 64)
    (notStack : destination ≠ stackPointer) :
    (match (wX_bits destination data).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  rcases destination with ⟨index⟩
  have indexNotStack : index ≠ 2#5 := by
    intro equals
    apply notStack
    simp [stackPointer, equals]
  have indexNatNotStack : index.toNat ≠ 2 := by
    have unequal := BitVec.toNat_ne.mp indexNotStack
    simpa using unequal
  have sailIndexNat : (Sail.BitVec.toNatInt index).toNat = index.toNat := rfl
  have indexLt : index.toNat < 32 := by
    simpa using index.isLt
  have indexCases : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 ∨
      index.toNat = 3 ∨ index.toNat = 4 ∨ index.toNat = 5 ∨ index.toNat = 6 ∨
      index.toNat = 7 ∨ index.toNat = 8 ∨ index.toNat = 9 ∨ index.toNat = 10 ∨
      index.toNat = 11 ∨ index.toNat = 12 ∨ index.toNat = 13 ∨ index.toNat = 14 ∨
      index.toNat = 15 ∨ index.toNat = 16 ∨ index.toNat = 17 ∨ index.toNat = 18 ∨
      index.toNat = 19 ∨ index.toNat = 20 ∨ index.toNat = 21 ∨ index.toNat = 22 ∨
      index.toNat = 23 ∨ index.toNat = 24 ∨ index.toNat = 25 ∨ index.toNat = 26 ∨
      index.toNat = 27 ∨ index.toNat = 28 ∨ index.toNat = 29 ∨ index.toNat = 30 ∨
      index.toNat = 31 := by
    omega
  rcases indexCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    first
    | omega
    | simp [wX_bits, wX, h, sailIndexNat, PreSail.writeReg, EStateM.run, EStateM.bind,
        EStateM.modifyGet, EStateM.pure, EStateM.instMonad, MonadState.modifyGet,
        MonadStateOf.modifyGet, modify, regval_into_reg, xreg_write_callback_apply,
        Std.ExtDHashMap.get?_insert]

/-- A generated `LUI` preserves `x2` whenever it writes a non-stack destination. -/
theorem execute_UTYPE_lui_preserves_stack_pointer (state : State) (immediate : BitVec 20)
    (destination : regidx) (notStack : destination ≠ stackPointer) :
    (match (execute_UTYPE immediate destination .LUI).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  rw [show execute_UTYPE immediate destination .LUI =
      (do
        wX_bits destination (sign_extend (m := 64) (immediate ++ 0x000#12))
        pure RETIRE_SUCCESS) by rfl]
  have frame := wX_bits_preserves_stack_pointer state destination
    (sign_extend (m := 64) (immediate ++ 0x000#12)) notStack
  cases hAction : (wX_bits destination
      (sign_extend (m := 64) (immediate ++ 0x000#12))).run state with
  | ok value after =>
    change wX_bits destination (sign_extend (m := 64) (immediate ++ 0x000#12)) state =
      .ok value after at hAction
    simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hAction] using frame
  | error error after =>
    change wX_bits destination (sign_extend (m := 64) (immediate ++ 0x000#12)) state =
      .error error after at hAction
    simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hAction] using frame

private theorem get_arch_pc_state_projection (state : State) :
    (match (get_arch_pc ()).run state with
    | .ok _ state' => state'
    | .error _ state' => state') = state := by
  simp [get_arch_pc, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
    EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe]
  cases h : state.regs.get? PC <;> rfl

private theorem execute_UTYPE_auipc_preserves_stack_pointer (state : State) (immediate : BitVec 20)
    (destination : regidx) (notStack : destination ≠ stackPointer) :
    (match (execute_UTYPE immediate destination .AUIPC).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  simp only [execute_UTYPE]
  cases hPc : (get_arch_pc ()).run state with
  | ok pc after =>
    change get_arch_pc () state = .ok pc after at hPc
    have afterEq : after = state := by
      have preserved := get_arch_pc_state_projection state
      change (match get_arch_pc () state with
        | .ok _ state' => state'
        | .error _ state' => state') = state at preserved
      simpa [hPc] using preserved
    subst after
    have frame := wX_bits_preserves_stack_pointer state destination
      (pc + sign_extend (m := 64) (immediate ++ 0x000#12)) notStack
    cases hWrite : (wX_bits destination
        (pc + sign_extend (m := 64) (immediate ++ 0x000#12))).run state with
    | ok value after =>
      change wX_bits destination (pc + sign_extend (m := 64) (immediate ++ 0x000#12)) state =
        .ok value after at hWrite
      simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hPc, hWrite]
        using frame
    | error error after =>
      change wX_bits destination (pc + sign_extend (m := 64) (immediate ++ 0x000#12)) state =
        .error error after at hWrite
      simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hPc, hWrite]
        using frame
  | error error after =>
    change get_arch_pc () state = .error error after at hPc
    have afterEq : after = state := by
      have preserved := get_arch_pc_state_projection state
      change (match get_arch_pc () state with
        | .ok _ state' => state'
        | .error _ state' => state') = state at preserved
      simpa [hPc] using preserved
    subst after
    simp [EStateM.run, EStateM.bind, EStateM.instMonad, hPc]

/-- Every generated U-type pure integer writer preserves `x2` off the stack destination. -/
theorem execute_UTYPE_preserves_stack_pointer (state : State) (immediate : BitVec 20)
    (destination : regidx) (op : uop) (notStack : destination ≠ stackPointer) :
    (match (execute_UTYPE immediate destination op).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  cases op with
  | LUI => exact execute_UTYPE_lui_preserves_stack_pointer state immediate destination notStack
  | AUIPC => exact execute_UTYPE_auipc_preserves_stack_pointer state immediate destination notStack

end BinaryFv.RiscV
