import BinaryFv.RiscV.Logic.BlockStep

/-!
# Shared generated-register run lemmas

`rX_x<n>_run` and `wX_x<n>_run` retain the target-facing theorem names used by machine proofs. Each
is now a compatibility wrapper around the target-independent, register-parameterized theorems in
`BinaryFv.RiscV.Instruction.Frame.Register`; the generated Sail action is proved only once there.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

/-- The architectural zero register reads as zero without consulting the register map. -/
theorem rX_x0_run (state : State) :
    Runs (rX_bits (.Regidx 0#5)) state state (0#64) :=
  rX_bits_run_zero state

theorem rX_x1_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x1 = some value) :
    Runs (rX_bits (.Regidx 1#5)) state state value := rX_bits_run_nonzero .r1 state value stored
theorem rX_x2_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x2 = some value) :
    Runs (rX_bits (.Regidx 2#5)) state state value := rX_bits_run_nonzero .r2 state value stored
theorem rX_x5_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x5 = some value) :
    Runs (rX_bits (.Regidx 5#5)) state state value := rX_bits_run_nonzero .r5 state value stored
theorem rX_x6_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x6 = some value) :
    Runs (rX_bits (.Regidx 6#5)) state state value := rX_bits_run_nonzero .r6 state value stored
theorem rX_x7_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x7 = some value) :
    Runs (rX_bits (.Regidx 7#5)) state state value := rX_bits_run_nonzero .r7 state value stored
theorem rX_x8_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x8 = some value) :
    Runs (rX_bits (.Regidx 8#5)) state state value := rX_bits_run_nonzero .r8 state value stored
theorem rX_x9_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x9 = some value) :
    Runs (rX_bits (.Regidx 9#5)) state state value := rX_bits_run_nonzero .r9 state value stored
theorem rX_x10_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x10 = some value) :
    Runs (rX_bits (.Regidx 10#5)) state state value := rX_bits_run_nonzero .r10 state value stored
theorem rX_x11_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x11 = some value) :
    Runs (rX_bits (.Regidx 11#5)) state state value := rX_bits_run_nonzero .r11 state value stored
theorem rX_x12_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x12 = some value) :
    Runs (rX_bits (.Regidx 12#5)) state state value := rX_bits_run_nonzero .r12 state value stored
theorem rX_x13_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x13 = some value) :
    Runs (rX_bits (.Regidx 13#5)) state state value := rX_bits_run_nonzero .r13 state value stored
theorem rX_x14_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x14 = some value) :
    Runs (rX_bits (.Regidx 14#5)) state state value := rX_bits_run_nonzero .r14 state value stored
theorem rX_x15_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x15 = some value) :
    Runs (rX_bits (.Regidx 15#5)) state state value := rX_bits_run_nonzero .r15 state value stored
theorem rX_x16_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x16 = some value) :
    Runs (rX_bits (.Regidx 16#5)) state state value := rX_bits_run_nonzero .r16 state value stored
theorem rX_x17_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x17 = some value) :
    Runs (rX_bits (.Regidx 17#5)) state state value := rX_bits_run_nonzero .r17 state value stored
theorem rX_x28_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x28 = some value) :
    Runs (rX_bits (.Regidx 28#5)) state state value := rX_bits_run_nonzero .r28 state value stored
theorem rX_x29_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x29 = some value) :
    Runs (rX_bits (.Regidx 29#5)) state state value := rX_bits_run_nonzero .r29 state value stored
theorem rX_x30_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x30 = some value) :
    Runs (rX_bits (.Regidx 30#5)) state state value := rX_bits_run_nonzero .r30 state value stored

theorem wX_x1_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 1#5) value) state { state with regs := state.regs.insert x1 value } () :=
  wX_bits_run_nonzero .r1 state value
theorem wX_x2_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 2#5) value) state { state with regs := state.regs.insert x2 value } () :=
  wX_bits_run_nonzero .r2 state value
theorem wX_x5_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 5#5) value) state { state with regs := state.regs.insert x5 value } () :=
  wX_bits_run_nonzero .r5 state value
theorem wX_x6_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 6#5) value) state { state with regs := state.regs.insert x6 value } () :=
  wX_bits_run_nonzero .r6 state value
theorem wX_x7_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 7#5) value) state { state with regs := state.regs.insert x7 value } () :=
  wX_bits_run_nonzero .r7 state value
theorem wX_x8_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 8#5) value) state { state with regs := state.regs.insert x8 value } () :=
  wX_bits_run_nonzero .r8 state value
theorem wX_x9_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 9#5) value) state { state with regs := state.regs.insert x9 value } () :=
  wX_bits_run_nonzero .r9 state value
theorem wX_x10_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 10#5) value) state { state with regs := state.regs.insert x10 value } () :=
  wX_bits_run_nonzero .r10 state value
theorem wX_x11_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 11#5) value) state { state with regs := state.regs.insert x11 value } () :=
  wX_bits_run_nonzero .r11 state value
theorem wX_x12_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 12#5) value) state { state with regs := state.regs.insert x12 value } () :=
  wX_bits_run_nonzero .r12 state value
theorem wX_x13_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 13#5) value) state { state with regs := state.regs.insert x13 value } () :=
  wX_bits_run_nonzero .r13 state value
theorem wX_x14_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 14#5) value) state { state with regs := state.regs.insert x14 value } () :=
  wX_bits_run_nonzero .r14 state value
theorem wX_x15_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 15#5) value) state { state with regs := state.regs.insert x15 value } () :=
  wX_bits_run_nonzero .r15 state value
theorem wX_x16_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 16#5) value) state { state with regs := state.regs.insert x16 value } () :=
  wX_bits_run_nonzero .r16 state value
theorem wX_x17_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 17#5) value) state { state with regs := state.regs.insert x17 value } () :=
  wX_bits_run_nonzero .r17 state value
theorem wX_x18_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 18#5) value) state { state with regs := state.regs.insert x18 value } () :=
  wX_bits_run_nonzero .r18 state value
theorem wX_x19_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 19#5) value) state { state with regs := state.regs.insert x19 value } () :=
  wX_bits_run_nonzero .r19 state value
theorem wX_x21_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 21#5) value) state { state with regs := state.regs.insert x21 value } () :=
  wX_bits_run_nonzero .r21 state value
theorem wX_x22_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 22#5) value) state { state with regs := state.regs.insert x22 value } () :=
  wX_bits_run_nonzero .r22 state value
theorem wX_x28_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 28#5) value) state { state with regs := state.regs.insert x28 value } () :=
  wX_bits_run_nonzero .r28 state value
theorem wX_x29_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 29#5) value) state { state with regs := state.regs.insert x29 value } () :=
  wX_bits_run_nonzero .r29 state value
theorem wX_x30_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 30#5) value) state { state with regs := state.regs.insert x30 value } () :=
  wX_bits_run_nonzero .r30 state value

end BinaryFv.Zesu.MachineExecution
