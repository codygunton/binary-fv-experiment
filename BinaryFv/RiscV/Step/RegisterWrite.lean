import BinaryFv.RiscV.Step.ControlFlow

/-! Target-independent post-state and frame lemmas for a retired register-writing instruction. -/

namespace BinaryFv.RiscV

open PreSail LeanRV64DExecutable.Functions Register

def afterRegisterWrite (state : State) (pc retired : BitVec 64) (destination : Register)
    (value : RegisterType destination) : State :=
  tryStepControlFlowAfterRetired
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
        destination value }
    (Sail.BitVec.addInt pc 4) retired

theorem afterRegisterWrite_register (state : State) (pc retired : BitVec 64)
    (destination register : Register) (value : RegisterType destination)
    (notDestination : destination ≠ register) (notPc : PC ≠ register)
    (notNextPc : nextPC ≠ register) (notIncrement : minstret_increment ≠ register)
    (notRetired : minstret ≠ register) :
    (afterRegisterWrite state pc retired destination value).regs.get? register =
      state.regs.get? register := by
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    notDestination, notPc, notNextPc, notIncrement, notRetired]

theorem afterRegisterWrite_writes (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only destination)) state
      (afterRegisterWrite state pc retired destination value) :=
  fun r hr =>
    afterRegisterWrite_register state pc retired destination r value
      (fun h => hr (Or.inr h.symm))
      (fun h => hr (Or.inl (Or.inl h.symm)))
      (fun h => hr (Or.inl (Or.inr (Or.inl h.symm))))
      (fun h => hr (Or.inl (Or.inr (Or.inr (Or.inr h.symm)))))
      (fun h => hr (Or.inl (Or.inr (Or.inr (Or.inl h.symm)))))

theorem afterRegisterWrite_mem (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    (afterRegisterWrite state pc retired destination value).mem = state.mem := rfl

theorem afterRegisterWrite_retired_present (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    RetiredCounterPresent (afterRegisterWrite state pc retired destination value) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]

theorem afterRegisterWrite_pc (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    (afterRegisterWrite state pc retired destination value).regs.get? PC =
      some (Sail.BitVec.addInt pc 4) := by
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    Std.ExtDHashMap.get?_insert]

end BinaryFv.RiscV
