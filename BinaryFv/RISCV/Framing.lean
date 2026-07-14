import BinaryFv.RISCV.Machine

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register

def MemoryEqualOutside (before after : State) (address : Nat) : Prop :=
  ∀ observed, observed ≠ address → before.mem.get? observed = after.mem.get? observed

/-- A generated Sail action has completed normally from `before` to `after`. -/
def Runs (action : SailM α) (before after : State) (result : α) : Prop :=
  action.run before = .ok result after

theorem Runs.bind {first : SailM α} {next : α → SailM β}
    {before middle after : State} {value : α} {result : β}
    (hFirst : Runs first before middle value) (hNext : Runs (next value) middle after result) :
    Runs (first >>= next) before after result := by
  change EStateM.bind first next before = .ok result after
  unfold EStateM.bind
  rw [show first before = .ok value middle from hFirst]
  exact hNext

def RegisterEqualOutside (before after : State) (written : Register) : Prop :=
  ∀ observed, observed ≠ written → before.regs.get? observed = after.regs.get? observed

theorem writeByte_run (state : State) (address : Nat) (value : BitVec 8) :
    (writeByte address value : SailM PUnit).run state =
      .ok PUnit.unit { state with mem := state.mem.insert address value } := by
  rfl

theorem writeByte_run_memory_get (state : State) (address observed : Nat) (value : BitVec 8) :
    (match (writeByte address value : SailM PUnit).run state with
    | .ok _ state' => state'.mem.get? observed
    | .error _ state' => state'.mem.get? observed) =
      if address == observed then some value else state.mem.get? observed := by
  change (state.mem.insert address value).get? observed = _
  simp only [Std.ExtHashMap.get?_eq_getElem?]
  rw [Std.ExtHashMap.getElem?_insert]

theorem writeByte_preserves_registers (state : State) (address : Nat) (value : BitVec 8) :
    (match (writeByte address value : SailM PUnit).run state with
    | .ok _ state' => state'.regs
    | .error _ state' => state'.regs) = state.regs := by
  rfl

theorem writeByte_preserves_memory_outside (state : State) (address observed : Nat)
    (value : BitVec 8) (distinct : observed ≠ address) :
    (match (writeByte address value : SailM PUnit).run state with
    | .ok _ state' => state'.mem.get? observed
    | .error _ state' => state'.mem.get? observed) = state.mem.get? observed := by
  rw [writeByte_run_memory_get]
  by_cases same : address = observed
  · exact (distinct same.symm).elim
  · simp [same]

theorem writeByte_memory_frame (state : State) (address : Nat) (value : BitVec 8) :
    MemoryEqualOutside state { state with mem := state.mem.insert address value } address := by
  intro observed distinct
  symm
  change (state.mem.insert address value).get? observed = state.mem.get? observed
  simp only [Std.ExtHashMap.get?_eq_getElem?]
  rw [Std.ExtHashMap.getElem?_insert]
  by_cases same : address = observed
  · exact (distinct same.symm).elim
  · simp [same]

theorem writeReg_run (state : State) (written : Register) (value : RegisterType written) :
    (writeReg written value : SailM PUnit).run state =
      .ok PUnit.unit { state with regs := state.regs.insert written value } := by
  rfl

theorem writeReg_register_frame (state : State) (written : Register)
    (value : RegisterType written) :
    RegisterEqualOutside state { state with regs := state.regs.insert written value } written := by
  intro observed distinct
  change state.regs.get? observed = (state.regs.insert written value).get? observed
  rw [Std.ExtDHashMap.get?_insert]
  simp [Ne.symm distinct]

theorem writeReg_preserves_memory (state : State) (written : Register)
    (value : RegisterType written) :
    (match (writeReg written value : SailM PUnit).run state with
    | .ok _ state' => state'.mem
    | .error _ state' => state'.mem) = state.mem := by
  rfl

end BinaryFv.RISCV
