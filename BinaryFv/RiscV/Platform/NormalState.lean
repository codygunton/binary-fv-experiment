import BinaryFv.RiscV.Model.State

/-!
# Inert platform state for normal execution
-/

namespace BinaryFv.RiscV

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- Inert platform state for normal direct execution; ABI and memory predicates remain separate. -/
def NormalExecutionState (state : State) : Prop :=
  state.regs.get? hart_state = some (HartState.HART_ACTIVE ()) ∧
    state.regs.get? cur_privilege = some Privilege.Machine ∧
      state.regs.get? satp = some (0 : BitVec 64) ∧
        state.regs.get? mideleg = some (0 : BitVec 64) ∧
          state.regs.get? mie = some (0 : BitVec 64) ∧
            state.regs.get? mip = some (0 : BitVec 64) ∧
              state.regs.get? pmpcfg_n = some (default : Vector (BitVec 8) 64) ∧
                state.regs.get? pmpaddr_n = some (default : Vector (BitVec 64) 64) ∧
                  state.regs.get? mcountinhibit = some (0 : BitVec 32) ∧
                    state.regs.get? minstretcfg = some (0 : BitVec 64) ∧
                      state.regs.get? elp = some
                        (landing_pad_bits_backwards landing_pad_expectation.NO_LP_EXPECTED) ∧
                        match state.regs.get? misa with
                        | some misaBits => Sail.BitVec.access misaBits 12 = 1#1
                        | none => False

end BinaryFv.RiscV
