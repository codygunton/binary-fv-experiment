import BinaryFv.Ssz.Level0MainSteps
import BinaryFv.Ssz.Level1Contracts

/-!
# Level 0 endpoint contract

This file composes the 24 instructions owned by `main` with the six immediate Level 1 contracts.
The first declarations establish the common execution region and the frame transports used after a
returning opaque call.
-/

namespace BinaryFv.Ssz

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.RiscV

/-- Every instruction selected at Level 0: parent-owned glue or one of its six opaque callees. -/
def MainExecutionPc (pc : BitVec 64) : Prop :=
  mainGluePcs pc ∨
  pcInRanges Generated.readInputExecutionPcRanges pc ∨
  pcInRanges Generated.allocatorGetExecutionPcRanges pc ∨
  DecodeExecutionPc pc ∨
  pcInRanges Generated.writeSuccessExecutionPcRanges pc ∨
  pcInRanges Generated.writeFailureExecutionPcRanges pc ∨
  pcInRanges Generated.zkvmExitExecutionPcRanges pc

private theorem instructionPreserved_abiCalleePreserved (register : Register)
    (preserved : instructionPreserved register) : abiCalleePreserved register := by
  rcases preserved.1 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  all_goals simp [abiCalleePreserved]

/-- A reviewed returning ABI contract restores the configured-machine premise needed by the next
Level 0 instruction. `minstret` is retained by presence rather than by false value equality. -/
theorem ConfiguredMachinePre.of_endpointCallFrame {before after : EndpointState}
    (configured : ConfiguredMachinePre mainGluePcs before.machine)
    (frame : EndpointCallFrame before after) :
    ConfiguredMachinePre mainGluePcs after.machine :=
  configured.mono
    (frame.1.weaken instructionPreserved_abiCalleePreserved)
    frame.2.1

/-- One exact non-syscall Sail instruction, lifted into and confined by the complete Level 0 region. -/
theorem main_confined_sail_step (stepNo : Nat) (before : EndpointState) (after : MachineState)
    (pc : BitVec 64) (atPc : EndpointPc before = some pc) (inside : mainGluePcs pc)
    (notSyscall : ¬ LinuxSyscallPc pc) (step : MachineStep stepNo before.machine after) :
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc stepNo 1 before
      { before with machine := after } := by
  apply ConfinedTrace.step stepNo 0 pc before { before with machine := after }
    { before with machine := after }
  · exact atPc
  · exact Or.inl inside
  · exact endpointStep_sail stepNo before after (fun target targetPc => by
      rw [atPc] at targetPc
      cases Option.some.inj targetPc
      exact notSyscall) step
  · exact .refl (stepNo + 1) _

end BinaryFv.Ssz
