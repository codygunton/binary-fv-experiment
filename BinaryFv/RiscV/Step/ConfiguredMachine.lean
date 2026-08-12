import BinaryFv.RiscV.Step.AbstractPremise

/-!
# Machine configuration retained across ordinary endpoint instructions

`main` writes `x1` while forming call targets, so its stable machine-register set is the generated
platform set with `x1` removed. This bundle is target-neutral: a target supplies only its owned-PC
predicate and concrete entry state. File-backed code and application memory remain target facts.
-/

namespace BinaryFv.RiscV

open PreSail LeanRV64DExecutable.Functions Register

/-- Platform registers needed by instruction retirement, excluding the link register written by
ordinary `auipc`/`jalr` call setup. -/
def instructionPreserved (register : Register) : Prop :=
  platformPreserved register ∧ register ≠ x1

/-- Reusable machine facts for stepping every instruction whose PC satisfies `pcs`. -/
structure ConfiguredMachinePre (pcs : BitVec 64 → Prop) (state : State) : Prop where
  normal : NormalExecutionState state
  retiredCounter : RetiredCounterPresent state
  platform : AbstractPlatform instructionPreserved pcs state
  landingPad : AbstractElp instructionPreserved (fun _ => True) state

private theorem normalRegisters_instructionPreserved {register : Register}
    (member : normalRegisters register) : instructionPreserved register := by
  constructor
  · exact normalRegisters_platformPreserved register member
  · rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp

/-- Transport the configured machine to a state produced by an instruction frame.  Counter
presence is supplied separately because every retiring instruction changes `minstret`. -/
theorem ConfiguredMachinePre.mono {pcs : BitVec 64 → Prop} {before after : State}
    (configured : ConfiguredMachinePre pcs before)
    (agree : Agree instructionPreserved before after)
    (retiredAfter : RetiredCounterPresent after) : ConfiguredMachinePre pcs after where
  normal := normalExecutionState_of_agree
    (agree.weaken (fun _ member => normalRegisters_instructionPreserved member)) configured.normal
  retiredCounter := retiredAfter
  platform := configured.platform.mono agree
  landingPad := configured.landingPad.mono agree

/-- Narrow a configured machine to a smaller owned-PC predicate. -/
theorem ConfiguredMachinePre.restrict {wide narrow : BitVec 64 → Prop} {state : State}
    (subset : ∀ pc, narrow pc → wide pc) (configured : ConfiguredMachinePre wide state) :
    ConfiguredMachinePre narrow state where
  normal := configured.normal
  retiredCounter := configured.retiredCounter
  platform := fun target pc agree landed inside =>
    configured.platform target pc agree landed (subset pc inside)
  landingPad := configured.landingPad

end BinaryFv.RiscV
