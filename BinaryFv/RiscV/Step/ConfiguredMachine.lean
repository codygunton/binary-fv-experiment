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
  seccfgPresent : ∃ bits, state.regs.get? mseccfg = some bits
  platform : AbstractPlatform instructionPreserved pcs state
  landingPad : AbstractElp instructionPreserved (fun _ => True) state

/-- The counter-increment prefix of `try_step` preserves every configured-machine register. -/
theorem agree_tryStepIncrement_instructionPreserved (state : State) :
    Agree instructionPreserved state (tryStepControlFlowAfterIncrement state) := by
  intro register preserved
  simpa [tryStepControlFlowAfterIncrement] using
    (writeReg_read_unchanged state minstret_increment register true (by
      rintro rfl
      simpa [platformPreserved] using preserved.1))

/-- Fetch, interrupt, and landing-pad premises at one configured instruction address. -/
theorem ConfiguredMachinePre.stepContext {pcs : BitVec 64 → Prop} {state : State}
    (configured : ConfiguredMachinePre pcs state) (pc : BitVec 64)
    (atPc : state.regs.get? PC = some pc) (inside : pcs pc) :
    FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc ∧
      FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc ∧
      InterruptDisabled (tryStepControlFlowAfterIncrement state) ∧
      LandingPadNotExpected (tryStepControlFlowAfterIncrement state) := by
  apply configured.platform _ pc (agree_tryStepIncrement_instructionPreserved state)
  · calc
      (tryStepControlFlowAfterIncrement state).regs.get? PC = state.regs.get? PC := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment PC true (by decide)
      _ = some pc := atPc
  · exact inside

/-- The concrete zero-inhibit retirement context fixed by `NormalExecutionState`. -/
theorem ConfiguredMachinePre.counters {pcs : BitVec 64 → Prop} {state : State}
    (configured : ConfiguredMachinePre pcs state) :
    ∃ retired, RetirementContext state retired 0 0 := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  refine ⟨retired, configured.normal.1, configured.normal.2.2.2.2.2.2.2.2.1,
    configured.normal.2.2.2.2.2.2.2.2.2.1, ?_, ?_, retiredRead⟩ <;> rfl

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
  seccfgPresent := by
    obtain ⟨bits, read⟩ := configured.seccfgPresent
    exact ⟨bits, (agree mseccfg (by simp [instructionPreserved, platformPreserved])).trans read⟩
  platform := configured.platform.mono agree
  landingPad := configured.landingPad.mono agree

/-- Narrow a configured machine to a smaller owned-PC predicate. -/
theorem ConfiguredMachinePre.restrict {wide narrow : BitVec 64 → Prop} {state : State}
    (subset : ∀ pc, narrow pc → wide pc) (configured : ConfiguredMachinePre wide state) :
    ConfiguredMachinePre narrow state where
  normal := configured.normal
  retiredCounter := configured.retiredCounter
  seccfgPresent := configured.seccfgPresent
  platform := fun target pc agree landed inside =>
    configured.platform target pc agree landed (subset pc inside)
  landingPad := configured.landingPad

end BinaryFv.RiscV
