import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4Contracts

/-! # `decodeExecutionWitness` error handoff into the rejection phase

The generated `decodeExecutionWitness` route from `0x12730` hands control to direct parent PC
`0x12734`.  That PC belongs to `decodeRaw`'s rejection/cleanup phase, not the 67-PC specialized
phase: it materializes status `2` in `s1` before the shared error continuation at `0x12738`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open BinaryFv.Zesu.Elflings.GeneratedLevel4Attribution
open PreSail LeanRV64DExecutable.Functions Register RegisterWriteStep

def level4ExecutionWitnessRejectionPcs : List Nat := [0x12734]

abbrev Level4ExecutionWitnessRejectionPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4ExecutionWitnessRejectionPcs

theorem level4ExecutionWitnessRejectionPcs_subset_rejection :
    level4ExecutionWitnessRejectionPcs.all
      decodeRawRejectionCleanupStatusCopyEpiloguePcs.contains = true := by
  native_decide

theorem level4ExecutionWitnessRejectionPcs_not_specialized :
    level4ExecutionWitnessRejectionPcs.all
      (fun pc => !(decodeRawSpecializedDispatchReturnsSuccessPcs.contains pc)) = true := by
  native_decide

private theorem level4_executionWitness_rejection_parent :
    Level4ExecutionWitnessRejectionPcs (BitVec.ofNat 64 0x12734) := by
  simp [Level4ExecutionWitnessRejectionPcs, level4ExecutionWitnessRejectionPcs]

private theorem level4_executionWitness_rejection_owned :
    RegisterWriteStep.decodeRawExecutionPcs (BitVec.ofNat 64 0x12734) := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  native_decide

private theorem level4_executionWitness_75568_75572_target :
    (functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75568_75572).handoff.target =
      0x12734 := by rfl

/-- The generated carrier-route array is the finite domain of a `decodeExecutionWitness`
parent-route provider. -/
private theorem level4_executionWitness_carrier_route_cases {route : AttributionOutcomeCarrierRoute}
    (listed : route ∈ decodeExecutionWitnessInterface.carrierRoutes) :
    route =
        functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75548_75552 ∨
      route =
        functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75568_75572 ∨
      route =
        functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75568_75668 ∨
      route =
        functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75856_75576 ∨
      route =
        functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75908_75576 ∨
      route =
        functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_76036_76040 ∨
      route =
        functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_76064_76068 ∨
      route =
        functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_77868_75576 := by
  rw [show decodeExecutionWitnessInterface.carrierRoutes =
    functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoutes by rfl] at listed
  rw [functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoutes_exact] at listed
  simpa using listed

private theorem level4_executionWitness_rejection_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12734)) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x12734) stepRetired x9
        (BitVec.ofNat 64 2)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x12734 0x93 0x04 0x20 0x00 0x002#12 0#5 9#5 .ADDI atPc (rX_x0_run _)
    (by
      rw [show iTypeResult .ADDI 0x002#12 0#64 = BitVec.ofNat 64 2 by decide]
      exact wX_x9_run _ _)
    (pcIn := ⟨level4_executionWitness_rejection_owned, by native_decide⟩)

def level4ExecutionWitnessRejectionWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x9

private theorem decoderPreserved_level4ExecutionWitnessRejectionWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4ExecutionWitnessRejectionWrites := by
  intro r preserved written
  rcases preserved with ⟨notLink, platform⟩
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint r platform bookkeeping
  · simp [platformPreserved] at platform

/-- Concrete rejection-phase input from the `decodeExecutionWitness` generated handoff.
It is deliberately weaker than `Level4TerminalStatusReady`: the later rejection continuation owns
the remaining PC and derives its particular terminal store rather than treating this status write
as a completed semantic carrier. -/
structure Level4ExecutionWitnessRejectionHandoff {margs : DecoderMachineArgs} {origin before : State}
    (after : State) (fromStep : Nat) (frame : Level4DecodeRawParentFrame margs origin before) : Prop where
  trace : Trace fromStep 1 before after
  confined : ConfinedPrefix Level4ExecutionWitnessRejectionPcs (fun _ => False)
    (fun _ _ _ _ _ => False) fromStep 1 before after
  writes : WritesOnlyRegs level4ExecutionWitnessRejectionWrites before after
  memory : after.mem = before.mem
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x12738)
  status : after.regs.get? x9 = some (BitVec.ofNat 64 2)
  preserved : frame.PreservedTo after

/-- Execute the direct `li s1,2` at the generated execution-witness error handoff and retain the
single original raw-decoder frame for the rejection phase. -/
theorem level4_executionWitness_rejection_handoff {margs : DecoderMachineArgs} {origin state : State}
    (frame : Level4DecodeRawParentFrame margs origin state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12734)) (fromStep : Nat) :
    ∃ after, Level4ExecutionWitnessRejectionHandoff after fromStep frame := by
  rcases frame.invariant with ⟨entry, stackEq, raEq, saved, sp, inputMemory, inputSeparated,
    stackWritable, rawWritable, rawSeparated, postStackAligned, code, machine, retired⟩
  let seg0 := Seg.nil Level4ExecutionWitnessRejectionPcs (fun _ => False)
    (fun _ _ _ _ _ => False) level4ExecutionWitnessRejectionWrites noMemory fromStep retired atPc
  obtain ⟨after, seg1⟩ := seg0.step level4_executionWitness_rejection_parent (by simp) x9
    (BitVec.ofNat 64 2) (BitVec.ofNat 64 0x12738)
    (level4_executionWitness_rejection_step machine (Agree.refl state) seg0.retired code
      fromStep seg0.atPc)
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4ExecutionWitnessRejectionWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have memory : after.mem = state.mem := seg1.memEq noMemory_empty
  have inputAfter : DecodedValue.MemoryBytes after margs.inputBase margs.bytes := by
    apply inputMemory.of_mem_eq
    intro index indexBound
    rw [memory]
  have codeAfter : Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
    rw [memory]
    exact code
  have spAfter : after.regs.get? x2 = some (BitVec.ofNat 64 entry.postStack) :=
    (seg1.writes x2 (by simp [level4ExecutionWitnessRejectionWrites])).trans sp
  have preserved : frame.PreservedTo after := by
    refine ⟨entry, stackEq, raEq, ?_, spAfter,
      inputAfter, inputSeparated, stackWritable, rawWritable, rawSeparated, postStackAligned,
      codeAfter, ?_, seg1.retired⟩
    · rw [Level4DecodeRawPrologueSavedFrame] at saved ⊢
      simp only [SavedWordBytes] at saved ⊢
      rw [memory]
      exact saved
    · exact machine.mono
        (seg1.agree decoderPreserved_level4ExecutionWitnessRejectionWrites_disjoint) seg1.retired
  exact ⟨after, ⟨seg1.trace, seg1.confined, seg1.writes, memory, seg1.atPc,
    seg1.reg x9 (BitVec.ofNat 64 2) (by simp), preserved⟩⟩

/-- The concrete rejection-phase predicate exported by the `0x12730 → 0x12734` generated route.
The later rejection proof receives the literal continuation PC and status value, not an arbitrary
phase choice or a completed dynamic-decoder semantic result. -/
def Level4ExecutionWitnessRejectionPhase
    (frame : Level4DecodeRawParentFrame margs origin initial) (state : State) : Prop :=
  state.regs.get? PC = some (BitVec.ofNat 64 0x12738) ∧
    state.regs.get? x9 = some (BitVec.ofNat 64 2) ∧ frame.PreservedTo state

/-- The generated `decodeExecutionWitness` H route `0x12730 → 0x12734` is resolved by one actual
parent Sail step into the typed rejection phase.  The enclosing exhaustive provider consumes finite
route membership to establish `routeEq` before invoking this route-specific theorem. -/
theorem level4_executionWitness_route_75568_75572_phase_decision
    {margs : DecoderMachineArgs} {origin initial current handoff : State}
    (frame : Level4DecodeRawParentFrame margs origin initial) (args : ContainerArgs)
    (rank : State → Nat) (fromStep : Nat)
    (progress : Level4HandoffProgress decodeExecutionWitnessInterface args origin fromStep current handoff)
    (_currentProtected : frame.PreservedTo current) (handoffProtected : frame.PreservedTo handoff)
    (routeEq : progress.route =
      functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75568_75572) :
    ParentRouteDecision decodeExecutionWitnessInterface args origin frame.PreservedTo
      (Level4ExecutionWitnessRejectionPhase frame) rank fromStep current handoff progress := by
  have atHandoff : handoff.regs.get? PC = some (BitVec.ofNat 64 0x12734) := by
    have target := progress.atTarget
    rw [routeEq] at target
    rw [level4_executionWitness_75568_75572_target] at target
    exact target
  obtain ⟨after, handoff⟩ := level4_executionWitness_rejection_handoff
    (frame.toState handoffProtected) atHandoff (fromStep + progress.prefixUsed + 1)
  exact .phaseHandoff after 1 handoff.trace handoff.preserved
    ⟨handoff.pc, handoff.status, handoff.preserved⟩

/-- The enclosing `decodeExecutionWitness` provider consumes its finite route membership to select
the `0x12730 → 0x12734` error case, then dispatches to the exact Sail rejection handoff. -/
theorem level4_executionWitness_provider_case_75572
    {margs : DecoderMachineArgs} {origin initial current handoff : State}
    (frame : Level4DecodeRawParentFrame margs origin initial) (args : ContainerArgs)
    (rank : State → Nat) (fromStep : Nat)
    (progress : Level4HandoffProgress decodeExecutionWitnessInterface args origin fromStep current handoff)
    (listed : progress.route ∈ decodeExecutionWitnessInterface.carrierRoutes)
    (currentProtected : frame.PreservedTo current) (handoffProtected : frame.PreservedTo handoff)
    (atHandoff : handoff.regs.get? PC = some (BitVec.ofNat 64 0x12734)) :
    ParentRouteDecision decodeExecutionWitnessInterface args origin frame.PreservedTo
      (Level4ExecutionWitnessRejectionPhase frame) rank fromStep current handoff progress := by
  have atTarget := progress.atTarget
  rcases level4_executionWitness_carrier_route_cases listed with routeEq | routeEq | routeEq | routeEq |
    routeEq | routeEq | routeEq | routeEq
  · rw [routeEq] at atTarget
    have pcConflict : some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12720) := by
      simpa [functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75548_75552] using atHandoff.symm.trans atTarget
    exact ((by decide : ¬ (some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12720))) pcConflict).elim
  · exact level4_executionWitness_route_75568_75572_phase_decision frame args rank fromStep progress
      currentProtected handoffProtected routeEq
  · rw [routeEq] at atTarget
    have pcConflict : some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12794) := by
      simpa [functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75568_75668] using atHandoff.symm.trans atTarget
    exact ((by decide : ¬ (some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12794))) pcConflict).elim
  · rw [routeEq] at atTarget
    have pcConflict : some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12738) := by
      simpa [functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75856_75576] using atHandoff.symm.trans atTarget
    exact ((by decide : ¬ (some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12738))) pcConflict).elim
  · rw [routeEq] at atTarget
    have pcConflict : some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12738) := by
      simpa [functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75908_75576] using atHandoff.symm.trans atTarget
    exact ((by decide : ¬ (some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12738))) pcConflict).elim
  · rw [routeEq] at atTarget
    have pcConflict : some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x128f8) := by
      simpa [functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_76036_76040] using atHandoff.symm.trans atTarget
    exact ((by decide : ¬ (some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x128f8))) pcConflict).elim
  · rw [routeEq] at atTarget
    have pcConflict : some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12914) := by
      simpa [functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_76064_76068] using atHandoff.symm.trans atTarget
    exact ((by decide : ¬ (some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12914))) pcConflict).elim
  · rw [routeEq] at atTarget
    have pcConflict : some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12738) := by
      simpa [functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_77868_75576] using atHandoff.symm.trans atTarget
    exact ((by decide : ¬ (some (BitVec.ofNat 64 0x12734) = some (BitVec.ofNat 64 0x12738))) pcConflict).elim

/-- The generated `decodeExecutionWitness` route `0x12850 → 0x12738` reaches its selected carrier
without an additional parent instruction: its exact carrier path is the terminal singleton
`[0x12738]`.  The semantic result remains supplied by the child's `CarrierObligation`. -/
theorem level4_executionWitness_route_75856_75576_carrier_decision
    {margs : DecoderMachineArgs} {origin initial current handoff : State}
    (frame : Level4DecodeRawParentFrame margs origin initial) (args : ContainerArgs)
    (rank : State → Nat) (fromStep : Nat)
    (progress : Level4HandoffProgress decodeExecutionWitnessInterface args origin fromStep current handoff)
    (_currentProtected : frame.PreservedTo current) (handoffProtected : frame.PreservedTo handoff)
    (routeEq : progress.route =
      functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75856_75576) :
    ParentRouteDecision decodeExecutionWitnessInterface args origin frame.PreservedTo
      (Level4ExecutionWitnessRejectionPhase frame) rank fromStep current handoff progress := by
  let carrierPath : CarrierPath := { carrierPc := 75576, pcs := #[75576] }
  have target : handoff.regs.get? PC = some (BitVec.ofNat 64 75576) := by
    have atTarget := progress.atTarget
    rw [routeEq] at atTarget
    simpa [functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75856_75576] using atTarget
  refine .carrier ?_ ?_
  · rw [routeEq]
    rfl
  · intro path listed _terminal
    rw [routeEq] at listed
    have pathEq : path = carrierPath := by
      simpa [carrierPath,
        functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75856_75576] using listed
    subst path
    refine ⟨handoff, ?_, ?_, handoffProtected⟩
    · refine {
        path := carrierPath
        listed := ?_
        startsAtTarget := ?_
        endsAtCarrier := ?_
        exactPcs := ?_
        exactTrace := ?_
        trace := ?_ }
      · rw [routeEq]
        simp [carrierPath,
          functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75856_75576]
      · rw [routeEq]
        simpa [carrierPath,
          functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75856_75576] using target
      · simpa [carrierPath] using target
      · rw [routeEq]
        rfl
      · simpa [carrierPath] using
          ExactCarrierPathTrace.terminal (fromStep + progress.prefixUsed + 1) 75576 handoff target
      · exact ⟨0, Trace.refl (fromStep + progress.prefixUsed + 1) handoff⟩
    · rfl

end BinaryFv.Zesu.MachineExecution
