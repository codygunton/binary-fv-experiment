import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HLevel3ForkNameSteps

/-!
# Level 3 fork-name dispatcher contract

This contract identifies the source fork selected by the schema byte. The machine exits at the
linked case block that materializes that fork's string, or at the reviewed rejection block.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

inductive ReviewedForkName where
  | frontier | homestead | daoFork | tangerineWhistle | spuriousDragon | byzantium
  | stPetersburg | istanbul | muirGlacier | berlin | london | arrowGlacier | grayGlacier
  | paris | shanghai | cancun | prague | osaka | bpo1 | bpo2 | amsterdam
  deriving DecidableEq

def reviewedForkNameForSchema : Nat → Option ReviewedForkName
  | 0x01 => some .frontier
  | 0x02 => some .homestead
  | 0x03 => some .daoFork
  | 0x04 => some .tangerineWhistle
  | 0x05 => some .spuriousDragon
  | 0x06 => some .byzantium
  | 0x07 => some .stPetersburg
  | 0x08 => some .istanbul
  | 0x09 => some .muirGlacier
  | 0x0a => some .berlin
  | 0x0b => some .london
  | 0x0c => some .arrowGlacier
  | 0x0d => some .grayGlacier
  | 0x0e => some .paris
  | 0x0f => some .shanghai
  | 0x10 => some .cancun
  | 0x11 => some .prague
  | 0x12 => some .osaka
  | 0x13 => some .bpo1
  | 0x14 => some .bpo2
  | 0x15 => some .amsterdam
  | _ => none

def reviewedForkNameTarget : ReviewedForkName → Nat
  | .frontier => 0x126a4
  | .homestead => 0x1224c
  | .daoFork => 0x125cc
  | .tangerineWhistle => 0x125ec
  | .spuriousDragon => 0x1259c
  | .byzantium => 0x12628
  | .stPetersburg => 0x12658
  | .istanbul => 0x125fc
  | .muirGlacier => 0x12688
  | .berlin => 0x125bc
  | .london => 0x12678
  | .arrowGlacier => 0x1258c
  | .grayGlacier => 0x125ac
  | .paris => 0x12648
  | .shanghai => 0x12580
  | .cancun => 0x125dc
  | .prague => 0x12570
  | .osaka => 0x12608
  | .bpo1 => 0x12668
  | .bpo2 => 0x12698
  | .amsterdam => 0x12618

def reviewedForkNameSchema : ReviewedForkName → Nat
  | .frontier => 0x01
  | .homestead => 0x02
  | .daoFork => 0x03
  | .tangerineWhistle => 0x04
  | .spuriousDragon => 0x05
  | .byzantium => 0x06
  | .stPetersburg => 0x07
  | .istanbul => 0x08
  | .muirGlacier => 0x09
  | .berlin => 0x0a
  | .london => 0x0b
  | .arrowGlacier => 0x0c
  | .grayGlacier => 0x0d
  | .paris => 0x0e
  | .shanghai => 0x0f
  | .cancun => 0x10
  | .prague => 0x11
  | .osaka => 0x12
  | .bpo1 => 0x13
  | .bpo2 => 0x14
  | .amsterdam => 0x15

def reviewedForkNameTableAddress (fork : ReviewedForkName) : Nat :=
  0x17228 + 8 * (reviewedForkNameSchema fork - 1)

/-- The pinned file bytes contain every reviewed fork-name jump-table target. -/
theorem reviewedForkNameTableRep (fork : ReviewedForkName)
    {memory : Std.ExtHashMap Nat (BitVec 8)}
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully memory) :
    UIntRep 8 memory (reviewedForkNameTableAddress fork) (reviewedForkNameTarget fork) := by
  refine ⟨?_, ?_, ?_⟩
  · cases fork <;> native_decide
  · cases fork <;> native_decide
  · intro index bound
    have indexCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
        index = 5 ∨ index = 6 ∨ index = 7 := by omega
    let address := reviewedForkNameTableAddress fork + index
    let byte := (Artifacts.programImage.readFileByte? address).getD 0
    have read : Artifacts.programImage.readFileByte? address = some byte := by
      cases fork <;>
        rcases indexCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        native_decide
    rw [loaded address byte read, UIntRep.byteAt_eq]
    cases fork <;>
      rcases indexCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      native_decide

structure ForkNameArgs where
  schema : Nat
  selected : Option ReviewedForkName
  tableAddress : Nat

def forkNameSelectionEntry (args : ForkNameArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 0x1221c) ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.schema) ∧
  ConfiguredMachinePre EndpointMachinePc state.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  match args.selected with
  | none =>
      reviewedForkNameForSchema args.schema = none ∧
      zopz0zI_u 20 (forkNameSchemaIndex args.schema) = true
  | some fork =>
      reviewedForkNameForSchema args.schema = some fork ∧
      zopz0zI_u 20 (forkNameSchemaIndex args.schema) = false ∧
      BitVec.ofNat 64 args.tableAddress =
        0x17228 + forkNameTableOffset (forkNameSchemaIndex args.schema) ∧
      UIntRep 8 state.machine.mem args.tableAddress (reviewedForkNameTarget fork) ∧
      LoadPmaAllows state.machine (BitVec.ofNat 64 args.tableAddress) 8 ∧
      LoadMMIOAddressExcluded (BitVec.ofNat 64 args.tableAddress) 8 ∧
      args.tableAddress < 2 ^ 64 ∧ args.tableAddress % 8 = 0 ∧
      Sail.BitVec.access (BitVec.ofNat 64 (reviewedForkNameTarget fork)) 1 = 0#1 ∧
      Sail.BitVec.update (BitVec.ofNat 64 (reviewedForkNameTarget fork)) 0 0#1 =
        BitVec.ofNat 64 (reviewedForkNameTarget fork)

def forkNameSelectionExit (args : ForkNameArgs) (outcome : Option ReviewedForkName)
    (before after : EndpointState) : Prop :=
  outcome = args.selected ∧
  after.machine.regs.get? PC = some (BitVec.ofNat 64
    (match args.selected with | none => 0x12638 | some fork => reviewedForkNameTarget fork)) ∧
  WritesOnlyRegs forkNameWrites before.machine after.machine ∧
  after.machine.mem = before.machine.mem ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine

def forkNameSelectionContract :
    RelationalMachineContract EndpointState ForkNameArgs (Option ReviewedForkName) :=
  { allows := fun args outcome => outcome = args.selected
    entry := forkNameSelectionEntry
    exit := forkNameSelectionExit
    stepBound := fun _ => 12 }

private theorem forkNameOwnPc_not_observed {pc : BitVec 64}
    (inside : forkNameOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold forkNameOwnPc pcInList at inside
  unfold BareMetalHostTransitionPc at observed
  unfold readContextReturnPc writeContextReturnPc exitContextStorePc at observed
  simp at inside
  rcases observed with observed | observed | observed
  all_goals omega

private theorem liftForkNameTrace (template : EndpointState)
    {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace forkNameOwnPc forkNameExitPc
      (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc forkNameOwnPc fromStep count
      { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step (stepRelation := EndpointStep) (statePc := EndpointPc)
        fromStep count pc { template with machine := before } { template with machine := middle }
        { template with machine := after } atPc inside ?_ ?_
      · exact endpointStep_sail fromStep { template with machine := before } middle
          (fun observed observedPc => by
            change before.regs.get? PC = some observed at observedPc
            rw [atPc] at observedPc
            cases Option.some.inj observedPc
            exact forkNameOwnPc_not_observed inside)
          machineStep
      · simpa using ih
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count callSite program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

private theorem forkNameExit_selected (fork : ReviewedForkName) :
    forkNameExitPc (BitVec.ofNat 64 (reviewedForkNameTarget fork)) := by
  cases fork <;> unfold forkNameExitPc pcInList <;> native_decide

/-- The production fork-name dispatcher satisfies its source-reviewed finite-selection contract. -/
theorem forkNameSelectionContract_implements :
    forkNameSelectionContract.Implements EndpointStep EndpointPc forkNameOwnPc forkNameExitPc := by
  intro args fromStep before entry
  rcases entry with ⟨atPc, schemaAt, configured, loaded, selection⟩
  cases selectedEq : args.selected with
  | none =>
      simp only [selectedEq] at selection
      obtain ⟨finalMachine, seg⟩ := forkNameRejectedRun fromStep args.schema before.machine
        configured atPc schemaAt selection.2 loaded
      let after : EndpointState := { before with machine := finalMachine }
      have endTrace : ScopedTrace forkNameOwnPc forkNameExitPc
          (fun _ _ _ _ _ => False) (fromStep + 3) 0 finalMachine finalMachine :=
        .exitAt (fromStep + 3) finalMachine 0x12638 seg.atPc (by
          unfold forkNameExitPc pcInList
          native_decide)
      have machineTrace : ScopedTrace forkNameOwnPc forkNameExitPc
          (fun _ _ _ _ _ => False) fromStep 3 before.machine finalMachine := by
        simpa using seg.confined 0 finalMachine endTrace
      refine ⟨3, after, none, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · change 3 ≤ 12
        omega
      · simpa [after] using liftForkNameTrace before machineTrace
      · exact ⟨0x12638, seg.atPc, by unfold forkNameExitPc pcInList; native_decide⟩
      · exact selectedEq.symm
      · refine ⟨selectedEq.symm, ?_, seg.writes, seg.memEq noMemory_empty,
          rfl, rfl, rfl, rfl,
          seg.retired, ?_, seg.aux⟩
        · simpa [selectedEq] using seg.atPc
        · rw [seg.memEq noMemory_empty]
          exact loaded
  | some fork =>
      simp only [selectedEq] at selection
      rcases selection with ⟨meaning, accepted, tableEq, targetRep, targetPma, targetNotMMIO,
        tableFits, tableAligned, targetAligned, targetUpdate⟩
      obtain ⟨finalMachine, seg⟩ := forkNameAcceptedRun fromStep args.schema
        args.tableAddress (reviewedForkNameTarget fork) before.machine configured atPc schemaAt
        accepted tableEq targetRep targetPma targetNotMMIO tableFits tableAligned targetAligned
        targetUpdate loaded
      let after : EndpointState := { before with machine := finalMachine }
      have endTrace : ScopedTrace forkNameOwnPc forkNameExitPc
          (fun _ _ _ _ _ => False) (fromStep + 12) 0 finalMachine finalMachine :=
        .exitAt (fromStep + 12) finalMachine
          (BitVec.ofNat 64 (reviewedForkNameTarget fork)) seg.atPc (forkNameExit_selected fork)
      have machineTrace : ScopedTrace forkNameOwnPc forkNameExitPc
          (fun _ _ _ _ _ => False) fromStep 12 before.machine finalMachine := by
        simpa using seg.confined 0 finalMachine endTrace
      refine ⟨12, after, some fork, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · change 12 ≤ 12
        omega
      · simpa [after] using liftForkNameTrace before machineTrace
      · exact ⟨BitVec.ofNat 64 (reviewedForkNameTarget fork), seg.atPc,
          forkNameExit_selected fork⟩
      · exact selectedEq.symm
      · refine ⟨selectedEq.symm, ?_, seg.writes, seg.memEq noMemory_empty,
          rfl, rfl, rfl, rfl,
          seg.retired, ?_, seg.aux⟩
        · simpa [selectedEq] using seg.atPc
        · rw [seg.memEq noMemory_empty]
          exact loaded

def Proposed_ssz_forkNameFromSchemaByte_fi_1_2fe4_Contract : Prop :=
  forkNameSelectionContract.Implements EndpointStep EndpointPc forkNameOwnPc forkNameExitPc

theorem proposed_forkNameFromSchemaByte_proved :
    Proposed_ssz_forkNameFromSchemaByte_fi_1_2fe4_Contract :=
  forkNameSelectionContract_implements

end BinaryFv.Zesu.Staging
