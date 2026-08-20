import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HLevel3CheckedSliceSteps

/-!
# Level 3 checked-slice contracts

The five inlined source instances use one source meaning. Each machine instance supplies its exact
entry bindings, exit PCs, register frame, and memory frame.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

structure CheckedSliceArgs where
  stackPointer : Nat
  sourceAddress : Nat
  sourceBytes : Array UInt8
  present : Bool
  startOffset : Nat
  endOffset : Nat

inductive CheckedSliceOutcome where
  | empty
  | invalid
  | selected (bytes : Array UInt8)
  deriving DecidableEq

/-- The source result of `getSlice`: reject reversed or oversized bounds, otherwise select bytes. -/
def checkedSliceMeaning (args : CheckedSliceArgs) : CheckedSliceOutcome :=
  if !args.present then .empty
  else if args.endOffset < args.startOffset then .invalid
  else if args.sourceBytes.size < args.endOffset then .invalid
  else .selected (args.sourceBytes.extract args.startOffset args.endOffset)

/-- Shared semantic contract schema for every inlined checked-slice instance. -/
def checkedSliceContract
    (machineEntry : CheckedSliceArgs → EndpointState → Prop)
    (machineExit : CheckedSliceArgs → CheckedSliceOutcome →
      EndpointState → EndpointState → Prop)
    (stepBound : CheckedSliceArgs → Nat) :
    RelationalMachineContract EndpointState CheckedSliceArgs CheckedSliceOutcome :=
  { allows := fun args outcome => outcome = checkedSliceMeaning args
    entry := machineEntry
    exit := fun args outcome before after =>
      outcome = checkedSliceMeaning args ∧ machineExit args outcome before after
    stepBound := stepBound }

def checkedSlice351cEntry (args : CheckedSliceArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some 0x130b0 ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.sourceBytes.size) ∧
  args.present = true ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x1a0) args.startOffset ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x4f8) args.endOffset ∧
  BytesRep state.machine.mem args.sourceAddress args.sourceBytes ∧
  args.sourceBytes.size < 2 ^ 64 ∧
  (∀ index, index < args.sourceBytes.size →
    ¬checkedSlice351cMemory args.stackPointer (args.sourceAddress + index)) ∧
  CheckedSliceMachineAccess args.stackPointer state.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def checkedSlice351cSelectedRep (args : CheckedSliceArgs) (outcome : CheckedSliceOutcome)
    (state : EndpointState) : Prop :=
  match outcome with
  | .empty => True
  | .invalid => True
  | .selected bytes =>
      bytes = args.sourceBytes.extract args.startOffset args.endOffset ∧
      BytesRep state.machine.mem (args.sourceAddress + args.startOffset) bytes

def checkedSlice351cExit (args : CheckedSliceArgs) (outcome : CheckedSliceOutcome)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (match outcome with
    | .empty => 0x130c8
    | .invalid => 0x13db0
    | .selected _ => 0x130c8) ∧
  checkedSlice351cSelectedRep args outcome after ∧
  BytesRep after.machine.mem args.sourceAddress args.sourceBytes ∧
  WritesOnlyRegs checkedSlice351cWrites before.machine after.machine ∧
  WritesOnlyWithin (checkedSlice351cMemory args.stackPointer) before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode

def checkedSlice351cContract :
    RelationalMachineContract EndpointState CheckedSliceArgs CheckedSliceOutcome :=
  checkedSliceContract checkedSlice351cEntry checkedSlice351cExit (fun _ => 6)

private theorem checkedSliceComparisonOfNat (left right : Nat)
    (leftFits : left < 2 ^ 64) (rightFits : right < 2 ^ 64) :
    zopz0zI_u (BitVec.ofNat 64 left) (BitVec.ofNat 64 right) = decide (left < right) := by
  simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt leftFits, Nat.mod_eq_of_lt rightFits]
  simp

private theorem checkedSlice351cOwnPc_not_observed {pc : BitVec 64}
    (inside : checkedSlice351cOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold checkedSlice351cOwnPc pcInList at inside
  unfold BareMetalHostTransitionPc at observed
  unfold readContextReturnPc writeContextReturnPc exitContextStorePc at observed
  simp at inside
  rcases observed with observed | observed | observed
  all_goals omega

private theorem liftCheckedSliceTrace (template : EndpointState)
    {own exit : BitVec 64 → Prop} {fromStep count : Nat} {before after : State}
    (ownNotObserved : ∀ {pc}, own pc → ¬BareMetalHostTransitionPc pc)
    (trace : ScopedTrace own exit (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc own fromStep count
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
            exact ownNotObserved inside)
          machineStep
      · simpa using ih
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count callSite program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

private theorem liftCheckedSlice351cTrace (template : EndpointState)
    {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace checkedSlice351cOwnPc checkedSlice351cExitPc
      (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc checkedSlice351cOwnPc fromStep count
      { template with machine := before } { template with machine := after } :=
  liftCheckedSliceTrace template checkedSlice351cOwnPc_not_observed trace

private theorem sourceRepOfCheckedSliceSeg {args : CheckedSliceArgs}
    {own exit : BitVec 64 → Prop} {W : RegSet} {M : Region} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (sourceRep : BytesRep before.mem args.sourceAddress args.sourceBytes)
    (outside : ∀ index, index < args.sourceBytes.size → ¬M (args.sourceAddress + index))
    (seg : Seg own exit (fun _ _ _ _ _ => False) W M
      kv fromStep count before after pc) :
    BytesRep after.mem args.sourceAddress args.sourceBytes :=
  sourceRep.of_writesOnlyWithin seg.mem outside

private theorem sourceRepOfSeg {args : CheckedSliceArgs} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (sourceRep : BytesRep before.mem args.sourceAddress args.sourceBytes)
    (outside : ∀ index, index < args.sourceBytes.size →
      ¬checkedSlice351cMemory args.stackPointer (args.sourceAddress + index))
    (seg : Seg checkedSlice351cOwnPc checkedSlice351cExitPc (fun _ _ _ _ _ => False)
      checkedSlice351cWrites (checkedSlice351cMemory args.stackPointer)
      kv fromStep count before after pc) :
    BytesRep after.mem args.sourceAddress args.sourceBytes :=
  sourceRepOfCheckedSliceSeg sourceRep outside seg

private theorem checkedSliceEndTrace {own exit : BitVec 64 → Prop}
    {fromStep count : Nat} {state : State} {pc : BitVec 64}
    (atPc : state.regs.get? PC = some pc) (exitPc : exit pc) :
    ScopedTrace own exit (fun _ _ _ _ _ => False) (fromStep + count) 0 state state :=
  .exitAt (fromStep + count) state pc atPc exitPc

private theorem checkedSlice351cEndTrace {fromStep count : Nat} {state : State}
    {pc : BitVec 64} (atPc : state.regs.get? PC = some pc)
    (exitPc : checkedSlice351cExitPc pc) :
    ScopedTrace checkedSlice351cOwnPc checkedSlice351cExitPc
      (fun _ _ _ _ _ => False) (fromStep + count) 0 state state :=
  checkedSliceEndTrace atPc exitPc

/-- The production `fi:1:351c` instance satisfies the shared checked-slice contract. -/
theorem checkedSlice351cContract_implements :
    checkedSlice351cContract.Implements EndpointStep EndpointPc
      checkedSlice351cOwnPc checkedSlice351cExitPc := by
  intro args fromStep before entry
  rcases entry with ⟨atPc, lengthAt, present, startRep, endRep, sourceRep, lengthFits,
    sourceOutside, access, loaded⟩
  have startFits := startRep.1
  have endFits := endRep.1
  by_cases reversed : args.endOffset < args.startOffset
  · have comparison : zopz0zI_u (BitVec.ofNat 64 args.endOffset)
        (BitVec.ofNat 64 args.startOffset) = true := by
      rw [checkedSliceComparisonOfNat args.endOffset args.startOffset endFits startFits]
      simp [reversed]
    obtain ⟨finalMachine, seg⟩ := checkedSlice351cInvalidStartEndRun fromStep
      args.stackPointer args.startOffset args.endOffset before.machine access atPc startRep endRep
      comparison loaded
    let after : EndpointState := { before with machine := finalMachine }
    have machineTrace : ScopedTrace checkedSlice351cOwnPc checkedSlice351cExitPc
        (fun _ _ _ _ _ => False) fromStep 4 before.machine finalMachine := by
      exact seg.confined 0 finalMachine
        (checkedSlice351cEndTrace seg.atPc (by unfold checkedSlice351cExitPc pcInList; native_decide))
    refine ⟨4, after, .invalid, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · change 4 ≤ 6
      omega
    · simpa [after] using liftCheckedSlice351cTrace before machineTrace
    · exact ⟨0x13db0, seg.atPc, by unfold checkedSlice351cExitPc pcInList; native_decide⟩
    · simp [checkedSlice351cContract, checkedSliceContract, checkedSliceMeaning, present, reversed]
    · refine ⟨by simp [checkedSliceMeaning, present, reversed], ?_, ?_, ?_, seg.writes, seg.mem,
        seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
      · simpa [after] using seg.atPc
      · simp [checkedSlice351cSelectedRep]
      · exact sourceRepOfSeg sourceRep sourceOutside seg
      · exact checkedSlice351cCodeOfSeg access loaded seg
  · have startEndComparison : zopz0zI_u (BitVec.ofNat 64 args.endOffset)
        (BitVec.ofNat 64 args.startOffset) = false := by
      rw [checkedSliceComparisonOfNat args.endOffset args.startOffset endFits startFits]
      simp [reversed]
    by_cases oversized : args.sourceBytes.size < args.endOffset
    · have lengthComparison : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
          (BitVec.ofNat 64 args.endOffset) = true := by
        rw [checkedSliceComparisonOfNat args.sourceBytes.size args.endOffset lengthFits endFits]
        simp [oversized]
      obtain ⟨finalMachine, seg⟩ := checkedSlice351cLengthCheckedRun fromStep
        args.stackPointer args.sourceBytes.size args.startOffset args.endOffset before.machine
        access atPc lengthAt startRep endRep startEndComparison lengthComparison loaded
      let after : EndpointState := { before with machine := finalMachine }
      have machineTrace : ScopedTrace checkedSlice351cOwnPc checkedSlice351cExitPc
          (fun _ _ _ _ _ => False) fromStep 6 before.machine finalMachine := by
        exact seg.confined 0 finalMachine
          (checkedSlice351cEndTrace seg.atPc
            (by unfold checkedSlice351cExitPc pcInList; native_decide))
      refine ⟨6, after, .invalid, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · change 6 ≤ 6
        omega
      · simpa [after] using liftCheckedSlice351cTrace before machineTrace
      · exact ⟨0x13db0, seg.atPc, by unfold checkedSlice351cExitPc pcInList; native_decide⟩
      · simp [checkedSlice351cContract, checkedSliceContract, checkedSliceMeaning, present, reversed,
          oversized]
      · refine ⟨by simp [checkedSliceMeaning, present, reversed, oversized], ?_, ?_, ?_, seg.writes,
          seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
        · simpa [after] using seg.atPc
        · simp [checkedSlice351cSelectedRep]
        · exact sourceRepOfSeg sourceRep sourceOutside seg
        · exact checkedSlice351cCodeOfSeg access loaded seg
    · have lengthComparison : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
          (BitVec.ofNat 64 args.endOffset) = false := by
        rw [checkedSliceComparisonOfNat args.sourceBytes.size args.endOffset lengthFits endFits]
        simp [oversized]
      obtain ⟨finalMachine, seg⟩ := checkedSlice351cLengthCheckedRun fromStep
        args.stackPointer args.sourceBytes.size args.startOffset args.endOffset before.machine
        access atPc lengthAt startRep endRep startEndComparison lengthComparison loaded
      let selected := args.sourceBytes.extract args.startOffset args.endOffset
      let after : EndpointState := { before with machine := finalMachine }
      have machineTrace : ScopedTrace checkedSlice351cOwnPc checkedSlice351cExitPc
          (fun _ _ _ _ _ => False) fromStep 6 before.machine finalMachine := by
        exact seg.confined 0 finalMachine
          (checkedSlice351cEndTrace seg.atPc
            (by unfold checkedSlice351cExitPc pcInList; native_decide))
      have sourceAfter := sourceRepOfSeg sourceRep sourceOutside seg
      have selectedRep : BytesRep finalMachine.mem (args.sourceAddress + args.startOffset)
          selected := by
        have range := sourceAfter.extractRange args.startOffset
          (args.endOffset - args.startOffset) (by omega)
        have endEq : args.startOffset + (args.endOffset - args.startOffset) =
            args.endOffset := Nat.add_sub_of_le (by omega)
        rw [endEq] at range
        simpa [selected] using range
      refine ⟨6, after, .selected selected, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · change 6 ≤ 6
        omega
      · simpa [after] using liftCheckedSlice351cTrace before machineTrace
      · exact ⟨0x130c8, seg.atPc, by unfold checkedSlice351cExitPc pcInList; native_decide⟩
      · simp [checkedSlice351cContract, checkedSliceContract, checkedSliceMeaning, present, reversed,
          oversized, selected]
      · refine ⟨by simp [checkedSliceMeaning, present, reversed, oversized, selected], ?_, ?_,
          sourceAfter, seg.writes, seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
        · simpa [after] using seg.atPc
        · exact ⟨rfl, by simpa [after] using selectedRep⟩
        · exact checkedSlice351cCodeOfSeg access loaded seg

def Proposed_ssz_decode__struct_1051_f_fi_1_351c_Contract : Prop :=
  checkedSlice351cContract.Implements EndpointStep EndpointPc
    checkedSlice351cOwnPc checkedSlice351cExitPc

theorem proposed_checkedSlice_351c_proved :
    Proposed_ssz_decode__struct_1051_f_fi_1_351c_Contract :=
  checkedSlice351cContract_implements

/-! ## Request-type-zero checked slice -/

def checkedSlice34fdEntry (args : CheckedSliceArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some 0x13098 ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.sourceBytes.size) ∧
  args.present = true ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x4e8) args.startOffset ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x4f0) args.endOffset ∧
  BytesRep state.machine.mem args.sourceAddress args.sourceBytes ∧
  args.sourceBytes.size < 2 ^ 64 ∧
  (∀ index, index < args.sourceBytes.size →
    ¬checkedSlice34fdMemory args.stackPointer (args.sourceAddress + index)) ∧
  CheckedSliceMachineAccess args.stackPointer state.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def checkedSlice34fdSelectedRep (args : CheckedSliceArgs) (outcome : CheckedSliceOutcome)
    (state : EndpointState) : Prop :=
  match outcome with
  | .empty => True
  | .invalid => True
  | .selected bytes =>
      bytes = args.sourceBytes.extract args.startOffset args.endOffset ∧
      state.machine.regs.get? x13 = some (BitVec.ofNat 64 args.startOffset) ∧
      state.machine.regs.get? x12 = some (BitVec.ofNat 64 args.endOffset) ∧
      BytesRep state.machine.mem (args.sourceAddress + args.startOffset) bytes

def checkedSlice34fdExit (args : CheckedSliceArgs) (outcome : CheckedSliceOutcome)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (match outcome with
    | .empty => 0x130b0
    | .invalid => 0x13db0
    | .selected _ => 0x130b0) ∧
  checkedSlice34fdSelectedRep args outcome after ∧
  BytesRep after.machine.mem args.sourceAddress args.sourceBytes ∧
  WritesOnlyRegs checkedSlice34fdWrites before.machine after.machine ∧
  WritesOnlyWithin (checkedSlice34fdMemory args.stackPointer) before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode

def checkedSlice34fdContract :
    RelationalMachineContract EndpointState CheckedSliceArgs CheckedSliceOutcome :=
  checkedSliceContract checkedSlice34fdEntry checkedSlice34fdExit (fun _ => 6)

private theorem checkedSlice34fdOwnPc_not_observed {pc : BitVec 64}
    (inside : checkedSlice34fdOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold checkedSlice34fdOwnPc pcInList at inside
  unfold BareMetalHostTransitionPc at observed
  unfold readContextReturnPc writeContextReturnPc exitContextStorePc at observed
  simp at inside
  rcases observed with observed | observed | observed
  all_goals omega

private theorem sourceRepOf34fdSeg {args : CheckedSliceArgs} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (sourceRep : BytesRep before.mem args.sourceAddress args.sourceBytes)
    (outside : ∀ index, index < args.sourceBytes.size →
      ¬checkedSlice34fdMemory args.stackPointer (args.sourceAddress + index))
    (seg : Seg checkedSlice34fdOwnPc checkedSlice34fdExitPc
      (fun _ _ _ _ _ => False) checkedSlice34fdWrites
      (checkedSlice34fdMemory args.stackPointer) kv fromStep count before after pc) :
    BytesRep after.mem args.sourceAddress args.sourceBytes :=
  sourceRepOfCheckedSliceSeg sourceRep outside seg

private theorem checkedSlice34fdMachineTrace (template : EndpointState)
    {stackPointer fromStep count : Nat} {kv : List RegVal}
    {before after : State} {pc : BitVec 64}
    (seg : Seg checkedSlice34fdOwnPc checkedSlice34fdExitPc
      (fun _ _ _ _ _ => False) checkedSlice34fdWrites
      (checkedSlice34fdMemory stackPointer) kv fromStep count before after pc)
    (exitPc : checkedSlice34fdExitPc pc) :
    ConfinedTrace EndpointStep EndpointPc checkedSlice34fdOwnPc fromStep count
      { template with machine := before } { template with machine := after } := by
  have trace : ScopedTrace checkedSlice34fdOwnPc checkedSlice34fdExitPc
      (fun _ _ _ _ _ => False) fromStep count before after :=
    seg.confined 0 after (checkedSliceEndTrace seg.atPc exitPc)
  exact liftCheckedSliceTrace template checkedSlice34fdOwnPc_not_observed trace

/-- The production `fi:1:34fd` instance satisfies the shared checked-slice contract. -/
theorem checkedSlice34fdContract_implements :
    checkedSlice34fdContract.Implements EndpointStep EndpointPc
      checkedSlice34fdOwnPc checkedSlice34fdExitPc := by
  intro args fromStep before entry
  rcases entry with ⟨atPc, lengthAt, present, startRep, endRep, sourceRep, lengthFits,
    sourceOutside, access, loaded⟩
  have startFits := startRep.1
  have endFits := endRep.1
  by_cases reversed : args.endOffset < args.startOffset
  · have startEndComparison : zopz0zI_u (BitVec.ofNat 64 args.endOffset)
        (BitVec.ofNat 64 args.startOffset) = true := by
      rw [checkedSliceComparisonOfNat args.endOffset args.startOffset endFits startFits]
      simp [reversed]
    have lengthComparison : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
        (BitVec.ofNat 64 args.endOffset) =
          decide (args.sourceBytes.size < args.endOffset) :=
      checkedSliceComparisonOfNat _ _ lengthFits endFits
    obtain ⟨finalMachine, seg⟩ := checkedSlice34fdRun fromStep args.stackPointer
      args.sourceBytes.size args.startOffset args.endOffset before.machine access atPc lengthAt
      startRep endRep startEndComparison lengthComparison loaded
    change Seg checkedSlice34fdOwnPc checkedSlice34fdExitPc (fun _ _ _ _ _ => False)
      checkedSlice34fdWrites (checkedSlice34fdMemory args.stackPointer) _ fromStep 4
      before.machine finalMachine 0x13db0 at seg
    let after : EndpointState := { before with machine := finalMachine }
    refine ⟨4, after, .invalid, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · change 4 ≤ 6
      omega
    · exact checkedSlice34fdMachineTrace before seg
        (by unfold checkedSlice34fdExitPc pcInList; native_decide)
    · exact ⟨0x13db0, seg.atPc, by unfold checkedSlice34fdExitPc pcInList; native_decide⟩
    · simp [checkedSlice34fdContract, checkedSliceContract, checkedSliceMeaning, present, reversed]
    · refine ⟨by simp [checkedSliceMeaning, present, reversed], ?_, ?_, ?_, seg.writes, seg.mem,
        seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
      · simpa [after] using seg.atPc
      · simp [checkedSlice34fdSelectedRep]
      · exact sourceRepOf34fdSeg sourceRep sourceOutside seg
      · exact checkedSlice34fdCodeOfSeg access loaded seg
  · have startEndComparison : zopz0zI_u (BitVec.ofNat 64 args.endOffset)
        (BitVec.ofNat 64 args.startOffset) = false := by
      rw [checkedSliceComparisonOfNat args.endOffset args.startOffset endFits startFits]
      simp [reversed]
    by_cases oversized : args.sourceBytes.size < args.endOffset
    · have lengthComparison : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
          (BitVec.ofNat 64 args.endOffset) = true := by
        rw [checkedSliceComparisonOfNat args.sourceBytes.size args.endOffset lengthFits endFits]
        simp [oversized]
      obtain ⟨finalMachine, seg⟩ := checkedSlice34fdRun fromStep args.stackPointer
        args.sourceBytes.size args.startOffset args.endOffset before.machine access atPc lengthAt
        startRep endRep startEndComparison lengthComparison loaded
      change Seg checkedSlice34fdOwnPc checkedSlice34fdExitPc (fun _ _ _ _ _ => False)
        checkedSlice34fdWrites (checkedSlice34fdMemory args.stackPointer) _ fromStep 6
        before.machine finalMachine 0x13db0 at seg
      let after : EndpointState := { before with machine := finalMachine }
      refine ⟨6, after, .invalid, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · change 6 ≤ 6
        omega
      · exact checkedSlice34fdMachineTrace before seg
          (by unfold checkedSlice34fdExitPc pcInList; native_decide)
      · exact ⟨0x13db0, seg.atPc, by unfold checkedSlice34fdExitPc pcInList; native_decide⟩
      · simp [checkedSlice34fdContract, checkedSliceContract, checkedSliceMeaning, present, reversed,
          oversized]
      · refine ⟨by simp [checkedSliceMeaning, present, reversed, oversized], ?_, ?_, ?_, seg.writes,
          seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
        · simpa [after] using seg.atPc
        · simp [checkedSlice34fdSelectedRep]
        · exact sourceRepOf34fdSeg sourceRep sourceOutside seg
        · exact checkedSlice34fdCodeOfSeg access loaded seg
    · have lengthComparison : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
          (BitVec.ofNat 64 args.endOffset) = false := by
        rw [checkedSliceComparisonOfNat args.sourceBytes.size args.endOffset lengthFits endFits]
        simp [oversized]
      obtain ⟨finalMachine, seg⟩ := checkedSlice34fdRun fromStep args.stackPointer
        args.sourceBytes.size args.startOffset args.endOffset before.machine access atPc lengthAt
        startRep endRep startEndComparison lengthComparison loaded
      change Seg checkedSlice34fdOwnPc checkedSlice34fdExitPc (fun _ _ _ _ _ => False)
        checkedSlice34fdWrites (checkedSlice34fdMemory args.stackPointer) _ fromStep 6
        before.machine finalMachine 0x130b0 at seg
      let selected := args.sourceBytes.extract args.startOffset args.endOffset
      let after : EndpointState := { before with machine := finalMachine }
      have sourceAfter := sourceRepOf34fdSeg sourceRep sourceOutside seg
      have selectedRep : BytesRep finalMachine.mem (args.sourceAddress + args.startOffset)
          selected := by
        have range := sourceAfter.extractRange args.startOffset
          (args.endOffset - args.startOffset) (by omega)
        have endEq : args.startOffset + (args.endOffset - args.startOffset) =
            args.endOffset := Nat.add_sub_of_le (by omega)
        rw [endEq] at range
        simpa [selected] using range
      refine ⟨6, after, .selected selected, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · change 6 ≤ 6
        omega
      · exact checkedSlice34fdMachineTrace before seg
          (by unfold checkedSlice34fdExitPc pcInList; native_decide)
      · exact ⟨0x130b0, seg.atPc, by unfold checkedSlice34fdExitPc pcInList; native_decide⟩
      · simp [checkedSlice34fdContract, checkedSliceContract, checkedSliceMeaning, present, reversed,
          oversized, selected]
      · refine ⟨by simp [checkedSliceMeaning, present, reversed, oversized, selected], ?_, ?_,
          sourceAfter, seg.writes, seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
        · simpa [after] using seg.atPc
        · refine ⟨rfl, ?_, ?_, ?_⟩
          · simpa [after] using seg.reg x13 (BitVec.ofNat 64 args.startOffset) (by simp)
          · simpa [after] using seg.reg x12 (BitVec.ofNat 64 args.endOffset) (by simp)
          · simpa [after] using selectedRep
        · exact checkedSlice34fdCodeOfSeg access loaded seg

def Proposed_ssz_decode__struct_1051_f_fi_1_34fd_Contract : Prop :=
  checkedSlice34fdContract.Implements EndpointStep EndpointPc
    checkedSlice34fdOwnPc checkedSlice34fdExitPc

theorem proposed_checkedSlice_34fd_proved :
    Proposed_ssz_decode__struct_1051_f_fi_1_34fd_Contract :=
  checkedSlice34fdContract_implements

end BinaryFv.Zesu.Staging
