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

/-! ## Request-type-two checked slice -/

structure CheckedSlice3541Args extends CheckedSliceArgs where
  tableBytes : Nat
  candidateEnd : Nat
  savedS8 : Nat
  savedS11 : Nat

def checkedSlice3541Entry (args : CheckedSlice3541Args) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some 0x130c8 ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.sourceBytes.size) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 args.tableBytes) ∧
  args.present = true ∧
  args.endOffset = (if 12 < args.tableBytes then args.candidateEnd else args.sourceBytes.size) ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x500) args.candidateEnd ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x198) args.startOffset ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x1b0) args.savedS8 ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x1a8) args.savedS11 ∧
  BytesRep state.machine.mem args.sourceAddress args.sourceBytes ∧
  args.sourceBytes.size < 2 ^ 64 ∧ args.tableBytes < 2 ^ 64 ∧
  (∀ index, index < args.sourceBytes.size →
    ¬checkedSlice3541Memory args.stackPointer (args.sourceAddress + index)) ∧
  CheckedSliceMachineAccess args.stackPointer state.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def checkedSlice3541Continuation (args : CheckedSlice3541Args) (state : EndpointState) : Prop :=
  state.machine.regs.get? x12 = some (BitVec.ofNat 64 args.endOffset) ∧
  state.machine.regs.get? x22 = some 1 ∧
  state.machine.regs.get? x24 = some (BitVec.ofNat 64 args.savedS8) ∧
  state.machine.regs.get? x27 = some (BitVec.ofNat 64 args.savedS11)

def checkedSlice3541SelectedRep (args : CheckedSlice3541Args) (outcome : CheckedSliceOutcome)
    (state : EndpointState) : Prop :=
  match outcome with
  | .empty => True
  | .invalid => True
  | .selected bytes =>
      bytes = args.sourceBytes.extract args.startOffset args.endOffset ∧
      checkedSlice3541Continuation args state ∧
      BytesRep state.machine.mem (args.sourceAddress + args.startOffset) bytes

def checkedSlice3541Exit (args : CheckedSlice3541Args) (outcome : CheckedSliceOutcome)
    (before after : EndpointState) : Prop :=
  (match outcome with
    | .empty => after.machine.regs.get? PC = some 0x130fc
    | .invalid => after.machine.regs.get? PC = some 0x13db0 ∨
        (after.machine.regs.get? PC = some 0x1230c ∧ checkedSlice3541Continuation args after)
    | .selected _ => after.machine.regs.get? PC = some 0x130fc) ∧
  checkedSlice3541SelectedRep args outcome after ∧
  BytesRep after.machine.mem args.sourceAddress args.sourceBytes ∧
  WritesOnlyRegs checkedSlice3541Writes before.machine after.machine ∧
  WritesOnlyWithin (checkedSlice3541Memory args.stackPointer) before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode

def checkedSlice3541Contract :
    RelationalMachineContract EndpointState CheckedSlice3541Args CheckedSliceOutcome :=
  { allows := fun args outcome => outcome = checkedSliceMeaning args.toCheckedSliceArgs
    entry := checkedSlice3541Entry
    exit := fun args outcome before after =>
      outcome = checkedSliceMeaning args.toCheckedSliceArgs ∧
        checkedSlice3541Exit args outcome before after
    stepBound := fun _ => 13 }

private theorem checkedSlice3541OwnPc_not_observed {pc : BitVec 64}
    (inside : checkedSlice3541OwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold checkedSlice3541OwnPc pcInList at inside
  unfold BareMetalHostTransitionPc at observed
  unfold readContextReturnPc writeContextReturnPc exitContextStorePc at observed
  simp at inside
  rcases observed with observed | observed | observed
  all_goals omega

private theorem sourceRepOf3541Seg {args : CheckedSlice3541Args} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (sourceRep : BytesRep before.mem args.sourceAddress args.sourceBytes)
    (outside : ∀ index, index < args.sourceBytes.size →
      ¬checkedSlice3541Memory args.stackPointer (args.sourceAddress + index))
    (seg : Seg checkedSlice3541OwnPc checkedSlice3541ExitPc
      (fun _ _ _ _ _ => False) checkedSlice3541Writes
      (checkedSlice3541Memory args.stackPointer) kv fromStep count before after pc) :
    BytesRep after.mem args.sourceAddress args.sourceBytes :=
  sourceRepOfCheckedSliceSeg sourceRep outside seg

private theorem checkedSlice3541MachineTrace (template : EndpointState)
    {stackPointer fromStep count : Nat} {kv : List RegVal}
    {before after : State} {pc : BitVec 64}
    (seg : Seg checkedSlice3541OwnPc checkedSlice3541ExitPc
      (fun _ _ _ _ _ => False) checkedSlice3541Writes
      (checkedSlice3541Memory stackPointer) kv fromStep count before after pc)
    (exitPc : checkedSlice3541ExitPc pc) :
    ConfinedTrace EndpointStep EndpointPc checkedSlice3541OwnPc fromStep count
      { template with machine := before } { template with machine := after } := by
  have trace : ScopedTrace checkedSlice3541OwnPc checkedSlice3541ExitPc
      (fun _ _ _ _ _ => False) fromStep count before after :=
    seg.confined 0 after (checkedSliceEndTrace seg.atPc exitPc)
  exact liftCheckedSliceTrace template checkedSlice3541OwnPc_not_observed trace

/-- The production `fi:1:3541` instance satisfies the type-two checked-slice contract. -/
theorem checkedSlice3541Contract_implements :
    checkedSlice3541Contract.Implements EndpointStep EndpointPc
      checkedSlice3541OwnPc checkedSlice3541ExitPc := by
  intro args fromStep before entry
  rcases entry with ⟨atPc, lengthAt, tableAt, present, endEq, candidateRep, startRep,
    savedS8Rep, savedS11Rep, sourceRep, lengthFits, tableFits, sourceOutside, access, loaded⟩
  have startFits := startRep.1
  have candidateFits := candidateRep.1
  have endFits : args.endOffset < 2 ^ 64 := by
    rw [endEq]
    by_cases hasNext : 12 < args.tableBytes
    · simpa [hasNext] using candidateFits
    · simpa [hasNext] using lengthFits
  have hasNextComparison : zopz0zI_u 12 (BitVec.ofNat 64 args.tableBytes) =
      decide (12 < args.tableBytes) := by
    simpa only [BitVec.ofNat_eq_ofNat] using
      checkedSliceComparisonOfNat 12 args.tableBytes (by omega) tableFits
  have selectedEndEq :
      (if decide (12 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size) =
        args.endOffset := by
    rw [endEq]
    by_cases hasNext : 12 < args.tableBytes <;> simp [hasNext]
  by_cases reversed : args.endOffset < args.startOffset
  · have invalid : zopz0zI_u (BitVec.ofNat 64 args.endOffset)
        (BitVec.ofNat 64 args.startOffset) = true := by
      rw [checkedSliceComparisonOfNat args.endOffset args.startOffset endFits startFits]
      simp [reversed]
    have invalidSelected : zopz0zI_u
        (BitVec.ofNat 64
          (if decide (12 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size))
        (BitVec.ofNat 64 args.startOffset) = true := by
      simpa only [selectedEndEq] using invalid
    obtain ⟨finalMachine, seg⟩ := checkedSlice3541InvalidStartEndRun fromStep
      args.stackPointer args.sourceBytes.size args.tableBytes args.candidateEnd args.startOffset
      before.machine access atPc lengthAt lengthFits tableAt candidateRep startRep
      hasNextComparison invalidSelected loaded
    let used := if decide (12 < args.tableBytes) then 7 else 8
    let after : EndpointState := { before with machine := finalMachine }
    have sourceAfter := sourceRepOf3541Seg sourceRep sourceOutside seg
    refine ⟨used, after, .invalid, by
      by_cases hasNext : 12 < args.tableBytes <;> simp [used, hasNext], ?_, ?_, ?_, ?_, ?_⟩
    · change used ≤ 13
      by_cases hasNext : 12 < args.tableBytes <;> simp [used, hasNext]
    · exact checkedSlice3541MachineTrace before seg
        (by unfold checkedSlice3541ExitPc pcInList; native_decide)
    · exact ⟨0x13db0, seg.atPc, by unfold checkedSlice3541ExitPc pcInList; native_decide⟩
    · simp [checkedSlice3541Contract, checkedSliceMeaning, present, reversed]
    · refine ⟨by simp [checkedSliceMeaning, present, reversed], ?_, ?_, sourceAfter,
        seg.writes, seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
      · exact Or.inl (by simpa [after] using seg.atPc)
      · simp [checkedSlice3541SelectedRep]
      · exact checkedSlice3541CodeOfSeg access loaded seg
  · have startEndValid : zopz0zI_u (BitVec.ofNat 64 args.endOffset)
        (BitVec.ofNat 64 args.startOffset) = false := by
      rw [checkedSliceComparisonOfNat args.endOffset args.startOffset endFits startFits]
      simp [reversed]
    have startEndSelected : zopz0zI_u
        (BitVec.ofNat 64
          (if decide (12 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size))
        (BitVec.ofNat 64 args.startOffset) = false := by
      simpa only [selectedEndEq] using startEndValid
    by_cases oversized : args.sourceBytes.size < args.endOffset
    · have lengthComparison : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
          (BitVec.ofNat 64 args.endOffset) = true := by
        rw [checkedSliceComparisonOfNat args.sourceBytes.size args.endOffset lengthFits endFits]
        simp [oversized]
      have lengthSelected : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
          (BitVec.ofNat 64
            (if decide (12 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size)) =
          true := by
        simpa only [selectedEndEq] using lengthComparison
      obtain ⟨finalMachine, seg⟩ := checkedSlice3541LengthCheckedRun fromStep
        args.stackPointer args.sourceBytes.size args.tableBytes args.candidateEnd args.startOffset
        args.savedS8 args.savedS11 before.machine access atPc lengthAt lengthFits tableAt
        candidateRep startRep savedS8Rep savedS11Rep hasNextComparison startEndSelected
        lengthSelected loaded
      let used := if decide (12 < args.tableBytes) then 12 else 13
      let after : EndpointState := { before with machine := finalMachine }
      have sourceAfter := sourceRepOf3541Seg sourceRep sourceOutside seg
      refine ⟨used, after, .invalid, by
        by_cases hasNext : 12 < args.tableBytes <;> simp [used, hasNext], ?_, ?_, ?_, ?_, ?_⟩
      · change used ≤ 13
        by_cases hasNext : 12 < args.tableBytes <;> simp [used, hasNext]
      · exact checkedSlice3541MachineTrace before seg
          (by unfold checkedSlice3541ExitPc pcInList; native_decide)
      · exact ⟨0x1230c, seg.atPc, by unfold checkedSlice3541ExitPc pcInList; native_decide⟩
      · simp [checkedSlice3541Contract, checkedSliceMeaning, present, reversed, oversized]
      · refine ⟨by simp [checkedSliceMeaning, present, reversed, oversized], ?_, ?_, sourceAfter,
          seg.writes, seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
        · refine Or.inr ⟨by simpa [after] using seg.atPc, ?_⟩
          unfold checkedSlice3541Continuation
          refine ⟨?_, ?_, ?_, ?_⟩
          · have x12At := seg.reg x12 (BitVec.ofNat 64
                (if decide (12 < args.tableBytes) then args.candidateEnd
                  else args.sourceBytes.size)) (by simp)
            rw [selectedEndEq] at x12At
            simpa [after] using x12At
          · simpa [after] using seg.reg x22 1 (by simp)
          · simpa [after] using seg.reg x24 (BitVec.ofNat 64 args.savedS8) (by simp)
          · simpa [after] using seg.reg x27 (BitVec.ofNat 64 args.savedS11) (by simp)
        · simp [checkedSlice3541SelectedRep]
        · exact checkedSlice3541CodeOfSeg access loaded seg
    · have lengthComparison : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
          (BitVec.ofNat 64 args.endOffset) = false := by
        rw [checkedSliceComparisonOfNat args.sourceBytes.size args.endOffset lengthFits endFits]
        simp [oversized]
      have lengthSelected : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
          (BitVec.ofNat 64
            (if decide (12 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size)) =
          false := by
        simpa only [selectedEndEq] using lengthComparison
      obtain ⟨finalMachine, seg⟩ := checkedSlice3541LengthCheckedRun fromStep
        args.stackPointer args.sourceBytes.size args.tableBytes args.candidateEnd args.startOffset
        args.savedS8 args.savedS11 before.machine access atPc lengthAt lengthFits tableAt
        candidateRep startRep savedS8Rep savedS11Rep hasNextComparison startEndSelected
        lengthSelected loaded
      let used := if decide (12 < args.tableBytes) then 12 else 13
      let selected := args.sourceBytes.extract args.startOffset args.endOffset
      let after : EndpointState := { before with machine := finalMachine }
      have sourceAfter := sourceRepOf3541Seg sourceRep sourceOutside seg
      have selectedRep : BytesRep finalMachine.mem (args.sourceAddress + args.startOffset)
          selected := by
        have range := sourceAfter.extractRange args.startOffset
          (args.endOffset - args.startOffset) (by omega)
        have endOffsetEq : args.startOffset + (args.endOffset - args.startOffset) =
            args.endOffset := Nat.add_sub_of_le (by omega)
        rw [endOffsetEq] at range
        simpa [selected] using range
      refine ⟨used, after, .selected selected, by
        by_cases hasNext : 12 < args.tableBytes <;> simp [used, hasNext], ?_, ?_, ?_, ?_, ?_⟩
      · change used ≤ 13
        by_cases hasNext : 12 < args.tableBytes <;> simp [used, hasNext]
      · exact checkedSlice3541MachineTrace before seg
          (by unfold checkedSlice3541ExitPc pcInList; native_decide)
      · exact ⟨0x130fc, seg.atPc, by unfold checkedSlice3541ExitPc pcInList; native_decide⟩
      · simp [checkedSlice3541Contract, checkedSliceMeaning, present, reversed, oversized, selected]
      · refine ⟨by simp [checkedSliceMeaning, present, reversed, oversized, selected], ?_, ?_,
          sourceAfter, seg.writes, seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
        · simpa [after] using seg.atPc
        · refine ⟨rfl, ?_, by simpa [after] using selectedRep⟩
          unfold checkedSlice3541Continuation
          refine ⟨?_, ?_, ?_, ?_⟩
          · have x12At := seg.reg x12 (BitVec.ofNat 64
                (if decide (12 < args.tableBytes) then args.candidateEnd
                  else args.sourceBytes.size)) (by simp)
            rw [selectedEndEq] at x12At
            simpa [after] using x12At
          · simpa [after] using seg.reg x22 1 (by simp)
          · simpa [after] using seg.reg x24 (BitVec.ofNat 64 args.savedS8) (by simp)
          · simpa [after] using seg.reg x27 (BitVec.ofNat 64 args.savedS11) (by simp)
        · exact checkedSlice3541CodeOfSeg access loaded seg

def Proposed_ssz_decode__struct_1051_f_fi_1_3541_Contract : Prop :=
  checkedSlice3541Contract.Implements EndpointStep EndpointPc
    checkedSlice3541OwnPc checkedSlice3541ExitPc

theorem proposed_checkedSlice_3541_proved :
    Proposed_ssz_decode__struct_1051_f_fi_1_3541_Contract :=
  checkedSlice3541Contract_implements

/-! ## Request-type-three checked slice -/

structure CheckedSlice3566Args extends CheckedSliceArgs where
  tableBytes : Nat
  candidateEnd : Nat
  savedS8 : Nat
  savedS11 : Nat

def checkedSlice3566Entry (args : CheckedSlice3566Args) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some 0x13100 ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.sourceBytes.size) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 args.tableBytes) ∧
  state.machine.regs.get? x12 = some 13 ∧
  state.machine.regs.get? x13 = some (BitVec.ofNat 64 args.startOffset) ∧
  args.present = decide (13 ≤ args.tableBytes) ∧
  args.endOffset = (if 16 < args.tableBytes then args.candidateEnd else args.sourceBytes.size) ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x508) args.candidateEnd ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x190) args.sourceAddress ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x1b0) args.savedS8 ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x1a8) args.savedS11 ∧
  BytesRep state.machine.mem args.sourceAddress args.sourceBytes ∧
  args.sourceBytes.size < 2 ^ 64 ∧ args.tableBytes < 2 ^ 64 ∧
  args.sourceAddress + args.startOffset < 2 ^ 64 ∧
  (∀ index, index < args.sourceBytes.size →
    ¬checkedSlice3566Memory args.stackPointer (args.sourceAddress + index)) ∧
  CheckedSliceMachineAccess args.stackPointer state.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def checkedSlice3566Continuation (args : CheckedSlice3566Args) (state : EndpointState) : Prop :=
  state.machine.regs.get? x22 = some 1 ∧
  state.machine.regs.get? x24 = some (BitVec.ofNat 64 args.savedS8) ∧
  state.machine.regs.get? x27 = some (BitVec.ofNat 64 args.savedS11)

def checkedSlice3566SelectedRep (args : CheckedSlice3566Args) (outcome : CheckedSliceOutcome)
    (state : EndpointState) : Prop :=
  match outcome with
  | .empty => True
  | .invalid => True
  | .selected bytes =>
      bytes = args.sourceBytes.extract args.startOffset args.endOffset ∧
      checkedSlice3566Continuation args state ∧
      UIntRep 8 state.machine.mem (args.stackPointer + 0x278)
        (args.sourceAddress + args.startOffset) ∧
      UIntRep 8 state.machine.mem (args.stackPointer + 0x280)
        (args.endOffset - args.startOffset) ∧
      BytesRep state.machine.mem (args.sourceAddress + args.startOffset) bytes

def checkedSlice3566Exit (args : CheckedSlice3566Args) (outcome : CheckedSliceOutcome)
    (before after : EndpointState) : Prop :=
  (match outcome with
    | .empty => after.machine.regs.get? PC = some 0x13198
    | .invalid => after.machine.regs.get? PC = some 0x13db0 ∨
        (after.machine.regs.get? PC = some 0x1230c ∧ checkedSlice3566Continuation args after)
    | .selected _ => after.machine.regs.get? PC = some 0x13144) ∧
  checkedSlice3566SelectedRep args outcome after ∧
  BytesRep after.machine.mem args.sourceAddress args.sourceBytes ∧
  WritesOnlyRegs checkedSlice3566Writes before.machine after.machine ∧
  WritesOnlyWithin (checkedSlice3566Memory args.stackPointer) before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode

def checkedSlice3566Contract :
    RelationalMachineContract EndpointState CheckedSlice3566Args CheckedSliceOutcome :=
  { allows := fun args outcome => outcome = checkedSliceMeaning args.toCheckedSliceArgs
    entry := checkedSlice3566Entry
    exit := fun args outcome before after =>
      outcome = checkedSliceMeaning args.toCheckedSliceArgs ∧
        checkedSlice3566Exit args outcome before after
    stepBound := fun _ => 17 }

private theorem checkedSlice3566OwnPc_not_observed {pc : BitVec 64}
    (inside : checkedSlice3566OwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold checkedSlice3566OwnPc pcInList at inside
  unfold BareMetalHostTransitionPc at observed
  unfold readContextReturnPc writeContextReturnPc exitContextStorePc at observed
  simp at inside
  rcases observed with observed | observed | observed
  all_goals omega

private theorem sourceRepOf3566Seg {args : CheckedSlice3566Args} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (sourceRep : BytesRep before.mem args.sourceAddress args.sourceBytes)
    (outside : ∀ index, index < args.sourceBytes.size →
      ¬checkedSlice3566Memory args.stackPointer (args.sourceAddress + index))
    (seg : Seg checkedSlice3566OwnPc checkedSlice3566ExitPc
      (fun _ _ _ _ _ => False) checkedSlice3566Writes
      (checkedSlice3566Memory args.stackPointer) kv fromStep count before after pc) :
    BytesRep after.mem args.sourceAddress args.sourceBytes :=
  sourceRepOfCheckedSliceSeg sourceRep outside seg

private theorem checkedSlice3566MachineTrace (template : EndpointState)
    {stackPointer fromStep count : Nat} {kv : List RegVal}
    {before after : State} {pc : BitVec 64}
    (seg : Seg checkedSlice3566OwnPc checkedSlice3566ExitPc
      (fun _ _ _ _ _ => False) checkedSlice3566Writes
      (checkedSlice3566Memory stackPointer) kv fromStep count before after pc)
    (exitPc : checkedSlice3566ExitPc pc) :
    ConfinedTrace EndpointStep EndpointPc checkedSlice3566OwnPc fromStep count
      { template with machine := before } { template with machine := after } := by
  have trace : ScopedTrace checkedSlice3566OwnPc checkedSlice3566ExitPc
      (fun _ _ _ _ _ => False) fromStep count before after :=
    seg.confined 0 after (checkedSliceEndTrace seg.atPc exitPc)
  exact liftCheckedSliceTrace template checkedSlice3566OwnPc_not_observed trace

/-- The production `fi:1:3566` instance satisfies the type-three checked-slice contract. -/
theorem checkedSlice3566Contract_implements :
    checkedSlice3566Contract.Implements EndpointStep EndpointPc
      checkedSlice3566OwnPc checkedSlice3566ExitPc := by
  intro args fromStep before entry
  rcases entry with ⟨atPc, lengthAt, tableAt, thresholdAt, startAt, presentEq, endEq,
    candidateRep, sourceBaseRep, savedS8Rep, savedS11Rep, sourceRep, lengthFits,
    tableFits, addressFits, sourceOutside, access, loaded⟩
  have startFits := sourceBaseRep.1
  have candidateFits := candidateRep.1
  have startOffsetFits : args.startOffset < 2 ^ 64 := by omega
  have presentComparison : zopz0zI_u (BitVec.ofNat 64 args.tableBytes) 13 =
      decide (args.tableBytes < 13) := by
    simpa only [BitVec.ofNat_eq_ofNat] using
      checkedSliceComparisonOfNat args.tableBytes 13 tableFits (by omega)
  by_cases present : 13 ≤ args.tableBytes
  · have presentTrue : args.present = true := by simpa [present] using presentEq
    have presentRoute : zopz0zI_u (BitVec.ofNat 64 args.tableBytes) 13 = false := by
      rw [presentComparison]
      simp [show ¬args.tableBytes < 13 by omega]
    have hasNextComparison : zopz0zI_u 16 (BitVec.ofNat 64 args.tableBytes) =
        decide (16 < args.tableBytes) := by
      simpa only [BitVec.ofNat_eq_ofNat] using
        checkedSliceComparisonOfNat 16 args.tableBytes (by omega) tableFits
    have selectedEndEq :
        (if decide (16 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size) =
          args.endOffset := by
      rw [endEq]
      by_cases hasNext : 16 < args.tableBytes <;> simp [hasNext]
    have endFits : args.endOffset < 2 ^ 64 := by
      rw [endEq]
      by_cases hasNext : 16 < args.tableBytes
      · simpa [hasNext] using candidateFits
      · simpa [hasNext] using lengthFits
    by_cases reversed : args.endOffset < args.startOffset
    · have reversedComparison : zopz0zI_u (BitVec.ofNat 64 args.endOffset)
          (BitVec.ofNat 64 args.startOffset) = true := by
        rw [checkedSliceComparisonOfNat args.endOffset args.startOffset endFits startOffsetFits]
        simp [reversed]
      have reversedSelected : zopz0zI_u
          (BitVec.ofNat 64
            (if decide (16 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size))
          (BitVec.ofNat 64 args.startOffset) = true := by
        simpa only [selectedEndEq] using reversedComparison
      obtain ⟨finalMachine, seg⟩ := checkedSlice3566InvalidStartEndRun fromStep
        args.stackPointer args.sourceBytes.size args.tableBytes args.candidateEnd args.startOffset
        before.machine access atPc lengthAt tableAt thresholdAt startAt candidateRep
        presentRoute hasNextComparison reversedSelected loaded
      let used := (if decide (16 < args.tableBytes) then 5 else 6) + 1
      let after : EndpointState := { before with machine := finalMachine }
      have sourceAfter := sourceRepOf3566Seg sourceRep sourceOutside seg
      refine ⟨used, after, .invalid, by
        by_cases hasNext : 16 < args.tableBytes <;> simp [used, hasNext], ?_, ?_, ?_, ?_, ?_⟩
      · change used ≤ 17
        by_cases hasNext : 16 < args.tableBytes <;> simp [used, hasNext]
      · exact checkedSlice3566MachineTrace before seg
          (by unfold checkedSlice3566ExitPc pcInList; native_decide)
      · exact ⟨0x13db0, seg.atPc, by unfold checkedSlice3566ExitPc pcInList; native_decide⟩
      · simp [checkedSlice3566Contract, checkedSliceMeaning, presentTrue, reversed]
      · refine ⟨by simp [checkedSliceMeaning, presentTrue, reversed], ?_, ?_, sourceAfter,
          seg.writes, seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
        · exact Or.inl (by simpa [after] using seg.atPc)
        · simp [checkedSlice3566SelectedRep]
        · exact checkedSlice3566CodeOfSeg access loaded seg
    · have validComparison : zopz0zI_u (BitVec.ofNat 64 args.endOffset)
          (BitVec.ofNat 64 args.startOffset) = false := by
        rw [checkedSliceComparisonOfNat args.endOffset args.startOffset endFits startOffsetFits]
        simp [reversed]
      have validSelected : zopz0zI_u
          (BitVec.ofNat 64
            (if decide (16 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size))
          (BitVec.ofNat 64 args.startOffset) = false := by
        simpa only [selectedEndEq] using validComparison
      by_cases oversized : args.sourceBytes.size < args.endOffset
      · have oversizedComparison : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
            (BitVec.ofNat 64 args.endOffset) = true := by
          rw [checkedSliceComparisonOfNat args.sourceBytes.size args.endOffset lengthFits endFits]
          simp [oversized]
        have oversizedSelected : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
            (BitVec.ofNat 64
              (if decide (16 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size)) =
            true := by
          simpa only [selectedEndEq] using oversizedComparison
        obtain ⟨finalMachine, seg⟩ := checkedSlice3566LengthRejectedRun fromStep
          args.stackPointer args.sourceBytes.size args.tableBytes args.candidateEnd args.startOffset
          args.savedS8 args.savedS11 before.machine access atPc lengthAt tableAt thresholdAt startAt
          candidateRep savedS8Rep savedS11Rep presentRoute
          hasNextComparison validSelected oversizedSelected loaded
        let used := (if decide (16 < args.tableBytes) then 5 else 6) + 5
        let after : EndpointState := { before with machine := finalMachine }
        have sourceAfter := sourceRepOf3566Seg sourceRep sourceOutside seg
        refine ⟨used, after, .invalid, by
          by_cases hasNext : 16 < args.tableBytes <;> simp [used, hasNext], ?_, ?_, ?_, ?_, ?_⟩
        · change used ≤ 17
          by_cases hasNext : 16 < args.tableBytes <;> simp [used, hasNext]
        · exact checkedSlice3566MachineTrace before seg
            (by unfold checkedSlice3566ExitPc pcInList; native_decide)
        · exact ⟨0x1230c, seg.atPc, by unfold checkedSlice3566ExitPc pcInList; native_decide⟩
        · simp [checkedSlice3566Contract, checkedSliceMeaning, presentTrue, reversed, oversized]
        · refine ⟨by simp [checkedSliceMeaning, presentTrue, reversed, oversized], ?_, ?_,
            sourceAfter, seg.writes, seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
          · refine Or.inr ⟨by simpa [after] using seg.atPc, ?_⟩
            unfold checkedSlice3566Continuation
            exact ⟨by simpa [after] using seg.reg x22 1 (by simp),
              by simpa [after] using seg.reg x24 (BitVec.ofNat 64 args.savedS8) (by simp),
              by simpa [after] using seg.reg x27 (BitVec.ofNat 64 args.savedS11) (by simp)⟩
          · simp [checkedSlice3566SelectedRep]
          · exact checkedSlice3566CodeOfSeg access loaded seg
      · have lengthComparison : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
            (BitVec.ofNat 64 args.endOffset) = false := by
          rw [checkedSliceComparisonOfNat args.sourceBytes.size args.endOffset lengthFits endFits]
          simp [oversized]
        have lengthSelected : zopz0zI_u (BitVec.ofNat 64 args.sourceBytes.size)
            (BitVec.ofNat 64
              (if decide (16 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size)) =
            false := by
          simpa only [selectedEndEq] using lengthComparison
        have startLeEnd : args.startOffset ≤ args.endOffset := by omega
        have differenceEq : BitVec.ofNat 64
              (if decide (16 < args.tableBytes) then args.candidateEnd else args.sourceBytes.size) -
            BitVec.ofNat 64 args.startOffset =
              BitVec.ofNat 64
                ((if decide (16 < args.tableBytes) then args.candidateEnd
                  else args.sourceBytes.size) - args.startOffset) := by
          rw [selectedEndEq]
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt endFits]
          omega
        have sliceLengthFits : args.endOffset - args.startOffset < 2 ^ 64 := by omega
        have selectedLengthFits :
            (if decide (16 < args.tableBytes) then args.candidateEnd
              else args.sourceBytes.size) - args.startOffset < 2 ^ 64 := by
          simpa only [selectedEndEq] using sliceLengthFits
        obtain ⟨finalMachine, seg, outputLengthRep, outputAddressRep⟩ :=
          checkedSlice3566SelectedRun fromStep args.stackPointer args.sourceBytes.size
            args.tableBytes args.candidateEnd args.startOffset args.savedS8 args.savedS11
            args.sourceAddress before.machine access atPc lengthAt tableAt thresholdAt startAt
            candidateRep sourceBaseRep savedS8Rep savedS11Rep
            presentRoute hasNextComparison validSelected
            lengthSelected differenceEq selectedLengthFits addressFits loaded
        let used := (if decide (16 < args.tableBytes) then 5 else 6) + 11
        let selected := args.sourceBytes.extract args.startOffset args.endOffset
        let after : EndpointState := { before with machine := finalMachine }
        have sourceAfter := sourceRepOf3566Seg sourceRep sourceOutside seg
        have outputLengthRep' := outputLengthRep
        rw [selectedEndEq] at outputLengthRep'
        have selectedRep : BytesRep finalMachine.mem (args.sourceAddress + args.startOffset)
            selected := by
          have range := sourceAfter.extractRange args.startOffset
            (args.endOffset - args.startOffset) (by omega)
          have endOffsetEq : args.startOffset + (args.endOffset - args.startOffset) =
              args.endOffset := Nat.add_sub_of_le startLeEnd
          rw [endOffsetEq] at range
          simpa [selected] using range
        refine ⟨used, after, .selected selected, by
          by_cases hasNext : 16 < args.tableBytes <;> simp [used, hasNext], ?_, ?_, ?_, ?_, ?_⟩
        · change used ≤ 17
          by_cases hasNext : 16 < args.tableBytes <;> simp [used, hasNext]
        · exact checkedSlice3566MachineTrace before seg
            (by unfold checkedSlice3566ExitPc pcInList; native_decide)
        · exact ⟨0x13144, seg.atPc, by unfold checkedSlice3566ExitPc pcInList; native_decide⟩
        · simp [checkedSlice3566Contract, checkedSliceMeaning, presentTrue, reversed, oversized,
            selected]
        · refine ⟨by simp [checkedSliceMeaning, presentTrue, reversed, oversized, selected],
            by simpa [after] using seg.atPc, ?_, sourceAfter, seg.writes, seg.mem, seg.retired,
            ?_, seg.aux, rfl, rfl, rfl, rfl⟩
          · refine ⟨rfl, ?_, by simpa [after, selectedEndEq] using outputAddressRep,
              by simpa [after] using outputLengthRep', by simpa [after] using selectedRep⟩
            unfold checkedSlice3566Continuation
            exact ⟨by simpa [after] using seg.reg x22 1 (by simp),
              by simpa [after] using seg.reg x24 (BitVec.ofNat 64 args.savedS8) (by simp),
              by simpa [after] using seg.reg x27 (BitVec.ofNat 64 args.savedS11) (by simp)⟩
          · exact checkedSlice3566CodeOfSeg access loaded seg
  · have presentFalse : args.present = false := by simpa [present] using presentEq
    have absentComparison : zopz0zI_u (BitVec.ofNat 64 args.tableBytes) 13 = true := by
      rw [presentComparison]
      simp [show args.tableBytes < 13 by omega]
    obtain ⟨finalMachine, seg⟩ := checkedSlice3566EmptyRun fromStep args.stackPointer
      args.tableBytes before.machine access atPc tableAt thresholdAt absentComparison loaded
    let after : EndpointState := { before with machine := finalMachine }
    have sourceAfter := sourceRepOf3566Seg sourceRep sourceOutside seg
    refine ⟨1, after, .empty, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · change 1 ≤ 17
      omega
    · exact checkedSlice3566MachineTrace before seg
        (by unfold checkedSlice3566ExitPc pcInList; native_decide)
    · exact ⟨0x13198, seg.atPc, by unfold checkedSlice3566ExitPc pcInList; native_decide⟩
    · simp [checkedSlice3566Contract, checkedSliceMeaning, presentFalse]
    · refine ⟨by simp [checkedSliceMeaning, presentFalse], by simpa [after] using seg.atPc,
        by simp [checkedSlice3566SelectedRep], sourceAfter, seg.writes, seg.mem, seg.retired,
        checkedSlice3566CodeOfSeg access loaded seg, seg.aux, rfl, rfl, rfl, rfl⟩

def Proposed_ssz_decode__struct_1051_f_fi_1_3566_Contract : Prop :=
  checkedSlice3566Contract.Implements EndpointStep EndpointPc
    checkedSlice3566OwnPc checkedSlice3566ExitPc

theorem proposed_checkedSlice_3566_proved :
    Proposed_ssz_decode__struct_1051_f_fi_1_3566_Contract :=
  checkedSlice3566Contract_implements

/-! ## Request-type-four checked slice -/

structure CheckedSlice358bArgs extends CheckedSliceArgs where
  tableBytes : Nat
  candidateEnd : Nat
  savedS8 : Nat
  savedS11 : Nat

def checkedSlice358bEntry (args : CheckedSlice358bArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some 0x13144 ∧
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.sourceBytes.size) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 args.tableBytes) ∧
  state.machine.regs.get? x12 = some (BitVec.ofNat 64 args.startOffset) ∧
  state.machine.regs.get? x14 = some 17 ∧
  args.present = decide (17 ≤ args.tableBytes) ∧
  args.endOffset = (if 20 < args.tableBytes then args.candidateEnd else args.sourceBytes.size) ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x510) args.candidateEnd ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x190) args.sourceAddress ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x1b0) args.savedS8 ∧
  UIntRep 8 state.machine.mem (args.stackPointer + 0x1a8) args.savedS11 ∧
  BytesRep state.machine.mem args.sourceAddress args.sourceBytes ∧
  args.sourceBytes.size < 2 ^ 64 ∧ args.tableBytes < 2 ^ 64 ∧
  args.sourceAddress + args.startOffset < 2 ^ 64 ∧
  (∀ index, index < args.sourceBytes.size →
    ¬MachineExecution.checkedSlice358bMemory args.stackPointer
      (args.sourceAddress + index)) ∧
  CheckedSliceMachineAccess args.stackPointer state.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def checkedSlice358bLoadedContinuation (args : CheckedSlice358bArgs)
    (state : EndpointState) : Prop :=
  state.machine.regs.get? x22 = some 1 ∧
  state.machine.regs.get? x24 = some (BitVec.ofNat 64 args.savedS8) ∧
  state.machine.regs.get? x27 = some (BitVec.ofNat 64 args.savedS11)

def checkedSlice358bNoNextContinuation (args : CheckedSlice358bArgs)
    (state : EndpointState) : Prop :=
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.sourceBytes.size) ∧
  state.machine.regs.get? x12 = some (BitVec.ofNat 64 args.startOffset) ∧
  state.machine.regs.get? x13 = some 20

def checkedSlice358bSelectedRep (args : CheckedSlice358bArgs)
    (outcome : CheckedSliceOutcome) (state : EndpointState) : Prop :=
  match outcome with
  | .empty => True
  | .invalid => True
  | .selected bytes =>
      bytes = args.sourceBytes.extract args.startOffset args.endOffset ∧
      if 20 < args.tableBytes then
        checkedSlice358bLoadedContinuation args state ∧
        UIntRep 8 state.machine.mem (args.stackPointer + 0x268)
          (args.sourceAddress + args.startOffset) ∧
        UIntRep 8 state.machine.mem (args.stackPointer + 0x270)
          (args.endOffset - args.startOffset) ∧
        BytesRep state.machine.mem (args.sourceAddress + args.startOffset) bytes
      else checkedSlice358bNoNextContinuation args state

def checkedSlice358bExit (args : CheckedSlice358bArgs) (outcome : CheckedSliceOutcome)
    (before after : EndpointState) : Prop :=
  (match outcome with
    | .empty => after.machine.regs.get? PC = some 0x13cb8
    | .invalid => after.machine.regs.get? PC = some 0x13db0 ∨
        (after.machine.regs.get? PC = some 0x1230c ∧
          checkedSlice358bLoadedContinuation args after) ∨
        (after.machine.regs.get? PC = some 0x13150 ∧
          checkedSlice358bNoNextContinuation args after)
    | .selected _ => if 20 < args.tableBytes then
        after.machine.regs.get? PC = some 0x131b0
      else after.machine.regs.get? PC = some 0x13150) ∧
  checkedSlice358bSelectedRep args outcome after ∧
  BytesRep after.machine.mem args.sourceAddress args.sourceBytes ∧
  WritesOnlyRegs MachineExecution.checkedSlice358bWrites before.machine after.machine ∧
  WritesOnlyWithin (MachineExecution.checkedSlice358bMemory args.stackPointer)
    before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode

def checkedSlice358bContract :
    RelationalMachineContract EndpointState CheckedSlice358bArgs CheckedSliceOutcome :=
  { allows := fun args outcome => outcome = checkedSliceMeaning args.toCheckedSliceArgs
    entry := checkedSlice358bEntry
    exit := fun args outcome before after =>
      outcome = checkedSliceMeaning args.toCheckedSliceArgs ∧
        checkedSlice358bExit args outcome before after
    stepBound := fun _ => 15 }

private theorem checkedSlice358bOwnPc_not_observed {pc : BitVec 64}
    (inside : checkedSlice358bOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold checkedSlice358bOwnPc pcInList at inside
  unfold BareMetalHostTransitionPc at observed
  unfold readContextReturnPc writeContextReturnPc exitContextStorePc at observed
  simp at inside
  rcases observed with observed | observed | observed
  all_goals omega

private theorem sourceRepOf358bSeg {args : CheckedSlice358bArgs} {kv : List RegVal}
    {fromStep count : Nat} {before after : State} {pc : BitVec 64}
    (sourceRep : BytesRep before.mem args.sourceAddress args.sourceBytes)
    (outside : ∀ index, index < args.sourceBytes.size →
      ¬checkedSlice358bMemory args.stackPointer (args.sourceAddress + index))
    (seg : Seg checkedSlice358bOwnPc checkedSlice358bExitPc
      (fun _ _ _ _ _ => False) checkedSlice358bWrites
      (checkedSlice358bMemory args.stackPointer) kv fromStep count before after pc) :
    BytesRep after.mem args.sourceAddress args.sourceBytes :=
  sourceRepOfCheckedSliceSeg sourceRep outside seg

private theorem checkedSlice358bMachineTrace (template : EndpointState)
    {stackPointer fromStep count : Nat} {kv : List RegVal}
    {before after : State} {pc : BitVec 64}
    (seg : Seg checkedSlice358bOwnPc checkedSlice358bExitPc
      (fun _ _ _ _ _ => False) checkedSlice358bWrites
      (checkedSlice358bMemory stackPointer) kv fromStep count before after pc)
    (exitPc : checkedSlice358bExitPc pc) :
    ConfinedTrace EndpointStep EndpointPc checkedSlice358bOwnPc fromStep count
      { template with machine := before } { template with machine := after } := by
  have trace : ScopedTrace checkedSlice358bOwnPc checkedSlice358bExitPc
      (fun _ _ _ _ _ => False) fromStep count before after :=
    seg.confined 0 after (checkedSliceEndTrace seg.atPc exitPc)
  exact liftCheckedSliceTrace template checkedSlice358bOwnPc_not_observed trace

private theorem checkedSliceGeComparisonOfNat (left right : Nat)
    (leftFits : left < 2 ^ 64) (rightFits : right < 2 ^ 64) :
    zopz0zKzJ_u (BitVec.ofNat 64 left) (BitVec.ofNat 64 right) = decide (right ≤ left) := by
  simp only [zopz0zKzJ_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt leftFits, Nat.mod_eq_of_lt rightFits]
  simp

/-- The production `fi:1:358b` instance satisfies the type-four checked-slice contract. -/
theorem checkedSlice358bContract_implements :
    checkedSlice358bContract.Implements EndpointStep EndpointPc
      checkedSlice358bOwnPc checkedSlice358bExitPc := by
  intro args fromStep before entry
  rcases entry with ⟨atPc, lengthAt, tableAt, startAt, thresholdAt, presentEq, endEq,
    candidateRep, sourceBaseRep, savedS8Rep, savedS11Rep, sourceRep, lengthFits,
    tableFits, addressFits, sourceOutside, access, loaded⟩
  have candidateFits := candidateRep.1
  have startFits : args.startOffset < 2 ^ 64 := by omega
  have presentComparison : zopz0zI_u (BitVec.ofNat 64 args.tableBytes) 17 =
      decide (args.tableBytes < 17) := by
    simpa only [BitVec.ofNat_eq_ofNat] using
      checkedSliceComparisonOfNat args.tableBytes 17 tableFits (by omega)
  have hasNextComparison : zopz0zI_u 20 (BitVec.ofNat 64 args.tableBytes) =
      decide (20 < args.tableBytes) := by
    simpa only [BitVec.ofNat_eq_ofNat] using
      checkedSliceComparisonOfNat 20 args.tableBytes (by omega) tableFits
  by_cases present : 17 ≤ args.tableBytes
  · have presentTrue : args.present = true := by simpa [present] using presentEq
    have presentRoute : zopz0zI_u (BitVec.ofNat 64 args.tableBytes) 17 = false := by
      rw [presentComparison]
      simp [show ¬args.tableBytes < 17 by omega]
    by_cases hasNext : 20 < args.tableBytes
    · have hasNextRoute : zopz0zI_u 20 (BitVec.ofNat 64 args.tableBytes) = true := by
        rw [hasNextComparison]
        simp [hasNext]
      have endEq' : args.endOffset = args.candidateEnd := by simpa [hasNext] using endEq
      have endFits : args.endOffset < 2 ^ 64 := by simpa [endEq'] using candidateFits
      by_cases reversed : args.endOffset < args.startOffset
      · have reversedComparison : zopz0zI_u (BitVec.ofNat 64 args.candidateEnd)
            (BitVec.ofNat 64 args.startOffset) = true := by
          rw [← endEq', checkedSliceComparisonOfNat args.endOffset args.startOffset endFits
            startFits]
          simp [reversed]
        obtain ⟨finalMachine, seg⟩ := checkedSlice358bInvalidStartEndRun fromStep
          args.stackPointer args.sourceBytes.size args.tableBytes args.candidateEnd
          args.startOffset before.machine access atPc lengthAt tableAt thresholdAt startAt
          candidateRep presentRoute hasNextRoute reversedComparison loaded
        let after : EndpointState := { before with machine := finalMachine }
        have sourceAfter := sourceRepOf358bSeg sourceRep sourceOutside seg
        refine ⟨5, after, .invalid, by omega, by change 5 ≤ 15; omega, ?_, ?_, ?_, ?_⟩
        · exact checkedSlice358bMachineTrace before seg
            (by unfold checkedSlice358bExitPc pcInList; native_decide)
        · exact ⟨0x13db0, seg.atPc,
            by unfold checkedSlice358bExitPc pcInList; native_decide⟩
        · simp [checkedSlice358bContract, checkedSliceMeaning, presentTrue, reversed]
        · refine ⟨by simp [checkedSliceMeaning, presentTrue, reversed], ?_, ?_, sourceAfter,
            seg.writes, seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
          · exact Or.inl (by simpa [after] using seg.atPc)
          · simp [checkedSlice358bSelectedRep]
          · exact checkedSlice358bCodeOfSeg access loaded seg
      · have validComparison : zopz0zI_u (BitVec.ofNat 64 args.candidateEnd)
            (BitVec.ofNat 64 args.startOffset) = false := by
          rw [← endEq', checkedSliceComparisonOfNat args.endOffset args.startOffset endFits
            startFits]
          simp [reversed]
        by_cases oversized : args.sourceBytes.size < args.endOffset
        · have lengthComparison : zopz0zKzJ_u
              (BitVec.ofNat 64 args.sourceBytes.size)
              (BitVec.ofNat 64 args.candidateEnd) = false := by
            rw [← endEq', checkedSliceGeComparisonOfNat args.sourceBytes.size args.endOffset
              lengthFits endFits]
            simp [oversized]
          obtain ⟨finalMachine, seg⟩ := checkedSlice358bLengthRejectedRun fromStep
            args.stackPointer args.sourceBytes.size args.tableBytes args.candidateEnd
            args.startOffset args.savedS8 args.savedS11 before.machine access atPc lengthAt
            tableAt thresholdAt startAt candidateRep savedS8Rep savedS11Rep presentRoute
            hasNextRoute validComparison lengthComparison loaded
          let after : EndpointState := { before with machine := finalMachine }
          have sourceAfter := sourceRepOf358bSeg sourceRep sourceOutside seg
          refine ⟨10, after, .invalid, by omega, by change 10 ≤ 15; omega, ?_, ?_, ?_, ?_⟩
          · exact checkedSlice358bMachineTrace before seg
              (by unfold checkedSlice358bExitPc pcInList; native_decide)
          · exact ⟨0x1230c, seg.atPc,
              by unfold checkedSlice358bExitPc pcInList; native_decide⟩
          · simp [checkedSlice358bContract, checkedSliceMeaning, presentTrue, reversed,
              oversized]
          · refine ⟨by simp [checkedSliceMeaning, presentTrue, reversed, oversized], ?_, ?_,
              sourceAfter, seg.writes, seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
            · refine Or.inr (Or.inl ⟨by simpa [after] using seg.atPc, ?_⟩)
              exact ⟨by simpa [after] using seg.reg x22 1 (by simp),
                by simpa [after] using seg.reg x24 (BitVec.ofNat 64 args.savedS8) (by simp),
                by simpa [after] using seg.reg x27 (BitVec.ofNat 64 args.savedS11) (by simp)⟩
            · simp [checkedSlice358bSelectedRep]
            · exact checkedSlice358bCodeOfSeg access loaded seg
        · have endLeLength : args.endOffset ≤ args.sourceBytes.size := Nat.le_of_not_gt oversized
          have lengthComparison : zopz0zKzJ_u
              (BitVec.ofNat 64 args.sourceBytes.size)
              (BitVec.ofNat 64 args.candidateEnd) = true := by
            rw [← endEq', checkedSliceGeComparisonOfNat args.sourceBytes.size args.endOffset
              lengthFits endFits]
            simp [endLeLength]
          have differenceEq : BitVec.ofNat 64 args.candidateEnd -
              BitVec.ofNat 64 args.startOffset =
              BitVec.ofNat 64 (args.candidateEnd - args.startOffset) := by
            rw [← endEq']
            apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt endFits]
            omega
          have sliceLengthFits : args.candidateEnd - args.startOffset < 2 ^ 64 := by
            rw [← endEq']
            omega
          obtain ⟨finalMachine, seg, outputAddressRep, outputLengthRep⟩ :=
            checkedSlice358bSelectedRun fromStep args.stackPointer args.sourceBytes.size
              args.tableBytes args.candidateEnd args.startOffset args.savedS8 args.savedS11
              args.sourceAddress before.machine access atPc lengthAt tableAt thresholdAt startAt
              candidateRep sourceBaseRep savedS8Rep savedS11Rep presentRoute hasNextRoute
              validComparison lengthComparison differenceEq sliceLengthFits addressFits loaded
          let selected := args.sourceBytes.extract args.startOffset args.endOffset
          let after : EndpointState := { before with machine := finalMachine }
          have sourceAfter := sourceRepOf358bSeg sourceRep sourceOutside seg
          have selectedRep : BytesRep finalMachine.mem
              (args.sourceAddress + args.startOffset) selected := by
            have range := sourceAfter.extractRange args.startOffset
              (args.endOffset - args.startOffset) (by omega)
            have endOffsetEq : args.startOffset + (args.endOffset - args.startOffset) =
                args.endOffset := Nat.add_sub_of_le (by omega)
            rw [endOffsetEq] at range
            simpa [selected] using range
          refine ⟨15, after, .selected selected, by omega, by change 15 ≤ 15; omega,
            ?_, ?_, ?_, ?_⟩
          · exact checkedSlice358bMachineTrace before seg
              (by unfold checkedSlice358bExitPc pcInList; native_decide)
          · exact ⟨0x131b0, seg.atPc,
              by unfold checkedSlice358bExitPc pcInList; native_decide⟩
          · simp [checkedSlice358bContract, checkedSliceMeaning, presentTrue, reversed,
              oversized, selected]
          · refine ⟨by simp [checkedSliceMeaning, presentTrue, reversed, oversized, selected],
              by simpa [after, hasNext] using seg.atPc, ?_, sourceAfter, seg.writes, seg.mem,
              seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
            · refine ⟨rfl, ?_⟩
              simp only [if_pos hasNext]
              refine ⟨⟨by simpa [after] using seg.reg x22 1 (by simp),
                by simpa [after] using seg.reg x24 (BitVec.ofNat 64 args.savedS8) (by simp),
                by simpa [after] using seg.reg x27 (BitVec.ofNat 64 args.savedS11) (by simp)⟩,
                ?_, ?_, by simpa [after] using selectedRep⟩
              · simpa [after, endEq'] using outputAddressRep
              · simpa [after, endEq'] using outputLengthRep
            · exact checkedSlice358bCodeOfSeg access loaded seg
    · have hasNextRoute : zopz0zI_u 20 (BitVec.ofNat 64 args.tableBytes) = false := by
        rw [hasNextComparison]
        simp [hasNext]
      have endEq' : args.endOffset = args.sourceBytes.size := by simpa [hasNext] using endEq
      obtain ⟨finalMachine, seg⟩ := checkedSlice358bEntryRun fromStep args.stackPointer
        args.sourceBytes.size args.tableBytes before.machine access atPc lengthAt tableAt
        thresholdAt presentRoute hasNextRoute loaded
      let after : EndpointState := { before with machine := finalMachine }
      have sourceAfter := sourceRepOf358bSeg sourceRep sourceOutside seg
      have continuation : checkedSlice358bNoNextContinuation args after :=
        ⟨by simpa [after] using seg.reg x10 (BitVec.ofNat 64 args.sourceBytes.size) (by simp),
          by simpa [after] using
            (seg.get x12 (by simp [checkedSlice358bWrites, stepBookkeeping])).trans startAt,
          by simpa [after] using seg.reg x13 20 (by simp)⟩
      by_cases reversed : args.endOffset < args.startOffset
      · refine ⟨3, after, .invalid, by omega, by change 3 ≤ 15; omega, ?_, ?_, ?_, ?_⟩
        · exact checkedSlice358bMachineTrace before seg
            (by unfold checkedSlice358bExitPc pcInList; native_decide)
        · exact ⟨0x13150, seg.atPc,
            by unfold checkedSlice358bExitPc pcInList; native_decide⟩
        · simp [checkedSlice358bContract, checkedSliceMeaning, presentTrue, reversed]
        · refine ⟨by simp [checkedSliceMeaning, presentTrue, reversed], ?_, ?_, sourceAfter,
            seg.writes, seg.mem, seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
          · exact Or.inr (Or.inr ⟨by simpa [after] using seg.atPc, continuation⟩)
          · simp [checkedSlice358bSelectedRep]
          · exact checkedSlice358bCodeOfSeg access loaded seg
      · let selected := args.sourceBytes.extract args.startOffset args.endOffset
        have startLeLength : args.startOffset ≤ args.sourceBytes.size := by omega
        refine ⟨3, after, .selected selected, by omega, by change 3 ≤ 15; omega,
          ?_, ?_, ?_, ?_⟩
        · exact checkedSlice358bMachineTrace before seg
            (by unfold checkedSlice358bExitPc pcInList; native_decide)
        · exact ⟨0x13150, seg.atPc,
            by unfold checkedSlice358bExitPc pcInList; native_decide⟩
        · simp [checkedSlice358bContract, checkedSliceMeaning, presentTrue, endEq', selected,
            startLeLength]
        · refine ⟨by simp [checkedSliceMeaning, presentTrue, endEq', selected, startLeLength],
            by simpa [after, hasNext] using seg.atPc, ?_, sourceAfter, seg.writes, seg.mem,
            seg.retired, ?_, seg.aux, rfl, rfl, rfl, rfl⟩
          · exact ⟨rfl, by simp [hasNext, continuation]⟩
          · exact checkedSlice358bCodeOfSeg access loaded seg
  · have presentFalse : args.present = false := by simpa [present] using presentEq
    have absentRoute : zopz0zI_u (BitVec.ofNat 64 args.tableBytes) 17 = true := by
      rw [presentComparison]
      simp [show args.tableBytes < 17 by omega]
    obtain ⟨finalMachine, seg⟩ := checkedSlice358bEntryRun fromStep args.stackPointer
      args.sourceBytes.size args.tableBytes before.machine access atPc lengthAt tableAt
      thresholdAt absentRoute hasNextComparison loaded
    have seg' : Seg checkedSlice358bOwnPc checkedSlice358bExitPc
        (fun _ _ _ _ _ => False) checkedSlice358bWrites
        (checkedSlice358bMemory args.stackPointer)
        [⟨x10, BitVec.ofNat 64 args.sourceBytes.size⟩,
          ⟨x11, BitVec.ofNat 64 args.tableBytes⟩]
        fromStep 1 before.machine finalMachine 0x13cb8 := by
      simpa using seg
    let after : EndpointState := { before with machine := finalMachine }
    have sourceAfter := sourceRepOf358bSeg sourceRep sourceOutside seg'
    refine ⟨1, after, .empty, by omega, by change 1 ≤ 15; omega, ?_, ?_, ?_, ?_⟩
    · exact checkedSlice358bMachineTrace before seg'
        (by unfold checkedSlice358bExitPc pcInList; native_decide)
    · exact ⟨0x13cb8, seg'.atPc,
        by unfold checkedSlice358bExitPc pcInList; native_decide⟩
    · simp [checkedSlice358bContract, checkedSliceMeaning, presentFalse]
    · refine ⟨by simp [checkedSliceMeaning, presentFalse], by simpa [after] using seg'.atPc,
        by simp [checkedSlice358bSelectedRep], sourceAfter, seg'.writes, seg'.mem, seg'.retired,
        checkedSlice358bCodeOfSeg access loaded seg', seg'.aux, rfl, rfl, rfl, rfl⟩

def Proposed_ssz_decode__struct_1051_f_fi_1_358b_Contract : Prop :=
  checkedSlice358bContract.Implements EndpointStep EndpointPc
    checkedSlice358bOwnPc checkedSlice358bExitPc

theorem proposed_checkedSlice_358b_proved :
    Proposed_ssz_decode__struct_1051_f_fi_1_358b_Contract :=
  checkedSlice358bContract_implements

end BinaryFv.Zesu.Staging
