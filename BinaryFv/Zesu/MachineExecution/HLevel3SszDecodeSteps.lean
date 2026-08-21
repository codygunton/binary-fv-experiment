import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HLevel3MemReadIntSteps
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.ProofProgress.OwnedPc
import BinaryFv.RiscV.Instruction.DecodeTactic
import BinaryFv.RiscV.Elfling.Seg

/-!
# Parent-owned `ssz.decode` steps

This module composes the instructions that belong to the selected `ssz.decode` instance, outside
its selected children. The first segment loads the allocator descriptor and stores both words in
the decoder frame.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

def sszDecodeAllocatorPrefixOwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x121ac, 0x121b0, 0x121b4, 0x121b8, 0x121bc, 0x121c0] pc

def sszDecodeAllocatorPrefixExitPc (pc : BitVec 64) : Prop :=
  pcInList [0x121c4, 0x12200] pc

def sszDecodeAllocatorPrefixWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x10 ∨ register = x12 ∨ register = x14

def sszDecodeAllocatorPrefixMemory (stackPointer : Nat) : Region := fun address =>
  byteRange (stackPointer + 0x4b8) 8 address ∨ byteRange (stackPointer + 0x4c0) 8 address

private theorem instructionPreserved_disjoint_sszDecodeAllocatorPrefixWrites :
    RegSet.Disjoint instructionPreserved sszDecodeAllocatorPrefixWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem sszDecodeAllocatorPrefixMemory_in_frame {args : DecodeInlineArgs} {address : Nat}
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (inside : sszDecodeAllocatorPrefixMemory
      (args.boundary.stackPointer - 0xbb0) address) :
    args.boundary.stackPointer - 0xbb0 ≤ address ∧ address < args.boundary.stackPointer := by
  unfold sszDecodeAllocatorPrefixMemory byteRange at inside
  rcases inside with first | second <;> omega

private theorem sszDecodeAllocatorAccessOfSeg {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {before : EndpointState} {kv a n cur pc}
    (frame : DecodeInlineFrame args values before)
    (seg : Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
      (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
      (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0)) kv a n
      before.machine cur pc) :
    DecodeBoundaryMachineAccess args.boundary cur :=
  frame.access.of_pma_regions_eq
    (seg.agree instructionPreserved_disjoint_sszDecodeAllocatorPrefixWrites) seg.retired
    (seg.get pma_regions (by simp [sszDecodeAllocatorPrefixWrites, stepBookkeeping]))

private theorem sszDecodeAllocatorCodeOfSeg {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {before : EndpointState} {kv a n cur pc}
    (frame : DecodeInlineFrame args values before)
    (seg : Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
      (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
      (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0)) kv a n
      before.machine cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  intro address byte fileByte
  rw [seg.mem address (by
    intro inside
    have outside := frame.access.frameNotCode address
      (sszDecodeAllocatorPrefixMemory_in_frame frame.stackFits inside).1
      (sszDecodeAllocatorPrefixMemory_in_frame frame.stackFits inside).2
    rw [fileByte] at outside
    cases outside)]
  exact frame.code address byte fileByte

/-- Exact `0x121ac: ld a0,0(a1)`. -/
theorem sszDecodeLoadAllocatorStateStep (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (access : DecodeBoundaryMachineAccess args.boundary state)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (atPc : state.regs.get? PC = some 0x121ac)
    (allocatorAt : state.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (rep : UIntRep 8 state.mem (args.boundary.stackPointer + 0x10)
      args.boundary.allocatorStateAddress)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121ac retired x10
        (BitVec.ofNat 64 args.boundary.allocatorStateAddress)) false := by
  apply configuredDwordLoadStep stepNo 0x121ac state 0 (.Regidx 11#5) (.Regidx 10#5)
    x10 (args.boundary.stackPointer + 0x10) 0 args.boundary.allocatorStateAddress
    (BitVec.ofNat 64 args.boundary.allocatorStateAddress) 0x03 0xb5 0x05 0x00
    access.configured atPc rep (access.callerLoad 0x10 8 (by omega))
    (access.callerNoMMIO 0x10 8 (by omega)) (by omega) (by omega) loaded
    (addressEq := by
      change BitVec.ofNat 64 (args.boundary.stackPointer + 0x10) +
        sign_extend (m := 64) (0 : BitVec 12) = _
      rw [show sign_extend (m := 64) (0 : BitVec 12) = 0 by native_decide]
      simp)
    (baseRun := by
      intro premise writes
      exact rX_x11_run premise _ ((writes.get x11 (by decide)).trans allocatorAt))
    (writeRun := by intro premise; exact wX_x10_run premise _)
    (decode := by configured_decode access.configured) (base := by rfl)

/-- Exact `0x121b0: ld a2,8(a1)`. -/
theorem sszDecodeLoadAllocatorVtableStep (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (access : DecodeBoundaryMachineAccess args.boundary state)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (atPc : state.regs.get? PC = some 0x121b0)
    (allocatorAt : state.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (rep : UIntRep 8 state.mem (args.boundary.stackPointer + 0x18)
      args.boundary.allocatorVtableAddress)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121b0 retired x12
        (BitVec.ofNat 64 args.boundary.allocatorVtableAddress)) false := by
  apply configuredDwordLoadStep stepNo 0x121b0 state 8 (.Regidx 11#5) (.Regidx 12#5)
    x12 (args.boundary.stackPointer + 0x10) 8 args.boundary.allocatorVtableAddress
    (BitVec.ofNat 64 args.boundary.allocatorVtableAddress) 0x03 0xb6 0x85 0x00
    access.configured atPc rep (access.callerLoad 0x18 8 (by omega))
    (access.callerNoMMIO 0x18 8 (by omega)) (by omega) (by omega) loaded
    (addressEq := by
      change BitVec.ofNat 64 (args.boundary.stackPointer + 0x10) + 8#64 = _
      rw [← BitVec.ofNat_add])
    (baseRun := by
      intro premise writes
      exact rX_x11_run premise _ ((writes.get x11 (by decide)).trans allocatorAt))
    (writeRun := by intro premise; exact wX_x12_run premise _)
    (decode := by configured_decode access.configured) (base := by rfl)

/-- Exact `0x121b4: li a4,3`. -/
theorem sszDecodeLoadFieldCountStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x121b4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121b4 retired x14 3) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121b4
  have execute : Runs (execute (.ITYPE (3, .Regidx 0#5, .Regidx 14#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x14 3 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 3 (.Regidx 0#5) (.Regidx 14#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 3 0 = 3#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 3 (.Regidx 0#5)
      (.Regidx 14#5) .ADDI 0 (rX_x0_run premise) (wX_x14_run premise _)
  exact configuredRegisterWriteStep stepNo 0x121b4 state x14 3
    (.ITYPE (3, .Regidx 0#5, .Regidx 14#5, .ADDI)) 0x13 0x07 0x30 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x121b8: sd a0,0x4b8(sp)`. -/
theorem sszDecodeStoreAllocatorStateStep (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (access : DecodeBoundaryMachineAccess args.boundary state)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (atPc : state.regs.get? PC = some 0x121b8)
    (stackAt : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (valueAt : state.regs.get? x10 =
      some (BitVec.ofNat 64 args.boundary.allocatorStateAddress))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x121b8)
          (args.boundary.stackPointer - 0xbb0 + 0x4b8)
          (BitVec.ofNat 64 args.boundary.allocatorStateAddress))
        0x121b8 retired) false := by
  apply configuredStackDwordStoreStep stepNo 0x121b8
    (args.boundary.stackPointer - 0xbb0) 0x4b8 state
    (BitVec.ofNat 64 args.boundary.allocatorStateAddress) 0x4b8 (.Regidx 10#5)
    0x23 0x3c 0xa1 0x4a access.configured atPc stackAt
    (access.frameStore 0x4b8 8 (by omega)) (access.frameNoMMIO 0x4b8 8 (by omega))
    (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) + 0x4b8#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := access.configured.storeDecodeContext
    decode_run
  · intro premise writes
    exact rX_x10_run premise _ ((writes.get x10 (by decide)).trans valueAt)

/-- Exact `0x121bc: sd a2,0x4c0(sp)`. -/
theorem sszDecodeStoreAllocatorVtableStep (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (access : DecodeBoundaryMachineAccess args.boundary state)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (atPc : state.regs.get? PC = some 0x121bc)
    (stackAt : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (valueAt : state.regs.get? x12 =
      some (BitVec.ofNat 64 args.boundary.allocatorVtableAddress))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x121bc)
          (args.boundary.stackPointer - 0xbb0 + 0x4c0)
          (BitVec.ofNat 64 args.boundary.allocatorVtableAddress))
        0x121bc retired) false := by
  apply configuredStackDwordStoreStep stepNo 0x121bc
    (args.boundary.stackPointer - 0xbb0) 0x4c0 state
    (BitVec.ofNat 64 args.boundary.allocatorVtableAddress) 0x4c0 (.Regidx 12#5)
    0x23 0x30 0xc1 0x4c access.configured atPc stackAt
    (access.frameStore 0x4c0 8 (by omega)) (access.frameNoMMIO 0x4c0 8 (by omega))
    (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) + 0x4c0#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := access.configured.storeDecodeContext
    decode_run
  · intro premise writes
    exact rX_x12_run premise _ ((writes.get x12 (by decide)).trans valueAt)

/-- The unique five-instruction allocator prefix of `ssz.decode`. -/
theorem sszDecodeAllocatorPrefixSeg (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x121ac)
    (allocatorAt : before.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10))) :
    ∃ after,
      Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
        (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
        (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0))
        [⟨x14, 3⟩, ⟨x12, BitVec.ofNat 64 args.boundary.allocatorVtableAddress⟩,
          ⟨x10, BitVec.ofNat 64 args.boundary.allocatorStateAddress⟩]
        fromStep 5 before.machine after 0x121c0 ∧
      UIntRep 8 after.mem (args.boundary.stackPointer - 0xbb0 + 0x4b8)
        args.boundary.allocatorStateAddress ∧
      UIntRep 8 after.mem (args.boundary.stackPointer - 0xbb0 + 0x4c0)
        args.boundary.allocatorVtableAddress := by
  have stackFits := frame.stackFits
  have stackUpper := frame.stackUpper
  obtain ⟨retired, retiredRead⟩ := frame.configured.retiredCounter
  have seg0 := Seg.nil sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
    (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
    (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0))
    fromStep ⟨retired, retiredRead⟩ atPc
  obtain ⟨s1, seg1⟩ := seg0.step
    (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
    (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList]) x10
    (BitVec.ofNat 64 args.boundary.allocatorStateAddress) 0x121b0
    (sszDecodeLoadAllocatorStateStep fromStep args before.machine frame.access
      frame.stackAligned frame.stackUpper atPc allocatorAt frame.allocatorState frame.code)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inl rfl)) (by decide) (by decide) (by simp [RegsOutside])
  have vtable1 := frame.allocatorVtable.of_writesOnlyWithin seg1.mem (by
    intro index bound inside
    have inFrame := sszDecodeAllocatorPrefixMemory_in_frame frame.stackFits inside
    omega)
  obtain ⟨s2, seg2⟩ := seg1.step
    (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
    (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList]) x12
    (BitVec.ofNat 64 args.boundary.allocatorVtableAddress) 0x121b4
    (sszDecodeLoadAllocatorVtableStep (fromStep + 1) args s1
      (sszDecodeAllocatorAccessOfSeg frame seg1) frame.stackAligned frame.stackUpper seg1.atPc
      ((seg1.get x11 (by simp [sszDecodeAllocatorPrefixWrites])).trans allocatorAt) vtable1
      (sszDecodeAllocatorCodeOfSeg frame seg1))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨s3, seg3⟩ := seg2.step
    (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
    (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList]) x14 3 0x121b8
    (sszDecodeLoadFieldCountStep (fromStep + 2) s2
      (sszDecodeAllocatorAccessOfSeg frame seg2).configured seg2.atPc
      (sszDecodeAllocatorCodeOfSeg frame seg2))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inr rfl))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨retired3, s4, s4Eq, seg4⟩ := seg3.stepStoreWitness
    (width := 8) (args.boundary.stackPointer - 0xbb0 + 0x4b8)
    (BitVec.ofNat 64 args.boundary.allocatorStateAddress) 0x121bc
    (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
    (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList])
    (sszDecodeStoreAllocatorStateStep (fromStep + 3) args s3
      (sszDecodeAllocatorAccessOfSeg frame seg3) frame.stackAligned frame.stackUpper seg3.atPc
      ((seg3.get x2 (by simp [sszDecodeAllocatorPrefixWrites])).trans frame.atStack)
      (seg3.reg x10 (BitVec.ofNat 64 args.boundary.allocatorStateAddress) (by simp))
      (sszDecodeAllocatorCodeOfSeg frame seg3))
    (by native_decide)
    (by intro address lower upper; unfold sszDecodeAllocatorPrefixMemory byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have storedState : UIntRep 8 s4.mem
      (args.boundary.stackPointer - 0xbb0 + 0x4b8)
      args.boundary.allocatorStateAddress := by
    rw [s4Eq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement s3) 0x121b8)
        (args.boundary.stackPointer - 0xbb0 + 0x4b8)
        args.boundary.allocatorStateAddress frame.allocatorState.1 (by omega)
  obtain ⟨retired4, s5, s5Eq, seg5⟩ := seg4.stepStoreWitness
    (width := 8) (args.boundary.stackPointer - 0xbb0 + 0x4c0)
    (BitVec.ofNat 64 args.boundary.allocatorVtableAddress) 0x121c0
    (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
    (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList])
    (sszDecodeStoreAllocatorVtableStep (fromStep + 4) args s4
      (sszDecodeAllocatorAccessOfSeg frame seg4) frame.stackAligned frame.stackUpper seg4.atPc
      ((seg4.get x2 (by simp [sszDecodeAllocatorPrefixWrites])).trans frame.atStack)
      (seg4.reg x12 (BitVec.ofNat 64 args.boundary.allocatorVtableAddress) (by simp))
      (sszDecodeAllocatorCodeOfSeg frame seg4))
    (by native_decide)
    (by intro address lower upper; unfold sszDecodeAllocatorPrefixMemory byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have storedState5 : UIntRep 8 s5.mem
      (args.boundary.stackPointer - 0xbb0 + 0x4b8)
      args.boundary.allocatorStateAddress := by
    refine ⟨storedState.1, storedState.2.1, ?_⟩
    intro index bound
    rw [s5Eq]
    simp only [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]
    rw [afterWriteBytes_mem_get?_of_outside]
    · simpa [coreStoreNextState, tryStepStoreAfterIncrement,
        tryStepControlFlowAfterIncrement] using storedState.2.2 index bound
    · intro writtenIndex
      omega
  have storedVtable : UIntRep 8 s5.mem
      (args.boundary.stackPointer - 0xbb0 + 0x4c0)
      args.boundary.allocatorVtableAddress := by
    rw [s5Eq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement s4) 0x121bc)
        (args.boundary.stackPointer - 0xbb0 + 0x4c0)
        args.boundary.allocatorVtableAddress frame.allocatorVtable.1 (by omega)
  exact ⟨s5, by simpa only [Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seg5,
    storedState5, storedVtable⟩

private theorem sszDecodeFieldCountBgeuRun (state : State) (inputSize : Nat)
    (fieldCountAt : state.regs.get? x14 = some 3)
    (inputSizeAt : state.regs.get? x13 = some (BitVec.ofNat 64 inputSize)) :
    Runs (bTypeTaken (.Regidx 13#5) (.Regidx 14#5) .BGEU) state state
      (zopz0zKzJ_u 3 (BitVec.ofNat 64 inputSize)) := by
  unfold bTypeTaken
  exact Runs.bind (rX_x14_run state 3 fieldCountAt)
    (Runs.bind (rX_x13_run state (BitVec.ofNat 64 inputSize) inputSizeAt) rfl)

/-- The fall-through branch implies that the four-byte schema word exists. -/
theorem sszDecodeInputLengthAtLeastFour (inputSize : Nat)
    (fits : inputSize < 2 ^ 64)
    (comparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 inputSize) = false) :
    4 ≤ inputSize := by
  simp only [zopz0zKzJ_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat] at comparison
  rw [Nat.mod_eq_of_lt fits] at comparison
  simp at comparison
  omega

/-- Exact taken or not-taken `0x121c0: bgeu a4,a3,0x12200`. -/
theorem sszDecodeFieldCountBranchStep (stepNo inputSize : Nat) (args : DecodeInlineArgs)
    (state : State)
    (access : DecodeBoundaryMachineAccess args.boundary state)
    (atPc : state.regs.get? PC = some 0x121c0)
    (fieldCountAt : state.regs.get? x14 = some 3)
    (inputSizeAt : state.regs.get? x13 = some (BitVec.ofNat 64 inputSize))
    (comparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 inputSize) = short)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if short then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x121c0 0x12200)
          0x12200 retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121c0)
          0x121c4 retired) false := by
  cases short
  · apply configuredBranchNotTakenStep stepNo 0x121c0 state 0x40 (.Regidx 13#5)
      (.Regidx 14#5) .BGEU 0x63 0x70 0xd7 0x04 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using sszDecodeFieldCountBgeuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121c0)
        inputSize
        ((stepPremiseState_writes state 0x121c0).get x14 (by decide) |>.trans fieldCountAt)
        ((stepPremiseState_writes state 0x121c0).get x13 (by decide) |>.trans inputSizeAt)
  · apply configuredBranchTakenStep stepNo 0x121c0 0x12200 state 0x40 (.Regidx 13#5)
      (.Regidx 14#5) .BGEU 0x63 0x70 0xd7 0x04 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using sszDecodeFieldCountBgeuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121c0)
        inputSize
        ((stepPremiseState_writes state 0x121c0).get x14 (by decide) |>.trans fieldCountAt)
        ((stepPremiseState_writes state 0x121c0).get x13 (by decide) |>.trans inputSizeAt)
    all_goals native_decide

/-- The allocator prefix and its first exact branch route. -/
theorem sszDecodeAllocatorBranchSeg (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x121ac)
    (allocatorAt : before.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (inputSizeAt : before.machine.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size))
    (comparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 args.boundary.input.size) = short) :
    ∃ after,
      Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
        (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
        (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0))
        [⟨x14, 3⟩, ⟨x12, BitVec.ofNat 64 args.boundary.allocatorVtableAddress⟩,
          ⟨x10, BitVec.ofNat 64 args.boundary.allocatorStateAddress⟩]
        fromStep 6 before.machine after (if short then 0x12200 else 0x121c4) ∧
      UIntRep 8 after.mem (args.boundary.stackPointer - 0xbb0 + 0x4b8)
        args.boundary.allocatorStateAddress ∧
      UIntRep 8 after.mem (args.boundary.stackPointer - 0xbb0 + 0x4c0)
        args.boundary.allocatorVtableAddress := by
  obtain ⟨branched, prefixSeg, storedState, storedVtable⟩ :=
    sszDecodeAllocatorPrefixSeg fromStep args values before frame atPc allocatorAt
  have currentInputSize : branched.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size) :=
    (prefixSeg.get x13 (by simp [sszDecodeAllocatorPrefixWrites])).trans inputSizeAt
  cases short
  · obtain ⟨retired, after, afterEq, full⟩ := prefixSeg.stepFallThroughWitness 0x121c4
      (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
      (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList])
      (sszDecodeFieldCountBranchStep (fromStep + 5) args.boundary.input.size args branched
        (sszDecodeAllocatorAccessOfSeg frame prefixSeg) prefixSeg.atPc
        (prefixSeg.reg x14 3 (by simp)) currentInputSize comparison
        (sszDecodeAllocatorCodeOfSeg frame prefixSeg))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    refine ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full,
      ?_, ?_⟩
    · rw [afterEq]
      exact storedState.of_mem_eq (fallThroughRetirement_mem branched 0x121c0 0x121c4 retired)
    · rw [afterEq]
      exact storedVtable.of_mem_eq
        (fallThroughRetirement_mem branched 0x121c0 0x121c4 retired)
  · obtain ⟨retired, after, afterEq, full⟩ := prefixSeg.stepJumpWitness 0x12200
      (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
      (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList])
      (sszDecodeFieldCountBranchStep (fromStep + 5) args.boundary.input.size args branched
        (sszDecodeAllocatorAccessOfSeg frame prefixSeg) prefixSeg.atPc
        (prefixSeg.reg x14 3 (by simp)) currentInputSize comparison
        (sszDecodeAllocatorCodeOfSeg frame prefixSeg))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    refine ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full,
      ?_, ?_⟩
    · rw [afterEq]
      exact storedState.of_mem_eq (jumpRetirement_mem branched 0x121c0 0x12200 retired)
    · rw [afterEq]
      exact storedVtable.of_mem_eq (jumpRetirement_mem branched 0x121c0 0x12200 retired)

/-- Typed entry facts for the first four-byte read after the allocator prefix. -/
structure SszDecodeSchemaWordEntry (args : DecodeInlineArgs) (state : State) : Prop where
  atPc : state.regs.get? PC = some 0x121c4
  atStack : state.regs.get? x2 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0))
  sourceAt : state.regs.get? x18 = some (BitVec.ofNat 64 args.boundary.inputAddress)
  sizeAt : state.regs.get? x13 = some (BitVec.ofNat 64 args.boundary.input.size)
  input : BytesRep state.mem args.boundary.inputAddress args.boundary.input
  inputAtLeastFour : 4 ≤ args.boundary.input.size
  access : DecodeBoundaryMachineAccess args.boundary state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem

/-- The fall-through route produces the exact typed entry for `mem.readInt`. -/
theorem sszDecodeAllocatorFallThroughHandoff (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x121ac)
    (allocatorAt : before.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (inputSizeAt : before.machine.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size))
    (sourceAt : before.machine.regs.get? x18 =
      some (BitVec.ofNat 64 args.boundary.inputAddress))
    (comparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 args.boundary.input.size) = false) :
    ∃ after,
      Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
        (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
        (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0))
        [⟨x14, 3⟩, ⟨x12, BitVec.ofNat 64 args.boundary.allocatorVtableAddress⟩,
          ⟨x10, BitVec.ofNat 64 args.boundary.allocatorStateAddress⟩]
        fromStep 6 before.machine after 0x121c4 ∧
      SszDecodeSchemaWordEntry args after := by
  obtain ⟨after, seg, _storedState, _storedVtable⟩ :=
    sszDecodeAllocatorBranchSeg fromStep args values before frame atPc allocatorAt inputSizeAt
      comparison
  have inputAfter := frame.input.of_writesOnlyWithin seg.mem (by
    intro index bound inside
    have inFrame := sszDecodeAllocatorPrefixMemory_in_frame frame.stackFits inside
    rcases frame.inputSeparated with above | below <;> omega)
  refine ⟨after, seg, seg.atPc, ?_, ?_, ?_, inputAfter,
    sszDecodeInputLengthAtLeastFour args.boundary.input.size frame.inputSize.1 comparison,
    sszDecodeAllocatorAccessOfSeg frame seg, sszDecodeAllocatorCodeOfSeg frame seg⟩
  · exact (seg.get x2 (by simp [sszDecodeAllocatorPrefixWrites])).trans frame.atStack
  · exact (seg.get x18 (by simp [sszDecodeAllocatorPrefixWrites])).trans sourceAt
  · exact (seg.get x13 (by simp [sszDecodeAllocatorPrefixWrites])).trans inputSizeAt

/-- Typed entry facts for the short-input route at `0x12200`. -/
structure SszDecodeShortLengthEntry (args : DecodeInlineArgs) (state : State) : Prop where
  atPc : state.regs.get? PC = some 0x12200
  atStack : state.regs.get? x2 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0))
  inputSizeAt : state.regs.get? x13 = some (BitVec.ofNat 64 args.boundary.input.size)
  access : DecodeBoundaryMachineAccess args.boundary state
  configured : ConfiguredMachinePre EndpointMachinePc state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem

/-- The taken first branch produces the exact short-input route entry. -/
theorem sszDecodeAllocatorShortHandoff (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x121ac)
    (allocatorAt : before.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (inputSizeAt : before.machine.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size))
    (comparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 args.boundary.input.size) = true) :
    ∃ after,
      Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
        (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
        (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0))
        [⟨x14, 3⟩, ⟨x12, BitVec.ofNat 64 args.boundary.allocatorVtableAddress⟩,
          ⟨x10, BitVec.ofNat 64 args.boundary.allocatorStateAddress⟩]
        fromStep 6 before.machine after 0x12200 ∧
      SszDecodeShortLengthEntry args after := by
  obtain ⟨after, seg, _storedState, _storedVtable⟩ :=
    sszDecodeAllocatorBranchSeg fromStep args values before frame atPc allocatorAt inputSizeAt
      comparison
  have access := sszDecodeAllocatorAccessOfSeg frame seg
  refine ⟨after, seg, seg.atPc, ?_, ?_, access, access.configured,
    sszDecodeAllocatorCodeOfSeg frame seg⟩
  · exact (seg.get x2 (by simp [sszDecodeAllocatorPrefixWrites])).trans frame.atStack
  exact (seg.get x13 (by simp [sszDecodeAllocatorPrefixWrites])).trans inputSizeAt

def sszDecodeLengthMinimumOwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x12204, 0x12208] pc

def sszDecodeLengthMinimumExitPc (pc : BitVec 64) : Prop :=
  pcInList [0x1220c, 0x1225c] pc

def sszDecodeLengthMinimumWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x12

private theorem instructionPreserved_disjoint_sszDecodeLengthMinimumWrites :
    RegSet.Disjoint instructionPreserved sszDecodeLengthMinimumWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  · simp [instructionPreserved, platformPreserved] at preserved

/-- Exact `0x12204: li a2,2`. -/
theorem sszDecodeLengthMinimumStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12204)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12204 retired x12 2) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12204
  have execute : Runs (execute (.ITYPE (2, .Regidx 0#5, .Regidx 12#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x12 2 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 2 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 2 0 = 2#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 2 (.Regidx 0#5)
      (.Regidx 12#5) .ADDI 0 (rX_x0_run premise) (wX_x12_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12204 state x12 2
    (.ITYPE (2, .Regidx 0#5, .Regidx 12#5, .ADDI)) 0x13 0x06 0x20 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

private theorem sszDecodeLengthMinimumBltuRun (state : State) (length : BitVec 64)
    (lengthAt : state.regs.get? x10 = some length)
    (minimumAt : state.regs.get? x12 = some 2) :
    Runs (bTypeTaken (.Regidx 12#5) (.Regidx 10#5) .BLTU) state state
      (zopz0zI_u length 2) := by
  unfold bTypeTaken
  exact Runs.bind (rX_x10_run state length lengthAt)
    (Runs.bind (rX_x12_run state 2 minimumAt) rfl)

/-- Exact taken or not-taken `0x12208: bltu a0,a2,0x1225c`. -/
theorem sszDecodeLengthMinimumBranchStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12208)
    (lengthAt : state.regs.get? x10 = some length)
    (minimumAt : state.regs.get? x12 = some 2)
    (comparison : zopz0zI_u length 2 = short)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if short then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x12208 0x1225c)
          0x1225c retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12208)
          0x1220c retired) false := by
  cases short
  · apply configuredBranchNotTakenStep stepNo 0x12208 state 0x54 (.Regidx 12#5)
      (.Regidx 10#5) .BLTU 0x63 0x6a 0xc5 0x04 configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode configured
    · simpa only [comparison] using sszDecodeLengthMinimumBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12208)
        length
        ((stepPremiseState_writes state 0x12208).get x10 (by decide) |>.trans lengthAt)
        ((stepPremiseState_writes state 0x12208).get x12 (by decide) |>.trans minimumAt)
  · apply configuredBranchTakenStep stepNo 0x12208 0x1225c state 0x54 (.Regidx 12#5)
      (.Regidx 10#5) .BLTU 0x63 0x6a 0xc5 0x04 configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode configured
    · simpa only [comparison] using sszDecodeLengthMinimumBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12208)
        length
        ((stepPremiseState_writes state 0x12208).get x10 (by decide) |>.trans lengthAt)
        ((stepPremiseState_writes state 0x12208).get x12 (by decide) |>.trans minimumAt)
    all_goals native_decide

/-- Both length routes use this one `li; bltu` composition. -/
theorem sszDecodeLengthMinimumBranchSeg (fromStep : Nat) (before : State)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (atPc : before.regs.get? PC = some 0x12204)
    (lengthAt : before.regs.get? x10 = some length)
    (comparison : zopz0zI_u length 2 = short)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeLengthMinimumOwnPc sszDecodeLengthMinimumExitPc
        (fun _ _ _ _ _ => False) sszDecodeLengthMinimumWrites noMemory
        [⟨x12, 2⟩] fromStep 2 before after (if short then 0x1225c else 0x1220c) := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil sszDecodeLengthMinimumOwnPc sszDecodeLengthMinimumExitPc
    (fun _ _ _ _ _ => False) sszDecodeLengthMinimumWrites noMemory
    fromStep ⟨retired, retiredRead⟩ atPc
  obtain ⟨middle, seg1⟩ := seg0.step
    (by owned_pc [sszDecodeLengthMinimumOwnPc, pcInList])
    (by owned_pc [sszDecodeLengthMinimumExitPc, pcInList]) x12 2 0x12208
    (sszDecodeLengthMinimumStep fromStep before configured atPc loaded)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr rfl) (by decide) (by decide) (by simp [RegsOutside])
  have configured1 := configured.mono
    (seg1.agree instructionPreserved_disjoint_sszDecodeLengthMinimumWrites) seg1.retired
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully middle.mem := by
    rw [seg1.memEq noMemory_empty]
    exact loaded
  cases short
  · obtain ⟨_, after, _, full⟩ := seg1.stepFallThroughWitness 0x1220c
      (by owned_pc [sszDecodeLengthMinimumOwnPc, pcInList])
      (by owned_pc [sszDecodeLengthMinimumExitPc, pcInList])
      (sszDecodeLengthMinimumBranchStep (fromStep + 1) middle configured1 seg1.atPc
        ((seg1.get x10 (by simp [sszDecodeLengthMinimumWrites])).trans lengthAt)
        (seg1.reg x12 2 (by simp)) comparison loaded1)
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full⟩
  · obtain ⟨_, after, _, full⟩ := seg1.stepJumpWitness 0x1225c
      (by owned_pc [sszDecodeLengthMinimumOwnPc, pcInList])
      (by owned_pc [sszDecodeLengthMinimumExitPc, pcInList])
      (sszDecodeLengthMinimumBranchStep (fromStep + 1) middle configured1 seg1.atPc
        ((seg1.get x10 (by simp [sszDecodeLengthMinimumWrites])).trans lengthAt)
        (seg1.reg x12 2 (by simp)) comparison loaded1)
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full⟩

def sszDecodeLengthShortOwnPc (pc : BitVec 64) : Prop := pc = 0x12200

def sszDecodeLengthShortExitPc (pc : BitVec 64) : Prop := pc = 0x12204

def sszDecodeLengthShortWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x10

/-- Exact `0x12200: mv a0,a3`. -/
theorem sszDecodeLengthShortMoveStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12200)
    (inputSizeAt : state.regs.get? x13 = some inputSize)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12200 retired x10 inputSize) false := by
  have resultEq : inputSize = iTypeResult .ADDI 0 inputSize := by
    change inputSize = inputSize + sign_extend (m := 64) (0#12)
    rw [show sign_extend (m := 64) (0#12) = 0 by native_decide]
    simp
  apply configuredITypeX10Step stepNo 0x12200 state 0 (.Regidx 13#5) .ADDI
    inputSize inputSize 0x13 0x85 0x06 0x00 configured atPc loaded (base := by rfl)
  · exact resultEq
  · intro premise writes
    exact rX_x13_run premise inputSize ((writes.get x13 (by decide)).trans inputSizeAt)
  · intro premise
    rw [← resultEq]
    exact wX_x10_run premise inputSize
  · configured_decode configured

/-- The short-input route reaches the shared minimum-length suffix. -/
theorem sszDecodeLengthShortRouteSeg (fromStep : Nat) (before : State)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (atPc : before.regs.get? PC = some 0x12200)
    (inputSizeAt : before.regs.get? x13 = some inputSize)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeLengthShortOwnPc sszDecodeLengthShortExitPc
        (fun _ _ _ _ _ => False) sszDecodeLengthShortWrites noMemory
        [⟨x10, inputSize⟩] fromStep 1 before after 0x12204 := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil sszDecodeLengthShortOwnPc sszDecodeLengthShortExitPc
    (fun _ _ _ _ _ => False) sszDecodeLengthShortWrites noMemory
    fromStep ⟨retired, retiredRead⟩ atPc
  exact seg0.step
    (by simp [sszDecodeLengthShortOwnPc])
    (by simp [sszDecodeLengthShortExitPc]) x10 inputSize 0x12204
    (sszDecodeLengthShortMoveStep fromStep before configured atPc inputSizeAt loaded)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr rfl) (by decide) (by decide) (by simp [RegsOutside])

def sszDecodeLengthValidatedOwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x121ec, 0x121f0, 0x121f4, 0x121f8, 0x121fc] pc

def sszDecodeLengthValidatedExitPc (pc : BitVec 64) : Prop := pc = 0x12204

def sszDecodeLengthValidatedWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x10 ∨ register = x18 ∨ register = x13

/-- Exact `0x121ec: addi a0,a3,-4`. -/
theorem sszDecodeLengthSubtractSchemaStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x121ec)
    (inputSizeAt : state.regs.get? x13 = some inputSize)
    (resultEq : candidate = iTypeResult .ADDI 0xffc inputSize)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121ec retired x10 candidate) false := by
  exact configuredITypeX10Step stepNo 0x121ec state 0xffc (.Regidx 13#5) .ADDI
    inputSize candidate 0x13 0x85 0xc6 0xff configured atPc loaded resultEq
    (by
      intro premise writes
      exact rX_x13_run premise inputSize ((writes.get x13 (by decide)).trans inputSizeAt))
    (by intro premise; rw [← resultEq]; exact wX_x10_run premise candidate)
    (by configured_decode configured) (base := by rfl)

private theorem sszDecodeLengthBneRun (state : State) (candidate schema : BitVec 64)
    (candidateAt : state.regs.get? x10 = some candidate)
    (schemaAt : state.regs.get? x14 = some schema) :
    Runs (bTypeTaken (.Regidx 14#5) (.Regidx 10#5) .BNE) state state
      (candidate != schema) := by
  unfold bTypeTaken
  exact Runs.bind (rX_x10_run state candidate candidateAt)
    (Runs.bind (rX_x14_run state schema schemaAt) rfl)

/-- Exact equal-length fall-through at `0x121f0: bne a0,a4,0x1220c`. -/
theorem sszDecodeLengthEqualBranchStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x121f0)
    (candidateAt : state.regs.get? x10 = some candidate)
    (schemaAt : state.regs.get? x14 = some schema)
    (equal : candidate = schema)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121f0)
        0x121f4 retired) false := by
  apply configuredBranchNotTakenStep stepNo 0x121f0 state 0x1c (.Regidx 14#5)
    (.Regidx 10#5) .BNE 0x63 0x1e 0xe5 0x00 configured atPc loaded
    (site := by native_decide) (base := by rfl)
  · configured_decode configured
  · simpa [equal] using sszDecodeLengthBneRun
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121f0)
      candidate schema
      ((stepPremiseState_writes state 0x121f0).get x10 (by decide) |>.trans candidateAt)
      ((stepPremiseState_writes state 0x121f0).get x14 (by decide) |>.trans schemaAt)

/-- Exact `0x121f4: addi s2,s2,4`. -/
theorem sszDecodeAdvanceSourceStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x121f4)
    (sourceAt : state.regs.get? x18 = some source)
    (resultEq : advanced = iTypeResult .ADDI 4 source)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121f4 retired x18 advanced) false := by
  exact configuredITypeRegisterStep stepNo 0x121f4 state 4 (.Regidx 18#5) (.Regidx 18#5)
    x18 .ADDI source advanced 0x13 0x09 0x49 0x00 configured atPc loaded
    (by
      intro premise writes
      exact rX_x18_run premise source ((writes.get x18 (by decide)).trans sourceAt))
    (by intro premise; rw [← resultEq]; exact wX_x18_run premise advanced)
    (by configured_decode configured) (base := by rfl)
    (destinationNotNextPc := by decide) (destinationNotHart := by decide)
    (destinationNotIncrement := by decide) (destinationNotRetired := by decide)

/-- Exact `0x121f8: mv a3,a0`. -/
theorem sszDecodeBindValidatedLengthStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x121f8)
    (candidateAt : state.regs.get? x10 = some candidate)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121f8 retired x13 candidate) false := by
  have resultEq : candidate = iTypeResult .ADDI 0 candidate := by
    change candidate = candidate + sign_extend (m := 64) (0#12)
    rw [show sign_extend (m := 64) (0#12) = 0 by native_decide]
    simp
  exact configuredITypeRegisterStep stepNo 0x121f8 state 0 (.Regidx 10#5) (.Regidx 13#5)
    x13 .ADDI candidate candidate 0x93 0x06 0x05 0x00 configured atPc loaded
    (by
      intro premise writes
      exact rX_x10_run premise candidate ((writes.get x10 (by decide)).trans candidateAt))
    (by intro premise; rw [← resultEq]; exact wX_x13_run premise candidate)
    (by configured_decode configured) (base := by rfl)
    (destinationNotNextPc := by decide) (destinationNotHart := by decide)
    (destinationNotIncrement := by decide) (destinationNotRetired := by decide)

/-- Exact `0x121fc: j 0x12204`. -/
theorem sszDecodeLengthJoinStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x121fc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x121fc 0x12204)
        0x12204 retired) false := by
  exact configuredJStep stepNo 0x121fc 0x12204 state 8 0x6f 0x00 0x80 0x00
    configured atPc loaded (by configured_decode configured)
    (by native_decide) (by native_decide) (by native_decide) (base := by rfl)

private theorem instructionPreserved_disjoint_sszDecodeLengthValidatedWrites :
    RegSet.Disjoint instructionPreserved sszDecodeLengthValidatedWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem sszDecodeLengthValidatedConfiguredOfSeg {before cur : State} {kv a n pc}
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (seg : Seg sszDecodeLengthValidatedOwnPc sszDecodeLengthValidatedExitPc
      (fun _ _ _ _ _ => False) sszDecodeLengthValidatedWrites noMemory
      kv a n before cur pc) : ConfiguredMachinePre EndpointMachinePc cur :=
  configured.mono (seg.agree instructionPreserved_disjoint_sszDecodeLengthValidatedWrites)
    seg.retired

private theorem sszDecodeLengthValidatedLoadedOfSeg {before cur : State} {kv a n pc}
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg sszDecodeLengthValidatedOwnPc sszDecodeLengthValidatedExitPc
      (fun _ _ _ _ _ => False) sszDecodeLengthValidatedWrites noMemory
      kv a n before cur pc) : Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  rw [seg.memEq noMemory_empty]
  exact loaded

/-- The validated route reaches the shared minimum-length suffix with one `Seg`. -/
theorem sszDecodeLengthValidatedRouteSeg (fromStep : Nat) (before : State)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (atPc : before.regs.get? PC = some 0x121ec)
    (inputSizeAt : before.regs.get? x13 = some inputSize)
    (schemaAt : before.regs.get? x14 = some schema)
    (sourceAt : before.regs.get? x18 = some source)
    (candidateEq : candidate = iTypeResult .ADDI 0xffc inputSize)
    (lengthEqual : candidate = schema)
    (advancedEq : advanced = iTypeResult .ADDI 4 source)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeLengthValidatedOwnPc sszDecodeLengthValidatedExitPc
        (fun _ _ _ _ _ => False) sszDecodeLengthValidatedWrites noMemory
        [⟨x13, candidate⟩, ⟨x18, advanced⟩, ⟨x10, candidate⟩]
        fromStep 5 before after 0x12204 := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := (Seg.nil sszDecodeLengthValidatedOwnPc sszDecodeLengthValidatedExitPc
    (fun _ _ _ _ _ => False) sszDecodeLengthValidatedWrites noMemory
    fromStep ⟨retired, retiredRead⟩ atPc).know x18 source sourceAt
  obtain ⟨s1, seg1⟩ := seg0.step
    (by owned_pc [sszDecodeLengthValidatedOwnPc, pcInList])
    (by simp [sszDecodeLengthValidatedExitPc]) x10 candidate 0x121f0
    (sszDecodeLengthSubtractSchemaStep fromStep before configured atPc inputSizeAt candidateEq
      loaded)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inl rfl)) (by decide) (by decide) (by simp [RegsOutside])
  obtain ⟨_, s2, _, seg2⟩ := seg1.stepFallThroughWitness 0x121f4
    (by owned_pc [sszDecodeLengthValidatedOwnPc, pcInList])
    (by simp [sszDecodeLengthValidatedExitPc])
    (sszDecodeLengthEqualBranchStep (fromStep + 1) s1
      (sszDecodeLengthValidatedConfiguredOfSeg configured seg1) seg1.atPc
      (seg1.reg x10 candidate (by simp))
      ((seg1.get x14 (by simp [sszDecodeLengthValidatedWrites])).trans schemaAt)
      lengthEqual (sszDecodeLengthValidatedLoadedOfSeg loaded seg1))
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have seg2' := seg2.forget (kv' := [⟨x10, candidate⟩]) (by simp)
  obtain ⟨s3, seg3⟩ := seg2'.step
    (by owned_pc [sszDecodeLengthValidatedOwnPc, pcInList])
    (by simp [sszDecodeLengthValidatedExitPc]) x18 advanced 0x121f8
    (sszDecodeAdvanceSourceStep (fromStep + 2) s2
      (sszDecodeLengthValidatedConfiguredOfSeg configured seg2') seg2'.atPc
      (seg2.reg x18 source (by simp))
      advancedEq (sszDecodeLengthValidatedLoadedOfSeg loaded seg2'))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨s4, seg4⟩ := seg3.step
    (by owned_pc [sszDecodeLengthValidatedOwnPc, pcInList])
    (by simp [sszDecodeLengthValidatedExitPc]) x13 candidate 0x121fc
    (sszDecodeBindValidatedLengthStep (fromStep + 3) s3
      (sszDecodeLengthValidatedConfiguredOfSeg configured seg3) seg3.atPc
      (seg3.reg x10 candidate (by simp)) (sszDecodeLengthValidatedLoadedOfSeg loaded seg3))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inr rfl))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨_, after, _, seg5⟩ := seg4.stepJumpWitness 0x12204
    (by owned_pc [sszDecodeLengthValidatedOwnPc, pcInList])
    (by simp [sszDecodeLengthValidatedExitPc])
    (sszDecodeLengthJoinStep (fromStep + 4) s4
      (sszDecodeLengthValidatedConfiguredOfSeg configured seg4) seg4.atPc
      (sszDecodeLengthValidatedLoadedOfSeg loaded seg4))
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seg5⟩

def sszDecodeSchemaMarkerOwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x1220c, 0x12210, 0x12214] pc

def sszDecodeSchemaMarkerExitPc (pc : BitVec 64) : Prop :=
  pcInList [0x12218, 0x1225c] pc

def sszDecodeSchemaMarkerWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x10 ∨ register = x12

private theorem sszDecodeOfNatAddOne (base : Nat) (_fits : base + 1 < 2 ^ 64) :
    BitVec.ofNat 64 base + sign_extend (m := 64) (1#12) = BitVec.ofNat 64 (base + 1) := by
  rw [show sign_extend (m := 64) (1#12) = 1#64 by native_decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- Exact `0x1220c: lbu a0,1(s2)`, through the shared byte-load theorem. -/
theorem sszDecodeLoadSchemaMarkerStep (stepNo baseAddress marker : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x1220c)
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem (baseAddress + 1) marker)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 1)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 1)) 1)
    (sumFits : baseAddress + 1 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1220c retired x10
        (zero_extend (m := 64) (BitVec.ofNat 8 marker))) false := by
  apply configuredByteLoadFromX18Step stepNo 0x1220c 1 state (.Regidx 10#5) x10
    (zero_extend (m := 64) (BitVec.ofNat 8 marker))
    0x03 0x45 0x19 0x00 baseAddress marker configured atPc base rep pma notMMIO sumFits loaded
  · configured_decode configured
  · intro premise
    exact wX_x10_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · exact sszDecodeOfNatAddOne baseAddress sumFits

/-- Exact `0x12210: li a2,1`. -/
theorem sszDecodeLoadSchemaMarkerExpectedStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12210)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12210 retired x12 1) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12210
  have execute : Runs (execute (.ITYPE (1, .Regidx 0#5, .Regidx 12#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x12 1 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 1 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 1 0 = 1#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 1 (.Regidx 0#5)
      (.Regidx 12#5) .ADDI 0 (rX_x0_run premise) (wX_x12_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12210 state x12 1
    (.ITYPE (1, .Regidx 0#5, .Regidx 12#5, .ADDI)) 0x13 0x06 0x10 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

private theorem sszDecodeSchemaMarkerBneRun (state : State) (marker : BitVec 64)
    (markerAt : state.regs.get? x10 = some marker)
    (expectedAt : state.regs.get? x12 = some 1) :
    Runs (bTypeTaken (.Regidx 12#5) (.Regidx 10#5) .BNE) state state (marker != 1) := by
  unfold bTypeTaken
  exact Runs.bind (rX_x10_run state marker markerAt)
    (Runs.bind (rX_x12_run state 1 expectedAt) rfl)

/-- Exact taken or not-taken `0x12214: bne a0,a2,0x1225c`. -/
theorem sszDecodeSchemaMarkerBranchStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12214)
    (markerAt : state.regs.get? x10 = some marker)
    (expectedAt : state.regs.get? x12 = some 1)
    (comparison : (marker != 1) = rejected)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if rejected then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x12214 0x1225c)
          0x1225c retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12214)
          0x12218 retired) false := by
  cases rejected
  · apply configuredBranchNotTakenStep stepNo 0x12214 state 0x48 (.Regidx 12#5)
      (.Regidx 10#5) .BNE 0x63 0x14 0xc5 0x04 configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode configured
    · simpa only [comparison] using sszDecodeSchemaMarkerBneRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12214)
        marker
        ((stepPremiseState_writes state 0x12214).get x10 (by decide) |>.trans markerAt)
        ((stepPremiseState_writes state 0x12214).get x12 (by decide) |>.trans expectedAt)
  · apply configuredBranchTakenStep stepNo 0x12214 0x1225c state 0x48 (.Regidx 12#5)
      (.Regidx 10#5) .BNE 0x63 0x14 0xc5 0x04 configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode configured
    · simpa only [comparison] using sszDecodeSchemaMarkerBneRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12214)
        marker
        ((stepPremiseState_writes state 0x12214).get x10 (by decide) |>.trans markerAt)
        ((stepPremiseState_writes state 0x12214).get x12 (by decide) |>.trans expectedAt)
    all_goals native_decide

private theorem instructionPreserved_disjoint_sszDecodeSchemaMarkerWrites :
    RegSet.Disjoint instructionPreserved sszDecodeSchemaMarkerWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

/-- The schema-marker load and comparison share one three-step `Seg` on both routes. -/
theorem sszDecodeSchemaMarkerSeg (fromStep baseAddress marker : Nat) (before : State)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (atPc : before.regs.get? PC = some 0x1220c)
    (base : before.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 before.mem (baseAddress + 1) marker)
    (pma : LoadPmaAllows before (BitVec.ofNat 64 (baseAddress + 1)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 1)) 1)
    (sumFits : baseAddress + 1 < 2 ^ 64)
    (comparison : (zero_extend (m := 64) (BitVec.ofNat 8 marker) != 1) = rejected)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeSchemaMarkerOwnPc sszDecodeSchemaMarkerExitPc
        (fun _ _ _ _ _ => False) sszDecodeSchemaMarkerWrites noMemory
        [⟨x12, 1⟩, ⟨x10, zero_extend (m := 64) (BitVec.ofNat 8 marker)⟩]
        fromStep 3 before after (if rejected then 0x1225c else 0x12218) := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil sszDecodeSchemaMarkerOwnPc sszDecodeSchemaMarkerExitPc
    (fun _ _ _ _ _ => False) sszDecodeSchemaMarkerWrites noMemory
    fromStep ⟨retired, retiredRead⟩ atPc
  obtain ⟨s1, seg1⟩ := seg0.step
    (by owned_pc [sszDecodeSchemaMarkerOwnPc, pcInList])
    (by owned_pc [sszDecodeSchemaMarkerExitPc, pcInList]) x10
    (zero_extend (m := 64) (BitVec.ofNat 8 marker)) 0x12210
    (sszDecodeLoadSchemaMarkerStep fromStep baseAddress marker before configured atPc base rep pma
      notMMIO sumFits loaded)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inl rfl)) (by decide) (by decide) (by simp [RegsOutside])
  have configured1 := configured.mono
    (seg1.agree instructionPreserved_disjoint_sszDecodeSchemaMarkerWrites) seg1.retired
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully s1.mem := by
    rw [seg1.memEq noMemory_empty]
    exact loaded
  obtain ⟨s2, seg2⟩ := seg1.step
    (by owned_pc [sszDecodeSchemaMarkerOwnPc, pcInList])
    (by owned_pc [sszDecodeSchemaMarkerExitPc, pcInList]) x12 1 0x12214
    (sszDecodeLoadSchemaMarkerExpectedStep (fromStep + 1) s1 configured1 seg1.atPc loaded1)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr rfl)) (by decide) (by decide) (by simp [RegsOutside])
  have configured2 := configured.mono
    (seg2.agree instructionPreserved_disjoint_sszDecodeSchemaMarkerWrites) seg2.retired
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully s2.mem := by
    rw [seg2.memEq noMemory_empty]
    exact loaded
  cases rejected
  · obtain ⟨_, after, _, full⟩ := seg2.stepFallThroughWitness 0x12218
      (by owned_pc [sszDecodeSchemaMarkerOwnPc, pcInList])
      (by owned_pc [sszDecodeSchemaMarkerExitPc, pcInList])
      (sszDecodeSchemaMarkerBranchStep (fromStep + 2) s2 configured2 seg2.atPc
        (seg2.reg x10 (zero_extend (m := 64) (BitVec.ofNat 8 marker)) (by simp))
        (seg2.reg x12 1 (by simp)) comparison loaded2)
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full⟩
  · obtain ⟨_, after, _, full⟩ := seg2.stepJumpWitness 0x1225c
      (by owned_pc [sszDecodeSchemaMarkerOwnPc, pcInList])
      (by owned_pc [sszDecodeSchemaMarkerExitPc, pcInList])
      (sszDecodeSchemaMarkerBranchStep (fromStep + 2) s2 configured2 seg2.atPc
        (seg2.reg x10 (zero_extend (m := 64) (BitVec.ofNat 8 marker)) (by simp))
        (seg2.reg x12 1 (by simp)) comparison loaded2)
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full⟩

/-! ## Shared cleanup stores -/

/-- Execute one exact decoder-frame `sd zero, offset(sp)` cleanup instruction. -/
theorem sszDecodeZeroDwordStoreStep (stepNo pc offset : Nat) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8) (args : DecodeInlineArgs) (state : State)
    (access : DecodeBoundaryMachineAccess args.boundary state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (atStack : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (aligned : (args.boundary.stackPointer - 0xbb0 + offset) % 8 = 0)
    (fits : args.boundary.stackPointer - 0xbb0 + offset + 8 ≤ 2 ^ 64)
    (frameBound : offset + 8 ≤ 0xbb0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) +
      sign_extend (m := 64) imm =
        BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (imm, .Regidx 0#5, .Regidx 2#5, 8)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc))
          (args.boundary.stackPointer - 0xbb0 + offset) 0)
        (BitVec.ofNat 64 pc) retired) false := by
  apply configuredStackDwordStoreStep stepNo pc
    (args.boundary.stackPointer - 0xbb0) offset state 0 imm (.Regidx 0#5)
    byte0 byte1 byte2 byte3 access.configured atPc atStack
    (access.frameStore offset 8 frameBound) (access.frameNoMMIO offset 8 frameBound)
    aligned fits loaded addressEq decode (by intro premise _; exact rX_x0_run premise)
    (site := site) (base := base)

/-- Execute one exact decoder-frame `sw zero, offset(sp)` cleanup instruction. -/
theorem sszDecodeZeroWordStoreStep (stepNo pc offset : Nat) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8) (args : DecodeInlineArgs) (state : State)
    (access : DecodeBoundaryMachineAccess args.boundary state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (atStack : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (aligned : (args.boundary.stackPointer - 0xbb0 + offset) % 4 = 0)
    (fits : args.boundary.stackPointer - 0xbb0 + offset + 4 ≤ 2 ^ 64)
    (frameBound : offset + 4 ≤ 0xbb0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) +
      sign_extend (m := 64) imm =
        BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (imm, .Regidx 0#5, .Regidx 2#5, 4)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 4)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pc))
          (args.boundary.stackPointer - 0xbb0 + offset) 0)
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  apply configuredStackWordStoreStep stepNo pc
    (args.boundary.stackPointer - 0xbb0) offset state 0 imm (.Regidx 0#5)
    byte0 byte1 byte2 byte3 access.configured atPc atStack
    (access.frameStore offset 4 frameBound) (access.frameNoMMIO offset 4 frameBound)
    aligned fits loaded addressEq decode (by intro premise _; exact rX_x0_run premise)
    (site := site) (base := base)

/-- Execute one exact decoder-frame `sh zero, offset(sp)` cleanup instruction. -/
theorem sszDecodeZeroHalfStoreStep (stepNo pc offset : Nat) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8) (args : DecodeInlineArgs) (state : State)
    (access : DecodeBoundaryMachineAccess args.boundary state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (atStack : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (aligned : (args.boundary.stackPointer - 0xbb0 + offset) % 2 = 0)
    (fits : args.boundary.stackPointer - 0xbb0 + offset + 2 ≤ 2 ^ 64)
    (frameBound : offset + 2 ≤ 0xbb0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) +
      sign_extend (m := 64) imm =
        BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (imm, .Regidx 0#5, .Regidx 2#5, 2)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 2)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pc))
          (args.boundary.stackPointer - 0xbb0 + offset) 0)
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  apply configuredStackHalfStoreStep stepNo pc
    (args.boundary.stackPointer - 0xbb0) offset state 0 imm (.Regidx 0#5)
    byte0 byte1 byte2 byte3 access.configured atPc atStack
    (access.frameStore offset 2 frameBound) (access.frameNoMMIO offset 2 frameBound)
    aligned fits loaded addressEq decode (by intro premise _; exact rX_x0_run premise)
    (site := site) (base := base)

/-- Execute one exact decoder-frame `sb zero, offset(sp)` cleanup instruction. -/
theorem sszDecodeZeroByteStoreStep (stepNo pc offset : Nat) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8) (args : DecodeInlineArgs) (state : State)
    (access : DecodeBoundaryMachineAccess args.boundary state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (atStack : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (fits : args.boundary.stackPointer - 0xbb0 + offset + 1 ≤ 2 ^ 64)
    (frameBound : offset + 1 ≤ 0xbb0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) +
      sign_extend (m := 64) imm =
        BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (imm, .Regidx 0#5, .Regidx 2#5, 1)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pc))
          (args.boundary.stackPointer - 0xbb0 + offset) 0)
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  apply configuredStackByteStoreStep stepNo pc
    (args.boundary.stackPointer - 0xbb0) offset state 0 imm (.Regidx 0#5)
    byte0 byte1 byte2 byte3 access.configured atPc atStack
    (access.frameStore offset 1 frameBound) (access.frameNoMMIO offset 1 frameBound)
    fits loaded addressEq decode (by intro premise _; exact rX_x0_run premise)
    (site := site) (base := base)

/-- Declare one exact double-word zero store from the shared cleanup theorem. -/
macro "sszDecodeZeroDwordSite(" name:ident ";" pc:term "," offset:term ";"
    byte0:term "," byte1:term "," byte2:term "," byte3:term ")" : command =>
  `(private theorem $name (stepNo : Nat) (args : DecodeInlineArgs) (state : State)
      (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
      (stackAligned : args.boundary.stackPointer % 16 = 0)
      (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
      (access : DecodeBoundaryMachineAccess args.boundary state)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (atStack : state.regs.get? x2 =
        some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
      (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepStoreAfterRetired
          (afterWriteBytes (width := 8)
            (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 $pc))
            (args.boundary.stackPointer - 0xbb0 + $offset) 0)
          (BitVec.ofNat 64 $pc) retired) false := by
      apply sszDecodeZeroDwordStoreStep stepNo $pc $offset (BitVec.ofNat 12 $offset)
        $byte0 $byte1 $byte2 $byte3 args state access atPc atStack
        (by omega) (by omega) (by omega) loaded
      · change BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) +
          BitVec.ofNat 64 $offset = _
        rw [← BitVec.ofNat_add]
      · configured_store_decode access.configured
      · native_decide
      · rfl)

sszDecodeZeroDwordSite(sszDecodeCleanupStore4a8; 0x1225c, 0x4a8;
  0x23, 0x34, 0x01, 0x4a)
sszDecodeZeroDwordSite(sszDecodeCleanupStore4b0; 0x12260, 0x4b0;
  0x23, 0x38, 0x01, 0x4a)
sszDecodeZeroDwordSite(sszDecodeCleanupStore488; 0x12268, 0x488;
  0x23, 0x34, 0x01, 0x48)
sszDecodeZeroDwordSite(sszDecodeCleanupStore490; 0x1226c, 0x490;
  0x23, 0x38, 0x01, 0x48)
sszDecodeZeroDwordSite(sszDecodeCleanupStore498; 0x12270, 0x498;
  0x23, 0x3c, 0x01, 0x48)
sszDecodeZeroDwordSite(sszDecodeCleanupStore4a0; 0x12274, 0x4a0;
  0x23, 0x30, 0x01, 0x4a)
sszDecodeZeroDwordSite(sszDecodeCleanupStore470; 0x12278, 0x470;
  0x23, 0x38, 0x01, 0x46)
sszDecodeZeroDwordSite(sszDecodeCleanupStore478; 0x1227c, 0x478;
  0x23, 0x3c, 0x01, 0x46)
sszDecodeZeroDwordSite(sszDecodeCleanupStore450; 0x12284, 0x450;
  0x23, 0x38, 0x01, 0x44)
sszDecodeZeroDwordSite(sszDecodeCleanupStore458; 0x12288, 0x458;
  0x23, 0x3c, 0x01, 0x44)
sszDecodeZeroDwordSite(sszDecodeCleanupStore460; 0x1228c, 0x460;
  0x23, 0x30, 0x01, 0x46)
sszDecodeZeroDwordSite(sszDecodeCleanupStore468; 0x12290, 0x468;
  0x23, 0x34, 0x01, 0x46)

/-- Declare one exact word zero store from the shared cleanup theorem. -/
macro "sszDecodeZeroWordSite(" name:ident ";" pc:term "," offset:term ";"
    byte0:term "," byte1:term "," byte2:term "," byte3:term ")" : command =>
  `(private theorem $name (stepNo : Nat) (args : DecodeInlineArgs) (state : State)
      (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
      (stackAligned : args.boundary.stackPointer % 16 = 0)
      (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
      (access : DecodeBoundaryMachineAccess args.boundary state)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (atStack : state.regs.get? x2 =
        some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
      (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepControlFlowAfterRetired
          (afterWriteBytes (width := 4)
            (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
              (BitVec.ofNat 64 $pc))
            (args.boundary.stackPointer - 0xbb0 + $offset) 0)
          (Sail.BitVec.addInt (BitVec.ofNat 64 $pc) 4) retired) false := by
      apply sszDecodeZeroWordStoreStep stepNo $pc $offset (BitVec.ofNat 12 $offset)
        $byte0 $byte1 $byte2 $byte3 args state access atPc atStack
        (by omega) (by omega) (by omega) loaded
      · change BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) +
          BitVec.ofNat 64 $offset = _
        rw [← BitVec.ofNat_add]
      · configured_decode access.configured
      · native_decide
      · rfl)

/-- Declare one exact half-word zero store from the shared cleanup theorem. -/
macro "sszDecodeZeroHalfSite(" name:ident ";" pc:term "," offset:term ";"
    byte0:term "," byte1:term "," byte2:term "," byte3:term ")" : command =>
  `(private theorem $name (stepNo : Nat) (args : DecodeInlineArgs) (state : State)
      (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
      (stackAligned : args.boundary.stackPointer % 16 = 0)
      (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
      (access : DecodeBoundaryMachineAccess args.boundary state)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (atStack : state.regs.get? x2 =
        some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
      (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepControlFlowAfterRetired
          (afterWriteBytes (width := 2)
            (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
              (BitVec.ofNat 64 $pc))
            (args.boundary.stackPointer - 0xbb0 + $offset) 0)
          (Sail.BitVec.addInt (BitVec.ofNat 64 $pc) 4) retired) false := by
      apply sszDecodeZeroHalfStoreStep stepNo $pc $offset (BitVec.ofNat 12 $offset)
        $byte0 $byte1 $byte2 $byte3 args state access atPc atStack
        (by omega) (by omega) (by omega) loaded
      · change BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) +
          BitVec.ofNat 64 $offset = _
        rw [← BitVec.ofNat_add]
      · configured_decode access.configured
      · native_decide
      · rfl)

/-- Declare one exact byte zero store from the shared cleanup theorem. -/
macro "sszDecodeZeroByteSite(" name:ident ";" pc:term "," offset:term ";"
    byte0:term "," byte1:term "," byte2:term "," byte3:term ")" : command =>
  `(private theorem $name (stepNo : Nat) (args : DecodeInlineArgs) (state : State)
      (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
      (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
      (access : DecodeBoundaryMachineAccess args.boundary state)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (atStack : state.regs.get? x2 =
        some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
      (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepControlFlowAfterRetired
          (afterWriteBytes (width := 1)
            (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
              (BitVec.ofNat 64 $pc))
            (args.boundary.stackPointer - 0xbb0 + $offset) 0)
          (Sail.BitVec.addInt (BitVec.ofNat 64 $pc) 4) retired) false := by
      apply sszDecodeZeroByteStoreStep stepNo $pc $offset (BitVec.ofNat 12 $offset)
        $byte0 $byte1 $byte2 $byte3 args state access atPc atStack
        (by omega) (by omega) loaded
      · change BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) +
          BitVec.ofNat 64 $offset = _
        rw [← BitVec.ofNat_add]
      · configured_decode access.configured
      · native_decide
      · rfl)

sszDecodeZeroWordSite(sszDecodeCleanupWord480; 0x12280, 0x480;
  0x23, 0x20, 0x01, 0x48)
sszDecodeZeroWordSite(sszDecodeCleanupWord2c8; 0x122e8, 0x2c8;
  0x23, 0x24, 0x01, 0x2c)
sszDecodeZeroHalfSite(sszDecodeCleanupHalf2cc; 0x122ec, 0x2cc;
  0x23, 0x16, 0x01, 0x2c)
sszDecodeZeroByteSite(sszDecodeCleanupByte2ce; 0x122f0, 0x2ce;
  0x23, 0x07, 0x01, 0x2c)
sszDecodeZeroWordSite(sszDecodeCleanupWord2c0; 0x122f4, 0x2c0;
  0x23, 0x20, 0x01, 0x2c)
sszDecodeZeroHalfSite(sszDecodeCleanupHalf2c4; 0x122f8, 0x2c4;
  0x23, 0x12, 0x01, 0x2c)
sszDecodeZeroByteSite(sszDecodeCleanupByte2c6; 0x122fc, 0x2c6;
  0x23, 0x03, 0x01, 0x2c)
sszDecodeZeroWordSite(sszDecodeCleanupWord2b8; 0x12300, 0x2b8;
  0x23, 0x2c, 0x01, 0x2a)
sszDecodeZeroHalfSite(sszDecodeCleanupHalf2bc; 0x12304, 0x2bc;
  0x23, 0x1e, 0x01, 0x2a)

/-- Exact `0x12264: auipc a0,5`, using the shared register-write step. -/
private theorem sszDecodeCleanupBaseHighStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12264)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12264 retired x10 0x17264) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12264
  have pcAtPremise : premise.regs.get? PC = some (0x12264 : BitVec 64) := by
    calc
      premise.regs.get? PC = (tryStepControlFlowAfterIncrement state).regs.get? PC := by
        simpa [premise, coreControlFlowNextState] using
          writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC PC 0x12268
            (by decide)
      _ = state.regs.get? PC := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment PC true (by decide)
      _ = some 0x12264 := atPc
  have execute : Runs (execute (.UTYPE (5, .Regidx 10#5, .AUIPC))) premise
      { premise with regs := premise.regs.insert x10 0x17264 } (.Retire_Success ()) := by
    change Runs (execute_UTYPE 5 (.Regidx 10#5) .AUIPC) _ _ _
    simpa using execute_UTYPE_auipc_run premise _ 5 (.Regidx 10#5) 0x12264
      (readReg_run premise PC _ pcAtPremise) (wX_x10_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12264 state x10 0x17264
    (.UTYPE (5, .Regidx 10#5, .AUIPC)) 0x17 0x55 0x00 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x12294: addi a1,a0,760`, using the shared I-type step. -/
private theorem sszDecodeCleanupBaseLowStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12294)
    (baseAt : state.regs.get? x10 = some 0x17264)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12294 retired x11 0x1755c) false := by
  have resultEq : (0x1755c : BitVec 64) = iTypeResult .ADDI 0x2f8 0x17264 := by
    native_decide
  exact configuredITypeX11Step stepNo 0x12294 state 0x2f8 (.Regidx 10#5) .ADDI
    0x17264 0x1755c 0x93 0x05 0x85 0x2f configured atPc loaded
    (by
      intro premise writes
      exact rX_x10_run premise 0x17264 ((writes.get x10 (by decide)).trans baseAt))
    (by intro premise; rw [← resultEq]; exact wX_x11_run premise 0x1755c)
    (by configured_decode configured) (base := by rfl)

def sszDecodeForkNameByteOwnPc (pc : BitVec 64) : Prop := pc = 0x12218

def sszDecodeForkNameByteExitPc (pc : BitVec 64) : Prop := pc = 0x1221c

def sszDecodeForkNameByteWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x10

/-- Exact `0x12218: lbu a0,0(s2)`, through the shared byte-load theorem. -/
theorem sszDecodeLoadForkNameByteStep (stepNo baseAddress schema : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12218)
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem baseAddress schema)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 baseAddress) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 baseAddress) 1)
    (baseFits : baseAddress < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12218 retired x10
        (zero_extend (m := 64) (BitVec.ofNat 8 schema))) false := by
  apply configuredByteLoadFromX18Step stepNo 0x12218 0 state (.Regidx 10#5) x10
    (zero_extend (m := 64) (BitVec.ofNat 8 schema))
    0x03 0x45 0x09 0x00 baseAddress schema configured atPc base (by simpa using rep)
    (by simpa using pma) (by simpa using notMMIO) (by simpa using baseFits) loaded
  · configured_decode configured
  · intro premise
    exact wX_x10_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rw [show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
    apply BitVec.eq_of_toNat_eq
    simp

/-- The parent schema-byte load produces the exact fork-name child register state. -/
theorem sszDecodeForkNameByteSeg (fromStep baseAddress schema : Nat) (before : State)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (atPc : before.regs.get? PC = some 0x12218)
    (base : before.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 before.mem baseAddress schema)
    (pma : LoadPmaAllows before (BitVec.ofNat 64 baseAddress) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 baseAddress) 1)
    (baseFits : baseAddress < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeForkNameByteOwnPc sszDecodeForkNameByteExitPc
        (fun _ _ _ _ _ => False) sszDecodeForkNameByteWrites noMemory
        [⟨x10, zero_extend (m := 64) (BitVec.ofNat 8 schema)⟩]
        fromStep 1 before after 0x1221c := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil sszDecodeForkNameByteOwnPc sszDecodeForkNameByteExitPc
    (fun _ _ _ _ _ => False) sszDecodeForkNameByteWrites noMemory
    fromStep ⟨retired, retiredRead⟩ atPc
  exact seg0.step
    (by simp [sszDecodeForkNameByteOwnPc])
    (by simp [sszDecodeForkNameByteExitPc]) x10
    (zero_extend (m := 64) (BitVec.ofNat 8 schema)) 0x1221c
    (sszDecodeLoadForkNameByteStep fromStep baseAddress schema before configured atPc base rep pma
      notMMIO baseFits loaded)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr rfl) (by decide) (by decide) (by simp [RegsOutside])

end BinaryFv.Zesu.MachineExecution
