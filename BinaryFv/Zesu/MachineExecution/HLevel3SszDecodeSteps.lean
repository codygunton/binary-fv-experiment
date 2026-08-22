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
  stackFits : 0xbb0 ≤ args.boundary.stackPointer
  stackAligned : args.boundary.stackPointer % 16 = 0
  stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64
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
  refine ⟨after, seg, seg.atPc, ?_, frame.stackFits, frame.stackAligned, frame.stackUpper,
    ?_, access, access.configured,
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

/-- The exact 256-byte file-backed template copied into the decoder frame. -/
def sszDecodeCleanupTemplateBytes : Array UInt8 :=
  Array.ofFn fun index : Fin 256 =>
    (Artifacts.programImage.readFileByte? (0x1755c + index.val)).getD 0

theorem sszDecodeCleanupTemplateBacked : ∀ index : Fin 256,
    (Artifacts.programImage.readFileByte? (0x1755c + index.val)).isSome := by
  native_decide

/-- Faithful loading gives the exact bytes consumed by the cleanup `memcpy`. -/
theorem sszDecodeCleanupTemplateRep (state : State)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    BytesRep state.mem 0x1755c sszDecodeCleanupTemplateBytes := by
  have size : sszDecodeCleanupTemplateBytes.size = 256 := by
    simp [sszDecodeCleanupTemplateBytes]
  refine ⟨by rw [size]; omega, ?_⟩
  intro index inBounds
  let fin : Fin 256 := ⟨index, by simpa [size] using inBounds⟩
  have backed := sszDecodeCleanupTemplateBacked fin
  cases readEq : Artifacts.programImage.readFileByte? (0x1755c + index) with
  | none => simp [fin, readEq] at backed
  | some byte =>
      rw [loaded _ _ readEq]
      have arrayByte : sszDecodeCleanupTemplateBytes[index] = byte := by
        simp [sszDecodeCleanupTemplateBytes, readEq]
      rw [arrayByte]

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
sszDecodeZeroDwordSite(sszDecodeCleanupStore430; 0x12298, 0x430;
  0x23, 0x38, 0x01, 0x42)
sszDecodeZeroDwordSite(sszDecodeCleanupStore438; 0x1229c, 0x438;
  0x23, 0x3c, 0x01, 0x42)
sszDecodeZeroDwordSite(sszDecodeCleanupStore440; 0x122a0, 0x440;
  0x23, 0x30, 0x01, 0x44)
sszDecodeZeroDwordSite(sszDecodeCleanupStore448; 0x122a4, 0x448;
  0x23, 0x34, 0x01, 0x44)
sszDecodeZeroDwordSite(sszDecodeCleanupStore310; 0x122b8, 0x310;
  0x23, 0x38, 0x01, 0x30)
sszDecodeZeroDwordSite(sszDecodeCleanupStore318; 0x122bc, 0x318;
  0x23, 0x3c, 0x01, 0x30)
sszDecodeZeroDwordSite(sszDecodeCleanupStore320; 0x122c0, 0x320;
  0x23, 0x30, 0x01, 0x32)
sszDecodeZeroDwordSite(sszDecodeCleanupStore328; 0x122c4, 0x328;
  0x23, 0x34, 0x01, 0x32)
sszDecodeZeroDwordSite(sszDecodeCleanupStore2f0; 0x122c8, 0x2f0;
  0x23, 0x38, 0x01, 0x2e)
sszDecodeZeroDwordSite(sszDecodeCleanupStore2f8; 0x122cc, 0x2f8;
  0x23, 0x3c, 0x01, 0x2e)
sszDecodeZeroDwordSite(sszDecodeCleanupStore300; 0x122d0, 0x300;
  0x23, 0x30, 0x01, 0x30)
sszDecodeZeroDwordSite(sszDecodeCleanupStore308; 0x122d4, 0x308;
  0x23, 0x34, 0x01, 0x30)
sszDecodeZeroDwordSite(sszDecodeCleanupStore2d0; 0x122d8, 0x2d0;
  0x23, 0x38, 0x01, 0x2c)
sszDecodeZeroDwordSite(sszDecodeCleanupStore2d8; 0x122dc, 0x2d8;
  0x23, 0x3c, 0x01, 0x2c)
sszDecodeZeroDwordSite(sszDecodeCleanupStore2e0; 0x122e0, 0x2e0;
  0x23, 0x30, 0x01, 0x2e)
sszDecodeZeroDwordSite(sszDecodeCleanupStore2e8; 0x122e4, 0x2e8;
  0x23, 0x34, 0x01, 0x2e)

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

/-- Exact `0x122a8: addi a0,sp,816`. -/
private theorem sszDecodeCleanupDestinationStep (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x122a8)
    (atStack : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x122a8 retired x10
        (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330))) false := by
  let source := BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)
  let result := BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)
  have resultEq : result = iTypeResult .ADDI 0x330 source := by
    change BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330) =
      BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) + sign_extend (m := 64) (0x330#12)
    rw [show sign_extend (m := 64) (0x330#12) = 0x330#64 by native_decide,
      ← BitVec.ofNat_add]
  apply configuredITypeX10Step stepNo 0x122a8 state 0x330 (.Regidx 2#5) .ADDI
    source result 0x13 0x05 0x01 0x33 configured atPc loaded (base := by rfl)
  · exact resultEq
  · intro premise writes
    exact rX_x2_run premise source ((writes.get x2 (by decide)).trans atStack)
  · intro premise
    rw [← resultEq]
    exact wX_x10_run premise result
  · configured_decode configured

/-- Exact `0x122ac: li a2,256`. -/
private theorem sszDecodeCleanupSizeStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x122ac)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x122ac retired x12 256) false := by
  have resultEq : (256 : BitVec 64) = iTypeResult .ADDI 0x100 0 := by native_decide
  exact configuredITypeRegisterStep stepNo 0x122ac state 0x100 (.Regidx 0#5)
    (.Regidx 12#5) x12 .ADDI 0 256 0x13 0x06 0x00 0x10 configured atPc loaded
    (by intro premise _; exact rX_x0_run premise)
    (by intro premise; rw [← resultEq]; exact wX_x12_run premise 256)
    (by configured_decode configured) (by native_decide) (by rfl)
    (by decide) (by decide) (by decide) (by decide)

/-- Exact `0x122b0: auipc ra,0xffffe`. -/
private theorem sszDecodeCleanupCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x122b0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x122b0 retired x1 0x102b0) false := by
  simpa using configuredAuipcStep stepNo state 0x122b0 0xffffe
    0x97 0xe0 0xff 0xff configured atPc loaded
    (base := by rfl) (decode := by configured_decode configured)

/-- Exact `0x122b4: jalr -220(ra)`, entering the proved `memcpy`. -/
private theorem sszDecodeCleanupMemcpyCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x122b4)
    (baseAt : state.regs.get? x1 = some 0x102b0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x122b4 0x101d4 x1 0x122b8)
        0x101d4 retired) false := by
  exact configuredJalrCallStep stepNo state 0x122b4 0x102b0 0xf24 0x101d4 0x122b8
    0xe7 0x80 0x40 0xf2 configured atPc baseAt loaded
    (base := by rfl) (decode := by configured_decode configured)

/-- Exact `0x12308: li s6,1`, after cleanup initialization. -/
private theorem sszDecodeCleanupSuccessTagStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12308)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12308 retired x22 1) false := by
  have resultEq : (1 : BitVec 64) = iTypeResult .ADDI 1 0 := by native_decide
  exact configuredITypeRegisterStep stepNo 0x12308 state 1 (.Regidx 0#5)
    (.Regidx 22#5) x22 .ADDI 0 1 0x13 0x0b 0x10 0x00 configured atPc loaded
    (by intro premise _; exact rX_x0_run premise)
    (by intro premise; rw [← resultEq]; exact wX_x22_run premise 1)
    (by configured_decode configured) (by native_decide) (by rfl)
    (by decide) (by decide) (by decide) (by decide)

/-- Execute one result word store through the shared base-register store theorem. -/
theorem sszDecodeResultDwordStoreStep (stepNo pc offset : Nat) (imm : BitVec 12)
    (sourceIndex : regidx) (byte0 byte1 byte2 byte3 : UInt8)
    (args : DecodeInlineArgs) (state : State) (value : BitVec 64)
    (access : DecodeBoundaryMachineAccess args.boundary state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (resultAt : state.regs.get? x8 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)))
    (sourceRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits sourceIndex) premise premise value)
    (offsetBound : 0x20 + offset + 8 ≤ 0x380)
    (aligned : (args.boundary.stackPointer + 0x20 + offset) % 8 = 0)
    (fits : args.boundary.stackPointer + 0x20 + offset + 8 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 (args.boundary.stackPointer + 0x20) +
      sign_extend (m := 64) imm =
        BitVec.ofNat 64 (args.boundary.stackPointer + 0x20 + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (imm, sourceIndex, .Regidx 8#5, 8)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc))
          (args.boundary.stackPointer + 0x20 + offset) value)
        (BitVec.ofNat 64 pc) retired) false := by
  apply configuredBaseDwordStoreStep stepNo pc
    (args.boundary.stackPointer + 0x20) offset state value imm (.Regidx 8#5) sourceIndex
    byte0 byte1 byte2 byte3 access.configured atPc
    (by simpa [Nat.add_assoc] using access.callerStore (0x20 + offset) 8 offsetBound)
    (by simpa [LoadMMIOAddressExcluded, StoreMMIOAddressExcluded, Nat.add_assoc] using
      access.callerNoMMIO (0x20 + offset) 8 offsetBound)
    aligned fits loaded addressEq decode (site := site) (base := base)
  · intro premise writes
    exact rX_x8_run premise _ ((writes.get x8 (by decide)).trans resultAt)
  · exact sourceRun

/-- Declare one exact result word store from the shared base-register theorem. -/
macro "sszDecodeResultDwordSite(" name:ident ";" pc:term "," offset:term ";"
    sourceIndex:term "," sourceRegister:term "," sourceRun:term ";"
    byte0:term "," byte1:term "," byte2:term "," byte3:term ")" : command =>
  `(theorem $name (stepNo : Nat) (args : DecodeInlineArgs) (state : State)
      (value : BitVec 64) (access : DecodeBoundaryMachineAccess args.boundary state)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (resultAt : state.regs.get? x8 =
        some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)))
      (sourceAt : state.regs.get? $sourceRegister = some value)
      (stackAligned : args.boundary.stackPointer % 16 = 0)
      (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
      (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepStoreAfterRetired
          (afterWriteBytes (width := 8)
            (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 $pc))
            (args.boundary.stackPointer + 0x20 + $offset) value)
          (BitVec.ofNat 64 $pc) retired) false := by
      apply sszDecodeResultDwordStoreStep stepNo $pc $offset (BitVec.ofNat 12 $offset)
        $sourceIndex $byte0 $byte1 $byte2 $byte3 args state value access atPc resultAt
      · intro premise writes
        exact $sourceRun premise value ((writes.get $sourceRegister (by decide)).trans sourceAt)
      · omega
      · omega
      · omega
      · exact loaded
      · change BitVec.ofNat 64 (args.boundary.stackPointer + 0x20) +
          BitVec.ofNat 64 $offset = _
        rw [← BitVec.ofNat_add]
      · configured_store_decode access.configured
      · exact (by native_decide)
      · exact (by rfl))

sszDecodeResultDwordSite(sszDecodeResultStoreS1; 0x1230c, 0x00;
  (.Regidx 9#5), x9, rX_x9_run; 0x23, 0x30, 0x94, 0x00)
sszDecodeResultDwordSite(sszDecodeResultStoreS10; 0x12310, 0x08;
  (.Regidx 26#5), x26, rX_x26_run; 0x23, 0x34, 0xa4, 0x01)
sszDecodeResultDwordSite(sszDecodeResultStoreS4; 0x12314, 0x10;
  (.Regidx 20#5), x20, rX_x20_run; 0x23, 0x38, 0x44, 0x01)
sszDecodeResultDwordSite(sszDecodeResultStoreS3; 0x12318, 0x18;
  (.Regidx 19#5), x19, rX_x19_run; 0x23, 0x3c, 0x34, 0x01)
sszDecodeResultDwordSite(sszDecodeResultStoreA7; 0x1231c, 0x20;
  (.Regidx 17#5), x17, rX_x17_run; 0x23, 0x30, 0x14, 0x03)
sszDecodeResultDwordSite(sszDecodeResultStoreA6; 0x12320, 0x28;
  (.Regidx 16#5), x16, rX_x16_run; 0x23, 0x34, 0x04, 0x03)
sszDecodeResultDwordSite(sszDecodeResultStoreT6; 0x12324, 0x30;
  (.Regidx 31#5), x31, rX_x31_run; 0x23, 0x38, 0xf4, 0x03)
sszDecodeResultDwordSite(sszDecodeResultStoreT0; 0x12328, 0x38;
  (.Regidx 5#5), x5, rX_x5_run; 0x23, 0x3c, 0x54, 0x02)
sszDecodeResultDwordSite(sszDecodeResultStoreS7First; 0x1232c, 0x40;
  (.Regidx 23#5), x23, rX_x23_run; 0x23, 0x30, 0x74, 0x05)
sszDecodeResultDwordSite(sszDecodeResultStoreA5; 0x12330, 0x48;
  (.Regidx 15#5), x15, rX_x15_run; 0x23, 0x34, 0xf4, 0x04)
sszDecodeResultDwordSite(sszDecodeResultStoreS7Second; 0x12334, 0x50;
  (.Regidx 23#5), x23, rX_x23_run; 0x23, 0x38, 0x74, 0x05)
sszDecodeResultDwordSite(sszDecodeResultStoreRa; 0x12338, 0x58;
  (.Regidx 1#5), x1, rX_x1_run; 0x23, 0x3c, 0x14, 0x04)

def sszDecodeResultStoresOwnPc (pc : BitVec 64) : Prop :=
  0x1230c ≤ pc.toNat ∧ pc.toNat < 0x1233c

def sszDecodeResultStoresExitPc (pc : BitVec 64) : Prop := pc = 0x1233c

def sszDecodeResultStoresMemory (args : DecodeInlineArgs) : Region :=
  byteRange (args.boundary.stackPointer + 0x20) 0x60

theorem instructionPreserved_disjoint_stepBookkeeping :
    RegSet.Disjoint instructionPreserved stepBookkeeping := by
  intro register preserved bookkeeping
  exact platformPreserved_disjoint register preserved.1 bookkeeping

theorem sszDecodeResultStoresAccessOfSeg {args : DecodeInlineArgs} {before cur : State}
    {kv a n pc} (access : DecodeBoundaryMachineAccess args.boundary before)
    (seg : Seg sszDecodeResultStoresOwnPc sszDecodeResultStoresExitPc
      (fun _ _ _ _ _ => False) stepBookkeeping (sszDecodeResultStoresMemory args)
      kv a n before cur pc) :
    DecodeBoundaryMachineAccess args.boundary cur :=
  access.of_pma_regions_eq
    (seg.agree instructionPreserved_disjoint_stepBookkeeping) seg.retired
    (seg.get pma_regions (by simp [stepBookkeeping]))

theorem sszDecodeResultStoresCodeOfSeg {args : DecodeInlineArgs} {before cur : State}
    {kv a n pc} (access : DecodeBoundaryMachineAccess args.boundary before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg sszDecodeResultStoresOwnPc sszDecodeResultStoresExitPc
      (fun _ _ _ _ _ => False) stepBookkeeping (sszDecodeResultStoresMemory args)
      kv a n before cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  intro address byte fileByte
  rw [seg.mem address (by
    intro inside
    unfold sszDecodeResultStoresMemory byteRange at inside
    have outside := access.callerNotCode address (by omega) (by omega)
    rw [fileByte] at outside
    cases outside)]
  exact code address byte fileByte

theorem sszDecodeResultStoresAppend {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeResultStoresOwnPc
      sszDecodeResultStoresExitPc (fun _ _ _ _ _ => False) stepBookkeeping
      (sszDecodeResultStoresMemory args) kv a n before cur pc)
    (offset : Nat) (value : BitVec 64) (nextPc : BitVec 64)
    (offsetBound : offset + 8 ≤ 0x60)
    (inRegion : sszDecodeResultStoresOwnPc pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement cur) pc)
          (args.boundary.stackPointer + 0x20 + offset) value)
        pc retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (keep : RegsOutside stepBookkeeping kv) :
    ∃ next, Seg sszDecodeResultStoresOwnPc sszDecodeResultStoresExitPc
      (fun _ _ _ _ _ => False) stepBookkeeping (sszDecodeResultStoresMemory args)
      kv a (n + 1) before next nextPc := by
  apply seg.stepStore (args.boundary.stackPointer + 0x20 + offset) value nextPc inRegion
    (by intro atExit; unfold sszDecodeResultStoresExitPc at atExit; subst pc
        simp [sszDecodeResultStoresOwnPc] at inRegion)
    run advance
  · intro other lower upper
    unfold sszDecodeResultStoresMemory byteRange
    omega
  · intro register bookkeeping
    exact bookkeeping
  · exact keep

def sszDecodeCleanupOwnPc (pc : BitVec 64) : Prop :=
  0x1225c ≤ pc.toNat ∧ pc.toNat < 0x1230c

def sszDecodeCleanupExitPc (pc : BitVec 64) : Prop := pc = 0x101d4 ∨ pc = 0x1230c

def sszDecodeCleanupWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x1 ∨ register = x10 ∨ register = x11 ∨
    register = x12

/-- The post-`memcpy` tail writes only retirement registers and the final status register. -/
def sszDecodeCleanupTailWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x22

def sszDecodeCleanupMemory (args : DecodeInlineArgs) : Region :=
  byteRange (args.boundary.stackPointer - 0xbb0) 0xbb0

/-- The post-`memcpy` tail writes only below decoder-frame offset `0x330`. -/
def sszDecodeCleanupTailMemory (args : DecodeInlineArgs) : Region :=
  byteRange (args.boundary.stackPointer - 0xbb0) 0x330

theorem instructionPreserved_disjoint_sszDecodeCleanupWrites :
    RegSet.Disjoint instructionPreserved sszDecodeCleanupWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

theorem instructionPreserved_disjoint_sszDecodeCleanupTailWrites :
    RegSet.Disjoint instructionPreserved sszDecodeCleanupTailWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  · simp [instructionPreserved, platformPreserved] at preserved

theorem sszDecodeCleanupTailAccessOfSeg {args : DecodeInlineArgs} {before cur : State}
    {kv a n pc} (access : DecodeBoundaryMachineAccess args.boundary before)
    (seg : Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites (sszDecodeCleanupTailMemory args)
      kv a n before cur pc) :
    DecodeBoundaryMachineAccess args.boundary cur :=
  access.of_pma_regions_eq
    (seg.agree instructionPreserved_disjoint_sszDecodeCleanupTailWrites) seg.retired
    (seg.get pma_regions (by simp [sszDecodeCleanupTailWrites, stepBookkeeping]))

theorem sszDecodeCleanupTailCodeOfSeg {args : DecodeInlineArgs} {before cur : State}
    {kv a n pc} (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites (sszDecodeCleanupTailMemory args)
      kv a n before cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  intro address byte fileByte
  rw [seg.mem address (by
    intro inside
    unfold sszDecodeCleanupTailMemory byteRange at inside
    have lower : args.boundary.stackPointer - 0xbb0 ≤ address := inside.1
    have upper : address < args.boundary.stackPointer := by omega
    have outside := access.frameNotCode address lower upper
    rw [fileByte] at outside
    cases outside)]
  exact code address byte fileByte

theorem sszDecodeCleanupAccessOfSeg {args : DecodeInlineArgs} {before cur : State}
    {kv a n pc} (access : DecodeBoundaryMachineAccess args.boundary before)
    (seg : Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
      kv a n before cur pc) :
    DecodeBoundaryMachineAccess args.boundary cur :=
  access.of_pma_regions_eq
    (seg.agree instructionPreserved_disjoint_sszDecodeCleanupWrites) seg.retired
    (seg.get pma_regions (by simp [sszDecodeCleanupWrites, stepBookkeeping]))

theorem sszDecodeCleanupCodeOfSeg {args : DecodeInlineArgs} {before cur : State}
    {kv a n pc} (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
      kv a n before cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  intro address byte fileByte
  rw [seg.mem address (by
    intro inside
    unfold sszDecodeCleanupMemory byteRange at inside
    have lower : args.boundary.stackPointer - 0xbb0 ≤ address := inside.1
    have upper : address < args.boundary.stackPointer := by
      omega
    have outside := access.frameNotCode address lower upper
    rw [fileByte] at outside
    cases outside)]
  exact code address byte fileByte

private theorem sszDecodeCleanupAppendStore {width : Nat} {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupWrites
      (sszDecodeCleanupMemory args) kv a n before cur pc)
    (offset : Nat) (value : BitVec (8 * width)) (nextPc : BitVec 64)
    (offsetFits : offset + width ≤ 0xbb0)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (keep : RegsOutside stepBookkeeping kv)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc)
          (args.boundary.stackPointer - 0xbb0 + offset) value)
        (Sail.BitVec.addInt pc 4) retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc) :
    ∃ next, Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
      kv a (n + 1) before next nextPc :=
  seg.stepStore (args.boundary.stackPointer - 0xbb0 + offset) value nextPc
    inRegion (by
      intro atExit
      unfold sszDecodeCleanupExitPc at atExit
      rcases atExit with rfl | rfl <;> simp [sszDecodeCleanupOwnPc] at inRegion)
    run advance
    (by intro other lower upper; simp [sszDecodeCleanupMemory, byteRange]; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    keep

private def CleanupDwordReps (state : State) (words : List (Nat × Nat)) : Prop :=
  ∀ word ∈ words, UIntRep 8 state.mem word.1 word.2

private theorem cleanupDwordRepsOfMemEq {before after : State} {words : List (Nat × Nat)}
    (reps : CleanupDwordReps before words) (memory : after.mem = before.mem) :
    CleanupDwordReps after words := by
  intro word member
  exact (reps word member).of_mem_eq memory

private theorem sszDecodeCleanupAppendRegister {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupWrites
      (sszDecodeCleanupMemory args) kv a n before cur pc)
    (dest : Register) (value : RegisterType dest) (nextPc : BitVec 64)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (afterRegisterWrite cur pc retired dest value) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (destination : sszDecodeCleanupWrites dest)
    (destNotPc : dest ≠ PC) (destNotRetired : dest ≠ minstret)
    (keep : RegsOutside (RegSet.union stepBookkeeping (RegSet.only dest)) kv) :
    ∃ next, Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
      (⟨dest, value⟩ :: kv) a (n + 1) before next nextPc :=
  seg.step inRegion (by
      intro atExit
      unfold sszDecodeCleanupExitPc at atExit
      rcases atExit with rfl | rfl <;> simp [sszDecodeCleanupOwnPc] at inRegion)
    dest value nextPc run advance
    (by intro register bookkeeping; exact Or.inl bookkeeping) destination
    destNotPc destNotRetired keep

/-- Append one register-only step and preserve a list of cleanup dword representations. -/
private theorem sszDecodeCleanupAppendRegisterWithDwordReps {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupWrites
      (sszDecodeCleanupMemory args) kv a n before cur pc)
    (words : List (Nat × Nat)) (wordsRep : CleanupDwordReps cur words)
    (dest : Register) (value : RegisterType dest) (nextPc : BitVec 64)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (afterRegisterWrite cur pc retired dest value) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (destination : sszDecodeCleanupWrites dest)
    (destNotPc : dest ≠ PC) (destNotRetired : dest ≠ minstret)
    (keep : RegsOutside (RegSet.union stepBookkeeping (RegSet.only dest)) kv) :
    ∃ next,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        (⟨dest, value⟩ :: kv) a (n + 1) before next nextPc ∧
      CleanupDwordReps next words := by
  obtain ⟨retired, run⟩ := run
  let next := afterRegisterWrite cur pc retired dest value
  have nextSeg := seg.stepKnown inRegion (by
      intro atExit
      unfold sszDecodeCleanupExitPc at atExit
      rcases atExit with rfl | rfl <;> simp [sszDecodeCleanupOwnPc] at inRegion)
    dest value nextPc retired run advance
    (by intro register bookkeeping; exact Or.inl bookkeeping) destination
    destNotPc destNotRetired keep
  refine ⟨next, nextSeg, cleanupDwordRepsOfMemEq wordsRep ?_⟩
  exact afterRegisterWrite_mem cur pc retired dest value

private theorem sszDecodeCleanupAppendDwordSite {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupWrites
      (sszDecodeCleanupMemory args) kv a n before cur pc)
    (offset : Nat) (nextPc : BitVec 64) (offsetFits : offset + 8 ≤ 0xbb0)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (site : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement cur) pc)
          (args.boundary.stackPointer - 0xbb0 + offset) 0)
        pc retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (keep : RegsOutside stepBookkeeping kv) :
    ∃ next, Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
      kv a (n + 1) before next nextPc := by
  apply sszDecodeCleanupAppendStore seg offset (0 : BitVec 64) nextPc offsetFits inRegion keep
    site advance

/-- The cleanup fields that the result-construction loads read at `0x1233c..0x1235c`.
Each field is zero because the parent stores zero into it before the fixed-template `memcpy` call. -/
structure SszDecodeCleanupZeroSlots (args : DecodeInlineArgs) (state : State) : Prop where
  slot470 : UIntRep 8 state.mem (args.boundary.stackPointer - 0xbb0 + 0x470) 0
  slot478 : UIntRep 8 state.mem (args.boundary.stackPointer - 0xbb0 + 0x478) 0
  slot480 : UIntRep 4 state.mem (args.boundary.stackPointer - 0xbb0 + 0x480) 0
  slot488 : UIntRep 8 state.mem (args.boundary.stackPointer - 0xbb0 + 0x488) 0
  slot490 : UIntRep 8 state.mem (args.boundary.stackPointer - 0xbb0 + 0x490) 0
  slot498 : UIntRep 8 state.mem (args.boundary.stackPointer - 0xbb0 + 0x498) 0
  slot4a0 : UIntRep 8 state.mem (args.boundary.stackPointer - 0xbb0 + 0x4a0) 0
  slot4a8 : UIntRep 8 state.mem (args.boundary.stackPointer - 0xbb0 + 0x4a8) 0
  slot4b0 : UIntRep 8 state.mem (args.boundary.stackPointer - 0xbb0 + 0x4b0) 0

/-- Preserve all cleanup slots across an exact memory equality. -/
theorem SszDecodeCleanupZeroSlots.of_mem_eq {args : DecodeInlineArgs} {before after : State}
    (slots : SszDecodeCleanupZeroSlots args before) (memory : after.mem = before.mem) :
    SszDecodeCleanupZeroSlots args after :=
  { slot470 := slots.slot470.of_mem_eq memory
    slot478 := slots.slot478.of_mem_eq memory
    slot480 := slots.slot480.of_mem_eq memory
    slot488 := slots.slot488.of_mem_eq memory
    slot490 := slots.slot490.of_mem_eq memory
    slot498 := slots.slot498.of_mem_eq memory
    slot4a0 := slots.slot4a0.of_mem_eq memory
    slot4a8 := slots.slot4a8.of_mem_eq memory
    slot4b0 := slots.slot4b0.of_mem_eq memory }

/-- Preserve all nine cleanup fields across a memory frame that excludes their byte windows. -/
theorem SszDecodeCleanupZeroSlots.of_writesOnlyWithin {args : DecodeInlineArgs}
    {before after : State} {owned : Region} (slots : SszDecodeCleanupZeroSlots args before)
    (writes : WritesOnlyWithin owned before after)
    (outside : ∀ address width, (address, width) ∈
      [(0x470, 8), (0x478, 8), (0x480, 4), (0x488, 8), (0x490, 8),
       (0x498, 8), (0x4a0, 8), (0x4a8, 8), (0x4b0, 8)] →
      ∀ index, index < width →
        ¬ owned (args.boundary.stackPointer - 0xbb0 + address + index)) :
    SszDecodeCleanupZeroSlots args after := by
  constructor
  · exact slots.slot470.of_writesOnlyWithin writes (outside 0x470 8 (by simp) )
  · exact slots.slot478.of_writesOnlyWithin writes (outside 0x478 8 (by simp) )
  · exact slots.slot480.of_writesOnlyWithin writes (outside 0x480 4 (by simp) )
  · exact slots.slot488.of_writesOnlyWithin writes (outside 0x488 8 (by simp) )
  · exact slots.slot490.of_writesOnlyWithin writes (outside 0x490 8 (by simp) )
  · exact slots.slot498.of_writesOnlyWithin writes (outside 0x498 8 (by simp) )
  · exact slots.slot4a0.of_writesOnlyWithin writes (outside 0x4a0 8 (by simp) )
  · exact slots.slot4a8.of_writesOnlyWithin writes (outside 0x4a8 8 (by simp) )
  · exact slots.slot4b0.of_writesOnlyWithin writes (outside 0x4b0 8 (by simp) )

/-- Preserve the slots across writes that stay below the first slot at frame offset `0x470`. -/
theorem SszDecodeCleanupZeroSlots.of_lowerFrameWrites {args : DecodeInlineArgs}
    {before after : State} {owned : Region} (slots : SszDecodeCleanupZeroSlots args before)
    (writes : WritesOnlyWithin owned before after)
    (upper : ∀ address, owned address →
      address < args.boundary.stackPointer - 0xbb0 + 0x470) :
    SszDecodeCleanupZeroSlots args after :=
  slots.of_writesOnlyWithin writes (by
    intro address width member index indexBound inside
    have below := upper _ inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h <;> cases h <;> omega)

/-- Append one register-only step and preserve all nine cleanup slots. -/
private theorem sszDecodeCleanupAppendRegisterWithZeroSlots {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupWrites
      (sszDecodeCleanupMemory args) kv a n before cur pc)
    (slots : SszDecodeCleanupZeroSlots args cur)
    (dest : Register) (value : RegisterType dest) (nextPc : BitVec 64)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (afterRegisterWrite cur pc retired dest value) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (destination : sszDecodeCleanupWrites dest)
    (destNotPc : dest ≠ PC) (destNotRetired : dest ≠ minstret)
    (keep : RegsOutside (RegSet.union stepBookkeeping (RegSet.only dest)) kv) :
    ∃ next,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        (⟨dest, value⟩ :: kv) a (n + 1) before next nextPc ∧
      SszDecodeCleanupZeroSlots args next := by
  obtain ⟨retired, run⟩ := run
  let next := afterRegisterWrite cur pc retired dest value
  have nextSeg := seg.stepKnown inRegion (by
      intro atExit
      unfold sszDecodeCleanupExitPc at atExit
      rcases atExit with rfl | rfl <;> simp [sszDecodeCleanupOwnPc] at inRegion)
    dest value nextPc retired run advance
    (by intro register bookkeeping; exact Or.inl bookkeeping) destination
    destNotPc destNotRetired keep
  exact ⟨next, nextSeg, slots.of_mem_eq (afterRegisterWrite_mem cur pc retired dest value)⟩

/-- Append one exact zero dword store and retain all earlier disjoint dword representations. -/
private theorem sszDecodeCleanupAppendZeroDwordWitness {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupWrites
      (sszDecodeCleanupMemory args) kv a n before cur pc)
    (words : List (Nat × Nat)) (wordsRep : CleanupDwordReps cur words)
    (offset : Nat) (nextPc : BitVec 64) (offsetFits : offset + 8 ≤ 0xbb0)
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (site : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement cur) pc)
          (args.boundary.stackPointer - 0xbb0 + offset) 0)
        pc retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (keep : RegsOutside stepBookkeeping kv)
    (disjoint : ∀ word, word ∈ words →
      word.1 + 8 ≤ args.boundary.stackPointer - 0xbb0 + offset ∨
      args.boundary.stackPointer - 0xbb0 + offset + 8 ≤ word.1) :
    ∃ next, Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        kv a (n + 1) before next nextPc ∧
      CleanupDwordReps next
        ((args.boundary.stackPointer - 0xbb0 + offset, 0) :: words) := by
  obtain ⟨retired, next, nextEq, nextSeg⟩ := seg.stepStoreWitness
    (width := 8) (args.boundary.stackPointer - 0xbb0 + offset) 0 nextPc inRegion
    (by
      intro atExit
      unfold sszDecodeCleanupExitPc at atExit
      rcases atExit with rfl | rfl <;> simp [sszDecodeCleanupOwnPc] at inRegion)
    site advance
    (by intro other lower upper; simp [sszDecodeCleanupMemory, byteRange]; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping) keep
  have stepWrites : WritesOnlyWithin
      (byteRange (args.boundary.stackPointer - 0xbb0 + offset) 8) cur next := by
    intro address outside
    rw [nextEq]
    exact storeRetirement_mem_writes cur pc (Sail.BitVec.addInt pc 4) retired
      (args.boundary.stackPointer - 0xbb0 + offset) 0 address outside
  have oldReps : CleanupDwordReps next words := by
    intro word member
    exact (wordsRep word member).of_writesOnlyWithin stepWrites (by
      intro index indexBound inside
      unfold byteRange at inside
      rcases disjoint word member with below | above <;> omega)
  have currentRep : UIntRep 8 next.mem
      (args.boundary.stackPointer - 0xbb0 + offset) 0 := by
    rw [nextEq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement cur) pc)
        (args.boundary.stackPointer - 0xbb0 + offset) 0 (by omega) (by omega)
  exact ⟨next, nextSeg, by
    intro word member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact currentRep
    · exact oldReps word member⟩

/-- Append the exact zero word store and retain all disjoint zero dwords. -/
private theorem sszDecodeCleanupAppendZeroWordWitness {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupWrites
      (sszDecodeCleanupMemory args) kv a n before cur pc)
    (words : List (Nat × Nat)) (wordsRep : CleanupDwordReps cur words)
    (offset : Nat) (nextPc : BitVec 64) (offsetFits : offset + 4 ≤ 0xbb0)
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (site : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 4)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc)
          (args.boundary.stackPointer - 0xbb0 + offset) 0)
        (Sail.BitVec.addInt pc 4) retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (keep : RegsOutside stepBookkeeping kv)
    (disjoint : ∀ word, word ∈ words →
      word.1 + 8 ≤ args.boundary.stackPointer - 0xbb0 + offset ∨
      args.boundary.stackPointer - 0xbb0 + offset + 4 ≤ word.1) :
    ∃ next,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        kv a (n + 1) before next nextPc ∧
      CleanupDwordReps next words ∧
      UIntRep 4 next.mem (args.boundary.stackPointer - 0xbb0 + offset) 0 := by
  obtain ⟨retired, next, nextEq, nextSeg⟩ := seg.stepStoreWitness
    (width := 4) (args.boundary.stackPointer - 0xbb0 + offset) 0 nextPc inRegion
    (by
      intro atExit
      unfold sszDecodeCleanupExitPc at atExit
      rcases atExit with rfl | rfl <;> simp [sszDecodeCleanupOwnPc] at inRegion)
    site advance
    (by intro other lower upper; simp [sszDecodeCleanupMemory, byteRange]; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping) keep
  have stepWrites : WritesOnlyWithin
      (byteRange (args.boundary.stackPointer - 0xbb0 + offset) 4) cur next := by
    intro address outside
    rw [nextEq]
    exact storeRetirement_mem_writes cur pc (Sail.BitVec.addInt pc 4) retired
      (args.boundary.stackPointer - 0xbb0 + offset) 0 address outside
  have oldReps : CleanupDwordReps next words := by
    intro word member
    exact (wordsRep word member).of_writesOnlyWithin stepWrites (by
      intro index indexBound inside
      unfold byteRange at inside
      rcases disjoint word member with below | above <;> omega)
  have currentRep : UIntRep 4 next.mem
      (args.boundary.stackPointer - 0xbb0 + offset) 0 := by
    rw [nextEq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_four
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc)
        (args.boundary.stackPointer - 0xbb0 + offset) 0 (by omega) (by omega)
  exact ⟨next, nextSeg, oldReps, currentRep⟩

/-- Append a lower-frame zero dword store and preserve all nine result-source slots. -/
private theorem sszDecodeCleanupAppendLowerDwordWithZeroSlots {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupWrites
      (sszDecodeCleanupMemory args) kv a n before cur pc)
    (slots : SszDecodeCleanupZeroSlots args cur)
    (offset : Nat) (nextPc : BitVec 64) (belowSlots : offset + 8 ≤ 0x470)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (site : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement cur) pc)
          (args.boundary.stackPointer - 0xbb0 + offset) 0)
        pc retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (keep : RegsOutside stepBookkeeping kv) :
    ∃ next,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        kv a (n + 1) before next nextPc ∧
      SszDecodeCleanupZeroSlots args next := by
  obtain ⟨retired, next, nextEq, nextSeg⟩ := seg.stepStoreWitness
    (width := 8) (args.boundary.stackPointer - 0xbb0 + offset) 0 nextPc inRegion
    (by
      intro atExit
      unfold sszDecodeCleanupExitPc at atExit
      rcases atExit with rfl | rfl <;> simp [sszDecodeCleanupOwnPc] at inRegion)
    site advance
    (by intro other lower upper; simp [sszDecodeCleanupMemory, byteRange]; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping) keep
  have stepWrites : WritesOnlyWithin
      (byteRange (args.boundary.stackPointer - 0xbb0 + offset) 8) cur next := by
    intro address outside
    rw [nextEq]
    exact storeRetirement_mem_writes cur pc (Sail.BitVec.addInt pc 4) retired
      (args.boundary.stackPointer - 0xbb0 + offset) 0 address outside
  exact ⟨next, nextSeg, slots.of_lowerFrameWrites stepWrites (by
    intro address inside
    unfold byteRange at inside
    omega)⟩

private theorem sszDecodeCleanupTailAppendStore {width : Nat} {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites
      (sszDecodeCleanupTailMemory args) kv a n before cur pc)
    (offset : Nat) (value : BitVec (8 * width)) (nextPc : BitVec 64)
    (offsetFits : offset + width ≤ 0x330)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (keep : RegsOutside stepBookkeeping kv)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc)
          (args.boundary.stackPointer - 0xbb0 + offset) value)
        (Sail.BitVec.addInt pc 4) retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc) :
    ∃ next, Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites (sszDecodeCleanupTailMemory args)
      kv a (n + 1) before next nextPc :=
  seg.stepStore (args.boundary.stackPointer - 0xbb0 + offset) value nextPc
    inRegion (by
      intro atExit
      unfold sszDecodeCleanupExitPc at atExit
      rcases atExit with rfl | rfl <;> simp [sszDecodeCleanupOwnPc] at inRegion)
    run advance
    (by intro other lower upper; simp [sszDecodeCleanupTailMemory, byteRange]; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    keep

private theorem sszDecodeCleanupTailAppendDwordSite {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites
      (sszDecodeCleanupTailMemory args) kv a n before cur pc)
    (offset : Nat) (nextPc : BitVec 64) (offsetFits : offset + 8 ≤ 0x330)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (site : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement cur) pc)
          (args.boundary.stackPointer - 0xbb0 + offset) 0)
        pc retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (keep : RegsOutside stepBookkeeping kv) :
    ∃ next, Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites (sszDecodeCleanupTailMemory args)
      kv a (n + 1) before next nextPc := by
  apply sszDecodeCleanupTailAppendStore seg offset (0 : BitVec 64) nextPc offsetFits inRegion
    keep site advance

private theorem sszDecodeCleanupTailAppendRegister {args : DecodeInlineArgs}
    {before cur : State} {kv a n pc} (seg : Seg sszDecodeCleanupOwnPc
      sszDecodeCleanupExitPc (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites
      (sszDecodeCleanupTailMemory args) kv a n before cur pc)
    (dest : Register) (value : RegisterType dest) (nextPc : BitVec 64)
    (inRegion : sszDecodeCleanupOwnPc pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (afterRegisterWrite cur pc retired dest value) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (destination : sszDecodeCleanupTailWrites dest)
    (destNotPc : dest ≠ PC) (destNotRetired : dest ≠ minstret)
    (keep : RegsOutside (RegSet.union stepBookkeeping (RegSet.only dest)) kv) :
    ∃ next, Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites (sszDecodeCleanupTailMemory args)
      (⟨dest, value⟩ :: kv) a (n + 1) before next nextPc :=
  seg.step inRegion (by
      intro atExit
      unfold sszDecodeCleanupExitPc at atExit
      rcases atExit with rfl | rfl <;> simp [sszDecodeCleanupOwnPc] at inRegion)
    dest value nextPc run advance
    (by intro register bookkeeping; exact Or.inl bookkeeping) destination
    destNotPc destNotRetired keep

/-- The first two cleanup stores reach the AUIPC setup instruction and expose both zero words. -/
private theorem sszDecodeCleanupFirstStoresWithZeroDwords (fromStep : Nat)
    (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [] fromStep 2 before after 0x12264 ∧
      CleanupDwordReps after
        [(args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
         (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
    (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
    fromStep ⟨retired, retiredRead⟩ atPc
  have run1 := sszDecodeCleanupStore4a8 (fromStep + 0) args before stackFits
    stackAligned stackUpper (sszDecodeCleanupAccessOfSeg access seg0) seg0.atPc
    ((seg0.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg0)
  obtain ⟨state1, seg1, reps1⟩ := sszDecodeCleanupAppendZeroDwordWitness seg0 []
    (by simp [CleanupDwordReps]) 0x4a8 0x12260 (by omega) stackFits stackUpper
    (by simp [sszDecodeCleanupOwnPc]) run1 (by native_decide) (by simp [RegsOutside])
    (by simp)
  have run2 := sszDecodeCleanupStore4b0 (fromStep + 1) args state1 stackFits
    stackAligned stackUpper (sszDecodeCleanupAccessOfSeg access seg1) seg1.atPc
    ((seg1.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg1)
  obtain ⟨state2, seg2, reps2⟩ := sszDecodeCleanupAppendZeroDwordWitness seg1
    [(args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] reps1 0x4b0 0x12264
    (by omega) stackFits stackUpper (by simp [sszDecodeCleanupOwnPc]) run2
    (by native_decide) (by simp [RegsOutside]) (by
      intro word member
      simp only [List.mem_singleton] at member
      subst word
      omega)
  exact ⟨state2, by simpa only [Nat.add_assoc] using seg2, reps2⟩

/-- The first two cleanup stores reach the AUIPC setup instruction. -/
theorem sszDecodeCleanupFirstStores (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [] fromStep 2 before after 0x12264 := by
  obtain ⟨after, seg, _reps⟩ := sszDecodeCleanupFirstStoresWithZeroDwords fromStep args
    before atPc atStack stackFits stackAligned stackUpper access configured code
  exact ⟨after, seg⟩

/-- The first cleanup register write preserves both initial zero-word representations. -/
private theorem sszDecodeCleanupBaseHighWithZeroDwords (fromStep : Nat)
    (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x10, 0x17264⟩] fromStep 3 before after 0x12268 ∧
      CleanupDwordReps after
        [(args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
         (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] := by
  obtain ⟨state2, seg2, reps2⟩ := sszDecodeCleanupFirstStoresWithZeroDwords fromStep args
    before atPc atStack stackFits stackAligned stackUpper access configured code
  have run3 := sszDecodeCleanupBaseHighStep (fromStep + 2) state2
    (sszDecodeCleanupAccessOfSeg access seg2).configured seg2.atPc
    (sszDecodeCleanupCodeOfSeg stackFits access code seg2)
  obtain ⟨state3, seg3, reps3⟩ := sszDecodeCleanupAppendRegisterWithDwordReps seg2
    [(args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] reps2 x10 0x17264 0x12268
    (by simp [sszDecodeCleanupOwnPc]) run3 (by native_decide)
    (by simp [sszDecodeCleanupWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  exact ⟨state3, by simpa only [Nat.add_assoc] using seg3, reps3⟩

/-- The first cleanup register write follows the two initial stores without exposing a state term. -/
theorem sszDecodeCleanupBaseHighAfterFirstStores (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x10, 0x17264⟩] fromStep 3 before after 0x12268 := by
  obtain ⟨after, seg, _reps⟩ := sszDecodeCleanupBaseHighWithZeroDwords fromStep args
    before atPc atStack stackFits stackAligned stackUpper access configured code
  exact ⟨after, seg⟩

/-- The first descriptor group adds four zero dwords to the two initial zero words. -/
private theorem sszDecodeCleanupFirstDescriptorGroupWithZeroDwords (fromStep : Nat)
    (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x10, 0x17264⟩] fromStep 7 before after 0x12278 ∧
      CleanupDwordReps after
        [(args.boundary.stackPointer - 0xbb0 + 0x4a0, 0),
         (args.boundary.stackPointer - 0xbb0 + 0x498, 0),
         (args.boundary.stackPointer - 0xbb0 + 0x490, 0),
         (args.boundary.stackPointer - 0xbb0 + 0x488, 0),
         (args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
         (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] := by
  obtain ⟨state3, seg3, reps3⟩ := sszDecodeCleanupBaseHighWithZeroDwords fromStep args
    before atPc atStack stackFits stackAligned stackUpper access configured code
  have run4 := sszDecodeCleanupStore488 (fromStep + 3) args state3 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg3) seg3.atPc
    ((seg3.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg3)
  obtain ⟨state4, seg4, reps4⟩ := sszDecodeCleanupAppendZeroDwordWitness seg3
    [(args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] reps3 0x488 0x1226c
    (by omega) stackFits stackUpper (by simp [sszDecodeCleanupOwnPc]) run4
    (by native_decide) (by simp [RegsOutside, stepBookkeeping]) (by
      intro word member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> omega)
  have run5 := sszDecodeCleanupStore490 (fromStep + 4) args state4 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg4) seg4.atPc
    ((seg4.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg4)
  obtain ⟨state5, seg5, reps5⟩ := sszDecodeCleanupAppendZeroDwordWitness seg4
    [(args.boundary.stackPointer - 0xbb0 + 0x488, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] reps4 0x490 0x12270
    (by omega) stackFits stackUpper (by simp [sszDecodeCleanupOwnPc]) run5
    (by native_decide) (by simp [RegsOutside, stepBookkeeping]) (by
      intro word member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> omega)
  have run6 := sszDecodeCleanupStore498 (fromStep + 5) args state5 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg5) seg5.atPc
    ((seg5.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg5)
  obtain ⟨state6, seg6, reps6⟩ := sszDecodeCleanupAppendZeroDwordWitness seg5
    [(args.boundary.stackPointer - 0xbb0 + 0x490, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x488, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] reps5 0x498 0x12274
    (by omega) stackFits stackUpper (by simp [sszDecodeCleanupOwnPc]) run6
    (by native_decide) (by simp [RegsOutside, stepBookkeeping]) (by
      intro word member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> omega)
  have run7 := sszDecodeCleanupStore4a0 (fromStep + 6) args state6 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg6) seg6.atPc
    ((seg6.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg6)
  obtain ⟨state7, seg7, reps7⟩ := sszDecodeCleanupAppendZeroDwordWitness seg6
    [(args.boundary.stackPointer - 0xbb0 + 0x498, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x490, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x488, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] reps6 0x4a0 0x12278
    (by omega) stackFits stackUpper (by simp [sszDecodeCleanupOwnPc]) run7
    (by native_decide) (by simp [RegsOutside, stepBookkeeping]) (by
      intro word member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> omega)
  exact ⟨state7, by simpa only [Nat.add_assoc] using seg7, reps7⟩

/-- The first cleanup descriptor group reaches `0x12278` through one shared store append. -/
theorem sszDecodeCleanupFirstDescriptorGroup (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x10, 0x17264⟩] fromStep 7 before after 0x12278 := by
  obtain ⟨after, seg, _reps⟩ :=
    sszDecodeCleanupFirstDescriptorGroupWithZeroDwords fromStep args before atPc atStack
      stackFits stackAligned stackUpper access configured code
  exact ⟨after, seg⟩

/-- All nine later load sources are zero after the store at `0x12280`. -/
private theorem sszDecodeCleanupZeroSlotsAt12284 (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x10, 0x17264⟩] fromStep 10 before after 0x12284 ∧
      SszDecodeCleanupZeroSlots args after := by
  obtain ⟨state7, seg7, reps7⟩ :=
    sszDecodeCleanupFirstDescriptorGroupWithZeroDwords fromStep args before atPc atStack
      stackFits stackAligned stackUpper access configured code
  have run8 := sszDecodeCleanupStore470 (fromStep + 7) args state7 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg7) seg7.atPc
    ((seg7.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg7)
  obtain ⟨state8, seg8, reps8⟩ := sszDecodeCleanupAppendZeroDwordWitness seg7
    [(args.boundary.stackPointer - 0xbb0 + 0x4a0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x498, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x490, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x488, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] reps7 0x470 0x1227c
    (by omega) stackFits stackUpper (by simp [sszDecodeCleanupOwnPc]) run8
    (by native_decide) (by simp [RegsOutside, stepBookkeeping]) (by
      intro word member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  have run9 := sszDecodeCleanupStore478 (fromStep + 8) args state8 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg8) seg8.atPc
    ((seg8.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg8)
  obtain ⟨state9, seg9, reps9⟩ := sszDecodeCleanupAppendZeroDwordWitness seg8
    [(args.boundary.stackPointer - 0xbb0 + 0x470, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4a0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x498, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x490, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x488, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] reps8 0x478 0x12280
    (by omega) stackFits stackUpper (by simp [sszDecodeCleanupOwnPc]) run9
    (by native_decide) (by simp [RegsOutside, stepBookkeeping]) (by
      intro word member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  have run10 := sszDecodeCleanupWord480 (fromStep + 9) args state9 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg9) seg9.atPc
    ((seg9.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg9)
  obtain ⟨state10, seg10, reps10, word480⟩ := sszDecodeCleanupAppendZeroWordWitness seg9
    [(args.boundary.stackPointer - 0xbb0 + 0x478, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x470, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4a0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x498, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x490, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x488, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4b0, 0),
     (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0)] reps9 0x480 0x12284
    (by omega) stackFits stackUpper (by simp [sszDecodeCleanupOwnPc]) run10
    (by native_decide) (by simp [RegsOutside, stepBookkeeping]) (by
      intro word member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  refine ⟨state10, by simpa only [Nat.add_assoc] using seg10, ?_⟩
  exact
    { slot470 := reps10 (args.boundary.stackPointer - 0xbb0 + 0x470, 0) (by simp)
      slot478 := reps10 (args.boundary.stackPointer - 0xbb0 + 0x478, 0) (by simp)
      slot480 := word480
      slot488 := reps10 (args.boundary.stackPointer - 0xbb0 + 0x488, 0) (by simp)
      slot490 := reps10 (args.boundary.stackPointer - 0xbb0 + 0x490, 0) (by simp)
      slot498 := reps10 (args.boundary.stackPointer - 0xbb0 + 0x498, 0) (by simp)
      slot4a0 := reps10 (args.boundary.stackPointer - 0xbb0 + 0x4a0, 0) (by simp)
      slot4a8 := reps10 (args.boundary.stackPointer - 0xbb0 + 0x4a8, 0) (by simp)
      slot4b0 := reps10 (args.boundary.stackPointer - 0xbb0 + 0x4b0, 0) (by simp) }

/-- The four lower descriptor stores preserve all nine result-source slots through `0x12294`. -/
private theorem sszDecodeCleanupBeforeBaseLowWithZeroSlots (fromStep : Nat)
    (args : DecodeInlineArgs) (before : State)
    (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x10, 0x17264⟩] fromStep 14 before after 0x12294 ∧
      SszDecodeCleanupZeroSlots args after := by
  obtain ⟨state10, seg10, slots10⟩ := sszDecodeCleanupZeroSlotsAt12284 fromStep args
    before atPc atStack stackFits stackAligned stackUpper access configured code
  have run11 := sszDecodeCleanupStore450 (fromStep + 10) args state10 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg10) seg10.atPc
    ((seg10.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg10)
  obtain ⟨state11, seg11, slots11⟩ := sszDecodeCleanupAppendLowerDwordWithZeroSlots
    seg10 slots10 0x450 0x12288 (by omega) (by simp [sszDecodeCleanupOwnPc]) run11
    (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have run12 := sszDecodeCleanupStore458 (fromStep + 11) args state11 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg11) seg11.atPc
    ((seg11.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg11)
  obtain ⟨state12, seg12, slots12⟩ := sszDecodeCleanupAppendLowerDwordWithZeroSlots
    seg11 slots11 0x458 0x1228c (by omega) (by simp [sszDecodeCleanupOwnPc]) run12
    (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have run13 := sszDecodeCleanupStore460 (fromStep + 12) args state12 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg12) seg12.atPc
    ((seg12.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg12)
  obtain ⟨state13, seg13, slots13⟩ := sszDecodeCleanupAppendLowerDwordWithZeroSlots
    seg12 slots12 0x460 0x12290 (by omega) (by simp [sszDecodeCleanupOwnPc]) run13
    (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have run14 := sszDecodeCleanupStore468 (fromStep + 13) args state13 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg13) seg13.atPc
    ((seg13.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg13)
  obtain ⟨state14, seg14, slots14⟩ := sszDecodeCleanupAppendLowerDwordWithZeroSlots
    seg13 slots13 0x468 0x12294 (by omega) (by simp [sszDecodeCleanupOwnPc]) run14
    (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  exact ⟨state14, by simpa only [Nat.add_assoc] using seg14, slots14⟩

/-- All cleanup stores before the template-address low immediate reach `0x12294`. -/
theorem sszDecodeCleanupBeforeBaseLow (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x10, 0x17264⟩] fromStep 14 before after 0x12294 := by
  obtain ⟨after, seg, _slots⟩ := sszDecodeCleanupBeforeBaseLowWithZeroSlots
    fromStep args before atPc atStack stackFits stackAligned stackUpper access configured code
  exact ⟨after, seg⟩

/-- The template address and its final descriptor stores preserve all nine cleanup slots. -/
private theorem sszDecodeCleanupBeforeDestinationWithZeroSlots (fromStep : Nat)
    (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x11, 0x1755c⟩, ⟨x10, 0x17264⟩] fromStep 19 before after 0x122a8 ∧
      SszDecodeCleanupZeroSlots args after := by
  obtain ⟨state14, seg14, slots14⟩ := sszDecodeCleanupBeforeBaseLowWithZeroSlots
    fromStep args before atPc atStack stackFits stackAligned stackUpper access configured code
  have run15 := sszDecodeCleanupBaseLowStep (fromStep + 14) state14
    (sszDecodeCleanupAccessOfSeg access seg14).configured seg14.atPc
    (seg14.reg x10 0x17264 (by simp))
    (sszDecodeCleanupCodeOfSeg stackFits access code seg14)
  obtain ⟨state15, seg15, slots15⟩ := sszDecodeCleanupAppendRegisterWithZeroSlots
    seg14 slots14 x11 0x1755c 0x12298
    (by simp [sszDecodeCleanupOwnPc]) run15 (by native_decide)
    (by simp [sszDecodeCleanupWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have run16 := sszDecodeCleanupStore430 (fromStep + 15) args state15 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg15) seg15.atPc
    ((seg15.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg15)
  obtain ⟨state16, seg16, slots16⟩ := sszDecodeCleanupAppendLowerDwordWithZeroSlots
    seg15 slots15 0x430 0x1229c (by omega) (by simp [sszDecodeCleanupOwnPc]) run16
    (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have run17 := sszDecodeCleanupStore438 (fromStep + 16) args state16 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg16) seg16.atPc
    ((seg16.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg16)
  obtain ⟨state17, seg17, slots17⟩ := sszDecodeCleanupAppendLowerDwordWithZeroSlots
    seg16 slots16 0x438 0x122a0 (by omega) (by simp [sszDecodeCleanupOwnPc]) run17
    (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have run18 := sszDecodeCleanupStore440 (fromStep + 17) args state17 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg17) seg17.atPc
    ((seg17.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg17)
  obtain ⟨state18, seg18, slots18⟩ := sszDecodeCleanupAppendLowerDwordWithZeroSlots
    seg17 slots17 0x440 0x122a4 (by omega) (by simp [sszDecodeCleanupOwnPc]) run18
    (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have run19 := sszDecodeCleanupStore448 (fromStep + 18) args state18 stackFits stackAligned
    stackUpper (sszDecodeCleanupAccessOfSeg access seg18) seg18.atPc
    ((seg18.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg18)
  obtain ⟨state19, seg19, slots19⟩ := sszDecodeCleanupAppendLowerDwordWithZeroSlots
    seg18 slots18 0x448 0x122a8 (by omega) (by simp [sszDecodeCleanupOwnPc]) run19
    (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  exact ⟨state19, by simpa only [Nat.add_assoc] using seg19, slots19⟩

/-- The template address and its final empty descriptor group reach the memcpy destination setup. -/
theorem sszDecodeCleanupBeforeDestination (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x11, 0x1755c⟩, ⟨x10, 0x17264⟩] fromStep 19 before after 0x122a8 := by
  obtain ⟨after, seg, _slots⟩ := sszDecodeCleanupBeforeDestinationWithZeroSlots
    fromStep args before atPc atStack stackFits stackAligned stackUpper access configured code
  exact ⟨after, seg⟩

/-- The complete parent-owned setup reaches `memcpy` while preserving all cleanup slots. -/
theorem sszDecodeCleanupMemcpyCallReadyWithZeroSlots (fromStep : Nat)
    (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x1, 0x102b0⟩, ⟨x12, 256⟩,
          ⟨x10, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)⟩,
          ⟨x11, 0x1755c⟩]
        fromStep 22 before after 0x122b4 ∧
      SszDecodeCleanupZeroSlots args after := by
  obtain ⟨state19, seg19, slots19⟩ := sszDecodeCleanupBeforeDestinationWithZeroSlots
    fromStep args before atPc atStack stackFits stackAligned stackUpper access configured code
  have seg19' := seg19.forget (kv' := [⟨x11, 0x1755c⟩]) (by simp)
  have run20 := sszDecodeCleanupDestinationStep (fromStep + 19) args state19
    (sszDecodeCleanupAccessOfSeg access seg19').configured seg19'.atPc
    ((seg19'.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupCodeOfSeg stackFits access code seg19')
  obtain ⟨state20, seg20, slots20⟩ := sszDecodeCleanupAppendRegisterWithZeroSlots
    seg19' slots19 x10
    (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)) 0x122ac
    (by simp [sszDecodeCleanupOwnPc]) run20 (by native_decide)
    (by simp [sszDecodeCleanupWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have run21 := sszDecodeCleanupSizeStep (fromStep + 20) state20
    (sszDecodeCleanupAccessOfSeg access seg20).configured seg20.atPc
    (sszDecodeCleanupCodeOfSeg stackFits access code seg20)
  obtain ⟨state21, seg21, slots21⟩ := sszDecodeCleanupAppendRegisterWithZeroSlots
    seg20 slots20 x12 256 0x122b0
    (by simp [sszDecodeCleanupOwnPc]) run21 (by native_decide)
    (by simp [sszDecodeCleanupWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have run22 := sszDecodeCleanupCallBaseStep (fromStep + 21) state21
    (sszDecodeCleanupAccessOfSeg access seg21).configured seg21.atPc
    (sszDecodeCleanupCodeOfSeg stackFits access code seg21)
  obtain ⟨state22, seg22, slots22⟩ := sszDecodeCleanupAppendRegisterWithZeroSlots
    seg21 slots21 x1 0x102b0 0x122b4
    (by simp [sszDecodeCleanupOwnPc]) run22 (by native_decide)
    (by simp [sszDecodeCleanupWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  exact ⟨state22, by simpa only [Nat.add_assoc] using seg22, slots22⟩

/-- The complete parent-owned setup reaches the exact `memcpy` call instruction. -/
theorem sszDecodeCleanupMemcpyCallReady (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x1225c)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x1, 0x102b0⟩, ⟨x12, 256⟩,
          ⟨x10, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)⟩,
          ⟨x11, 0x1755c⟩]
        fromStep 22 before after 0x122b4 := by
  obtain ⟨after, seg, _slots⟩ := sszDecodeCleanupMemcpyCallReadyWithZeroSlots
    fromStep args before atPc atStack stackFits stackAligned stackUpper access configured code
  exact ⟨after, seg⟩

/-- Execute the exact cleanup call from the opaque pre-call `Seg`. -/
theorem sszDecodeCleanupMemcpyCallRun {args : DecodeInlineArgs} {before callReady : State}
    {fromStep : Nat}
    (seg : Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
      [⟨x1, 0x102b0⟩, ⟨x12, 256⟩,
        ⟨x10, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)⟩,
        ⟨x11, 0x1755c⟩]
      fromStep 22 before callReady 0x122b4)
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ retired, Runs (try_step (fromStep + 22) false) callReady
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement callReady) 0x122b4 0x101d4 x1 0x122b8)
        0x101d4 retired) false :=
  sszDecodeCleanupMemcpyCallStep (fromStep + 22) callReady
    (sszDecodeCleanupAccessOfSeg access seg).configured seg.atPc
    (seg.reg x1 0x102b0 (by simp))
    (sszDecodeCleanupCodeOfSeg stackFits access code seg)

/-- The configured-machine facts survive the cleanup direct-call retirement. -/
theorem configuredAfterSszDecodeCleanupCall (state : State) (retired : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    ConfiguredMachinePre EndpointMachinePc
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x122b4 0x101d4 x1 0x122b8)
        0x101d4 retired) := by
  apply configured.mono
  · simpa [callLinkState] using
      (callRetirement_writes state 0x122b4 0x101d4 retired x1 0x122b8).agree
        (by
          intro register preserved written
          rcases written with bookkeeping | rfl
          · exact platformPreserved_disjoint register preserved.1 bookkeeping
          · exact preserved.2 rfl)
  · simpa using tryStepControlFlowAfterRetired_retired_present
      (callLinkState (tryStepControlFlowAfterIncrement state) 0x122b4 0x101d4 x1 0x122b8)
      0x101d4 retired

/-- The twelve post-`memcpy` dword stores reach the narrow cleanup fields at `0x122e8`. -/
theorem sszDecodeCleanupAfterMemcpyDwords (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x122b8)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites (sszDecodeCleanupTailMemory args)
        [] fromStep 12 before after 0x122e8 := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
    (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites (sszDecodeCleanupTailMemory args)
    fromStep ⟨retired, retiredRead⟩ atPc
  have run1 := sszDecodeCleanupStore310 (fromStep + 0) args before stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg0) seg0.atPc
    ((seg0.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg0)
  obtain ⟨state1, seg1⟩ := sszDecodeCleanupTailAppendDwordSite seg0 0x310 0x122bc
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run1 (by native_decide)
    (by simp [RegsOutside])
  have run2 := sszDecodeCleanupStore318 (fromStep + 1) args state1 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg1) seg1.atPc
    ((seg1.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg1)
  obtain ⟨state2, seg2⟩ := sszDecodeCleanupTailAppendDwordSite seg1 0x318 0x122c0
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run2 (by native_decide)
    (by simp [RegsOutside])
  have run3 := sszDecodeCleanupStore320 (fromStep + 2) args state2 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg2) seg2.atPc
    ((seg2.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg2)
  obtain ⟨state3, seg3⟩ := sszDecodeCleanupTailAppendDwordSite seg2 0x320 0x122c4
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run3 (by native_decide)
    (by simp [RegsOutside])
  have run4 := sszDecodeCleanupStore328 (fromStep + 3) args state3 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg3) seg3.atPc
    ((seg3.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg3)
  obtain ⟨state4, seg4⟩ := sszDecodeCleanupTailAppendDwordSite seg3 0x328 0x122c8
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run4 (by native_decide)
    (by simp [RegsOutside])
  have run5 := sszDecodeCleanupStore2f0 (fromStep + 4) args state4 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg4) seg4.atPc
    ((seg4.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg4)
  obtain ⟨state5, seg5⟩ := sszDecodeCleanupTailAppendDwordSite seg4 0x2f0 0x122cc
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run5 (by native_decide)
    (by simp [RegsOutside])
  have run6 := sszDecodeCleanupStore2f8 (fromStep + 5) args state5 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg5) seg5.atPc
    ((seg5.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg5)
  obtain ⟨state6, seg6⟩ := sszDecodeCleanupTailAppendDwordSite seg5 0x2f8 0x122d0
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run6 (by native_decide)
    (by simp [RegsOutside])
  have run7 := sszDecodeCleanupStore300 (fromStep + 6) args state6 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg6) seg6.atPc
    ((seg6.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg6)
  obtain ⟨state7, seg7⟩ := sszDecodeCleanupTailAppendDwordSite seg6 0x300 0x122d4
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run7 (by native_decide)
    (by simp [RegsOutside])
  have run8 := sszDecodeCleanupStore308 (fromStep + 7) args state7 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg7) seg7.atPc
    ((seg7.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg7)
  obtain ⟨state8, seg8⟩ := sszDecodeCleanupTailAppendDwordSite seg7 0x308 0x122d8
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run8 (by native_decide)
    (by simp [RegsOutside])
  have run9 := sszDecodeCleanupStore2d0 (fromStep + 8) args state8 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg8) seg8.atPc
    ((seg8.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg8)
  obtain ⟨state9, seg9⟩ := sszDecodeCleanupTailAppendDwordSite seg8 0x2d0 0x122dc
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run9 (by native_decide)
    (by simp [RegsOutside])
  have run10 := sszDecodeCleanupStore2d8 (fromStep + 9) args state9 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg9) seg9.atPc
    ((seg9.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg9)
  obtain ⟨state10, seg10⟩ := sszDecodeCleanupTailAppendDwordSite seg9 0x2d8 0x122e0
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run10 (by native_decide)
    (by simp [RegsOutside])
  have run11 := sszDecodeCleanupStore2e0 (fromStep + 10) args state10 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg10) seg10.atPc
    ((seg10.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg10)
  obtain ⟨state11, seg11⟩ := sszDecodeCleanupTailAppendDwordSite seg10 0x2e0 0x122e4
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run11 (by native_decide)
    (by simp [RegsOutside])
  have run12 := sszDecodeCleanupStore2e8 (fromStep + 11) args state11 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg11) seg11.atPc
    ((seg11.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg11)
  obtain ⟨state12, seg12⟩ := sszDecodeCleanupTailAppendDwordSite seg11 0x2e8 0x122e8
    (by omega) (by simp [sszDecodeCleanupOwnPc]) run12 (by native_decide)
    (by simp [RegsOutside])
  exact ⟨state12, by simpa only [Nat.add_assoc] using seg12⟩

/-- The post-`memcpy` cleanup reaches `0x1230c` with the success tag in `s6`. -/
theorem sszDecodeCleanupAfterMemcpyComplete (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (atPc : before.regs.get? PC = some 0x122b8)
    (atStack : before.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (access : DecodeBoundaryMachineAccess args.boundary before)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupTailWrites (sszDecodeCleanupTailMemory args)
        [⟨x22, 1⟩] fromStep 21 before after 0x1230c := by
  obtain ⟨state12, seg12⟩ := sszDecodeCleanupAfterMemcpyDwords fromStep args before atPc atStack
    stackFits stackAligned stackUpper access configured code
  have run13 := sszDecodeCleanupWord2c8 (fromStep + 12) args state12 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg12) seg12.atPc
    ((seg12.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg12)
  obtain ⟨state13, seg13⟩ := sszDecodeCleanupTailAppendStore seg12 0x2c8 (0 : BitVec 32)
    0x122ec (by omega) (by simp [sszDecodeCleanupOwnPc]) (by simp [RegsOutside])
    run13 (by native_decide)
  have run14 := sszDecodeCleanupHalf2cc (fromStep + 13) args state13 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg13) seg13.atPc
    ((seg13.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg13)
  obtain ⟨state14, seg14⟩ := sszDecodeCleanupTailAppendStore seg13 0x2cc (0 : BitVec 16)
    0x122f0 (by omega) (by simp [sszDecodeCleanupOwnPc]) (by simp [RegsOutside])
    run14 (by native_decide)
  have run15 := sszDecodeCleanupByte2ce (fromStep + 14) args state14 stackFits stackUpper
    (sszDecodeCleanupTailAccessOfSeg access seg14) seg14.atPc
    ((seg14.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg14)
  obtain ⟨state15, seg15⟩ := sszDecodeCleanupTailAppendStore seg14 0x2ce (0 : BitVec 8)
    0x122f4 (by omega) (by simp [sszDecodeCleanupOwnPc]) (by simp [RegsOutside])
    run15 (by native_decide)
  have run16 := sszDecodeCleanupWord2c0 (fromStep + 15) args state15 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg15) seg15.atPc
    ((seg15.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg15)
  obtain ⟨state16, seg16⟩ := sszDecodeCleanupTailAppendStore seg15 0x2c0 (0 : BitVec 32)
    0x122f8 (by omega) (by simp [sszDecodeCleanupOwnPc]) (by simp [RegsOutside])
    run16 (by native_decide)
  have run17 := sszDecodeCleanupHalf2c4 (fromStep + 16) args state16 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg16) seg16.atPc
    ((seg16.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg16)
  obtain ⟨state17, seg17⟩ := sszDecodeCleanupTailAppendStore seg16 0x2c4 (0 : BitVec 16)
    0x122fc (by omega) (by simp [sszDecodeCleanupOwnPc]) (by simp [RegsOutside])
    run17 (by native_decide)
  have run18 := sszDecodeCleanupByte2c6 (fromStep + 17) args state17 stackFits stackUpper
    (sszDecodeCleanupTailAccessOfSeg access seg17) seg17.atPc
    ((seg17.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg17)
  obtain ⟨state18, seg18⟩ := sszDecodeCleanupTailAppendStore seg17 0x2c6 (0 : BitVec 8)
    0x12300 (by omega) (by simp [sszDecodeCleanupOwnPc]) (by simp [RegsOutside])
    run18 (by native_decide)
  have run19 := sszDecodeCleanupWord2b8 (fromStep + 18) args state18 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg18) seg18.atPc
    ((seg18.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg18)
  obtain ⟨state19, seg19⟩ := sszDecodeCleanupTailAppendStore seg18 0x2b8 (0 : BitVec 32)
    0x12304 (by omega) (by simp [sszDecodeCleanupOwnPc]) (by simp [RegsOutside])
    run19 (by native_decide)
  have run20 := sszDecodeCleanupHalf2bc (fromStep + 19) args state19 stackFits stackAligned
    stackUpper (sszDecodeCleanupTailAccessOfSeg access seg19) seg19.atPc
    ((seg19.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans atStack)
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg19)
  obtain ⟨state20, seg20⟩ := sszDecodeCleanupTailAppendStore seg19 0x2bc (0 : BitVec 16)
    0x12308 (by omega) (by simp [sszDecodeCleanupOwnPc]) (by simp [RegsOutside])
    run20 (by native_decide)
  have run21 := sszDecodeCleanupSuccessTagStep (fromStep + 20) state20
    (sszDecodeCleanupTailAccessOfSeg access seg20).configured seg20.atPc
    (sszDecodeCleanupTailCodeOfSeg stackFits access code seg20)
  obtain ⟨state21, seg21⟩ := sszDecodeCleanupTailAppendRegister seg20 x22 1 0x1230c
    (by simp [sszDecodeCleanupOwnPc]) run21 (by native_decide)
    (by simp [sszDecodeCleanupTailWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  exact ⟨state21, by simpa only [Nat.add_assoc] using seg21⟩

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
