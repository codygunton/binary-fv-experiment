import BinaryFv.Zesu.MachineExecution.HLevel3RawEncoderSteps

/-!
# Shared Level 3 Boolean encoder steps

The called Boolean encoder has one production instance. This module reuses the configured
instruction classes and exposes its exact parent-owned prologue before the shared raw encoder.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

def booleanEncoderWord (value : Bool) : BitVec 64 := if value then 1 else 0

theorem booleanEncoderMaskResult (value : Bool) :
    booleanEncoderWord value = iTypeResult .ANDI 1 (booleanEncoderWord value) := by
  cases value <;> native_decide

/-- Production `0x15b9c: addi sp,sp,-16`. -/
theorem booleanEncoderSubtractStep (stepNo stackPointer : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15b9c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (lower : 16 ≤ stackPointer) (upper : stackPointer < 2 ^ 64) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15b9c retired x2
        (BitVec.ofNat 64 (stackPointer - 16))) false := by
  exact configuredAddiX2Step stepNo 0x15b9c state 0xff0
    (BitVec.ofNat 64 stackPointer) (BitVec.ofNat 64 (stackPointer - 16))
    0x13 0x01 0x01 0xff configured atPc stack loaded
    (stackSubtractResult stackPointer 16 0xff0 lower upper (by native_decide))
    (by write_success_decode configured) (base := by rfl)

/-- Production `0x15ba0: sd ra,8(sp)`. -/
theorem booleanEncoderSaveReturnStep (stepNo stackPointer returnAddress : Nat) (state : State)
    (access : EncoderCallMachineAccess 16
      { returnAddress := returnAddress, callerStack := stackPointer,
        inputSize := inputSize, value := value } state)
    (atPc : state.regs.get? PC = some 0x15ba0)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (stackPointer - 16)))
    (link : state.regs.get? x1 = some (BitVec.ofNat 64 returnAddress))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (lower : 16 ≤ stackPointer) (upper : stackPointer < 2 ^ 64) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x15ba0)
          (stackPointer - 16 + 8) (BitVec.ofNat 64 returnAddress))
        0x15ba0 retired) false := by
  exact configuredStackDwordStoreStep stepNo 0x15ba0 (stackPointer - 16) 8 state
    (BitVec.ofNat 64 returnAddress) 8 (.Regidx 1#5) 0x23 0x34 0x11 0x00
    access.output.configured atPc stack (access.frameStore 8 8 (by omega))
    (access.frameStoreNoMMIO 8 8 (by omega))
    (by
      rcases Nat.dvd_of_mod_eq_zero access.stackAligned with ⟨factor, rfl⟩
      omega)
    (by
      omega)
    loaded
    (by
      rw [show sign_extend (m := 64) (8 : BitVec 12) = BitVec.ofNat 64 8 by native_decide]
      change BitVec.ofNat 64 (stackPointer - 16) + BitVec.ofNat 64 8 = _
      rw [← BitVec.ofNat_add])
    (by configured_store_decode access.output.configured)
    (by
      intro premise writes
      exact rX_x1_run premise (BitVec.ofNat 64 returnAddress)
        ((writes.get x1 (by decide)).trans link))
    (base := by unfold BaseInstructionEncoding; native_decide)

/-- Production `0x15ba4: andi a0,a0,1`. -/
theorem booleanEncoderMaskStep (stepNo : Nat) (value : Bool) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15ba4)
    (source : state.regs.get? x10 = some (booleanEncoderWord value))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15ba4 retired x10 (booleanEncoderWord value)) false := by
  exact configuredITypeX10Step stepNo 0x15ba4 state 1 (.Regidx 10#5) .ANDI
    (booleanEncoderWord value) (booleanEncoderWord value) 0x13 0x75 0x15 0x00
    configured atPc loaded (booleanEncoderMaskResult value)
    (by
      intro premise writes
      exact rX_x10_run premise (booleanEncoderWord value)
        ((writes.get x10 (by decide)).trans source))
    (by
      intro premise
      rw [← booleanEncoderMaskResult value]
      exact wX_x10_run premise _)
    (by write_success_decode configured) (base := by rfl)

/-- Production `0x15ba8: sb a0,7(sp)`. -/
theorem booleanEncoderStoreStep (stepNo stackPointer : Nat) (value : Bool) (state : State)
    (access : EncoderCallMachineAccess 16
      { returnAddress := returnAddress, callerStack := stackPointer,
        inputSize := inputSize, value := value } state)
    (atPc : state.regs.get? PC = some 0x15ba8)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (stackPointer - 16)))
    (source : state.regs.get? x10 = some (booleanEncoderWord value))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (lower : 16 ≤ stackPointer) (upper : stackPointer < 2 ^ 64) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 1)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15ba8)
          (stackPointer - 16 + 7) (booleanEncoderWord value))
        (Sail.BitVec.addInt 0x15ba8 4) retired) false := by
  exact configuredStackByteStoreStep stepNo 0x15ba8 (stackPointer - 16) 7 state
    (booleanEncoderWord value) 7 (.Regidx 10#5) 0xa3 0x03 0xa1 0x00
    access.output.configured atPc stack (access.frameStore 7 1 (by omega))
    (access.frameStoreNoMMIO 7 1 (by omega))
    (by
      omega)
    loaded
    (by
      rw [show sign_extend (m := 64) (7 : BitVec 12) = BitVec.ofNat 64 7 by native_decide]
      change BitVec.ofNat 64 (stackPointer - 16) + BitVec.ofNat 64 7 = _
      rw [← BitVec.ofNat_add])
    (by write_success_decode access.output.configured)
    (by
      intro premise writes
      exact rX_x10_run premise (booleanEncoderWord value)
        ((writes.get x10 (by decide)).trans source))
    (base := by unfold BaseInstructionEncoding; native_decide)

end BinaryFv.Zesu.MachineExecution
