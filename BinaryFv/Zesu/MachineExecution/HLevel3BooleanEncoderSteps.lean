import BinaryFv.Zesu.MachineExecution.EncoderCallPrologue

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
  exact encoderCallSubtract16Step stepNo 0x15b9c stackPointer state configured atPc stack
    loaded lower upper (by native_decide)

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
  exact encoderCallSaveReturn16Step stepNo 0x15ba0 stackPointer returnAddress state access
    atPc stack link loaded lower upper (by native_decide)

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
