import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.RiscV.Step.TryStepStackAddi
import BinaryFv.RiscV.Step.TryStepStackAddiMemory
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L1_1
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L1_2

/-!
# Shared `zesu_decode_raw` epilogue

The wrapper paths meet at `0x1035c`.  This module proves that common instruction sequence; callers
supply the value already selected for `a0`, the normalized status in `a1`, and the ordinary
machine frame carried from their own path.  No source-function ABI is assigned to an inline child.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Execute the actual `ld s2, 2000(sp)` at `0x10370`. -/
theorem wrapper_epilogue_load_s2_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10370))
    (stack s2 address : BitVec 64) (stackValue : state.regs.get? x2 = some stack)
    (addressEq : stack + sign_extend (m := 64) (0x7d0#12) = address)
    (savedBase : Nat) (addressNat : savedBase = address.toNat)
    (frame : SavedWordBytes state savedBase s2)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10370) retired x18 s2) false :=
  decoderLoadStepOfDecoderAgree (dest := x18) (value := s2) machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10370 0x03 0x39 0x01 0x7d 0x7d0#12 2#5 18#5 false 8 s2 atPc
    (wrapper_epilogue_saved_load_read machine agree (BitVec.ofNat 64 0x10370) 0x7d0#12 (.Regidx 2#5)
      s2 stack address (rX_x2_run _ stack (decoderExecuteState_get? stackValue)) addressEq
      savedBase addressNat frame aligned allowed)
    (by rw [extend_value_dword]; exact wX_x18_run _ s2)

/-- Execute the final wrapper stack restoration; with the preceding `+560`, it exactly reverses
the prologue's `0xa20`-byte allocation. `decoderITypeStepOfDecoderAgree` again, as for the first
restoration. -/
theorem wrapper_epilogue_final_stack_restore_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10374))
    (stack : BitVec 64) (stackValue : state.regs.get? x2 = some stack) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterFinalStackRestore state retired stack) false := by
  obtain ⟨retired, run⟩ := decoderITypeStepOfDecoderAgree machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10374 0x13 0x01 0x01 0x7f 0x7f0#12 2#5 2#5 .ADDI atPc
    (rX_x2_run _ stack (decoderExecuteState_get? stackValue))
    (wX_x2_run _ (stack + sign_extend (m := 64) 0x7f0#12))
  exact ⟨retired, by
    simpa [wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired_eq_afterRegisterWrite]
      using run⟩

/-- Retire the actual final `ret`, jumping to the explicitly restored return address. -/
theorem wrapper_epilogue_return_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10378))
    (link : BitVec 64) (linkValue : state.regs.get? x1 = some link)
    (linkEven : Sail.BitVec.update link 0 0#1 = link) (linkBit1 : Sail.BitVec.access link 1 = 0#1) :
    ∃ retired, Runs (try_step stepNo false) state (wrapperAfterReturn state retired link) false ∧
      (wrapperAfterReturn state retired link).regs.get? PC = some link := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContextOfDecoderAgree machine agree
  obtain ⟨retired, run⟩ := decoderRetStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10378 0x67 0x80 0x00 0x00 1#5 link link atPc
    (rX_bits_run_x1 _ _ (decoderExecuteState_get? linkValue))
  refine ⟨retired, ?_, ?_⟩
  · simpa [wrapperAfterReturn] using run
  · simp [wrapperAfterReturn, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]

/-- The common wrapper epilogue stopped at the generated function-instance exit instruction.
This retires the six instructions from `0x10360` through `0x10374`, but leaves `ret` at
`0x10378` unexecuted. -/
structure WrapperEpilogueExitResult (fromStep : Nat) (base before after : State)
    (link savedS0 savedS1 savedS2 restoredStack result status : BitVec 64) : Prop where
  trace : Trace fromStep 6 before after
  confined : WrapperPrefix fromStep 6 before after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  ra : after.regs.get? x1 = some link
  s0 : after.regs.get? x8 = some savedS0
  s1 : after.regs.get? x9 = some savedS1
  s2 : after.regs.get? x18 = some savedS2
  sp : after.regs.get? x2 = some restoredStack
  a0 : after.regs.get? x10 = some result
  a1 : after.regs.get? x11 = some status
  memory : after.mem = before.mem
  code : canonicalContractParams.env.CodeIntact after
  agree : Agree decoderPreserved base after
  retired : RetiredCounterPresent after

end BinaryFv.Zesu.MachineExecution
