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

/-- Execute the common status store.  The target is explicit because `s2` is a live wrapper value,
not a callee argument convention. -/
theorem wrapper_epilogue_status_store_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1035c))
    (statusBase target status : BitVec 64) (targetValue : state.regs.get? x18 = some statusBase)
    (statusValue : state.regs.get? x11 = some status)
    (targetEq : statusBase + sign_extend (m := 64) 0x4#12 = target)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr target) 4 = true)
    (allowed : DecoderAccessRange DecoderWritableByte target 4) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterStatusStore state retired target status) false := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContextOfDecoderAgree machine agree
  obtain ⟨retired, run⟩ := decoderStoreWordStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x1035c 0x23 0x22 0xb9 0x00 0x4#12 11#5 18#5 statusBase status target atPc
    (rX_bits_run_x18 _ statusBase (decoderExecuteState_get? targetValue))
    (rX_bits_run_x11 _ status (decoderExecuteState_get? statusValue))
    targetEq allowed
  exact ⟨retired, by
    simpa [wrapperAfterStatusStore, afterMemoryWrite,
      show Sail.BitVec.addInt (BitVec.ofNat 64 0x1035c) 4 = BitVec.ofNat 64 0x10360 from by decide]
      using run⟩

/-- Execute the first of the wrapper's two epilogue stack restorations.

`addi sp, sp, 560` is an ordinary `ITYPE`, so this is `decoderITypeStepOfDecoderAgree` at the
`ADDI` opcode with `sp` as both source and destination: the fetch, decode, execute and `try_step`
postlude are all the class lemma's, and only the two register runs and the post-state identity are
this module's. Before the class lemma accepted `Agree decoderPreserved` it was unreachable here,
because the wrapper's prologue `jalr` has already clobbered `x1`. -/
theorem wrapper_epilogue_first_stack_restore_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10360))
    (stack : BitVec 64) (stackValue : state.regs.get? x2 = some stack) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterFirstStackRestore state retired stack) false := by
  obtain ⟨retired, run⟩ := decoderITypeStepOfDecoderAgree machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10360 0x13 0x01 0x01 0x23 0x230#12 2#5 2#5 .ADDI atPc
    (rX_x2_run _ stack (decoderExecuteState_get? stackValue))
    (wX_x2_run _ (stack + sign_extend (m := 64) 0x230#12))
  exact ⟨retired, by
    simpa [wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired_eq_afterRegisterWrite]
      using run⟩

/-- Execute the actual `ld ra, 2024(sp)` at `0x10364`. -/
theorem wrapper_epilogue_load_ra_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10364))
    (stack link address : BitVec 64) (stackValue : state.regs.get? x2 = some stack)
    (addressEq : stack + sign_extend (m := 64) (0x7e8#12) = address)
    (savedBase : Nat) (addressNat : savedBase = address.toNat)
    (frame : SavedWordBytes state savedBase link)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10364) retired x1 link) false :=
  decoderLoadStepOfDecoderAgree (dest := x1) (value := link) machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10364 0x83 0x30 0x81 0x7e 0x7e8#12 2#5 1#5 false 8 link atPc
    (wrapper_epilogue_saved_load_read machine agree (BitVec.ofNat 64 0x10364) 0x7e8#12 (.Regidx 2#5)
      link stack address (rX_x2_run _ stack (decoderExecuteState_get? stackValue)) addressEq
      savedBase addressNat frame aligned allowed)
    (by rw [extend_value_dword]; exact wX_x1_run _ link)

/-- Execute the actual `ld s0, 2016(sp)` at `0x10368`. -/
theorem wrapper_epilogue_load_s0_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10368))
    (stack s0 address : BitVec 64) (stackValue : state.regs.get? x2 = some stack)
    (addressEq : stack + sign_extend (m := 64) (0x7e0#12) = address)
    (savedBase : Nat) (addressNat : savedBase = address.toNat)
    (frame : SavedWordBytes state savedBase s0)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10368) retired x8 s0) false :=
  decoderLoadStepOfDecoderAgree (dest := x8) (value := s0) machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10368 0x03 0x34 0x01 0x7e 0x7e0#12 2#5 8#5 false 8 s0 atPc
    (wrapper_epilogue_saved_load_read machine agree (BitVec.ofNat 64 0x10368) 0x7e0#12 (.Regidx 2#5)
      s0 stack address (rX_x2_run _ stack (decoderExecuteState_get? stackValue)) addressEq
      savedBase addressNat frame aligned allowed)
    (by rw [extend_value_dword]; exact wX_x8_run _ s0)

/-- Execute the actual `ld s1, 2008(sp)` at `0x1036c`. -/
theorem wrapper_epilogue_load_s1_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1036c))
    (stack s1 address : BitVec 64) (stackValue : state.regs.get? x2 = some stack)
    (addressEq : stack + sign_extend (m := 64) (0x7d8#12) = address)
    (savedBase : Nat) (addressNat : savedBase = address.toNat)
    (frame : SavedWordBytes state savedBase s1)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1036c) retired x9 s1) false :=
  decoderLoadStepOfDecoderAgree (dest := x9) (value := s1) machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x1036c 0x83 0x34 0x81 0x7d 0x7d8#12 2#5 9#5 false 8 s1 atPc
    (wrapper_epilogue_saved_load_read machine agree (BitVec.ofNat 64 0x1036c) 0x7d8#12 (.Regidx 2#5)
      s1 stack address (rX_x2_run _ stack (decoderExecuteState_get? stackValue)) addressEq
      savedBase addressNat frame aligned allowed)
    (by rw [extend_value_dword]; exact wX_x9_run _ s1)

end BinaryFv.Zesu.MachineExecution
