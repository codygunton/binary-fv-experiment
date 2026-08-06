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
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L2_1
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L2_2
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L3_1
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L4_1
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L5_1

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

/-- Compose the six real wrapper epilogue instructions through the final stack deallocation,
stopping at the function-instance exit instruction rather than retiring `ret`. -/
theorem wrapper_epilogue_to_exit {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (fromStep : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10360))
    (stackBase link savedS0 savedS1 savedS2 stack restoredStack result status raAddress s0Address s1Address
      s2Address : BitVec 64)
    (frame : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 state)
    (stackValue : state.regs.get? x2 = some stack)
    (resultValue : state.regs.get? x10 = some result) (statusValue : state.regs.get? x11 = some status)
    (raAddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7e8#12) = raAddress)
    (s0AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7e0#12) = s0Address)
    (s1AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7d8#12) = s1Address)
    (s2AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7d0#12) = s2Address)
    (raAddressNat : stackBase.toNat + 0xa18 = raAddress.toNat)
    (s0AddressNat : stackBase.toNat + 0xa10 = s0Address.toNat)
    (s1AddressNat : stackBase.toNat + 0xa08 = s1Address.toNat)
    (s2AddressNat : stackBase.toNat + 0xa00 = s2Address.toNat)
    (raAligned : is_aligned_vaddr (virtaddr.Virtaddr raAddress) 8 = true)
    (s0Aligned : is_aligned_vaddr (virtaddr.Virtaddr s0Address) 8 = true)
    (s1Aligned : is_aligned_vaddr (virtaddr.Virtaddr s1Address) 8 = true)
    (s2Aligned : is_aligned_vaddr (virtaddr.Virtaddr s2Address) 8 = true)
    (raAllowed : DecoderAccessRange (DecoderReadableByte machineArgs) raAddress 8)
    (s0Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s0Address 8)
    (s1Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s1Address 8)
    (s2Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s2Address 8)
    (restoredStackEq : (stack + sign_extend (m := 64) (0x230#12)) +
      sign_extend (m := 64) (0x7f0#12) = restoredStack) :
    ∃ after, WrapperEpilogueExitResult fromStep base state after link savedS0 savedS1 savedS2 restoredStack
      result status := by
  obtain ⟨retiredFirst, retiredRa, firstRun, raRun, firstTrace, raAtRa, frameRa, retiredRaPresent⟩ :=
    wrapper_epilogue_first_restore_and_ra machine agree retiredPresent code fromStep atPc stackBase link
      savedS0 savedS1 savedS2 stack raAddress frame stackValue raAddressEq raAddressNat raAligned raAllowed
  let afterFirst := wrapperAfterFirstStackRestore state retiredFirst stack
  let afterRa := afterRegisterWrite afterFirst (BitVec.ofNat 64 0x10364) retiredRa x1 link
  have agreeFirst : Agree decoderPreserved base afterFirst := by
    apply agree.trans
    intro register preserved
    cases register <;>
      simp only [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert] at preserved ⊢ <;>
      simp_all [decoderPreserved, platformPreserved]
  have agreeRa : Agree decoderPreserved base afterRa := agreeFirst.trans
    (afterRegisterWrite_agree_of (P := decoderPreserved) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have codeRa : canonicalContractParams.env.CodeIntact afterRa := by
    simpa [afterRa, afterFirst, wrapperAfterFirstStackRestore, afterRegisterWrite_mem] using code
  have memoryRa : afterRa.mem = state.mem := by rfl
  have stackRa : afterRa.regs.get? x2 = some (stack + sign_extend (m := 64) (0x230#12)) :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans
      (tryStepStackAddiAfterRetired_stackPointer state (BitVec.ofNat 64 0x10360) 0x230#12 stack
        retiredFirst)
  have resultRa : afterRa.regs.get? x10 = some result := by
    simp [afterRa, afterFirst, afterRegisterWrite, wrapperAfterFirstStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resultValue]
  have statusRa : afterRa.regs.get? x11 = some status := by
    simp [afterRa, afterFirst, afterRegisterWrite, wrapperAfterFirstStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, statusValue]
  have atS0 : afterRa.regs.get? PC = some (BitVec.ofNat 64 0x10368) := by
    simpa [afterRa] using afterRegisterWrite_pc afterFirst (BitVec.ofNat 64 0x10364) retiredRa x1 link
  obtain ⟨afterS2, saved⟩ := wrapper_epilogue_restore_saved_registers machine agreeRa retiredRaPresent
    codeRa (fromStep + 2) atS0 stackBase link savedS0 savedS1 savedS2
    (stack + sign_extend (m := 64) (0x230#12)) result status s0Address s1Address s2Address frameRa raAtRa
    stackRa resultRa statusRa s0AddressEq s1AddressEq s2AddressEq s0AddressNat s1AddressNat s2AddressNat
    s0Aligned s1Aligned s2Aligned s0Allowed s1Allowed s2Allowed
  obtain ⟨retiredStack, stackRun⟩ := wrapper_epilogue_final_stack_restore_step machine saved.agree
    saved.retired saved.code (fromStep + 5) saved.pc
    (stack + sign_extend (m := 64) (0x230#12)) saved.sp
  let afterStack := wrapperAfterFinalStackRestore afterS2 retiredStack
    (stack + sign_extend (m := 64) (0x230#12))
  have stackAgree : Agree decoderPreserved afterS2 afterStack := by
    intro register preserved
    cases register <;>
      simp only [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert] at preserved ⊢ <;>
      simp_all [decoderPreserved, platformPreserved]
  have retiredStackPresent : RetiredCounterPresent afterStack := by
    refine ⟨Sail.BitVec.addInt retiredStack 1, ?_⟩
    simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick]
  have atRa : afterFirst.regs.get? PC = some (BitVec.ofNat 64 0x10364) := by
    simp [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
      stackAddiNextState, tryStepStackAddiAfterIncrement, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
    decide
  have prefixFirst : WrapperPrefix fromStep 1 state afterFirst :=
    ConfinedPrefix.ownStep' atPc (by simpa [afterFirst] using firstRun)
  have prefixRa : WrapperPrefix (fromStep + 1) 1 afterFirst afterRa :=
    ConfinedPrefix.ownStep' atRa (by simpa [afterFirst, afterRa] using raRun)
  have prefixStack : WrapperPrefix (fromStep + 5) 1 afterS2 afterStack :=
    ConfinedPrefix.ownStep' saved.pc (by simpa [afterStack] using stackRun)
  have confined : WrapperPrefix fromStep 6 state afterStack := by
    confined_steps [prefixFirst, prefixRa, saved.confined, prefixStack]
  refine ⟨afterStack, ⟨?_, confined, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [Nat.add_assoc] using Trace.append firstTrace (Trace.append saved.trace
      (Trace.one (fromStep + 5) afterS2 afterStack (by simpa [afterStack] using stackRun)))
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert]
    decide
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.ra]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.s0]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.s1]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.s2]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, restoredStackEq]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.a0]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.a1]
  · calc afterStack.mem = afterS2.mem := by rfl
      _ = afterRa.mem := saved.memory
      _ = state.mem := memoryRa
  · simpa [afterStack, wrapperAfterFinalStackRestore] using saved.code
  · exact saved.agree.trans stackAgree
  · exact retiredStackPresent

/-- Compose the real seven-instruction epilogue after the status store. -/
theorem wrapper_epilogue_complete {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (fromStep : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10360))
    (stackBase link savedS0 savedS1 savedS2 stack restoredStack result status raAddress s0Address s1Address
      s2Address : BitVec 64)
    (frame : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 state)
    (stackValue : state.regs.get? x2 = some stack)
    (resultValue : state.regs.get? x10 = some result) (statusValue : state.regs.get? x11 = some status)
    (raAddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7e8#12) = raAddress)
    (s0AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7e0#12) = s0Address)
    (s1AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7d8#12) = s1Address)
    (s2AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7d0#12) = s2Address)
    (raAddressNat : stackBase.toNat + 0xa18 = raAddress.toNat)
    (s0AddressNat : stackBase.toNat + 0xa10 = s0Address.toNat)
    (s1AddressNat : stackBase.toNat + 0xa08 = s1Address.toNat)
    (s2AddressNat : stackBase.toNat + 0xa00 = s2Address.toNat)
    (raAligned : is_aligned_vaddr (virtaddr.Virtaddr raAddress) 8 = true)
    (s0Aligned : is_aligned_vaddr (virtaddr.Virtaddr s0Address) 8 = true)
    (s1Aligned : is_aligned_vaddr (virtaddr.Virtaddr s1Address) 8 = true)
    (s2Aligned : is_aligned_vaddr (virtaddr.Virtaddr s2Address) 8 = true)
    (raAllowed : DecoderAccessRange (DecoderReadableByte machineArgs) raAddress 8)
    (s0Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s0Address 8)
    (s1Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s1Address 8)
    (s2Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s2Address 8)
    (restoredStackEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7f0#12) = restoredStack)
    (linkEven : Sail.BitVec.update link 0 0#1 = link) (linkBit1 : Sail.BitVec.access link 1 = 0#1) :
    ∃ after, WrapperEpilogueCompleteResult fromStep base state after link savedS0 savedS1 savedS2 restoredStack
      result status := by
  obtain ⟨retiredFirst, retiredRa, firstRun, raRun, firstTrace, raAtRa, frameRa, retiredRaPresent⟩ :=
    wrapper_epilogue_first_restore_and_ra machine agree retiredPresent code fromStep atPc stackBase link
      savedS0 savedS1 savedS2 stack raAddress frame stackValue raAddressEq raAddressNat raAligned raAllowed
  let afterFirst := wrapperAfterFirstStackRestore state retiredFirst stack
  let afterRa := afterRegisterWrite afterFirst (BitVec.ofNat 64 0x10364) retiredRa x1 link
  have agreeFirst : Agree decoderPreserved base afterFirst := by
    apply agree.trans
    intro register preserved
    cases register <;>
      simp only [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert] at preserved ⊢ <;>
      simp_all [decoderPreserved, platformPreserved]
  have agreeRa : Agree decoderPreserved base afterRa := agreeFirst.trans
    (afterRegisterWrite_agree_of (P := decoderPreserved) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have codeRa : canonicalContractParams.env.CodeIntact afterRa := by
    simpa [afterRa, afterFirst, wrapperAfterFirstStackRestore, afterRegisterWrite_mem] using code
  have memoryRa : afterRa.mem = state.mem := by rfl
  have stackRa : afterRa.regs.get? x2 = some (stack + sign_extend (m := 64) (0x230#12)) :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans
      (tryStepStackAddiAfterRetired_stackPointer state (BitVec.ofNat 64 0x10360) 0x230#12 stack
        retiredFirst)
  have resultRa : afterRa.regs.get? x10 = some result := by
    simp [afterRa, afterFirst, afterRegisterWrite, wrapperAfterFirstStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resultValue]
  have statusRa : afterRa.regs.get? x11 = some status := by
    simp [afterRa, afterFirst, afterRegisterWrite, wrapperAfterFirstStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, statusValue]
  have atS0 : afterRa.regs.get? PC = some (BitVec.ofNat 64 0x10368) := by
    simpa [afterRa] using afterRegisterWrite_pc afterFirst (BitVec.ofNat 64 0x10364) retiredRa x1 link
  obtain ⟨afterS2, saved⟩ := wrapper_epilogue_restore_saved_registers machine agreeRa retiredRaPresent
    codeRa (fromStep + 2) atS0 stackBase link savedS0 savedS1 savedS2
    (stack + sign_extend (m := 64) (0x230#12)) result status s0Address s1Address s2Address frameRa raAtRa
    stackRa resultRa statusRa s0AddressEq s1AddressEq s2AddressEq s0AddressNat s1AddressNat s2AddressNat
    s0Aligned s1Aligned s2Aligned s0Allowed s1Allowed s2Allowed
  obtain ⟨afterReturn, final⟩ := wrapper_epilogue_final_restore_and_return machine (fromStep + 2)
    stackBase link savedS0 savedS1 savedS2 (stack + sign_extend (m := 64) (0x230#12)) restoredStack result
    status saved saved.pc restoredStackEq linkEven linkBit1
  refine ⟨afterReturn, ⟨?_, final.pc, final.ra, final.s0, final.s1, final.s2, final.sp, final.a0,
    final.a1, ?_, final.code, final.agree, final.retired⟩⟩
  · simpa only [Nat.add_assoc] using Trace.append firstTrace (Trace.append saved.trace final.trace)
  · calc afterReturn.mem = afterS2.mem := final.memory
      _ = afterRa.mem := saved.memory
      _ = state.mem := memoryRa

end BinaryFv.Zesu.MachineExecution
