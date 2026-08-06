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
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L5_2

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

theorem wrapper_epilogue_restore_saved_registers {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (fromStep : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10368))
    (stackBase link savedS0 savedS1 savedS2 stack result status s0Address s1Address s2Address : BitVec 64)
    (frame : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 state)
    (raValue : state.regs.get? x1 = some link)
    (stackValue : state.regs.get? x2 = some stack)
    (resultValue : state.regs.get? x10 = some result)
    (statusValue : state.regs.get? x11 = some status)
    (s0AddressEq : stack + sign_extend (m := 64) (0x7e0#12) = s0Address)
    (s1AddressEq : stack + sign_extend (m := 64) (0x7d8#12) = s1Address)
    (s2AddressEq : stack + sign_extend (m := 64) (0x7d0#12) = s2Address)
    (s0AddressNat : stackBase.toNat + 0xa10 = s0Address.toNat)
    (s1AddressNat : stackBase.toNat + 0xa08 = s1Address.toNat)
    (s2AddressNat : stackBase.toNat + 0xa00 = s2Address.toNat)
    (s0Aligned : is_aligned_vaddr (virtaddr.Virtaddr s0Address) 8 = true)
    (s1Aligned : is_aligned_vaddr (virtaddr.Virtaddr s1Address) 8 = true)
    (s2Aligned : is_aligned_vaddr (virtaddr.Virtaddr s2Address) 8 = true)
    (s0Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s0Address 8)
    (s1Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s1Address 8)
    (s2Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s2Address 8) :
    ∃ after, WrapperEpilogueSavedRegistersResult fromStep base state after stackBase link savedS0 savedS1
      savedS2 stack result status := by
  obtain ⟨retiredS0, s0Run⟩ := wrapper_epilogue_load_s0_step machine agree retiredPresent code
    fromStep atPc stack savedS0 s0Address stackValue s0AddressEq (stackBase.toNat + 0xa10)
    s0AddressNat frame.2.1 s0Aligned s0Allowed
  let afterS0 := afterRegisterWrite state (BitVec.ofNat 64 0x10368) retiredS0 x8 savedS0
  have agreeS0 : Agree decoderPreserved base afterS0 :=
    agree.trans (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have retiredS0Present : RetiredCounterPresent afterS0 :=
    afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10368) retiredS0 x8 savedS0
  have atS1 : afterS0.regs.get? PC = some (BitVec.ofNat 64 0x1036c) := by
    simpa [afterS0] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10368) retiredS0 x8 savedS0
  have stackS0 : afterS0.regs.get? x2 = some stack :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans stackValue
  have frameS0 : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 afterS0 :=
    WrapperSavedRegisterFrame.of_mem_eq frame (afterRegisterWrite_mem _ _ _ _ _)
  have codeS0 : canonicalContractParams.env.CodeIntact afterS0 := by
    simpa [afterS0, afterRegisterWrite_mem] using code
  have machineS0 := machine.mono agreeS0 retiredS0Present
  obtain ⟨retiredS1, s1Run⟩ := wrapper_epilogue_load_s1_step machineS0 (Agree.refl afterS0)
    retiredS0Present codeS0 (fromStep + 1) atS1 stack savedS1 s1Address stackS0 s1AddressEq
    (stackBase.toNat + 0xa08) s1AddressNat frameS0.2.2.1 s1Aligned s1Allowed
  let afterS1 := afterRegisterWrite afterS0 (BitVec.ofNat 64 0x1036c) retiredS1 x9 savedS1
  have agreeS1 : Agree decoderPreserved base afterS1 :=
    agreeS0.trans (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have retiredS1Present : RetiredCounterPresent afterS1 :=
    afterRegisterWrite_retired_present afterS0 (BitVec.ofNat 64 0x1036c) retiredS1 x9 savedS1
  have atS2 : afterS1.regs.get? PC = some (BitVec.ofNat 64 0x10370) := by
    simpa [afterS1] using afterRegisterWrite_pc afterS0 (BitVec.ofNat 64 0x1036c) retiredS1 x9 savedS1
  have stackS1 : afterS1.regs.get? x2 = some stack :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans stackS0
  have frameS1 : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 afterS1 :=
    WrapperSavedRegisterFrame.of_mem_eq frameS0 (afterRegisterWrite_mem _ _ _ _ _)
  have codeS1 : canonicalContractParams.env.CodeIntact afterS1 := by
    simpa [afterS1, afterRegisterWrite_mem] using codeS0
  have machineS1 := machine.mono agreeS1 retiredS1Present
  obtain ⟨retiredS2, s2Run⟩ := wrapper_epilogue_load_s2_step machineS1 (Agree.refl afterS1)
    retiredS1Present codeS1 (fromStep + 2) atS2 stack savedS2 s2Address stackS1 s2AddressEq
    (stackBase.toNat + 0xa00) s2AddressNat frameS1.2.2.2 s2Aligned s2Allowed
  let afterS2 := afterRegisterWrite afterS1 (BitVec.ofNat 64 0x10370) retiredS2 x18 savedS2
  have agreeS2 : Agree decoderPreserved base afterS2 :=
    agreeS1.trans (afterRegisterWrite_agree_of (P := decoderPreserved)
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have prefixS0 : WrapperPrefix fromStep 1 state afterS0 :=
    ConfinedPrefix.ownStep' atPc (by simpa [afterS0] using s0Run)
  have prefixS1 : WrapperPrefix (fromStep + 1) 1 afterS0 afterS1 :=
    ConfinedPrefix.ownStep' atS1 (by simpa [afterS0, afterS1] using s1Run)
  have prefixS2 : WrapperPrefix (fromStep + 2) 1 afterS1 afterS2 :=
    ConfinedPrefix.ownStep' atS2 (by simpa [afterS1, afterS2] using s2Run)
  have savedPrefix : WrapperPrefix fromStep 3 state afterS2 := by
    confined_steps [prefixS0, prefixS1, prefixS2]
  refine ⟨afterS2, ⟨?_, savedPrefix, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · trace_steps [(by simpa [afterS0] using s0Run), (by simpa [afterS0, afterS1] using s1Run),
      (by simpa [afterS1, afterS2] using s2Run)]
  · simpa [afterS2] using
      afterRegisterWrite_pc afterS1 (BitVec.ofNat 64 0x10370) retiredS2 x18 savedS2
  · rfl
  · exact ((afterRegisterWrite_writes _ _ _ _ _).get x1 (by decide)).trans
      (((afterRegisterWrite_writes _ _ _ _ _).get x1 (by decide)).trans
        (((afterRegisterWrite_writes _ _ _ _ _).get x1 (by decide)).trans raValue))
  · simp [afterS2, afterS1, afterS0, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [afterS2, afterS1, afterS0, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [afterS2, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · exact ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans
      (((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans
        (((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans stackValue))
  · exact ((afterRegisterWrite_writes _ _ _ _ _).get x10 (by decide)).trans
      (((afterRegisterWrite_writes _ _ _ _ _).get x10 (by decide)).trans
        (((afterRegisterWrite_writes _ _ _ _ _).get x10 (by decide)).trans resultValue))
  · exact ((afterRegisterWrite_writes _ _ _ _ _).get x11 (by decide)).trans
      (((afterRegisterWrite_writes _ _ _ _ _).get x11 (by decide)).trans
        (((afterRegisterWrite_writes _ _ _ _ _).get x11 (by decide)).trans statusValue))
  · exact WrapperSavedRegisterFrame.of_mem_eq frameS1 (afterRegisterWrite_mem _ _ _ _ _)
  · simpa [afterS2, afterRegisterWrite_mem] using codeS1
  · exact agreeS2
  · exact afterRegisterWrite_retired_present afterS1 (BitVec.ofNat 64 0x10370) retiredS2 x18 savedS2

/-- Execute `addi sp, sp, 2032` and the production `ret` after the typed saved-register phase. -/
theorem wrapper_epilogue_final_restore_and_return {base before state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (fromStep : Nat) (stackBase link savedS0 savedS1 savedS2 stack restoredStack result status : BitVec 64)
    (saved : WrapperEpilogueSavedRegistersResult fromStep base before state stackBase link savedS0 savedS1
      savedS2 stack result status)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10374))
    (restoredStackEq : stack + sign_extend (m := 64) (0x7f0#12) = restoredStack)
    (linkEven : Sail.BitVec.update link 0 0#1 = link) (linkBit1 : Sail.BitVec.access link 1 = 0#1) :
    ∃ after, WrapperEpilogueReturnResult (fromStep + 3) base state after link savedS0 savedS1 savedS2
      stack restoredStack result status := by
  obtain ⟨retiredStack, stackRun⟩ := wrapper_epilogue_final_stack_restore_step machine saved.agree
    saved.retired saved.code (fromStep + 3) atPc stack saved.sp
  let afterStack := wrapperAfterFinalStackRestore state retiredStack stack
  have stackAgree : Agree decoderPreserved state afterStack :=
    epilogue_afterFinalStackRestore_agree state retiredStack _
  have agreeStack : Agree decoderPreserved base afterStack := saved.agree.trans stackAgree
  have retiredStackPresent : RetiredCounterPresent afterStack := by
    refine ⟨Sail.BitVec.addInt retiredStack 1, ?_⟩
    simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick]
  have codeStack : canonicalContractParams.env.CodeIntact afterStack := by
    simpa [afterStack, wrapperAfterFinalStackRestore] using saved.code
  have machineStack := machine.mono agreeStack retiredStackPresent
  have atReturn : afterStack.regs.get? PC = some (BitVec.ofNat 64 0x10378) := by
    simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
      stackAddiNextState, tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert]
    decide
  have linkStack : afterStack.regs.get? x1 = some link := by
    simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
      stackAddiNextState, tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.ra]
  obtain ⟨retiredReturn, returnRun, pcReturn⟩ := wrapper_epilogue_return_step machineStack
    (Agree.refl afterStack) retiredStackPresent codeStack (fromStep + 4) atReturn link linkStack
    linkEven linkBit1
  let afterReturn := wrapperAfterReturn afterStack retiredReturn link
  refine ⟨afterReturn, ⟨?_, pcReturn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · trace_steps [(by simpa [afterStack] using stackRun), (by simpa [afterReturn] using returnRun)]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.ra]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.s0]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.s1]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.s2]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, restoredStackEq]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.a0]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.a1]
  · rfl
  · simpa [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore] using saved.code
  · have returnAgree : Agree decoderPreserved afterStack afterReturn :=
      Agree.weaken (fun _ preserved => preserved.2)
        ((jumpRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
    exact agreeStack.trans returnAgree
  · unfold RetiredCounterPresent
    simp [afterReturn, wrapperAfterReturn, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]

end BinaryFv.Zesu.MachineExecution
