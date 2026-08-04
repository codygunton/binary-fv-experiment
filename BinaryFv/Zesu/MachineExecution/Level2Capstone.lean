import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch
import BinaryFv.Zesu.MachineExecution.Level2Epilogue

/-!
# Level 2 wrapper dispatch-to-return composition

This module joins a concrete outcome-dispatch route to the common status store and epilogue.  It
keeps the route trace, the real store step, and the restored caller frame visible; it introduces no
callable interface for either inlined child.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The concrete `sw a1, 4(s2)` cannot touch any of the four saved wrapper words. -/
theorem wrapper_epilogue_status_store_preserves_saved_frame
    (state : State) (retired status : BitVec 64) (stackBase : Nat)
    (link savedS0 savedS1 savedS2 : BitVec 64)
    (frame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 state)
    (stackAvoidsStatusGlobals : stackBase + 0xa20 ≤ 0x4215020 ∨ 0x4215028 ≤ stackBase) :
    WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2
      (wrapperAfterStatusStore state retired (BitVec.ofNat 64 0x4215024) status) := by
  have preserveSlot (offset : Nat) (offsetBound : offset + 8 ≤ 0xa20)
      (value : BitVec 64) (saved : SavedWordBytes state (stackBase + offset) value) :
      SavedWordBytes
        (wrapperAfterStatusStore state retired (BitVec.ofNat 64 0x4215024) status)
        (stackBase + offset) value := by
    intro index indexBound
    have indexLt : index < 8 := by
      rw [BinaryFv.RiscV.Sep.leBytes_length] at indexBound
      exact indexBound
    have outside : ∀ storeIndex : Fin 4,
        0x4215024 + storeIndex.val ≠ stackBase + offset + index := by
      intro storeIndex equal
      rcases stackAvoidsStatusGlobals with below | above <;> omega
    have preserved := afterWriteBytes_mem_get?_of_outside
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x1035c)) 0x4215024
      (Sail.BitVec.extractLsb status 31 0) (stackBase + offset + index) outside
    have preservedState :
        (wrapperAfterStatusStore state retired (BitVec.ofNat 64 0x4215024) status).mem.get?
          (stackBase + offset + index) = state.mem.get? (stackBase + offset + index) := by
      simpa [wrapperAfterStatusStore, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement]
        using preserved
    exact preservedState.trans (saved index indexBound)
  rcases frame with ⟨linkFrame, s0Frame, s1Frame, s2Frame⟩
  exact ⟨preserveSlot 0xa18 (by omega) link linkFrame,
    preserveSlot 0xa10 (by omega) savedS0 s0Frame,
    preserveSlot 0xa08 (by omega) savedS1 s1Frame,
    preserveSlot 0xa00 (by omega) savedS2 s2Frame⟩

/-- Compose one already-selected result-tag route through the concrete status store and the seven
remaining epilogue instructions.  `s2` is fixed to the wrapper's generated globals base, so the
store target is exactly `0x4215024`; the saved-frame transport above proves that this store leaves
the caller-save words readable by the following loads. -/
theorem wrapper_dispatch_route_through_epilogue
    {base before routeAfter : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (fromStep routeSteps : Nat)
    (result status link savedS0 savedS1 savedS2 stack restoredStack : BitVec 64)
    (route : WrapperDispatchRouteFrame base before routeAfter fromStep routeSteps
      (BitVec.ofNat 64 0x1035c) result status)
    (savedFrame : WrapperSavedRegisterFrame stack.toNat link savedS0 savedS1 savedS2
      routeAfter)
    (stackAvoidsStatusGlobals : stack.toNat + 0xa20 ≤ 0x4215020 ∨ 0x4215028 ≤ stack.toNat)
    (s2Value : routeAfter.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (stackValue : routeAfter.regs.get? x2 = some stack)
    (raAddress s0Address s1Address s2Address : BitVec 64)
    (raAddressEq : (stack + sign_extend (m := 64) (0x230#12)) +
      sign_extend (m := 64) (0x7e8#12) = raAddress)
    (s0AddressEq : (stack + sign_extend (m := 64) (0x230#12)) +
      sign_extend (m := 64) (0x7e0#12) = s0Address)
    (s1AddressEq : (stack + sign_extend (m := 64) (0x230#12)) +
      sign_extend (m := 64) (0x7d8#12) = s1Address)
    (s2AddressEq : (stack + sign_extend (m := 64) (0x230#12)) +
      sign_extend (m := 64) (0x7d0#12) = s2Address)
    (raAddressNat : stack.toNat + 0xa18 = raAddress.toNat)
    (s0AddressNat : stack.toNat + 0xa10 = s0Address.toNat)
    (s1AddressNat : stack.toNat + 0xa08 = s1Address.toNat)
    (s2AddressNat : stack.toNat + 0xa00 = s2Address.toNat)
    (raAligned : is_aligned_vaddr (virtaddr.Virtaddr raAddress) 8 = true)
    (s0Aligned : is_aligned_vaddr (virtaddr.Virtaddr s0Address) 8 = true)
    (s1Aligned : is_aligned_vaddr (virtaddr.Virtaddr s1Address) 8 = true)
    (s2Aligned : is_aligned_vaddr (virtaddr.Virtaddr s2Address) 8 = true)
    (raAllowed : DecoderAccessRange (DecoderReadableByte machineArgs) raAddress 8)
    (s0Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s0Address 8)
    (s1Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s1Address 8)
    (s2Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s2Address 8)
    (restoredStackEq : (stack + sign_extend (m := 64) (0x230#12)) +
      sign_extend (m := 64) (0x7f0#12) = restoredStack)
    (linkEven : Sail.BitVec.update link 0 0#1 = link)
    (linkBit1 : Sail.BitVec.access link 1 = 0#1) :
    ∃ afterStore after,
      Runs (try_step (fromStep + routeSteps) false) routeAfter afterStore false ∧
      Trace fromStep (routeSteps + 8) before after ∧
      WrapperEpilogueCompleteResult (fromStep + routeSteps + 1) base afterStore after
        link savedS0 savedS1 savedS2 restoredStack result status := by
  have routeAgree : Agree decoderPreserved base routeAfter :=
    Agree.weaken (fun _ preserved => preserved.2) route.platform
  have statusTargetNat : (BitVec.ofNat 64 0x4215024).toNat = 0x4215024 := by native_decide
  obtain ⟨retired, statusStore⟩ := wrapper_epilogue_status_store_step machine routeAgree
    route.retired
    route.code (fromStep + routeSteps) route.atTerminal (BitVec.ofNat 64 0x4215020)
    (BitVec.ofNat 64 0x4215024) status s2Value route.statusValue (by decide) (by decide) (by
      refine ⟨by decide, by decide, ?_⟩
      intro index indexBound
      right; left
      unfold DecoderGlobalsByte
      rw [statusTargetNat]
      simp only [Elflings.GeneratedDecoderGlobals.bssBase,
        Elflings.GeneratedDecoderGlobals.bssSize]
      omega)
  let afterStore := wrapperAfterStatusStore routeAfter retired (BitVec.ofNat 64 0x4215024) status
  have storeFrame : WrapperSavedRegisterFrame stack.toNat link savedS0 savedS1 savedS2
      afterStore := by
    simpa [afterStore] using
      wrapper_epilogue_status_store_preserves_saved_frame routeAfter retired status
      stack.toNat link savedS0 savedS1 savedS2 savedFrame stackAvoidsStatusGlobals
  have storeAgree : Agree decoderPreserved base afterStore := by
    apply routeAgree.trans
    intro register preserved
    have notPc : PC ≠ register := by
      intro equal
      subst register
      simpa [decoderPreserved, platformPreserved] using preserved
    have notNextPc : nextPC ≠ register := by
      intro equal
      subst register
      simpa [decoderPreserved, platformPreserved] using preserved
    have notIncrement : minstret_increment ≠ register := by
      intro equal
      subst register
      simpa [decoderPreserved, platformPreserved] using preserved
    have notRetired : minstret ≠ register := by
      intro equal
      subst register
      simpa [decoderPreserved, platformPreserved] using preserved
    simp [afterStore, wrapperAfterStatusStore, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, afterWriteBytes_regs, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, notPc, notNextPc,
      notIncrement, notRetired]
  have storeRetired : RetiredCounterPresent afterStore := by
    refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
    simp [afterStore, wrapperAfterStatusStore, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]
  have storeCode : canonicalContractParams.env.CodeIntact afterStore := by
    have notFileBacked : ∀ index : Fin 4,
        Artifacts.programImage.readFileByte? (0x4215024 + index.val) = none := by
      native_decide
    have codeAtExecute : Artifacts.programImage.fileBytesMatchMemory
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement routeAfter)
          (BitVec.ofNat 64 0x1035c)).mem := by
      simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement] using route.code
    apply fileBytesMatchMemory_afterWriteBytes Artifacts.programImage
    · exact notFileBacked
    simpa [afterStore, wrapperAfterStatusStore, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterRetired] using codeAtExecute
  have storePc : afterStore.regs.get? PC = some (BitVec.ofNat 64 0x10360) := by
    simp [afterStore, wrapperAfterStatusStore, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have storeStack : afterStore.regs.get? x2 = some stack := by
    simpa [afterStore, wrapperAfterStatusStore, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, afterWriteBytes_regs, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert] using stackValue
  have storeResult : afterStore.regs.get? x10 = some result := by
    simpa [afterStore, wrapperAfterStatusStore, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, afterWriteBytes_regs, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert] using route.resultValue
  have storeStatus : afterStore.regs.get? x11 = some status := by
    simpa [afterStore, wrapperAfterStatusStore, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, afterWriteBytes_regs, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert] using route.statusValue
  obtain ⟨after, epilogue⟩ :=
    wrapper_epilogue_complete machine storeAgree storeRetired storeCode
    (fromStep + routeSteps + 1) storePc stack link savedS0 savedS1 savedS2 stack restoredStack result
    status raAddress s0Address s1Address s2Address storeFrame storeStack storeResult storeStatus
    raAddressEq s0AddressEq s1AddressEq s2AddressEq raAddressNat s0AddressNat s1AddressNat s2AddressNat
    raAligned s0Aligned s1Aligned s2Aligned raAllowed s0Allowed s1Allowed s2Allowed
    restoredStackEq
    linkEven linkBit1
  refine ⟨afterStore, after, ?_, ?_, ?_⟩
  · simpa [afterStore] using statusStore
  · simpa [Nat.add_assoc] using Trace.append route.trace
      (Trace.append (Trace.one (fromStep + routeSteps) routeAfter afterStore statusStore)
        epilogue.trace)
  exact epilogue

end BinaryFv.Zesu.MachineExecution
