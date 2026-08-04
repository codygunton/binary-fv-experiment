import BinaryFv.Zesu.MachineExecution.Level2FirstSuccessAdapter
import BinaryFv.Zesu.MachineExecution.Level2Tag0PostCopy
import BinaryFv.Zesu.MachineExecution.Level2WrapperRestoreAddresses
import BinaryFv.Zesu.MachineExecution.Level2Capstone

/-! The tag-zero stored-result copy followed by the wrapper-owned exit suffix. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The complete tag-zero suffix from the stored-result-copy entry to the generated wrapper exit.
The `scopedTrace` field retains wrapper ownership while `trace` retains the flat Sail run. -/
structure Tag0CopyToExitResult (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (entry before callState afterCopy routeAfter afterStore after : State) (contents : ByteArray)
    (link savedS0 savedS1 savedS2 : BitVec 64) (fromStep used : Nat) : Prop where
  copy : Tag0StoredResultCopyPhase args stackBase entry before contents link savedS0 savedS1 savedS2
    fromStep used callState afterCopy
  postcopy : Tag0PostcopyResult afterCopy afterCopy routeAfter (fromStep + 6 + used) contents
    (BitVec.ofNat 64 stackBase) link savedS0 savedS1 savedS2
  store : Runs (try_step (fromStep + 6 + used + 3) false) routeAfter afterStore false
  epilogue : WrapperEpilogueExitResult (fromStep + 6 + used + 4) afterCopy afterStore after
    link savedS0 savedS1 savedS2 (BitVec.ofNat 64 (stackBase + 0xa20))
    (BitVec.ofNat 64 1) (BitVec.ofNat 64 1)
  trace : Trace fromStep (16 + used) before after
  scopedTrace : ScopedTrace
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep (16 + used) before after

/-- Compose a stored-result-copy phase through its three tag-zero instructions, status store, and
the six wrapper-owned epilogue instructions, stopping at the generated `ret` at `0x10378`. -/
theorem tag0_copy_to_exit
    {args : ZesuDecodeRawArgs} {stackBase fromStep used : Nat}
    {entry before callState afterCopy : State} (contents : ByteArray)
    (link savedS0 savedS1 savedS2 : BitVec 64)
    (phase : Tag0StoredResultCopyPhase args stackBase entry before contents link savedS0 savedS1 savedS2
      fromStep used callState afterCopy) :
    ∃ routeAfter afterStore after,
      Tag0CopyToExitResult args stackBase entry before callState afterCopy routeAfter afterStore after
      contents link savedS0 savedS1 savedS2 fromStep used := by
  let stack := BitVec.ofNat 64 stackBase
  have stackNat : stack.toNat = stackBase := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have fits := phase.machineEntry.stackFrameFits
    omega
  have statusSlot : DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 0x4215370) 1 := by
    have statusSlotNat : (BitVec.ofNat 64 0x4215370).toNat = 0x4215370 := by native_decide
    rw [DecoderAccessRange, statusSlotNat]
    refine ⟨by decide, by decide, ?_⟩
    intro index indexBound
    right; left
    unfold DecoderGlobalsByte
    simp only [Elflings.GeneratedDecoderGlobals.bssBase,
      Elflings.GeneratedDecoderGlobals.bssSize]
    omega
  have payloadBeforeStack : 0x4215370 ≤ stack.toNat := by
    have separated := wrapper_stack_after_stored_result phase.machineEntry
    rw [stackNat]
    omega
  let pre : Tag0PostMemcpyPre afterCopy afterCopy (zesuDecodeRawMachineArgs args) :=
    { machine := phase.machine
      platform := Agree.refl afterCopy
      retired := phase.retired
      code := phase.code
      atPc := phase.atResume
      stack := stack
      stackValue := by simpa [stack] using phase.stack
      globalsValue := phase.globals
      statusSlot := statusSlot
      contents := contents
      payload := phase.destinationBytes
      payloadLength := phase.contentsSize
      link := link
      savedS0 := savedS0
      savedS1 := savedS1
      savedS2 := savedS2
      savedFrame := by simpa [stackNat] using phase.savedFrame
      payloadBeforeStack := payloadBeforeStack }
  obtain ⟨routeAfter, postcopy⟩ := tag0_postcopy_complete pre (fromStep + 6 + used)
  let restore := wrapperRestoreAddresses_of_machinePre args stackBase entry phase.machineEntry
  obtain ⟨afterStore, after, store, routeTrace, epilogue⟩ :=
    wrapper_dispatch_route_through_exit pre.machine (fromStep + 6 + used) 3
      (BitVec.ofNat 64 1) (BitVec.ofNat 64 1) link savedS0 savedS1 savedS2 stack
      (BitVec.ofNat 64 (stackBase + 0xa20)) postcopy.terminal postcopy.savedFrame
      (by simpa [stackNat] using phase.machineEntry.stackAvoidsStatusGlobals)
      postcopy.globalsValue postcopy.stackValue
      restore.raAddress restore.s0Address restore.s1Address restore.s2Address
      restore.raAddressEq restore.s0AddressEq restore.s1AddressEq restore.s2AddressEq
      restore.raAddressNat restore.s0AddressNat restore.s1AddressNat restore.s2AddressNat
      restore.raAligned restore.s0Aligned restore.s1Aligned restore.s2Aligned
      restore.raAllowed restore.s0Allowed restore.s1Allowed restore.s2Allowed
      (by simpa [stack] using wrapper_final_stack_address stackBase)
  have statusConfined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 6 + used + 3) 1 routeAfter afterStore :=
    ConfinedPrefix.ownStep postcopy.atTerminal (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) store
  have finalExit : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 6 + used + 10) 0 after after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x10378) epilogue.pc (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw])
  have tail : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 6 + used) 10 afterCopy after := by
    have afterPostcopy : ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (fromStep + 6 + used + 3) 7 routeAfter after := by
      have afterEpilogue : ScopedTrace
          (functionInstanceExecutionPcs generatedProgram
            functionInstance_raw_decoder_root_zesu_decode_raw)
          (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
          Level2ChildSummary (fromStep + 6 + used + 4) 6 afterStore after := by
        exact epilogue.confined 0 after (by simpa [Nat.add_assoc] using finalExit)
      exact statusConfined 6 after (by simpa [Nat.add_assoc] using afterEpilogue)
    exact postcopy.confined 7 after (by simpa [Nat.add_assoc] using afterPostcopy)
  have scopedTrace : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep (6 + used + 10) before after := by
    exact phase.scopedPrefix 10 after (by simpa [Nat.add_assoc] using tail)
  refine ⟨routeAfter, afterStore, after, ?_⟩
  refine ⟨phase, postcopy, store, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, stack] using epilogue
  · have flat : Trace (fromStep + 6 + used) 10 afterCopy after := by
      simpa using routeTrace
    have flat' : Trace (fromStep + (6 + used)) 10 afterCopy after := by
      simpa [Nat.add_assoc] using flat
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Trace.append phase.trace flat'
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using scopedTrace

end BinaryFv.Zesu.MachineExecution
