import BinaryFv.Zesu.MachineExecution.Level2FirstSuccessAdapter
import BinaryFv.Zesu.MachineExecution.Level2Tag0PostCopy
import BinaryFv.Zesu.MachineExecution.Level2WrapperRestoreAddresses
import BinaryFv.Zesu.MachineExecution.Level2Capstone
import BinaryFv.Zesu.MachineExecution.OwnedPc

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
structure Tag0CopyToExitResult (args : ZesuDecodeRawArgs)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (stackBase : Nat)
    (entry before callState afterCopy routeAfter afterStore after : State) (contents : ByteArray)
    (link savedS0 savedS1 savedS2 : BitVec 64) (fromStep used : Nat) : Prop where
  copy : Tag0StoredResultCopyPhase args value stackBase entry before contents link savedS0 savedS1 savedS2
    fromStep used callState afterCopy
  postcopy : Tag0PostcopyResult afterCopy afterCopy routeAfter (fromStep + 6 + used) contents
    args.inputBase args.bytes value (BitVec.ofNat 64 stackBase) link savedS0 savedS1 savedS2
  store : Runs (try_step (fromStep + 6 + used + 3) false) routeAfter afterStore false
  epilogue : WrapperEpilogueExitResult (fromStep + 6 + used + 4) afterCopy afterStore after
    link savedS0 savedS1 savedS2 (BitVec.ofNat 64 (stackBase + 0xa20))
    (BitVec.ofNat 64 1) (BitVec.ofNat 64 1)
  trace : Trace fromStep (16 + used) before after
  scopedTrace : WrapperScopedTrace fromStep (16 + used) before after
  statusWord : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status 1
  globalsFrame : DecoderGlobalsBoundaryFrame routeAfter after
  inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes
  representation : ∃ cursorBefore cursorAfter,
    StatelessInputRepInHeapInterval after args.inputBase args.bytes 0x4215030 value
      cursorBefore cursorAfter
  attemptedFrame : after.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted =
    before.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted
  storedTag : DecodedValue.OptionTagRep after
    (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) true

/-- Compose a stored-result-copy phase through its three tag-zero instructions, status store, and
the six wrapper-owned epilogue instructions, stopping at the generated `ret` at `0x10378`. -/
theorem tag0_copy_to_exit
    {args : ZesuDecodeRawArgs} {value : BinaryFv.Specs.SSZ.StatelessInput}
    {stackBase fromStep used : Nat}
    {entry before callState afterCopy : State} (contents : ByteArray)
    (link savedS0 savedS1 savedS2 : BitVec 64)
    (phase : Tag0StoredResultCopyPhase args value stackBase entry before contents link savedS0 savedS1 savedS2
      fromStep used callState afterCopy) :
    ∃ routeAfter afterStore after,
      Tag0CopyToExitResult args value stackBase entry before callState afterCopy routeAfter afterStore after
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
  let pre : Tag0PostMemcpyPre afterCopy afterCopy (zesuDecodeRawMachineArgs args) value :=
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
      representation := phase.destinationRepresentation
      link := link
      savedS0 := savedS0
      savedS1 := savedS1
      savedS2 := savedS2
      savedFrame := by simpa [stackNat] using phase.savedFrame
      payloadBeforeStack := payloadBeforeStack
      inputMemory := phase.inputMemory
      inputAvoidsDecoderGlobals := phase.machineEntry.inputAvoidsDecoderGlobals }
  obtain ⟨routeAfter, postcopy⟩ := tag0_postcopy_complete pre (fromStep + 6 + used)
  let restore := wrapperRestoreAddresses_of_machinePre args stackBase entry phase.machineEntry
  obtain ⟨afterStore, after, store, routeTrace, epilogue, exitGlobals⟩ :=
    wrapper_dispatch_route_through_exit_with_globals pre.machine (fromStep + 6 + used) 3
      (BitVec.ofNat 64 1) (BitVec.ofNat 64 1) link savedS0 savedS1 savedS2 stack
      (BitVec.ofNat 64 (stackBase + 0xa20)) postcopy.terminal postcopy.savedFrame
      (by simpa [stackNat] using phase.machineEntry.stackAvoidsStatusGlobals)
      postcopy.globalsValue postcopy.stackValue
      restore.raAddress restore.s0Address restore.s1Address restore.s2Address
      restore.raAddressEq restore.s0AddressEq restore.s1AddressEq restore.s2AddressEq
      restore.facts.raAddressNat restore.facts.s0AddressNat restore.facts.s1AddressNat restore.facts.s2AddressNat
      restore.facts.raAligned restore.facts.s0Aligned restore.facts.s1Aligned restore.facts.s2Aligned
      restore.facts.raAllowed restore.facts.s0Allowed restore.facts.s1Allowed restore.facts.s2Allowed
      (by simpa [stack] using wrapper_final_stack_address stackBase)
  have statusConfined : WrapperPrefix (fromStep + 6 + used + 3) 1 routeAfter afterStore :=
    ConfinedPrefix.ownStep' postcopy.atTerminal store
  have finalExit : WrapperScopedTrace (fromStep + 6 + used + 10) 0 after after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x10378) epilogue.pc (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw])
  have tail : WrapperScopedTrace (fromStep + 6 + used) 10 afterCopy after := by
    have afterPostcopy : WrapperScopedTrace (fromStep + 6 + used + 3) 7 routeAfter after := by
      have afterEpilogue : WrapperScopedTrace (fromStep + 6 + used + 4) 6 afterStore after :=
        epilogue.confined 0 after (by simpa [Nat.add_assoc] using finalExit)
      exact statusConfined 6 after (by simpa [Nat.add_assoc] using afterEpilogue)
    exact postcopy.confined 7 after (by simpa [Nat.add_assoc] using afterPostcopy)
  have scopedTrace : WrapperScopedTrace fromStep (6 + used + 10) before after :=
    phase.scopedPrefix 10 after (by simpa [Nat.add_assoc] using tail)
  have inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes := by
    intro index indexBound
    have inputAvoids : args.inputBase + args.bytes.size ≤ Elflings.GeneratedDecoderGlobals.bssBase ∨
        Elflings.GeneratedDecoderGlobals.bssBase + Elflings.GeneratedDecoderGlobals.bssSize ≤
          args.inputBase := by
      simpa [zesuDecodeRawMachineArgs] using pre.inputAvoidsDecoderGlobals
    rw [exitGlobals.memoryOutsideStatus (args.inputBase + index) (by
      rcases inputAvoids with inputBefore | globalsBefore
      · left
        have statusInGlobals : Elflings.GeneratedDecoderGlobals.bssBase ≤ 0x4215024 := by
          native_decide
        omega
      · right
        have statusEndInGlobals : 0x4215028 ≤ Elflings.GeneratedDecoderGlobals.bssBase +
            Elflings.GeneratedDecoderGlobals.bssSize := by native_decide
        omega)]
    exact postcopy.inputMemory index indexBound
  obtain ⟨cursorBefore, cursorAfter, postcopyRepresentation, cursorBound⟩ :=
    postcopy.representation
  obtain ⟨bases, heapWithin, transportRepresentation⟩ := postcopyRepresentation.transport
  have finalRepresentation : StatelessInputRepInHeapInterval after args.inputBase args.bytes
      0x4215030 value cursorBefore cursorAfter := transportRepresentation (by
    intro address footprint
    symm
    apply exitGlobals.memoryOutsideStatus address
    rcases footprint with root | heap
    · right
      dsimp [range] at root
      omega
    · left
      have within := heapWithin address heap
      have heapBeforeStatus : Elflings.canonicalHeapLimit ≤ 0x4215024 := by native_decide
      omega)
  have attemptedFrame : after.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted =
      before.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted := by
    rw [exitGlobals.boundaryFrame.1, postcopy.attemptedFrame, phase.globalsFrame.1]
  have storedTag : DecodedValue.OptionTagRep after
      (Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) true := by
    change after.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) = some (1#8)
    rw [exitGlobals.boundaryFrame.2]
    exact postcopy.storedTag
  refine ⟨routeAfter, afterStore, after, ?_⟩
  refine ⟨phase, postcopy, store, ?_, ?_, ?_, by simpa using exitGlobals.statusWord,
    exitGlobals.boundaryFrame, inputMemory,
    ⟨cursorBefore, cursorAfter, finalRepresentation⟩, attemptedFrame, storedTag⟩
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, stack] using epilogue
  · have flat : Trace (fromStep + 6 + used) 10 afterCopy after := by
      simpa using routeTrace
    have flat' : Trace (fromStep + (6 + used)) 10 afterCopy after := by
      simpa [Nat.add_assoc] using flat
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Trace.append phase.trace flat'
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using scopedTrace

end BinaryFv.Zesu.MachineExecution
