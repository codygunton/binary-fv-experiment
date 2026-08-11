import BinaryFv.Zesu.MachineExecution.Level2RetryRejectionToDispatch
import BinaryFv.Zesu.MachineExecution.Level2WrapperRestoreAddresses
import BinaryFv.Zesu.MachineExecution.Level2Capstone
import BinaryFv.Zesu.MachineExecution.OwnedPc

/-! The common retry-rejection tail through the generated wrapper exit. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The retry rejection suffix executes its two-instruction handoff, common status store, and six
epilogue instructions, stopping at the generated `ret` at `0x10378`. -/
structure RetryRejectionToExitResult (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (entry base before afterTail afterStore after : State) (fromStep : Nat)
    (link savedS0 savedS1 savedS2 : BitVec 64) : Prop where
  tail : RetryRejectionToStatusStore base before afterTail (zesuDecodeRawMachineArgs args) fromStep
  store : Runs (try_step (fromStep + 2) false) afterTail afterStore false
  restoreFacts : Nonempty
    (WrapperRestoreAddresses (zesuDecodeRawMachineArgs args) (BitVec.ofNat 64 stackBase))
  epilogue : WrapperEpilogueExitResult (fromStep + 3) base afterStore after link savedS0 savedS1
    savedS2 (BitVec.ofNat 64 (stackBase + 0xa20)) (BitVec.ofNat 64 0) (BitVec.ofNat 64 2)
  trace : Trace fromStep 9 before after
  confined : WrapperPrefix fromStep 9 before after
  scopedTrace : WrapperScopedTrace fromStep 9 before after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  a0 : after.regs.get? x10 = some (BitVec.ofNat 64 0)
  a1 : after.regs.get? x11 = some (BitVec.ofNat 64 2)
  sp : after.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0xa20))
  globals : after.regs.get? x18 = some savedS2
  savedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 afterTail
  memory : after.mem = afterStore.mem
  statusWord : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status 2
  globalsFrame : DecoderGlobalsBoundaryFrame before after
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after
  inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes

/-- Compose the common retry-rejection handoff with the status store and epilogue exit.  Restore
addresses and access permissions come from the entered wrapper frame; the current saved frame is
transported through the handoff and status store, rather than supplied as an ABI premise. -/
theorem retry_rejection_to_exit
    {args : ZesuDecodeRawArgs} {stackBase fromStep : Nat} {entry base before : State}
    (machineEntry : ZesuDecodeRawMachinePre args stackBase entry)
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (zesuDecodeRawMachineArgs args) base)
    (agree : Agree platformPreserved base before) (retired : RetiredCounterPresent before)
    (code : canonicalContractParams.env.CodeIntact before)
    (atPc : before.regs.get? PC = some (BitVec.ofNat 64 0x10420))
    (stack : before.regs.get? x2 = some (BitVec.ofNat 64 stackBase))
    (globals : before.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (status : before.regs.get? x11 = some (BitVec.ofNat 64 2))
    (inputMemory : DecodedValue.MemoryBytes before args.inputBase args.bytes)
    (link savedS0 savedS1 savedS2 : BitVec 64)
    (savedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 before) :
    ∃ afterTail afterStore after,
      RetryRejectionToExitResult args stackBase entry base before afterTail afterStore after fromStep
        link savedS0 savedS1 savedS2 := by
  obtain ⟨afterTail, tail⟩ := retry_rejection_to_status_store machine agree retired code fromStep atPc
  have tailStatus : afterTail.regs.get? x11 = some (BitVec.ofNat 64 2) := by
    rw [tail.statusValue]
    exact status
  have tailStack : afterTail.regs.get? x2 = some (BitVec.ofNat 64 stackBase) := by
    rw [tail.stackValue]
    exact stack
  have tailGlobals : afterTail.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    rw [tail.globalsValue]
    exact globals
  have tailFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 afterTail :=
    WrapperSavedRegisterFrame.of_mem_eq savedFrame tail.memory
  have stackNat : (BitVec.ofNat 64 stackBase).toNat = stackBase := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have fits := machineEntry.stackFrameFits
    omega
  let route : WrapperTerminalRouteFrame base before afterTail fromStep 2
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 2) :=
    { trace := tail.trace
      atTerminal := tail.atStatusStore
      resultValue := tail.resultValue
      statusValue := tailStatus
      platform := tail.platform
      code := tail.code
      retired := tail.retired }
  let restore := wrapperRestoreAddresses_of_machinePre args stackBase entry machineEntry
  obtain ⟨afterStore, after, store, trace, epilogue, exitGlobals⟩ :=
    wrapper_dispatch_route_through_exit_with_globals machine fromStep 2 (BitVec.ofNat 64 0) (BitVec.ofNat 64 2)
      link savedS0 savedS1 savedS2 (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 (stackBase + 0xa20))
      route (by simpa [stackNat] using tailFrame)
      (by simpa [stackNat] using machineEntry.stackAvoidsStatusGlobals) tailGlobals tailStack
      restore.raAddress restore.s0Address restore.s1Address restore.s2Address
      restore.raAddressEq restore.s0AddressEq restore.s1AddressEq restore.s2AddressEq
      restore.facts.raAddressNat restore.facts.s0AddressNat restore.facts.s1AddressNat restore.facts.s2AddressNat
      restore.facts.raAligned restore.facts.s0Aligned restore.facts.s1Aligned restore.facts.s2Aligned
      restore.facts.raAllowed restore.facts.s0Allowed restore.facts.s1Allowed restore.facts.s2Allowed
      (by simpa using wrapper_final_stack_address stackBase)
  have statusConfined : WrapperPrefix (fromStep + 2) 1 afterTail afterStore :=
    ConfinedPrefix.ownStep' tail.atStatusStore store
  have finalExit : WrapperScopedTrace (fromStep + 9) 0 after after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x10378) epilogue.pc (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw])
  have suffix : WrapperScopedTrace (fromStep + 2) 7 afterTail after := by
    have epilogueTrace : WrapperScopedTrace (fromStep + 3) 6 afterStore after :=
      epilogue.confined 0 after (by simpa [Nat.add_assoc] using finalExit)
    exact statusConfined 6 after (by simpa [Nat.add_assoc] using epilogueTrace)
  have scopedTrace : WrapperScopedTrace fromStep 9 before after :=
    tail.confined 7 after (by simpa [Nat.add_assoc] using suffix)
  have confined : WrapperPrefix fromStep 9 before after := by
    have epilogueConfined : WrapperPrefix (fromStep + 3) 6 afterStore after := epilogue.confined
    confined_steps [tail.confined, statusConfined, epilogueConfined]
  have globalsFrame : DecoderGlobalsBoundaryFrame before after := by
    constructor
    · rw [exitGlobals.boundaryFrame.1, tail.memory]
    · rw [exitGlobals.boundaryFrame.2, tail.memory]
  have finalInputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes := by
    have tailInput : DecodedValue.MemoryBytes afterTail args.inputBase args.bytes :=
      inputMemory.of_mem_eq (fun _ _ => by rw [tail.memory])
    intro index indexBound
    rw [exitGlobals.memoryOutsideStatus (args.inputBase + index) (by
      rcases machineEntry.inputAvoidsDecoderGlobals with inputBefore | globalsBefore
      · left
        have statusInGlobals : Elflings.GeneratedDecoderGlobals.bssBase ≤ 0x4215024 := by
          native_decide
        omega
      · right
        have statusEndInGlobals : 0x4215028 ≤ Elflings.GeneratedDecoderGlobals.bssBase +
            Elflings.GeneratedDecoderGlobals.bssSize := by native_decide
        omega)]
    exact tailInput index indexBound
  refine ⟨afterTail, afterStore, after, ?_⟩
  exact ⟨tail, store, ⟨restore⟩, epilogue, by simpa [Nat.add_assoc] using trace, confined, scopedTrace,
    epilogue.pc, epilogue.a0, epilogue.a1, epilogue.sp, epilogue.s2, tailFrame, epilogue.memory,
    by simpa using exitGlobals.statusWord, globalsFrame, epilogue.code, epilogue.retired,
    finalInputMemory⟩

end BinaryFv.Zesu.MachineExecution
