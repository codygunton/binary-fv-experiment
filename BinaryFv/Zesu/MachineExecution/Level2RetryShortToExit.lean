import BinaryFv.Zesu.MachineExecution.Level2RetryRejectionAdapters
import BinaryFv.Zesu.MachineExecution.Level2RetryRejectionToExit

/-! The short retry rejection consumes its selected decoder body before the common wrapper exit. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated PreSail LeanRV64DExecutable.Functions Register

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The short retry rejection's selected Level 3 body, real branch, and nine-step wrapper suffix. -/
structure RetryShortRejectionToExitResult (args : DecodeInlineArgs) (fromStep used : Nat)
    (entry before childAfter handoff afterTail afterStore after : State) (link s0 s1 s2 : BitVec 64) : Prop where
  edge : RetryShortRejectionEdgeResult args fromStep used before childAfter handoff link s0 s1 s2
  suffix : RetryRejectionToExitResult ⟨args.inputBase, args.bytes⟩ args.stackBase entry handoff handoff
    afterTail afterStore after (fromStep + used + 1) link s0 s1 s2
  trace : Trace (fromStep + used) 10 childAfter after
  confined : ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary (fromStep + used) 10 childAfter after
  scopedTrace : ScopedTrace
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep (used + 10) before after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  a0 : after.regs.get? x10 = some (BitVec.ofNat 64 0)
  a1 : after.regs.get? x11 = some (BitVec.ofNat 64 2)
  sp : after.regs.get? x2 = some (BitVec.ofNat 64 (args.stackBase + 0xa20))
  globals : after.regs.get? x18 = some s2
  savedFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 afterTail
  memory : after.mem = afterStore.mem
  statusWord : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status 2
  globalsFrame : DecoderGlobalsBoundaryFrame before after
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after
  inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes

/-- Compose the short-input retry child with its real branch and common status-store/epilogue suffix.
The machine premise is transported from the wrapper entry to the checked handoff using proved
decoder-preserved agreement, rather than assuming preservation of the link register or a source ABI. -/
theorem retry_short_rejection_to_exit
    {args : DecodeInlineArgs} {fromStep : Nat} {entry before : State}
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs before)
    (pre : DecodeInlinePre args before) (phase : args.phase = .retryAfterInvalidSsz)
    (short : args.bytes.size < 4) (link s0 s1 s2 : BitVec 64)
    (saved : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 before) :
    ∃ used childAfter handoff afterTail afterStore after,
      RetryShortRejectionToExitResult args fromStep used entry before childAfter handoff afterTail afterStore
        after link s0 s1 s2 := by
  obtain ⟨used, childAfter, handoff, edge⟩ :=
    retry_short_rejection_edge fromStep args before pre phase short link s0 s1 s2 saved
  have handoffMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs handoff :=
    DecoderMachinePre.mono edge.handoffAgree edge.handoffRetired machine
  obtain ⟨afterTail, afterStore, after, suffix⟩ := retry_rejection_to_exit machineEntry handoffMachine
    (Agree.refl _) edge.handoffRetired edge.handoffCode edge.branchPc edge.handoffStack edge.handoffGlobals
    edge.handoffStatus edge.inputMemory link s0 s1 s2 edge.handoffFrame
  have residualScoped : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + used) 10 childAfter after :=
    edge.branchPrefix 9 after (by simpa [Nat.add_assoc] using suffix.scopedTrace)
  have scopedTrace : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep (used + 10) before after :=
    ScopedTrace.childBody fromStep used 10
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id before childAfter after
      (Level2ChildSummary.decode edge.child) (by simpa [Nat.add_assoc] using residualScoped)
  have confined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + used) 10 childAfter after := by
    exact ConfinedPrefix.trans edge.branchPrefix (by simpa [Nat.add_assoc] using suffix.confined)
  have globalsFrame : DecoderGlobalsBoundaryFrame before after := by
    constructor
    · rw [suffix.globalsFrame.1, edge.globalsFrame.1]
    · rw [suffix.globalsFrame.2, edge.globalsFrame.2]
  refine ⟨used, childAfter, handoff, afterTail, afterStore, after, ?_⟩
  exact ⟨edge, suffix,
    by simpa [Nat.add_assoc] using
      Trace.append (Trace.one (fromStep + used) childAfter _ edge.branch) suffix.trace,
    confined, scopedTrace, suffix.pc, suffix.a0, suffix.a1, suffix.sp, suffix.globals,
    suffix.savedFrame, suffix.memory, suffix.statusWord, globalsFrame, suffix.code, suffix.retired,
    suffix.inputMemory⟩

end BinaryFv.Zesu.MachineExecution
