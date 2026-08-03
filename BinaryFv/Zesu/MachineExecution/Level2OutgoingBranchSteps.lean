import BinaryFv.Zesu.MachineExecution.DecodeInlineProof

/-!
# Sail steps for Level 2's outgoing `decode` branches

The inlined Level 3 decoder deliberately stops at the source PCs of these edges.  This module owns
only the immediate wrapper instructions and keeps their semantic premises explicit.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exact post-state of the Level 2 propagation branch at `0x10380`. -/
def decodeInlinePropagateErrorBranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10380) (BitVec.ofNat 64 0x103fc))
    (BitVec.ofNat 64 0x103fc) retired

/-- A propagated non-`invalidSsz` error has a tag different from the retry tag `2`, so Level 2
retires the real `bne a0, a1, 0x103fc` edge through Sail. -/
theorem decodeInline_propagate_error_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (error : Contracts.DecodeError)
    (phase : args.phase = .propagateError error) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlinePropagateErrorBranchAfter state retired) false ∧
      (decodeInlinePropagateErrorBranchAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x103fc) := by
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10380) := by
    simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry
  have pcIn := decodeInline_owned_in_execution_region (0x10380, 0x06b51e63)
    (by simp [decodeInlineOwnedInstructionWords])
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10380) 0x63#8 0x1e#8 0xb5#8 0x06#8 :=
    fetchFileInstruction state 0x10380 0x63 0x1e 0xb5 0x06 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine (Agree.refl state)
    (BitVec.ofNat 64 0x10380) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters pre.machine.normal (Agree.refl state) pre.machine.retiredCounter
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have wordEq : fetchWord 0x63#8 0x1e#8 0xb5#8 0x06#8 =
      (0x06b51e63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x1e#8 0xb5#8 0x06#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x7c#13, .Regidx 11#5, .Regidx 10#5, .BNE)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10380)
  obtain ⟨notInvalid, -, tagA0, tagA1⟩ := pre.propagateReason error phase
  have x10AtExecute : executeState.regs.get? x10 =
      some (BitVec.ofNat 64 (decodeInternalResultTag (.error error))) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tagA0]
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 2) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tagA1]
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BNE)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState _ x11AtExecute) ?_
    have bitsNe : BitVec.ofNat 64 (decodeInternalResultTag (.error error)) ≠ 2#64 := by
      cases error <;> simp [decodeInternalResultTag] at notInvalid ⊢
    have comparison : (BitVec.ofNat 64 (decodeInternalResultTag (.error error)) != 2#64) = true :=
      bne_iff_ne.mpr bitsNe
    rw [comparison]
    rfl
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x10380) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have targetEq : BitVec.ofNat 64 0x10380 + sign_extend (m := 64) (0x7c#13) =
      BitVec.ofNat 64 0x103fc := by decide
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      state.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := pre.machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match read : state.regs.get? misa with
    | none => simp [read] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [read] using normalMisa⟩
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x10380)
    misaBits misaRead
  have run := tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x10380)
    (BitVec.ofNat 64 0x10380) retired (0x7c#13) (.Regidx 11#5) (.Regidx 10#5) .BNE
    inhibit config 0x63#8 0x1e#8 0xb5#8 0x06#8 (_get_Misa_C misaBits == 1#1)
    fetch noMMIO fetchBytes interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected condition (readReg_run executeState PC _ pcAtExecute)
    (by decide) (by decide) zca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [decodeInlinePropagateErrorBranchAfter, targetEq] using run
  · simp [decodeInlinePropagateErrorBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

end BinaryFv.Zesu.MachineExecution
