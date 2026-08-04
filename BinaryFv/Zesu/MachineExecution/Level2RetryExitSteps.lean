import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryFinish

/-!
# Sail steps for the retry exits owned by `zesu_decode_raw`

The Level 3 `decode` contract stops before these two rejection branches. This module consumes its
outgoing frame and executes their real wrapper instructions through Sail. The exact-prefix
result-tag load at `0x103f8` is the next retry-exit phase.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.ProgramImage BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep
open BinaryFv.RiscV.Sep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def decodeInlineRetryShortBranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10394) (BitVec.ofNat 64 0x10420))
    (BitVec.ofNat 64 0x10420) retired

/-- A short retry input takes the wrapper's `bltu a2, a0, 0x10420` exit. -/
theorem retry_short_length_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (before state : State) (pre : DecodeInlinePre args before)
    (frame : DecodeInlineMachinePost before state)
    (outgoing : DecodeInlineOutgoingFrame args state)
    (phase : args.phase = .retryAfterInvalidSsz) (short : args.bytes.size < 4)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10394)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlineRetryShortBranchAfter state retired) false ∧
      (decodeInlineRetryShortBranchAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10420) := by
  have prefixFalse : Contracts.meaningHasExactErePrefix args.bytes = false :=
    meaningHasExactErePrefix_false_of_size_lt_four args.bytes short
  have values : state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) ∧
      state.regs.get? x12 = some
        (BitVec.ofNat 64 (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4))) := by
    simpa [DecodeInlineOutgoingFrame, phase, prefixFalse, short] using outgoing
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x10394) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact frame.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10394) 0x63#8 0x66#8 0xa6#8 0x08#8 :=
    fetchFileInstruction state 0x10394 0x63 0x66 0xa6 0x08 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have machine := pre.machine.mono frame.agree frame.retiredCounter
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x10394) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal (Agree.refl state) frame.retiredCounter
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x66#8 0xa6#8 0x08#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x8c#13, .Regidx 10#5, .Regidx 12#5, .BLTU)) := by
    change Runs (ext_decode (0x08a66663 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10394)
  have x10AtExecute : executeState.regs.get? x10 =
      some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, values.1]
  have x12AtExecute : executeState.regs.get? x12 = some
      (BitVec.ofNat 64 (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4))) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, values.2]
  have condition : Runs (bTypeTaken (.Regidx 10#5) (.Regidx 12#5) .BLTU)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_x12_run executeState _ x12AtExecute) ?_
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    have sizeBound : args.bytes.size < 2 ^ 32 := by
      have := pre.rootInputBound
      omega
    have leftFits : args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4) < 2 ^ 64 := by omega
    have rightFits : 2 ^ 64 - 2 ^ 32 < 2 ^ 64 := by omega
    simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt leftFits, Nat.mod_eq_of_lt rightFits]
    have comparison :
        (Int.ofNat (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4)) <b
          Int.ofNat (2 ^ 64 - 2 ^ 32)) = true := by
      simp only [decide_eq_true_eq]
      exact Int.ofNat_lt.mpr (by omega)
    rw [comparison]
    rfl
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x10394) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have targetEq : BitVec.ofNat 64 0x10394 + sign_extend (m := 64) (0x8c#13) =
      BitVec.ofNat 64 0x10420 := by decide
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      state.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match read : state.regs.get? misa with
    | none => simp [read] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [read] using normalMisa⟩
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x10394)
    misaBits misaRead
  have run := tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x10394)
    (BitVec.ofNat 64 0x10394) retired (0x8c#13) (.Regidx 10#5) (.Regidx 12#5) .BLTU
    inhibit config 0x63#8 0x66#8 0xa6#8 0x08#8 (_get_Misa_C misaBits == 1#1)
    fetch noMMIO fetchBytes interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected condition (readReg_run executeState PC _ pcAtExecute)
    (by decide) (by decide) zca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [decodeInlineRetryShortBranchAfter, targetEq] using run
  · simp [decodeInlineRetryShortBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- A mismatched four-byte framing word takes the wrapper's `bne a3, a0, 0x10420` exit. -/
theorem retry_prefix_mismatch_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (before state : State) (pre : DecodeInlinePre args before)
    (frame : DecodeInlineMachinePost before state)
    (outgoing : DecodeInlineOutgoingFrame args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size)
    (notExact : Contracts.meaningHasExactErePrefix args.bytes = false)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103c4)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlineRetryPrefixBranchTaken state retired) false ∧
      (decodeInlineRetryPrefixBranchTaken state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10420) := by
  have values : state.regs.get? x10 = some
      (BitVec.ofNat 64 (prefixHigh16 args.bytes) |||
        BitVec.ofNat 64 (prefixLow16 args.bytes)) ∧
      state.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4)) := by
    simp only [DecodeInlineOutgoingFrame, phase, notExact, Bool.false_eq_true, ↓reduceIte,
      show ¬ args.bytes.size < 4 by omega] at outgoing
    exact outgoing
  obtain ⟨declared, read, assembly, declaredBound⟩ :=
    prefix_halves_or_eq_readU32LE args.bytes fourBytes
  have declaredRead : state.regs.get? x10 = some (BitVec.ofNat 64 declared) := by
    rw [← assembly]
    exact values.1
  have different : declared ≠ args.bytes.size - 4 :=
    prefix_declared_ne_of_meaning_false args.bytes declared fourBytes read notExact
  obtain ⟨retired, run, atTarget, -, -, -⟩ :=
    decodeInline_retry_prefix_branch_taken stepNo args before state pre frame.agree
      frame.retiredCounter frame.code atPc declared declaredBound declaredRead values.2 different
  exact ⟨retired, run, atTarget⟩

end BinaryFv.Zesu.MachineExecution
