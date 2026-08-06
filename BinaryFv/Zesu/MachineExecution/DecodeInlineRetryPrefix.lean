import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof

/-!
# Framing-word arithmetic and the retry-path prefix branch at `0x103c4`

The retry exits these facts select are executed by Level 2, not by the inlined `decode` scope, and
neither the little-endian framing-word arithmetic nor the `bne a3, a0, 0x10420` step needs anything
from `DecodeInlineProof`: both are stated against the generic instruction-class steps and the pinned
image alone. Splitting them out stops `Level2RetryExitSteps`, and with it the whole Level 2
outcome-dispatch spine, from waiting on `DecodeInlineProof`'s single-core segment; `DecodeInlineProof`
imports this module, so every existing reference resolves unchanged.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep
open BinaryFv.RiscV.Sep

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- An input shorter than the four-byte framing word cannot have an exact ERE prefix. -/
theorem meaningHasExactErePrefix_false_of_size_lt_four (bytes : ByteArray)
    (short : bytes.size < 4) : Contracts.meaningHasExactErePrefix bytes = false := by
  simp [Contracts.meaningHasExactErePrefix, BinaryFv.Specs.SSZ.readU32LE?, short]

/-- The two child-produced halves are exactly the framing reader's little-endian `u32`. -/
theorem prefix_halves_or_eq_readU32LE (bytes : ByteArray) (fourBytes : 4 ≤ bytes.size) :
    ∃ declared,
      BinaryFv.Specs.SSZ.readU32LE? bytes 0 = some declared ∧
      BitVec.ofNat 64 (prefixHigh16 bytes) ||| BitVec.ofNat 64 (prefixLow16 bytes) =
        BitVec.ofNat 64 declared ∧
      declared < 2 ^ 32 := by
  let byte0 := bytes.get! 0
  let byte1 := bytes.get! 1
  let byte2 := bytes.get! 2
  let byte3 := bytes.get! 3
  let declared := byte0.toNat + byte1.toNat * 2 ^ 8 +
    byte2.toNat * 2 ^ 16 + byte3.toNat * 2 ^ 24
  refine ⟨declared, ?_, ?_, ?_⟩
  · rw [BinaryFv.Specs.SSZ.readU32LE?, if_neg (by omega)]
  · have assembly := prefixHalvesAssemblyValue
      (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
      (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
    dsimp [prefixLow16, prefixHigh16, declared, byte0, byte1, byte2, byte3]
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)] using assembly
  · have bound0 := UInt8.toNat_lt byte0
    have bound1 := UInt8.toNat_lt byte1
    have bound2 := UInt8.toNat_lt byte2
    have bound3 := UInt8.toNat_lt byte3
    dsimp [declared]
    omega

theorem prefix_declared_eq_of_meaning_true (bytes : ByteArray) (declared : Nat)
    (read : BinaryFv.Specs.SSZ.readU32LE? bytes 0 = some declared)
    (exactPrefix : Contracts.meaningHasExactErePrefix bytes = true) :
    declared = bytes.size - 4 := by
  rw [Contracts.meaningHasExactErePrefix, read] at exactPrefix
  simp only [Bool.and_eq_true, decide_eq_true_eq] at exactPrefix
  exact beq_iff_eq.mp exactPrefix.2

theorem prefix_declared_ne_of_meaning_false (bytes : ByteArray) (declared : Nat)
    (fourBytes : 4 ≤ bytes.size)
    (read : BinaryFv.Specs.SSZ.readU32LE? bytes 0 = some declared)
    (notExact : Contracts.meaningHasExactErePrefix bytes = false) :
    declared ≠ bytes.size - 4 := by
  intro equal
  rw [Contracts.meaningHasExactErePrefix, read] at notExact
  simp [fourBytes, equal] at notExact

def decodeInlineRetryPrefixBranchFallThrough (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103c4))
    (BitVec.ofNat 64 0x103c8) retired

/-- Execute `bne a3, a0, 0x10420` as not taken when the framing word equals `bytes.size - 4`. -/
theorem decodeInline_retry_prefix_branch_not_taken (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103c4))
    (declared : Nat) (declaredRead : state.regs.get? x10 = some (BitVec.ofNat 64 declared))
    (lengthRead : state.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4)))
    (equal : declared = args.bytes.size - 4) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlineRetryPrefixBranchFallThrough state retired) false ∧
      (decodeInlineRetryPrefixBranchFallThrough state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x103c8) ∧
      Agree decoderPreserved state (decodeInlineRetryPrefixBranchFallThrough state retired) ∧
      RetiredCounterPresent (decodeInlineRetryPrefixBranchFallThrough state retired) ∧
      (decodeInlineRetryPrefixBranchFallThrough state retired).mem = state.mem := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  obtain ⟨retired, run⟩ := decoderBranchNotTakenStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x103c4 0x63 0x9e 0xa6 0x04 0x5c#13 10#5 13#5 .BNE atPc
    (by unfold bTypeTaken
        refine Runs.bind (rX_x13_run _ _ (decoderExecuteState_get? lengthRead)) ?_
        refine Runs.bind (rX_bits_run_x10 _ _ (decoderExecuteState_get? declaredRead)) ?_
        simp [equal]
        rfl)
  refine ⟨retired, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [decodeInlineRetryPrefixBranchFallThrough] using run
  · simp [decodeInlineRetryPrefixBranchFallThrough, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  · exact Agree.weaken (fun _ preserved => preserved.2)
      ((fallThroughRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
  · refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
    simp [decodeInlineRetryPrefixBranchFallThrough, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]

def decodeInlineRetryPrefixBranchTaken (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103c4) (BitVec.ofNat 64 0x10420))
    (BitVec.ofNat 64 0x10420) retired

/-- Execute `bne a3, a0, 0x10420` as taken when the framing word differs from `bytes.size - 4`. -/
theorem decodeInline_retry_prefix_branch_taken (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103c4))
    (declared : Nat) (declaredBound : declared < 2 ^ 32)
    (declaredRead : state.regs.get? x10 = some (BitVec.ofNat 64 declared))
    (lengthRead : state.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4)))
    (different : declared ≠ args.bytes.size - 4) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlineRetryPrefixBranchTaken state retired) false ∧
      (decodeInlineRetryPrefixBranchTaken state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10420) ∧
      Agree decoderPreserved state (decodeInlineRetryPrefixBranchTaken state retired) ∧
      RetiredCounterPresent (decodeInlineRetryPrefixBranchTaken state retired) ∧
      (decodeInlineRetryPrefixBranchTaken state retired).mem = state.mem := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContextOfDecoderAgree machine (Agree.refl state)
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103c4)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 declared) :=
    decoderExecuteState_get? declaredRead
  have x13AtExecute : executeState.regs.get? x13 =
      some (BitVec.ofNat 64 (args.bytes.size - 4)) :=
    decoderExecuteState_get? lengthRead
  have lengthBound : args.bytes.size - 4 < 2 ^ 64 := by
    have := pre.rootInputBound
    omega
  have bitsDifferent : BitVec.ofNat 64 (args.bytes.size - 4) ≠
      BitVec.ofNat 64 declared := by
    intro equalBits
    apply different
    have declaredBound64 : declared < 2 ^ 64 := by omega
    have equalNat : args.bytes.size - 4 = declared := by
      rw [← Nat.mod_eq_of_lt lengthBound, ← Nat.mod_eq_of_lt declaredBound64]
      exact congrArg BitVec.toNat equalBits
    exact equalNat.symm
  have condition : Runs (bTypeTaken (.Regidx 10#5) (.Regidx 13#5) .BNE)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_x13_run executeState _ x13AtExecute) ?_
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    have comparison : (BitVec.ofNat 64 (args.bytes.size - 4) !=
        BitVec.ofNat 64 declared) = true := bne_iff_ne.mpr bitsDifferent
    rw [comparison]
    rfl
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) state
      (decodeInlineRetryPrefixBranchTaken state retired) false :=
    decoderBranchTakenStep machine (Agree.refl state) retiredPresent
      (hasExactErePrefix_programImage_of_codeIntact code)
      stepNo 0x103c4 0x63 0x9e 0xa6 0x04 0x5c#13 10#5 13#5 .BNE (BitVec.ofNat 64 0x10420)
      atPc condition
  refine ⟨retired, run, ?_, ?_, ?_, rfl⟩
  · simp [decodeInlineRetryPrefixBranchTaken, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · exact Agree.weaken (fun _ preserved => preserved.2)
      ((jumpRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
  · refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
    simp [decodeInlineRetryPrefixBranchTaken, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]

end BinaryFv.Zesu.MachineExecution
