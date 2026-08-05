import BinaryFv.Zesu.MachineExecution.GeneratedWordStep
import BinaryFv.Zesu.MachineExecution.Seg
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

/-- A short retry input takes the wrapper's `bltu a2, a0, 0x10420` exit.

The successor is existential: what the caller used to re-derive by unfolding a named
`decodeInlineRetryShortBranchAfter` is read off the `Seg` fields instead. `childSummary` is a
variable because a single owned step is confined whatever the enclosing summary is. -/
theorem retry_short_length_branch_step
    {childSummary : BinaryFv.Binary.Elfling.FunctionInstanceId → Nat → Nat → State → State → Prop}
    (stepNo : Nat) (args : DecodeInlineArgs)
    (before state : State) (pre : DecodeInlinePre args before)
    (frame : DecodeInlineMachinePost before state)
    (outgoing : DecodeInlineOutgoingFrame args state)
    (phase : args.phase = .retryAfterInvalidSsz) (short : args.bytes.size < 4)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10394)) :
    ∃ handoff,
      Runs (try_step stepNo false) state handoff false ∧
      Seg decodeRawExecutionPcs decodeRawExit childSummary stepBookkeeping noMemory []
        stepNo 1 state handoff (BitVec.ofNat 64 0x10420) := by
  have prefixFalse : Contracts.meaningHasExactErePrefix args.bytes = false :=
    meaningHasExactErePrefix_false_of_size_lt_four args.bytes short
  have values : state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) ∧
      state.regs.get? x12 = some
        (BitVec.ofNat 64 (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4))) := by
    simpa [DecodeInlineOutgoingFrame, phase, prefixFalse, short] using outgoing
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact frame.code
  have machine := pre.machine.mono frame.agree frame.retiredCounter
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10394)
  have premise : WritesOnlyRegs stepBookkeeping state executeState :=
    stepPremiseState_writes state (BitVec.ofNat 64 0x10394)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) :=
    (premise.get x10 (by decide)).trans values.1
  have x12AtExecute : executeState.regs.get? x12 = some
      (BitVec.ofNat 64 (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4))) :=
    (premise.get x12 (by decide)).trans values.2
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
  obtain ⟨retired, jumped⟩ := decoderBranchTakenStep machine (Agree.refl state)
    frame.retiredCounter image stepNo 0x10394 0x63 0x66 0xa6 0x08 0x8c#13 10#5 12#5 .BLTU
    (BitVec.ofNat 64 0x10420) atPc condition
  exact ⟨_, jumped,
    { trace := Trace.one stepNo _ _ jumped
      confined := ConfinedPrefix.ownStep' atPc jumped
      writes := jumpRetirement_writes state _ _ retired
      mem := writesOnlyWithin_of_mem_eq (jumpRetirement_mem state _ _ retired)
      retired := jumpRetirement_retired_present state _ _ retired
      atPc := jumpRetirement_pc state _ _ retired
      regs := RegsHold.nil _ }⟩

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

/-- Execute the wrapper-owned `lhu a0, -1552(a0)` after the exact-prefix retry.  The Level 3
outgoing frame supplies both the retained result tag at `sp + 0x9f0` and the pointer
`a0 = sp + 0x1000`; this theorem executes the pinned `0x9f055503` word through Sail and reaches
the following wrapper instruction at `0x103fc`. -/
theorem retry_exact_result_tag_step (stepNo : Nat) (args : DecodeInlineArgs)
    (before state : State) (pre : DecodeInlinePre args before)
    (frame : DecodeInlineMachinePost before state)
    (outgoing : DecodeInlineOutgoingFrame args state)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103f8)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103f8) retired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (Contracts.meaningDecode args.bytes))))
        false := by
  let tag := Contracts.decodeInternalResultTag (Contracts.meaningDecode args.bytes)
  have tagLt : tag < 2 ^ 16 := by
    simp only [tag]
    cases result : Contracts.meaningDecode args.bytes with
    | ok value => simp [Contracts.decodeInternalResultTag]
    | error error => cases error <;> simp [Contracts.decodeInternalResultTag]
  have tagCases : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 := by
    simp only [tag]
    cases result : Contracts.meaningDecode args.bytes with
    | ok value => simp [Contracts.decodeInternalResultTag]
    | error error => cases error <;> simp [Contracts.decodeInternalResultTag]
  have values : state.regs.get? x10 = some (BitVec.ofNat 64 (args.stackBase + 0x1000)) ∧
      state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
        MemoryRepresentation.ResultStatusLERep state (args.stackBase + 0x9f0) tag := by
    simpa [DecodeInlineOutgoingFrame, phase, exactPrefix, tag] using outgoing
  have resultSize : Contracts.canonicalContractParams.env.record.entryResult = 848 := by
    have pinned := congrArg (fun record => record.entryResult)
      Contracts.canonicalRecordSizes_pinned
    simpa [Contracts.canonicalContractParams, Contracts.canonicalEnvironment] using pinned
  let address := BitVec.ofNat 64 (args.stackBase + 0x9f0)
  have addressFits : args.stackBase + 0x9f0 + 2 ≤ 2 ^ 64 := by
    have fit := pre.stackObjectsFit
    rw [resultSize] at fit
    omega
  have addressNat : address.toNat = args.stackBase + 0x9f0 := by
    simp [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : args.stackBase + 0x9f0 < 2 ^ 64)]
  have machine := pre.machine.mono frame.agree frame.retiredCounter
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103f8)
  have executeAgree : Agree decoderPreserved state executeState :=
    Agree.weaken (fun _ preserved => preserved.2)
      (agree_stepPremiseState state (BitVec.ofNat 64 0x103f8))
  have pointerAtExecute : executeState.regs.get? x10 =
      some (BitVec.ofNat 64 (args.stackBase + 0x1000)) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x103f8)).get x10 (by decide)).trans values.1
  obtain ⟨mstatusBits, mstatusReadBase, mprvZero⟩ := machine.mstatus
  obtain ⟨mseccfgBase, mseccfgReadBase, pmmDisabled⟩ := machine.mseccfg
  have mstatusRead : executeState.regs.get? mstatus = some mstatusBits :=
    (executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusReadBase
  have privilegeRead : executeState.regs.get? cur_privilege = some Privilege.Machine :=
    (executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      machine.normal.2.1
  have mseccfgReadExecute : executeState.regs.get? mseccfg = some mseccfgBase :=
    (executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgReadBase
  have addressEq : BitVec.ofNat 64 (args.stackBase + 0x1000) +
      sign_extend (m := 64) (0x9f0#12) = address := by
    rw [show sign_extend (m := 64) (0x9f0#12) = -(BitVec.ofNat 64 0x610) by decide,
      ← BitVec.sub_eq_add_neg, BitVec.sub_eq_iff_eq_add, ← BitVec.ofNat_add]
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) (0x9f0#12))
        (MemoryAccessType.Load mem_payload.Data) 2)
      executeState executeState (.Ext_DataAddr_OK (virtaddr.Virtaddr address)) := by
    rw [← addressEq]
    exact get_transformed_data_addr_machine_load_run executeState (.Regidx 10#5)
      (BitVec.ofNat 64 (args.stackBase + 0x1000)) (sign_extend (m := 64) (0x9f0#12)) mstatusBits
      mseccfgBase (rX_x10_run executeState _ pointerAtExecute) mstatusRead privilegeRead
      mprvZero mseccfgReadExecute pmmDisabled
  have allowed : DecoderAccessRange (DecoderReadableByte args.machineArgs) address 2 := by
    refine ⟨by decide, ?_, ?_⟩
    · simpa [addressNat] using addressFits
    intro index indexLt
    right; right; left
    rw [addressNat]
    have stackByte := pre.stackObjectsReadable (0x9f0 + index) (by
      rw [resultSize]
      omega)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stackByte
  have addressMod : address.toNat % 2 = 0 := by
    rw [addressNat]
    have stackAligned := pre.stackAligned
    omega
  have aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 2 = true := by
    simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, ← Int.ofNat_tmod,
      addressMod]
    rfl
  obtain ⟨physAccess, loadNoMMIO⟩ :=
    machine.dataAccess.load executeState address 2 executeAgree allowed (by
      simp only [is_aligned_paddr, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast,
        ← Int.ofNat_tmod, addressMod]
      rfl)
  rcases values.2.2 with ⟨-, lowByte, highByte⟩
  have executeMemory : executeState.mem = state.mem := rfl
  have memoryBytes : ∀ (index : Nat) (indexLt : index < (leBytes 2 (BitVec.ofNat 16 tag)).length),
      executeState.mem.get? (address.toNat + index) =
        some (leBytes 2 (BitVec.ofNat 16 tag))[index] := by
    intro index indexLt
    rw [leBytes_length] at indexLt
    have indexCases : index = 0 ∨ index = 1 := by omega
    rcases indexCases with rfl | rfl
    · rw [executeMemory, addressNat]
      rcases tagCases with h | h | h | h <;> simpa [h, leBytes] using lowByte
    · rw [executeMemory, addressNat]
      rcases tagCases with h | h | h | h <;> simpa [h, leBytes] using highByte
  have hread := vmem_read_half_from_bytes_run executeState (.Regidx 10#5)
    (sign_extend (m := 64) (0x9f0#12)) address mstatusBits (BitVec.ofNat 16 tag)
    mstatusRead privilegeRead mprvZero addressRun aligned physAccess loadNoMMIO memoryBytes
  have extended : extend_value true (BitVec.ofNat 16 tag) = BitVec.ofNat 64 tag := by
    rcases tagCases with h | h | h | h <;>
      simp [h, extend_value, zero_extend, Sail.BitVec.zeroExtend]
  have write : Runs (wX_bits (.Regidx 10#5) (BitVec.ofNat 64 tag)) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 tag) } () :=
    wX_x10_run executeState (BitVec.ofNat 64 tag)
  exact decoderLhuStepOfDecoderAgree machine (Agree.refl state) frame.retiredCounter
    (hasExactErePrefix_programImage_of_codeIntact frame.code)
    stepNo 0x103f8 0x03 0x55 0x05 0x9f 0x9f0#12 10#5 10#5 atPc
    hread (by simpa [extended] using write)

end BinaryFv.Zesu.MachineExecution
