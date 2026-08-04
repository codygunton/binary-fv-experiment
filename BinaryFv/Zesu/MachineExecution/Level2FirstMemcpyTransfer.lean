import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep

/-!
# The first `memcpy` transfer in `zesu_decode_raw`

This module owns the real `jalr` at `0x10338`, the emitted `memcpy` summary, and its `ret` back
to `0x1033c`.  The call is attributed to the first inlined `decode` segment, but the enclosing
Level 2 wrapper trace owns the call boundary.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- State immediately after the real `jalr x1, -0x47c(x1)` at `0x10338`. -/
def firstMemcpyCallAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10338) (BitVec.ofNat 64 0x13eb8) x1
      (BitVec.ofNat 64 0x1033c))
    (BitVec.ofNat 64 0x13eb8) retired

/-- Sail execution of the first emitted-`memcpy` call.  Its inputs are the registers established
by the preceding four proved `decode` instructions; no callable source ABI is assumed. -/
theorem first_memcpy_call_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (code : canonicalContractParams.env.CodeIntact state)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10338))
    (callBase : state.regs.get? x1 = some (BitVec.ofNat 64 0x14334)) :
    ∃ retired,
      Runs (try_step stepNo false) state (firstMemcpyCallAfter state retired) false ∧
      (firstMemcpyCallAfter state retired).regs.get? PC = some (BitVec.ofNat 64 0x13eb8) ∧
      (firstMemcpyCallAfter state retired).regs.get? x1 = some (BitVec.ofNat 64 0x1033c) ∧
      (firstMemcpyCallAfter state retired).regs.get? x10 = state.regs.get? x10 ∧
      (firstMemcpyCallAfter state retired).regs.get? x11 = state.regs.get? x11 ∧
      (firstMemcpyCallAfter state retired).regs.get? x12 = state.regs.get? x12 ∧
      (firstMemcpyCallAfter state retired).regs.get? x2 = state.regs.get? x2 ∧
      Agree decoderPreserved state (firstMemcpyCallAfter state retired) ∧
      (firstMemcpyCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (firstMemcpyCallAfter state retired) := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (BitVec.ofNat 64 0x10338) :=
    ⟨decodeInline_owned_in_execution_region (0x10338, 0xb84080e7)
      (by simp [decodeInlineOwnedInstructionWords]), by native_decide⟩
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10338) 0xe7#8 0x80#8 0x40#8 0xb8#8 :=
    fetchFileInstruction state 0x10338 0xe7 0x80 0x40 0xb8 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree pre.machine agree
    (BitVec.ofNat 64 0x10338) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree pre.machine.normal agree retiredPresent
  have wordEq : fetchWord 0xe7#8 0x80#8 0x40#8 0xb8#8 = (0xb84080e7 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xe7#8 0x80#8 0x40#8 0xb8#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0xb84#12, .Regidx 1#5, .Regidx 1#5)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10338)
  have executeAgree : Agree decoderPreserved baseState executeState := Agree.trans agree
    (Agree.weaken (fun _ preserved => preserved.2)
      (agree_stepPremiseState state (BitVec.ofNat 64 0x10338)))
  have helpElp : Runs (update_elp_state (.Regidx 1#5)) executeState executeState () :=
    pre.machine.landingPad executeState (.Regidx 1#5) trivial executeAgree
  have linkRead : executeState.regs.get? nextPC = some (BitVec.ofNat 64 0x1033c) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10338) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp
    decide
  have sourceRead : executeState.regs.get? x1 = some (BitVec.ofNat 64 0x14334) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, callBase]
  have targetEq : Sail.BitVec.update
      ((BitVec.ofNat 64 0x14334) + sign_extend (m := 64) (0xb84#12)) 0 0#1 =
      BitVec.ofNat 64 0x13eb8 := by decide
  have hwrite : Runs (wX_bits (.Regidx 1#5) (BitVec.ofNat 64 0x1033c))
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x10338) (BitVec.ofNat 64 0x13eb8))
      (callLinkState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x10338) (BitVec.ofNat 64 0x13eb8) x1
        (BitVec.ofNat 64 0x1033c)) () := wX_bits_run_x1 _ _
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      baseState.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := pre.machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match misaRead : baseState.regs.get? misa with
    | none => simp [misaRead] at normalMisa
    | some misaBits => exact ⟨misaBits, rfl, by simpa [misaRead] using normalMisa⟩
  have misaState : state.regs.get? misa = some misaBits :=
    (agree misa (by simp [decoderPreserved, platformPreserved])).trans misaRead
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x10338)
    misaBits misaState
  have callRun := tryStepJalrCallRetires stepNo state
    (BitVec.ofNat 64 0x10338) (BitVec.ofNat 64 0x14334) retired
    (BitVec.ofNat 64 0x1033c) (0xb84#12) (.Regidx 1#5) (.Regidx 1#5) x1
    (BitVec.ofNat 64 0x1033c) inhibit config 0xe7#8 0x80#8 0x40#8 0xb8#8
    (_get_Misa_C misaBits == 1#1)
    (by simpa [targetEq] using hwrite) (by decide) (by decide) (by decide) (by decide)
    fetch noMMIO fetchBytes interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected helpElp (get_next_pc_run executeState _ linkRead)
    (rX_bits_run_x1 executeState _ sourceRead) (by decide) zca hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead
  have run : Runs (try_step stepNo false) state (firstMemcpyCallAfter state retired) false := by
    simpa [firstMemcpyCallAfter, targetEq] using callRun
  have preserveGeneral (register : Register) (notLink : register ≠ x1)
      (notPc : register ≠ PC) (notNextPc : register ≠ nextPC)
      (notIncrement : register ≠ minstret_increment) (notRetired : register ≠ minstret) :
      (firstMemcpyCallAfter state retired).regs.get? register = state.regs.get? register := by
    have preserved := jalrCallAfterRetired_agree_of
      (P := fun candidate => candidate = register) state (BitVec.ofNat 64 0x10338)
      (BitVec.ofNat 64 0x13eb8) retired x1 (BitVec.ofNat 64 0x1033c)
      (Ne.symm notLink) (Ne.symm notPc) (Ne.symm notNextPc)
      (Ne.symm notIncrement) (Ne.symm notRetired)
    exact preserved register rfl
  refine ⟨retired, run, ?_, ?_, preserveGeneral x10 (by decide) (by decide) (by decide)
    (by decide) (by decide), preserveGeneral x11 (by decide) (by decide) (by decide)
    (by decide) (by decide), preserveGeneral x12 (by decide) (by decide) (by decide)
    (by decide) (by decide), preserveGeneral x2 (by decide) (by decide) (by decide)
    (by decide) (by decide), ?_, jalrCallAfterRetired_mem _ _ _ _ _ _, ?_⟩
  · simp [firstMemcpyCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  · apply tryStepControlFlowAfterRetired_preserves_register
    · exact callLinkState_link _ _ _ x1 (BitVec.ofNat 64 0x1033c)
    · decide
    · decide
  · apply jalrCallAfterRetired_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  · exact ⟨Sail.BitVec.addInt retired 1, by
      simp [firstMemcpyCallAfter, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick]⟩

end BinaryFv.Zesu.MachineExecution
