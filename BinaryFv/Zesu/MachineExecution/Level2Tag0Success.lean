import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.GeneratedWordStep
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.Zesu.MachineExecution.MemcpyInstance
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge

/-!
# Tag-zero stored-result continuation

The zero-result route reaches `0x1033c`. This module executes the wrapper instructions that copy
the successful result into `raw_decoder_root.stored_result` before the common status-store entry.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep GeneratedWordStep

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The wrapper's own confined-prefix scope, named once for this module: `zesu_decode_raw`'s
execution addresses, its generated exit pcs, and the Level 2 child summaries. `Level2Epilogue` names
the same proposition `WrapperPrefix`, which this module sits beside in the import graph and so
cannot see; both are `abbrev`s, hence reducible and interchangeable with each other and with the
spelled-out `ConfinedPrefix` application. The retired step count stays an explicit argument, because
it is what the child-summary interface consumes. -/
abbrev DecodeRawPrefix (fromStep len : Nat) (before after : State) : Prop :=
  ConfinedPrefix decodeRawExecutionPcs decodeRawExit Level2ChildSummary fromStep len before after

/-- The one call boundary this module proves, named once: the wrapper's scope, the wrapper and
`memcpy` function instances, and the `memcpyStoredResult` binding, leaving only the trace offset,
the retired child length, and the two states to vary. Reducible, like `DecodeRawPrefix`. -/
abbrev StoredResultCallTransfer (fromStep used : Nat) (callState resumed : State) : Type :=
  CallTransfer decodeRawExecutionPcs decodeRawExit
    Level2ChildSummary memcpyStoredResult generatedProgram
    functionInstance_raw_decoder_root_zesu_decode_raw functionInstance_memcpy
    fromStep used callState resumed

/-- Facts at `0x1033c` required to execute the tag-zero stored-result copy.  The eventual Level 2
capstone must derive this record from the wrapper prologue and the selected `decode` success result;
it is not an ABI assigned to the inlined decoder. -/
structure Tag0StoredResultCopyPre (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry state : State)
    (contents : ByteArray) (link savedS0 savedS1 savedS2 : BitVec 64) : Prop where
  machineEntry : ZesuDecodeRawMachinePre args stackBase entry
  atCopyStart : state.regs.get? PC = some (BitVec.ofNat 64 0x1033c)
  machine : DecoderMachinePre decodeRawExecutionPcs (zesuDecodeRawMachineArgs args) state
  retired : RetiredCounterPresent state
  code : canonicalContractParams.env.CodeIntact state
  stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackBase)
  globals : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  savedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 state
  sourceBytes : MemoryRepresentation.MemoryBytes state (stackBase + 32) contents
  contentsSize : contents.size = 832

/-- The tag-zero stored-result copy, with its four wrapper-owned setup instructions and the emitted
`memcpy` call kept as a composable Level 2 prefix.  The prefix stops at `0x10350`, which is not
claimed to be a wrapper exit; a later theorem supplies the following owned instructions. -/
structure Tag0StoredResultCopyPhase (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry state : State)
    (contents : ByteArray) (link savedS0 savedS1 savedS2 : BitVec 64) (fromStep used : Nat)
    (callState resumed : State) : Prop where
  machineEntry : ZesuDecodeRawMachinePre args stackBase entry
  setup : DecodeRawPrefix fromStep 4 state callState
  transfer : Nonempty (StoredResultCallTransfer (fromStep + 4) used callState resumed)
  scopedPrefix : DecodeRawPrefix fromStep (6 + used) state resumed
  trace : Trace fromStep (6 + used) state resumed
  atResume : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10350)
  savedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 resumed
  destinationBytes : MemoryRepresentation.MemoryBytes resumed 0x4215030 contents
  contentsSize : contents.size = 832
  code : canonicalContractParams.env.CodeIntact resumed
  retired : RetiredCounterPresent resumed
  stack : resumed.regs.get? x2 = some (BitVec.ofNat 64 stackBase)
  globals : resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  machine : DecoderMachinePre decodeRawExecutionPcs (zesuDecodeRawMachineArgs args) resumed

/-- Execute `addi a0, s2, 16` at `0x1033c`, selecting the 832-byte `stored_result` payload. -/
theorem tag0_stored_result_destination_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1033c))
    (globals : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1033c) retired x10
        (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 0x4215020))) false := by
  obtain ⟨seccfgBits, privilege, seccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x01090513 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x010#12, .Regidx 18#5, .Regidx 10#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1033c)
  have globalsAtExecute : executeState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x1033c)).get x18 (by decide)).trans globals
  let result := iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 0x4215020)
  have execute : Runs (execute (.ITYPE (0x010#12, .Regidx 18#5, .Regidx 10#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x10 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x010#12 (.Regidx 18#5) (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x010#12 (.Regidx 18#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 0x4215020) (rX_bits_run_x18 executeState _ globalsAtExecute)
      (wX_x10_run executeState result)
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x1033c 0x01090513 atPc decode execute

/-- Execute `addi a1, sp, 32` at `0x10340`, selecting the stack-resident result bytes. -/
theorem tag0_stored_result_source_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10340))
    (stack : BitVec 64) (stackRead : state.regs.get? x2 = some stack) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10340) retired x11
        (iTypeResult .ADDI 0x020#12 stack)) false := by
  obtain ⟨seccfgBits, privilege, seccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x02010593 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10340)
  have stackAtExecute : executeState.regs.get? x2 = some stack :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10340)).get x2 (by decide)).trans stackRead
  let result := iTypeResult .ADDI 0x020#12 stack
  have execute : Runs (execute (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 11#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x11 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x020#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x020#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI
      stack (rX_bits_run_x2 executeState _ stackAtExecute) (wX_x11_run executeState result)
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x10340 0x02010593 atPc decode execute

/-- Execute `addi a2, x0, 832` at `0x10344`. -/
theorem tag0_stored_result_length_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10344)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10344) retired x12
        (iTypeResult .ADDI 0x340#12 (0#64))) false := by
  obtain ⟨seccfgBits, privilege, seccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x34000613 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10344)
  let result := iTypeResult .ADDI 0x340#12 (0#64)
  have execute : Runs (execute (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x12 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x340#12 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x340#12 (.Regidx 0#5) (.Regidx 12#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x12_run executeState result)
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x10344 0x34000613 atPc decode execute

/-- Execute `auipc ra, 4` at `0x10348`, establishing the real `memcpy` call base. -/
theorem tag0_stored_result_call_page_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10348)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10348) retired x1 (BitVec.ofNat 64 0x14348)) false := by
  obtain ⟨seccfgBits, privilege, seccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x00004097 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10348)
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x10348) :=
    (((tryStepControlFlowAfterIncrement_writes state).trans
      (coreControlFlowNextState_writes _ (BitVec.ofNat 64 0x10348))).get PC (by decide)).trans atPc
  have execute : Runs (execute (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC))) executeState
      { executeState with regs := executeState.regs.insert x1 (BitVec.ofNat 64 0x14348) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_auipc_run executeState _ 0x00004#20 (.Regidx 1#5)
      (BitVec.ofNat 64 0x10348)
    · exact readReg_run _ _ _ pcAtExecute
    · simpa using wX_bits_run_x1 executeState (BitVec.ofNat 64 0x14348)
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x10348 0x00004097 atPc decode execute

/-- State immediately after the stored-result `jalr` at `0x1034c`. -/
def tag0StoredResultMemcpyCallAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1034c) (BitVec.ofNat 64 0x13eb8) x1
      (BitVec.ofNat 64 0x10350))
    (BitVec.ofNat 64 0x13eb8) retired

/-- Normalize the source setup instruction's modular RV64 result to the bounded stack address. -/
private theorem tag0_stored_result_source_value (stackBase : Nat) :
    iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 stackBase) =
      BitVec.ofNat 64 (stackBase + 32) := by
  rw [show BitVec.ofNat 64 (stackBase + 32) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 32 by rw [← BitVec.ofNat_add]]
  unfold iTypeResult
  rw [show sign_extend (0x020#12) = (0x20#64) by decide]

/-- Normalize the zero-register length setup instruction. -/
private theorem tag0_stored_result_length_value :
    iTypeResult .ADDI 0x340#12 (0#64) = BitVec.ofNat 64 832 := by decide

/-- Execute the actual stored-result `jalr x1, -0x490(x1)`.  Its arguments are the four values
established by the preceding wrapper instructions, rather than an ABI premise. -/
theorem tag0_stored_result_memcpy_call_step
    {args : ZesuDecodeRawArgs} {state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs (zesuDecodeRawMachineArgs args) state)
    (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1034c))
    (callBase : state.regs.get? x1 = some (BitVec.ofNat 64 0x14348)) :
    ∃ retired,
      Runs (try_step stepNo false) state (tag0StoredResultMemcpyCallAfter state retired) false ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? PC = some (BitVec.ofNat 64 0x13eb8) ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x1 = some (BitVec.ofNat 64 0x10350) ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x10 = state.regs.get? x10 ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x11 = state.regs.get? x11 ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x12 = state.regs.get? x12 ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x2 = state.regs.get? x2 ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x18 = state.regs.get? x18 ∧
      Agree decoderPreserved state (tag0StoredResultMemcpyCallAfter state retired) ∧
      (tag0StoredResultMemcpyCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (tag0StoredResultMemcpyCallAfter state retired) := by
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state 0x1034c 0xb70080e7 (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x1034c) atPc (fetchPc _) _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal (Agree.refl state) retiredPresent
  have decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0xb70#12, .Regidx 1#5, .Regidx 1#5)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1034c)
  have executeAgree : Agree decoderPreserved state executeState :=
    Agree.weaken (fun _ preserved => preserved.2)
      (agree_stepPremiseState state (BitVec.ofNat 64 0x1034c))
  have helpElp : Runs (update_elp_state (.Regidx 1#5)) executeState executeState () :=
    machine.landingPad executeState (.Regidx 1#5) trivial executeAgree
  have linkRead : executeState.regs.get? nextPC = some (BitVec.ofNat 64 0x10350) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x1034c) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp
    decide
  have sourceRead : executeState.regs.get? x1 = some (BitVec.ofNat 64 0x14348) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x1034c)).get x1 (by decide)).trans callBase
  have targetEq : Sail.BitVec.update
      ((BitVec.ofNat 64 0x14348) + sign_extend (m := 64) (0xb70#12)) 0 0#1 =
      BitVec.ofNat 64 0x13eb8 := by decide
  have hwrite : Runs (wX_bits (.Regidx 1#5) (BitVec.ofNat 64 0x10350))
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x1034c) (BitVec.ofNat 64 0x13eb8))
      (callLinkState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x1034c) (BitVec.ofNat 64 0x13eb8) x1
        (BitVec.ofNat 64 0x10350)) () := wX_bits_run_x1 _ _
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      state.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match h : state.regs.get? misa with
    | none => simp [h] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [h] using normalMisa⟩
  have misaState : state.regs.get? misa = some misaBits := misaRead
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x1034c)
    misaBits misaState
  have callRun := tryStepJalrCallRetires stepNo state
    (BitVec.ofNat 64 0x1034c) (BitVec.ofNat 64 0x14348) retired
    (BitVec.ofNat 64 0x10350) (0xb70#12) (.Regidx 1#5) (.Regidx 1#5) x1
    (BitVec.ofNat 64 0x10350) inhibit config byte0 byte1 byte2 byte3
    (_get_Misa_C misaBits == 1#1)
    (by simpa [targetEq] using hwrite) (by decide) (by decide) (by decide) (by decide)
    fetch noMMIO fetchBytes interrupts baseEncoding decode
    notExpected helpElp (get_next_pc_run executeState _ linkRead)
    (rX_bits_run_x1 executeState _ sourceRead) (by decide) zca hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead
  have run : Runs (try_step stepNo false) state (tag0StoredResultMemcpyCallAfter state retired) false := by
    simpa [tag0StoredResultMemcpyCallAfter, targetEq] using callRun
  have callWrites : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x1)) state
      (tag0StoredResultMemcpyCallAfter state retired) :=
    callRetirement_writes state (BitVec.ofNat 64 0x1034c) (BitVec.ofNat 64 0x13eb8) retired x1
      (BitVec.ofNat 64 0x10350)
  refine ⟨retired, run, ?_, ?_, callWrites.get x10 (by decide), callWrites.get x11 (by decide),
    callWrites.get x12 (by decide), callWrites.get x2 (by decide),
    callWrites.get x18 (by decide), ?_, jalrCallAfterRetired_mem _ _ _ _ _ _, ?_⟩
  · exact tryStepControlFlowAfterRetired_pc _ (BitVec.ofNat 64 0x13eb8) retired
  · apply tryStepControlFlowAfterRetired_preserves_register
    · exact callLinkState_link _ _ _ x1 (BitVec.ofNat 64 0x10350)
    · decide
    · decide
  · apply jalrCallAfterRetired_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  · exact ⟨Sail.BitVec.addInt retired 1, by
      simp [tag0StoredResultMemcpyCallAfter, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick]⟩

/-- Compose the four wrapper-owned setup words into the real stored-result call boundary. -/
theorem tag0_stored_result_setup
    {args : ZesuDecodeRawArgs} {stackBase : Nat} {entry state : State}
    (contents : ByteArray) (link savedS0 savedS1 savedS2 : BitVec 64)
    (pre : Tag0StoredResultCopyPre args stackBase entry state contents link savedS0 savedS1 savedS2)
    (fromStep : Nat) :
    ∃ r0 r1 r2 r3 callState,
      Trace fromStep 4 state callState ∧
      DecodeRawPrefix fromStep 4 state callState ∧
      callState = afterRegisterWrite
        (afterRegisterWrite
          (afterRegisterWrite
            (afterRegisterWrite state (BitVec.ofNat 64 0x1033c) r0 x10
              (BitVec.ofNat 64 0x4215030))
            (BitVec.ofNat 64 0x10340) r1 x11 (BitVec.ofNat 64 (stackBase + 32)))
          (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832))
        (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348) ∧
      callState.regs.get? PC = some (BitVec.ofNat 64 0x1034c) ∧
      callState.regs.get? x10 = some (BitVec.ofNat 64 0x4215030) ∧
      callState.regs.get? x11 = some (BitVec.ofNat 64 (stackBase + 32)) ∧
      callState.regs.get? x12 = some (BitVec.ofNat 64 832) ∧
      callState.regs.get? x1 = some (BitVec.ofNat 64 0x14348) ∧
      callState.regs.get? x2 = some (BitVec.ofNat 64 stackBase) ∧
      Agree decoderPreserved state callState ∧
      RetiredCounterPresent callState ∧
      canonicalContractParams.env.CodeIntact callState ∧
      WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 callState ∧
      MemoryRepresentation.MemoryBytes callState (stackBase + 32) contents := by
  obtain ⟨r0, h0⟩ := tag0_stored_result_destination_step pre.machine (Agree.refl state)
    pre.retired pre.code fromStep pre.atCopyStart pre.globals
  let s0 := afterRegisterWrite state (BitVec.ofNat 64 0x1033c) r0 x10 (BitVec.ofNat 64 0x4215030)
  have a0 : Agree platformPreserved state s0 := (Agree.refl state).trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have c0 : RetiredCounterPresent s0 := afterRegisterWrite_retired_present _ _ _ _ _
  have code0 : canonicalContractParams.env.CodeIntact s0 := by
    rw [DecoderEnvironment.CodeIntact, afterRegisterWrite_mem]
    exact pre.code
  have pc0 : s0.regs.get? PC = some (BitVec.ofNat 64 0x10340) := by
    simpa [s0] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x1033c) r0 x10
      (BitVec.ofNat 64 0x4215030)
  have stack0 : s0.regs.get? x2 = some (BitVec.ofNat 64 stackBase) :=
    ((afterRegisterWrite_writes state (BitVec.ofNat 64 0x1033c) r0 x10
      (BitVec.ofNat 64 0x4215030)).get x2 (by decide)).trans pre.stack
  obtain ⟨r1, h1⟩ := tag0_stored_result_source_step pre.machine a0 c0 code0
    (fromStep + 1) pc0 _ stack0
  have sourceValue := tag0_stored_result_source_value stackBase
  rw [sourceValue] at h1
  let s1 := afterRegisterWrite s0 (BitVec.ofNat 64 0x10340) r1 x11
    (BitVec.ofNat 64 (stackBase + 32))
  have a1 : Agree platformPreserved state s1 := a0.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have c1 : RetiredCounterPresent s1 := afterRegisterWrite_retired_present _ _ _ _ _
  have code1 : canonicalContractParams.env.CodeIntact s1 := by
    rw [DecoderEnvironment.CodeIntact, afterRegisterWrite_mem]
    exact code0
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10344) := by
    simpa [s1] using afterRegisterWrite_pc s0 (BitVec.ofNat 64 0x10340) r1 x11
      (BitVec.ofNat 64 (stackBase + 32))
  obtain ⟨r2, h2⟩ := tag0_stored_result_length_step pre.machine a1 c1 code1
    (fromStep + 2) pc1
  rw [tag0_stored_result_length_value] at h2
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832)
  have a2 : Agree platformPreserved state s2 := a1.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have c2 : RetiredCounterPresent s2 := afterRegisterWrite_retired_present _ _ _ _ _
  have code2 : canonicalContractParams.env.CodeIntact s2 := by
    rw [DecoderEnvironment.CodeIntact, afterRegisterWrite_mem]
    exact code1
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10348) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x10344) r2 x12
      (BitVec.ofNat 64 832)
  obtain ⟨r3, h3⟩ := tag0_stored_result_call_page_step pre.machine a2 c2 code2
    (fromStep + 3) pc2
  let callState := afterRegisterWrite s2 (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348)
  have a2Decoder : Agree decoderPreserved state s2 := fun register preserved =>
    a2 register preserved.2
  have a3 : Agree decoderPreserved state callState := a2Decoder.trans
    (afterRegisterWrite_agree_of (P := decoderPreserved)
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have c3 : RetiredCounterPresent callState := afterRegisterWrite_retired_present _ _ _ _ _
  have code3 : canonicalContractParams.env.CodeIntact callState := by
    rw [DecoderEnvironment.CodeIntact, afterRegisterWrite_mem]
    exact code2
  have w1 : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x11)) s0 s1 :=
    afterRegisterWrite_writes s0 (BitVec.ofNat 64 0x10340) r1 x11
      (BitVec.ofNat 64 (stackBase + 32))
  have w2 : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x12)) s1 s2 :=
    afterRegisterWrite_writes s1 (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832)
  have w3 : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x1)) s2 callState :=
    afterRegisterWrite_writes s2 (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348)
  refine ⟨r0, r1, r2, r3, callState, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, a3, c3, code3, ?_, ?_⟩
  · trace_steps [(by simpa [s0] using h0), (by simpa [s1] using h1), (by simpa [s2] using h2),
      (by simpa [callState] using h3)]
  · have first : DecodeRawPrefix fromStep 1 state s0 :=
      ConfinedPrefix.ownStep' pre.atCopyStart (by simpa [s0] using h0)
    have second : DecodeRawPrefix (fromStep + 1) 1 s0 s1 :=
      ConfinedPrefix.ownStep' pc0 (by simpa [s1] using h1)
    have third : DecodeRawPrefix (fromStep + 2) 1 s1 s2 :=
      ConfinedPrefix.ownStep' pc1 (by simpa [s2] using h2)
    have fourth : DecodeRawPrefix (fromStep + 3) 1 s2 callState :=
      ConfinedPrefix.ownStep' pc2 (by simpa [callState] using h3)
    confined_steps [first, second, third, fourth]
  · simpa [callState] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10348) r3 x1
      (BitVec.ofNat 64 0x14348)
  · exact (w3.get x10 (by decide)).trans ((w2.get x10 (by decide)).trans
      ((w1.get x10 (by decide)).trans
        (afterRegisterWrite_destination state (BitVec.ofNat 64 0x1033c) r0 x10
          (BitVec.ofNat 64 0x4215030) (by decide) (by decide))))
  · exact (w3.get x11 (by decide)).trans ((w2.get x11 (by decide)).trans
      (afterRegisterWrite_destination s0 (BitVec.ofNat 64 0x10340) r1 x11
        (BitVec.ofNat 64 (stackBase + 32)) (by decide) (by decide)))
  · exact (w3.get x12 (by decide)).trans
      (afterRegisterWrite_destination s1 (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832)
        (by decide) (by decide))
  · exact afterRegisterWrite_destination s2 (BitVec.ofNat 64 0x10348) r3 x1
      (BitVec.ofNat 64 0x14348) (by decide) (by decide)
  · exact (w3.get x2 (by decide)).trans ((w2.get x2 (by decide)).trans
      ((w1.get x2 (by decide)).trans stack0))
  · apply WrapperSavedRegisterFrame.of_mem_eq pre.savedFrame
    simp [callState, s2, s1, s0, afterRegisterWrite_mem]
  · apply pre.sourceBytes.of_mem_eq
    simp [callState, s2, s1, s0, afterRegisterWrite_mem]

/-- The exact arguments carried by the tag-zero wrapper copy. -/
def tag0StoredResultCopyArgs (stackBase : Nat) (contents : ByteArray) : CopyArgs where
  destination := 0x4215030
  source := stackBase + 32
  length := 832
  contents := contents

/-- Turn the wrapper's typed stored-result boundary into the compiled `memcpy` machine entry.
The source is a proved stack payload and the destination is the checked private decoder BSS range. -/
theorem tag0_stored_result_memcpy_machine_pre
    {args : ZesuDecodeRawArgs} {stackBase : Nat} {entry state childEntry : State}
    (contents : ByteArray) (pre : Tag0StoredResultCopyPre args stackBase entry state
      contents link savedS0 savedS1 savedS2)
    (agree : Agree decoderPreserved state childEntry)
    (retired : RetiredCounterPresent childEntry)
    (atEntry : childEntry.regs.get? PC = some (BitVec.ofNat 64 0x13eb8))
    (returnAddress : childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x10350)) :
    MemcpyMachinePre canonicalContractParams.env (tag0StoredResultCopyArgs stackBase contents) childEntry := by
  let copyArgs := tag0StoredResultCopyArgs stackBase contents
  let machine : DecoderMachinePre decodeRawExecutionPcs
      (zesuDecodeRawMachineArgs args) childEntry :=
    DecoderMachinePre.mono agree retired pre.machine
  have sourceFits : copyArgs.source + copyArgs.length ≤ 2 ^ 64 := by
    dsimp [copyArgs, tag0StoredResultCopyArgs]
    have frameFits := pre.machineEntry.stackFrameFits
    omega
  have destinationFits : copyArgs.destination + copyArgs.length ≤ 2 ^ 64 := by
    dsimp [copyArgs, tag0StoredResultCopyArgs]
    decide
  have destinationNotFile : ∀ index, index < copyArgs.length →
      canonicalContractParams.env.image.readFileByte? (copyArgs.destination + index) = none := by
    intro index bound
    cases read : canonicalContractParams.env.image.readFileByte? (copyArgs.destination + index) with
    | none => rfl
    | some byte =>
      have fileBelow : copyArgs.destination + index < 86028 :=
        Entrypoints.ZesuDecodeRaw.file_addr_lt (by
          simpa [canonicalContractParams, canonicalEnvironment] using read)
      dsimp [copyArgs, tag0StoredResultCopyArgs] at bound fileBelow ⊢
      omega
  have destinationNotAllocator : ∀ address, canonicalContractParams.env.allocatorState address →
      address < copyArgs.destination ∨ copyArgs.destination + copyArgs.length ≤ address := by
    intro address allocator
    left
    unfold canonicalContractParams canonicalEnvironment at allocator
    unfold Elflings.canonicalAllocatorState at allocator
    rcases allocator with h | h <;>
      have heapPosBound : Elflings.canonicalHeapPosAddr + 8 ≤ Entrypoints.ZesuDecodeRaw.heapCeiling := by native_decide
    all_goals
      have heapTopBound : Elflings.canonicalHeapTopAddr + 8 ≤ Entrypoints.ZesuDecodeRaw.heapCeiling := by native_decide
      have globalBase : Entrypoints.ZesuDecodeRaw.heapCeiling ≤ 0x4215020 := by
        simpa using Entrypoints.ZesuDecodeRaw.arena_disjoint_from_globals
      dsimp [copyArgs, tag0StoredResultCopyArgs]
      omega
  have sourceReadable : ∀ index, index < copyArgs.length →
      DecoderReadableByte (zesuDecodeRawMachineArgs args) (copyArgs.source + index) := by
    intro index bound
    right; right; left
    dsimp [copyArgs, tag0StoredResultCopyArgs] at bound ⊢
    simpa [Nat.add_assoc] using
      pre.machineEntry.stackFrameWritable (32 + index) (by omega)
  have destinationWritable : ∀ index, index < copyArgs.length →
      DecoderWritableByte (copyArgs.destination + index) := by
    intro index bound
    right; left
    unfold DecoderGlobalsByte
    dsimp [copyArgs, tag0StoredResultCopyArgs] at bound ⊢
    have bssBase : Elflings.GeneratedDecoderGlobals.bssBase = 0x4215020 := by native_decide
    have bssSize : Elflings.GeneratedDecoderGlobals.bssSize = 864 := by native_decide
    omega
  apply memcpyMachinePre_of_decoder copyArgs childEntry machine
  · intro pc bodyPc
    rcases bodyPc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact regionPc _
  · exact atEntry
  · exact ⟨BitVec.ofNat 64 0x10350, returnAddress, by decide⟩
  · rfl
  · simp [copyArgs, tag0StoredResultCopyArgs]
  · dsimp [copyArgs, tag0StoredResultCopyArgs]
    have frameFits := pre.machineEntry.stackFrameFits
    omega
  · dsimp [copyArgs, tag0StoredResultCopyArgs]
    decide
  · exact sourceFits
  · exact destinationFits
  · exact destinationNotFile
  · exact destinationNotAllocator
  · exact sourceReadable
  · exact destinationWritable

/-- Execute the complete stored-result call phase: four wrapper setup words, the real `jalr`, the
proved emitted `memcpy` body, and its real `ret` to `0x10350`.  The returned frame and payload are
the exact facts consumed by the following three wrapper instructions. -/
theorem tag0_stored_result_copy_phase
    {args : ZesuDecodeRawArgs} {stackBase : Nat} {entry state : State}
    (contents : ByteArray) (link savedS0 savedS1 savedS2 : BitVec 64)
    (pre : Tag0StoredResultCopyPre args stackBase entry state contents link savedS0 savedS1 savedS2)
    (fromStep : Nat) :
    ∃ used callState resumed, Tag0StoredResultCopyPhase args stackBase entry state contents link savedS0
      savedS1 savedS2 fromStep used callState resumed := by
  obtain ⟨r0, r1, r2, r3, callState, setupTrace, setupPrefix, callStateEq, callPc, destination, source,
    length, callBase, stack, setupAgree, setupCounter, setupCode, setupFrame, setupSource⟩ :=
    tag0_stored_result_setup contents link savedS0 savedS1 savedS2 pre fromStep
  have callMachine := DecoderMachinePre.mono setupAgree setupCounter pre.machine
  subst callState
  obtain ⟨callRetired, callRun, childPc, childLink, childDestination, childSource, childLength,
    childStack, childGlobals, callAgree, callMemory, childCounter⟩ :=
    tag0_stored_result_memcpy_call_step callMachine setupCounter setupCode
      (fromStep + 4) callPc callBase
  let childEntry := tag0StoredResultMemcpyCallAfter
    (afterRegisterWrite
      (afterRegisterWrite
        (afterRegisterWrite
          (afterRegisterWrite state (BitVec.ofNat 64 0x1033c) r0 x10
            (BitVec.ofNat 64 0x4215030))
          (BitVec.ofNat 64 0x10340) r1 x11
          (BitVec.ofNat 64 (stackBase + 32)))
        (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832))
      (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348)) callRetired
  let copyArgs := tag0StoredResultCopyArgs stackBase contents
  have childAgree : Agree decoderPreserved state childEntry := setupAgree.trans callAgree
  have childCode : canonicalContractParams.env.CodeIntact childEntry := by
    rw [DecoderEnvironment.CodeIntact, show childEntry.mem = state.mem by
      simpa [childEntry] using callMemory]
    exact pre.code
  have childSourceMemory : MemoryRepresentation.MemoryBytes childEntry (stackBase + 32) contents := by
    intro index bound
    rw [show childEntry.mem = state.mem by simpa [childEntry] using callMemory]
    exact pre.sourceBytes index bound
  have machinePre : MemcpyMachinePre canonicalContractParams.env copyArgs childEntry := by
    apply tag0_stored_result_memcpy_machine_pre contents pre childAgree childCounter
    · simpa [childEntry] using childPc
    · simpa [childEntry] using childLink
  have sourcePre : (contractMemcpy canonicalContractParams.env).pre copyArgs childEntry := by
    constructor
    · refine ⟨childSourceMemory, ?_, childCode, ?_, ?_, ?_⟩
      · simpa [copyArgs, tag0StoredResultCopyArgs] using pre.contentsSize
      · simpa [copyArgs, tag0StoredResultCopyArgs, childEntry] using childDestination.trans destination
      · simpa [copyArgs, tag0StoredResultCopyArgs, childEntry] using childSource.trans source
      · simpa [copyArgs, tag0StoredResultCopyArgs, childEntry] using childLength.trans length
    · left
      dsimp [copyArgs, tag0StoredResultCopyArgs]
      have separated := Entrypoints.ZesuDecodeRaw.wrapper_stack_after_stored_result pre.machineEntry
      omega
  have compiledEntry : (compiledMemcpyContract canonicalContractParams.env).binding.entry
      copyArgs childEntry := ⟨sourcePre, machinePre⟩
  obtain ⟨used, childExit, bound, childTrace, childPost⟩ :=
    compiledMemcpyInstanceContract_proved copyArgs (fromStep + 5) childEntry compiledEntry
  dsimp [copyArgs] at bound childTrace childPost compiledEntry
  obtain ⟨returnRetired, returnRun, resumePc⟩ :=
    memcpy_return_step (fromStep + 5 + used) (tag0StoredResultCopyArgs stackBase contents)
      (BitVec.ofNat 64 0x10350) childEntry childExit (by decide) (by decide) compiledEntry childTrace
      (by simpa [childEntry] using childLink) childPost
  have fullChildPost := childPost
  have atRet : childExit.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) := by
    obtain ⟨retPc, atRet, isExit⟩ := childTrace.trace.final_at_exit
    have retPcEq : retPc = BitVec.ofNat 64 0x13ec0 := by
      apply BitVec.eq_of_toNat_eq
      simpa [functionInstanceExitPred, FunctionInstance.isExit, functionInstance_memcpy] using isExit
    simpa [retPcEq] using atRet
  rcases childPost with ⟨sourcePost, machinePost⟩
  rcases sourcePost with ⟨exitCode, -, -, copyFrame, -, destinationMemory⟩
  let resumed := memcpyReturnAfter (BitVec.ofNat 64 0x10350) childExit returnRetired
  have returnWrites : WritesOnlyRegs stepBookkeeping childExit resumed :=
    jumpRetirement_writes childExit (BitVec.ofNat 64 0x13ec0) (BitVec.ofNat 64 0x10350)
      returnRetired
  have body : Level2ChildSummary functionInstance_memcpyId (fromStep + 5) used childEntry childExit :=
    .memcpy ⟨rfl, tag0StoredResultCopyArgs stackBase contents, compiledEntry, bound, childTrace,
      fullChildPost⟩
  have transfer : StoredResultCallTransfer (fromStep + 4) used _ resumed :=
    { valid := memcpyStoredResult_valid
      callPc := BitVec.ofNat 64 0x1034c
      atCall := callPc
      callSource := by decide
      callInRegion := regionPc _
      callNotExit := notExitPc _
      sCall := childEntry
      doCall := by simpa [childEntry] using callRun
      calleeEntryPc := BitVec.ofNat 64 0x13eb8
      atCalleeEntry := machinePre.entry
      calleeEntryMatches := by decide
      sRet := childExit
      body
      retPc := BitVec.ofNat 64 0x13ec0
      atRet
      retInRegion := regionPc _
      retNotExit := notExitPc _
      doReturn := by simpa [resumed, Nat.add_assoc] using returnRun
      returnPc := BitVec.ofNat 64 0x10350
      atResume := by simpa [resumed] using resumePc
      returnMatches := by decide
      resumeInRegion := regionPc _ }
  have callPrefix := ConfinedPrefix.ofCall transfer
  have scopedPrefix : DecodeRawPrefix fromStep (6 + used) state resumed :=
    ConfinedPrefix.trans' _ setupPrefix callPrefix
  have resumedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 resumed := by
    apply WrapperSavedRegisterFrame.of_mem_eq
      (WrapperSavedRegisterFrame.of_stored_result_copy pre.machineEntry setupFrame
        (tag0StoredResultCopyArgs stackBase contents) rfl rfl copyFrame)
    simp [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState]
  have childExitAgree : Agree decoderPreserved state childExit := childAgree.trans
    (Agree.weaken (fun register preserved => by
      rcases preserved with ⟨notLink, platform⟩
      rcases platform with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [NonW]) machinePost.frame)
  have resumedAgree : Agree decoderPreserved state resumed :=
    childExitAgree.trans
      (returnWrites.agree (platformPreserved_disjoint.weaken (fun _ preserved => preserved.2)))
  have resumedMachine : DecoderMachinePre decodeRawExecutionPcs
      (zesuDecodeRawMachineArgs args) resumed :=
    DecoderMachinePre.mono resumedAgree
      (jumpRetirement_retired_present childExit (BitVec.ofNat 64 0x13ec0)
        (BitVec.ofNat 64 0x10350) returnRetired) pre.machine
  refine ⟨used,
    afterRegisterWrite
      (afterRegisterWrite
        (afterRegisterWrite
          (afterRegisterWrite state (BitVec.ofNat 64 0x1033c) r0 x10
            (BitVec.ofNat 64 0x4215030))
          (BitVec.ofNat 64 0x10340) r1 x11 (BitVec.ofNat 64 (stackBase + 32)))
        (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832))
      (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348), resumed, ?_⟩
  refine ⟨pre.machineEntry, setupPrefix, ⟨transfer⟩, scopedPrefix,
    ?_, by simpa [resumed] using resumePc, resumedFrame, ?_, pre.contentsSize, ?_, ?_, ?_, ?_,
      resumedMachine⟩
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.append setupTrace
      (Trace.append (Trace.one (fromStep + 4) _ childEntry (by simpa [childEntry] using callRun))
        (Trace.append childTrace.trace.toTrace
          (Trace.one (fromStep + 5 + used) childExit resumed returnRun)))
  · simpa [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState] using destinationMemory
  · rw [DecoderEnvironment.CodeIntact]
    simpa [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState] using exitCode
  · exact jumpRetirement_retired_present childExit (BitVec.ofNat 64 0x13ec0)
      (BitVec.ofNat 64 0x10350) returnRetired
  · exact (returnWrites.get x2 (by decide)).trans
      ((machinePost.frame x2 (by simp [NonW])).trans (childStack.trans stack))
  · have stable := machinePost.frame x18 (by simp [NonW])
    have setupWrites :=
      (((afterRegisterWrite_writes state (BitVec.ofNat 64 0x1033c) r0 x10
              (BitVec.ofNat 64 0x4215030)).trans
            (afterRegisterWrite_writes _ (BitVec.ofNat 64 0x10340) r1 x11
              (BitVec.ofNat 64 (stackBase + 32)))).trans
          (afterRegisterWrite_writes _ (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832))).trans
        (afterRegisterWrite_writes _ (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348))
    have setupGlobals := (setupWrites.get x18 (by decide)).trans pre.globals
    exact (returnWrites.get x18 (by decide)).trans
      (stable.trans (childGlobals.trans setupGlobals))

end BinaryFv.Zesu.MachineExecution
