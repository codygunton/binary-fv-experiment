import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.ExportedContractExecution
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.CanonicalEntry
import BinaryFv.Zesu.MachineExecution.RawErrorProof
import BinaryFv.Zesu.MachineExecution.RawResultProof

/-!
# Compiled accessor calls

This module replaces the address-free accessor assumptions used by `Assembly.lean` with obligations
that bind each source contract to the selected compiled function instance.  Each accessor is
assembled separately.  The first theorem exposes only the state facts needed to enter the second;
it does not make Lean elaborate both complete source postconditions in one proof.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.DecodedValue
open BinaryFv.Zesu.Elflings.Validation
open BinaryFv.Zesu.Elflings.Generated
open LeanRV64DExecutable.Functions

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Every Level 1 fetch address whose machine conditions must survive the wrapper and first
accessor call: the wrapper return, both accessor entries, and both accessor returns. -/
def level1PlatformPcs : List Nat :=
  0x10378 :: rawResultInstructionPcs ++ rawErrorInstructionPcs

def level1LoadAccesses : List (Nat × Nat) :=
  [(Elflings.canonicalDecoderGlobalsLayout.status, 4),
    (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset, 1)]

theorem configureFetchPinned_level1PlatformPcs :
    configureFetchPinnedB level1PlatformPcs = true := by
  native_decide

theorem configureLoadPinned_level1LoadAccesses :
    configureLoadPinnedB level1LoadAccesses = true := by
  native_decide

theorem rawResultInstructionPcs_subset_level1 :
    ∀ pc ∈ rawResultInstructionPcs, pc ∈ level1PlatformPcs := by
  intro pc hpc
  simp [level1PlatformPcs, hpc]

theorem rawErrorInstructionPcs_subset_level1 :
    ∀ pc ∈ rawErrorInstructionPcs, pc ∈ level1PlatformPcs := by
  intro pc hpc
  simp [level1PlatformPcs, hpc]

theorem rawError_entry_mem_level1PlatformPcs :
    resolvedSymbols.rawError ∈ level1PlatformPcs := by
  native_decide

/-- Transport pinned load permissions across any frame that preserves the platform registers.
Every accessor step in this module frames its loads exactly this way. -/
private theorem loadPlatformPinned_of_agree {before after : State} {accesses : List (Nat × Nat)}
    (agree : Agree platformPreserved before after) (pinned : LoadPlatformPinned before accesses) :
    LoadPlatformPinned after accesses :=
  loadPlatformPinned_frame (platformPreserved_mstatus agree) (platformPreserved_mseccfg agree)
    (platformPreserved_pmaRegions agree) pinned

/-- Transport a caller-selected set of fetch conditions across a contract frame. -/
theorem exitPlatformsFor_of_agree {pcs : List Nat} {before after : State}
    (agree : Agree platformPreserved before after) (retired : RetiredCounterPresent after)
    (code : canonicalEnvironment.CodeIntact after)
    (platform : ∀ pc ∈ pcs, ExitPlatform before pc) :
    ∀ pc ∈ pcs, ExitPlatform after pc :=
  fun pc hpc => exitPlatform_of_agree agree retired (programImage_of_codeIntact code)
    (platform pc hpc)

/-- Transport a caller-selected set of fetch conditions across the return to the runner. -/
theorem exitPlatformsFor_of_exitRetFrame {pcs : List Nat} {before after : State}
    (frame : ExitRetFrame before after) (code : canonicalEnvironment.CodeIntact before)
    (platform : ∀ pc ∈ pcs, ExitPlatform before pc) :
    ∀ pc ∈ pcs, ExitPlatform after pc :=
  exitPlatformsFor_of_agree frame.agree frame.retired (codeIntact_of_mem_eq frame.mem code) platform

/-- The selected compiled wrapper obligation. Its entry condition is the checked canonical machine
state, rather than an arbitrary state satisfying only the public C binding. -/
abbrev DecodeInstanceObligation : Prop :=
  CompiledZesuDecodeRawInstanceContract

/-- Run the selected compiled wrapper from the exact state built for this input, then retain fetch
conditions for every Level 1 call and return address. -/
theorem decodeRun_of_compiledLevel1 (decode : DecodeInstanceObligation) (input : ByteArray)
    (inputBound : input.size < 2 * 1024 * 1024) :
    ∃ (entryState atExit finalState : State) (count : Nat),
      Runs (buildZesuEntryState input) initialState entryState () ∧
      TraceToSentinel sentinelWord 0 (count + 1) entryState finalState ∧
      count + 1 ≤ entryStepBound input.size + 1 ∧
      CanonicalDecodeExit input entryState atExit ∧
      ExitRetFrame atExit finalState ∧
      (∀ pc ∈ level1PlatformPcs, ExitPlatform finalState pc) ∧
      LoadPlatformPinned finalState level1LoadAccesses := by
  obtain ⟨nodes, hn⟩ := controlFlow_some
  have hfind : Program.find? generatedProgram generatedProgram.entry =
      some functionInstance_raw_decoder_root_zesu_decode_raw := by rfl
  obtain ⟨entryState, hrun, hcompiledEntry⟩ :=
    buildZesuEntryState_compiled_entry input inputBound
  obtain ⟨abiState, hrunAbi, -, hlink, -, hnormal, hpresent, hpinned, hloadPinned, -⟩ :=
    buildZesuEntryState_entry_binding_abi input
  have sameState : abiState = entryState := by
    unfold Runs at hrun hrunAbi
    rw [hrun] at hrunAbi
    injection hrunAbi with _ stateEqual
    exact stateEqual.symm
  subst abiState
  change preZesuDecodeRaw canonicalEnvironment Elflings.canonicalDecoderGlobalsLayout Elflings.canonicalResultBuffer
      canonicalStatelessInputRep DecoderGlobalsModel.fresh
      ⟨canonicalRunnerLayout.inputBase, input⟩ entryState ∧
      CompiledZesuDecodeRawPre ⟨canonicalRunnerLayout.inputBase, input⟩ entryState at hcompiledEntry
  obtain ⟨hpma, hhtif⟩ :=
    hpinned level1PlatformPcs configureFetchPinned_level1PlatformPcs
  have hcodeEntry : Artifacts.programImage.fileBytesLoadedFaithfully entryState.mem :=
    programImage_of_codeIntact hcompiledEntry.1.2.1
  have hplatformEntry : ∀ pc ∈ level1PlatformPcs, ExitPlatform entryState pc := by
    intro pc hpc
    obtain ⟨regions, region, hregions, hmatch, hexec⟩ := hpma pc hpc
    exact
      { normal := hnormal
        mstatusRead := hpresent.2.1
        meipRead := hpresent.2.2.1
        seccfgRead := hpresent.2.2.2.2
        pmaAllows := ⟨regions, region, hregions, hmatch, hexec⟩
        htifRead := hhtif
        retired := hpresent.1
        link := hlink
        code := hcodeEntry }
  have hloadsEntry : LoadPlatformPinned entryState level1LoadAccesses :=
    hloadPinned level1LoadAccesses configureLoadPinned_level1LoadAccesses
  obtain ⟨count, atExit, hbound, htrace, hcompiledExit⟩ :=
    decode ⟨canonicalRunnerLayout.inputBase, input⟩ 0 entryState hcompiledEntry
  have hexit : CanonicalDecodeExit input entryState atExit := by
    simpa [compiledZesuDecodeRawContract] using hcompiledExit
  obtain ⟨finalState, hsentinel, -, -, hframe⟩ :=
    entryTraceToSentinel_of_enteredFunctionTrace hn hfind
      (exitPlatform_of_agree hexit.2.2.2.1 hexit.2.2.2.2.1
        (programImage_of_codeIntact hexit.2.1)
        (hplatformEntry 0x10378 (by simp [level1PlatformPcs])))
      htrace
  have hloadsAtExit : LoadPlatformPinned atExit level1LoadAccesses :=
    loadPlatformPinned_of_agree hexit.2.2.2.1 hloadsEntry
  have hloadsFinal : LoadPlatformPinned finalState level1LoadAccesses :=
    loadPlatformPinned_of_agree hframe.agree hloadsAtExit
  have hbound' : count ≤ entryStepBound input.size := by
    simpa [compiledZesuDecodeRawContract, functionInstanceZesuDecodeRaw, entryStepBound] using hbound
  exact ⟨entryState, atExit, finalState, count, hrun, hsentinel,
    Nat.add_le_add_right hbound' 1, hexit, hframe,
    exitPlatformsFor_of_exitRetFrame hframe hexit.2.1
      (exitPlatformsFor_of_agree hexit.2.2.2.1 hexit.2.2.2.2.1 hexit.2.1
        hplatformEntry), hloadsFinal⟩

/-- Facts preserved by the compiled `zesu_raw_result` call and needed by `zesu_raw_error`. -/
structure RawResultHandoff (model : DecoderGlobalsModel) (before middle : State) : Prop where
  reaches :
    AccessorReachesSentinel resolvedSymbols.rawResult rawResultStepBound before middle
  returnCode :
    observeReturnCode? middle =
      some (if model.stored.isSome then Elflings.canonicalResultBuffer else 0)
  code : canonicalEnvironment.CodeIntact middle
  globals :
    DecoderGlobalsScalarRep Elflings.canonicalDecoderGlobalsLayout model middle
  platform : ∀ pc ∈ level1PlatformPcs, ExitPlatform middle pc
  loads : LoadPlatformPinned middle level1LoadAccesses

/-- Run the selected compiled `zesu_raw_result` instance and produce the exact handoff required by
the following accessor call. -/
theorem rawResultHandoff_of_compiled
    (implements : ∀ {functionInstance : FunctionInstance},
      functionInstance ∈ generatedProgram.functionInstances →
      functionInstance.entryPc = resolvedSymbols.rawResult →
        RawResultInstanceObligation functionInstance)
    {state : State} {model : DecoderGlobalsModel}
    (hplatform : ∀ pc ∈ level1PlatformPcs, ExitPlatform state pc)
    (hloads : LoadPlatformPinned state level1LoadAccesses)
    (hcode : canonicalEnvironment.CodeIntact state)
    (hscalar : DecoderGlobalsScalarRep Elflings.canonicalDecoderGlobalsLayout model state)
    (hstored : StoredResultDiscriminantRep Elflings.canonicalDecoderGlobalsLayout model state) :
    ∃ middle, RawResultHandoff model state middle := by
  obtain ⟨nodes, hn⟩ := controlFlow_some
  let setup := accessorSetup resolvedSymbols.rawResult state
  have hsetup : Agree platformPreserved state setup :=
    agree_accessorSetup _ (hplatform resolvedSymbols.rawResult (by native_decide)).link
  have hloadsSetup : LoadPlatformPinned setup level1LoadAccesses :=
    loadPlatformPinned_of_agree hsetup hloads
  have hmachine : RawResultMachinePre setup :=
    { entry := by simp [setup, accessorSetup, Std.ExtDHashMap.get?_insert]
      instructions := by
        intro pc hpc
        exact exitPlatform_accessorSetup _
          (hplatform pc (rawResultInstructionPcs_subset_level1 pc hpc))
      discriminantLoad := hloadsSetup.allows
        (Elflings.canonicalDecoderGlobalsLayout.storedResult +
          Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset, 1)
        (by simp [level1LoadAccesses])
      mstatus := hloadsSetup.mstatus
      mseccfg := hloadsSetup.mseccfg }
  obtain ⟨functionInstance, hmem, hentry, ⟨execution⟩⟩ :=
    runSelectedRawResult implements model 0 setup
      (contractRawResult_entry_accessorSetup
        (resultBuffer := canonicalContractParams.resultBuffer) _
        (hplatform 0x137A8
          (rawResultInstructionPcs_subset_level1 0x137A8 (by decide))).normal hcode hstored)
      hmachine
  obtain ⟨count, atExit, hbound, htrace, hpost⟩ := execution
  obtain ⟨middle, -, hreach, -, hframe⟩ :=
    rawResultReachesSentinel_of_enteredFunctionTrace hn hmem hentry hbound
      (exitPlatform_of_agree hpost.2.2.2.1 hpost.2.2.2.2.1
        (programImage_of_codeIntact hpost.1)
        (exitPlatform_accessorSetup _ (hplatform 0x137A8
          (rawResultInstructionPcs_subset_level1 0x137A8 (by decide)))))
      htrace
  have hpointerBound :
      (if model.stored.isSome then Elflings.canonicalResultBuffer else 0) < 2 ^ 64 := by
    have hbelow := canonicalResultBuffer_below_ceiling
    have hceiling := runtime_below_ceiling.2
    have : loadedCeiling < 2 ^ 64 := by decide
    split <;> omega
  have hloadsAtExit : LoadPlatformPinned atExit level1LoadAccesses :=
    loadPlatformPinned_of_agree hpost.2.2.2.1 hloadsSetup
  have hloadsMiddle : LoadPlatformPinned middle level1LoadAccesses :=
    loadPlatformPinned_of_agree hframe.agree hloadsAtExit
  refine ⟨middle, hreach,
    observeReturnCode_of_a0 hpointerBound (hframe.returnValue.trans hpost.2.2.2.2.2.2),
    codeIntact_of_mem_eq hframe.mem hpost.1,
    decoderGlobalsScalarRep_of_mem_eq hframe.mem
      (decoderGlobalsScalarRep_survives_accessor hpost.2.2.1 hscalar), ?_, hloadsMiddle⟩
  exact exitPlatformsFor_of_exitRetFrame hframe hpost.1
    (exitPlatformsFor_of_agree hpost.2.2.2.1 hpost.2.2.2.2.1 hpost.1
      (fun pc hpc => exitPlatform_accessorSetup _ (hplatform pc hpc)))

/-- Run the selected compiled `zesu_raw_error` instance from the state handed off by
`rawResultHandoff_of_compiled`. -/
theorem rawErrorResult_of_compiled
    (implements : ∀ {functionInstance : FunctionInstance},
      functionInstance ∈ generatedProgram.functionInstances →
      functionInstance.entryPc = resolvedSymbols.rawError →
        RawErrorInstanceObligation functionInstance)
    {model : DecoderGlobalsModel} {before middle : State}
    (handoff : RawResultHandoff model before middle) :
    ∃ after,
      AccessorReachesSentinel resolvedSymbols.rawError rawErrorStepBound middle after ∧
      observeReturnCode? after = some model.status.code := by
  obtain ⟨nodes, hn⟩ := controlFlow_some
  let setup := accessorSetup resolvedSymbols.rawError middle
  have hsetup : Agree platformPreserved middle setup :=
    agree_accessorSetup _
      (handoff.platform resolvedSymbols.rawError rawError_entry_mem_level1PlatformPcs).link
  have hloadsSetup : LoadPlatformPinned setup level1LoadAccesses :=
    loadPlatformPinned_of_agree hsetup handoff.loads
  have hmachine : RawErrorMachinePre setup :=
    { entry := by simp [setup, accessorSetup, Std.ExtDHashMap.get?_insert]
      instructions := by
        intro pc hpc
        exact exitPlatform_accessorSetup _
          (handoff.platform pc (rawErrorInstructionPcs_subset_level1 pc hpc))
      statusLoad := hloadsSetup.allows (Elflings.canonicalDecoderGlobalsLayout.status, 4)
        (by simp [level1LoadAccesses])
      mstatus := hloadsSetup.mstatus
      mseccfg := hloadsSetup.mseccfg }
  obtain ⟨functionInstance, hmem, hentry, ⟨execution⟩⟩ :=
    runSelectedRawError implements model 0 setup
      (contractRawError_entry_accessorSetup _
        (handoff.platform resolvedSymbols.rawError rawError_entry_mem_level1PlatformPcs).normal
        handoff.code handoff.globals)
      hmachine
  obtain ⟨count, atExit, hbound, htrace, hpost⟩ := execution
  obtain ⟨after, -, hreach, -, hframe⟩ :=
    rawErrorReachesSentinel_of_enteredFunctionTrace hn hmem hentry hbound
      (exitPlatform_of_agree hpost.2.2.2.1 hpost.2.2.2.2.1
        (programImage_of_codeIntact hpost.1)
        (exitPlatform_accessorSetup _
          (handoff.platform 0x13788
            (rawErrorInstructionPcs_subset_level1 0x13788 (by decide)))))
      htrace
  refine ⟨after, hreach, ?_⟩
  exact observeReturnCode_of_a0 (statusCode_lt_two_pow_64 model.status)
    (hframe.returnValue.trans hpost.2.2.2.2.2.2)

/-- Compose the two selected compiled accessor calls without exposing either expanded source
postcondition. -/
theorem accessorTraces_of_compiled
    {state : State} {model : DecoderGlobalsModel}
    (hplatform : ∀ pc ∈ level1PlatformPcs, ExitPlatform state pc)
    (hloads : LoadPlatformPinned state level1LoadAccesses)
    (hcode : canonicalEnvironment.CodeIntact state)
    (hscalar : DecoderGlobalsScalarRep Elflings.canonicalDecoderGlobalsLayout model state)
    (hstored : StoredResultDiscriminantRep Elflings.canonicalDecoderGlobalsLayout model state) :
    ∃ middle after,
      AccessorReachesSentinel resolvedSymbols.rawResult rawResultStepBound state middle ∧
      observeReturnCode? middle =
        some (if model.stored.isSome then Elflings.canonicalResultBuffer else 0) ∧
      AccessorReachesSentinel resolvedSymbols.rawError rawErrorStepBound middle after ∧
      observeReturnCode? after = some model.status.code := by
  obtain ⟨middle, handoff⟩ := rawResultHandoff_of_compiled
    BinaryFv.Zesu.MachineExecution.rawResultInstanceObligation_proved hplatform hloads hcode
    hscalar hstored
  obtain ⟨after, herror, hstatus⟩ :=
    rawErrorResult_of_compiled
      BinaryFv.Zesu.MachineExecution.rawErrorInstanceObligation_proved handoff
  exact ⟨middle, after, handoff.reaches, handoff.returnCode, herror, hstatus⟩

/-- The remaining compiled decoder obligation used by the Level 1 runner proof. -/
structure CompiledLevel1Assumptions : Prop where
  decode : DecodeInstanceObligation

/-- Accepted inputs produce the runner witness from the remaining Level 1 decoder obligation. -/
theorem successfulRun_of_compiledLevel1 (contracts : CompiledLevel1Assumptions)
    {input : ByteArray} (inputBound : input.size < 2 * 1024 * 1024)
    {value : BinaryFv.Specs.SSZ.StatelessInput}
    (accepts : BinaryFv.Specs.SSZ.decode input = .accepted value) :
    Nonempty (SuccessfulRun input value) := by
  obtain ⟨entryState, atExit, finalState, count, hrun, htrace, hbound, hexit, hframe,
    hplatform, hloads⟩ := decodeRun_of_compiledLevel1 contracts.decode input inputBound
  obtain ⟨hcode, htag, hinput, hvalue⟩ :=
    successfulRun_fields_of_canonicalDecodeExit catalogGroundsInSpec_holds inputBound accepts hexit
  have hcodeFinal : observeReturnCode? finalState = some 1 :=
    observeReturnCode_of_regs_eq hframe.returnValue hcode
  have htagFinal : observeOptionTag? finalState storedResultDiscriminantAddr = some true :=
    observeOptionTag_of_mem_eq hframe.mem htag
  have hinputFinal : MemoryBytes finalState canonicalRunnerLayout.inputBase input :=
    memoryBytes_of_mem_eq hframe.mem hinput
  have hvalueFinal : StatelessInputRep finalState canonicalRunnerLayout.inputBase input
      Elflings.canonicalResultBuffer value :=
    statelessInputRep_of_mem_eq hframe.mem hvalue
  have hmeaning : meaningDecode input = .ok value :=
    meaningDecode_ok_of_spec_accepts catalogGroundsInSpec_holds inputBound accepts
  have hglobals := hexit.2.2.2.2.2
  rw [hmeaning] at hglobals
  obtain ⟨middle, after, hreachResult, hcodeResult, hreachError, hcodeError⟩ :=
    accessorTraces_of_compiled hplatform hloads
      (codeIntact_of_mem_eq hframe.mem hexit.2.1)
      (decoderGlobalsScalarRep_of_mem_eq hframe.mem hglobals.1)
      (storedResultDiscriminantRep_of_mem_eq hframe.mem hglobals.2.1)
  refine successfulRun_of_acceptedAccessorTraces input value hrun htrace hbound hcodeFinal htagFinal
    hinputFinal hvalueFinal ⟨middle, after, hreachResult, ?_, hreachError, ?_⟩
  · rw [hcodeResult, freshGlobals_ok_pointer]
  · rw [hcodeError, freshGlobals_ok_statusCode]

/-- Rejected inputs produce the runner witness from the same remaining obligations. -/
theorem rejectedRun_of_compiledLevel1 (contracts : CompiledLevel1Assumptions)
    {input : ByteArray} (inputBound : input.size < 2 * 1024 * 1024)
    (rejects : BinaryFv.Specs.SSZ.decode input = .rejected) :
    Nonempty (RejectedRun input) := by
  obtain ⟨entryState, atExit, finalState, count, hrun, htrace, hbound, hexit, hframe,
    hplatform, hloads⟩ := decodeRun_of_compiledLevel1 contracts.decode input inputBound
  obtain ⟨hcode, htag, -, hstatus⟩ :=
    rejectedRun_fields_of_canonicalDecodeExit catalogGroundsInSpec_holds inputBound rejects hexit
  have hcodeFinal : observeReturnCode? finalState = some 0 :=
    observeReturnCode_of_regs_eq hframe.returnValue hcode
  have htagFinal : observeOptionTag? finalState storedResultDiscriminantAddr = some false :=
    observeOptionTag_of_mem_eq hframe.mem htag
  obtain ⟨error, hmeaning⟩ :=
    meaningDecode_error_of_spec_rejects catalogGroundsInSpec_holds inputBound rejects
  have hglobals := hexit.2.2.2.2.2
  obtain ⟨middle, after, hreachResult, hcodeResult, hreachError, hcodeError⟩ :=
    accessorTraces_of_compiled hplatform hloads
      (codeIntact_of_mem_eq hframe.mem hexit.2.1)
      (decoderGlobalsScalarRep_of_mem_eq hframe.mem hglobals.1)
      (storedResultDiscriminantRep_of_mem_eq hframe.mem hglobals.2.1)
  refine rejectedRun_of_rejectedAccessorTraces input hrun htrace hbound hcodeFinal htagFinal hstatus
    ⟨middle, after, hreachResult, ?_, hreachError, hcodeError⟩
  rw [hcodeResult, hmeaning, freshGlobals_error_pointer]

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
