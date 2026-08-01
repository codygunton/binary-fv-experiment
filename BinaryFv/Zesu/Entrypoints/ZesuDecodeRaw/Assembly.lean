import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.SentinelAssembly
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeGlue

/-!
# The capstone: a complete run of the wrapper, from the local contract assumptions alone

Three layers were built to meet here and this module is the joint.

* **The machine half** (`SentinelAssembly.lean`) turns a function instance's own
  `EnteredFunctionTrace` into a `TraceToSentinel`, by proving the exit `ret` retires onto the
  runner's sentinel. It needs the instance's obligation and an `ExitPlatform` bundle, nothing else.
* **The value half** (`DecodeGlue.lean`) turns the wrapper's exit binding into every non-trace field
  of `SuccessfulRun`/`RejectedRun`, from `catalogGroundsInSpec` and the input bound.
* **The joint** (`Accessors.lean`) assembles the two witnesses from exactly those pieces.

What this module supplies is the exported-contract seam and the three transports that carry a fact
established at one state to the state the next layer speaks about.

## The three transports, and why each is not bookkeeping

**Across the exit `ret`** (`ExitRetFrame`, proved in `SentinelAssembly.lean`). Every contract
postcondition is about the state the exit instruction is *reached in*; every observation the runner
makes is at the state the trace *ends in*, one retirement later. The two are not the same state and
nothing related them, so `SuccessfulRun.returnCode` — `observeReturnCode? finalState = some 1` —
could not be built from the wrapper's `a0` clause at all. The `ret` writes four registers over an
untouched memory, and that is exactly what the frame records.

**Across the accessor prologue** (`exitPlatform_accessorSetup`). `runAccessor` writes `ra`, `sp`,
`PC` and `nextPC` before entering. `ra` is in `platformPreserved`, so the transport is *not* the
trivial framing argument the other three get: it holds because the prologue writes the sentinel that
the runner had already put there. Where that is not true, the accessor's `ret` has nowhere to land.

**Across an accessor call** (`decoderGlobalsScalarRep_survives_accessor`). `zesu_raw_error`'s entry
binding wants the scalar globals at the state `zesu_raw_result` returned in, and `postRawResult` says
nothing about the globals directly — only that the call writes nowhere outside its own (empty) record
and the stack. So the transport is the ownership clause plus the fact that the decoder's private
`.bss` is not the runner's stack, which `canonicalStack_disjoint_from_globals` settles.

## What is assumed here

The wrapper and two accessor contracts, grouped as `ExportedContractAssumptions`.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.MemoryRepresentation
open BinaryFv.Zesu.Elflings.Validation
open BinaryFv.Zesu.Elflings.Generated (generatedProgram)
open LeanRV64DExecutable.Functions Register

set_option maxRecDepth 100000

/-! ## Reading a memory-only fact at a later state

Six predicates the layers above trade in read `.mem` and nothing else, so each survives any step that
leaves memory alone — which is what both the exit `ret` and the accessor prologue do. They are stated
rather than inlined because `▸` cannot see through them: `DecoderGlobalsScalarRep` mentions no state
component syntactically, so rewriting with a memory equation does not apply to it. -/

/-- The borrowed input window. -/
theorem memoryBytes_of_mem_eq {s t : State} {base : Nat} {bytes : ByteArray}
    (hmem : t.mem = s.mem) (h : MemoryBytes s base bytes) : MemoryBytes t base bytes := by
  intro index hindex; rw [hmem]; exact h index hindex

/-- The pinned image's file bytes. -/
theorem codeIntact_of_mem_eq {env : DecoderEnvironment} {s t : State} (hmem : t.mem = s.mem)
    (h : env.CodeIntact s) : env.CodeIntact t :=
  show env.image.fileBytesMatchMemory t.mem from hmem ▸ h

/-- The `attempted` flag and the 32-bit status word. -/
theorem decoderGlobalsScalarRep_of_mem_eq {layout : DecoderGlobalsLayout}
    {model : DecoderGlobalsModel} {s t : State} (hmem : t.mem = s.mem)
    (h : DecoderGlobalsScalarRep layout model s) : DecoderGlobalsScalarRep layout model t := by
  refine ⟨?_, ?_⟩
  · show t.mem.get? _ = _
    rw [hmem]; exact h.1
  · intro index hindex
    rw [hmem]; exact h.2 index hindex

/-- The inline `stored_result` discriminant byte. -/
theorem storedResultDiscriminantRep_of_mem_eq {layout : DecoderGlobalsLayout}
    {model : DecoderGlobalsModel} {s t : State} (hmem : t.mem = s.mem)
    (h : StoredResultDiscriminantRep layout model s) :
    StoredResultDiscriminantRep layout model t := by
  show t.mem.get? _ = _
  rw [hmem]; exact h

/-- The runner's own discriminant observation. -/
theorem observeOptionTag_of_mem_eq {s t : State} {base : Nat} {tag : Bool} (hmem : t.mem = s.mem)
    (h : observeOptionTag? s base = some tag) : observeOptionTag? t base = some tag := by
  unfold observeOptionTag? at h ⊢; rw [hmem]; exact h

/-- The decoded value's whole representation. Not memory-only definitionally — it is a nest of
structures — so this goes through the root's own footprint transport, with the agreement discharged
from the memory equation at every address rather than at a chosen region. -/
theorem rawV4Rep_of_mem_eq {s t : State} {inputBase rootBase : Nat} {input : ByteArray}
    {value : BinaryFv.Specs.SSZ.RawV4} (hmem : t.mem = s.mem)
    (h : RawV4Rep s inputBase input rootBase value) :
    RawV4Rep t inputBase input rootBase value := by
  obtain ⟨_, htransport⟩ :=
    Footprint.rawV4_footprint_abi inputBase input rootBase value s
      BinaryFv.Zesu.Artifacts.raw_stateless_input_layout.1 h
  exact htransport _ (fun address _ => (congrArg (·.get? address) hmem).symm)

/-- The C-ABI return code, at a state that agrees on `a0`. -/
theorem observeReturnCode_of_regs_eq {s t : State} {code : Nat}
    (hregs : t.regs.get? x10 = s.regs.get? x10) (h : observeReturnCode? s = some code) :
    observeReturnCode? t = some code := by
  unfold observeReturnCode? at h ⊢; rw [hregs]; exact h

/-- Every `DecodeStatus` code is one of six small numbers, so the `BitVec.toNat` round trip
`observeReturnCode?` performs loses nothing. The rejected branch's analogue of
`returnCode_lt_two_pow_64`. -/
theorem statusCode_lt_two_pow_64 (status : DecodeStatus) : status.code < 2 ^ 64 := by
  cases status <;> decide

/-! ## The decoder's private globals survive an accessor call

`postRawResult`'s ownership clause is `WritesOnlyWithinOwnRecord 0 0` — "writes nothing outside its
own stack frame". Turning that into "the globals still read the same" needs the globals to be outside
the stack, which is a fact about two pinned address ranges rather than about the function instance. -/

/-- **Nothing in the decoder's `.bss` is inside an accessor's write permission.** The record half is
empty by construction (`recordBase = recordSize = 0`, an accessor produces no record); the stack half
is `canonicalStack_disjoint_from_globals`. -/
theorem globals_outside_accessor_permission {address : Nat} (below : address < globalsCeiling) :
    ¬ Region.union (allocatedRegion 0 0 0 0) canonicalEnvironment.stack address := by
  rintro (hrecord | hstack)
  · rcases hrecord with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  · exact canonicalStack_disjoint_from_globals address below hstack

/-- Every byte either accessor's entry binding reads is inside the decoder's `.bss`. Read off the
generated layout, so a relocated global fails here rather than making the transports above vacuous. -/
theorem decoderGlobals_below_ceiling :
    Elflings.canonicalDecoderGlobalsLayout.attempted < globalsCeiling ∧
      Elflings.canonicalDecoderGlobalsLayout.status + 3 < globalsCeiling ∧
      Elflings.canonicalDecoderGlobalsLayout.storedResult
          + Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset
        < globalsCeiling := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The address `zesu_raw_result` returns on success is inside the decoder's `.bss` too, hence a
genuine machine address. Named rather than inlined so the `native_decide` door it opens is owned by a
one-line fact instead of by the assembly theorem that spends it. -/
theorem canonicalResultBuffer_below_ceiling : Elflings.canonicalResultBuffer < globalsCeiling := by
  native_decide

/-- **`zesu_raw_error`'s entry binding survives the `zesu_raw_result` call**, which is the one place
the two accessor calls are not independent: the second is entered from the state the first returned
in. -/
theorem decoderGlobalsScalarRep_survives_accessor {before after : State}
    {model : DecoderGlobalsModel}
    (frame : canonicalEnvironment.WritesOnlyWithinOwnRecord 0 0 before after)
    (h : DecoderGlobalsScalarRep Elflings.canonicalDecoderGlobalsLayout model before) :
    DecoderGlobalsScalarRep Elflings.canonicalDecoderGlobalsLayout model after := by
  obtain ⟨hflag, hword⟩ := h
  refine ⟨?_, ?_⟩
  · show after.mem.get? _ = _
    rw [frame _ (globals_outside_accessor_permission decoderGlobals_below_ceiling.1)]
    exact hflag
  · intro index hindex
    rw [frame _ (globals_outside_accessor_permission
      (show Elflings.canonicalDecoderGlobalsLayout.status + index < globalsCeiling by
        have := decoderGlobals_below_ceiling.2.1; omega))]
    exact hword index hindex

/-- The discriminant byte survives it too, for the same reason. Not consumed by `zesu_raw_error`'s
own binding, but carried so the accepted branch's `storedPresent` stays available. -/
theorem storedResultDiscriminantRep_survives_accessor {before after : State}
    {model : DecoderGlobalsModel}
    (frame : canonicalEnvironment.WritesOnlyWithinOwnRecord 0 0 before after)
    (h : StoredResultDiscriminantRep Elflings.canonicalDecoderGlobalsLayout model before) :
    StoredResultDiscriminantRep Elflings.canonicalDecoderGlobalsLayout model after := by
  show after.mem.get? _ = _
  rw [frame _ (globals_outside_accessor_permission decoderGlobals_below_ceiling.2.2)]
  exact h

/-! ## The exit bundle, carried along the whole run

`buildZesuEntryState_exitPlatform` establishes `ExitPlatform` at all three attachment addresses at
the state the builder produces. Every later attachment needs it at a *later* state, and each hop is
one of the two lemmas below. Carrying all three addresses at once rather than the one each hop needs
is deliberate: the accessors' bundles are wanted after the wrapper's `ret`, so a hop that dropped the
other two would have to be re-run. -/

/-- **The canonical environment's `CodeIntact` is the pinned image's**, spelled the way
`ExitPlatform.code` spells it. Stated rather than left to unification: `canonicalEnvironment` carries
an 86 KB byte array, and letting the elaborator discover the projection at each use costs a `whnf`
timeout instead of a rewrite. -/
theorem programImage_of_codeIntact {state : State} (h : canonicalEnvironment.CodeIntact state) :
    Artifacts.programImage.fileBytesMatchMemory state.mem := by
  have himage : canonicalEnvironment.image = Artifacts.programImage := by
    simp only [canonicalEnvironment]
  have h' : canonicalEnvironment.image.fileBytesMatchMemory state.mem := h
  rwa [himage] at h'

/-- One hop across a callee that honours the frame clauses — which is every contract in this
target. -/
theorem exitPlatforms_of_agree {before after : State}
    (agree : Agree platformPreserved before after) (retired : RetiredCounterPresent after)
    (code : canonicalEnvironment.CodeIntact after)
    (h : ∀ pc ∈ sentinelExitPcs, ExitPlatform before pc) :
    ∀ pc ∈ sentinelExitPcs, ExitPlatform after pc :=
  fun pc hpc => exitPlatform_of_agree agree retired (programImage_of_codeIntact code) (h pc hpc)

/-- One hop across the exit `ret` itself. -/
theorem exitPlatforms_of_exitRetFrame {before after : State} (frame : ExitRetFrame before after)
    (code : canonicalEnvironment.CodeIntact before)
    (h : ∀ pc ∈ sentinelExitPcs, ExitPlatform before pc) :
    ∀ pc ∈ sentinelExitPcs, ExitPlatform after pc :=
  exitPlatforms_of_agree frame.agree frame.retired (codeIntact_of_mem_eq frame.mem code) h

/-! ## The exported-contract seam

The runner needs the wrapper and the two accessors, not a generated per-instance manifest. Keeping
this structure beside its consumer makes the dependency exact. -/

structure ExportedContractAssumptions : Prop where
  decode :
    ∀ {functionInstance : FunctionInstance},
      Program.find? generatedProgram generatedProgram.entry = some functionInstance →
        BinaryFv.RiscV.Elfling.FunctionInstanceContract.Implements
          (functionInstanceExecutionPcs generatedProgram functionInstance)
          (functionInstanceExitPred functionInstance)
          (functionInstanceEntryWord functionInstance)
          (functionInstanceZesuDecodeRaw canonicalContractParams.env
            canonicalContractParams.globals canonicalContractParams.resultBuffer
            canonicalContractParams.repRawV4 DecoderGlobalsModel.fresh)
  rawResult :
    ∀ {functionInstance : FunctionInstance},
      functionInstance ∈ generatedProgram.functionInstances →
      functionInstance.entryPc = resolvedSymbols.rawResult →
        BinaryFv.RiscV.Elfling.Implements
          (functionInstanceExecutionPcs generatedProgram functionInstance)
          (functionInstanceExitPred functionInstance)
          (functionInstanceEntryWord functionInstance)
          (contractRawResult canonicalContractParams.env canonicalContractParams.globals
            canonicalContractParams.resultBuffer)
  rawError :
    ∀ {functionInstance : FunctionInstance},
      functionInstance ∈ generatedProgram.functionInstances →
      functionInstance.entryPc = resolvedSymbols.rawError →
        BinaryFv.RiscV.Elfling.Implements
          (functionInstanceExecutionPcs generatedProgram functionInstance)
          (functionInstanceExitPred functionInstance)
          (functionInstanceEntryWord functionInstance)
          (contractRawError canonicalContractParams.env canonicalContractParams.globals)

/-! ## Both accessor calls, from the exported contracts

Stated once, at an arbitrary ghost model, because the accepted and rejected branches differ only in
which model the wrapper recorded — and both accessors' answers are functions of it. That is the whole
reason `AcceptedAccessorTraces` and `RejectedAccessorTraces` have the same shape. -/

/-- **The accessor residue, discharged.** Both exported accessors run from `state` to their sentinels
within their own contract bounds, returning what their contracts say at `model`. -/
theorem accessorTraces_of_exported (contracts : ExportedContractAssumptions) {state : State}
    {model : DecoderGlobalsModel} (hplatform : ∀ pc ∈ sentinelExitPcs, ExitPlatform state pc)
    (hcode : canonicalEnvironment.CodeIntact state)
    (hscalar : DecoderGlobalsScalarRep Elflings.canonicalDecoderGlobalsLayout model state)
    (hstored : StoredResultDiscriminantRep Elflings.canonicalDecoderGlobalsLayout model state) :
    ∃ middle after : State,
      AccessorReachesSentinel resolvedSymbols.rawResult rawResultStepBound state middle ∧
      observeReturnCode? middle
        = some (if model.stored.isSome then Elflings.canonicalResultBuffer else 0) ∧
      AccessorReachesSentinel resolvedSymbols.rawError rawErrorStepBound middle after ∧
      observeReturnCode? after = some model.status.code := by
  obtain ⟨nodes, hn⟩ := controlFlow_some
  -- `zesu_raw_result`, from the runner's prologue over `state`.
  obtain ⟨fiResult, hmemResult, hentryResult⟩ := rawResult_function_instance_found
  obtain ⟨countResult, atExitResult, hboundResult, hrunResult, hpostResult⟩ :=
    contracts.rawResult hmemResult hentryResult model 0
      (accessorSetup resolvedSymbols.rawResult state)
      (contractRawResult_entry_accessorSetup (resultBuffer := canonicalContractParams.resultBuffer)
        _ hcode hstored)
  obtain ⟨middle, -, hreachResult, -, hframeResult⟩ :=
    rawResultReachesSentinel_of_enteredFunctionTrace hn hmemResult hentryResult hboundResult
      (exitPlatform_of_agree hpostResult.2.2.2.1 hpostResult.2.2.2.2.1
        (programImage_of_codeIntact hpostResult.1)
        (exitPlatform_accessorSetup _ (hplatform 0x137A8 (by decide))))
      hrunResult
  -- The pointer it returned, read where the runner reads it: after the `ret`, not at the exit.
  have hpointerBound :
      (if model.stored.isSome then Elflings.canonicalResultBuffer else 0) < 2 ^ 64 := by
    have hbelow := canonicalResultBuffer_below_ceiling
    have hceiling := runtime_below_ceiling.2
    have : loadedCeiling < 2 ^ 64 := by decide
    split <;> omega
  have hcodeResult : observeReturnCode? middle
      = some (if model.stored.isSome then Elflings.canonicalResultBuffer else 0) :=
    observeReturnCode_of_a0 hpointerBound
      (hframeResult.returnValue.trans hpostResult.2.2.2.2.2.2)
  -- `zesu_raw_error`, entered from the state `zesu_raw_result` returned in.
  obtain ⟨fiError, hmemError, hentryError⟩ := rawError_function_instance_found
  have hcodeMiddle : canonicalEnvironment.CodeIntact middle :=
    codeIntact_of_mem_eq hframeResult.mem hpostResult.1
  have hscalarMiddle : DecoderGlobalsScalarRep Elflings.canonicalDecoderGlobalsLayout model middle :=
    decoderGlobalsScalarRep_of_mem_eq hframeResult.mem
      (decoderGlobalsScalarRep_survives_accessor hpostResult.2.2.1 hscalar)
  obtain ⟨countError, atExitError, hboundError, hrunError, hpostError⟩ :=
    contracts.rawError hmemError hentryError model 0
      (accessorSetup resolvedSymbols.rawError middle)
      (contractRawError_entry_accessorSetup _ hcodeMiddle hscalarMiddle)
  obtain ⟨after, -, hreachError, -, hframeError⟩ :=
    rawErrorReachesSentinel_of_enteredFunctionTrace hn hmemError hentryError hboundError
      (exitPlatform_of_agree hpostError.2.2.2.1 hpostError.2.2.2.2.1
        (programImage_of_codeIntact hpostError.1)
        (exitPlatform_accessorSetup _
          (exitPlatforms_of_exitRetFrame hframeResult hpostResult.1
            (exitPlatforms_of_agree hpostResult.2.2.2.1 hpostResult.2.2.2.2.1 hpostResult.1
              (fun pc hpc => exitPlatform_accessorSetup _ (hplatform pc hpc)))
            0x13788 (by decide))))
      hrunError
  refine ⟨middle, after, hreachResult, hcodeResult, hreachError, ?_⟩
  exact observeReturnCode_of_a0 (statusCode_lt_two_pow_64 model.status)
    (hframeError.returnValue.trans hpostError.2.2.2.2.2.2)

/-! ## The wrapper's own run

Everything above the accessors, in one existential: the builder's run, the composed sentinel trace
inside the runner's budget, the exit binding at the state the exit was reached in, the frame that
carries it forward, and the exit bundle still standing where the accessors need it. -/

/-- **A complete run of the exported wrapper, from the local proofs alone.** -/
theorem decodeRun_of_exported (contracts : ExportedContractAssumptions) (input : ByteArray) :
    ∃ (entryState atExit finalState : State) (count : Nat),
      Runs (buildZesuEntryState input) initialState entryState () ∧
      TraceToSentinel sentinelWord 0 (count + 1) entryState finalState ∧
      count + 1 ≤ entryStepBound input.size + 1 ∧
      CanonicalDecodeExit input entryState atExit ∧
      ExitRetFrame atExit finalState ∧
      (∀ pc ∈ sentinelExitPcs, ExitPlatform finalState pc) := by
  obtain ⟨nodes, hn⟩ := controlFlow_some
  obtain ⟨fi, hfind⟩ : ∃ fi, Program.find? generatedProgram generatedProgram.entry = some fi :=
    Option.isSome_iff_exists.mp entry_function_instance_found
  -- One state, with both the entry binding and the exit bundle: `buildZesuEntryState_exitPlatform`
  -- and `buildZesuEntryState_entry_binding` are separate existentials over the same builder, so the
  -- ABI theorem they are both derived from is what pins them to the same state.
  obtain ⟨entryState, hrun, hbinding, hlink, -, hnormal, hpresent, hpinned, -⟩ :=
    buildZesuEntryState_entry_binding_abi input
  obtain ⟨hpma, hhtif⟩ := hpinned sentinelExitPcs configureFetchPinned_sentinelExits
  have hcodeEntry : Artifacts.programImage.fileBytesMatchMemory entryState.mem :=
    programImage_of_codeIntact hbinding.2.1
  have hplatformEntry : ∀ pc ∈ sentinelExitPcs, ExitPlatform entryState pc := by
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
  -- The wrapper's own obligation, applied at that state.
  obtain ⟨count, atExit, hbound, hrunTrace, hexit⟩ :=
    canonicalDecodeExit_of_implements (contracts.decode hfind) input 0 hbinding
  obtain ⟨finalState, htrace, -, -, hframe⟩ :=
    entryTraceToSentinel_of_enteredFunctionTrace hn hfind
      (exitPlatform_of_agree hexit.2.2.2.1 hexit.2.2.2.2.1
        (programImage_of_codeIntact hexit.2.1) (hplatformEntry 0x10378 (by decide)))
      hrunTrace
  exact ⟨entryState, atExit, finalState, count, hrun, htrace, by omega, hexit, hframe,
    exitPlatforms_of_exitRetFrame hframe hexit.2.1
      (exitPlatforms_of_agree hexit.2.2.2.1 hexit.2.2.2.2.1 hexit.2.1 hplatformEntry)⟩

/-! ## The two witnesses

Each is the wrapper's run, the value half read off its exit binding, and the accessor residue at the
model the wrapper recorded. No machine reasoning happens here; every step is one of the three
transports or one of the two halves. -/

/-- **An accepted input has a successful run.** -/
theorem successfulRun_of_exported (contracts : ExportedContractAssumptions) {input : ByteArray}
    (inputBound : input.size < 2 * 1024 * 1024) {value : BinaryFv.Specs.SSZ.RawV4}
    (accepts : BinaryFv.Specs.SSZ.decode input = .accepted value) : Nonempty (SuccessfulRun input value) := by
  obtain ⟨entryState, atExit, finalState, count, hrun, htrace, hbound, hexit, hframe, hplatform⟩ :=
    decodeRun_of_exported contracts input
  obtain ⟨hcode, htag, hinput, hvalue⟩ :=
    successfulRun_fields_of_canonicalDecodeExit catalogGroundsInSpec_holds inputBound accepts hexit
  -- The four decode-side observations, moved across the `ret` the trace ends with.
  have hcodeFinal : observeReturnCode? finalState = some 1 :=
    observeReturnCode_of_regs_eq hframe.returnValue hcode
  have htagFinal : observeOptionTag? finalState storedResultDiscriminantAddr = some true :=
    observeOptionTag_of_mem_eq hframe.mem htag
  have hinputFinal : MemoryBytes finalState canonicalRunnerLayout.inputBase input :=
    memoryBytes_of_mem_eq hframe.mem hinput
  have hvalueFinal : RawV4Rep finalState canonicalRunnerLayout.inputBase input
      Elflings.canonicalResultBuffer value := rawV4Rep_of_mem_eq hframe.mem hvalue
  -- The model the wrapper recorded, and the accessor residue at it.
  have hmeaning : meaningDecode input = .ok value :=
    meaningDecode_ok_of_spec_accepts catalogGroundsInSpec_holds inputBound accepts
  have hglobals := hexit.2.2.2.2.2
  rw [hmeaning] at hglobals
  obtain ⟨middle, after, hreachResult, hcodeResult, hreachError, hcodeError⟩ :=
    accessorTraces_of_exported contracts hplatform (codeIntact_of_mem_eq hframe.mem hexit.2.1)
      (decoderGlobalsScalarRep_of_mem_eq hframe.mem hglobals.1)
      (storedResultDiscriminantRep_of_mem_eq hframe.mem hglobals.2.1)
  refine successfulRun_of_acceptedAccessorTraces input value hrun htrace hbound hcodeFinal htagFinal
    hinputFinal hvalueFinal ⟨middle, after, hreachResult, ?_, hreachError, ?_⟩
  · rw [hcodeResult, freshGlobals_ok_pointer]
  · rw [hcodeError, freshGlobals_ok_statusCode]

/-- **A rejected input has a rejected run**, at the status the wrapper recorded — the same number
`zesu_raw_error` returns from that model, which is what makes the two halves name one status rather
than two. -/
theorem rejectedRun_of_exported (contracts : ExportedContractAssumptions) {input : ByteArray}
    (inputBound : input.size < 2 * 1024 * 1024)
    (rejects : BinaryFv.Specs.SSZ.decode input = .rejected) : Nonempty (RejectedRun input) := by
  obtain ⟨entryState, atExit, finalState, count, hrun, htrace, hbound, hexit, hframe, hplatform⟩ :=
    decodeRun_of_exported contracts input
  obtain ⟨hcode, htag, hinput, hstatus⟩ :=
    rejectedRun_fields_of_canonicalDecodeExit catalogGroundsInSpec_holds inputBound rejects hexit
  have hcodeFinal : observeReturnCode? finalState = some 0 :=
    observeReturnCode_of_regs_eq hframe.returnValue hcode
  have htagFinal : observeOptionTag? finalState storedResultDiscriminantAddr = some false :=
    observeOptionTag_of_mem_eq hframe.mem htag
  obtain ⟨error, hmeaning⟩ :=
    meaningDecode_error_of_spec_rejects catalogGroundsInSpec_holds inputBound rejects
  have hglobals := hexit.2.2.2.2.2
  obtain ⟨middle, after, hreachResult, hcodeResult, hreachError, hcodeError⟩ :=
    accessorTraces_of_exported contracts hplatform (codeIntact_of_mem_eq hframe.mem hexit.2.1)
      (decoderGlobalsScalarRep_of_mem_eq hframe.mem hglobals.1)
      (storedResultDiscriminantRep_of_mem_eq hframe.mem hglobals.2.1)
  refine rejectedRun_of_rejectedAccessorTraces input hrun htrace hbound hcodeFinal htagFinal hstatus
    ⟨middle, after, hreachResult, ?_, hreachError, hcodeError⟩
  rw [hcodeResult, hmeaning, freshGlobals_error_pointer]

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
