import BinaryFv.Zesu.MachineExecution.Level2FirstSuccessToExit
import BinaryFv.Zesu.MachineExecution.Level2FirstInvalidPrefixMismatchToExit
import BinaryFv.Zesu.MachineExecution.Level2FirstInvalidShortToExit
import BinaryFv.Zesu.MachineExecution.Level2FirstInvalidExactToExit
import BinaryFv.Zesu.MachineExecution.Level2FirstInvalidExactSuccessToExit
import BinaryFv.Zesu.MachineExecution.Level2PropagatedErrorToExit
import BinaryFv.Zesu.MachineExecution.Level2RetryExactToExit
import BinaryFv.Zesu.MachineExecution.Level2RetryPrefixMismatchToExit
import BinaryFv.Zesu.MachineExecution.Level2RetryShortToExit
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeGlue
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2SummaryComposition
import Lean.Elab.Tactic.Omega

/-!
# Conditional Level 2 wrapper contract

The route proofs stop at the generated wrapper exit and retain their owned `ScopedTrace`s.  The
exported contract additionally needs a flat trace over the wrapper's execution extent and the full
`postZesuDecodeRaw` globals representation.  The two named edges below are the remaining work that
connects those concrete route results to that exported boundary; their conclusions spell out the
bound, trace, and postcondition instead of packaging them in an opaque assumption.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Elflings.Generated
open BinaryFv.Zesu.MachineExecution
open LeanRV64DExecutable.Functions Register

/-- The real routes that can follow a failed first `meaningDecodeRaw` attempt.  Each constructor
retains the route's actual final state, rather than replacing its Sail evidence by a tag or an ABI
claim. -/
inductive Level2NonFirstRoute (args : ZesuDecodeRawArgs) (fromStep : Nat) (entry after : State) : Prop where
  | firstInvalidShort
      {atDecode firstAfter branch retryBefore childAfter handoff afterTail afterStore : State}
      {firstUsed retryUsed : Nat} {branchRetired retryRetired link s0 s1 s2 : BitVec 64}
      (route : FirstInvalidShortToExitResult args stackBase fromStep entry atDecode firstAfter branch
        retryBefore childAfter handoff afterTail afterStore after firstUsed retryUsed branchRetired
        retryRetired link s0 s1 s2) :
      Level2NonFirstRoute args fromStep entry after
  | firstInvalidPrefixMismatch
      {atDecode firstAfter branch retryBefore childAfter handoff afterTail afterStore : State}
      {firstUsed retryUsed : Nat} {branchRetired retryRetired link s0 s1 s2 : BitVec 64}
      (route : FirstInvalidPrefixMismatchToExitResult args stackBase fromStep entry atDecode firstAfter
        branch retryBefore childAfter handoff afterTail afterStore after firstUsed retryUsed
        branchRetired retryRetired link s0 s1 s2) :
      Level2NonFirstRoute args fromStep entry after
  | firstInvalidExactSuccess
      {atDecode firstAfter branch retryBefore childAfter dispatch copyStart callState afterCopy routeAfter afterStore : State}
      {firstUsed retryUsed copyUsed : Nat} {branchRetired retryRetired link s0 s1 s2 : BitVec 64}
      {value : BinaryFv.Specs.SSZ.StatelessInput} {contents : ByteArray}
      (route : FirstInvalidExactSuccessToExitResult args stackBase fromStep entry atDecode firstAfter branch
        retryBefore childAfter dispatch copyStart callState afterCopy routeAfter afterStore after firstUsed retryUsed
        copyUsed branchRetired retryRetired link s0 s1 s2 value contents) :
      Level2NonFirstRoute args fromStep entry after
  | firstInvalidExactError
      {atDecode firstAfter branch retryBefore childAfter dispatch routeAfter afterStore : State}
      {firstUsed retryUsed : Nat} {error : Contracts.DecodeError} {link s0 s1 s2 : BitVec 64}
      (route : FirstInvalidExactErrorToExitResult args stackBase fromStep entry atDecode firstAfter branch
        retryBefore childAfter dispatch routeAfter afterStore after firstUsed retryUsed error link s0 s1 s2) :
      Level2NonFirstRoute args fromStep entry after
  | firstPropagatedError
      {atDecode firstAfter branch retryBefore childAfter dispatch routeAfter afterStore : State}
      {firstUsed propagatedUsed : Nat} {error : Contracts.DecodeError}
      {branchRetired retryRetired link s0 s1 s2 : BitVec 64}
      (route : FirstPropagatedErrorToExitResult args stackBase fromStep entry atDecode firstAfter branch
        retryBefore childAfter dispatch routeAfter afterStore after firstUsed propagatedUsed error
        branchRetired retryRetired link s0 s1 s2) :
      Level2NonFirstRoute args fromStep entry after

/-- Every non-first constructor now includes the wrapper-owned prefix that reaches the particular
retry or propagated-error state it starts from.  The old retry-only constructors accepted an
unrelated `entry`, which made the exported trace conclusion unprovable. -/
theorem Level2NonFirstRoute.scopedTrace
    {args : ZesuDecodeRawArgs} {fromStep : Nat} {entry after : State}
    (route : Level2NonFirstRoute args fromStep entry after) :
    ∃ count, WrapperScopedTrace fromStep count entry after := by
  cases route with
  | firstInvalidShort route =>
      exact ⟨_, route.scopedTrace⟩
  | firstInvalidPrefixMismatch route =>
      exact ⟨_, route.scopedTrace⟩
  | firstInvalidExactSuccess route =>
      exact ⟨_, route.scopedTrace⟩
  | firstInvalidExactError route =>
      exact ⟨_, route.scopedTrace⟩
  | firstPropagatedError route =>
      exact ⟨_, route.scopedTrace⟩

/-- Converts the concrete first-success route into the exported wrapper boundary.  In particular,
this edge must expand the route's `ScopedTrace` and establish the final `DecoderGlobalsRep`; neither
fact follows from its exit-register fields alone. -/
def FirstSuccessRouteToExportedPost : Prop :=
  ∀ {args : ZesuDecodeRawArgs} {stackBase fromStep : Nat}
    {entry atDecode atCall resumed callState afterCopy routeAfter afterStore after : State}
    {value : BinaryFv.Specs.SSZ.StatelessInput} {contents : ByteArray}
    {link savedS0 savedS1 savedS2 : BitVec 64} {childUsed calleeUsed copyUsed : Nat},
    preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry →
    ZesuDecodeRawMachinePre args stackBase entry →
    meaningDecodeRaw args.bytes = .ok value →
    FirstSuccessToExitResult args stackBase fromStep entry atDecode atCall resumed callState afterCopy
      routeAfter afterStore after value contents link savedS0 savedS1 savedS2 childUsed calleeUsed copyUsed →
    ∃ count : Nat,
      count ≤ compiledZesuDecodeRawContract.binding.stepBound args ∧
      EnteredFunctionTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceEntryWord functionInstance_raw_decoder_root_zesu_decode_raw)
        fromStep count entry after ∧
      postZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
        canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
        DecoderGlobalsModel.fresh args (meaningDecode args.bytes) entry after

/-- The concrete first-success route already retains the wrapper-wide trace, the two emitted-copy
bounds, and the first `decodeRaw` success bound.  Flatten those selected summaries and expose the
route's concrete final export frame. -/
theorem firstSuccessRouteToExportedPost : FirstSuccessRouteToExportedPost := by
  intro args stackBase fromStep entry atDecode atCall resumed callState afterCopy routeAfter afterStore
    after value contents link savedS0 savedS1 savedS2 childUsed calleeUsed copyUsed source machine success
    route
  let count := 37 + childUsed + calleeUsed + copyUsed
  have bound : count ≤ compiledZesuDecodeRawContract.binding.stepBound args := by
    change 37 + childUsed + calleeUsed + copyUsed ≤
      2 * (16384 + 512 * args.bytes.size) + 1024
    have decodeBound := route.decodeBound
    have firstMemcpyBound := route.firstMemcpy.copyBound
    have tag0CopyBound := route.tag0.copy.copyBound
    omega
  have trace : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      fromStep count entry after := by
    simpa [count] using route.scopedTrace.toFunctionTrace level2ChildSummary_composes_decodeRaw
  have entered : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceEntryWord functionInstance_raw_decoder_root_zesu_decode_raw)
      fromStep count entry after := by
    refine ⟨?_, ?_, ?_, trace⟩
    · simpa [functionInstanceEntryWord,
        functionInstance_raw_decoder_root_zesu_decode_raw] using machine.atEntry
    · owned_pc
    · owned_pc
  have decoded : meaningDecode args.bytes = .ok value := by
    simp [Contracts.meaningDecode, success]
  exact ⟨count, bound, entered, by simpa [decoded] using route.exportFrame.postZesuDecodeRaw⟩

/-- Produces one real non-first route from the wrapper entry.  This is the remaining retry and
propagation-control-flow composition, separated from the exported-post transport below so that the
latter cannot silently assume a route that the machine proof never reached. -/
def NonFirstRoutesFromEntry : Prop :=
  ∀ {args : ZesuDecodeRawArgs} {stackBase fromStep : Nat} {entry : State}
    {rawError : Contracts.DecodeError},
    preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry →
    ZesuDecodeRawMachinePre args stackBase entry →
    meaningDecodeRaw args.bytes = .error rawError →
    ∃ after, Level2NonFirstRoute args fromStep entry after

/-- Produce the two non-exact first-`invalidSsz` routes from the exported wrapper entry.  This is
the concrete short/prefix-mismatch portion of `NonFirstRoutesFromEntry`; the exact-prefix and
first propagated-error cases remain separate because they use distinct selected child exits. -/
theorem first_invalid_nonexact_routes_from_entry
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    {args : ZesuDecodeRawArgs} {stackBase fromStep : Nat} {entry : State}
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (firstInvalid : meaningDecodeRaw args.bytes = .error .invalidSsz)
    (notExact : meaningHasExactErePrefix args.bytes = false) :
    ∃ after, Level2NonFirstRoute args fromStep entry after := by
  by_cases short : args.bytes.size < 4
  · obtain ⟨atDecode, firstAfter, branch, retryBefore, childAfter, handoff, afterTail, afterStore,
      after, firstUsed, retryUsed, branchRetired, retryRetired, link, s0, s1, s2, route⟩ :=
      first_invalid_short_to_exit allocator decode fromStep args stackBase entry source machine
        firstInvalid short
    exact ⟨after, .firstInvalidShort route⟩
  · have fourBytes : 4 ≤ args.bytes.size := by omega
    obtain ⟨atDecode, firstAfter, branch, retryBefore, childAfter, handoff, afterTail, afterStore,
      after, firstUsed, retryUsed, branchRetired, retryRetired, link, s0, s1, s2, route⟩ :=
      first_invalid_prefix_mismatch_to_exit allocator decode fromStep args stackBase entry source
        machine firstInvalid fourBytes notExact
    exact ⟨after, .firstInvalidPrefixMismatch route⟩

/-- Produce the first-`invalidSsz`, exact-prefix retry-success route from the exported entry. -/
theorem first_invalid_exact_success_route_from_entry
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    {args : ZesuDecodeRawArgs} {stackBase fromStep : Nat} {entry : State}
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (firstInvalid : meaningDecodeRaw args.bytes = .error .invalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (success : meaningDecode args.bytes = .ok value) :
    ∃ after, Level2NonFirstRoute args fromStep entry after := by
  obtain ⟨atDecode, firstAfter, branch, retryBefore, childAfter, dispatch, copyStart, contents, copyUsed,
    callState, afterCopy, routeAfter, afterStore, after, firstUsed, retryUsed, branchRetired, retryRetired,
    link, s0, s1, s2, route⟩ :=
    first_invalid_exact_success_to_exit allocator decode fromStep args stackBase entry source machine
      firstInvalid exactPrefix value success
  exact ⟨after, .firstInvalidExactSuccess route⟩

/-- Produce the first-`invalidSsz`, exact-prefix retry-error route from the exported entry. -/
theorem first_invalid_exact_error_route_from_entry
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    {args : ZesuDecodeRawArgs} {stackBase fromStep : Nat} {entry : State}
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (firstInvalid : meaningDecodeRaw args.bytes = .error .invalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true) (error : Contracts.DecodeError)
    (semanticResult : meaningDecode args.bytes = .error error) :
    ∃ after, Level2NonFirstRoute args fromStep entry after := by
  obtain ⟨atDecode, firstAfter, branch, retryBefore, childAfter, dispatch, routeAfter, afterStore,
    after, firstUsed, retryUsed, link, s0, s1, s2, route⟩ :=
    first_invalid_exact_error_to_exit allocator decode fromStep args stackBase entry source machine
      firstInvalid exactPrefix error semanticResult
  exact ⟨after, .firstInvalidExactError route⟩

/-- A first `unknownFork` or `outOfMemory` result takes the wrapper's real propagation entry. -/
theorem first_propagated_error_route_from_entry
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    {args : ZesuDecodeRawArgs} {stackBase fromStep : Nat} {entry : State}
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (error : Contracts.DecodeError) (notInvalid : error ≠ .invalidSsz)
    (rawResult : meaningDecodeRaw args.bytes = .error error) :
    ∃ after, Level2NonFirstRoute args fromStep entry after := by
  obtain ⟨atDecode, firstAfter, branch, retryBefore, childAfter, dispatch, routeAfter, afterStore,
    after, firstUsed, propagatedUsed, branchRetired, retryRetired, link, s0, s1, s2, route⟩ :=
    first_propagated_error_to_exit allocator decode fromStep args stackBase entry source machine
      error notInvalid rawResult
  exact ⟨after, .firstPropagatedError route⟩

/-- Converts one concrete non-first route into the exported wrapper boundary.  The route index pins
the same input, entry state, starting step, and final state used by the conclusion. -/
def NonFirstRouteToExportedPost : Prop :=
  ∀ {args : ZesuDecodeRawArgs} {stackBase fromStep : Nat} {entry after : State}
    {rawError : Contracts.DecodeError},
    preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry →
    ZesuDecodeRawMachinePre args stackBase entry →
    meaningDecodeRaw args.bytes = .error rawError →
    Level2NonFirstRoute args fromStep entry after →
    ∃ count : Nat,
      count ≤ compiledZesuDecodeRawContract.binding.stepBound args ∧
      EnteredFunctionTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceEntryWord functionInstance_raw_decoder_root_zesu_decode_raw)
        fromStep count entry after ∧
      postZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
        canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
        DecoderGlobalsModel.fresh args (meaningDecode args.bytes) entry after

/-- The factual portion of `NonFirstRouteToExportedPost`: every selected route already has its
flat wrapper trace and exported memory/register/global representation. The still-separate count
bound must be derived from the same retained route lengths rather than assumed here. -/
def NonFirstRouteExportedFacts : Prop :=
  ∀ {args : ZesuDecodeRawArgs} {stackBase fromStep : Nat} {entry after : State}
    {rawError : Contracts.DecodeError},
    preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry →
    ZesuDecodeRawMachinePre args stackBase entry →
    meaningDecodeRaw args.bytes = .error rawError →
    Level2NonFirstRoute args fromStep entry after →
    ∃ count : Nat,
      EnteredFunctionTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceEntryWord functionInstance_raw_decoder_root_zesu_decode_raw)
        fromStep count entry after ∧
      postZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
        canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
        DecoderGlobalsModel.fresh args (meaningDecode args.bytes) entry after

private theorem postZesuDecodeRaw_of_error_frame
    {args : ZesuDecodeRawArgs} {error : Contracts.DecodeError} {entry after : State}
    (inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes)
    (code : canonicalContractParams.env.CodeIntact after)
    (returnCode : after.regs.get? x10 = some (BitVec.ofNat 64 0))
    (platform : Agree platformPreserved entry after)
    (retired : RetiredCounterPresent after)
    (attempted : FlagRep after Elflings.canonicalDecoderGlobalsLayout.attempted true)
    (status : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status
      (Contracts.statusOfResult (.error error)).code)
    (storedTag : DecodedValue.OptionTagRep after
      (Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) false) :
    postZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args (.error error) entry after := by
  refine ⟨inputMemory, code, returnCode, platform, retired, ?_⟩
  rw [freshGlobals_error]
  exact ⟨⟨attempted, status⟩, ⟨storedTag, trivial⟩⟩

private theorem entered_wrapper_trace
    {args : ZesuDecodeRawArgs} {stackBase fromStep count : Nat} {entry after : State}
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (trace : WrapperScopedTrace fromStep count entry after) :
    EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceEntryWord functionInstance_raw_decoder_root_zesu_decode_raw)
      fromStep count entry after :=
  { startsAtEntry := machine.atEntry
    entryInRegion := by owned_pc
    entryNotExit := by owned_pc
    trace := trace.toFunctionTrace level2ChildSummary_composes_decodeRaw }

/-- Convert each completed first-invalid route into its actual exported postcondition and the flat
wrapper trace. Count arithmetic is deliberately absent: it is the remaining route-specific proof. -/
theorem nonFirstRoute_exportedFacts : NonFirstRouteExportedFacts := by
  intro args stackBase fromStep entry after rawError source machine rawResult route
  cases route with
  | firstInvalidShort route =>
      refine ⟨_, entered_wrapper_trace machine route.scopedTrace, ?_⟩
      have post := postZesuDecodeRaw_of_error_frame (error := .invalidSsz)
        route.inputMemory route.code route.exitResult route.platform route.retired route.attempted
        (by simpa [Contracts.statusOfResult, Contracts.DecodeStatus.code] using route.statusWord)
        route.storedTag
      simpa [route.semanticResult] using post
  | firstInvalidPrefixMismatch route =>
      refine ⟨_, entered_wrapper_trace machine route.scopedTrace, ?_⟩
      have post := postZesuDecodeRaw_of_error_frame (error := .invalidSsz)
        route.inputMemory route.code route.exitResult route.platform route.retired route.attempted
        (by simpa [Contracts.statusOfResult, Contracts.DecodeStatus.code] using route.statusWord)
        route.storedTag
      simpa [route.semanticResult] using post
  | firstInvalidExactSuccess route =>
      refine ⟨_, entered_wrapper_trace machine route.scopedTrace, ?_⟩
      simpa [route.semanticResult] using route.exportFrame.postZesuDecodeRaw
  | firstInvalidExactError route =>
      refine ⟨_, entered_wrapper_trace machine route.scopedTrace, ?_⟩
      have post := postZesuDecodeRaw_of_error_frame (error := _)
        route.inputMemory route.code route.exitResult route.platform route.retired route.attempted
        (by simpa [retryExactErrorStatus] using route.statusWord) route.storedTag
      simpa [route.semanticResult] using post
  | firstPropagatedError route =>
      refine ⟨_, entered_wrapper_trace machine route.scopedTrace, ?_⟩
      have post := postZesuDecodeRaw_of_error_frame (error := _)
        route.inputMemory route.code route.exitResult route.platform route.retired route.attempted
        (by simpa [Contracts.statusOfResult, Contracts.DecodeStatus.code] using route.statusWord)
        route.storedTag
      simpa [route.semanticResult] using post

/-- Every non-first route retains the bounds of the concrete Level 3 executions it actually
composes.  Combining those retained bounds with the wrapper-owned suffix gives the exported
function's step bound without replacing a route by a separate existential execution. -/
theorem nonFirstRouteToExportedPost : NonFirstRouteToExportedPost := by
  intro args stackBase fromStep entry after rawError source machine rawResult route
  cases route with
  | firstInvalidShort route =>
      refine ⟨_, ?_, entered_wrapper_trace machine route.scopedTrace, ?_⟩
      · change _ ≤ 2 * (16384 + 512 * args.bytes.size) + 1024
        have firstBound := route.firstInvalidBound
        have retryBound := route.retryShortBound
        omega
      · obtain ⟨_, _, post⟩ :=
        nonFirstRoute_exportedFacts source machine rawResult (.firstInvalidShort route)
        exact post
  | firstInvalidPrefixMismatch route =>
      refine ⟨_, ?_, entered_wrapper_trace machine route.scopedTrace, ?_⟩
      · change _ ≤ 2 * (16384 + 512 * args.bytes.size) + 1024
        have firstBound := route.firstInvalidBound
        have retryBound := route.retryPrefixMismatchBound
        omega
      · obtain ⟨_, _, post⟩ :=
        nonFirstRoute_exportedFacts source machine rawResult (.firstInvalidPrefixMismatch route)
        exact post
  | firstInvalidExactSuccess route =>
      refine ⟨_, ?_, entered_wrapper_trace machine route.scopedTrace, ?_⟩
      · change _ ≤ 2 * (16384 + 512 * args.bytes.size) + 1024
        have firstBound := route.firstInvalidBound
        have retryBound := route.retryExactBound
        have copyBound := route.copyBound
        have exactPrefix := route.exactPrefix
        have fourBytes : 4 ≤ args.bytes.size := by
          unfold meaningHasExactErePrefix at exactPrefix
          split at exactPrefix <;> simp_all
        rw [ByteArray.size_extract] at retryBound
        omega
      · obtain ⟨_, _, post⟩ :=
        nonFirstRoute_exportedFacts source machine rawResult (.firstInvalidExactSuccess route)
        exact post
  | firstInvalidExactError route =>
      rename_i stackBase' atDecode firstAfter branch retryBefore childAfter dispatch routeAfter afterStore
        firstUsed retryUsed error link s0 s1 s2
      refine ⟨_, ?_, entered_wrapper_trace machine route.scopedTrace, ?_⟩
      · change _ ≤ 2 * (16384 + 512 * args.bytes.size) + 1024
        have firstBound := route.firstInvalidBound
        have retryBound := route.retryExactBound
        have exactPrefix := route.exactPrefix
        have fourBytes : 4 ≤ args.bytes.size := by
          unfold meaningHasExactErePrefix at exactPrefix
          split at exactPrefix <;> simp_all
        rw [ByteArray.size_extract] at retryBound
        cases error <;> simp [retryExactErrorRouteSteps] at * <;> omega
      · obtain ⟨_, _, post⟩ :=
        nonFirstRoute_exportedFacts source machine rawResult (.firstInvalidExactError route)
        exact post
  | firstPropagatedError route =>
      rename_i stackBase' atDecode firstAfter branch retryBefore childAfter dispatch routeAfter afterStore
        firstUsed propagatedUsed error branchRetired retryRetired link s0 s1 s2
      refine ⟨_, ?_, entered_wrapper_trace machine route.scopedTrace, ?_⟩
      · change _ ≤ 2 * (16384 + 512 * args.bytes.size) + 1024
        have firstBound := route.firstBound
        have propagatedZero := route.propagatedZero
        cases error <;> simp_all <;> omega
      · obtain ⟨_, _, post⟩ :=
        nonFirstRoute_exportedFacts source machine rawResult (.firstPropagatedError route)
        exact post

/-- The conditional Level 2 refinement edge.  The success branch invokes the existing complete
first-success execution theorem; the non-first branch remains explicit because its retry-entry
composition and final globals proof are not yet one theorem. -/
theorem compiledZesuDecodeRawContract_of_level2_routes
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    (firstSuccess : FirstSuccessRouteToExportedPost)
    (nonFirstRoutes : NonFirstRoutesFromEntry)
    (nonFirst : NonFirstRouteToExportedPost) :
    CompiledZesuDecodeRawInstanceContract := by
  intro args fromStep entry pre
  change preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry ∧ CompiledZesuDecodeRawPre args entry at pre
  rcases pre with ⟨source, stackBase, machine⟩
  cases semantic : meaningDecodeRaw args.bytes with
  | ok value =>
      obtain ⟨atDecode, atCall, contents, childUsed, calleeUsed, resumed, link, savedS0, savedS1,
        savedS2, copyUsed, callState, afterCopy, routeAfter, afterStore, after, route⟩ :=
        first_success_to_exit allocator decode fromStep args stackBase entry
          source machine value semantic
      obtain ⟨count, bound, trace, post⟩ := firstSuccess source machine semantic route
      refine ⟨count, after, bound, trace, ?_⟩
      simpa only [compiledZesuDecodeRawContract, functionInstanceZesuDecodeRaw,
        specZesuDecodeRaw] using post
  | error rawError =>
      obtain ⟨after, route⟩ := nonFirstRoutes source machine semantic
      obtain ⟨count, bound, trace, post⟩ := nonFirst source machine semantic route
      refine ⟨count, after, bound, trace, ?_⟩
      simpa only [compiledZesuDecodeRawContract, functionInstanceZesuDecodeRaw,
        specZesuDecodeRaw] using post

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
