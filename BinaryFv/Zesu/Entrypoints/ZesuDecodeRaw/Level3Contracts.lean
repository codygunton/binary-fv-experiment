import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeInlineContract
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level3Boundaries
import BinaryFv.Zesu.MachineExecution.MemcpyInstance
import BinaryFv.RiscV.Elfling.ProgramGeometry

/-!
# Level 3 contracts below inlined `decode`

This level selects the emitted `decodeRaw`, the two real segments attributed to the inlined
`hasExactErePrefix`, and the already proved emitted `memcpy`. The prefix helper is not assigned its
source ABI: its first segment starts after parent instructions prepare constants, and both segments
stop before generated outgoing instructions that the parent executes.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv BinaryFv.Binary BinaryFv.Binary.Elfling BinaryFv.RiscV
open BinaryFv.RiscV.Elfling BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Elflings.Generated BinaryFv.Zesu.DecodedValue
open LeanRV64DExecutable.Functions Register

def entryMachineArgs (args : EntryArgs) : DecoderMachineArgs where
  inputBase := args.base
  bytes := args.bytes

/-- Registers the emitted `decodeRaw` function must return to its inlined caller. Besides the
machine-platform frame, the caller immediately reuses `sp`, `s0`, `s1`, and the wrapper's live
global-object base in `s2`, plus the wrapper values held in `s3` through `s11`. This is a checked
contract clause for this concrete call boundary, not a general RISC-V ABI claim. -/
def decodeRawCallerPreserved (register : Register) : Prop :=
  platformPreserved register ∨ register = x2 ∨ register = x8 ∨ register = x9 ∨ register = x18 ∨
    decodeRawCalleeSaved register

/-- The caller copies the first 832 bytes of the result object on every retry outcome, so the
compiled child boundary must expose that those bytes are initialized. -/
def DecodeRawResultPayloadInitialized (args : EntryArgs) (state : State) : Prop :=
  ∃ contents : ByteArray, contents.size = 832 ∧ MemoryBytes state args.resultBase contents

/-- The 32-byte wrapper caller-save area at `allocatorBase + 0x9f0` is live across the emitted
`decodeRaw` call. Source `postEntry` permits unrelated stack writes, so this relative machine frame
is an explicit condition of the compiled call boundary rather than a source-semantic consequence. -/
def DecodeRawCallerSaveArea (args : EntryArgs) (before after : State) : Prop :=
  ∀ index, index < 32 →
    after.mem.get? (args.allocatorBase + 0x9f0 + index) =
      before.mem.get? (args.allocatorBase + 0x9f0 + index)

/-- The emitted `decodeRaw` invocation advances the concrete bump cursor only within the checked
canonical arena. Unlike result-payload provenance, this applies to error exits too: a failed
decode can still have allocated before discovering the error. -/
def DecodeRawAllocationWithinCanonicalArena (before after : State) : Prop :=
  ∃ cursorBefore cursorAfter,
    canonicalContractParams.env.cursor? before = some cursorBefore ∧
      canonicalContractParams.env.cursor? after = some cursorAfter ∧
      canonicalContractParams.env.arenaBase ≤ cursorBefore ∧
      cursorBefore ≤ cursorAfter ∧ cursorAfter ≤ Elflings.canonicalHeapLimit

/-- A cursor interval confined to the canonical arena cannot contain a byte of the decoder's
private `.bss`. This discharges the allocation component of `decodeRaw`'s ownership permission;
the result record, allocator state, and stack require their own concrete exclusions. -/
theorem decodeRawAllocationInterval_outside_decoderGlobals {cursorBefore cursorAfter address : Nat}
    (cursorBound : cursorAfter ≤ Elflings.canonicalHeapLimit)
    (global : DecoderGlobalsByte address) :
    ¬ Contracts.interval cursorBefore cursorAfter address := by
  rcases global with ⟨globalsBase, _⟩
  rintro ⟨_, beforeEnd⟩
  have arenaBeforeGlobals : Elflings.canonicalHeapLimit ≤ Elflings.GeneratedDecoderGlobals.bssBase := by
    native_decide
  omega

/-- The source `decodeRaw` contract strengthened with its real emitted entry, configured machine
premises, and the return frame needed by its caller. The source meaning and bound are unchanged;
the exit additionally preserves the link/platform registers plus the caller's live `sp`, `s0`, and
`s1`, and leaves a readable retired counter so the caller can execute the generated `ret`. -/
def compiledDecodeRawContract : FunctionInstanceContract
    EntryArgs (Except Contracts.DecodeError BinaryFv.Specs.SSZ.StatelessInput) :=
  let source := (contractDecodeRaw canonicalContractParams.env
    canonicalContractParams.repStatelessInput).toFunctionInstance
  { spec := source.spec
    binding :=
      { entry := fun args state => source.binding.entry args state ∧
          state.regs.get? PC = some (BitVec.ofNat 64 0x10444) ∧
          DecodeRawEntryFrame state ∧
          DecodeRawReturnLinkPre state ∧
          DecoderMachinePre
            (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
            (entryMachineArgs args) state
        exit := fun args outcome before after =>
          source.binding.exit args outcome before after ∧
            Agree decodeRawCallerPreserved before after ∧
            RetiredCounterPresent after ∧
            DecodeRawResultPayloadInitialized args after ∧
            DecodeRawCallerSaveArea args before after ∧
            DecodeRawSuccessAllocationProvenance args outcome before after ∧
            DecodeRawAllocationWithinCanonicalArena before after
        stepBound := source.binding.stepBound } }

/-- Project the wrapper caller-save-area frame from a compiled `decodeRaw` exit. -/
theorem compiledDecodeRawCallerSaveArea {args : EntryArgs} {outcome} {before after : State}
    (post : compiledDecodeRawContract.binding.exit args outcome before after) :
    DecodeRawCallerSaveArea args before after := post.2.2.2.2.1

/-- Project the result-independent arena bound from a compiled `decodeRaw` exit. -/
theorem compiledDecodeRawAllocationWithinCanonicalArena {args : EntryArgs} {outcome}
    {before after : State}
    (post : compiledDecodeRawContract.binding.exit args outcome before after) :
    DecodeRawAllocationWithinCanonicalArena before after := post.2.2.2.2.2.2

/-- Lift a concrete exclusion of each component of an allocation-owned region to a byte frame.
The caller must establish exclusions for the result record, allocator state, stack, and cursor
interval separately; this lemma deliberately supplies none of them. -/
theorem writesOnlyWithinOwnAllocation_preserves_byte {recordBase recordSize address : Nat}
    {before after : State}
    (writes : canonicalContractParams.env.WritesOnlyWithinOwnAllocation
      recordBase recordSize before after)
    (outside : ∀ cursorBefore cursorAfter,
      canonicalContractParams.env.cursor? before = some cursorBefore →
      canonicalContractParams.env.cursor? after = some cursorAfter →
      ¬ canonicalContractParams.env.ownedRegion recordBase recordSize cursorBefore cursorAfter address) :
    after.mem.get? address = before.mem.get? address := by
  obtain ⟨cursorBefore, cursorAfter, beforeCursor, afterCursor, frame⟩ := writes
  exact frame address (outside cursorBefore cursorAfter beforeCursor afterCursor)

/-- The unresolved Level 3 condition for the one emitted `decodeRaw` instance. -/
abbrev CompiledDecodeRawInstanceContract : Prop :=
  compiledDecodeRawContract.ImplementsFunctionInstance
    functionInstance_ssz_raw_decodeRaw
    (functionInstanceReachedPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
    (functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
    (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)

/-- The exact typed summary produced at either call from inlined `decode`. -/
def compiledDecodeRawSummary (child : FunctionInstanceId) (fromStep used : Nat)
    (before after : State) : Prop :=
  child = functionInstance_ssz_raw_decodeRawId ∧
    compiledDecodeRawContract.summary
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
      (functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
      fromStep used before after

theorem compiledDecodeRawSummary_of_contract (contract : CompiledDecodeRawInstanceContract)
    (args : EntryArgs) (fromStep : Nat) (before : State)
    (entry : compiledDecodeRawContract.binding.entry args before) :
    ∃ used after,
      used ≤ compiledDecodeRawContract.binding.stepBound args ∧
        compiledDecodeRawSummary functionInstance_ssz_raw_decodeRawId
          fromStep used before after := by
  obtain ⟨used, after, bound, trace, post⟩ := contract args fromStep before entry
  exact ⟨used, after, bound, rfl, args, entry, bound, trace, post⟩

inductive HasExactErePrefixPhase where
  | lengthGate
  | prefixBytes
deriving DecidableEq, Repr

structure HasExactErePrefixInlineArgs where
  phase : HasExactErePrefixPhase
  inputBase : Nat
  bytes : ByteArray

namespace HasExactErePrefixInlineArgs

def entryPc (args : HasExactErePrefixInlineArgs) : BitVec 64 :=
  match args.phase with
  | .lengthGate => BitVec.ofNat 64 0x10390
  | .prefixBytes => BitVec.ofNat 64 0x10398

def machineArgs (args : HasExactErePrefixInlineArgs) : DecoderMachineArgs where
  inputBase := args.inputBase
  bytes := args.bytes

end HasExactErePrefixInlineArgs

/-- Actual state at either attributed segment entry. `s0` and `s1` are live registers of inlined
`decode`; the first segment additionally consumes constants prepared by parent-owned instructions. -/
structure HasExactErePrefixInlinePre (args : HasExactErePrefixInlineArgs)
    (state : State) : Prop where
  atEntry : state.regs.get? PC = some args.entryPc
  inputPointer : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)
  inputLength : state.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size)
  globalsValue : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  inputMemory : MemoryBytes state args.inputBase args.bytes
  code : canonicalContractParams.env.CodeIntact state
  inputFits : args.inputBase + args.bytes.size ≤ 2 ^ 64
  rootInputBound : args.bytes.size < 2 * 1024 * 1024
  preparedConstants : args.phase = .lengthGate →
    state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) ∧
      state.regs.get? x12 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))
  prefixExists : args.phase = .prefixBytes → 4 ≤ args.bytes.size
  machine : DecoderMachinePre
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
    args.machineArgs state

/-- Exact state immediately before the generated outgoing instruction of either segment. The
parent owns that outgoing instruction: `bltu` after the length segment and the final `or` after the
byte segment. -/
def HasExactErePrefixInlinePost (args : HasExactErePrefixInlineArgs)
    (after : State) : Prop :=
  match args.phase with
  | .lengthGate =>
      after.regs.get? PC = some (BitVec.ofNat 64 0x10394) ∧
        after.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) ∧
        after.regs.get? x12 = some
          (BitVec.ofNat 64 (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4)))
  | .prefixBytes =>
      after.regs.get? PC = some (BitVec.ofNat 64 0x103c0) ∧
        after.regs.get? x10 = some (BitVec.ofNat 64 (prefixLow16 args.bytes)) ∧
        after.regs.get? x14 = some (BitVec.ofNat 64 (prefixHigh16 args.bytes)) ∧
        after.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4))

def hasExactErePrefixInlineStepBound (_ : HasExactErePrefixInlineArgs) : Nat := 12

theorem hasExactErePrefixInline_entry_in_region (args : HasExactErePrefixInlineArgs) :
    functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
      args.entryPc := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  cases phaseEq : args.phase <;>
    simp [HasExactErePrefixInlineArgs.entryPc, phaseEq] <;> native_decide

theorem hasExactErePrefixInline_length_exit :
    functionInstanceExitPred
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
      (BitVec.ofNat 64 0x10394) := by
  simp [functionInstanceExitPred, FunctionInstance.isExit,
    functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35]

theorem hasExactErePrefixInline_prefix_exit :
    functionInstanceExitPred
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
      (BitVec.ofNat 64 0x103c0) := by
  simp [functionInstanceExitPred, FunctionInstance.isExit,
    functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35]

/-- The two decoder-global bytes that the wrapper needs unchanged across an inlined
`hasExactErePrefix` segment. This is a machine boundary frame, separate from the helper's
semantic postcondition and checked trace coverage. -/
def DecoderGlobalsBoundaryFrame (before after : State) : Prop :=
  after.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted =
      before.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted ∧
    after.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) =
      before.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset)

/-- Machine facts preserved by either selected inlined `hasExactErePrefix` segment and consumed by
the surrounding `decode` instructions. These are proved from the segment's actual Sail execution;
they are not source-ABI assumptions for the inlined helper. -/
structure HasExactErePrefixInlineFrame (args : HasExactErePrefixInlineArgs)
    (before after : State) : Prop where
  agree : Agree decoderPreserved before after
  callerFrame : Agree decodeRawCalleeSaved before after
  retiredCounter : RetiredCounterPresent after
  stackPointer : after.regs.get? x2 = before.regs.get? x2
  inputPointer : after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)
  inputLength : after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size)
  globals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  status : after.regs.get? x11 = before.regs.get? x11
  memory : after.mem = before.mem

theorem HasExactErePrefixInlineFrame.globalsBoundary
    (frame : HasExactErePrefixInlineFrame args before after) :
    DecoderGlobalsBoundaryFrame before after := by
  simp [DecoderGlobalsBoundaryFrame, frame.memory]

/-- The two non-ABI segments attributed to the selected inlined prefix helper. -/
def HasExactErePrefixInlineContract : Prop :=
  ∀ (args : HasExactErePrefixInlineArgs) (fromStep : Nat) (before : State),
    HasExactErePrefixInlinePre args before →
      ∃ used after,
        used ≤ hasExactErePrefixInlineStepBound args ∧
          FunctionTrace
            (functionInstanceExecutionPcs generatedProgram
              functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
          (functionInstanceExitPred
            functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
            fromStep used before after ∧
          HasExactErePrefixInlinePost args after ∧
          HasExactErePrefixInlineFrame args before after

/-- Exact child-summary relation consumed by the inlined-`decode` scope. -/
def hasExactErePrefixInlineSummary (child : FunctionInstanceId) (fromStep used : Nat)
    (before after : State) : Prop :=
  child =
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id ∧
    ∃ args,
      HasExactErePrefixInlinePre args before ∧
        used ≤ hasExactErePrefixInlineStepBound args ∧
        FunctionTrace
          (functionInstanceExecutionPcs generatedProgram
            functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
          (functionInstanceExitPred
            functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
          fromStep used before after ∧
        HasExactErePrefixInlinePost args after ∧
        HasExactErePrefixInlineFrame args before after

theorem hasExactErePrefixInlineSummary_of_contract
    (contract : HasExactErePrefixInlineContract)
    (args : HasExactErePrefixInlineArgs) (fromStep : Nat) (before : State)
    (pre : HasExactErePrefixInlinePre args before) :
    ∃ used after,
      hasExactErePrefixInlineSummary
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
        fromStep used before after := by
  obtain ⟨used, after, bound, trace, post, frame⟩ := contract args fromStep before pre
  exact ⟨used, after, rfl, args, pre, bound, trace, post, frame⟩

/-- The complete selected Level 3 child relation. -/
inductive Level3ChildSummary :
    FunctionInstanceId → Nat → Nat → State → State → Prop where
  | decodeRaw {fromStep used before after}
      (run : compiledDecodeRawSummary functionInstance_ssz_raw_decodeRawId
        fromStep used before after) :
      Level3ChildSummary functionInstance_ssz_raw_decodeRawId fromStep used before after
  | hasExactErePrefix {fromStep used before after}
      (run : hasExactErePrefixInlineSummary
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
        fromStep used before after) :
      Level3ChildSummary
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
        fromStep used before after
  | memcpy {fromStep used before after}
      (run : MachineExecution.compiledMemcpySummary functionInstance_memcpyId
        fromStep used before after) :
      Level3ChildSummary functionInstance_memcpyId fromStep used before after

/-- The Level 3 contract for the selected inlined `ssz_raw.decode` instance.  In addition to its
semantic exit and machine frame, it preserves the wrapper's saved return-address/callee-save area,
which the immediate caller reloads after every `decode` outcome. -/
def DecodeInlineFirstInvalidInputFrame (args : DecodeInlineArgs) (after : State) : Prop :=
  args.phase = .first →
    Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz →
      after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
        after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size)

/-- Every unsuccessful first `decodeRaw` return retains the two wrapper arguments used by the
second `decode` entry.  `invalidSsz` is only one such result: `unknownFork` and `outOfMemory`
take the propagation entry with the same live registers. -/
def DecodeInlineFirstErrorInputFrame (args : DecodeInlineArgs) (after : State) : Prop :=
  args.phase = .first →
    ∀ error, Contracts.meaningDecodeRaw args.bytes = .error error →
      after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
        after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size)

def DecodeInlineFirstAllocationFrame (args : DecodeInlineArgs) (before after : State) : Prop :=
  args.phase = .first → DecodeRawAllocationWithinCanonicalArena before after

/-- A successful first `decodeRaw` retains both its semantic heap-placement witness and the
result-independent canonical-arena cursor bound through the parent-owned setup instructions. -/
def DecodeInlineFirstSuccessProvenanceFrame (args : DecodeInlineArgs) (before after : State) : Prop :=
  args.phase = .first →
    ∀ value, Contracts.meaningDecodeRaw args.bytes = .ok value →
      DecodeRawSuccessAllocationProvenance args.firstRawArgs (.ok value) before after

/-- The successful retry retains the second `decodeRaw` allocation interval and the subsequent
no-allocation ledger frame. Together they identify the only arena-owned writes on this route. -/
def DecodeInlineRetrySuccessAllocationFrame (args : DecodeInlineArgs) (before after : State) : Prop :=
  args.phase = .retryAfterInvalidSsz →
    Contracts.meaningHasExactErePrefix args.bytes = true →
      ∃ decoded contents,
        Contracts.postEntry canonicalContractParams.env args.retryRawArgs
            canonicalContractParams.repStatelessInput (Contracts.meaningDecode args.bytes) before decoded ∧
          contents.size = 832 ∧
          MemoryBytes decoded args.retryRawArgs.resultBase contents ∧
          Contracts.CopyDestinationFrame
            { source := args.retryRawArgs.resultBase, destination := args.finalResultBase,
              length := 832, contents := contents } decoded after ∧
          MemoryBytes after args.retryRawArgs.resultBase contents ∧
          MemoryBytes after args.finalResultBase contents ∧
          canonicalContractParams.env.CodeIntact after ∧
          canonicalContractParams.env.NoAllocation decoded after ∧
          DecodeRawAllocationWithinCanonicalArena before decoded ∧
          DecodeRawSuccessAllocationProvenance args.retryRawArgs
            (Contracts.meaningDecode args.bytes) before decoded

def Level3DecodeInlineContract : Prop :=
  ∀ (args : DecodeInlineArgs) (fromStep : Nat) (before : State),
    DecodeInlinePre args before →
      ∃ used after,
        used ≤ decodeInlineStepBound args ∧
          ScopedTrace
            (functionInstanceExecutionPcs generatedProgram
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
            (DecodeInlineExit args) Level3ChildSummary fromStep used before after ∧
          FunctionTrace
            (functionInstanceExecutionPcs generatedProgram
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
            (DecodeInlineExit args) fromStep used before after ∧
          DecodeInlinePost args before after ∧
          DecodeInlineMachinePost before after ∧
          DecodeInlineOutgoingFrame args after ∧
          DecodeInlineCallerSaveArea args before after ∧
          DecodeInlineFirstInvalidInputFrame args after ∧
          DecodeInlineFirstErrorInputFrame args after ∧
          DecodeInlineFirstAllocationFrame args before after ∧
          DecodeInlineFirstSuccessProvenanceFrame args before after ∧
          DecodeInlineRetrySuccessAllocationFrame args before after ∧
          (args.phase = .first → ∀ value, Contracts.meaningDecodeRaw args.bytes = .ok value →
            used ≤ 16384 + 512 * args.bytes.size + 13) ∧
          (args.phase = .first → Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz →
            used ≤ 16392 + 512 * args.bytes.size) ∧
          (args.phase = .retryAfterInvalidSsz →
            Contracts.meaningHasExactErePrefix args.bytes = true →
              used ≤ 16384 + 512 * args.retryRawArgs.bytes.size + 6765) ∧
          (args.phase = .retryAfterInvalidSsz →
            Contracts.meaningHasExactErePrefix args.bytes = false →
              args.bytes.size < 4 → used ≤ 16) ∧
          (args.phase = .retryAfterInvalidSsz →
            Contracts.meaningHasExactErePrefix args.bytes = false →
              4 ≤ args.bytes.size → used ≤ 30) ∧
          (∀ error, args.phase = .propagateError error → used = 0)

/-- The resulting `decode` summary consumed by the Level 2 wrapper proof. -/
def level3DecodeChildSummary :
    FunctionInstanceId → Nat → Nat → State → State → Prop :=
  decodeChildSummary Level3ChildSummary

private theorem decodeInlineExit_is_generated_exit (args : DecodeInlineArgs) {pc : BitVec 64}
    (exit : DecodeInlineExit args pc) :
    functionInstanceExitPred
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 pc := by
  cases phase : args.phase <;> simp [DecodeInlineExit, phase] at exit ⊢
  · cases result : Contracts.meaningDecodeRaw args.bytes <;> simp [result] at exit ⊢
    all_goals subst pc <;> simp [functionInstanceExitPred, FunctionInstance.isExit,
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
  · by_cases exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true
    · simp [exactPrefix] at exit
      subst pc
      simp [functionInstanceExitPred, FunctionInstance.isExit,
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
    · by_cases short : args.bytes.size < 4
      · simp [exactPrefix, short] at exit
        subst pc
        simp [functionInstanceExitPred, FunctionInstance.isExit,
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
      · simp [exactPrefix, short] at exit
        subst pc
        simp [functionInstanceExitPred, FunctionInstance.isExit,
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
  · subst pc
    simp [functionInstanceExitPred, FunctionInstance.isExit,
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]

private theorem generated_child_composes_with_semantic_exit
    {parent child : FunctionInstance} {outerExit : BitVec 64 → Prop}
    {fromStep used count : Nat} {before after final : State}
    (parentMember : parent ∈ generatedProgram.functionInstances)
    (childCallee : child ∈ calleeFunctionInstances generatedProgram parent)
    (outerExitGenerated : ∀ pc, outerExit pc → functionInstanceExitPred parent pc)
    (body : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram child)
      (functionInstanceExitPred child) fromStep used before after)
    (cont : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram parent)
      outerExit (fromStep + used) count after final) :
    FunctionTrace
      (functionInstanceExecutionPcs generatedProgram parent)
      outerExit fromStep (used + count) before final := by
  let geometry := programGeometry_of_check (program := generatedProgram) (by native_decide)
  exact summaryComposes_of_subtrace
    (fun pc inside => geometry.calleeWithinExecution parent parentMember child childCallee pc inside)
    (fun pc inside outerExit =>
      geometry.calleeExitContainment parent parentMember child childCallee pc inside
        (outerExitGenerated pc outerExit))
    body cont

private theorem generated_member_of_find {functionInstance : FunctionInstance}
    (found : generatedProgram.find? functionInstance.id = some functionInstance) :
    functionInstance ∈ generatedProgram.functionInstances :=
  Array.mem_of_find?_eq_some found

private theorem decodeRaw_is_generated :
    functionInstance_ssz_raw_decodeRaw ∈ generatedProgram.functionInstances :=
  generated_member_of_find (by
    set_option maxRecDepth 100000 in
    rfl)

private theorem decodeRaw_is_decode_callee :
    functionInstance_ssz_raw_decodeRaw ∈ calleeFunctionInstances generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 := by
  apply Array.mem_filter.mpr
  refine ⟨decodeRaw_is_generated, ?_⟩
  native_decide

private theorem hasExactErePrefix_is_generated :
    functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35 ∈
      generatedProgram.functionInstances :=
  generated_member_of_find (by
    set_option maxRecDepth 100000 in
    rfl)

private theorem hasExactErePrefix_is_decode_callee :
    functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35 ∈
      calleeFunctionInstances generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 := by
  apply Array.mem_filter.mpr
  refine ⟨hasExactErePrefix_is_generated, ?_⟩
  native_decide

private theorem memcpy_is_generated :
    functionInstance_memcpy ∈ generatedProgram.functionInstances :=
  generated_member_of_find (by
    set_option maxRecDepth 100000 in
    rfl)

private theorem memcpy_is_decode_callee :
    functionInstance_memcpy ∈ calleeFunctionInstances generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 := by
  apply Array.mem_filter.mpr
  refine ⟨memcpy_is_generated, ?_⟩
  native_decide

private theorem decode_is_generated :
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
      generatedProgram.functionInstances := by
  apply generated_member_of_find
  set_option maxRecDepth 100000 in
  rfl

theorem level3ChildSummary_composes_decode (args : DecodeInlineArgs) :
    SummariesCompose
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary := by
  intro child fromStep used count before after final run cont
  cases run with
  | decodeRaw run =>
      rcases run with ⟨_, childArgs, pre, bound, trace, post⟩
      exact generated_child_composes_with_semantic_exit decode_is_generated decodeRaw_is_decode_callee
        (fun pc h => decodeInlineExit_is_generated_exit args h) trace.trace cont
  | hasExactErePrefix run =>
      rcases run with ⟨_, childArgs, pre, bound, trace, post, frame⟩
      exact generated_child_composes_with_semantic_exit decode_is_generated
        hasExactErePrefix_is_decode_callee
        (fun pc h => decodeInlineExit_is_generated_exit args h) trace cont
  | memcpy run =>
      rcases run with ⟨_, childArgs, pre, bound, trace, post⟩
      exact generated_child_composes_with_semantic_exit decode_is_generated memcpy_is_decode_callee
        (fun pc h => decodeInlineExit_is_generated_exit args h) trace.trace cont

theorem level3DecodeChildSummary_of_contract (contract : Level3DecodeInlineContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) :
    ∃ used after, level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep used before after := by
  obtain ⟨used, after, bound, scopedTrace, flat, post, machinePost, outgoing, _, _, _⟩ :=
    contract args fromStep before pre
  exact ⟨used, after, rfl, args, pre, bound, scopedTrace, flat, post, machinePost, outgoing⟩

/-- The Level 2 caller needs the same selected-child summary and caller-save frame together; this
projection prevents it from reopening the deeper `decodeRaw` contract. -/
theorem level3DecodeChildSummary_of_contract_with_save_area (contract : Level3DecodeInlineContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) :
    ∃ used after,
      level3DecodeChildSummary
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
        fromStep used before after ∧
      DecodeInlineCallerSaveArea args before after := by
  obtain ⟨used, after, bound, scopedTrace, flat, post, machinePost, outgoing, saveArea, _, _⟩ :=
    contract args fromStep before pre
  exact ⟨used, after, ⟨rfl, args, pre, bound, scopedTrace, flat, post, machinePost, outgoing⟩,
    saveArea⟩

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
