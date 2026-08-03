import GeneratedProgram
import BinaryFv.RiscV.Step.AbstractPremise
import BinaryFv.Zesu.Contracts.CanonicalParams
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Boundaries

/-!
# Contract for the inlined `decode` machine segments

The compiler did not emit a callable `decode` function. Its instructions are entered first at
`0x10308`; after an `invalidSsz` result, wrapper instructions may enter the retry region at
`0x10380`. This contract therefore quantifies over those two real entries and stops at the generated
outgoing instruction of the active segment. It never assumes a RISC-V function ABI at either entry.

The first phase implements `meaningDecodeRaw` on the original input. A successful first phase stops
at the `memcpy` call that copies the 832-byte result object. The retry phase implements
`meaningDecode`: it checks the exact ERE prefix and, when present, runs `decodeRaw` on the four-byte
tail. These are the semantic facts the wrapper needs to turn the two machine phases into the
source-level `decode` result.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV
open BinaryFv.RiscV.Elfling BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Elflings.Generated BinaryFv.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-- The two actual entries into the inlined `decode` instructions. -/
inductive DecodeInlinePhase where
  | first
  | retryAfterInvalidSsz
deriving DecidableEq, Repr

/-- Source data and the wrapper stack base shared by both `decode` phases. -/
structure DecodeInlineArgs where
  phase : DecodeInlinePhase
  stackBase : Nat
  inputBase : Nat
  bytes : ByteArray

namespace DecodeInlineArgs

def allocatorBase (args : DecodeInlineArgs) : Nat := args.stackBase + 0x10
def finalResultBase (args : DecodeInlineArgs) : Nat := args.stackBase + 0x20
def firstTemporaryResultBase (args : DecodeInlineArgs) : Nat := args.stackBase + 0x360

def firstRawArgs (args : DecodeInlineArgs) : EntryArgs where
  base := args.inputBase
  bytes := args.bytes
  allocatorBase := args.allocatorBase
  resultBase := args.firstTemporaryResultBase

def finalArgs (args : DecodeInlineArgs) : EntryArgs where
  base := args.inputBase
  bytes := args.bytes
  allocatorBase := args.allocatorBase
  resultBase := args.finalResultBase

def entryPc (args : DecodeInlineArgs) : BitVec 64 :=
  match args.phase with
  | .first => BitVec.ofNat 64 0x10308
  | .retryAfterInvalidSsz => BitVec.ofNat 64 0x10380

end DecodeInlineArgs

/-! ## Compiled-machine premises -/

/-- The input slice relevant to configured decoder data access. Stack and arena placement come from
the canonical environment, so this deliberately carries no invented callee stack pointer. -/
structure DecoderMachineArgs where
  inputBase : Nat
  bytes : ByteArray

def DecodeInlineArgs.machineArgs (args : DecodeInlineArgs) : DecoderMachineArgs where
  inputBase := args.inputBase
  bytes := args.bytes

/-- Bytes the inlined decoder may read: the immutable image, its input, its stack objects, allocator
state, or the arena. This describes data placement, not an execution result. -/
def DecoderReadableByte (args : DecoderMachineArgs) (address : Nat) : Prop :=
  (∃ byte, canonicalContractParams.env.image.readByte? address = some byte) ∨
    (args.inputBase ≤ address ∧ address < args.inputBase + args.bytes.size) ∨
    canonicalContractParams.env.stack address ∨
    canonicalContractParams.env.allocatorState address ∨
    (canonicalContractParams.env.arenaBase ≤ address ∧
      address < Elflings.canonicalHeapLimit)

/-- Bytes the inlined decoder may write. The input and immutable image are deliberately absent. -/
def DecoderWritableByte (address : Nat) : Prop :=
  canonicalContractParams.env.stack address ∨
    canonicalContractParams.env.allocatorState address ∨
    (canonicalContractParams.env.arenaBase ≤ address ∧
      address < Elflings.canonicalHeapLimit)

/-- Every byte in one machine access belongs to `allowed`; the non-wrapping condition makes the
address range an ordinary half-open interval rather than a modular one. -/
def DecoderAccessRange (allowed : Nat → Prop) (address : BitVec 64) (width : Nat) : Prop :=
  address.toNat + width ≤ 2 ^ 64 ∧
    ∀ index, index < width → allowed (address.toNat + index)

/-- Data-access behavior of the configured machine over the decoder's readable and writable
ranges. It is quantified over states preserving the platform registers so it remains usable after
ordinary instructions. No trace, decoded value, or semantic postcondition occurs here. -/
structure DecoderDataAccess (args : DecoderMachineArgs) (base : State) : Prop where
  load : ∀ (state : State) (address : BitVec 64) (width : Nat),
    Agree platformPreserved base state →
      DecoderAccessRange (DecoderReadableByte args) address width →
      Runs (phys_access_check (MemoryAccessType.Load mem_payload.Data) PBMT_PMA .Machine
        (physaddr.Physaddr address) width false) state state none ∧
      Runs (within_mmio_readable (physaddr.Physaddr address) width) state state false
  store : ∀ (state : State) (address : BitVec 64) (width : Nat),
    Agree platformPreserved base state →
      DecoderAccessRange DecoderWritableByte address width →
      Runs (phys_access_check (MemoryAccessType.Store mem_payload.Data) PBMT_PMA .Machine
        (physaddr.Physaddr address) width false) state state none ∧
      Runs (within_mmio_writable (physaddr.Physaddr address) width) state state false

/-- Machine configuration needed to execute either compiled inline phase. Fetch is restricted to
the generated `decode` PCs; data access is restricted to the concrete image/input/runtime regions.
These premises are transportable machine facts, not an assumption that the decoder succeeds. -/
structure DecoderMachinePre (instructionPcs : BitVec 64 → Prop)
    (args : DecoderMachineArgs) (state : State) : Prop where
  normal : NormalExecutionState state
  retiredCounter : RetiredCounterPresent state
  platform : BinaryFv.RiscV.AbstractPlatform platformPreserved instructionPcs state
  dataAccess : DecoderDataAccess args state
  landingPad : BinaryFv.RiscV.AbstractElp platformPreserved (fun _ => True) state

/-- The shared machine premise specialized to the generated inlined-`decode` instruction set. -/
abbrev DecodeInlineMachinePre (args : DecodeInlineArgs) (state : State) : Prop :=
  DecoderMachinePre
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
    args.machineArgs state

/-- The error-union tag loaded by the wrapper-facing inline instructions. This is not the public
`DecodeStatus` value: `outOfMemory` has internal tag `1` and public status code `4`. -/
def decodeInternalResultTag :
    Except DecodeError BinaryFv.Specs.SSZ.RawV4 → Nat
  | .ok _ => 0
  | .error .outOfMemory => 1
  | .error .invalidSsz => 2
  | .error .unknownFork => 3

/-- Machine and source facts at either real inline entry. `s0`, `s1`, and `sp` are live values of
the surrounding wrapper, not an invented callee ABI. -/
structure DecodeInlinePre (args : DecodeInlineArgs) (state : State) : Prop where
  atEntry : state.regs.get? PC = some args.entryPc
  stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)
  inputValue : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)
  lengthValue : state.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size)
  inputMemory : MemoryBytes state args.inputBase args.bytes
  code : canonicalContractParams.env.CodeIntact state
  inputFits : args.inputBase + args.bytes.size ≤ 2 ^ 64
  stackObjectsFit : args.stackBase + 0x6b0 + canonicalContractParams.env.record.entryResult ≤
    2 ^ 64
  machine : DecodeInlineMachinePre args state
  retryReason : args.phase = .retryAfterInvalidSsz →
    meaningDecodeRaw args.bytes = .error .invalidSsz ∧
      state.regs.get? x10 = some (BitVec.ofNat 64 2)

/-- The first `decodeRaw` outcome at its temporary result object, together with the exact boundary
state consumed next by either the wrapper branch or the proved `memcpy` call. -/
def DecodeInlineFirstPost (args : DecodeInlineArgs)
    (before after : State) : Prop :=
  let result := meaningDecodeRaw args.bytes
  postEntry canonicalContractParams.env args.firstRawArgs canonicalContractParams.repRawV4
      result before after ∧
    match result with
    | .ok _ =>
        after.regs.get? PC = some (BitVec.ofNat 64 0x10338) ∧
        after.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase) ∧
        after.regs.get? x11 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
        after.regs.get? x12 = some (BitVec.ofNat 64 832) ∧
        ∃ rootBytes : ByteArray,
          rootBytes.size = 832 ∧
            MemoryBytes after args.firstTemporaryResultBase rootBytes
    | .error _ =>
        after.regs.get? PC = some (BitVec.ofNat 64 0x10324) ∧
        after.regs.get? x10 = some (BitVec.ofNat 64 (decodeInternalResultTag result))

/-- The retry phase either rejects before a second `decodeRaw`, or finishes the retry and its
832-byte result copy. In both cases the result is the complete source `meaningDecode`. -/
def DecodeInlineRetryPost (args : DecodeInlineArgs)
    (before after : State) : Prop :=
  let result := meaningDecode args.bytes
  postEntry canonicalContractParams.env args.finalArgs canonicalContractParams.repRawV4
      result before after ∧
    if meaningHasExactErePrefix args.bytes then
      after.regs.get? PC = some (BitVec.ofNat 64 0x103f8) ∧
        after.regs.get? x10 = some (BitVec.ofNat 64 (decodeInternalResultTag result))
    else
      result = .error .invalidSsz ∧
        (after.regs.get? PC = some (BitVec.ofNat 64 0x10394) ∨
          after.regs.get? PC = some (BitVec.ofNat 64 0x103c4))

/-- Semantic exit condition selected by the real entry phase. -/
def DecodeInlinePost (args : DecodeInlineArgs) (before after : State) : Prop :=
  match args.phase with
  | .first => DecodeInlineFirstPost args before after
  | .retryAfterInvalidSsz => DecodeInlineRetryPost args before after

/-- A conservative bound inherited from the source `decode` contract. It covers two raw attempts,
the prefix check, and the fixed wrapper-local instruction sequences. -/
def decodeInlineStepBound (args : DecodeInlineArgs) : Nat :=
  2 * (16384 + 512 * args.bytes.size)

/-! ## Generated-boundary checks -/

/-- Each phase starts at one of the two entries accepted by the checked inline boundary. -/
theorem decodeInline_entry_accepted (args : DecodeInlineArgs) :
    decodeInlineBoundary.acceptsEntry
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      args.entryPc.toNat := by
  cases phaseEq : args.phase <;>
    simp [DecodeInlineArgs.entryPc, phaseEq, decodeInlineBoundary, InlineBoundary.acceptsEntry,
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]

/-- Each phase entry is inside the generated execution region. -/
theorem decodeInline_entry_in_region (args : DecodeInlineArgs) :
    functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      args.entryPc := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  cases phaseEq : args.phase <;>
    simp [DecodeInlineArgs.entryPc, phaseEq] <;>
    native_decide

/-- The initial entry is not already a generated exit, so its trace must execute instructions. -/
theorem decodeInline_first_entry_not_exit :
    ¬ functionInstanceExitPred
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x10308) := by
  simp [functionInstanceExitPred, FunctionInstance.isExit,
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]

/-- The retry entry is itself an outgoing branch source. A zero-step child body here is real: the
enclosing checked transfer still retires that branch before returning to wrapper-owned code. -/
theorem decodeInline_retry_entry_is_exit :
    functionInstanceExitPred
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x10380) := by
  simp [functionInstanceExitPred, FunctionInstance.isExit,
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]

/-- Every semantic postcondition stops at one of the generated outgoing instructions. -/
theorem decodeInline_post_at_generated_exit (args : DecodeInlineArgs) (before after : State)
    (post : DecodeInlinePost args before after) :
    ∃ pc, after.regs.get? PC = some pc ∧
      functionInstanceExitPred
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 pc := by
  cases phaseEq : args.phase with
  | first =>
      simp only [DecodeInlinePost, phaseEq, DecodeInlineFirstPost] at post
      cases resultEq : meaningDecodeRaw args.bytes with
      | ok value =>
          rw [resultEq] at post
          refine ⟨BitVec.ofNat 64 0x10338, post.2.1, ?_⟩
          simp [functionInstanceExitPred, FunctionInstance.isExit,
            functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
      | error error =>
          rw [resultEq] at post
          refine ⟨BitVec.ofNat 64 0x10324, post.2.1, ?_⟩
          simp [functionInstanceExitPred, FunctionInstance.isExit,
            functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
  | retryAfterInvalidSsz =>
      simp only [DecodeInlinePost, phaseEq, DecodeInlineRetryPost] at post
      cases prefixEq : meaningHasExactErePrefix args.bytes with
      | false =>
          simp only [prefixEq, Bool.false_eq_true, ↓reduceIte] at post
          rcases post.2.2 with atEarly | atLate
          · refine ⟨BitVec.ofNat 64 0x10394, atEarly, ?_⟩
            simp [functionInstanceExitPred, FunctionInstance.isExit,
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
          · refine ⟨BitVec.ofNat 64 0x103c4, atLate, ?_⟩
            simp [functionInstanceExitPred, FunctionInstance.isExit,
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
      | true =>
          simp only [prefixEq, ↓reduceIte] at post
          refine ⟨BitVec.ofNat 64 0x103f8, post.2.1, ?_⟩
          simp [functionInstanceExitPred, FunctionInstance.isExit,
            functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]

/-- The fixed correctness condition for the two inlined `decode` phases. Its trace uses the exact
generated execution region and generated outgoing-instruction set for this compiled instance.

This uses `FunctionTrace`, not `EnteredFunctionTrace`, because the retry entry `0x10380` is also an
outgoing branch source and can therefore have a genuine zero-step child body. The checked
`InlineTransfer` that consumes the summary always executes that outgoing instruction. -/
def DecodeInlineContract : Prop :=
  ∀ (args : DecodeInlineArgs) (fromStep : Nat) (before : State),
    DecodeInlinePre args before →
      ∃ used after,
        used ≤ decodeInlineStepBound args ∧
          FunctionTrace
            (functionInstanceExecutionPcs generatedProgram
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
            (functionInstanceExitPred
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
            fromStep used before after ∧
          DecodeInlinePost args before after

/-- The exact caller-side summary carried by a checked Level 2 inline transfer. -/
def decodeChildSummary (child : FunctionInstanceId) (fromStep used : Nat)
    (before after : State) : Prop :=
  child = functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id ∧
    ∃ args : DecodeInlineArgs,
      DecodeInlinePre args before ∧
        used ≤ decodeInlineStepBound args ∧
        FunctionTrace
          (functionInstanceExecutionPcs generatedProgram
            functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
          (functionInstanceExitPred
            functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
          fromStep used before after ∧
        DecodeInlinePost args before after

/-- The fixed contract produces exactly the child summary consumed by the wrapper scope. -/
theorem decodeChildSummary_of_contract (contract : DecodeInlineContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) :
    ∃ used after, decodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep used before after := by
  obtain ⟨used, after, bound, trace, post⟩ := contract args fromStep before pre
  exact ⟨used, after, rfl, args, pre, bound, trace, post⟩

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
