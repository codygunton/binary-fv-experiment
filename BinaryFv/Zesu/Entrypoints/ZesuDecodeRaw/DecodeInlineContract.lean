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
  | propagateError (error : Contracts.DecodeError)
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

def retryRawArgs (args : DecodeInlineArgs) : EntryArgs where
  base := args.inputBase + 4
  bytes := args.bytes.extract 4 args.bytes.size
  allocatorBase := args.allocatorBase
  resultBase := args.stackBase + 0x6b0

def finalArgs (args : DecodeInlineArgs) : EntryArgs where
  base := args.inputBase
  bytes := args.bytes
  allocatorBase := args.allocatorBase
  resultBase := args.finalResultBase

def entryPc (args : DecodeInlineArgs) : BitVec 64 :=
  match args.phase with
  | .first => BitVec.ofNat 64 0x10308
  | .retryAfterInvalidSsz => BitVec.ofNat 64 0x10380
  | .propagateError _ => BitVec.ofNat 64 0x10380

end DecodeInlineArgs

/-! ## Compiled-machine premises -/

/-- Registers whose values remain stable while executing decoder-owned instructions. The link
register is excluded because emitted calls update it before transferring to their child bodies. -/
def decoderPreserved (r : Register) : Prop :=
  r ≠ x1 ∧ platformPreserved r

/-- The input slice relevant to configured decoder data access. Stack and arena placement come from
the canonical environment, so this deliberately carries no invented callee stack pointer. -/
structure DecoderMachineArgs where
  inputBase : Nat
  bytes : ByteArray

def DecodeInlineArgs.machineArgs (args : DecodeInlineArgs) : DecoderMachineArgs where
  inputBase := args.inputBase
  bytes := args.bytes

/-- Bytes in the generated private decoder-globals block. The bounds come from the linker map and
validated generated artifact, not from a handwritten address. -/
def DecoderGlobalsByte (address : Nat) : Prop :=
  Elflings.GeneratedDecoderGlobals.bssBase ≤ address ∧
    address < Elflings.GeneratedDecoderGlobals.bssBase +
      Elflings.GeneratedDecoderGlobals.bssSize

/-- Bytes the decoder and its wrapper may read: the immutable image, input, stack objects, private
decoder globals, allocator state, or arena. This describes data placement, not an execution result. -/
def DecoderReadableByte (args : DecoderMachineArgs) (address : Nat) : Prop :=
  (∃ byte, canonicalContractParams.env.image.readByte? address = some byte) ∨
    (args.inputBase ≤ address ∧ address < args.inputBase + args.bytes.size) ∨
    canonicalContractParams.env.stack address ∨
    DecoderGlobalsByte address ∨
    canonicalContractParams.env.allocatorState address ∨
    (canonicalContractParams.env.arenaBase ≤ address ∧
      address < Elflings.canonicalHeapLimit)

/-- Bytes the decoder and wrapper may write. The input and immutable image are deliberately absent. -/
def DecoderWritableByte (address : Nat) : Prop :=
  canonicalContractParams.env.stack address ∨
    DecoderGlobalsByte address ∨
    canonicalContractParams.env.allocatorState address ∨
    (canonicalContractParams.env.arenaBase ≤ address ∧
      address < Elflings.canonicalHeapLimit)

/-- Every byte in one nonempty machine access belongs to `allowed`; the non-wrapping condition
makes the address range an ordinary half-open interval rather than a modular one. `0 < width`
excludes vacuous zero-width ranges: the configured PMA region ends below `2 ^ 63`, while an empty
range at an arbitrary 64-bit address would otherwise satisfy the byte clause without denoting a
permitted data access. -/
def DecoderAccessRange (allowed : Nat → Prop) (address : BitVec 64) (width : Nat) : Prop :=
  0 < width ∧ address.toNat + width ≤ 2 ^ 64 ∧
    ∀ index, index < width → allowed (address.toNat + index)

/-- Data-access behavior of the configured machine over the decoder's readable and writable
ranges. It is quantified over states preserving the decoder's machine registers so it remains
usable across ordinary instructions and emitted call setup. No trace, decoded value, or semantic
postcondition occurs here. -/
structure DecoderDataAccess (args : DecoderMachineArgs) (base : State) : Prop where
  load : ∀ (state : State) (address : BitVec 64) (width : Nat),
    Agree decoderPreserved base state →
      DecoderAccessRange (DecoderReadableByte args) address width →
      Runs (phys_access_check (MemoryAccessType.Load mem_payload.Data) PBMT_PMA .Machine
        (physaddr.Physaddr address) width false) state state none ∧
      Runs (within_mmio_readable (physaddr.Physaddr address) width) state state false
  store : ∀ (state : State) (address : BitVec 64) (width : Nat),
    Agree decoderPreserved base state →
      DecoderAccessRange DecoderWritableByte address width →
      Runs (phys_access_check (MemoryAccessType.Store mem_payload.Data) PBMT_PMA .Machine
        (physaddr.Physaddr address) width false) state state none ∧
      Runs (within_mmio_writable (physaddr.Physaddr address) width) state state false

theorem DecoderDataAccess.mono {args : DecoderMachineArgs} {before after : State}
    (agree : Agree decoderPreserved before after) (access : DecoderDataAccess args before) :
    DecoderDataAccess args after where
  load state address width afterAgree allowed :=
    access.load state address width (Agree.trans agree afterAgree) allowed
  store state address width afterAgree allowed :=
    access.store state address width (Agree.trans agree afterAgree) allowed

/-- A child that reads a subset of the parent's readable bytes inherits the same concrete machine
access behavior. Writable bytes are program-wide and therefore unchanged. -/
theorem DecoderDataAccess.narrow {outer inner : DecoderMachineArgs} {state : State}
    (subset : ∀ address, DecoderReadableByte inner address → DecoderReadableByte outer address)
    (access : DecoderDataAccess outer state) : DecoderDataAccess inner state where
  load next address width agree allowed := access.load next address width agree
    ⟨allowed.1, allowed.2.1, by
    intro index bound
    exact subset _ (allowed.2.2 index bound)⟩
  store := access.store

/-- Machine configuration needed to execute either compiled inline phase. Fetch is restricted to
the generated `decode` PCs; data access is restricted to the concrete image/input/runtime regions.
These premises are transportable machine facts, not an assumption that the decoder succeeds. -/
structure DecoderMachinePre (instructionPcs : BitVec 64 → Prop)
    (args : DecoderMachineArgs) (state : State) : Prop where
  normal : NormalExecutionState state
  retiredCounter : RetiredCounterPresent state
  mstatus : ∃ bits, state.regs.get? mstatus = some bits ∧ _get_Mstatus_MPRV bits = 0#1
  mseccfg : ∃ bits, state.regs.get? mseccfg = some bits ∧
    pmm_mode_backwards (_get_Seccfg_PMM bits) = .PMM_Disabled
  platform : BinaryFv.RiscV.AbstractPlatform decoderPreserved instructionPcs state
  dataAccess : DecoderDataAccess args state
  landingPad : BinaryFv.RiscV.AbstractElp decoderPreserved (fun _ => True) state

theorem DecoderMachinePre.mono {instructionPcs : BitVec 64 → Prop} {args : DecoderMachineArgs}
    {before after : State} (agree : Agree decoderPreserved before after)
    (retired : RetiredCounterPresent after)
    (machine : DecoderMachinePre instructionPcs args before) :
    DecoderMachinePre instructionPcs args after where
  normal := normalExecutionState_of_agree
    (Agree.weaken (fun register preserved => by
      refine ⟨?_, normalRegisters_platformPreserved register preserved⟩
      intro equal
      subst register
      simp [normalRegisters] at preserved) agree) machine.normal
  retiredCounter := retired
  mstatus := by
    obtain ⟨bits, read, mprv⟩ := machine.mstatus
    exact ⟨bits,
      (agree Register.mstatus (by simp [decoderPreserved, platformPreserved])).trans read, mprv⟩
  mseccfg := by
    obtain ⟨bits, read, disabled⟩ := machine.mseccfg
    exact ⟨bits,
      (agree Register.mseccfg (by simp [decoderPreserved, platformPreserved])).trans read,
      disabled⟩
  platform := machine.platform.mono agree
  dataAccess := machine.dataAccess.mono agree
  landingPad := machine.landingPad.mono agree

theorem DecoderMachinePre.restrict {outer inner : BitVec 64 → Prop} {args : DecoderMachineArgs}
    {state : State} (subset : ∀ pc, inner pc → outer pc)
    (machine : DecoderMachinePre outer args state) : DecoderMachinePre inner args state where
  normal := machine.normal
  retiredCounter := machine.retiredCounter
  mstatus := machine.mstatus
  mseccfg := machine.mseccfg
  platform := fun next pc agree atPc pcIn => machine.platform next pc agree atPc (subset pc pcIn)
  dataAccess := machine.dataAccess
  landingPad := machine.landingPad

/-- Specialize a machine premise to a child input whose readable region is contained in the
parent's. This changes no execution or platform fact. -/
theorem DecoderMachinePre.narrowInput {instructionPcs : BitVec 64 → Prop}
    {outer inner : DecoderMachineArgs} {state : State}
    (subset : ∀ address, DecoderReadableByte inner address → DecoderReadableByte outer address)
    (machine : DecoderMachinePre instructionPcs outer state) :
    DecoderMachinePre instructionPcs inner state where
  normal := machine.normal
  retiredCounter := machine.retiredCounter
  mstatus := machine.mstatus
  mseccfg := machine.mseccfg
  platform := machine.platform
  dataAccess := machine.dataAccess.narrow subset
  landingPad := machine.landingPad

/-- The shared machine premise specialized to the generated inlined-`decode` instruction set. -/
abbrev DecodeInlineMachinePre (args : DecodeInlineArgs) (state : State) : Prop :=
  DecoderMachinePre
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
    args.machineArgs state

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
  rootInputBound : args.bytes.size < 2 * 1024 * 1024
  stackAligned : args.stackBase % 16 = 0
  stackObjectsFit : args.stackBase + 0x6b0 + canonicalContractParams.env.record.entryResult ≤
    2 ^ 64
  stackObjectsReadable : ∀ index,
    index < 0x6b0 + canonicalContractParams.env.record.entryResult →
      canonicalContractParams.env.stack (args.stackBase + index)
  machine : DecodeInlineMachinePre args state
  retryReason : args.phase = .retryAfterInvalidSsz →
    meaningDecodeRaw args.bytes = .error .invalidSsz ∧
      state.regs.get? x10 = some (BitVec.ofNat 64 2) ∧
      state.regs.get? x11 = some (BitVec.ofNat 64 2)
  propagateReason : ∀ error, args.phase = .propagateError error →
    error ≠ .invalidSsz ∧
      meaningDecodeRaw args.bytes = .error error ∧
      state.regs.get? x10 =
        some (BitVec.ofNat 64 (decodeInternalResultTag (.error error))) ∧
      state.regs.get? x11 = some (BitVec.ofNat 64 2)

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

/-- The successful retry retains the second `decodeRaw` result object and copies only its 832-byte
payload to the final object. The emitted `memcpy` does not copy the following two-byte result tag;
the Level 2 wrapper reads that tag from the retained retry object at `sp + 0x9f0`.

`decoded` records the state at which the second `decodeRaw` postcondition held. The exact copy frame
then connects that semantic result to the final state without falsely claiming a tag at the payload
destination. -/
def DecodeInlineRetrySuccessPost (args : DecodeInlineArgs) (before after : State) : Prop :=
  let result := meaningDecode args.bytes
  ∃ decoded contents,
    postEntry canonicalContractParams.env args.retryRawArgs canonicalContractParams.repRawV4
        result before decoded ∧
      contents.size = 832 ∧
      MemoryBytes decoded args.retryRawArgs.resultBase contents ∧
      CopyDestinationFrame
        { destination := args.finalResultBase
          source := args.retryRawArgs.resultBase
          length := 832
          contents := contents }
        decoded after ∧
      MemoryBytes after args.retryRawArgs.resultBase contents ∧
      MemoryBytes after args.finalResultBase contents ∧
      canonicalContractParams.env.CodeIntact after ∧
      canonicalContractParams.env.NoAllocation decoded after

/-- The retry phase either rejects before a second `decodeRaw`, or finishes the retry and its
832-byte payload copy. In both cases the result is the complete source `meaningDecode`.

The successful phase stops before the outgoing tag load at `0x103f8`; the Level 2 wrapper owns that
instruction. -/
def DecodeInlineRetryPost (args : DecodeInlineArgs)
    (before after : State) : Prop :=
  let result := meaningDecode args.bytes
  if meaningHasExactErePrefix args.bytes then
    DecodeInlineRetrySuccessPost args before after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x103f8)
  else
    result = .error .invalidSsz ∧
      if args.bytes.size < 4 then
        after.regs.get? PC = some (BitVec.ofNat 64 0x10394)
      else
        after.regs.get? PC = some (BitVec.ofNat 64 0x103c4)

/-- Semantic exit condition selected by the real entry phase. -/
def DecodeInlinePost (args : DecodeInlineArgs) (before after : State) : Prop :=
  match args.phase with
  | .first => DecodeInlineFirstPost args before after
  | .retryAfterInvalidSsz => DecodeInlineRetryPost args before after
  | .propagateError error =>
      error ≠ .invalidSsz ∧
        meaningDecodeRaw args.bytes = .error error ∧
        meaningDecode args.bytes = .error error ∧
        after.regs.get? PC = some (BitVec.ofNat 64 0x10380) ∧
        after = before

/-- The stopping PCs for this particular source-level outcome. Generated exit inventories contain
every branch with an edge leaving the instance, but `decode` may legitimately take such a branch's
other edge and continue. Selecting exits from the source result prevents a trace from stopping at an
intermediate mixed branch while preserving the exact generated exit PC at the real outcome. -/
def DecodeInlineExit (args : DecodeInlineArgs) (pc : BitVec 64) : Prop :=
  match args.phase with
  | .first =>
      match meaningDecodeRaw args.bytes with
      | .ok _ => pc = BitVec.ofNat 64 0x10338
      | .error _ => pc = BitVec.ofNat 64 0x10324
  | .retryAfterInvalidSsz =>
      if meaningHasExactErePrefix args.bytes then
        pc = BitVec.ofNat 64 0x103f8
      else
        if args.bytes.size < 4 then
          pc = BitVec.ofNat 64 0x10394
        else
          pc = BitVec.ofNat 64 0x103c4
  | .propagateError _ => pc = BitVec.ofNat 64 0x10380

/-- A conservative bound inherited from the source `decode` contract. It covers two raw attempts,
the prefix check, and the fixed wrapper-local instruction sequences. -/
def decodeInlineStepBound (args : DecodeInlineArgs) : Nat :=
  2 * (16384 + 512 * args.bytes.size)

/-- Machine facts retained at every selected `decode` exit. These are consequences of the child
execution, not premises supplied by the wrapper. They are exactly the facts needed to execute the
outgoing instruction owned by Level 2. -/
structure DecodeInlineMachinePost (before after : State) : Prop where
  agree : Agree decoderPreserved before after
  retiredCounter : RetiredCounterPresent after
  code : canonicalContractParams.env.CodeIntact after

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

/-- The retry entry is a generated outgoing branch source because one edge leaves `decode`. It is
not an outcome-selected exit: the retry precondition fixes both compared tags to `2`, so execution
must take the fallthrough edge into the retry body. -/
theorem decodeInline_retry_entry_is_exit :
    functionInstanceExitPred
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x10380) := by
  simp [functionInstanceExitPred, FunctionInstance.isExit,
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]

theorem decodeInline_retry_entry_not_selected_exit (args : DecodeInlineArgs)
    (phase : args.phase = .retryAfterInvalidSsz) :
    ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10380) := by
  simp [DecodeInlineExit, phase]

/-- Every semantic postcondition stops at the outcome-selected exit. -/
theorem decodeInline_post_at_selected_exit (args : DecodeInlineArgs) (before after : State)
    (post : DecodeInlinePost args before after) :
    ∃ pc, after.regs.get? PC = some pc ∧ DecodeInlineExit args pc := by
  cases phaseEq : args.phase with
  | first =>
      simp only [DecodeInlinePost, phaseEq, DecodeInlineFirstPost] at post
      cases resultEq : meaningDecodeRaw args.bytes with
      | ok value =>
          rw [resultEq] at post
          exact ⟨BitVec.ofNat 64 0x10338, post.2.1, by simp [DecodeInlineExit, phaseEq, resultEq]⟩
      | error error =>
          rw [resultEq] at post
          exact ⟨BitVec.ofNat 64 0x10324, post.2.1, by simp [DecodeInlineExit, phaseEq, resultEq]⟩
  | retryAfterInvalidSsz =>
      simp only [DecodeInlinePost, phaseEq, DecodeInlineRetryPost] at post
      cases prefixEq : meaningHasExactErePrefix args.bytes with
      | false =>
          simp only [prefixEq, Bool.false_eq_true, ↓reduceIte] at post
          by_cases short : args.bytes.size < 4
          · have atEarly : after.regs.get? PC = some (BitVec.ofNat 64 0x10394) := by
              simpa [short] using post.2
            exact ⟨BitVec.ofNat 64 0x10394, atEarly,
              by simp [DecodeInlineExit, phaseEq, prefixEq, short]⟩
          · have atLate : after.regs.get? PC = some (BitVec.ofNat 64 0x103c4) := by
              simpa [short] using post.2
            exact ⟨BitVec.ofNat 64 0x103c4, atLate,
              by simp [DecodeInlineExit, phaseEq, prefixEq, short]⟩
      | true =>
          simp only [prefixEq, ↓reduceIte] at post
          exact ⟨BitVec.ofNat 64 0x103f8, post.2,
            by simp [DecodeInlineExit, phaseEq, prefixEq]⟩
  | propagateError error =>
      simp only [DecodeInlinePost, phaseEq] at post
      exact ⟨BitVec.ofNat 64 0x10380, post.2.2.2.1,
        by simp [DecodeInlineExit, phaseEq]⟩

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
          by_cases short : args.bytes.size < 4
          · have atEarly : after.regs.get? PC = some (BitVec.ofNat 64 0x10394) := by
              simpa [short] using post.2
            refine ⟨BitVec.ofNat 64 0x10394, atEarly, ?_⟩
            simp [functionInstanceExitPred, FunctionInstance.isExit,
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
          · have atLate : after.regs.get? PC = some (BitVec.ofNat 64 0x103c4) := by
              simpa [short] using post.2
            refine ⟨BitVec.ofNat 64 0x103c4, atLate, ?_⟩
            simp [functionInstanceExitPred, FunctionInstance.isExit,
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
      | true =>
          simp only [prefixEq, ↓reduceIte] at post
          refine ⟨BitVec.ofNat 64 0x103f8, post.2, ?_⟩
          simp [functionInstanceExitPred, FunctionInstance.isExit,
            functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
  | propagateError error =>
      simp only [DecodeInlinePost, phaseEq] at post
      refine ⟨BitVec.ofNat 64 0x10380, post.2.2.2.1, ?_⟩
      simp [functionInstanceExitPred, FunctionInstance.isExit,
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]

/-- The fixed correctness condition for the two inlined `decode` phases. Its trace uses the exact
generated execution region and generated outgoing-instruction set for this compiled instance.

The `ScopedTrace` parameter is the one selected-child relation supplied by Level 3. It lets this
contract execute `decode`-owned instructions while consuming proved or assumed summaries at the
`decodeRaw`, `hasExactErePrefix`, and `memcpy` boundaries. -/
def DecodeInlineContract
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop) : Prop :=
  ∀ (args : DecodeInlineArgs) (fromStep : Nat) (before : State),
    DecodeInlinePre args before →
      ∃ used after,
        used ≤ decodeInlineStepBound args ∧
          ScopedTrace
            (functionInstanceExecutionPcs generatedProgram
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
            (DecodeInlineExit args)
            childSummary
            fromStep used before after ∧
          DecodeInlinePost args before after ∧
          DecodeInlineMachinePost before after

/-- The exact caller-side summary carried by a checked Level 2 inline transfer. -/
def decodeChildSummary
    (level3ChildSummary : FunctionInstanceId → Nat → Nat → State → State → Prop)
    (child : FunctionInstanceId) (fromStep used : Nat)
    (before after : State) : Prop :=
  child = functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id ∧
    ∃ args : DecodeInlineArgs,
      DecodeInlinePre args before ∧
        used ≤ decodeInlineStepBound args ∧
        ScopedTrace
          (functionInstanceExecutionPcs generatedProgram
            functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
          (DecodeInlineExit args)
          level3ChildSummary
          fromStep used before after ∧
        DecodeInlinePost args before after ∧
        DecodeInlineMachinePost before after

/-- The fixed contract produces exactly the child summary consumed by the wrapper scope. -/
theorem decodeChildSummary_of_contract
    (level3ChildSummary : FunctionInstanceId → Nat → Nat → State → State → Prop)
    (contract : DecodeInlineContract level3ChildSummary)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) :
    ∃ used after, decodeChildSummary level3ChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep used before after := by
  obtain ⟨used, after, bound, trace, post, machinePost⟩ := contract args fromStep before pre
  exact ⟨used, after, rfl, args, pre, bound, trace, post, machinePost⟩

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
