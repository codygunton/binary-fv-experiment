import GeneratedProgram
import BinaryFv.RiscV.Step.AbstractPremise
import BinaryFv.Zesu.Contracts.CanonicalParams
import BinaryFv.Zesu.Contracts.StatelessInputRelocation
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
open BinaryFv.Zesu.Elflings.Generated BinaryFv.Zesu.DecodedValue
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

/-- Arena bytes that remain ordinary memory under the canonical Sail platform. The CLINT window starts
at `plat_clint_base` inside the 64 MiB allocator arena, so the whole arena cannot be a data-access
permission. The root's `< 2 MiB` allocation bound stays below this boundary; the fixed signature
window is above the arena, and the canonical configuration disables HTIF (`htif_tohost_base = none`). -/
def DecoderSafeArenaByte (address : Nat) : Prop :=
  canonicalContractParams.env.arenaBase ≤ address ∧
    address < Elflings.canonicalHeapLimit ∧ address < BitVec.toNat plat_clint_base

/-- Checked canonical platform/layout facts used to keep dynamic allocator addresses out of MMIO. -/
theorem canonicalHeapBase_pinned : Elflings.canonicalHeapBase = 86048 := by native_decide

theorem canonicalHeapLimit_pinned : Elflings.canonicalHeapLimit = 67194912 := by native_decide

theorem clintBase_pinned : BitVec.toNat plat_clint_base = 33554432 := by native_decide

theorem clintSize_pinned : BitVec.toNat plat_clint_size = 786432 := by native_decide

theorem signatureBase_pinned : BitVec.toNat plat_sig_base = 201326592 := by native_decide

theorem signatureSize_pinned : BitVec.toNat plat_sig_size = 32 := by native_decide

/-- Under `root_compliance`'s input bound, the allocation ledger cannot reach the CLINT window. -/
theorem allocation_before_clint_of_root_input_bound (inputSize : Nat)
    (inputBound : inputSize < 2 * 1024 * 1024) :
    Elflings.canonicalHeapBase + Runtime.rawAllocationBound inputSize <
      BitVec.toNat plat_clint_base := by
  rw [canonicalHeapBase_pinned, clintBase_pinned]
  unfold Runtime.rawAllocationBound
  omega

/-- The signature window lies above the complete canonical allocator arena. -/
theorem canonicalArena_before_signature :
    Elflings.canonicalHeapLimit ≤ BitVec.toNat plat_sig_base := by
  rw [canonicalHeapLimit_pinned, signatureBase_pinned]
  omega

/-- Bytes the decoder and its wrapper may read: file-backed immutable image bytes, input, stack
objects, private decoder globals, allocator state, or the ordinary-memory prefix of the allocator
arena. `readByte?` is deliberately not used: its zero-filled virtual-memory tail includes CLINT,
whereas code and immutable constants are established by `CodeIntact.fileBytesLoadedFaithfully`.
Zero-filled decoder BSS and allocator cells are covered only by their explicit predicates. -/
def DecoderReadableByte (args : DecoderMachineArgs) (address : Nat) : Prop :=
  (∃ byte, canonicalContractParams.env.image.readFileByte? address = some byte) ∨
    (args.inputBase ≤ address ∧ address < args.inputBase + args.bytes.size) ∨
    canonicalContractParams.env.stack address ∨
    DecoderGlobalsByte address ∨
    canonicalContractParams.env.allocatorState address ∨
    DecoderSafeArenaByte address

/-- Bytes the decoder and wrapper may write. The input and immutable image are deliberately absent. -/
def DecoderWritableByte (address : Nat) : Prop :=
  canonicalContractParams.env.stack address ∨
    DecoderGlobalsByte address ∨
    canonicalContractParams.env.allocatorState address ∨
    DecoderSafeArenaByte address

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
      is_aligned_paddr (physaddr.Physaddr address) width = true →
      Runs (phys_access_check (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA .Machine
        (physaddr.Physaddr address) width false) state state none ∧
      Runs (within_mmio_readable (physaddr.Physaddr address) width) state state false
  store : ∀ (state : State) (address : BitVec 64) (width : Nat),
    Agree decoderPreserved base state →
      DecoderAccessRange DecoderWritableByte address width →
      is_aligned_paddr (physaddr.Physaddr address) width = true →
      Runs (phys_access_check (MemoryAccessType.Store mem_payload.Data) page_based_mem_type.PBMT_PMA .Machine
        (physaddr.Physaddr address) width false) state state none ∧
      Runs (within_mmio_writable (physaddr.Physaddr address) width) state state false

theorem DecoderDataAccess.mono {args : DecoderMachineArgs} {before after : State}
    (agree : Agree decoderPreserved before after) (access : DecoderDataAccess args before) :
    DecoderDataAccess args after where
  load state address width afterAgree allowed aligned :=
    access.load state address width (Agree.trans agree afterAgree) allowed aligned
  store state address width afterAgree allowed aligned :=
    access.store state address width (Agree.trans agree afterAgree) allowed aligned

/-- A child that reads a subset of the parent's readable bytes inherits the same concrete machine
access behavior. Writable bytes are program-wide and therefore unchanged. -/
theorem DecoderDataAccess.narrow {outer inner : DecoderMachineArgs} {state : State}
    (subset : ∀ address, DecoderReadableByte inner address → DecoderReadableByte outer address)
    (access : DecoderDataAccess outer state) : DecoderDataAccess inner state where
  load next address width agree allowed aligned := access.load next address width agree
    ⟨allowed.1, allowed.2.1, by
    intro index bound
    exact subset _ (allowed.2.2 index bound)⟩ aligned
  store := access.store

/-- Fetchable instruction starts inside a byte-range execution scope. `RegionPcs` remains the trace
confinement predicate because a retired instruction occupies bytes; fetch premises apply only at
aligned instruction starts. -/
def DecoderFetchPc (executionPcs : BitVec 64 → Prop) (pc : BitVec 64) : Prop :=
  executionPcs pc ∧ pc.toNat % 4 = 0

/-- Machine configuration needed to execute either compiled inline phase. Fetch is restricted to
aligned starts in the generated `decode` scope; data access is restricted to the concrete
image/input/runtime regions. These premises are transportable machine facts, not an assumption that
the decoder succeeds. -/
structure DecoderMachinePre (instructionPcs : BitVec 64 → Prop)
    (args : DecoderMachineArgs) (state : State) : Prop where
  normal : NormalExecutionState state
  retiredCounter : RetiredCounterPresent state
  mstatus : ∃ bits, state.regs.get? mstatus = some bits ∧ _get_Mstatus_MPRV bits = 0#1
  mseccfg : ∃ bits, state.regs.get? mseccfg = some bits ∧
    pmm_mode_backwards (_get_Seccfg_PMM bits) = .PMM_Disabled
  platform : BinaryFv.RiscV.AbstractPlatform decoderPreserved (DecoderFetchPc instructionPcs) state
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
  platform := fun next pc agree atPc pcIn =>
    machine.platform next pc agree atPc ⟨subset pc pcIn.1, pcIn.2⟩
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

/-- The wrapper values live across the emitted `decodeRaw` child which are not part of the
platform register frame. -/
def decodeRawCalleeSaved (register : Register) : Prop :=
  register = x19 ∨ register = x20 ∨ register = x21 ∨ register = x22 ∨ register = x23 ∨
    register = x24 ∨ register = x25 ∨ register = x26 ∨ register = x27

/-- The retirement bookkeeping does not touch the wrapper values live across `decodeRaw`. -/
theorem decodeRawCalleeSaved_disjoint : RegSet.Disjoint decodeRawCalleeSaved stepBookkeeping := by
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

/-- The optimized entry shape at the emitted `decodeRaw` boundary. These are live wrapper values,
not a source-level RISC-V ABI premise. -/
def DecodeRawEntryFrame (state : State) : Prop :=
  ∃ stackPointer savedS0 savedS1 savedS2 savedS3 savedS4 savedS5 savedS6 savedS7 savedS8
      savedS9 savedS10 savedS11,
    state.regs.get? x2 = some stackPointer ∧
    state.regs.get? x8 = some savedS0 ∧
    state.regs.get? x9 = some savedS1 ∧
    state.regs.get? x18 = some savedS2 ∧
    state.regs.get? x19 = some savedS3 ∧
    state.regs.get? x20 = some savedS4 ∧
    state.regs.get? x21 = some savedS5 ∧
    state.regs.get? x22 = some savedS6 ∧
    state.regs.get? x23 = some savedS7 ∧
    state.regs.get? x24 = some savedS8 ∧
    state.regs.get? x25 = some savedS9 ∧
    state.regs.get? x26 = some savedS10 ∧
    state.regs.get? x27 = some savedS11

/-- The emitted `ret` at `0x10530` reads the caller-provided link.  The compiled raw-decoder
entry therefore requires the two alignment facts which Sail checks for that return; both concrete
inline `jalr` callers derive them from their literal return PCs. -/
def DecodeRawReturnLinkPre (state : State) : Prop :=
  ∃ link, state.regs.get? x1 = some link ∧
    Sail.BitVec.update link 0 0#1 = link ∧ Sail.BitVec.access link 1 = 0#1

/-- The low-bit condition consumed by the generated Sail `ret`, recovered for the caller's
concrete link register rather than supplied as a route-local instruction premise. -/
theorem DecodeRawReturnLinkPre.update_low_bit
    (pre : DecodeRawReturnLinkPre state) (linkAt : state.regs.get? x1 = some link) :
    Sail.BitVec.update link 0 0#1 = link := by
  rcases pre with ⟨entryLink, entryLinkAt, updateLowBit, -⟩
  have entryLinkEq : entryLink = link := by
    simpa only [Option.some.injEq] using entryLinkAt.symm.trans linkAt
  simpa only [entryLinkEq] using updateLowBit

/-- The access-bit condition consumed by the generated Sail `ret`, recovered from the compiled
raw-decoder entry rather than supplied by a parent return route. -/
theorem DecodeRawReturnLinkPre.access_bit_one_zero
    (pre : DecodeRawReturnLinkPre state) (linkAt : state.regs.get? x1 = some link) :
    Sail.BitVec.access link 1 = 0#1 := by
  rcases pre with ⟨entryLink, entryLinkAt, -, accessBitOne⟩
  have entryLinkEq : entryLink = link := by
    simpa only [Option.some.injEq] using entryLinkAt.symm.trans linkAt
  simpa only [entryLinkEq] using accessBitOne

/-- The concrete raw-call frame is needed only on inline phases that execute an emitted
`decodeRaw` call.  The propagated-error phase exits before either call site. -/
def DecodeInlineRawCallFrame (args : DecodeInlineArgs) (state : State) : Prop :=
  match args.phase with
  | .first | .retryAfterInvalidSsz => DecodeRawEntryFrame state
  | .propagateError _ => True

/-- Transport the stable `s3`–`s11` part of an emitted `decodeRaw` entry frame while the wrapper
sets its concrete call arguments and link. -/
theorem DecodeRawEntryFrame.of_calleeSaved_agree {before after : State}
    (frame : DecodeRawEntryFrame before)
    (calleeSaved : Agree decodeRawCalleeSaved before after)
    {stackPointer savedS0 savedS1 savedS2 : BitVec 64}
    (stack : after.regs.get? x2 = some stackPointer)
    (savedS0AtEntry : after.regs.get? x8 = some savedS0)
    (savedS1AtEntry : after.regs.get? x9 = some savedS1)
    (savedS2AtEntry : after.regs.get? x18 = some savedS2) :
    DecodeRawEntryFrame after := by
  rcases frame with ⟨_, _, _, _, savedS3, savedS4, savedS5, savedS6, savedS7, savedS8,
    savedS9, savedS10, savedS11, _, _, _, _, savedS3Before, savedS4Before, savedS5Before,
    savedS6Before, savedS7Before, savedS8Before, savedS9Before, savedS10Before, savedS11Before⟩
  exact ⟨stackPointer, savedS0, savedS1, savedS2, savedS3, savedS4, savedS5, savedS6,
    savedS7, savedS8, savedS9, savedS10, savedS11, stack, savedS0AtEntry,
    savedS1AtEntry, savedS2AtEntry,
    (calleeSaved x19 (by simp [decodeRawCalleeSaved])).trans savedS3Before,
    (calleeSaved x20 (by simp [decodeRawCalleeSaved])).trans savedS4Before,
    (calleeSaved x21 (by simp [decodeRawCalleeSaved])).trans savedS5Before,
    (calleeSaved x22 (by simp [decodeRawCalleeSaved])).trans savedS6Before,
    (calleeSaved x23 (by simp [decodeRawCalleeSaved])).trans savedS7Before,
    (calleeSaved x24 (by simp [decodeRawCalleeSaved])).trans savedS8Before,
    (calleeSaved x25 (by simp [decodeRawCalleeSaved])).trans savedS9Before,
    (calleeSaved x26 (by simp [decodeRawCalleeSaved])).trans savedS10Before,
    (calleeSaved x27 (by simp [decodeRawCalleeSaved])).trans savedS11Before⟩

/-- Machine and source facts at either real inline entry. `s0`, `s1`, `s2`, and `sp` are live
values of the surrounding wrapper, not an invented callee ABI. -/
structure DecodeInlinePre (args : DecodeInlineArgs) (state : State) : Prop where
  atEntry : state.regs.get? PC = some args.entryPc
  stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)
  inputValue : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)
  lengthValue : state.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size)
  globalsValue : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  rawCallFrame : DecodeInlineRawCallFrame args state
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
  /-- The two inline callers inherit the exported input/stack separation.  The Level 4 raw-entry
  adapter narrows this canonical-stack fact to its thirteen saved-register stores. -/
  inputAvoidsCanonicalStack : ∀ address, canonicalContractParams.env.stack address →
    args.inputBase + args.bytes.size ≤ address ∨ address < args.inputBase
  /-- The real wrapper's complete writable frame, retained for parent-owned raw-decoder slots
  that lie outside the thirteen saved-register words. -/
  stackFrameWritable : ∀ index, index < 0xa20 →
    canonicalContractParams.env.stack (args.stackBase + index)
  rawFrameWritable : ∀ index, index < 0x7f0 →
    canonicalContractParams.env.stack (args.stackBase - 0xe80 + index)
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

/-- Narrow the caller's canonical input/stack separation to the raw decoder's thirteen saved
register words.  This is the adapter used when the actual inline call constructs its Level 4 raw
entry context; it is not a selected Level 4 contract premise. -/
theorem DecodeInlinePre.inputStackSeparated_of_saveArea
    (pre : DecodeInlinePre args state) (stack : Nat)
    (saveAreaWritable : ∀ index, index < 104 →
      canonicalContractParams.env.stack (stack + 0x788 + index))
    (address : Nat) (lower : stack + 0x788 ≤ address) (upper : address < stack + 0x7f0) :
    args.inputBase + args.bytes.size ≤ address ∨ address < args.inputBase := by
  apply pre.inputAvoidsCanonicalStack address
  rw [show address = stack + 0x788 + (address - (stack + 0x788)) by omega]
  exact saveAreaWritable _ (by omega)

/-- Rebase the Level 2 caller-frame permission at the raw prologue's entry stack value.  The
prologue later exposes this unchanged to parent phases that access post-`sp` temporary slots. -/
theorem DecodeInlinePre.stackFrameWritable_of_entryStack
    (pre : DecodeInlinePre args state) (stack : Nat)
    (entryStack : args.stackBase = stack + 0x7f0) (index : Nat) (indexBound : index < 0xa20) :
    canonicalContractParams.env.stack (stack + 0x7f0 + index) := by
  rw [← entryStack]
  exact pre.stackFrameWritable index indexBound

theorem DecodeInlinePre.rawFrameWritable_of_postStack
    (pre : DecodeInlinePre args state) (postStack : Nat)
    (entryStack : args.stackBase = postStack + 0xe80) (index : Nat) (indexBound : index < 0x7f0) :
    canonicalContractParams.env.stack (postStack + index) := by
  have writable := pre.rawFrameWritable index indexBound
  rw [entryStack] at writable
  simpa using writable

/-- On success, the complete result representation records that every descriptor-selected heap
range lies in the allocator interval consumed by this `decodeRaw` invocation. Error outcomes have
no result heap to place. This is separate from `postEntry`: that source-shaped postcondition is
generic in a container representation, while this clause names the canonical machine layout. -/
def DecodeRawSuccessAllocationProvenance (args : EntryArgs)
    (result : Except Contracts.DecodeError BinaryFv.Specs.SSZ.StatelessInput)
    (before after : State) : Prop :=
  match result with
  | .ok value =>
      ∃ cursorBefore cursorAfter,
        canonicalContractParams.env.cursor? before = some cursorBefore ∧
          canonicalContractParams.env.cursor? after = some cursorAfter ∧
            StatelessInputRepInHeapInterval after args.base args.bytes args.resultBase value
              cursorBefore cursorAfter
  | .error _ => True

/-- Parent-owned register instructions preserve the `decodeRaw` allocation ledger and represented
heap ranges because neither cursor observation nor the representation reads registers. -/
theorem decodeRawSuccessAllocationProvenance_of_mem_eq {args : EntryArgs} {result} {before after
    before' after' : State} (beforeMemory : before'.mem = before.mem)
    (afterMemory : after'.mem = after.mem)
    (provenance : DecodeRawSuccessAllocationProvenance args result before after) :
    DecodeRawSuccessAllocationProvenance args result before' after' := by
  cases result with
  | error error => trivial
  | ok value =>
      rcases provenance with ⟨cursorBefore, cursorAfter, beforeCursor, afterCursor, allocated⟩
      refine ⟨cursorBefore, cursorAfter, ?_, ?_, allocated.of_mem_eq afterMemory⟩
      · unfold DecoderEnvironment.cursor? at beforeCursor ⊢
        unfold observeWord64? at beforeCursor ⊢
        rw [beforeMemory]
        exact beforeCursor
      · unfold DecoderEnvironment.cursor? at afterCursor ⊢
        unfold observeWord64? at afterCursor ⊢
        rw [afterMemory]
        exact afterCursor

/-- The first `decodeRaw` outcome at its temporary result object, together with the exact boundary
state consumed next by either the wrapper branch or the proved `memcpy` call. -/
def DecodeInlineFirstPost (args : DecodeInlineArgs)
    (before after : State) : Prop :=
  let result := meaningDecodeRaw args.bytes
  postEntry canonicalContractParams.env args.firstRawArgs canonicalContractParams.repStatelessInput
      result before after ∧
    DecodeRawSuccessAllocationProvenance args.firstRawArgs result before after ∧
      match result with
      | .ok _ =>
          after.regs.get? PC = some (BitVec.ofNat 64 0x10338) ∧
          after.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase) ∧
          after.regs.get? x11 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
          after.regs.get? x12 = some (BitVec.ofNat 64 832) ∧
          after.regs.get? x1 = some (BitVec.ofNat 64 0x14334) ∧
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
    postEntry canonicalContractParams.env args.retryRawArgs canonicalContractParams.repStatelessInput
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
  callerFrame : Agree decodeRawCalleeSaved before after
  retiredCounter : RetiredCounterPresent after
  code : canonicalContractParams.env.CodeIntact after
  globalsValue : after.regs.get? x18 = before.regs.get? x18

/-- The 32 bytes holding the wrapper's saved return address and callee-saved registers.  Level 3
proves this concrete frame for outcomes that execute `decodeRaw`; Level 2 consumes it before the
wrapper epilogue reloads those words. -/
def DecodeInlineCallerSaveArea (args : DecodeInlineArgs) (before after : State) : Prop :=
  ∀ index, index < 32 →
    after.mem.get? (args.stackBase + 0xa00 + index) =
      before.mem.get? (args.stackBase + 0xa00 + index)

def prefixLow16 (bytes : ByteArray) : Nat :=
  (bytes.get! 0).toNat + (bytes.get! 1).toNat * 2 ^ 8

def prefixHigh16 (bytes : ByteArray) : Nat :=
  (bytes.get! 2).toNat * 2 ^ 16 + (bytes.get! 3).toNat * 2 ^ 24

/-- Facts at the particular `decode` outgoing instruction selected by `args.phase` and the source
outcome. These are deliberately separate from the platform frame: Level 2 consumes the exact
register comparison or result-tag bytes needed by the next wrapper-owned instruction. -/
def DecodeInlineOutgoingFrame (args : DecodeInlineArgs) (after : State) : Prop :=
  match args.phase with
  | .first => after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)
  | .retryAfterInvalidSsz =>
      if meaningHasExactErePrefix args.bytes then
        after.regs.get? x10 = some (BitVec.ofNat 64 (args.stackBase + 0x1000)) ∧
          after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
            DecodedValue.ResultStatusLERep after
              (args.stackBase + 0x9f0)
              (decodeInternalResultTag (meaningDecode args.bytes))
      else if args.bytes.size < 4 then
        after.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) ∧
          after.regs.get? x12 = some
            (BitVec.ofNat 64 (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4)))
      else
        after.regs.get? x10 = some
          (BitVec.ofNat 64 (prefixHigh16 args.bytes) |||
            BitVec.ofNat 64 (prefixLow16 args.bytes)) ∧
          after.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4))
  | .propagateError error =>
      after.regs.get? x10 = some
          (BitVec.ofNat 64 (decodeInternalResultTag (.error error))) ∧
        after.regs.get? x11 = some (BitVec.ofNat 64 2)

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
          exact ⟨BitVec.ofNat 64 0x10338, post.2.2.1,
            by simp [DecodeInlineExit, phaseEq, resultEq]⟩
      | error error =>
          rw [resultEq] at post
          exact ⟨BitVec.ofNat 64 0x10324, post.2.2.1,
            by simp [DecodeInlineExit, phaseEq, resultEq]⟩
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
          refine ⟨BitVec.ofNat 64 0x10338, post.2.2.1, ?_⟩
          simp [functionInstanceExitPred, FunctionInstance.isExit,
            functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
      | error error =>
          rw [resultEq] at post
          refine ⟨BitVec.ofNat 64 0x10324, post.2.2.1, ?_⟩
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
          FunctionTrace
            (functionInstanceExecutionPcs generatedProgram
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
            (DecodeInlineExit args)
            fromStep used before after ∧
          DecodeInlinePost args before after ∧
          DecodeInlineMachinePost before after ∧
          DecodeInlineOutgoingFrame args after

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
        FunctionTrace
          (functionInstanceExecutionPcs generatedProgram
            functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
          (DecodeInlineExit args) fromStep used before after ∧
        DecodeInlinePost args before after ∧
        DecodeInlineMachinePost before after ∧
        DecodeInlineOutgoingFrame args after

/-- The fixed contract produces exactly the child summary consumed by the wrapper scope. -/
theorem decodeChildSummary_of_contract
    (level3ChildSummary : FunctionInstanceId → Nat → Nat → State → State → Prop)
    (contract : DecodeInlineContract level3ChildSummary)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) :
    ∃ used after, decodeChildSummary level3ChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep used before after := by
  obtain ⟨used, after, bound, scopedTrace, flat, post, machinePost, outgoing⟩ :=
    contract args fromStep before pre
  exact ⟨used, after, rfl, args, pre, bound, scopedTrace, flat, post, machinePost, outgoing⟩

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
