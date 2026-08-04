import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeInlineContract
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level3Boundaries
import BinaryFv.Zesu.MachineExecution.MemcpyInstance

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
open BinaryFv.Zesu.Elflings.Generated BinaryFv.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

def entryMachineArgs (args : EntryArgs) : DecoderMachineArgs where
  inputBase := args.base
  bytes := args.bytes

/-- Registers the emitted `decodeRaw` function must return to its inlined caller. Besides the
machine-platform frame, the caller immediately reuses `sp`, `s0`, and `s1`. -/
def decodeRawCallerPreserved (register : Register) : Prop :=
  platformPreserved register ∨ register = x2 ∨ register = x8 ∨ register = x9

/-- The caller copies the first 832 bytes of the result object on every retry outcome, so the
compiled child boundary must expose that those bytes are initialized. -/
def DecodeRawResultPayloadInitialized (args : EntryArgs) (state : State) : Prop :=
  ∃ contents : ByteArray, contents.size = 832 ∧ MemoryBytes state args.resultBase contents

/-- The source `decodeRaw` contract strengthened with its real emitted entry, configured machine
premises, and the return frame needed by its caller. The source meaning and bound are unchanged;
the exit additionally preserves the link/platform registers plus the caller's live `sp`, `s0`, and
`s1`, and leaves a readable retired counter so the caller can execute the generated `ret`. -/
def compiledDecodeRawContract : FunctionInstanceContract
    EntryArgs (Except Contracts.DecodeError BinaryFv.Specs.SSZ.RawV4) :=
  let source := (contractDecodeRaw canonicalContractParams.env
    canonicalContractParams.repRawV4).toFunctionInstance
  { spec := source.spec
    binding :=
      { entry := fun args state => source.binding.entry args state ∧
          state.regs.get? PC = some (BitVec.ofNat 64 0x10444) ∧
          DecoderMachinePre
            (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
            (entryMachineArgs args) state
        exit := fun args outcome before after =>
          source.binding.exit args outcome before after ∧
            Agree decodeRawCallerPreserved before after ∧
            RetiredCounterPresent after ∧
            DecodeRawResultPayloadInitialized args after
        stepBound := source.binding.stepBound } }

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
          HasExactErePrefixInlinePost args after

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
        HasExactErePrefixInlinePost args after

theorem hasExactErePrefixInlineSummary_of_contract
    (contract : HasExactErePrefixInlineContract)
    (args : HasExactErePrefixInlineArgs) (fromStep : Nat) (before : State)
    (pre : HasExactErePrefixInlinePre args before) :
    ∃ used after,
      hasExactErePrefixInlineSummary
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
        fromStep used before after := by
  obtain ⟨used, after, bound, trace, post⟩ := contract args fromStep before pre
  exact ⟨used, after, rfl, args, pre, bound, trace, post⟩

/-- The complete selected Level 3 child relation. The `memcpy` arm is already closed by Sail. -/
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

/-- The Level 3 conditional theorem to prove: execute every `decode`-owned instruction while using
exactly the three selected child summaries above. -/
abbrev Level3DecodeInlineContract : Prop := DecodeInlineContract Level3ChildSummary

/-- The resulting `decode` summary consumed by the Level 2 wrapper proof. -/
def level3DecodeChildSummary :
    FunctionInstanceId → Nat → Nat → State → State → Prop :=
  decodeChildSummary Level3ChildSummary

theorem level3DecodeChildSummary_of_contract (contract : Level3DecodeInlineContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) :
    ∃ used after, level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep used before after :=
  decodeChildSummary_of_contract Level3ChildSummary contract args fromStep before pre

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
