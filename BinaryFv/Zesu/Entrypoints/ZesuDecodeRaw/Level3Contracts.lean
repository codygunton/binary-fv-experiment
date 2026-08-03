import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeInlineContract
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

/-- The source `decodeRaw` contract strengthened only with the real emitted entry and configured
machine premises for this generated body. Its meaning, postcondition, and bound are unchanged. -/
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
        exit := source.binding.exit
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

def prefixLow16 (bytes : ByteArray) : Nat :=
  (bytes.get! 0).toNat + (bytes.get! 1).toNat * 2 ^ 8

def prefixHigh16 (bytes : ByteArray) : Nat :=
  (bytes.get! 2).toNat * 2 ^ 16 + (bytes.get! 3).toNat * 2 ^ 24

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

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
