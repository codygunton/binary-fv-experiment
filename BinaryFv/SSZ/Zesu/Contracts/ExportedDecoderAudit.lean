import BinaryFv.SSZ.Zesu.Contracts.Runtime

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-!
# Exported-decoder vertical tests

Row A's binding-level checks on the exported wrapper and its accessors, stated as theorems so a
regression cannot silently revert them. These are definitional facts about the bindings — they do
not depend on Sail execution, the runner, or the concrete contract parameters.

The "old wrapper binding" the plan contrasts against is gone: it required the internal convention
`x10 = resultBase`, so a caller that set only the real C ABI registers `a0 = input`, `a1 = len`
would not have satisfied it. The two `wrapper_entry_requires_*` theorems pin that the new binding is
stated against exactly those real registers, which is the correction.
-/

/-- **The wrapper entry binds the input pointer in `a0`.** A state whose `a0` is not the input base
does not satisfy the entry binding — so a mutated argument register fails. -/
theorem wrapper_entry_requires_input_in_a0 (env : DecoderEnvironment)
    (globals : DecoderGlobalsLayout) (incoming : DecoderGlobalsModel) (args : ZesuDecodeRawArgs)
    (state : State) (hbad : state.regs.get? x10 ≠ some (BitVec.ofNat 64 args.inputBase)) :
    ¬ preZesuDecodeRaw env globals incoming args state := by
  intro h
  exact hbad h.2.2.1

/-- **The wrapper entry binds the length in `a1`.** A state whose `a1` is not the input length does
not satisfy the entry binding. -/
theorem wrapper_entry_requires_length_in_a1 (env : DecoderEnvironment)
    (globals : DecoderGlobalsLayout) (incoming : DecoderGlobalsModel) (args : ZesuDecodeRawArgs)
    (state : State) (hbad : state.regs.get? x11 ≠ some (BitVec.ofNat 64 args.bytes.size)) :
    ¬ preZesuDecodeRaw env globals incoming args state := by
  intro h
  exact hbad h.2.2.2.1

/-- **Relocation leaves the `RoutineSpec` untouched.** The exported wrapper's shared specification is
independent of the global locations and result-buffer address, so relinking the binary (which moves
those addresses) changes bindings but never what the routine means. -/
theorem wrapper_spec_is_relocation_invariant (env : DecoderEnvironment)
    (g₁ g₂ : DecoderGlobalsLayout) (rb₁ rb₂ : Nat)
    (rep : ContainerRepresentation SszBridge.RawV4) (incoming : DecoderGlobalsModel) :
    (occurrenceZesuDecodeRaw env g₁ rb₁ rep incoming).spec
      = (occurrenceZesuDecodeRaw env g₂ rb₂ rep incoming).spec :=
  rfl

/-- The accessor `zesu_raw_error` means exactly the status the ghost globals model records. -/
theorem raw_error_reads_model_status (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (model : DecoderGlobalsModel) :
    (contractRawError env globals).meaning model = .ok model.status.code :=
  rfl

/-- The accessor `zesu_raw_result` means the canonical buffer pointer exactly when the ghost globals
model has a stored value, and null otherwise. -/
theorem raw_result_reads_model_pointer (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (model : DecoderGlobalsModel) :
    (contractRawResult env globals resultBuffer).meaning model
      = .ok (if model.stored.isSome then resultBuffer else 0) :=
  rfl

/-- **A fresh successful call feeds the accessors a non-null result of the exact status.** After the
wrapper stores a decoded value, `zesu_raw_result` yields the canonical buffer and `zesu_raw_error`
yields `ok`. -/
theorem accessors_after_fresh_success (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (value : SszBridge.RawV4) :
    (contractRawResult env globals resultBuffer).meaning
        (resultingGlobals DecoderGlobalsModel.fresh (.ok value)) = .ok resultBuffer ∧
    (contractRawError env globals).meaning
        (resultingGlobals DecoderGlobalsModel.fresh (.ok value)) = .ok DecodeStatus.ok.code := by
  constructor <;>
    simp [contractRawResult, contractRawError, resultingGlobals, callOutcome,
      DecodeCallOutcome.status, DecodeCallOutcome.stored, DecoderGlobalsModel.fresh]

/-- **A fresh rejected call feeds the accessors a null result.** After the wrapper rejects,
`zesu_raw_result` yields null. -/
theorem accessors_after_fresh_rejection (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (error : SszDecodeError) :
    (contractRawResult env globals resultBuffer).meaning
        (resultingGlobals DecoderGlobalsModel.fresh (.error error)) = .ok 0 := by
  simp [contractRawResult, resultingGlobals, callOutcome, DecodeCallOutcome.stored,
    DecoderGlobalsModel.fresh]

end BinaryFv.SSZ.Zesu.Contracts
