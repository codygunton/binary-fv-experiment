import BinaryFv.Zesu.MachineExecution.DecodeInlineProof
import BinaryFv.Zesu.MachineExecution.Level2WrapperProof

/-!
# The wrapper prefix that consumes the Level 3 first-phase decode theorem

`Level2WrapperProof` executes every wrapper-owned instruction without depending on the proved
inlined-`decode` machine execution. Exactly one of its results consumes
`decodeInline_first_level3_save_area`, so that result lives here instead: it keeps the wrapper
execution module — the largest single elaboration segment in the build — off `DecodeInlineProof`'s
import closure, so the two elaborate concurrently rather than in series.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.ProgramImage BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.RiscV.Sep
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep GeneratedWordStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The selected inlined `decode` region is contained in its enclosing wrapper's generated
execution region. This is checked from the generated call relation, not handwritten address bounds. -/
private theorem decodeInline_executionPcs_subset_wrapper (pc : BitVec 64)
    (inside : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 pc) :
    functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw pc := by
  have parentMember : functionInstance_raw_decoder_root_zesu_decode_raw ∈
      generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨1, by native_decide, rfl⟩
  have childMember :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨3, by native_decide, rfl⟩
  have childIsCallee :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        BinaryFv.RiscV.Elfling.calleeFunctionInstances generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw := by
    apply Array.mem_filter.mpr
    exact ⟨childMember, by native_decide⟩
  exact BinaryFv.Zesu.Elflings.Validation.generated_program_geometry.calleeWithinExecution
    functionInstance_raw_decoder_root_zesu_decode_raw parentMember
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 childIsCallee
    pc inside

/-- The nineteen-step wrapper prefix establishes the complete first-phase `decode` entry and then
visibly consumes the Level 3 conditional theorem. It retains that theorem's bound, scoped trace,
and semantic postcondition alongside the Level 2 child summary, so the wrapper proof can dispatch
the actual result without recovering facts from an opaque existential. -/
theorem wrapper_reaches_decode_first_contract
    (allocator : AllocatorInlineContract) (decodeRaw : CompiledDecodeRawInstanceContract)
    (fromStep : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ atDecode, Trace fromStep 19 entry atDecode ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 19 entry atDecode ∧
      ∃ decodeArgs : DecodeInlineArgs,
        decodeArgs =
            { phase := .first
              stackBase := stackBase
              inputBase := args.inputBase
              bytes := args.bytes } ∧
          DecodeInlinePre decodeArgs atDecode ∧
          Agree decoderPreserved entry atDecode ∧
          ∃ used after,
            Level2ChildSummary
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
              (fromStep + 19) used atDecode after ∧
            level3DecodeChildSummary
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
              (fromStep + 19) used atDecode after ∧
            used ≤ decodeInlineStepBound decodeArgs ∧
            ScopedTrace
              (functionInstanceExecutionPcs generatedProgram
                functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
              (DecodeInlineExit decodeArgs) Level3ChildSummary
              (fromStep + 19) used atDecode after ∧
            DecodeInlinePost decodeArgs atDecode after ∧
            DecodeInlineMachinePost atDecode after ∧
            DecodeInlineOutgoingFrame decodeArgs after ∧
            DecodeInlineCallerSaveArea decodeArgs atDecode after ∧
            ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
              entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
              WrapperSavedRegisterFrame stackBase link s0 s1 s2 atDecode := by
  obtain ⟨atDecode, trace, confined, pc, stack, savedInput, length, globals, inputMemory, agree, retired,
    code, savedFrame⟩ :=
    wrapper_through_allocator_setup allocator fromStep args stackBase entry source machine
  let decodeArgs : DecodeInlineArgs :=
    { phase := .first
      stackBase := stackBase
      inputBase := args.inputBase
      bytes := args.bytes }
  have parentMachine := machine.machine.mono agree retired
  have decodeMachine : DecodeInlineMachinePre decodeArgs atDecode := by
    simpa [DecodeInlineArgs.machineArgs, decodeArgs, zesuDecodeRawMachineArgs] using
      parentMachine.restrict decodeInline_executionPcs_subset_wrapper
  let pre : DecodeInlinePre decodeArgs atDecode :=
    { atEntry := by simpa [decodeArgs, DecodeInlineArgs.entryPc] using pc
      stackValue := by simpa [decodeArgs] using stack
      inputValue := by simpa [decodeArgs] using savedInput
      lengthValue := by simpa [decodeArgs] using length
      globalsValue := globals
      inputMemory := by simpa [decodeArgs] using inputMemory
      code := code
      inputFits := machine.inputFits
      rootInputBound := machine.inputBound
      stackAligned := machine.stackAligned
      stackObjectsFit := machine.stackObjectsFit
      stackObjectsReadable := machine.stackObjectsReadable
      machine := decodeMachine
      retryReason := by simp [decodeArgs]
      propagateReason := by
        intro error phase
        simp [decodeArgs] at phase }
  have firstPhase : decodeArgs.phase = .first := by simp [decodeArgs]
  obtain ⟨used, after, bound, childTrace, post, machinePost, outgoing, saveArea⟩ :=
    decodeInline_first_level3_save_area decodeRaw decodeArgs (fromStep + 19) atDecode pre firstPhase
  have level3 : level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      (fromStep + 19) used atDecode after :=
    ⟨rfl, decodeArgs, pre, bound, childTrace, post, machinePost, outgoing⟩
  exact ⟨atDecode, trace, confined, decodeArgs, rfl, pre, agree, used, after, .decode level3,
    level3, bound, childTrace, post, machinePost, outgoing, saveArea, savedFrame⟩

end BinaryFv.Zesu.MachineExecution
