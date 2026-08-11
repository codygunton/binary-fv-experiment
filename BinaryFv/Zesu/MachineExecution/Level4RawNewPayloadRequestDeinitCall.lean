import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4Contracts
import BinaryFv.Zesu.MachineExecution.Level4RawNewPayloadRequestDeinitSteps

/-! # Selected excluded:3 call and return inside `decodeRaw` -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.RiscV
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open LeanRV64DExecutable.Functions Register RegisterWriteStep

set_option genInjectivity false in
/-- Live parent facts after the `jalr` at `0x129e8` enters selected excluded region 3. -/
structure Level4RawNewPayloadRequestDeinitCallReady (margs : DecoderMachineArgs)
    (origin before : State) where
  frame : Level4DecodeRawParentFrame margs origin before
  args : DeinitInlineArgs
  recordBase : args.recordBase = frame.stack - 0x690 + 0x2d0
  stackPointer : args.stackPointer = frame.stack - 0x690
  frameSize : args.frameSize = 0x50
  atPc : before.regs.get? PC = some (BitVec.ofNat 64 0x131ec)
  link : before.regs.get? x1 = some (BitVec.ofNat 64 0x129ec)
  record : before.regs.get? x10 = some (BitVec.ofNat 64 args.recordBase)
  allocator : before.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase)
  allocatorPair : DeinitAllocatorPair args before
  allocatorOutsideFrame : DeinitAllocatorPairOutsideFrame args
  allocatorFits : args.allocatorBase < 2 ^ 64

/-- The concrete child entry follows from the protected raw frame and the live values established
by the parent setup at `0x129cc..0x129e8`. -/
theorem Level4RawNewPayloadRequestDeinitCallReady.interfaceEntry
    (ready : Level4RawNewPayloadRequestDeinitCallReady margs origin before) :
    rawNewPayloadRequestDeinitInterface.entry ready.args before := by
  rcases ready with ⟨frame, args, recordBase, stackPointer, frameSize, atPc, link,
    record, allocator, allocatorPair, allocatorOutsideFrame, allocatorFits⟩
  obtain ⟨entry, stackEq, -, -, sp, -, -, -, -, -, -, code, -, -⟩ := frame.invariant
  have entryPostStackEq := entry.postStackEq
  have postStackEq : entry.postStack = frame.stack - 0x690 := by omega
  have postStackFits : frame.stack - 0x690 < 2 ^ 64 := by
    have stackFits := entry.stackFits
    omega
  refine ⟨atPc, ?_, record, allocator, ?_, link, allocatorPair, allocatorOutsideFrame,
    frameSize, ?_, ?_, allocatorFits, ?_, ?_⟩
  · change Artifacts.programImage.fileBytesLoadedFaithfully before.mem
    exact code
  · rw [stackPointer, ← postStackEq]
    exact sp
  · rw [frameSize, stackPointer, ← postStackEq]
    exact entry.nestedCallFrameFits
  · rw [recordBase, ← postStackEq]
    have stackFits := entry.stackFits
    omega
  · rw [stackPointer]
    exact postStackFits
  · rw [stackPointer, frameSize, ← postStackEq]
    have stackFits := entry.stackFits
    omega

private theorem savedWordBytes_of_deinitFrame
    {args : DeinitInlineArgs} {before after : State} {stack offset : Nat} {value : BitVec 64}
    (stackPointer : args.stackPointer = stack - 0x690)
    (memory : WritesOnlyWithin (rawNewPayloadRequestDeinitFrame args) before after)
    (minimum : 0x788 ≤ offset) (saved : SavedWordBytes before (stack + offset) value) :
    SavedWordBytes after (stack + offset) value := by
  intro index bound
  rw [memory (stack + offset + index) (by
    simp only [rawNewPayloadRequestDeinitFrame]
    rw [stackPointer]
    intro inside
    omega)]
  exact saved index bound

private theorem level4DecodeRawPrologueSavedFrame_of_deinitFrame
    {args : DeinitInlineArgs} {before after : State} {stack : Nat}
    {ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64}
    (stackPointer : args.stackPointer = stack - 0x690)
    (memory : WritesOnlyWithin (rawNewPayloadRequestDeinitFrame args) before after)
    (saved : Level4DecodeRawPrologueSavedFrame before stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) :
    Level4DecodeRawPrologueSavedFrame after stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 := by
  rcases saved with ⟨hra, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11⟩
  exact ⟨savedWordBytes_of_deinitFrame stackPointer memory (by omega) hra,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs0,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs1,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs2,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs3,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs4,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs5,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs6,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs7,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs8,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs9,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs10,
    savedWordBytes_of_deinitFrame stackPointer memory (by omega) hs11⟩

/-- The selected deinit summary returns at the real parent continuation and reconstructs the full
protected raw-decoder frame; excluded region 10 remains internal to the selected contract. -/
theorem level4_rawNewPayloadRequestDeinit_call_return
    (contract : RawNewPayloadRequestDeinitContract)
    (ready : Level4RawNewPayloadRequestDeinitCallReady margs origin before) (fromStep : Nat) :
    ∃ used after,
      Trace fromStep used before after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x129ec) ∧
      ready.frame.PreservedTo after := by
  rcases ready with ⟨frame, args, recordBase, stackPointer, frameSize, atEntry, link,
    record, allocator, allocatorPair, allocatorOutsideFrame, allocatorFits⟩
  let ready : Level4RawNewPayloadRequestDeinitCallReady margs origin before :=
    ⟨frame, args, recordBase, stackPointer, frameSize, atEntry, link, record, allocator,
      allocatorPair, allocatorOutsideFrame, allocatorFits⟩
  have interfaceEntry := ready.interfaceEntry
  obtain ⟨used, after, -, trace, atPc, -, sp, -, -, -, memory, agree, retired, code, -⟩ :=
    rawNewPayloadRequestDeinit_call contract args fromStep before interfaceEntry
  obtain ⟨entry, stackEq, raEq, saved, -, input, inputSep, stackWritable, rawWritable,
    rawSep, aligned, -, machine, -⟩ := frame.invariant
  have inputAfter : DecodedValue.MemoryBytes after margs.inputBase margs.bytes := by
    apply input.of_mem_eq
    intro index bound
    rw [memory (margs.inputBase + index) (by
      simp only [rawNewPayloadRequestDeinitFrame]
      intro inside
      have entryPostStackEq := entry.postStackEq
      have separated := entry.nestedCallFrameInputSeparated (margs.inputBase + index)
        (by omega) (by omega)
      omega)]
  have savedAfter := level4DecodeRawPrologueSavedFrame_of_deinitFrame
    stackPointer memory saved
  have machineAfter : DecoderMachinePre decodeRawExecutionPcs margs after :=
    machine.mono agree retired
  refine ⟨used, after, trace.trace.toTrace, atPc, entry, stackEq, raEq, savedAfter, ?_, inputAfter,
    inputSep, stackWritable, rawWritable, rawSep, aligned, code, machineAfter, retired⟩
  have entryPostStackEq := entry.postStackEq
  have argsPostStack : args.stackPointer = entry.postStack := by omega
  rw [← argsPostStack]
  exact sp

end BinaryFv.Zesu.MachineExecution
