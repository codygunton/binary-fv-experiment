# Zesu machine execution

This directory proves how concrete instructions and basic blocks from the pinned Zesu binary execute
under the generated Sail RISC-V semantics. It is the target-specific bridge between decoded machine
code and the higher-level source-function contracts.

- `DecodeTactic.lean` provides local support for discharging instruction-decoding goals.
- `RegisterRuns.lean` supplies compatibility wrappers for the generic `NonzeroXRegister` read/write
  runs in `RiscV/Instruction/Frame/Register.lean`.
- `InstructionClassSteps.lean` and `GeneratedWordStep.lean` are the preferred instruction and
  generated-image evidence entry points. `decodeInline_first_result_pointer_step` uses
  `GeneratedWordStep.generatedRegisterWriteStep` with explicit `.ITYPE` and `execute_ITYPE_run`
  premises. The latter requires `fileBytesLoadedFaithfully`, `readFileByte?`, and `DecoderMachinePre`;
  it does not apply to Blob's `matchesMemory`/`readByte?` evidence without a proved bridge.
- `Seg.lean` composes a measured expensive straight-line owned segment without exposing each
  successor state. Before introducing a new segment, look for an existing owned route such as
  `wrapper_dispatch_tag3_owned_terminal_route` in `Level2OutcomeDispatch.lean`.
- `ParserBlocks.lean` proves selected parser block executions.
- `BlobScheduleAndResultStores.lean` is an older standalone vertical slice retained temporarily; no
  active root proof depends on it.

Closed instruction inventories belong in `Artifacts/`; control-flow structure belongs in
`ControlFlow/`; source function meanings belong in `Contracts/`.
