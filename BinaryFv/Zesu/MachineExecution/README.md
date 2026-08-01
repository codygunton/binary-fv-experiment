# Zesu machine execution

This directory proves how concrete instructions and basic blocks from the pinned Zesu binary execute
under the generated Sail RISC-V semantics. It is the target-specific bridge between decoded machine
code and the higher-level source-function contracts.

- `DecodeTactic.lean` provides local support for discharging instruction-decoding goals.
- `RegisterRuns.lean` proves recurring register-level execution patterns.
- `ParserBlocks.lean` proves selected parser block executions.
- `BlobScheduleAndResultStores.lean` is an older standalone vertical slice retained temporarily; no
  active root proof depends on it.

Closed instruction inventories belong in `Artifacts/`; control-flow structure belongs in
`ControlFlow/`; routine meanings belong in `Contracts/`.
