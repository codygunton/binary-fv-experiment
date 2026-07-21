# Zesu verification modules

The directory names describe the subject of each definition or theorem; there is no catch-all
`Proof` namespace.

- `Artifact`: the pinned ELF, symbols, compiler-reflected ABI data, and closed instruction
  inventories.
- `ControlFlow`: decoded functions, basic-block/control-flow facts, and reachability.
- `MachineExecution`: generated-Sail instruction behavior and composed block traces.
- `MemoryRepresentation`: predicates and observers connecting Sail memory to native Zesu values.
- `SpecCorrespondence`: lemmas connecting machine-memory operations to the SizzLean specification.
- `Runtime`: allocator, allocation-bound, and memory-copy contracts.
- `Entrypoints`: end-to-end ABI-call traces and result interpretation, grouped by exported function.
  `ZesuDecodeRaw` covers `zesu_decode_raw`.

`Interface.lean` defines the public executable API. The SSZ root theorem is in the parent
`BinaryFv/SSZ/Root.lean` module.

`MachineExecution/BlobScheduleAndResultStores.lean` is a retained vertical slice: it currently
contains both closed instruction inventories and their execution proofs. Its next structural
cleanup is to move the inventories to `Artifact` while preserving the proved declarations.
