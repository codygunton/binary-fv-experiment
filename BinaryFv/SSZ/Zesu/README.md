# Zesu verification modules

The directory names describe the subject of each definition or theorem; there is no catch-all
`Proof` namespace.

- [`Artifact`](Artifact): the pinned ELF, symbols, compiler-reflected ABI data, and closed instruction
  inventories.
- [`ControlFlow`](ControlFlow): decoded functions, basic-block/control-flow facts, and reachability.
- [`MachineExecution`](MachineExecution): generated-Sail instruction behavior and composed block
  traces.
- [`MemoryRepresentation`](MemoryRepresentation): predicates and observers connecting Sail memory to
  native Zesu values.
- [`SpecCorrespondence`](SpecCorrespondence): lemmas connecting machine-memory operations to the
  SizzLean specification.
- [`Runtime`](Runtime): allocator, allocation-bound, and memory-copy contracts.
- [`Entrypoints`](Entrypoints): end-to-end ABI-call traces and result interpretation, grouped by
  exported function.
  `ZesuDecodeRaw` covers `zesu_decode_raw`.
- [`Contracts`](Contracts): the source-level meaning of each decoder routine and the machine
  interface each compiled function instance must satisfy. Begin with its [README](Contracts/README.md).
- [`Elfling`](Elfling): the generated function instance map and its validation against the canonical ELF,
  including control-flow edges, calls, inlined children, global addresses, and parameter locations.
  Begin with its [README](Elfling/README.md); regenerate the data with
  `nix build .#elfling-program`.

[`Interface.lean`](Interface.lean) defines the public executable API. The SSZ root theorem is in
[`BinaryFv/SSZ/Root.lean`](../Root.lean).

[`MachineExecution/BlobScheduleAndResultStores.lean`](MachineExecution/BlobScheduleAndResultStores.lean)
is a retained vertical slice containing both closed instruction inventories and their execution
proofs.
