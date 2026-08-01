# Zesu contracts

This directory states what source-level Zesu functions are required to mean. Contracts describe
inputs, outputs, failure behavior, and memory ownership without baking in a compiled address or
control-flow layout.

A source function and a compiled function instance are not the same thing. The catalog assigns one
contract to each source function identity, including concrete generic specializations such as
`readArray[32]`. The generated program may contain several emitted or inlined instances of that
identity; contract dispatch applies the source function's contract separately to every such instance.

That separation is deliberate: recompiling Zesu may change its blocks and addresses without changing
the behavior it must implement. Binary structure belongs in `Artifacts/`, `ControlFlow/`, and
`Elflings/`; proofs about concrete instructions belong in `MachineExecution/`.

- `Catalog/Entries.lean` is the authoritative list of source function identities and their contract
  tags. `Catalog/Dispatch.lean` maps each generated function instance to the typed contract selected
  by its source identity. `Catalog/Validation.lean` states coverage, uniqueness, and semantic checks.
  `Catalog.lean` is only their umbrella import; `CatalogAudit.lean` proves structural facts about them.
- `PrimitiveReadsAndSlices.lean` contains contracts for bounded byte slices, integer reads, fixed-size
  reads, and small input checks. `Collections.lean` and `Containers.lean` cover decoding functions
  that assemble repeated values and structured SSZ objects.
- `Entry.lean` and `ExportedDecoder.lean` describe the public decoding boundary.
- `CanonicalProgram.lean` checks that the program and environment used by the contracts come from the
  pinned Zesu sources and ELF. `ContractComposition.lean` proves that the per-instance obligations
  compose along the call and inline graph into the entrypoint obligation used by the root theorem.
