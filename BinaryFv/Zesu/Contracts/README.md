# Zesu contracts

This directory states what Zesu routines are required to mean. Contracts describe inputs, outputs,
failure behavior, memory ownership, and the correctness claim for each routine without baking in its
current address or control-flow layout.

That separation is deliberate: recompiling Zesu may change its blocks and addresses without changing
the behavior it must implement. Binary structure belongs in `Artifacts/`, `ControlFlow/`, and
`Elflings/`; proofs about concrete instructions belong in `MachineExecution/`.

- `Catalog.lean` collects the per-routine contracts, and `CatalogAudit.lean` checks the catalog's
  expected shape.
- `Leaves.lean`, `Collections.lean`, `Containers.lean`, and related files group contracts by behavior.
- `Entry.lean` and `ExportedDecoder.lean` describe the public decoding boundary.
- `ProgramCorrectness.lean` packages the local obligations needed to prove the whole program correct.
