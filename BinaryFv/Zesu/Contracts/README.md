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
  reads, and small input checks. Their meanings follow the source representation exactly, including
  little-endian assembly of multi-byte integers. `Collections.lean` and `Containers.lean` cover
  decoding functions that assemble repeated values and structured SSZ objects.
- `Entry.lean` and `ExportedDecoder.lean` describe the public decoding boundary.
- `CanonicalParams.lean` fixes the environment, ABI layouts, globals, and representations to values
  derived from the pinned artifacts. `CanonicalProgram.lean` states the canonical image, provenance,
  entry, and byte-readability conditions independently of any particular proof decomposition.
- `SemanticObligations.lean` proves the source-shaped meanings' error and acceptance properties and
  isolates the remaining oracle-agreement premise. Its header records the non-kernel trust introduced
  by the one `bv_decide`-based byte-assembly proof.
- `RepresentationAudit.lean` proves that the canonical representations depend only on memory.
  `Footprint.lean` identifies the memory each representation actually reads and proves the footprints
  are tight.
- `FrameGap.lean` exhibits why child postconditions alone permit a later sibling to overwrite an
  earlier result. `Ownership.lean` introduces the required write confinement, and
  `OwnershipComposition.lean` proves how confined sibling runs preserve prior representations. These
  modules supply reusable conditional composition theorems; concrete machine proofs must establish
  their write premises.
- `ExportedDecoderAudit.lean` pins the public C ABI bindings and rejects the old internal calling
  convention. `CatalogAudit.lean` checks catalog structure independently of machine execution.
- `ContractComposition.lean` contains the generic catalog-wide local-to-global theorem. D′'s public
  root does not require a completed 141-instance proof: it exposes the three exported contracts as
  assumptions and leaves their refinement to later PRs.
