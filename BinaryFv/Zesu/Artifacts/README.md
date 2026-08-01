# Zesu binary artifacts

This directory records immutable facts extracted from the pinned Zesu ELF. It contains the binary
image, load layout, symbols, compiler ABI information, allocator call sites, and closed instruction
inventories used by later proofs.

These files answer questions about what was shipped, not what the decoder ought to do. Semantic
requirements belong in `Contracts/`; decoded control-flow facts belong in `ControlFlow/`.

- `Image.lean` and `Layout.lean` define the canonical bytes and their loaded address ranges.
- `Symbols.lean` names important addresses in that image.
- `AbiManifest.lean` and `AllocatorCalls.lean` record compiler-derived interface facts.
- `PrimitiveReadInventory.lean` records the pinned instruction words for primitive readers.
