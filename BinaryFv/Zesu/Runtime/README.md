# Zesu runtime support

This directory models implementation details supplied by Zesu's runtime rather than by the SSZ decoder
logic itself. It currently covers the bump allocator, its compiler-visible call interface, and the
allocation bound used by decoder proofs.

- `BumpAllocator.lean` defines the allocator state and operations.
- `AllocatorVtable.lean` connects those operations to the function pointers found in the pinned binary.
- `AllocationBound.lean` states the resource bound needed by higher-level execution proofs.
- `AllocationCursor.lean` proves the padding-aware cursor arithmetic needed to turn a total allocation
  bound into success of each bump allocation and non-exhaustion of the arena. Connecting that pure
  model to the machine cursor remains a concrete execution-proof obligation.

Semantic obligations for source functions that use the runtime belong in `Contracts/Runtime.lean`; immutable
allocator call-site facts belong in `Artifacts/AllocatorCalls.lean`.
