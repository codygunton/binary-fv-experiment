# Proving that Zesu's allocations succeed

Zesu allocates the decoded value from a fixed memory arena. The verification must show that these
allocations behave like the compiled allocator and that every admitted decode fits in the arena.
Otherwise a proof of the parsing logic could still end in an unexpected out-of-memory result.

This directory provides that runtime argument:

- [`BumpAllocator.lean`](BumpAllocator.lean) models the allocator's actual rule: align the current
  cursor, return that address, and advance the cursor when the request fits.
- [`AllocationBound.lean`](AllocationBound.lean) bounds the total memory an admitted decode may
  request and proves that the bound fits in Zesu's arena.
- [`AllocationCursor.lean`](AllocationCursor.lean) includes alignment padding, adds the costs of
  successive allocations, and proves that an allocation succeeds whenever the remaining bound fits.
- [`AllocatorVtable.lean`](AllocatorVtable.lean) proves that the allocator function pointer loaded
  from the pinned binary has the expected value.

These files prove the reusable allocator model and arithmetic. A concrete machine proof must still
show that the binary's cursor follows this model and that its actual allocation requests stay within
the bound. The source-function contracts for those calls live in
[`Contracts/Runtime.lean`](../Contracts/Runtime.lean); fixed call sites and vtable addresses from the
ELF live in [`Artifacts/AllocatorCalls.lean`](../Artifacts/AllocatorCalls.lean).
