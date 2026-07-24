# Zesu values in RISC-V memory

The SSZ specification works with Lean values. The compiled decoder works with Zig records, slices,
optional values, and heap allocations in RISC-V memory. This directory defines predicates that say
when a region of Sail machine memory represents a particular Lean value.

Read the files in this order:

1. [`RawV4.lean`](RawV4.lean) defines the reusable byte, word, vector, slice, and heap-array
   predicates, then builds the complete top-level `RawV4Rep`.
2. [`Containers.lean`](Containers.lean) defines the seven nested decoder-container representations.
3. [`Result.lean`](Result.lean) describes the internal `decodeRaw` hidden-result union.
4. [`Observers.lean`](Observers.lean) contains guarded functions that reconstruct represented values
   from Sail memory.

A representation predicate does not allocate or decode anything. It only relates:

- a Lean value,
- the caller's input bytes when a slice borrows from that input,
- a base address, and
- a machine state containing the corresponding bytes and pointers.

Field offsets, sizes, and alignments are checked against the ABI manifest produced by the same pinned
Zig compiler that builds the decoder. Optional payload bytes are intentionally unconstrained when
the option is absent; only the discriminant is meaningful in that case.
