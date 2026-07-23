# Zesu values in RISC-V memory

The SSZ specification works with Lean values. The compiled decoder works with Zig records, slices,
optional values, and heap allocations in RISC-V memory. This directory defines predicates that say
when a region of Sail machine memory represents a particular Lean value.

Read `Basic.lean` and `Collections.lean` for reusable words, vectors, slices, and heap arrays. Then
read `Containers.lean` for the seven decoder container types and `RawV4.lean` for the complete
top-level result.

A representation predicate does not allocate or decode anything. It only relates:

- a Lean value,
- the caller's input bytes when a slice borrows from that input,
- a base address, and
- a machine state containing the corresponding bytes and pointers.

Field offsets, sizes, and alignments are checked against the ABI manifest produced by the same pinned
Zig compiler that builds the decoder. Optional payload bytes are intentionally unconstrained when
the option is absent; only the discriminant is meaningful in that case.
