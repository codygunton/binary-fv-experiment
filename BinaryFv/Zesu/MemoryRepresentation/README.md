# Reading Zesu values from machine memory

The Ethereum SSZ specification describes structured Lean values. The compiled Zesu decoder stores
the same information as Zig records, optional values, slices, pointers, and heap allocations in
RISC-V memory. This directory defines and proves the connection between those two views.

A representation states what bytes and pointers must be present for memory to hold a particular
Lean value. It does not run the decoder or allocate memory. Some slices point into the caller's
input buffer rather than owning a copy, so their representations include both the input bytes and
the address of that buffer.

## Memory layouts

1. [`RawV4.lean`](RawV4.lean) defines the common layouts for bytes, little-endian integers, slices,
   arrays, and optional values, then uses them to describe the complete top-level `RawV4` value.
2. [`Containers.lean`](Containers.lean) describes the seven nested Zesu container types, including
   their inline fields and heap-backed collections.
3. [`Result.lean`](Result.lean) describes the value and status stored by `decodeRaw` when it returns.

The field addresses, sizes, and alignments in these definitions are checked against the ABI manifest
from the pinned Zig build. When an optional value is absent, only its discriminant has meaning; the
unused payload bytes are deliberately left unconstrained.

## Reading values back

[`Observers.lean`](Observers.lean) contains functions that read bytes, words, slices, and container
fields from Sail memory. Each function returns `none` if a required byte or pointer is missing.
[`PrimitiveReads.lean`](PrimitiveReads.lean) applies the pinned SSZ integer readers to bytes obtained
from memory.

[`ValueObserver.lean`](ValueObserver.lean) combines those readers into `observeRawV4?`, which
reconstructs a complete `BinaryFv.Specs.SSZ.RawV4`. Its main theorem says that if memory represents a
value, and the borrowed input buffer is present, the observer returns exactly that value.

This reverse direction matters for soundness. A layout that leaves part of a value unspecified
could claim that the same machine state represents two different Lean values. A previous
`RawV4FixedFieldsRep` did exactly that by omitting fields of the chain configuration.
`RawV4.lean` now includes the full `ChainConfigRep`, and its regression theorem checks that the fork
activation and blob schedule are fixed by memory.

## Agreement with the SSZ specification

The remaining files prove that Zesu's source-level decoding rules inspect the same bytes as the
pinned Ethereum SSZ specification:

- [`EntryOffsets.lean`](EntryOffsets.lean) proves that both decoders read the same four top-level
  offsets and therefore split the input into the same four field bodies.
- [`ChainOffsets.lean`](ChainOffsets.lean) proves the corresponding facts for the nested fork
  activation, fork configuration, and chain configuration values, including their fixed fields.
- [`EncodeDecode.lean`](EncodeDecode.lean) proves the needed fact that re-encoding a successfully
  decoded 64-bit value reproduces its bytes. Its bit-vector proof uses `bv_decide`, and the file
  records the resulting trust dependency.
- [`ZeroOffsetAlias.lean`](ZeroOffsetAlias.lean) proves that a zero first offset is rejected for lists
  of variable-size elements, while documenting why the statement is false for fixed-size elements.
