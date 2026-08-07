# Recovering Zesu's decoded value from machine memory

This directory turns the bytes, pointers, and lengths left by the compiled Zesu decoder into the
`StatelessInput` value used by the Ethereum SSZ specification. This is not another parser for the
original SSZ input. It reads Zesu's already-decoded result from RISC-V memory and proves what value
that memory contains.

That bridge is necessary because the machine proof and the specification speak different
languages. The machine proof ends with registers and memory; the specification returns a structured
Lean value. Without this layer, the root theorem could show that Zesu executed and wrote bytes, but
not that those bytes represent the value returned by the specification.

## Describing the decoded result in memory

[`StatelessInput.lean`](StatelessInput.lean) describes the complete top-level result using the native
layouts of integers, slices, arrays, optional values, pointers, and allocations.
[`Containers.lean`](Containers.lean) describes the seven heap-owning Zig structs nested inside that
result. [`Result.lean`](Result.lean) describes the result value and status stored by `decodeRaw`.

These predicates do not run the decoder or allocate memory. They state what must already be present
for memory to contain a particular value. Field offsets, sizes, and alignments are checked against
the ABI manifest from the pinned Zig build. Borrowed slices also record the original input buffer
because some decoded fields point into it instead of owning a copy.

## Reconstructing the Lean value

[`Observers.lean`](Observers.lean) safely reads primitive fields, slices, and nested structs from
Sail memory. [`PrimitiveReads.lean`](PrimitiveReads.lean) connects the bytes it reads to the pinned
SSZ integer readers. [`ValueObserver.lean`](ValueObserver.lean) combines them into
`observeStatelessInput?` and proves that a memory state satisfying the representation reconstructs
exactly the claimed `BinaryFv.Specs.SSZ.StatelessInput`.

That uniqueness result prevents an incomplete layout from assigning two different decoded values
to the same machine state. The complete `ChainConfigRep`, for example, ensures that the fork
activation and optional blob schedule are determined by memory rather than silently left free.

## Showing that the decoded value follows the specification

The remaining files connect Zesu's source-level decoding rules to the pinned Ethereum SSZ
specification. They establish the specification side of the same final value comparison:

- [`EntryOffsets.lean`](EntryOffsets.lean) proves that both decoders read the same four top-level
  offsets and therefore split the input into the same four field bodies.
- [`ChainOffsets.lean`](ChainOffsets.lean) proves the corresponding facts for the nested fork
  activation, fork configuration, and chain configuration values, including their fixed fields.
- [`EncodeDecode.lean`](EncodeDecode.lean) proves the needed fact that re-encoding a successfully
  decoded 64-bit value reproduces its bytes. Its bit-vector proof uses `bv_decide`, and the file
  records the resulting trust dependency.
- [`ZeroOffsetAlias.lean`](ZeroOffsetAlias.lean) proves that a zero first offset is rejected for lists
  of variable-size elements, while documenting why the statement is false for fixed-size elements.
