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

Representations say when memory *holds* a value; observers go the other way and *read* one back.
[Observers.lean](Observers.lean) has the guarded readers for words, byte regions, and the chain
config, and [ValueObserver.lean](ValueObserver.lean) assembles them into `observeRawV4?`, which
reconstructs a complete
`SszBridge.RawV4` from machine memory. `observe_raw_v4_of_rep` is the correspondence that ties the
two directions together: anything the representation says is there, the observer reads back exactly.
It needs one hypothesis the representation deliberately omits — the caller's input in memory —
because the borrowed slices alias that buffer.

A representation that under-determines its value makes a *total* observer impossible, which is not a
stylistic concern but a soundness one: `RawV4FixedFieldsRep` once pinned only two words of the chain
config, so one state represented values differing in the fork activation and blob schedule, and the
observer correspondence was false as stated. [RawV4.lean](RawV4.lean) now pins the whole
`ChainConfigRep`, with
`rawV4FixedFields_pins_fork_activation_and_blob_schedule` as the regression.
