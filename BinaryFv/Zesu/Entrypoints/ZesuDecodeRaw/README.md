# Building and running `zesu_decode_raw`

This directory contains both the executable runner and the proof that three exported machine
contracts are sufficient for that runner to agree with the SSZ specification. Read it in three
groups.

## Executable runner

1. [Layout.lean](Layout.lean) places the input, stack, and return sentinel away from the linked image
   and heap.
2. [Preflight.lean](Preflight.lean) rejects a different ELF or an input outside the theorem's size
   bound.
3. [Fuel.lean](Fuel.lean) derives the runner budget from the exported function instance's contract bound.
4. [StateBuilder.lean](StateBuilder.lean) configures Sail, loads file-backed image bytes, initializes
   globals, copies the input, and writes the C ABI registers.
5. [EntryBinding.lean](EntryBinding.lean) proves that the resulting state satisfies the exported
   contract's entry predicate.
6. [Classify.lean](Classify.lean) turns a finished run plus the two accessor returns into a public
   outcome or a specific error.
7. [Runner.lean](Runner.lean) puts it together; the public
   [Interface.lean](../../Interface.lean) delegates to it.

## Contract entry and result interpretation

1. [EntryBinding.lean](EntryBinding.lean) proves that the constructed Sail state satisfies the
   exported decoder contract's real C ABI entry condition.
2. [DecodeGlue.lean](DecodeGlue.lean) converts the decoder contract's exit facts into the successful
   or rejected result facts consumed by the classifier.
3. [Accessors.lean](Accessors.lean) threads the two accessor calls and states exactly which accessor
   traces remain machine-proof premises.

## Machine-to-runner assembly

1. [GeneratedReturnExits.lean](../../Elflings/GeneratedReturnExits.lean) establishes that the three
   exported exits used here really decode as returns.
2. [ReturnToSentinel.lean](ReturnToSentinel.lean) proves that executing those returns reaches the
   runner's stop address.
3. [ExportedContractExecution.lean](ExportedContractExecution.lean) assumes the contracts for the
   exported decoder and two accessors, then derives the successful and rejected machine runs used by
   `Root.lean`.

## Level 4 inventory

[Level4BoundaryInventory.lean](Level4BoundaryInventory.lean) names the 18 production rows displayed
under emitted `ssz_raw.decodeRaw`: 14 generated `FunctionInstance` values and four separately typed
cleanup or stdlib regions. It records the four direct `readOffset` occurrences independently. The
four non-`FunctionInstance` boundaries cannot use `FunctionInstanceContract`; Level 4 must give them
honest inline-region contracts. The generated machine-region check also pins `decodeRaw`'s 172
parent-owned PCs; this inventory is the boundary map for the next machine-proof refinement, not a
semantic proof of those boundaries.

Only file-backed ELF bytes are loaded eagerly. The roughly 69 MiB BSS and arena tail remain sparse;
the builder writes the mutable globals it needs explicitly, and zero-fills the machine stack the way
an operating system hands a process zeroed pages — without that, the decoder's genuine reads of
stack bytes it never wrote would trap, since Sail's `readByte` traps on absent memory. The arena
needs no such fill: the allocator's blocks are written before they are read, which the executable
runner tests confirm end to end. [CodeIntactRegression.lean](CodeIntactRegression.lean) demonstrates
why code integrity covers file-backed bytes rather than requiring mutable BSS to remain equal to its
initial zero image.

The runner stops when the decoder returns to the sentinel, then *executes* the two exported
accessors — `zesu_raw_result` and `zesu_raw_error` — from the post-return state rather than
re-reading the globals they read, so the answer depends on the same code a caller would run.
Reaching the sentinel, trapping, and exhausting fuel are distinct outcomes, and so are the ways a
returned run can still fail: an undocumented status, a result slot that disagrees with the return
code, an unreadable value, and an exhausted arena each keep their own error. None of them may become
a rejection — `wrapper_rejection_forces_checks` states that as a converse and
`executeDecode_rejected_forces_checks` lifts it to the public entry.

`Root.root_compliance_of_exported_contracts` is the public conclusion. It does not assume that an
arbitrary generated program is correct: it assumes the three exported contracts used by this
runner. Concrete Sail proofs discharge those assumptions one contract at a time.
