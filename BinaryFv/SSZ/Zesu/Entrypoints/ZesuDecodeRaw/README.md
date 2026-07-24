# Building and running `zesu_decode_raw`

This directory is the bridge from the public Lean API to the concrete Sail execution of the exported
decoder. Read the files in this order:

1. [Layout.lean](Layout.lean) places the input, stack, and return sentinel away from the linked image
   and heap.
2. [Preflight.lean](Preflight.lean) rejects a different ELF or an input outside the theorem's size
   bound.
3. [Fuel.lean](Fuel.lean) derives the runner budget from the exported occurrence's contract bound.
4. [StateBuilder.lean](StateBuilder.lean) configures Sail, loads file-backed image bytes, initializes
   globals, copies the input, and writes the C ABI registers.
5. [EntryBinding.lean](EntryBinding.lean) proves that the resulting state satisfies the exported
   contract's entry predicate.
6. [Classify.lean](Classify.lean) turns a finished run plus the two accessor returns into a public
   outcome or a specific error.
7. [Runner.lean](Runner.lean) puts it together; the public
   [Interface.lean](../../Interface.lean) delegates to it.

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

[RunnerExecution.lean](../../Validation/RunnerExecution.lean) runs all of this against the pinned
binary in the Sail model and compares the result with the SSZ oracle.
