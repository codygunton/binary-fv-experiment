# Building and running `zesu_decode_raw`

This directory is the bridge from the public Lean API to the concrete Sail execution of the exported
decoder. Read the files in this order:

1. `Layout.lean` places the input, stack, and return sentinel away from the linked image and heap.
2. `Preflight.lean` rejects a different ELF or an input outside the theorem's size bound.
3. `Fuel.lean` derives the runner budget from the exported occurrence's contract bound.
4. `StateBuilder.lean` configures Sail, loads file-backed image bytes, initializes globals, copies the
   input, and writes the C ABI registers.
5. `EntryBinding.lean` proves that the resulting state satisfies the exported contract's entry
   predicate.

Only file-backed ELF bytes are loaded eagerly. The roughly 69 MiB BSS and arena tail remain sparse;
the builder writes the mutable globals it needs explicitly. `CodeIntactRegression.lean` demonstrates
why code integrity covers file-backed bytes rather than requiring mutable BSS to remain equal to its
initial zero image.

The runner stops when the decoder returns to the sentinel. Reaching the sentinel, trapping, and
exhausting fuel are distinct outcomes so later correspondence proofs cannot conflate them.
