# RISC-V machine logic

This directory defines reusable statements about Sail RISC-V states and executions. It does not
parse executables or run the concrete loaders.

[`LoadedImage.lean`](LoadedImage.lean) says when a parsed `ProgramImage` has been loaded faithfully
into Sail memory. [`Execution/ImageLoad.lean`](../Execution/ImageLoad.lean) implements the loaders,
and [`Proof/ImageLoadCorrectness.lean`](../Proof/ImageLoadCorrectness.lean) proves what those loaders
write and preserve. This separation allows the same loaded-image relation to be used with an image
obtained from ELF or from another executable format.

The other modules define machine execution, traces, memory and register framing, separation logic,
loop induction, and the sentinel-terminated runner interface used by target proofs.
