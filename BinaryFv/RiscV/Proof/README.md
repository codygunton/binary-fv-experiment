# RISC-V correspondence proofs

The execution modules define programs that manipulate Sail state. This directory proves that those
programs establish the memory and execution facts used by higher-level runners.

[ImageLoadCorrectness.lean](ImageLoadCorrectness.lean) proves that the sparse image, input, and fill
loaders write the intended bytes and leave every other address unchanged. In particular, loading a
single-segment `ProgramImage` establishes `fileBytesLoadedFaithfully`; ELF parsing into that image is
a separate step.
[RunnerCorrespondence.lean](RunnerCorrespondence.lean) shows that when Sail execution reaches the
runner's reserved stop address, the executable runner returns the result observed in that final
machine state.

These lemmas are target-independent. Zesu supplies a concrete image and layout; the generic proofs
explain why running the loaders and stepper realizes those target-specific facts.
