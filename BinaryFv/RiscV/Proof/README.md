# RISC-V correspondence proofs

The execution modules define programs that manipulate Sail state. This directory proves that those
programs establish the memory and execution facts used by higher-level runners.

[ImageLoadFrame.lean](ImageLoadFrame.lean) proves that the sparse image, input, and fill loaders write
the intended bytes and leave every other address unchanged.
[RunnerCorrespondence.lean](RunnerCorrespondence.lean) connects a proved sentinel trace to the
executable runner's result.

These lemmas are target-independent. Zesu supplies a concrete image and layout; the generic proofs
explain why running the loaders and stepper realizes those target-specific facts.
