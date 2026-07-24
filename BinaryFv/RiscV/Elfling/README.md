# Elfling proof layer

Elfling connects a compiled RISC-V program to readable, function-shaped Lean proofs. The extractor
finds each emitted or inlined function occurrence in the binary and records its instructions,
control-flow edges, children, calls, and exits. Lean checks that generated description before using
it in a proof.

If you are new to this directory, read the files in this order:

1. [`BinaryFv/Binary/Elfling/Instance.lean`](../../Binary/Elfling/Instance.lean) defines the
   architecture-independent program and function-occurrence data.
2. [`FunctionTrace.lean`](FunctionTrace.lean) describes execution that stays inside one occurrence.
3. [`Contract.lean`](Contract.lean) separates a routine's shared meaning from one occurrence's
   register and memory placement.
4. [`Boundary.lean`](Boundary.lean) composes a parent trace with summaries of calls and inlined
   children.
5. [`BoundaryTests.lean`](BoundaryTests.lean) contains small positive and negative examples of the
   boundary checks.

An **occurrence** is one compiled appearance of a source routine. A routine may have one standalone
body and several inlined occurrences, each with different registers or stack slots. A **binding**
describes that machine-specific placement; a **specification** describes the source-level result and
is shared between occurrences.

The generated files and extracted addresses are evidence, not trusted axioms. Boolean checks and
Lean theorems in this layer reject stale edges, invented boundaries, missing parameter locations,
and inconsistent step counts.
