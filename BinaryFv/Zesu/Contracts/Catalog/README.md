# Matching Zesu source functions to contracts

This directory records which Zesu source functions the verification covers and which behavioral
contract each one must satisfy. The entries contain source names and concrete generic
specializations, but no instruction addresses. A separate generated program records where each
compiled function instance appears in the pinned binary.

[`Entries.lean`](Entries.lean) contains the list. For each source function it records:

- the source file, qualified function name, and generic specialization that identify it;
- which handwritten contract describes its behavior;
- whether the function must appear in the binary or is intentionally absent, with a checked reason.

The module also records the expected hash of each pinned source file. Generated function instances
carry their source-file hash, which is checked against this list.

[`Dispatch.lean`](Dispatch.lean) turns a catalog entry and a compiled function instance into the
precise proposition that must be proved about that instance. The proposition retains the real input
and result types of the selected contract; for example, an integer reader and the exported decoder
do not get forced into one erased, weak interface.

[`Validation.lean`](Validation.lean) states the checks that connect the list to a generated program:

- every required source function has a compiled instance;
- every compiled instance belongs to a listed source function;
- excluded functions really are absent;
- no two entries or instances are accidentally treated as the same;
- every required generic specialization, such as a particular `readArray` width, is present; and
- extraction reported no unresolved source attribution.

The same module also collects specification-level claims about the contracts, such as which errors
they may return, when they accept input, and whether the composed decoder returns the same value as
the pinned Ethereum SSZ specification.

[`../Catalog.lean`](../Catalog.lean) only imports these three modules.
[`../CatalogAudit.lean`](../CatalogAudit.lean) proves the closed checks about the handwritten list.
Proofs about the meanings of the functions are in
[`../SemanticObligations.lean`](../SemanticObligations.lean), while proofs that compiled instructions
satisfy the selected contracts belong to the machine-execution and refinement layers.
