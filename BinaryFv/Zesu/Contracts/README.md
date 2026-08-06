# Zesu function contracts

This directory states what each relevant Zesu function must do. A contract names the function's
inputs, its result or error, the machine state in which it may run, and the memory it may change. It
does not depend on the addresses chosen by one particular compilation.

One source function can appear more than once in the binary because the compiler may emit a callable
copy, inline it into callers, or specialize a generic function for several concrete types or sizes.
Each compiled appearance is a **function instance**. The catalog gives all instances originating
from the same source function the same behavioral contract, while allowing each instance to have
its own addresses and register bindings.

## Reading the contracts

1. [`Environment.lean`](Environment.lean) defines the machine and memory facts shared by the
   contracts: the loaded program, input bytes, allocator state, decoder globals, result layouts, and
   the addresses a function is allowed to modify. [`Error.lean`](Error.lean) defines decoder errors.
2. [`PrimitiveReadsAndSlices.lean`](PrimitiveReadsAndSlices.lean) specifies bounded slices, integer
   reads, fixed-size byte reads, offset checks, and length checks. [`Options.lean`](Options.lean),
   [`Collections.lean`](Collections.lean), and [`Containers.lean`](Containers.lean) build on those
   operations to specify optional values, repeated values, and structured SSZ values.
3. [`Runtime.lean`](Runtime.lean) specifies the allocator and memory-copy functions used by the
   decoder. [`Entry.lean`](Entry.lean) specifies internal decoder entry functions.
   [`ExportedDecoder.lean`](ExportedDecoder.lean) specifies the public `zesu_decode_raw` function and
   the two functions that read its stored result and status.
4. [`Canonicality.lean`](Canonicality.lean) states the SSZ encoding rules enforced by the decoder,
   such as valid offsets and canonical lengths.

## Connecting contracts to the compiled binary

[`Catalog/`](Catalog/README.md) lists the source functions covered by the proof and selects the
contract for each one. [`CanonicalParams.lean`](CanonicalParams.lean) supplies the concrete memory
layout, globals, allocator, and result representations extracted from the pinned build.
[`CanonicalProgram.lean`](CanonicalProgram.lean) states the required facts about that build: its
identity, source provenance, entry point, readable instruction bytes, and function-instance
structure. [`ProgramCriteria.lean`](ProgramCriteria.lean) collects the program-wide checks used by
the composition theorem.

[`ContractComposition.lean`](ContractComposition.lean) proves the following general result. If the
compiled call graph has no cycles, and every function instance satisfies its contract whenever the
instances it calls satisfy theirs, then every function instance satisfies its contract without that
assumption. The proof proceeds from functions with no unresolved callees toward their callers; it
does not assume the entry function's conclusion in order to prove it.

## Protecting results in memory

A function may allocate memory or use its stack, so it would be false to say that it changes only
its result bytes. Instead, each contract identifies all memory owned by that call and requires its
writes to stay within that memory.

[`FrameGap.lean`](FrameGap.lean) gives a concrete counterexample showing why this is necessary: a
later child call can otherwise overwrite a result produced by an earlier child.
[`Ownership.lean`](Ownership.lean) proves that an earlier result survives when the later call writes
only within a disjoint region.
[`Footprint.lean`](Footprint.lean) identifies the bytes read by each result representation, and
[`OwnershipComposition.lean`](OwnershipComposition.lean) applies the preservation argument to a
sequence of later calls. [`RepresentationAudit.lean`](RepresentationAudit.lean) checks that the
canonical result representations depend only on memory, as those preservation proofs require.

## Checks and remaining assumptions

[`CatalogAudit.lean`](CatalogAudit.lean) checks that catalog entries are distinct, required generic
specializations are present, exclusions are explicit, and every entry selects one contract.
[`ExportedDecoderAudit.lean`](ExportedDecoderAudit.lean) checks that the public functions use the
actual C ABI registers and that their result/status behavior matches the stated model.

[`SemanticObligations.lean`](SemanticObligations.lean) proves many facts about the source-level
specifications, including which errors functions can return and exact acceptance conditions. It
also identifies the remaining specification-level assumption: agreement between the composed Zesu
decoder meaning and the pinned Ethereum SSZ specification on the decoded value.

D′ does not yet prove the machine execution of every cataloged function instance. Its public theorem
assumes the contracts for `zesu_decode_raw`, `zesu_raw_result`, and `zesu_raw_error`; later PRs replace
those assumptions with instruction-level Sail proofs.
