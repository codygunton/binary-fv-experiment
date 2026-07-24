# Zesu decoder contracts

This directory describes what each part of the compiled Zesu SSZ decoder is supposed to do. These
files are specifications and proof interfaces; they are not a second implementation of the decoder.

Start with:

1. [`Entry.lean`](Entry.lean) describes the source-level decoding pipeline and its relationship to
   the SSZ oracle.
2. [`Catalog.lean`](Catalog.lean) lists the source routines and selects the contract assigned to each
   one.
3. [`ExportedDecoder.lean`](ExportedDecoder.lean) models the public C function and its private global
   state.
4. [`CanonicalParams.lean`](CanonicalParams.lean) fixes the binary image, heap, ABI layouts, and
   memory representations used by the program-level obligation.
5. [`ProgramCorrectness.lean`](ProgramCorrectness.lean) collects the per-occurrence obligations for
   the generated program.

[ProgramCorrectness.lean](ProgramCorrectness.lean) also defines the Row D local-to-global
composition. A local occurrence proof owns its own instructions and may splice summaries for
lower-ranked children. Generated geometry and boundary checks then expand all local proofs into
closed traces. [CompositionTests.lean](CompositionTests.lean) contains small counterexamples showing
that cycles, missing summaries, bad ranks, and bad boundaries are rejected.

Most internal routines use `FunctionContract`: arguments describe source values, `meaning` gives the
expected result, and `pre`/`post` connect those values to machine state. The exported wrapper is
different. Its actual ABI is `zesu_decode_raw(input, len) -> i32`, and it communicates the decoded
value and status through private globals observed by `zesu_raw_result` and `zesu_raw_error`.

Addresses and layouts must come from the pinned ELF, linker map, DWARF, or compiler-produced ABI
manifest. [`CanonicalParams.lean`](CanonicalParams.lean) collects those checked facts so later proofs
cannot choose convenient addresses or placeholder representations.
