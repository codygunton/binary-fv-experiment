# Generated Zesu occurrence data

This directory specializes the generic Elfling proof layer to the compiled Zesu decoder. The
generator finds every emitted and inlined routine occurrence and writes Lean data for its identity,
control flow, parameter locations, and referenced globals. Handwritten Lean modules then validate
that data and expose safer definitions to the contract proofs.

The most useful entry points are:

- `BindingInventory.lean`: explains where each source parameter lives at machine entry.
- `GeneratedDecoderGlobals.lean`: validates the addresses and sizes of decoder and allocator globals.
- `BlobScheduleInstance.lean`: a small generated occurrence used as an end-to-end example.

Files named `Generated*.lean` are build products and should not be edited by hand. The raw binding
table preserves DWARF exactly. A separate effective table fills the few locations optimized out of
DWARF using narrow, checked rules based on pinned Zig call sites or the RISC-V C ABI. Generation
fails instead of guessing when no rule applies.

Occurrence numbers such as `occ140` are stable identifiers within the pinned generated program, not
source routine names or runtime addresses.

Row D adds three checked views of this program:

- `GeneratedProgramGeometry.lean` proves the call/inline graph is ranked and its address extents fit.
- `GeneratedBoundaryInventory.lean` accounts for every direct successor and the three indirect
  allocator-vtable calls.
- `ManifestCheck.lean` proves the human proof backlog has exactly one accurate row per occurrence.
