# Generated Zesu function instance data

This directory specializes the generic Elfling proof layer to the compiled Zesu decoder. The
generator finds every emitted and inlined routine function instance and writes Lean data for its identity,
control flow, parameter locations, and referenced globals. Handwritten Lean modules then validate
that data and expose safer definitions to the contract proofs.

The most useful entry points are:

- [`BindingInventory.lean`](BindingInventory.lean) explains where each source parameter lives at
  machine entry.
- [`GeneratedDecoderGlobals.lean`](GeneratedDecoderGlobals.lean) is handwritten validation of the
  generated decoder and allocator global-address tables.
- [`BlobScheduleFunctionInstance.lean`](BlobScheduleFunctionInstance.lean) is a generated, checked-in vertical-slice
  function instance. Its header identifies the generator and says not to edit it manually.

Do not infer editability from a `Generated` filename: some tracked `Generated*.lean` modules are
handwritten validators for generated data. Generated files identify themselves with a `GENERATED
FILE` header. The main `GeneratedElfling.lean`, `DecoderGlobals.lean`, and
`GeneratedBindings.lean` artifacts are outputs of `nix build .#elfling-program` and are not
committed. The hermetic proof build links that output at `build/elfling-program-lean/`; for a manual
build, the output is available through the Nix result link unless `--out-link` selects another path.

The raw binding table preserves DWARF exactly. A separate effective table fills locations optimized
out of DWARF using narrow, checked rules based on pinned Zig call sites or the RISC-V C ABI.
Generation fails instead of guessing when no rule applies.

FunctionInstance numbers such as `functionInstance140` are stable identifiers within the pinned generated program, not
source routine names or runtime addresses.
