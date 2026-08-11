# Zesu Amsterdam V4 SSZ

The decoder source is browsable in the [`deps/zesu`](../../deps/zesu) submodule, pinned to
`codygunton/zesu@96f1621468ba54755d653f19cbc9704e789be001`. The unchanged comparison baseline is in
[`deps/zesu-upstream`](../../deps/zesu-upstream), pinned to
`Consensys/zesu@aa6c94339987d278acb8b7fa409c864dbd3d05aa`. These working copies are for inspection;
the Nix inputs independently pin and build the same revisions.

`adapter/main.c` exposes the selected repaired Zesu raw decoder as a freestanding RV64 executable.
`tests/` contains binary-specific differential, boundary, extraction, and sink-observability checks.
`trace/` contains the production trace capture and classification tools plus their committed coverage
reports; it also generates the Lean occurrence evidence checked by the binary-specific test library.
`docs/field-correspondence.md` identifies which Zesu result field represents each field of the
Amsterdam V4 value, including the encoding of optional values and variable-length collections. The
Lean predicates and observers that formalize this relationship live under
`BinaryFv/Zesu/DecodedValue/`. The reusable specification itself lives in
`BinaryFv/Specs/SSZ`.

The adapter exists for QEMU execution and static measurement. The compliance proof targets the
exported `zesu_decode_raw` ABI and the exact Nix-built ELF, not stdin parsing or output formatting.
