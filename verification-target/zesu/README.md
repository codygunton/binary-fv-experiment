# Zesu Amsterdam V4 SSZ

`adapter/main.c` exposes the selected repaired Zesu raw decoder as a freestanding RV64 executable.
`tests/` contains binary-specific differential, boundary, extraction, and sink-observability checks.
`trace/` contains the production trace capture and classification tools plus their committed coverage
reports; it also generates the Lean occurrence evidence checked by the binary-specific test library.
`docs/field-correspondence.md` identifies which Zesu result field represents each field of the
Amsterdam V4 value, including the encoding of optional values and variable-length collections. The
Lean predicates and observers that formalize this relationship live under
`BinaryFv/Zesu/MemoryRepresentation/`. The reusable specification itself lives in
`BinaryFv/Specs/SSZ`.

The adapter exists for QEMU execution and static measurement. The compliance proof targets the
exported `zesu_decode_raw` ABI and the exact Nix-built ELF, not stdin parsing or output formatting.
