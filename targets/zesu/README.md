# Zesu Amsterdam V4 SSZ

`adapter/main.c` exposes the selected repaired Zesu raw decoder as a freestanding RV64 executable.
`tests/` contains binary-specific differential, boundary, extraction, and sink-observability checks.
`docs/field-correspondence.md` freezes the mapping from Zesu's representation to the logical Amsterdam
V4 value. The reusable specification itself lives in `BinaryFv/Specs/SSZ`.

The adapter exists for QEMU execution and static measurement. The compliance proof targets the
exported `zesu_decode_raw` ABI and the exact Nix-built ELF, not stdin parsing or output formatting.
