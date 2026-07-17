# Zesu Amsterdam V4 SSZ

`adapter/main.c` exposes the selected repaired Zesu raw decoder as a freestanding RV64 executable.
`spec/` is the SizzLean-backed Lean oracle, `tests/` contains three-way differential, boundary, and
sink-observability checks, and `docs/field-correspondence.md` freezes the full value mapping.

The adapter exists for QEMU execution and static measurement. The compliance proof targets the
exported `zesu_decode_raw` ABI and the exact Nix-built ELF, not stdin parsing or output formatting.
