# Developer tools

`analyze_rv64.py` performs target-independent direct-control-flow analysis over an RV64
disassembly. Nix invokes it to produce machine-readable and Markdown reports for each retained ELF.

`generate_elfling_program.py` is the deterministic SSZ Elfling generator: it reads the byte-identical
DWARF sidecars, the pinned linker map, and an objdump of the canonical Zesu decoder, and emits the
address-bearing Elfling scaffold (`GeneratedProgram.lean`, `program.json`, `program.md`). It runs
hermetically under `nix build .#elfling-program` (two independent runs must be byte-identical), and
nothing it emits is trusted — every claim is re-checked in Lean against the canonical ELF and the
Sail-decoded control flow. The root README's "Regenerating deterministic artifacts" section lists the
full command surface.

Target-specific vector and differential checks live beside their targets under `targets/*/*/tests/`.
