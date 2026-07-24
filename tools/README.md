# Developer tools

`analyze_rv64.py` performs target-independent direct-control-flow analysis over an RV64
disassembly. Nix invokes it to produce machine-readable and Markdown reports for each retained ELF.

`generate_elfling_program.py` turns the compiled Zesu decoder into data for the Elfling proof layer.
It reads DWARF for occurrences and parameter locations, the linker map and symbol tables for global
addresses, and objdump output for instructions and control flow. A small explicit set of locations
removed by optimization is recovered from pinned Zig call sites or the RISC-V C ABI.

The generator emits the address-bearing program, readable reports, decoder globals, and raw and
effective parameter-binding tables. Run it through `nix build .#elfling-program`; the build runs it
twice and requires byte-identical output.

Generated output is evidence, not an axiom. Lean checks it against the pinned ELF and Sail-decoded
instructions. If DWARF omits a parameter and no narrow recovery rule applies, generation fails
instead of guessing. The root README's “Regenerating deterministic artifacts” section lists the full
command surface.

Target-specific vector and differential checks live beside their targets under `targets/*/*/tests/`.
