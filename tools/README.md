# Developer tools

[`analyze_rv64.py`](analyze_rv64.py) performs target-independent direct-control-flow analysis over an RV64
disassembly. Nix invokes it to produce machine-readable and Markdown reports for each retained ELF.

[`generate_elfling_program.py`](generate_elfling_program.py) turns the compiled Zesu decoder into
data for the Elfling proof layer. It reads DWARF for function instances and parameter locations, the linker
map and symbol tables for global addresses, and objdump output for instructions and control flow.
Locations removed by optimization are recovered only by explicit rules over pinned Zig call sites.
The RISC-V ABI applies only at real machine call boundaries, never at inlined source-function
boundaries.

The generator emits the address-bearing program, readable reports, decoder globals, and raw and
effective parameter-binding tables. The effective table is the one proof authors should use: it
contains narrow, source-checked recovery for parameters DWARF omitted, while the raw table remains
available to audit what the compiler actually reported. The output also distinguishes emitted calls
to explicitly excluded functions and records return exits separately from other ways control leaves
a function instance. Each generated Lean definition is named from its source function,
specialization, and inline call path, so proof code does not depend on an instance's position in the
generated array. Run the generator through `nix build .#elfling-program`; the build tests those names,
runs the generator twice, and requires byte-identical output.

`lean_profile.py` captures, merges and serves Lean's own profiler output when the build gets slow.
`capture` writes one Firefox Profiler JSON per module (Lean emits one per process, and Lake runs one
per module, so a build-wide profile does not exist natively); `merge` combines them into a single
profile; `serve` browses them and hands them to profiler.firefox.com. Read them with the **inverted
call stack** — nested totals are inclusive, and summing them is how you conclude that a 39 s module
contains twenty declarations of 30 s each. `AGENTS.md` has the rules this instrument produced.

Target-specific vector and differential checks live beside their targets under `targets/*/*/tests/`.

Generated output is evidence, not an axiom. Lean checks it against the pinned ELF and Sail-decoded
instructions. If DWARF omits a parameter and no narrow recovery rule applies, generation fails
instead of guessing. The root README's “Regenerating deterministic artifacts” section lists the full
command surface.

Implementation-specific vector and differential checks live under
`verification-target/<implementation>/tests/`.

## Canonical machine-region database

[`generate_machine_regions.py`](generate_machine_regions.py) is the single structural extractor for
hierarchical proof regions. The `.#machine-regions` Nix target runs it twice with pinned LLVM 21,
requires byte-identical JSON, Lean, and UI outputs, and runs its corruption tests. Its inputs are the
production ELF and `.#elfling-program`, whose DWARF sidecars are already checked against the production
bytes.

LLVM supplies disassembly and the standard structural analyses are derived in one pass:

- exact instruction ownership and unit entries/exits;
- complete direct successors with indirect transfers left explicit;
- strongly connected components and loop membership;
- conservative register/memory effects and backwards liveness;
- source locations and inline stacks inherited from checked LLVM DWARF.

The output is untrusted. Generated Lean checks instruction words and complete direct edges against the
production ELF decoded through Sail, checks exact ownership/SCC tiling, and checks SCC
strong-connectivity plus acyclic condensation certificates. QEMU remains a falsification tool for
candidate interfaces; it does not define the static database. IR/MIR may add explanatory provenance
when reproducibly tied to emitted instructions, but neither is needed for the structural artifact.

Build the reviewed UI with:

```sh
nix build .#machine-regions-ui
cd result
python3 -m http.server 8420 --bind 127.0.0.1
```

The remaining non-LLVM facts are deliberately explicit: targets loaded at runtime through vtables,
and semantic contracts describing the SSZ value computed by a region.
