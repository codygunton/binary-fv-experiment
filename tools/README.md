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

## Building proof regions from compiler and binary evidence

The hierarchical SSZ proof needs one reviewed description of the production machine code. DWARF is
useful input to that description, but it is not the authority for machine semantics.

Use DWARF for source file/line provenance, per-instruction inline stacks, distinguishing repeated
inline occurrences, and variable locations only when the location expression explicitly covers the
selected entry PC. Do not use DWARF alone to define proof-region boundaries, CFG edges or exits,
inline arguments, calling conventions, or machine contracts. In particular, an inlined source
function does not obey the RISC-V function ABI.

Complement DWARF with the production ELF's bytes, symbols, relocations, and disassembly; Sail decoding
for instruction meaning and direct successors; optimized LLVM IR plus debug metadata to explain
inlining and optimization; unoptimized LLVM IR for source-level signatures and types, used only as
provenance; production execution traces for falsification and interface discovery; and the pinned SSZ
model and differential vectors for semantic comparison.

Useful independent diagnostic tools are `llvm-dwarfdump --verify`,
`llvm-symbolizer --inlining`, `llvm-objdump`, `llvm-readelf`, QEMU instruction tracing, and a second
RISC-V semantic implementation such as Sail. Ghidra, angr, and decompilers may help investigate a
disagreement, but their inferred CFGs and types are not proof premises. Alive2 proves LLVM
transformations, not source-to-production-binary equivalence, so it does not close this project's
main gap.

### The canonical machine-region database

The missing integration artifact is a deterministic, address-keyed database with one row per
production instruction:

```text
address; encoded word; decoded instruction; operands; source location; inline stack;
selected proof-unit owner; direct successors; resolved indirect successors; basic block;
loop/SCC; entry/exit classification; static reads/writes; candidate live-in/live-out
```

Generate it from the production ELF, checked DWARF sidecars, and reviewed resolutions of indirect
transfers. Derive the curation UI, Depth inventories, Lean region definitions, tiling/CFG checks,
composition witnesses, and mutation targets from this same artifact. Each derived consumer must
reject missing rows, duplicate ownership, unresolved reachable transfers, and stale ELF or DWARF
hashes. Lean must re-check the semantic fields against the canonical ELF and Sail decoder rather
than trusting the generator.

### Six admission problems and how to solve them

1. **Exact tiling.** Store a single selected owner for every reachable instruction. Compute each
   parent's residue as its owned instructions minus selected descendants, and reject gaps,
   overlaps, instructions outside the parent, or differing ELF hashes. Use interval/set checks in
   the generator and an independent decidable partition theorem in Lean; use the existing curation
   UI to review the result.

2. **Unambiguous entry.** Derive basic blocks from the production ELF and require a selected unit to
   have one entry edge unless its contract explicitly models multiple entries. Use
   `llvm-objdump` and ELF symbols only as cross-checks; compute predecessors from the Sail-decoded
   CFG. Dominators from LLVM's standard graph algorithms or a small deterministic
   Lengauer-Tarjan implementation identify natural single-entry regions. Lean checks the chosen
   entry and all incoming edges.

3. **Complete CFG, including indirect transfers.** Sail decoding is authoritative for instruction
   classes and direct successors. Resolve jump tables, allocator vtables, and function pointers
   using ELF relocations, read-only data, and proved memory-layout facts; compare with QEMU traces,
   but never infer completeness from observed runs. Keep every unresolved reachable indirect edge
   explicit and block admission until it is resolved or represented by a sound over-approximation.

4. **Path-sensitive exits.** An exit is a feasible edge from the unit to its parent residue, not
   every call or syntactic transfer. Classify edges after call/return and indirect-target resolution,
   and preserve the edge's condition. Use dominators, post-dominators, and symbolic branch
   conditions to eliminate impossible exits; validate the classification against traces and
   mutation tests. Lean checks that every executable internal step stays inside or takes one listed
   exit.

5. **Whole-loop containment.** Run strongly connected components with a standard implementation
   such as Tarjan or Kosaraju on the resolved CFG; record each loop SCC and its entry/back/exit
   edges. Reject a selection that cuts an SCC unless it introduces an explicit loop contract.
   Natural loops use dominator back-edges where available; irreducible SCCs remain explicit.
   Prove loops symbolically with an invariant and decreasing measure rather than unrolling their
   SSZ capacity.

6. **A meaningful machine interface.** Compute conservative register/CSR/memory read-write sets
   from Sail-decoded instructions, then perform standard backwards liveness and reaching-definition
   analyses over the resolved CFG. Compare predicted live-ins/live-outs with QEMU boundary traces
   over a diverse corpus and targeted mutations. A human then states the smallest satisfiable
   machine contract; ABI names are permitted only at genuine call boundaries. Admission requires a
   concrete execution-shaped satisfiability witness, a composition theorem, and a mutation that
   makes each empirical checker fail.

The static analyses above are candidate-generation and consistency checks. The trusted path remains:
production bytes decoded in Lean, explicit reviewed region data, and kernel-checked refinement
theorems.
