# Zesu Elflings

An Elfling connects a source-level Zesu function to the instructions that implement it in the pinned
ELF. This directory validates one generated whole-program description against the canonical binary and
the Sail-decoded control-flow graph.

The checks cover instruction identity, provenance, control-flow edges, coverage, and exact
reachability in both directions. Proofs use regions selected from this shared model; there are no
separate generated copies for individual source functions.

The underlying `GeneratedProgram` and decoder globals are produced deterministically by
`nix build .#elfling-program`. Files committed here prove properties of that generated input and must
not become a second handwritten source of binary structure.

The main checks are organized by the question they answer:

- `GeneratedProgramValidation.lean` checks that the generated inventory and the source-function
  catalog agree in both directions, that excluded functions did not enter the inventory, that source
  hashes match the pinned sources, and that every claimed instruction byte exists in the production
  ELF. Here “coverage” means inventory coverage, not execution-test coverage.
- `GeneratedProgramInstructions.lean` and `GeneratedProgramCfg.lean` check the claimed instructions,
  entries, exits, and direct transfers against the decoded binary.
- `GeneratedReachabilityExact.lean` proves that the generated reachable-address list is exactly the
  direct control-flow closure of the exported entry.
- `GeneratedProgramReachablePartition.lean` then accounts for every one of those reachable
  instructions: each belongs either to a cataloged function instance or to a named, categorized
  exclusion, never both. It does not prove that excluded code is behaviorally irrelevant; that
  remains an explicit obligation for later execution proofs.
- `GeneratedProvenanceCheck.lean` checks the source locations and hashes attached to generated
  function instances. `GeneratedValidationBridges.lean` contains the general lemmas that turn these
  concrete Boolean checks into propositions used by the rest of the library.
- `GeneratedExtentReadability.lean` proves that the loaded binary contains every instruction a
  function may execute, including instructions in functions it calls, and that none of those
  instruction addresses is the runner's stop address.
- `GeneratedReturnExits.lean` proves that the exit instructions used by the exported decoder and its
  two accessors are actual `ret` instructions. Other generated exits may be branches, calls, or the
  end of a compiled fragment, so they are not treated as returns.

This directory does not try to prove a complete nesting geometry or classify every edge by its role
in a particular composition strategy. Those are obligations of the proof decomposition that uses
them. Keeping them beside that decomposition makes their purpose and required assumptions visible.
