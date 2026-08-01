# Zesu Elflings

An Elfling connects a source-level Zesu function to the instructions that implement it in the pinned
ELF. This directory validates one generated whole-program description against the canonical binary and
the Sail-decoded control-flow graph.

The checks cover instruction identity, provenance, control-flow edges, nesting, coverage, and exact
reachability in both directions. Proofs use regions selected from this shared model; there are no
separate generated copies for individual routines.

The underlying `GeneratedProgram` and decoder globals are produced deterministically by
`nix build .#elfling-program`. Files committed here prove properties of that generated input and must
not become a second handwritten source of binary structure.
