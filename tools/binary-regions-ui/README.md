# Binary-regions UI

This offline D3 viewer renders generated function ownership, CFG, source locations, proof status,
and proof-authoring data for the production SSZ endpoint ELF.

The UI must keep four claims distinct: machine structure, source mapping, kernel-checked proof
connection, and untrusted authoring suggestions. Nix packages fresh JSON beside this viewer;
`./serve-binary-regions-ui` rebuilds the pinned Zesu objects and serves the UI on
`0.0.0.0`. The flamegraph keeps its original zoom, pan, call-hierarchy details, proof coloring, and
proof-map views. It opens on the SSZ-decode-only entrypoint; **full program** switches to the complete
Zesu `main` hierarchy. Machine structure and source lines come from the same ReleaseSmall object;
the generated proof map supplies current proof colors.

The left rail is **call depth**, which is contiguous and matches the flamegraph's physical rows.
Proof refinement level follows actual call and inlining edges and can differ for shared emitted
functions; clicking a frame reports both values. For example, `memcpy` is displayed once at call
depth 1 because many descendants share the emitted body, but it is proof Level 2 and is not one of
the six assumptions in `Level1ContractAssumptions`.
