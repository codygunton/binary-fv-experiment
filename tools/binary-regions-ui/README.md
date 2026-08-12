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
Every static callsite gets its own displayed instance, even when multiple callers invoke the same
emitted function body. Clicking a frame reports that invocation's callsite and return PC. Proof
status first keys the callsite instance; a body-level theorem such as `memcpyInstanceContract` is
shown as reusable machine work, not as evidence that every caller-specific composition is complete.
