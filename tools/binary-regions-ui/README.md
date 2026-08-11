# Binary-regions UI

This offline D3 viewer renders generated function ownership, CFG, source-location, proof status, and
proof-authoring data. The viewer is retained, but its old grafted-`decodeRaw` dataset was removed.
It will be wired to artifacts generated from the authentic upstream Zesu ELF once that executable
adapter exists.

The UI must keep four claims distinct: machine structure, source mapping, kernel-checked proof
connection, and untrusted authoring suggestions. Nix will package fresh JSON beside this viewer;
`./serve-binary-regions-ui` rebuilds the pinned authentic-Zesu object and serves this retained UI on
`0.0.0.0`. The flamegraph keeps its original zoom, pan, call-hierarchy details, proof coloring, and
proof-map views. All frames start red: the new target has no kernel-backed manifest yet. Machine
structure and source lines come from the same ReleaseSmall object; EVM-Sail appears only as a future
refinement dependency, not as established correspondence.
