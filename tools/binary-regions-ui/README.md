# Binary-regions UI

This offline D3 viewer renders generated function ownership, CFG, source-location, proof status, and
proof-authoring data. The viewer is retained, but its old grafted-`decodeRaw` dataset was removed.
It will be wired to artifacts generated from the authentic upstream Zesu ELF once that executable
adapter exists.

The UI must keep four claims distinct: machine structure, source mapping, kernel-checked proof
connection, and untrusted authoring suggestions. Nix will package fresh JSON beside this viewer;
`./serve-binary-regions-ui` rebuilds the pinned authentic-Zesu objects and serves this retained UI on
`0.0.0.0`. The flamegraph keeps its original zoom, pan, call-hierarchy details, proof coloring, and
proof-map views. It opens on the SSZ-decode-only entrypoint; **full program** switches to the complete
Zesu `main` hierarchy. All frames start red: the new target has no kernel-backed manifest yet. Machine
structure and source lines come from the same ReleaseSmall object; EVM-Sail appears only as a future
refinement dependency, not as established correspondence. The displayed hierarchy has `main` as its
bottom frame;
the JSON retains the full-object instruction total without rendering unreachable object material.
