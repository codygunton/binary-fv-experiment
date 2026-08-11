# Binary-regions UI

This offline D3 viewer renders generated function ownership, CFG, source-location, proof status, and
proof-authoring data. The viewer is retained, but its old grafted-`decodeRaw` dataset was removed.
It will be wired to artifacts generated from the authentic upstream Zesu ELF once that executable
adapter exists.

The UI must keep four claims distinct: machine structure, source mapping, kernel-checked proof
connection, and untrusted authoring suggestions. Nix will package fresh JSON beside this viewer;
`./serve-binary-regions-ui` remains the launcher once the new package is restored.
