# SHA FV Experiment

This repository reproduces a binary-size comparison for two candidate binary-verification targets:

- SHA-3 from `mjosaarinen/tiny_sha3`
- DEFLATE inflate from `richgel999/miniz`, specifically `miniz_tinfl.c`

The upstream source revisions are pinned as non-flake inputs in `flake.lock`. The local harnesses in
`scripts/` keep the relevant entry points reachable so section garbage collection does not erase the
code under measurement.

## Reproduce

```sh
nix build .#stats
cat result/stats.md
```

or:

```sh
nix run .#stats
```

The same derivation is exposed as a check:

```sh
nix flake check
```

The derivation builds native x86-64 objects/executables and cross-compiled AArch64
objects/executables using `gcc16`, `binutils`, and `zig`, all from pinned Nixpkgs.

Current pinned Nix output:

| Target | x86 object `.text` | x86 linked `.text` | x86 selected instrs | AArch64 object `.text` | AArch64 linked `.text` |
|---|---:|---:|---:|---:|---:|
| SHA-3 `sha3.c` | 1,152 B | 2,083 B | 189 | 1,348 B | 1,843 B |
| miniz `tinfl` | 6,619 B | 7,095 B | 1,513 | 6,568 B | 6,813 B |

The native object sizes, selected implementation instruction counts, and AArch64 sizes match the
initial host probe. Full native linked `.text` includes the pinned Nix C runtime/linker material, so
it is slightly larger than the exploratory host-linked ELF.

## Scope

The native executables are run as a sanity check. The AArch64 executables are cross-compiled for
size comparison but are not run by the derivation.

Generated outputs, cloned exploratory repositories, and local AI coordination files are ignored by
git.
