# SHA FV Experiment

This repository reproduces a binary-size comparison for two candidate binary-verification targets:

- SHA-3 from `mjosaarinen/tiny_sha3`
- DEFLATE inflate from `richgel999/miniz`, specifically `miniz_tinfl.c`

The upstream source revisions are pinned as non-flake inputs in `flake.lock`. The local C harnesses
in `harness/` keep the relevant entry points reachable so section garbage collection does not erase
the code under measurement.

## Layout

- `harness/`: C harnesses linked against each implementation.
- `include/`: local build shims, currently the generated `miniz_export.h` expected by `miniz`.
- `scripts/`: shell scripts for measurement and executing the native probes.

## Reproduce

```sh
nix build .#stats
cat result/stats.md
```

or:

```sh
nix run .#stats
```

To execute the native probe binaries directly:

```sh
./scripts/run-sha3-probe.sh
./scripts/run-tinfl-probe.sh
```

To compute full native disassemblies for inspection:

```sh
nix build .#stats
nix develop -c sh -c 'objdump -d result/build/sha3_probe > sha3_probe.objdump.txt'
nix develop -c sh -c 'objdump -d result/build/tinfl_probe > tinfl_probe.objdump.txt'
```

The Nix result also includes the same files at `result/sha3_probe.objdump.txt` and
`result/tinfl_probe.objdump.txt`.

The same derivation is exposed as a check:

```sh
nix flake check
```

The derivation builds native x86-64 objects/executables and cross-compiled AArch64
objects/executables using `gcc16`, `binutils`, and `zig`, all from pinned Nixpkgs.

Current pinned Nix output:

| Target | x86 object `.text` | x86 linked `.text` | x86 selected symbol instrs | x86 full `objdump -d` lines | x86 full instr lines | AArch64 object `.text` | AArch64 linked `.text` |
|---|---:|---:|---:|---:|---:|---:|---:|
| SHA-3 `sha3.c` | 1,152 B | 2,083 B | 189 | 305 | 268 | 1,348 B | 1,843 B |
| miniz `tinfl` | 6,619 B | 7,095 B | 1,513 | 1,623 | 1,592 | 6,568 B | 6,813 B |

“Selected symbol instrs” is a symbol-filtered instruction-line count: SHA-3 counts `sha3_keccakf`,
`sha3_init`, `sha3_update`, `sha3_final`, `sha3`, and `main`; DEFLATE counts `tinfl_decompress`,
`tinfl_decompress_mem_to_mem`, and `main`. The full `objdump -d` columns count the entire native
linked ELF, including startup/runtime sections. The native object sizes, selected symbol instruction
counts, and AArch64 sizes match the initial host probe; full native linked `.text` includes the
pinned Nix C runtime/linker material, so it is slightly larger than the exploratory host-linked ELF.

## Scope

The native executables are run as a sanity check. The AArch64 executables are cross-compiled for
size comparison but are not run by the derivation.

Generated outputs, cloned exploratory repositories, and local AI coordination files are ignored by
git.
