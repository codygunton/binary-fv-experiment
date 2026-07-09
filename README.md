# SHA FV Experiment

This repository compares two candidate binary-verification targets:

- SHA-3 from `mjosaarinen/tiny_sha3`
- DEFLATE inflate from `richgel999/miniz`, specifically `miniz_tinfl.c`

The upstream source revisions are pinned as non-flake inputs in `flake.lock`.

## Layout

- `harness/`: local C entry points with one `main` per target.
- `include/`: local build shims, currently the generated `miniz_export.h` expected by `miniz`.
- `scripts/`: shell conveniences only.

## Build

Build SHA-3:

```sh
nix build .#sha3
```

That produces:

```text
result/bin/sha3
result/bin/sha3.aarch64
result/obj/sha3.o
result/obj/sha3.aarch64.o
```

Run SHA-3:

```sh
nix run .#sha3 -- formal-binary-probe
```

or:

```sh
./scripts/run-sha3.sh
```

`scripts/run-sha3.sh` defaults to `formal-binary-probe`; pass arguments to override it:

```sh
./scripts/run-sha3.sh hello
```

Build the stats report:

```sh
nix build .#stats
cat result/stats.md
```

The default package is `.#stats`, so this is equivalent:

```sh
nix build
```

## Objdump

For SHA-3 inspection:

```sh
nix run .#dump > sha3.objdump.txt
```

The stats build also writes:

```text
result/objdump/sha3.txt
result/objdump/tinfl.txt
```

## Stats

Current pinned Nix output:

| Target         | x86 object `.text` | x86 linked `.text` | x86 selected symbol instrs | x86 full `objdump -d` lines | x86 full instr lines | AArch64 object `.text` | AArch64 linked `.text` |
| -------------- | -----------------: | -----------------: | -------------------------: | --------------------------: | -------------------: | ---------------------: | ---------------------: |
| SHA-3 `sha3.c` |            1,152 B |            2,601 B |                        217 |                         355 |                  308 |                1,348 B |                2,280 B |
| miniz `tinfl`  |            6,619 B |            7,088 B |                      1,513 |                       1,623 |                1,592 |                6,568 B |                6,813 B |

“Selected symbol instrs” is a symbol-filtered instruction-line count. For SHA-3 it counts
`sha3_keccakf`, `sha3_init`, `sha3_update`, `sha3_final`, `sha3`, and `main`. The full
`objdump -d` columns count the entire native linked ELF, including startup/runtime sections.

## Checks

```sh
nix flake check
```

The native binaries are run as sanity checks while building. AArch64 binaries are cross-compiled for
size comparison but are not run.
