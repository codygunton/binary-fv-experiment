# SHA FV Experiment

This repository compares two candidate binary-verification targets:

- SHA-3 from `mjosaarinen/tiny_sha3`
- DEFLATE inflate from `richgel999/miniz`, specifically `miniz_tinfl.c`

The upstream source revisions are pinned as non-flake inputs in `flake.lock`. The only binary
target built by this repo is `RV64IM_Zicclsm` with ABI `lp64`; execution goes through
`qemu-riscv64`.

## Layout

- `harness/`: local C entry points with one `main` per target.
- `include/`: local freestanding build shims used by the `miniz_tinfl.c` target.
- `scripts/`: shell conveniences only.
- `specs/`: pinned Lean spec repositories, checked in as git submodules.
- `ShaFv/`: local Lean proof scaffold.
- `build/`: ignored local output links and generated inspection files.

## Build

Use explicit output links under `build/` for local build artifacts.

Build SHA-3:

```sh
mkdir -p build
nix build .#sha3 --out-link build/sha3
```

That produces:

```text
build/sha3/bin/sha3
build/sha3/obj/sha3.o
build/sha3/obj/sha3-main.o
build/sha3/obj/riscv64_start.o
build/sha3/obj/riscv64_runtime.o
build/sha3/meta/elf-sha256.txt
build/sha3/meta/entrypoint.txt
build/sha3/meta/elf-attributes.txt
build/sha3/meta/program-headers.txt
build/sha3/meta/symbols.txt
```

`build/sha3/bin/sha3` is a RISC-V ELF, not a host executable. Run SHA-3 through the Nix app:

```sh
nix run .#sha3 -- sha3-sample-message
```

or:

```sh
./scripts/run-sha3.sh
```

`scripts/run-sha3.sh` supplies `sha3-sample-message` when no message is passed. That value is only
the default message to hash; pass one argument to hash a different string:

```sh
./scripts/run-sha3.sh hello
```

Build and run the DEFLATE target:

```sh
mkdir -p build
nix build .#tinfl --out-link build/tinfl
nix run .#tinfl
```

The dev shell contains the RISC-V compiler/binutils and qemu-user:

```sh
nix develop
riscv64-unknown-linux-gnu-gcc --version
qemu-riscv64 --version
```

Build the stats report:

```sh
nix build .#stats --out-link build/stats
cat build/stats/stats.md
```

The default package is `.#stats`, so this is equivalent while still keeping the local link in
`build/`:

```sh
nix build --out-link build/stats
```

## Lean

Initialize the spec submodules after cloning:

```sh
git submodule update --init --recursive
```

The SHA-3 scaffold imports `gdncc/Cryptography` and states:

```lean
theorem root_compliance :
    ∀ msg : ByteArray,
      Bin.main msg = Spec.exec msg
```

`Bin.main` is the proof boundary intended to denote the behavior of the one fixed SHA-3 ELF built by
this repository. ELF identity, loading, process setup, and RISC-V execution belong behind that
definition rather than appearing as arguments to the root theorem. The proof is intentionally
stubbed with `sorry`.

Generate the pinned executable Lean translation of the Sail RISC-V model first:

```sh
mkdir -p build
nix build .#sail-riscv-lean --out-link build/sail-riscv-lean
```

Then build the local proof scaffold and generated machine semantics:

```sh
nix develop
lake build ShaFv
```

This generation target uses `riscv/sail-riscv` 0.12 and the REMS Sail compiler 0.20.1 from the
locked Nixpkgs revision. It selects the `main`, `I_insts`, and `M_insts` Sail module roots, retains
the core Zicclsm memory semantics, and disables upstream CMake's configure-time dependency
downloads. The generated model is compiled into the root project's `.lake/build`.

`ShaFv.RISCV.entryInstructionCorrect_eq_true` is a closed theorem that executes the known first
instruction at ELF entrypoint `0x101b8` and checks `gp = 0x121b8` and `PC = 0x101bc`. It does not yet
prove that the manually loaded opcode came from the hashed ELF; that requires the pending ELF loader
lemma before it can contribute to `root_compliance`.

`kim-em/lean-zip` is vendored under `specs/deflate` for the DEFLATE spec, but is not imported by
the root Lake package yet because it currently pins a newer Lean toolchain than `gdncc/Cryptography`.

## Objdump

For SHA-3 inspection:

```sh
mkdir -p build
nix run .#dump > build/sha3.objdump.txt
```

For direct inspection of either target after a package build:

```sh
nix build .#sha3 --out-link build/sha3
nix develop -c sh -c 'riscv64-unknown-linux-gnu-objdump -d build/sha3/bin/sha3 > build/sha3.objdump.txt'
nix build .#tinfl --out-link build/tinfl
nix develop -c sh -c 'riscv64-unknown-linux-gnu-objdump -d build/tinfl/bin/tinfl > build/tinfl.objdump.txt'
```

The stats build also writes:

```text
build/stats/objdump/sha3.txt
build/stats/objdump/tinfl.txt
```

## Stats

Current pinned Nix output:

| Target         | RV64 object `.text` | RV64 linked `.text` | RV64 selected symbol instrs | RV64 full `objdump -d` lines | RV64 full instr lines |
| -------------- | ------------------: | ------------------: | --------------------------: | ---------------------------: | --------------------: |
| SHA-3 `sha3.c` |             1,540 B |             1,680 B |                         286 |                          335 |                   312 |
| miniz `tinfl`  |             6,418 B |             6,397 B |                       1,457 |                        1,498 |                 1,481 |

“Selected symbol instrs” is a symbol-filtered instruction-line count. For SHA-3 it counts
`sha3_keccakf`, `sha3_init`, `sha3_update`, `sha3_final`, `sha3`, and `main`. The full
`objdump -d` columns count each entire linked RISC-V ELF, including the local freestanding
startup/runtime sections.

## Checks

```sh
nix flake check
```

The `.#stats` check runs the RISC-V binaries under `qemu-riscv64` as sanity checks.
