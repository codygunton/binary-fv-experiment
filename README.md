# SHA FV Experiment

This repository compares two preserved baseline binary-verification targets and two Ethereum
evaluation candidates:

- SHA-3 from `mjosaarinen/tiny_sha3` (baseline)
- DEFLATE inflate from `richgel999/miniz`, specifically `miniz_tinfl.c` (baseline)
- a freestanding RustCrypto Ethereum Keccak-256 wrapper traced to the pinned Reth dependency path
- Zesu's extracted freestanding raw SSZ decoder

The upstream source revisions are pinned as non-flake inputs in `flake.lock`. The measured binary
targets are `RV64IM_Zicclsm` with ABI `lp64` and run through `qemu-riscv64`; the separate
host-native `zesu-ssz-value` formatter exists only for the full-value differential and is excluded
from RV64 metrics.

## Layout

- `harness/`: local C entry points with one `main` per target.
- `include/`: local freestanding build shims used by the `miniz_tinfl.c` target.
- `scripts/`: shell conveniences only.
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
build/sha3/meta/elf-attributes.txt
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

Build the Ethereum candidates:

```sh
nix build .#reth-keccak --out-link build/reth-keccak
nix run .#reth-keccak -- 616263

nix build .#zesu-ssz --out-link build/zesu-ssz
```

`reth-keccak` accepts one hexadecimal input argument. `zesu-ssz` accepts raw bytes on standard
input; its empty-input result is intentionally `invalid` with exit status 1.

Run the pinned Zesu native and zkeVM fixture suites (production and the raw-SSZ extraction) with:

```sh
nix build .#zesu-native-suite --out-link build/zesu-native-suite
```

This evaluation-only package provides the upstream dependencies through Nix and raises only the
fixture runner's input cap for a 264.3 MiB fixture. It runs both unmodified Zesu and the explicit
candidate patch, so the fixture suite verifies preservation rather than claiming the patch is absent.

Run the value-producing SSZ evaluation gates after creating a `uv sync --locked` environment for
the pinned `ethereum/execution-specs` revision:

```sh
PY=/path/to/execution-specs/.venv/bin/python
nix build .#zesu-value --out-link build/zesu-ssz-value
nix build .#zesu-sink-observability --out-link build/zesu-sink-observability
(cd specs/ssz-bridge && lake build repl && lake build ssz_bridge ssz_bridge_test && lake exe ssz_bridge_test)

"$PY" -B tests/ssz_differential_audit.py \
  --reference-python "$PY" \
  --zesu-value-binary build/zesu-ssz-value/bin/zesu-ssz-value \
  --lean-binary specs/ssz-bridge/.lake/build/bin/ssz_bridge
"$PY" -B tests/ssz_boundary_audit.py --extended \
  --reference-python "$PY" \
  --zesu-value-binary build/zesu-ssz-value/bin/zesu-ssz-value \
  --lean-binary specs/ssz-bridge/.lake/build/bin/ssz_bridge
```

The strict gate covers Amsterdam V4 only. V3 is an explicitly quarantined legacy Zesu format with
no matching pinned full-schema oracle.

The Reth candidate deliberately evaluates the Reth-locked RustCrypto portable `Keccak256` path,
not Reth's default assembly-accelerated host binary. Its output metadata records the exact Reth
revision and verified upstream `Cargo.lock` hash.

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

## Objdump

`dump` accepts any evaluation target (and preserves `sha3` as its default):

```sh
mkdir -p build
nix run .#dump -- sha3 > build/sha3.objdump.txt
nix run .#dump -- reth-keccak > build/reth-keccak.objdump.txt
nix run .#dump -- zesu-ssz > build/zesu-ssz.objdump.txt
```

The four supported names are `sha3`, `tinfl`, `reth-keccak`, and `zesu-ssz`. For direct
inspection after a package build, substitute any target name below:

```sh
nix build .#sha3 --out-link build/sha3
nix develop -c sh -c 'riscv64-unknown-linux-gnu-objdump -d build/sha3/bin/sha3 > build/sha3.objdump.txt'
```

The stats build also writes:

```text
build/stats/objdump/sha3.txt
build/stats/objdump/tinfl.txt
build/stats/objdump/reth-keccak.txt
build/stats/objdump/zesu-ssz.txt
build/stats/objdump/zesu-ssz-parser.txt
build/stats/analysis/<target>.json
build/stats/analysis/<target>.md
```

## Stats

`build/stats/stats.md` summarizes the four linked RV64 binaries plus a separate
`zesu-ssz-parser` analysis rooted at `zesu_decode_raw`; the latter excludes the CLI and anti-DCE
sink from the decision metric. `stats.tsv` contains object and linked `.text`, legacy
selected-symbol counts, full and entry-reachable instructions, reachable functions,
protocol-owned reachable instructions, blocks, CFG edges, branches, direct calls, loop SCCs, call
depth, opcode classes, forbidden-instruction counts, objdump line counts, artifact sizes, and paths
to each complete analysis report. The individual `analysis/<target>.json` files additionally retain
function lists, ownership buckets, unresolved indirect calls, and ISA-gate details.

## Checks

```sh
nix flake check
```

The `.#stats` check runs the RISC-V binaries under `qemu-riscv64` as sanity checks.
