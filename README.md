# Binary FV Experiment

This repository proves properties of concrete Ethereum-related RV64 binaries against executable
Lean specifications. It retains one target:

- **Zesu Amsterdam V4 SSZ:** the repaired lossless raw decoder at
  `codygunton/zesu@96f1621468ba54755d653f19cbc9704e789be001`, with the original upstream
  revision retained as its preservation baseline.

The former Reth RustCrypto Keccak-256, tiny-SHA3, and miniz/tinfl targets are historical only and
are no longer built. Their measurements remain in
[the target evaluation](docs/evaluations/ethereum-target-evaluation.md), and the Keccak proof tree
remains in Git history.

## Repository map

This is a curated `tree -L 2`: comments describe ownership rather than every generated file.

```text
.
├── .github/
│   └── workflows/          # merge-to-main validation and manual heavyweight checks
├── BinaryFv/
│   ├── Binary/             # architecture-independent addresses and program images
│   ├── RiscV/              # reusable Sail model, ELF, execution, logic, and proof layers
│   ├── Specs/              # implementation-independent executable specifications
│   └── Zesu/               # Zesu decoder proof: artifacts, contracts, execution, and root
├── deps/                   # browsable submodules for the exact Zesu source revisions
├── docs/
│   └── evaluations/        # durable design/evaluation records; docs/ai is local and ignored
├── nix/
│   ├── targets.nix         # exact SSZ target builds
│   ├── analysis.nix        # objdump, CFG, size, and summary-statistics artifacts
│   └── proof.nix           # generated Lean inputs and hermetic root-library build
├── targets/
│   └── zesu/               # concrete adapter, ABI material, binary tests, and correspondence
├── runtime/
│   └── riscv64/            # shared freestanding startup and C runtime
├── tests/
│   └── Specs/SSZ/          # target-independent Amsterdam V4 specification tests
├── tools/
│   ├── analyze_rv64.py              # target-independent static RV64 analysis
│   ├── generate_elfling_program.py  # deterministic ELF/DWARF/CFG -> Elfling scaffold generator
│   └── ssz-oracle/                   # executable SSZ oracle tool project
├── flake.nix               # public packages, apps, checks, and pinned inputs
├── lakefile.lean           # root Lean library and generated-source inputs
└── README.md

build/                      # ignored local Nix output links and generated proof artifacts
.worktrees/                 # ignored concurrent Git worktrees
docs/ai/                    # ignored agent plans and project index
STATUS.md                   # ignored status for the active workstream
```

Each tracked top-level directory has its own README with its boundary and entry points.

Initialize the source submodules after cloning if you want to inspect Zesu locally:

```sh
git submodule update --init
```

The submodules are for source review. Nix independently fetches the same pinned revisions and remains
responsible for every build.

## Build and run

All proof-facing binaries use `RV64IM_Zicclsm`, the `lp64` ABI, and a freestanding runtime. QEMU is
only a development/conformance runner; the Lean proof enters each exported protocol ABI directly.

```sh
mkdir -p build

nix build .#zesu-ssz --out-link build/zesu-ssz
nix build .#stats --out-link build/stats
nix run .#dump -- zesu-ssz
```

`zesu-ssz` reads raw bytes from standard input and intentionally rejects empty input.
`build/stats/stats.md` reports the protocol entry and retains the full `_start` composition for
context.

## SSZ conformance

The strict V4 gate compares the pinned Python execution-specs reference, the SizzLean-backed Lean
oracle, and the host-only Zesu formatter:

```sh
PY=/path/to/execution-specs/.venv/bin/python
nix build .#zesu-value --out-link build/zesu-ssz-value
nix build .#zesu-sink-observability --out-link build/zesu-sink-observability

(
  cd tools/ssz-oracle
  lake build repl ssz_oracle ssz_oracle_test
  lake exe ssz_oracle_test
)

"$PY" -B targets/zesu/tests/ssz_differential_audit.py \
  --reference-python "$PY" \
  --zesu-value-binary build/zesu-ssz-value/bin/zesu-ssz-value \
  --lean-binary tools/ssz-oracle/.lake/build/bin/ssz_oracle
```

`nix build .#zesu-native-suite` and the extended boundary audit are explicit heavyweight release
checks, not default local checks.

## Lean proof layers

The import direction is one-way:

```text
SizzLean  ->  Specs.SSZ
Binary  ->  RiscV
Binary  +  RiscV  +  Specs.SSZ  ->  Zesu
```

`BinaryFv/RiscV/` is generic over the loaded binary; the import audit in `nix/proof.nix` enforces
that it never imports the target. `BinaryFv/Specs/SSZ/` contains the implementation-independent
executable Ethereum SSZ specification. Under `BinaryFv/Zesu/`, `Artifacts/` contains immutable
bytes, symbols, ranges, and closed static facts; `ControlFlow/` contains decode-dependent inventory;
`Contracts/` holds handwritten, address-free source-function contracts; `Elflings/` contains the
deterministically generated address-bearing model validated against the canonical ELF and
Sail-decoded control flow; and `MachineExecution/` and `Entrypoints/` configure the machine and
runner. All of it composes into `BinaryFv/Zesu/Root.lean`.

The intended public theorem remains:

```lean
theorem ssz_root_compliance :
    forall input : ByteArray,
      input.size < 2 ^ 32 ->
      RiscvSpec.execute zesuSszBinary input = .ok (BinaryFv.Specs.SSZ.decode input)
```

The canonical proof inputs are regenerated with pinned Nix derivations — see
[Regenerating deterministic artifacts](#regenerating-deterministic-artifacts).

## Regenerating deterministic artifacts

Every generated input is a pinned, hermetic Nix derivation: the same inputs produce byte-identical
output, and `nix build .#<name> --out-link build/<name>` reproduces any of them. The Elfling scaffold
and the audit LLVM IR additionally require byte-identical output across two independent runs.

Lean proof inputs (consumed by `.#binary-fv-lean`):

```sh
nix build .#sail-riscv-lean          # Sail RV64 model as Lean
nix build .#zesu-ssz-elf-lean        # Zesu SSZ decoder ELF image as Lean
nix build .#sizzlean-lean            # pinned pure SizzLean dependency closure
nix build .#zesu-abi-manifest        # compiler-reflected Zesu ABI layout
```

SSZ Elfling scaffold — deterministic ELF/DWARF/CFG -> Elfling code generation via
`tools/generate_elfling_program.py`:

```sh
nix build .#zesu-raw-ssz-sidecar     # byte-identical DWARF sidecar for the decoder .text
nix build .#zesu-ssz-runtime-sidecar # DWARF sidecar for the linked runtime
nix build .#elfling-program          # -> GeneratedProgram.lean, program.json, program.md, determinism.txt
nix build .#elfling-decoder-llvm-ir  # audit-only optimized LLVM IR (never a proof input)
```

Build the root library hermetically end to end, or incrementally during development:

```sh
nix build .#binary-fv-lean
# or:
lake build repl
lake build BinaryFv GeneratedProgram
```

Determinism, relocation, and fault-injection gates (also run by `nix flake check`):

```sh
nix build .#elfling-relocation-check         # relink at a different base; identities stay stable
nix build .#elfling-generator-defects-check  # fault-injection negative tests
```

`GeneratedProgram.lean` is not committed — `.#elfling-program` regenerates it on every build.

## Trust boundary

For this spike, closed facts extracted from the pinned Zesu ELF may use `native_decide`. This covers
artifact identity, layout, bytes at fixed addresses, symbols, decoded words, and static call/stack
summaries. It does not cover Sail execution, control flow, functional correctness, framing, or
specification correspondence.

The approved `bv_decide` certificate checker independently contributes `Lean.ofReduceBool` and
`Lean.trustCompiler` when it reaches the SAT backend. Therefore compliance capstones may report
`[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`; issue #26 tracks
that decision. The four allowlisted `sorry`s — two in `BinaryFv/Zesu/Root.lean` and two in
`BinaryFv/Zesu/Entrypoints/ZesuDecodeRaw/Execution.lean` — remain the authorized
root-compliance scaffolds and must be removed before claiming compliance.

## Validation policy

Builder and reviewer agents run Lean and Nix gates locally. Pull requests do not run the expensive
Lean build; the workflow runs after merge to `main`, and the heavyweight Zesu suite remains manually
dispatched.

```sh
nix flake check --no-build
nix build --max-jobs 1 --no-link .#binary-fv-lean
```
