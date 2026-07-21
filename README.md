# Binary FV Experiment

This repository proves properties of concrete Ethereum-related RV64 binaries against executable
Lean specifications. It retains two targets:

- **Reth RustCrypto Keccak-256:** a freestanding C ABI around the portable `Keccak256` dependency
  versions locked by Reth.
- **Zesu Amsterdam V4 SSZ:** the repaired lossless raw decoder at
  `codygunton/zesu@96f1621468ba54755d653f19cbc9704e789be001`, with the original upstream
  revision retained as its preservation baseline.

The former tiny-SHA3 and miniz/tinfl measurement baselines are historical only and are no longer
built. Their results remain in [the target evaluation](docs/evaluations/ethereum-target-evaluation.md).

## Repository map

This is a curated `tree -L 2`: comments describe ownership rather than every generated file.

```text
.
├── .github/
│   └── workflows/          # merge-to-main validation and manual heavyweight checks
├── BinaryFv/
│   ├── Binary/             # architecture-independent addresses and program images
│   ├── RiscV/              # reusable Sail model, ELF, execution, logic, and proof layers
│   ├── Keccak/             # Keccak spec bridge and the Reth-specific compliance proof
│   └── SSZ/                # Zesu SSZ decoder proof: contracts, deterministic Elfling scaffold, root
├── docs/
│   └── evaluations/        # durable design/evaluation records; docs/ai is local and ignored
├── nix/
│   ├── targets.nix         # exact Keccak and SSZ target builds
│   ├── analysis.nix        # objdump, CFG, size, and target-comparison artifacts
│   └── proof.nix           # generated Lean inputs and hermetic root-library build
├── targets/
│   ├── common/             # shared freestanding RV64 startup and runtime
│   ├── keccak/             # exact Reth wrapper, ABI adapter, and adjacent vector tests
│   └── ssz/                # exact Zesu adapter, Lean bridge, audits, and correspondence
├── tools/
│   ├── analyze_rv64.py              # target-independent static RV64 analysis
│   └── generate_elfling_program.py  # deterministic ELF/DWARF/CFG -> Elfling scaffold generator
├── flake.nix               # public packages, apps, checks, and pinned inputs
├── lakefile.lean           # root Lean library and generated-source inputs
└── README.md

build/                      # ignored local Nix output links and generated proof artifacts
.worktrees/                 # ignored concurrent Git worktrees
docs/ai/                    # ignored agent plans and project index
STATUS.md                   # ignored status for the active workstream
```

Each tracked top-level directory has its own README with its boundary and entry points.

## Build and run

All proof-facing binaries use `RV64IM_Zicclsm`, the `lp64` ABI, and a freestanding runtime. QEMU is
only a development/conformance runner; the Lean proof enters each exported protocol ABI directly.

```sh
mkdir -p build

nix build .#reth-keccak --out-link build/reth-keccak
nix run .#reth-keccak -- 616263

nix build .#zesu-ssz --out-link build/zesu-ssz
nix build .#stats --out-link build/stats
nix run .#dump -- reth-keccak
nix run .#dump -- zesu-ssz
```

`reth-keccak` accepts one hexadecimal message. `zesu-ssz` reads raw bytes from standard input and
intentionally rejects empty input. `build/stats/stats.md` compares both protocol entries and retains
their full `_start` compositions for context.

## SSZ conformance

The strict V4 gate compares the pinned Python execution-specs reference, the SizzLean-backed Lean
bridge, and the host-only Zesu formatter:

```sh
PY=/path/to/execution-specs/.venv/bin/python
nix build .#zesu-value --out-link build/zesu-ssz-value
nix build .#zesu-sink-observability --out-link build/zesu-sink-observability

(
  cd targets/ssz/zesu/spec
  lake build repl ssz_bridge ssz_bridge_test
  lake exe ssz_bridge_test
)

"$PY" -B targets/ssz/zesu/tests/ssz_differential_audit.py \
  --reference-python "$PY" \
  --zesu-value-binary build/zesu-ssz-value/bin/zesu-ssz-value \
  --lean-binary targets/ssz/zesu/spec/.lake/build/bin/ssz_bridge
```

`nix build .#zesu-native-suite` and the extended boundary audit are explicit heavyweight release
checks, not default local checks.

## Lean proof layers

The import direction is one-way:

```text
Binary  ->  RiscV  ->  Keccak.Reth
Binary  +  Spec.Keccak  ->  Keccak.SpecBridge
RiscV  +  Reth.Artifact  +  SpecBridge  ->  Reth correlation proofs
everything  ->  Keccak.Reth.Root
```

`BinaryFv/RiscV/` is generic over the loaded binary. `BinaryFv/Keccak/SpecBridge/` contains only pure
lane/byte correspondence. Under `BinaryFv/Keccak/Reth/`, `Artifact/` contains immutable bytes,
symbols, ranges, and closed static facts; `Analysis/` contains decode-dependent inventory;
`Execution/` configures the machine and runner; `Proof/` connects those objects to generated Sail
semantics.

The generated Sail decoder reads machine CSRs while checking enabled extensions, so decoded
instructions are deliberately in `Reth/Analysis/`, not static `Reth/Artifact/` data.

The intended public theorem remains:

```lean
theorem root_compliance :
    forall msg : ByteArray,
      msg.size < RiscvSpec.maxMessageSize ->
      RiscvSpec.execute binary msg = .ok (Spec.Keccak.keccak256 msg)
```

The Zesu SSZ target has a parallel structure under `BinaryFv/SSZ/`: handwritten, address-free
per-routine contracts (`Zesu/Contracts/`), the deterministically generated address-bearing Elfling
scaffold validated against the canonical ELF and Sail-decoded control flow (`Zesu/Elfling/`),
composed into `BinaryFv/SSZ/Root.lean`.

The canonical proof inputs for both targets are regenerated with pinned Nix derivations — see
[Regenerating deterministic artifacts](#regenerating-deterministic-artifacts).

## Regenerating deterministic artifacts

Every generated input is a pinned, hermetic Nix derivation: the same inputs produce byte-identical
output, and `nix build .#<name> --out-link build/<name>` reproduces any of them. The Elfling scaffold
and the audit LLVM IR additionally require byte-identical output across two independent runs.

Lean proof inputs (consumed by `.#binary-fv-lean`):

```sh
nix build .#sail-riscv-lean          # Sail RV64 model as Lean (shared by both targets)
nix build .#reth-keccak-elf-lean     # Reth Keccak ELF image as Lean
nix build .#keccak-spec-lean         # Keccak specification as Lean
nix build .#zesu-ssz-elf-lean        # Zesu SSZ decoder ELF image as Lean
nix build .#ssz-spec-lean            # SizzLean SSZ bridge specification as Lean
nix build .#zesu-abi-manifest        # compiler-reflected Zesu ABI layout
```

SSZ Elfling scaffold — deterministic ELF/DWARF/CFG -> Elfling code generation via
`tools/generate_elfling_program.py`:

```sh
nix build .#zesu-raw-ssz-sidecar     # byte-identical DWARF sidecar for the decoder .text
nix build .#zesu-ssz-runtime-sidecar # DWARF sidecar for the linked runtime
nix build .#elfling-program          # -> GeneratedProgram.lean, program.json, program.md, determinism.txt
nix build .#blob-schedule-instance   # -> BlobScheduleInstance.lean (regenerated + verified vs committed)
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
`BlobScheduleInstance.lean` is committed; `.#blob-schedule-instance` regenerates it and fails the
build unless the regenerated file is byte-identical to the committed copy (a drift guard).

## Trust boundary

For this spike, closed facts extracted from the pinned Reth ELF may use `native_decide`. This covers
artifact identity, layout, bytes at fixed addresses, symbols, decoded words, and static call/stack
summaries. It does not cover Sail execution, control flow, functional correctness, framing, or
specification correspondence.

The approved `bv_decide` certificate checker independently contributes `Lean.ofReduceBool` and
`Lean.trustCompiler` when it reaches the SAT backend. Therefore compliance capstones may report
`[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`; issue #26 tracks
that decision. The single `sorry` in `BinaryFv/Keccak/Reth/Root.lean` remains the authorized
root-compliance scaffold and must be removed before claiming compliance.

## Validation policy

Builder and reviewer agents run Lean and Nix gates locally. Pull requests do not run the expensive
Lean build; the workflow runs after merge to `main`, and the heavyweight Zesu suite remains manually
dispatched.

```sh
nix flake check --no-build
nix build --max-jobs 1 --no-link .#binary-fv-lean
```
