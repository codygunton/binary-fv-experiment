# Binary FV Experiment

This repository keeps two RV64 measurement baselines and two selected Ethereum verification
targets:

- SHA-3 from `mjosaarinen/tiny_sha3` and DEFLATE inflate from `richgel999/miniz` remain baselines.
- The Keccak target is a freestanding C ABI around the portable RustCrypto `Keccak256` dependency
  versions locked by Reth, not a full Reth node binary.
- The SSZ target is the repaired Amsterdam V4 raw decoder at
  `codygunton/zesu@96f1621468ba54755d653f19cbc9704e789be001`; original
  `Consensys/zesu@aa6c94339987d278acb8b7fa409c864dbd3d05aa` remains its preservation baseline.

All binary artifacts are `RV64IM_Zicclsm` with `lp64` ABI and run through `qemu-riscv64`. Generated
ELFs, Lean source, traces, CFGs, and reports belong under ignored `build/` links.

## Build and evaluation

```sh
mkdir -p build
nix build .#reth-keccak --out-link build/reth-keccak
nix run .#reth-keccak -- 616263

nix build .#zesu-ssz --out-link build/zesu-ssz
nix build .#stats --out-link build/stats
```

`reth-keccak` takes one hexadecimal message. `zesu-ssz` reads raw bytes from standard input and
intentionally rejects empty input. `build/stats/stats.md` retains the uniform protocol-entry
measurements and full-composition context for all four targets.

The strict V4 SSZ gate uses the pinned Python execution-specs reference, SizzLean/Lean bridge, and
host-only Zesu formatter:

```sh
PY=/path/to/execution-specs/.venv/bin/python
nix build .#zesu-value --out-link build/zesu-ssz-value
nix build .#zesu-sink-observability --out-link build/zesu-sink-observability
(cd specs/ssz-bridge && lake build repl && lake build ssz_bridge ssz_bridge_test && lake exe ssz_bridge_test)

"$PY" -B tests/ssz_differential_audit.py \
  --reference-python "$PY" \
  --zesu-value-binary build/zesu-ssz-value/bin/zesu-ssz-value \
  --lean-binary specs/ssz-bridge/.lake/build/bin/ssz_bridge
```

`nix build .#zesu-native-suite --out-link build/zesu-native-suite` is an explicit heavyweight
preservation package. It runs both upstream and repaired-fork native/zkeVM suites; it is deliberately
not part of default `nix flake check`. The extended boundary corpus is likewise an explicit release
checkpoint:

```sh
"$PY" -B tests/ssz_boundary_audit.py --extended \
  --reference-python "$PY" \
  --zesu-value-binary build/zesu-ssz-value/bin/zesu-ssz-value \
  --lean-binary specs/ssz-bridge/.lake/build/bin/ssz_bridge
```

## Keccak binary-compliance scaffold

The proof-facing artifact is the canonical `.#reth-keccak` linked ELF. The proof build generates:

```sh
nix build .#sail-riscv-lean --out-link build/sail-riscv-lean
nix build .#reth-keccak-elf-lean --out-link build/reth-keccak-elf-lean
nix build .#keccak-spec-lean --out-link build/keccak-spec-lean
lake build repl
lake build BinaryFv
```

`BinaryFv.RISCV` contains generic bounded ELF parsing, image loading, and generated Sail support.
`BinaryFv.Keccak` owns target-specific parsed-symbol and ABI facts. No Reth address or opcode is
proof input: the parser derives `reth_keccak256` from the embedded ELF.

The frozen direct-call ABI enters that symbol with `a0 = message pointer`, `a1 = message length`,
and `a2 = 32-byte output pointer`; even an empty input has a valid message address. Successful
return requires `a0 = 0` at the sentinel and reads exactly 32 output bytes. CLI parsing and Linux
syscalls remain outside the proof-facing path.

The public target theorem is:

```lean
theorem root_compliance :
    forall msg : ByteArray,
      msg.size < RiscvSpec.maxMessageSize ->
      RiscvSpec.execute binary msg = .ok (Spec.Keccak.keccak256 msg)
```

At the scaffold checkpoint only this theorem may contain `sorry`; it hides ELF loading, direct ABI
setup, authoritative Sail execution, fuel, and output-memory extraction. The complete proof stack
must remove all proof-scope `sorry`s and custom axioms before it claims root compliance.

### Fixed-artifact trust policy

`native_decide` is permitted only for closed facts computed from pinned Nix inputs, such as parsed
ELF layout or static-inventory facts. Those facts are convenience evidence, not kernel-only proofs:
their axiom reports include Lean's native compiler trust boundary. Until a reviewed exception states
that boundary in the root claim, no theorem used by `root_compliance` may depend on a
`native_decide` fact; root-facing artifact facts must instead have kernel-checked proofs.

## Checks and CI

```sh
nix flake check
```

The default lightweight checks cover the RV64 targets, stats/ISA gates, Reth vectors, the hermetic
pinned-Lean root-library build, Lean bridge, strict core SSZ differential, and sink observability.
GitHub requires the `RV64 targets, root Lean, stats, and Reth vectors` and `SSZ bridge, core
differential, and sink` jobs for `main`; the heavyweight Zesu workflow is manually dispatched for
release checkpoints.
