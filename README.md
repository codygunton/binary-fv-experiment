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
nix build .#ssz-spec-lean --out-link build/ssz-spec-lean
lake build repl
lake build SszSpec BinaryFv.SSZ
```

`ssz-spec-lean` is a hash-checked source closure, not a Lake dependency: it contains just the six
pure SizzLean SSZ modules and `SszBridge/Core.lean`. The executable bridge remains a separate Lean
4.29 project and continues to own its OpenSSL-backed hash dependencies and integration tests.

### Proof-tree layers

The library is three layers, and a module's path states which one it is in. The dependency direction
is one-way:

```text
Binary  ->  RiscV  ->  Keccak.Reth
Binary  +  Spec.Keccak  ->  Keccak.SpecBridge
RiscV  +  Reth.Artifact  +  SpecBridge  ->  Reth spec-correlation proofs
RiscV  +  SszBridge  ->  SSZ
everything  ->  Keccak.Reth.Root
```

| Layer | Umbrella | Holds |
| --- | --- | --- |
| `BinaryFv/Binary/` | `BinaryFv.Binary` | Architecture-independent address ranges and the loadable program image. |
| `BinaryFv/RiscV/` | `BinaryFv.RiscV` | Everything generic over the binary under analysis: `Model` (generated-Sail state/monad, ISA init, RV64 constants), `ELF`, `Logic` (framing, separation logic, traces, loop induction), `Platform` (PMP/PMA, translation, MMIO, fetch/store environment), `Instruction/{Frame,Execute}`, `Step` (`try_step` packaging), `Execution` (loaders, sentinel runner), `Analysis` (reachability, call graph, stack flow), `Proof` (image-fetch lifting, runner correspondence). |
| `BinaryFv/Keccak/SpecBridge/` | — | Pure correspondence with `Spec.Keccak`: lane/byte serialization. No ELF address, artifact, runner, or machine state. |
| `BinaryFv/Keccak/Reth/` | `BinaryFv.Keccak` | The target. `Artifact/` is immutable data and closed static facts only — parsing, symbols, ranges, encoded words, image bytes — and depends on nothing above it; `Analysis/` holds the artifact's decoded-instruction inventory and the reachability, call-graph, and stack-flow results built on it; `Execution/` is machine configuration and executable runners; `Proof/` connects those objects to Sail semantics; `Root.lean` states `root_compliance`. |
| `BinaryFv/SSZ/` | `BinaryFv.SSZ` | Amsterdam V4 SSZ target. `SpecBridge/` normalizes the pinned SizzLean bridge to complete acceptance or rejection; Zesu artifact, analysis, execution, and proof layers follow under the same target without changing the generic RISC-V layer. |

Import the umbrellas (`BinaryFv.Binary`, `BinaryFv.RiscV`, `BinaryFv.Keccak`, `BinaryFv.SSZ`) rather
than leaf modules; `BinaryFv.lean` imports exactly those four.

Three invariants are enforced by `nix flake check`, not by convention:

* **No RISC-V module may mention Keccak or Reth** — by name, by import, or in prose. The generic
  layer is generic over the binary under analysis, and a dangling docstring reference to a deleted
  Keccak constant is as much a defect as an import, so the audit matches the bare string.
* **No RISC-V or Binary module may use `native_decide`.** The fixed-artifact exception below covers
  closed facts about the pinned ELF, which are target facts by construction.
* **Nothing under `Reth/Artifact/` may import `Execution`, `Proof`, or `Analysis`.** `Artifact/` is
  static data about the pinned image, so it must depend on nothing above it. This one greps the
  import graph rather than a keyword: the generated Sail decoder reads `cur_privilege`/`mseccfg`
  (via `currentlyEnabled Ext_Zicfilp`) before it matches an opcode, so *decoding* the artifact's
  words needs a configured machine. Decoded words are therefore not static facts, and everything
  derived from them lives in `Reth/Analysis/`, a peer of `Artifact/` rather than a child.

That last point departs from the original refactor plan, which files `Analysis/` under `Artifact/`.
The plan also requires `Artifact/` to hold no machine contract, and the two cannot both hold once the
decoder turns out to read CSRs; the boundary won, since it is the property the layering exists for.

No Reth address or opcode is proof input: the parser derives `reth_keccak256` from the embedded ELF.

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

A narrow, reviewed exception is in force for this spike. **Closed facts extracted from the pinned,
Nix-built Reth Keccak ELF may be discharged with `native_decide`, and therefore trust Lean's native
compiler.** Such facts appear in the axiom reports of the theorems that use them as
`Lean.ofReduceBool` and `Lean.trustCompiler`, including transitively in theorems reachable from
`root_compliance`. This is deliberate and approved: the ELF parser is not formalized or
kernel-evaluated in this spike.

**Scope of the exception — closed artifact facts only.** It covers exactly: artifact *identity*
(the pinned bytes are the Nix-built ELF), *layout* (parsed headers/segments/section bounds), *byte*
facts (the value at a fixed file/virtual address), and *static inventory* (symbol tables, decoded
instruction words at fixed addresses, call/stack-flow summaries). These are all decidable statements
about one fixed, immutable input.

**Outside the artifact exception.** Direct `native_decide`, new axioms, and `sorry` are *not*
permitted for: execution semantics (anything about the generated Sail `try_step`/`execute`), functional
correctness, control flow, arithmetic and bitvector reasoning, framing/separation, or specification
correspondence (`Spec.Keccak.*`). Those proofs must be checked by Lean, subject only to the separately
approved `bv_decide` certificate-checker boundary described below.

**Resulting axiom boundary.** Compliance capstones report
`[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`. There are **two
independent sources** of the two native axioms, and both must be understood:

1. **Closed artifact facts** — the `native_decide` fetch/inventory facts covered by the exception
   above.
2. **`bv_decide`** — its LRAT certificate is checked through `Lean.reduceBool`, so *any* `bv_decide`
   call that reaches the SAT backend contributes `ofReduceBool`/`trustCompiler` on its own, with no
   artifact dependency whatsoever. For example `assemble_leWord` is a pure `BitVec` identity about
   eight bytes and still carries both. (`bv_decide` goals closed by `bv_normalize` preprocessing
   alone do not.)

So removing the artifact `native_decide` facts alone would **not** clear the two native axioms from
the capstones; the `bv_decide` uses would still contribute them. Any earlier claim to the contrary in
this repo was incorrect. The maintainer accepts the native `bv_decide` certificate checker in the
trusted base for this proof-of-concept; issue #26 tracks the audit and the decision whether to retain
or remove that trust in the final project. This approval remains separate from the closed-artifact
exception above.

Theorems that use neither source (e.g. the conditional stack-window and `*_of_budget` lemmas, and the
pure framing lemmas) remain at `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`.

**The mathematical claim is unchanged.** `root_compliance`'s statement — the interface quoted above —
is not weakened by this exception; only the trust footprint of its artifact inputs is stated
explicitly.

Why the exception: kernel-evaluating the bounded ELF parser over the embedded image was measured at
>5 minutes and >100 GB RSS (OOM) on the pinned toolchain, because the parser's `Array.mapM` uses
well-founded recursion that does not reduce definitionally. Formalizing the parser is out of scope
for this spike.

## Checks and CI

```sh
nix flake check
```

The default lightweight checks cover the RV64 targets, stats/ISA gates, Reth vectors, the hermetic
pinned-Lean root-library build, Lean bridge, strict core SSZ differential, and sink observability.
GitHub requires the `RV64 targets, root Lean, stats, and Reth vectors` and `SSZ bridge, core
differential, and sink` jobs for `main`; the heavyweight Zesu workflow is manually dispatched for
release checkpoints.
