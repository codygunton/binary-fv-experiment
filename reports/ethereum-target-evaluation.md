# Ethereum target evaluation decision

> **Correction — 2026-07-13.** The original “replace neither” conclusion is withdrawn. It
> treated an eventual machine-refinement proof as a Reth selection gate, measured a raw Zesu
> decoder whose result could be eliminated, and compared acceptance rather than decoded values.
> Reth passes target selection; Zesu is pending a lossless, value-level reevaluation. The old
> 724-instruction figure and acceptance-only divergences below are historical evidence, not a
> selection decision.

## Corrected interim decision

**Replace the current FIPS SHA-3 target with the Reth-locked portable RustCrypto Keccak path.**
It passed the relevant target-selection evidence: it is Ethereum Keccak-256, has reproducible
RV64IM_Zicclsm construction, passes the boundary vectors, and has a meaningful protocol-owned
reachability measurement. A complete binary-compliance proof is a later proof obligation, not a
reason to reject a candidate at selection time.

**Do not yet select or reject Zesu SSZ.** The existing raw harness only reports acceptance, its
discarded decoded value makes the 724-instruction measurement unsound, and the bridge does not
perform a full SizzLean-backed value comparison. The candidate must be repaired and remeasured
using a lossless raw schema representation and a strict Python/Lean/Zesu value differential.

This branch is isolated from `main` commit
`65d82dc7e9f56f836e5f31cd94da0f78c28b7a41`; it does not alter or stack on PR #2. **PR #2 must
not continue unchanged on the old FIPS SHA-3 target.** Its generic machine-semantics work remains
reusable, but its eventual cryptographic target should be this Reth-locked Keccak path. No Zesu
upstream issue or PR was opened.

## Reproducible inputs and candidate boundaries

| Role | Pinned source |
|---|---|
| Reth provenance | `paradigmxyz/reth@9384bc53d8c0c77e59cac83fdaaf3b372c6d2216` |
| Zesu | `Consensys/zesu@aa6c94339987d278acb8b7fa409c864dbd3d05aa` |
| Keccak Lean oracle | `trailofbits/scroll-fv@0c3927ba4d6773b4cfd1d949cba342268b104d91` |
| SSZ theorem library audit | `etheorem/etheorem@032ab6c6d67186ba60b734e0f2c44ba1bb8b6fb0` |
| V4 execution-spec reference | `ethereum/execution-specs@bd8c673552d957dbe9c9f3f2656b87201f5ae646` |

All compared ELFs use `RV64IM_Zicclsm` and `lp64`; the checked toolchain is GCC 15.2.0,
binutils 2.46, and qemu-riscv64 11.0.1.  The Nix build verifies the full Reth lockfile hash
(`39867b4a9bae8c97872ce4f51ae184c13ba3db2c57b9c6772e31e83711866b97`).

`reth-keccak` is deliberately a freestanding C ABI around the Reth-locked RustCrypto
`sha3::Keccak256` dependency path (`sha3 0.11.0`, `keccak 0.2.0`) with its portable software
backend.  It is **not** a complete Reth node or Reth's default assembly-accelerated host binary.
The six independent Ethereum Keccak vectors at lengths 0, 1, 135, 136, 137, and 200 pass; the
136-byte boundary distinguishes Ethereum Keccak padding from FIPS SHA3-256.

`zesu-ssz` is a local patch extraction of `decodeRaw`, before the unchanged transaction-RLP
conversion in Zesu's production `decode`.  It exposes only raw-SSZ accept/reject through a small
freestanding harness, so it is not value-level equivalence evidence for the production decoder.
The separately built unmodified Zesu object retains its crypto/precompile dependencies.  The raw
object has only `ZKVM_HEAP_POS`, `ZKVM_HEAP_TOP`, and `memcpy` unresolved; the linked
`zesu-ssz` candidate's direct-reachability analysis finds no hash/cryptographic implementation.

## RV64 measurements

Measurements come from `nix build .#stats --out-link build/stats`; linked analysis starts at
`_start`.  “Protocol” is reachable code attributed by documented symbol ownership rules, rather
than a source-level component boundary.

| Target | Object / linked `.text` | Full / reachable instr. | Protocol | Funcs | Blocks / CFG edges | Cond. branches | Calls | Loop SCCs | Call depth | Opcode classes | Objdump lines (all / instr.) | ISA |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|---|---:|---|
| `sha3` | 1,540 / 1,680 B | 312 / 312 | 234 | 9 | 62 / 84 | 18 | 12 | 9 | 6 | I/system 308, M 4 | 335 / 312 | pass |
| `tinfl` | 6,418 / 6,397 B | 1,481 / 1,387 | 1,344 | 6 | 345 / 520 | 168 | 12 | 8 | 5 | I/system 1,383, M 4 | 1,498 / 1,481 | pass |
| `reth-keccak` | 128,504 / 3,424 B | 796 / 796 | 623 | 14 | 102 / 159 | 38 | 29 | 15 | 7 | I/system 793, M 3 | 829 / 796 | pass |
| `zesu-ssz` | 5,444 / 5,744 B | 1,309 / 901 | 724 | 5 | 142 / 235 | 83 | 19 | 8 | recursive | I/system 897, M 4 | 1,324 / 1,309 | pass |

The legacy selected-symbol counts remain 286 for SHA-3 and 1,457 for miniz.  Reth's 228 is its
legacy selected-symbol count in the linked ELF, not an archive-wide metric; the fairer
cross-language comparison is its 623 protocol-owned reachable instructions, which exceeds the
286-instruction SHA baseline.  Zesu's direct-reachable ownership split is protocol 724, harness
50, runtime 17, and Zig runtime 110 instructions.  Parser and allocator behavior is inlined into
`zesu_decode_raw`, so the analyzer cannot separately attribute those source components.  Complete
maps, symbol tables, objdumps, ownership buckets, and analyzer JSON remain reproducible under
ignored `build/stats/`.  Reth has one unresolved indirect-call block (`0x10cec`), so reachability
and ISA claims below are scoped to the analyzer's direct control-flow graph.

| Gate | Result | Evidence |
|---|---|---|
| RV64IM_Zicclsm only | pass (direct-reachability analysis) | No forbidden instruction in the analyzer's direct-reachability set. |
| Reth is Ethereum Keccak and no smaller than the SHA target | pass for selection evidence | Portable `Keccak256`, six boundary vectors, 623 protocol-reachable instructions. |
| Raw SSZ excludes crypto | pass | Raw object/link graph excludes crypto; full production object is retained separately for attribution. |
| SSZ protocol size in `[0.75, 3] × 1,457` | **fail** | 724 is below the 1,092.75 lower bound. |
| SSZ reaches/exceeds miniz on two of blocks, edges, SCCs, funcs | **fail** | It only ties loop SCCs (8); 142 < 345 blocks, 235 < 520 edges, and 5 < 6 functions. |
| SSZ has relevant semantic structure | pass as exercised, not as conformance | Corpus exercises nested containers, offset tables, bounded lists, allocation, loops, and malformed exits. |

## Formal and differential audit

The pinned Scroll-FV Keccak module built with Lean 4.29.1 (`lake build
Spec.Keccak.Keccak256`).  It is an executable Ethereum Keccak-256 oracle (rate 136, suffix
`0x01`, 32-byte digest), and agrees with all six Reth vectors.  For the audited
`Spec.Keccak.keccak256` dependency footprint, `#print axioms` reports only `propext` and
`Quot.sound`; this is useful oracle evidence, not a refinement proof from RustCrypto machine code.

The pinned SizzLean package and its focused tests built with its own Lean 4.29.1 toolchain
(`lake build SizzLean SizzLeanTests`).  This focused command did not invoke an external
`consensus-spec-tests` harness, so this evaluation makes no current consensus-vector claim.
`#print axioms` reports that `decode_encode` and `serialize_injective` depend on `propext`,
`Classical.choice`, `Quot.sound`, and the three native axioms
`SizzLean.Proofs.decode_encode_uintN16._native.bv_decide.ax_1_6`,
`SizzLean.Proofs.decode_encode_uintN32._native.bv_decide.ax_1_6`, and
`SizzLean.Proofs.decode_encode_uintN64._native.bv_decide.ax_1_6`; `encode_size_le_max` depends
only on `propext` and `Quot.sound`.  Its SHA-256 FFI declarations are separate explicit axioms.
More importantly, its `BasicSupported` proof coverage excludes mixed/nested variable-size offset
containers needed by `SszStatelessInput`, so its existing theorem coverage cannot establish this
schema's decoder correctness.

`specs/ssz-bridge/` is therefore an axiom-free, executable-only Lean normalization bridge.  It
checks schema `0x0001`, optional Ere framing, V3/V4 dispatch, nested canonical offsets, relevant
bounds, witnesses, chain configuration, public keys, and raw transaction lists.  It emits
normalization metadata rather than a full decoded value; the Zesu raw ABI only returns
accept/reject.  The pinned Python reference independently checks V4 Amsterdam inputs only;
V3 cases below are structural-only until a matching historical Python oracle is pinned.

The corpus runner in `tests/ssz_differential_audit.py` compared the Lean bridge, Python V4
reference, and the RV64 extracted raw-SSZ candidate.  They agree on the two valid raw V4 cases
and reject eight shared malformed V4 cases (schema ID, truncation, three top-level offset errors,
two transaction table errors, and fixed-element divisibility).  Lean and the extracted candidate
also agree on valid V4 Ere and V3 raw/Ere structural cases; Python is intentionally not queried
for those.

The strict run reports seven divergences, so the decoder gate fails:

| Cases | Lean / Python | Extracted raw-SSZ candidate |
|---|---|---|
| `oversized-extra-data-33`; `too-many-withdrawals-17`; `too-many-versioned-hashes-4097`; `malformed-deposit-fixed-size`; `unknown-fork-index`; `noncanonical-npr-first-offset` | reject | accepts |
| `ere-heuristic-collision-raw` (a valid 1,048,836-byte raw input whose first word equals `size - 4`) | accepts | rejects |

The companion correctly framed collision input is accepted by Lean and the extracted candidate;
it isolates the raw/Ere framing heuristic rather than a general size limitation.

## Native-suite verification

`nix build .#zesu-native-suite --out-link build/zesu-native-suite` passed.  It runs `zig build
test` and `zig build zkevm-tests` twice: first on the pinned production decoder, then on a fresh
copy with the raw-SSZ patch applied by `patch --fuzz=0`.  The latter proves the preserved production
`decode` wrapper still builds and passes the full native and pinned zkeVM fixture suites after
`decodeRaw` extraction.

The Nix package supplies upstream's assumed `/usr/local` crypto dependencies from pinned
derivations, including `herumi/mcl@0499298adcfad3bbcebf77f17700ebbe97166060`
(`sha256-Nyd8SyURTpExgvB2B/uEfhEBU7YLQgNY6s1saQ1rS1Y=`), and changes only the fixture runner's
file cap from 256 MiB to 512 MiB; the pinned fixture archive
(`sha256-a1/W3qd8xepR39w1sDvcpBh1km4XrSbz6+v5hBA4o2Y=`) contains a 264.3 MiB JSON fixture.  These
adaptations do not change decoder behavior.  The raw RV64 object is separately built by
`.#zesuRawObject`; its linked harness is the candidate measured and compared above.

## Retained future theorem shape

The following is intentionally a proposed target for a separate proof plan, not a theorem
established here:

```lean
theorem keccak_root_compliance :
    forall msg : ByteArray,
      RethKeccak.execute keccakBinary msg = .ok (KeccakSpec.hash msg)

theorem ssz_root_compliance :
    forall input : ByteArray,
      input.size < 2^32 ->
      ZesuSsz.execute sszBinary input = .ok (SszSpec.decodeStatelessInput input)
```

`decodeStatelessInput` would return `Except SszError RawStatelessInput`; outer `.ok` would state
machine execution terminates without trapping.  Neither statement follows from this evaluation:
the Keccak work lacks the machine-refinement proof, and the SSZ statement is contradicted by the
observed corpus divergences.
