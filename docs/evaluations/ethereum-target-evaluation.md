# Ethereum target evaluation decision

> **Foundation decision — 2026-07-14.** Select both the Reth-lockfile RustCrypto portable
> Keccak-256 path and the repaired Amsterdam V4 Zesu raw-SSZ decoder. The original upstream Zesu
> revision remains pinned as the production-preservation baseline; the selected decoder is the
> exact `codygunton/zesu` repair commit. The former two-of-four parser-only structural comparison
> remains reported, but is retired as a hard selection gate: Zig inlining determines its function
> count and the CFG-edge result differs from miniz by one.

The former “replace neither” decision is superseded. Its 724-instruction Zesu result measured an
accept/reject extraction whose decoded result could be dead-code eliminated, and its differential
compared acceptance rather than decoded values. Neither is used as decision evidence below.

## Decision

**Reth Keccak is selected.** The artifact is a freestanding RV64IM_Zicclsm C ABI around the
portable `Keccak256` implementation from the Reth-locked RustCrypto dependency path
(`sha3 0.11.0`, `keccak 0.2.0`). It is deliberately not a full Reth node or Reth's
assembly-accelerated host path. The six independent Ethereum Keccak vectors at lengths 0, 1, 135,
136, 137, and 200 pass; the 136-byte vector distinguishes Ethereum Keccak padding from FIPS
SHA3-256.

**Zesu SSZ is selected.** The selected artifact is the lossless Amsterdam V4 repair at
`codygunton/zesu@96f1621468ba54755d653f19cbc9704e789be001`, based exactly on upstream
`aa6c94339987d278acb8b7fa409c864dbd3d05aa`. It has a full Python/Lean/Zesu differential and
observable RV64 result consumption. Both the original upstream baseline and the repaired-fork
native/zkeVM compositions pass all 23,822 fixtures. The Amsterdam execution boundary requires one
exact recovered SEC1 public key per decoded transaction, while raw SSZ decoding remains
schema-only.

The parser-root measurements remain useful evidence: Zesu has 319 blocks, 510 CFG edges, one
protocol-owned function, and 11 loop SCCs, compared with miniz's 338, 511, two, and seven. They
are not a hard selection veto. The one-function result is compiler-inlining-sensitive, and the
one-edge difference does not reliably separate proof difficulty; Zesu also has 3,356
protocol-owned instructions, heterogeneous nested containers, bounded lists, allocation,
data-dependent loops, and malformed exits. The retained `_start` full-composition context is still
not substituted for the parser-only metric, because it would count measurement adapters as
semantic complexity.

Do not enlarge the candidate to production SSZ+RLP or choose a different protocol without review;
that would change the agreed scope. This PR remains isolated from `main` commit
`65d82dc7e9f56f836e5f31cd94da0f78c28b7a41` and does not alter or stack on PR #2. PR #2's generic
machine-semantics work remains reusable, but it should not continue unchanged on the old FIPS
SHA-3 target.

## Pinned inputs

| Role | Pinned source |
|---|---|
| Reth provenance | `paradigmxyz/reth@9384bc53d8c0c77e59cac83fdaaf3b372c6d2216` |
| Zesu preservation baseline | `Consensys/zesu@aa6c94339987d278acb8b7fa409c864dbd3d05aa` |
| Selected Zesu SSZ artifact | `codygunton/zesu@96f1621468ba54755d653f19cbc9704e789be001` (`sha-fv-amsterdam-v4`) |
| Keccak Lean oracle | `trailofbits/scroll-fv@0c3927ba4d6773b4cfd1d949cba342268b104d91` |
| SSZ executable library | `etheorem/etheorem@032ab6c6d67186ba60b734e0f2c44ba1bb8b6fb0` |
| V4 executable reference | `ethereum/execution-specs@bd8c673552d957dbe9c9f3f2656b87201f5ae646` |

All compared ELFs use `RV64IM_Zicclsm` and `lp64`; the checked toolchain is GCC 15.2.0, binutils
2.46, and qemu-riscv64 11.0.1. The Nix construction verifies the complete pinned Reth
`Cargo.lock` hash `39867b4a9bae8c97872ce4f51ae184c13ba3db2c57b9c6772e31e83711866b97`.

## Corrected SSZ candidate and conformance evidence

`verification-target/zesu/docs/field-correspondence.md` freezes the Amsterdam V4 schema and the deterministic,
complete `ssz-value-v1` record protocol. The raw Zesu type preserves all 256 bits of base fee,
chain ID zero, activation optionals, blob schedule, typed execution requests, fixed vectors, and
every variable byte/list value. Its separate production adapter continues to perform RLP
transaction decoding and rejects an unrepresentable `uint256` base fee rather than truncating it.

The raw decoder parses V4 before considering exact Ere framing, has canonical offset and bound
checks, and corrects the earlier raw/Ere-prefix collision. The measurement build keeps a separate
allocator object, exported `zesu_decode_raw` decoder entry, exported `zesu_raw_result` accessor,
and sink object with no LTO across those boundaries. The host-only `zesu-ssz-value` formatter uses
the same raw type but is not linked into the RV64 metric. Its QEMU sink regression changes 33
independent rich-value fields and observes
33 distinct checksums; the checksum is anti-DCE evidence only, never value-equivalence evidence.

The selected fork is a source-equivalent promotion of the former local repair: commit
`96f1621468ba54755d653f19cbc9704e789be001` was created by strict application of that exact
10-file source diff to the pinned upstream base. The fork regenerates the same parser-root RV64
measurement (3,356 protocol instructions, 319 blocks, 510 CFG edges, one protocol function, and
11 loop SCCs), passes the complete value differential, and produces `ok 403514199dfc50e5` for the
canonical rich QEMU sink fixture. That checksum is recorded only as a behavior-preservation
checkpoint; the byte-for-byte full-value differential remains the conformance evidence.

The strict V4 differential requires byte-for-byte `ssz-value-v1` agreement on every valid case and
rejection by all implementations on every malformed case:

| Gate | Result |
|---|---|
| Core raw/Ere, empty/rich, high-`uint256`, nested/optional corpus | 7 valid and 42 malformed cases pass three-way |
| Practical boundary corpus | 30 extended max/over-bound cases pass three-way, including 8,192 deposits, 32,768 public keys, and 262,144 witness-code entries |
| Production preservation | Original upstream and repaired-fork native/zkeVM compositions each pass 23,822/23,822 fixtures; Amsterdam execution checks exact recovered public keys |
| Raw parser focused Zig tests | 5/5 pass |
| Repaired source provenance | The exact personal-fork repair commit is based on pinned upstream and builds the selected candidate |
| V3 | Quarantined and excluded: the audited legacy branch is a hybrid with no matching released full schema |

The boundary corpus deliberately does not materialize a 1 GiB transaction/access-list item or the
one/four-million-entry transaction/state lists in a full-value renderer. Those cases would emit
tens to hundreds of MiB per oracle; the decoder retains their explicit bounds, and the corpus
documents the limitation rather than treating it as a pass.

The V3 audit found no independently executable full schema to pin. Its fallback requires the
current 16-byte all-variable prefixed envelope, 44-byte new-payload request, typed request
container, nested chain/fork configuration, and packed 65-byte keys, but recognizes a 528-byte
pre-block-access-list payload. It entered Zesu in
[`1fe4f56`](https://github.com/Consensys/zesu/commit/1fe4f56ddb4c662249c4f7ecd9c5fcbd7c8cad5d).
The first execution-specs stateless schema
(`288ea51a49d50194d62a536d922fd8b9b6b61e11`) already has a different unprefixed outer form; the
v0.3.4 fixture revision (`b1d870f8f06d9eba3d74179c39660cedb98f1f38`) has typed requests but a
540-byte payload; and v0.4.1 (`b6b764ff21bb754b79e11ef5dc7ad1f79996e923`) has the prefixed outer
form but still a 540-byte payload. Deneb's consensus-specs `ExecutionPayload` is a useful
528-byte component comparison, not a `StatelessInput` oracle. V3 is therefore not accepted by the
measured `decodeRaw` path and is excluded from every strict differential statement.

The Lean oracle is an executable SizzLean-backed V4 specification, not a proof of this mixed-container
schema. It uses `SSZType.deserialize` and exact reserialization to reject SizzLean's accepted
noncanonical empty variable-list alias. The legitimate 1 MiB raw/Ere collision needs an unlimited
host stack because SizzLean's fixed-element serializer is recursive; the differential runner raises
only that process limit and retains the exact reserialization check. Focused `#print axioms` reports
`decodeCanonical` depends on `propext, Quot.sound` and `RawV4.render` on `propext`; existing
SizzLean `BasicSupported` theorem coverage does not cover this nested mixed-variable schema.

## Comparable RV64 measurements

Every decision-facing row starts at the linked ELF's exported protocol root: `sha3`,
`tinfl_decompress_mem_to_mem`, `reth_keccak256`, or `zesu_decode_raw`. The object/linked sizes and
full-instruction column retain linked-ELF context; reachability and control-flow columns use those
uniform roots. “Protocol” and “protocol funcs” use the shared ownership map, avoiding the former
comparison of CLI-rooted baseline control flow with a decoder-rooted Zesu analysis.

| Target | Protocol entry | Measured artifact | Object / linked `.text` | Full / reachable instr. | Protocol | Protocol funcs | Blocks / CFG edges | Loop SCCs |
|---|---|---|---:|---:|---:|---:|---:|---:|
| `sha3` | `sha3` | `sha3.o` | 1,540 / 1,680 B | 312 / 243 | 234 | 5 | 43 / 58 | 5 |
| `tinfl` | `tinfl_decompress_mem_to_mem` | `tinfl.o` | 6,418 / 6,397 B | 1,481 / 1,360 | 1,344 | 2 | 338 / 511 | 7 |
| `reth-keccak` | `reth_keccak256` | RustCrypto archive | 128,504 / 3,424 B | 796 / 788 | 623 | 3 | 99 / 155 | 14 |
| `zesu-ssz-parser` | `zesu_decode_raw` | decoder object | 15,300 / 17,912 B | 3,984 / 3,384 | 3,356 | 1 | 319 / 510 | 11 |

The generated stats also retain `_start` full-composition rows for context. They do not feed the
decision gates; for example, the Zesu composition has 3,932 reachable instructions, 435 blocks,
714 edges, and 24 loop SCCs only because it starts at the CLI and includes the allocator and sink.
Direct reachability is deliberately conservative: the Reth root can include labeled harness or
runtime code after a noreturn-call fallthrough, while its unchanged ownership map still attributes
623 instructions and three functions to the portable Keccak path.

The fair SSZ interval is `[0.75, 3] × 1,344 = [1,008, 4,032]` protocol-owned reachable
instructions. The parser's 3,356 passes that size gate. It is semantically distinct from Keccak:
it has heterogeneous nested containers, multiple offset tables, bounded lists, allocation,
data-dependent loops, and malformed exits. Its raw parser object has no RLP or cryptographic
undefined symbol, and the parser/composition objects pass the RV64IM_Zicclsm ISA scan.

The direct-control-flow analyzer leaves six allocator-vtable `jalr` blocks explicit; it does not
guess those indirect targets or convert them into a pass. The separate-object symbol checks show
the decoder imports only `memcpy`, `memmove`, and `zesu_raw_alloc`; the sink imports only
`memcpy` and `zesu_raw_result`. This supports the raw parser boundary but is not a claim of a
whole-program indirect-call proof.

## Gate outcome

| Gate | Result | Evidence |
|---|---|---|
| Reth is Ethereum Keccak and exceeds SHA's protocol size | pass | Six vectors; 623 versus 234 protocol instructions |
| Zesu corpus V4 decoded values agree | pass | Strict core and extended practical-boundary three-way differentials |
| Zesu preserves production behavior | pass | Original upstream and repaired-fork native/zkeVM compositions each pass 23,822/23,822 fixtures |
| Zesu result is observable without sink pollution | pass | Separate objects, structural checks, and 33-mutation QEMU regression |
| Zesu raw parser excludes crypto/RLP and uses RV64IM_Zicclsm | pass, direct-boundary scope | Object imports, symbols, direct CFG analysis, and ISA scan |
| Zesu protocol size is in `[1,008, 4,032]` | pass | 3,356 parser-owned direct-reachable instructions |
| Zesu/miniz structural comparison | recorded, not a selection gate | Loop SCCs: 11 ≥ 7; blocks: 319 < 338; edges: 510 < 511; functions: 1 < 2. Inlining and a one-edge delta make this unsuitable as a hard veto. |

## Reproduction

```sh
# Selected-fork and RV64/anti-DCE/metrics gates
git clone https://github.com/codygunton/zesu.git /tmp/zesu
git -C /tmp/zesu rev-parse sha-fv-amsterdam-v4
nix build .#zesu-native-suite --out-link build/zesu-native-suite
nix build .#zesu-sink-observability --out-link build/zesu-sink-observability
nix build .#stats --out-link build/stats
nix build .#reth-keccak --out-link build/reth-keccak
nix flake check

# Lean/SizzLean oracle
(cd tools/ssz-oracle && lake build repl && lake build ssz_oracle ssz_oracle_test && lake exe ssz_oracle_test)

# With a `uv sync --locked` environment for the pinned execution-specs revision:
PY=/path/to/execution-specs/.venv/bin/python
nix build .#zesu-value --out-link build/zesu-ssz-value
"$PY" -B verification-target/zesu/tests/ssz_differential_audit.py \\
  --reference-python "$PY" \\
  --zesu-value-binary build/zesu-ssz-value/bin/zesu-ssz-value \\
  --lean-binary tools/ssz-oracle/.lake/build/bin/ssz_oracle
"$PY" -B verification-target/zesu/tests/ssz_boundary_audit.py --extended \\
  --reference-python "$PY" \\
  --zesu-value-binary build/zesu-ssz-value/bin/zesu-ssz-value \\
  --lean-binary tools/ssz-oracle/.lake/build/bin/ssz_oracle
```

## Retained future theorem shape

This evaluation does not establish a binary-compliance theorem. A later reviewed plan may target:

```lean
theorem keccak_root_compliance :
    forall msg : ByteArray,
      RethKeccak.execute keccakBinary msg = .ok (KeccakSpec.hash msg)

theorem ssz_root_compliance :
    forall input : ByteArray,
      input.size < 2^32 ->
      RiscvSpec.execute zesuSszBinary input = .ok (BinaryFv.Specs.SSZ.decode input)
```

Here `BinaryFv.Specs.SSZ.decode` returns the complete lossless raw V4 value or a specification
error; ABI representation remains hidden at the machine boundary. No upstream Zesu issue or pull
request was opened.
