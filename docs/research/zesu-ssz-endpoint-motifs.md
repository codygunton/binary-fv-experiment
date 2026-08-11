# Instruction motifs in the Zesu SSZ decode endpoint

The motif analysis, retargeted from the archived grafted `decodeRaw` to the real upstream Zesu SSZ
decode endpoint. Method and tool are unchanged and documented in
`binary-ngram-motifs.md`; this reports what the new target says. Everything below comes from
`out/zesu-ssz-a.json`, seed 20260810, 5000 resamples. Two runs are byte-identical.

Input: `zesu-cfg.json` from `nix build .#zesuSszDecodeCfg`, object sha256 `a387cf56…`.

## 1. Scope

| count | meaning |
|---|---|
| 5442 | symbol instruction references in the artifact |
| **4435** | distinct instructions — the corpus |
| 37 / 159 | functions / function instances (123 inlined) |
| 889 | basic blocks |

5442 − 4435 = 1007, exactly the size of `main`. `main` and `ssz_decode_root.main` are **one
function under two names**, sharing all 1007 program counters. Rows are deduplicated by pc.

2173 pcs are claimed by up to **6 nested function instances** at once. Ownership is therefore a
stack, not a value; the owner here is the innermost instance, which is the analogue of exact
ownership in the old database. That yields 134 distinct owners.

## 2. The endpoint is mostly not SSZ

Attribution matters here. The artifact's function-level `semanticGroup` assigns a whole function to
one group, so it credits all 1007 instructions of `main` to `ssz` even though most of them are
inlined code from elsewhere. Attributing each instruction to its **innermost inline instance**, and
that instance to its source file, gives the real composition:

| source | instructions | share |
|---|---|---|
| `rlp_decode.zig` | 2028 | **45.7%** |
| **`ssz.zig`** | **603** | **13.6%** |
| `Allocator.zig` | 483 | 10.9% |
| `alt_fl_alloc.zig` | 411 | 9.3% |
| `array_list.zig` | 366 | 8.3% |
| `mem.zig` | 331 | 7.5% |
| `rlp.zig` | 137 | 3.1% |
| `ssz_decode_root.zig` | 36 | 0.8% |

**RLP decoding is 48.8% of the endpoint; SSZ decoding is 13.6%.** The harness proper is 36
instructions. Allocation and standard-library support together are 36%.

Within the SSZ share:

| instructions | instance | kind |
|---|---|---|
| 432 | `ssz.decode` | inlined into `main` |
| 81 | `ssz.decodeByteListList` | concrete |
| 57 | `ssz.decodeWithdrawal` | inlined |
| 33 | small struct decoders, `forkNameFromSchemaByte` | inlined |
| 0 | every `ssz.readU32` instance | fully absorbed |

Any plan that budgets effort proportionally to "the SSZ endpoint" is budgeting mostly for RLP,
allocation, and the Zig standard library.

## 2a. Why RLP and SSZ are interleaved at all

SSZ is the outer envelope; RLP is the payload. The mechanism is
`stateless/stateless/ssz.zig:320-324`:

```zig
// transactions: List[ByteList, N] — offset-table format
const txs_raw = try decodeByteListList(alloc, ep_data[off_transactions..off_withdrawals]);
const transactions = try alloc.alloc(input_mod.Transaction, txs_raw.len);
for (txs_raw, 0..) |raw_tx, i| {
    transactions[i] = try rlp_decode.decodeSingleTx(alloc, raw_tx);
}
```

The whole `StatelessInput` is SSZ-encoded. Inside it, `execution_payload.transactions` is an SSZ
`List[ByteList, N]` — a list of **opaque** byte strings. Each of those byte strings is an
RLP-encoded Ethereum transaction. SSZ never looks inside them; it splits the offset table into
slices and hands each slice to the RLP decoder.

This mirrors Ethereum's real layering. Consensus-layer and stateless-witness formats are SSZ, but
transactions inside an execution payload stay RLP-encoded for execution-layer compatibility, so an
SSZ container carrying them must treat them as opaque bytes.

That layering is also why the instruction counts are so lopsided. `decodeByteListList` reads a
`u32` offset table and returns **zero-copy slices into the input** — 81 instructions, no parsing
and no copying. Parsing a transaction is the opposite: typed envelopes, and separate decoders for
field lists (940), access lists (310), authorization lists (222), hash lists (175) and addresses
(63).

## 3. Geometry: less inlined, so long motifs are worth less

| | new target | archived grafted target |
|---|---|---|
| instructions | 4435 | 3369 |
| segments | 761 | 314 |
| segment mean / median / max | 5.8 / 3 / 157 | 10.7 / 4 / 476 |
| BTYPE share | 7.8% | 3.9% |
| JAL share | 3.3% | 1.4% |

Branch density roughly doubled, because this is real code with real calls rather than one
massively inlined function. Straight-line runs are correspondingly shorter, and the coverage
ceiling falls hard:

| n | ceiling, new | ceiling, old |
|---|---|---|
| 4 | 70.8% | 85.1% |
| 8 | **48.3%** | 72.0% |
| 12 | 36.5% | 65.2% |
| 20 | 21.6% | 55.2% |

## 4. Results

662 motifs tested across lengths 2–14. **58 are significant** at family-wise p < 0.05, worst case
over all three nulls — against 11 on the old target. 297 of 682 closed motifs are self-contained.

Top motifs by invocations saved:

| n | sites | owners | p | invocations saved | motif |
|---|---|---|---|---|---|
| 8 | 15 | 10 | 0.0002 | 105 | `lbu ×4; slli; or; slli; slli` |
| 2 | 96 | 35 | 0.0104 | 96 | `sd(r,sp) sd(r,sp)` |
| 9 | 12 | 7 | 0.0002 | 96 | `lbu ×4; slli; or; slli; slli; or` |
| 4 | 29 | 17 | 0.0002 | 87 | `slli or slli slli` |
| 6 | 16 | 11 | 0.0002 | 80 | `lbu ×4; slli; or` |
| 4 | 24 | 10 | 0.0002 | 72 | `sd ×4 (sp)` |
| 4 | 17 | **17** | 0.0012 | 51 | `addi(sp,sp); sd(ra,sp); sd; sd` |

Disqualified motifs: 155 straddle an owner boundary, 140 contain a control transfer (against 66 on
the old target — the denser branching again), 80 are confined to one instance, 10 are tandem
repeats.

### The four-byte read replicates exactly

The old target's headline motif reappears here, on an independently compiled binary from a
different source tree, with **the same immediate structure**:

```
slots=7   constant=3 (values 8, 16, 24)   tied to one base=4   genuinely free=0   -> 1 lemma argument
```

Shifts of exactly 8, 16 and 24 over four consecutive byte loads, with a single varying base offset.
This is the strongest evidence in either study that the motif is a real semantic operation — a
little-endian u32 read — and not an artefact of the grafted decoder.

### One old conclusion reverses

The archived study concluded that ABI frame handling was **not** a reuse opportunity, because the
prologue appeared in only 2 owners. On the real target, `addi(sp,sp); sd(ra,sp); sd; sd` occurs at
17 sites in **17 distinct function instances**, and stack-save runs `sd(r,sp) sd(r,sp)` occur 96
times across 35 instances.

That conclusion was an artefact of the grafted target being one massively inlined function with 12
stack frames. With real calls, prologue and epilogue handling becomes one of the best reuse
opportunities available. **This is the clearest way the retarget changed an answer.**

## 5. Coverage strategy

Greedy tiling, minimising lemma count plus residual, where value = uses × (n−1):

| level | lemmas | coverage | invocations removed |
|---|---|---|---|
| α (register roles) | 17 | 39.2% | 24.0% |
| opcode only | 19 | 52.2% | 32.0% |
| **instruction class** | **15** | **62.6%** | **35.6%** |

Instruction-class level wins on all three measures at once, reproducing the ordering found on the
old target (11 lemmas, 68.2%, 36.1%). The class-level picks are blunt: `LOAD LOAD` at 300 uses,
`STORE STORE` at 205, `ITYPE ITYPE AUIPC` at 139, `SHIFTIOP SHIFTIOP RTYPE RTYPE` at 52.

The unresolved cost is unchanged: a class-level lemma merges several dataflow shapes and needs
register-distinctness hypotheses, which this model does not price.

## 6. Controls

| control | result |
|---|---|
| Shuffled corpus | **0 of 12** lengths significant (old target: 1 of 22) |
| Planted motif | length 7, planted 9, recovered 9 |
| Scheduler invariance | 0 failures in 1167–1480 re-schedulings per length; order-dependent control fails 887–1454 |
| Determinism | two runs byte-identical |

Observed owner support against the maximum over 5000 resamples of each null:

| n | observed | N1 max | N2 max | N3 max |
|---|---|---|---|---|
| 2 | 38 | 9 | 27 | 21 |
| 4 | 17 | 2 | 8 | 5 |
| 8 | 10 | 0 | 3 | 2 |
| 12 | 3 | 0 | 2 | 0 |

From n=4 up, the observed value exceeds every null's maximum over 5000 resamples.

## 7. The effect derivation, and how it was checked

`zesu-cfg.json` records mnemonics, operands, bytes, blocks and the inline hierarchy, but **not
register or memory effects**. `load_zesu_cfg` derives them from opcode class and operand position.

Derived facts that a proof would rest on must not be assumed correct, so the derivation was run
against the old artifact, which carries LLVM's own recorded effects: **100% agreement on all 3287
non-`jalr` instructions**. Every residual mismatch is `jalr` written in the old `offset(rs1)`
syntax; all 187 `jalr`/`jr` in the new artifact use the three-operand form.

That check found two real defects rather than confirming a belief:

1. `zero` was counted as a dataflow source. It is a constant, and 81 stores in this artifact source
   it, so every one gained a spurious dependence.
2. The one-register `jalr offset(rs1)` form was read as writing its base register.

A third defect was found by the retarget itself: the old branch-target rule treated any bare
immediate above `0x10000` as a target. Program counters in a relocatable object start at 0, so
every small branch target was being recorded as an immediate. The rule is now class-based.

## 8. Limitations

- **The line-based payoff model is no longer calibrated.** Its only measured rate, −19 lines per
  register-write step, came from `PLAN_PROOF_PATTERNS.md` measurements against
  `InstructionClassSteps.lean`, which the pivot deleted. Motifs here are therefore ranked by
  **invocations saved**, a structural count, and any line figure the tool still emits should be
  ignored until re-measured against the new proof layer.
- **No SCC, loop, or liveness data.** The old database supplied these; `zesu-cfg.json` does not, so
  the tandem-repeat classification rests on motif periodicity alone, without the loop cross-check.
- **Motifs are linear.** Windows are consecutive instructions inside one basic block; nothing here
  searches CFG paths.
- **Nothing is proved.** This ranks candidates.
