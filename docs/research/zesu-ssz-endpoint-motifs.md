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

### What the endpoint leaves undecoded

The second stage runs on transactions only. Recording this matters because it bounds what the
endpoint's correctness theorem can claim: after this endpoint, `transactions` are structured
`Transaction` values, while `witness.nodes` and `witness.headers` are still undifferentiated bytes.
"Fully deserializes `StatelessInput`" would overclaim.

| field | stage 1 (de-SSZ) | stage 2 | result |
|---|---|---|---|
| `transactions` | `decodeByteListList` | **`rlp_decode.decodeSingleTx`** | structured |
| `withdrawals` | fixed 44-byte records → `decodeWithdrawal` | n/a (SSZ, not RLP) | structured |
| `witness.nodes` | `decodeByteListList` | none | raw bytes, RLP undecoded |
| `witness.headers` | `decodeByteListList` | none | raw bytes, RLP undecoded |
| `witness.codes` | `decodeByteListList` | none | raw bytecode, never RLP |
| `public_keys` | `decodeByteListList` | none | raw keys |

The witness is RLP-encoded data that this endpoint hands onward untouched. Decoding it lives in
`deps/zesu/src/stateless/mpt/main.zig` (`verifyWitness`), outside this target.

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

Reported by `tools/ngram_dashboard.py`, which is a separate tool from `ngram_motifs.py`.
`ngram_motifs.py` asks which motifs are statistically real. This asks how much of the binary
motifs can cover, and at what price in lemmas. The dashboard renders every table in this section
and section 5a; regenerate it with

```
python3 tools/ngram_dashboard.py --cfg result-zesu-ssz-decode-cfg/zesu-cfg.json \
    --out-json out/ngram-dashboard.json --out-html out/ngram-dashboard.html
```

### 5.0 Do not report a per-length repeat census

An earlier revision of this section did, and it overcounts twice over. A run of three loads yields
**two** overlapping `LOAD LOAD` windows, and the same run is counted again at every shorter length,
inside every longer pattern containing it. `LOAD LOAD` appears in 459 raw windows; a covering
places it **30** times. Any statistic that counts windows per length independently inflates the
same code by an order of magnitude, and the inflation is worst exactly where the code is most
repetitive.

Everything below comes from one **covering** run, which attributes each instruction to exactly one
pattern at exactly one length. Column sums are therefore meaningful.

### 5.1 The covering

Start at the largest repeated length. Place its occurrences, disjointly. Take those instructions
off the table. Drop to n−1 and repeat, down to n=2. A pattern must still occur twice *after* the
longer patterns took their instructions, or it is not placed. Windows are restricted to what a
`Seg` lemma can state: inside one basic block, inside one function instance, no control transfer.

| sizes used | coverage | lemmas spent |
|---|---|---|
| n ≥ 12 | 13.9% | 12 |
| n ≥ 8 | 29.5% | 40 |
| n ≥ 5 | 45.8% | 86 |
| n ≥ 2 | **74.2%** | 149 |

**Uses per lemma decides the tail, not rarity.** A lemma pays for itself by being applied at many
sites: 11.2 sites at n=2, 6.3 at n=4, 3.1 at n=5, and **exactly 2.0 at every length from 14 up**.
The long motifs are used the minimum number of times that still counts as a repeat, so a
51-instruction lemma applied twice cannot repay its authoring cost under any cost model.

Per level, same covering:

| level | largest repeat | coverage | lemmas | invocations removed |
|---|---|---|---|---|
| exact 32-bit word | 14 | 28.8% | 127 | 19.9% |
| mnemonic + operands | 14 | 28.8% | 127 | 19.9% |
| mnemonic + register names | 32 | 51.1% | 188 | 38.3% |
| mnemonic + register roles (α) | 46 | 68.5% | 203 | 52.6% |
| opcode | 51 | 72.2% | 180 | 56.7% |
| **instruction class** | **51** | **74.2%** | **149** | **58.8%** |

The class level wins on coverage and on lemma count at once, which is why the rest of this section
uses it. That ordering reproduces the archived target's.

### 5.2 A previous defect in this section

The table this section used to carry — 15 lemmas, 62.6%, 35.6% — came from an ad-hoc script that
ranked candidates by `uses` rather than by the `uses × (n−1)` it claimed to use. It therefore took
`LOAD LOAD` (n=2, 300 uses, value 300) ahead of `LOAD LOAD LOAD` (n=3, 280 uses, value 560). The
level ordering it reported was right; its numbers were not.

The value-weighted covering it belonged to is now removed rather than repaired. Its objective was
`uses × (n−1) − 20`, and section 9 establishes that *both* terms are ungrounded: the unit is a
class-lemma invocation that no longer exists in the tree, and the constant 20 came from a
calibration against the file the pivot deleted. The covering reported above weights nothing and
needs no constant, so it survives that finding intact.

## 5a. What kind of repetition is this?

The artifact maps every inline instance, so "is a discovered repeat just a function the compiler
inlined twice?" is answerable rather than a guess. Of 88 distinct function names, **12 have two or
more instances**, and those instances hold 20.6% of the binary.

### The search rediscovered a function

The strongest motif in the study, `lbu lbu lbu lbu slli or slli slli or or`, is exactly the body of
`mem.readInt`, which the compiler inlined 7 times with that shape. **Seven placements of the
covering equal a whole `mem.readInt` body, instruction for instruction.** Nothing told the search
that functions exist.

Do not also count `ssz.readU32`: all 10 of its instances are **pc-identical** to the `mem.readInt`
they inline, so it is a pure wrapper contributing no code of its own. Ten of the 14 `mem.readInt`
instances sit inside one.

### One source function is not one shape of code

| function | instances | byte shapes | register shapes | opcode shapes | class shapes |
|---|---|---|---|---|---|
| `mem.readInt` | 14 | 14 | 14 | **6** | 6 |
| `ssz.readU32` | 10 | 10 | 10 | 5 | 5 |
| `mem.writeInt` | 10 | 10 | 10 | 5 | 5 |
| `alt_fl_alloc.sizeClassOfBytes` | 4 | 4 | 4 | **1** | 1 |
| `mem.Allocator.rawAlloc` | 3 | 3 | 2 | 2 | 1 |

Inlining specialises each call site, so an exact-code lemma is the wrong abstraction even for one
source function: `mem.readInt` has 14 instances and 14 distinct byte sequences. The opcode
sequence *is* shared — by 7 instances at a time, not by all 14. The six shapes differ for real
reasons: u32 against u64 (10 instructions against 22), a signed `lb` variant, and call sites where
a following store or compare landed inside the inline range.

Note how rarely the class column improves on the opcode column. **For a repeated function body,
opcodes already do the work**; the class abstraction earns its keep on cross-function motifs.

### Whole-body lemma candidates

A body earns a lemma when two or more instances share a class-level shape. Bodies nested inside a
chosen one are skipped.

| function | length | sites | instructions | share | `Seg` possible |
|---|---|---|---|---|---|
| **`alt_fl_alloc.sizeClassOfBytes`** | 78 | 4 | 312 | **7.0%** | no — 24 transfers |
| `ssz_decode_root.put` | 15 | 6 | 90 | 2.0% | yes |
| `mem.readInt` | 10 | 7 | 70 | 1.6% | yes |
| `mem.readInt` (u64 form) | 22 | 3 | 66 | 1.5% | yes |
| `mem.Allocator.allocAdvancedWithRetAddr` | 25 | 2 | 50 | 1.1% | no — 4 transfers |

`alt_fl_alloc.sizeClassOfBytes` is the largest single prize in the study: **one lemma, 7.0% of the
binary**, four instances of 78 instructions all sharing one class shape. It holds 24 control
transfers, so no `Seg` lemma can state it. It needs a function-level lemma form.

### How much leverage is more than "these instances are the same function"?

Each lemma in the covering is classified by where its sites sit.

| what repeats | lemmas | instructions | share of binary |
|---|---|---|---|
| same function, several instances | **8** | 205 | **4.6%** |
| across different functions | 113 | 2463 | 55.5% |
| inside one instance | 28 | 624 | 14.1% |

**Only 4.6% of the binary is coverage that merely restates "these instances are the same
function".** That is the part a whole-body lemma subsumes. The rest is leverage the inline map
cannot give:

- `ld ld` at 30 sites across **23 distinct functions**;
- `addi mv mv auipc` at 23 sites across 15 functions;
- a 32-instruction motif placed 5 times **inside a single instance** of `rlp_decode.decodeTxFields`.

The four-byte read is an example of the useful kind rather than the trivial kind. Its 14 sites span
three function names — 8 in `mem.readInt`, 5 in `ssz.decode`, 1 in `ssz.decodeByteListList` — and
the last two open-code the idiom instead of calling it. A whole-body `readInt` lemma would miss six
of the fourteen.

### The strategies compose

| strategy | lemmas | coverage | instructions / lemma |
|---|---|---|---|
| n-gram motifs alone | 149 | 74.2% | 22.1 |
| whole inlined bodies alone | 10 | 14.6% | **64.8** |
| **bodies first, then motifs** | 151 | **79.2%** | 23.3 |

Whole-body lemmas are three times as productive per lemma, but they reach only the sixth of the
binary the compiler duplicated. Most repetition here is *inside* one large single-instance
function: `rlp_decode.decodeTxFields` hosts 719 covered instructions on its own. Take the bodies
first, then let the motif covering work on the remainder — **two extra lemmas buy five points of
coverage.**

### The unresolved cost

Unchanged, and now the only thing standing between this ranking and a decision: a class-level
lemma merges several dataflow shapes and needs register-distinctness hypotheses, which no model
here prices. Section 9 proposes the experiment that would price it.

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

- **RESOLVED (section 9): the payoff model prices 26% of the cost.** Fetch and decode are 74% and
  no motif lemma shares either. Every case saves 12-20%, and `uses x (n-1)` barely predicts which.
- **The payoff model prices motifs against a baseline that does not exist.** Its unit is "one
  class-lemma invocation", but `InstructionClassSteps.lean` and the `decoderLoadStep` family were
  deleted in the pivot and nothing replaced them — zero references survive in the tree. Its only
  measured rate, −19 lines per register-write step, came from `PLAN_PROOF_PATTERNS.md` measurements
  against that deleted file. Motifs here are therefore ranked by **invocations saved**, a
  structural count of a unit whose price is unknown, and any line figure the tool still emits
  should be ignored. Section 9 Case 0 is what would fix this.
- **RESOLVED (section 9): `Seg` now has one.** `BinaryFv/Zesu/Machine/` on branch `motif-lemmas`
  retires `0x70` through `StepPremises`, and that bundle already removes the retire cost entirely.
- **`Seg` has no consumers.** The segment machinery every motif lemma would be stated in is
  complete and unused: outside `Seg.lean` there are zero uses of its combinators. This study ranks
  candidates for a layer that no proof has yet adopted.
- **No SCC, loop, or liveness data.** The old database supplied these; `zesu-cfg.json` does not, so
  the tandem-repeat classification rests on motif periodicity alone, without the loop cross-check.
- **Motifs are linear.** Windows are consecutive instructions inside one basic block; nothing here
  searches CFG paths.
- **Nothing is proved.** This ranks candidates.

## 9. The spike ran, partly. The authoring question is still open.

Executed on branch `motif-lemmas`. Data in `docs/research/motif-lemma-measurements.md`.

### 9.1 What was measured

**The CI cost of proving this binary.** Fetch is four `native_decide`s per instruction at
**84.8ms each**, measured across 2624 calls in five modules spanning a 13x size range, linear
throughout. `decide` cannot do the job at all -- the image is 17740 bytes as `ByteArray.mk` chunks
joined by `++`, and kernel reduction overflows the C stack.

Per instruction: **339ms fetch, ~50ms decode, ~136ms execute, ~0 retire** (`StepPremises` carries
the retire premises once per segment). Floor for this report's 149-lemma covering, 3292
instructions: **18.6 minutes**. Whole binary: **25.1**.

That floor is irreducible by any arrangement of motif lemmas, because each instruction owns a
different word. **Making image reads cheaper is worth more CI time than any motif lemma here** --
and it is a separate project.

### 9.2 The authoring measurement: this report's ranking is confirmed

Five cases were written as motif lemmas and applied at every site. Lines, from files that build:

| case | motif | n | sites | no lemma | with lemma | **saved** | break-even |
|---|---|---|---|---|---|---|---|
| C | `mv addi` | 2 | 45 | 900 | 608 | **32%** | 3.3 sites |
| C | `ld ld addi` | 3 | 13 | 312 | 196 | **37%** | 2.5 |
| D | `addi mv mv auipc` | 4 | 21 | 588 | 304 | **48%** | 2.1 |
| A | `mem.readInt` | 10 | 7 | 364 | 146 | **60%** | 1.4 |
| G | `decodeTxFields` tail | 32 | 5 | 680 | 204 | **70%** | 1.1 |
| **all five** | | | | **2844** | **1458** | **49%** | |

**The saving rises monotonically with `n` across a 16x range, and every case pays.** That is what
section 5's `uses x (n-1)` predicts. The mechanism is visible in the numbers: the baseline grows at
about four lines per instruction while an application is flat at thirteen.

49% is a **lower bound**. Applications here are standalone theorems that restate their context;
inline in a larger proof they are about one line, which gives 87% on the same five cases.

### 9.3 Two side conditions this report does not price, and one it predicted that did not appear

- **`adv`** — `Sail.BitVec.addInt q 4 = q + 4`. A concrete site gets this by `decide`; a lemma over
  a symbolic start cannot. One argument per site.
- **Address association** — `(start + 4k) + 4` and `start + 4(k+1)` are not definitionally equal for
  `BitVec`, so the flat form needs a rewrite at every step. Nesting the addresses avoids it. This
  constrains how a motif lemma may be *stated*.
- **Not** the register-distinctness hypotheses section 5 predicted. Those never appeared, because
  `Seg.step` already takes `destination` and `keep` as parameters a caller carries per segment.

### 9.4 Three cases could not be measured, and one of them exposes a defect in this report

| case | motif | n | sites | reason |
|---|---|---|---|---|
| B | `mem.writeInt` | 15 | 6 | **its instances are not contiguous** |
| F | `rawAlloc`/`rawRemap` | 4 | 3 | ends in `jalr` |
| E | `sizeClassOfBytes` | 78 | 4 | 48 of 78 are control transfers |

**Case B is not a linear motif.** The `mem.writeInt` instance entered at `0x2cc0` holds 16 program
counters spread over 36 instruction slots, and four of its six site pairs overlap — the scheduler
interleaved them. Section 5a counts these as six sites of one shape, which they are as *instances*;
they are not six linear windows. **An instance is a set of program counters, not a run**, and this
report's site counts do not distinguish the two.

E and F need `FunctionInstanceContract` rather than `Seg`. E is section 5a's largest single prize.

### 9.5 A methodological result worth more than the numbers

Every blocked case's generated file **typechecked on the first attempt** and produced a plausible
saving — B 66%, G 71%, E 71%, F 19%. All four were worthless: the per-instruction premises are
hypotheses, and nothing forces them satisfiable at the real address. At those sites they are not.

What caught it was cross-referencing each case's addresses against this artifact's own mnemonics.
The compiler did not, and could not. **A Lean file that builds is not evidence that it says
anything about the binary.**

### 9.6 What else the spike established

- `0x70` retires — the first kernel-backed machine theorem on this target.
- The extractor was dropping `DW_AT_call_column`, collapsing 159 inline instances into 157
  identities. Both collisions were in `alt_fl_alloc.sizeClass`/`sizeClassOfBytes`.
- Case D has 21 provable sites, not 23: two of its `auipc`s carry `.rela.text` relocations.
- CI cost, separately: 84.8ms per `native_decide`, an 18.6-minute floor for this report's covering.

## 10. The 2-5-grams: worth writing

Section 9.2 answers the part that matters. A bespoke lemma at n=2 saves **32%** over 45 sites and
breaks even at 3.3 — so the short motifs pay, and the question of whether to write them is settled
in favour of writing them.

Whether a *tactic* would beat the bespoke lemma is still untested. It is now a smaller question:
the lemma already returns 32% at the shortest length, so a tactic competes for the remainder rather
than for the whole prize.
