# Instruction motifs in the Zesu SSZ binary

A statistical search for instruction sequences that repeat often enough, across enough distinct
function instances, that one parameterised `Seg` lemma would pay for itself.

`PLAN_PROOF_PATTERNS.md` attacked proof-authoring cost from the Lean-text side. This is the
machine-code side. The tool is `tools/ngram_motifs.py`; every number below comes from
`out/motifs.json`, produced with seed 20260810 and 5000 resamples by:

```sh
python3 tools/ngram_motifs.py \
  --regions   ../../build/machine-regions-lean/machine-regions.json \
  --objdump   ../../build/stats/objdump/zesu-ssz.txt \
  --control-objdump ../../build/stats/objdump/reth-keccak.txt \
  --out-json out/motifs.json --out-md out/motifs.md \
  --resamples 5000 --maximum-test-length 16 --dag-lengths 4 6 8 12 --dag-windows 400
```

Two runs of that command are byte-identical (1059310 bytes). The one number not read from the JSON
is the cross-target overlap in §7, which compares `objdump_mnemonic_motifs` applied to both
disassemblies; the tool stores only the control's set.

## 1. What the corpus is, and what it is not

Three instruction counts circulate in this repository and they disagree. They reconcile exactly:

| Count | Meaning |
|---|---|
| **3984** | every instruction in `.text`, across all 10 ELF symbols |
| **3444** | `summary.binaryInstructionCount` — addresses in declared regions |
| **3369** | `instructions` rows — the corpus used here |

- 3984 − 3444 = 540 = `zesu_raw_sink_checksum` 451 + `main` 72 + `write_all` 9 + `_start` 8.
- 3444 − 3369 = 75 = 39 addresses inside `zesu_decode_raw` that no owner claims, plus all 36
  addresses of `zesu_raw_alloc`, `zesu_raw_error` and `zesu_raw_result`, which have no owner rows.
- The 39 unowned `zesu_decode_raw` addresses are live code, not padding: `0x10440` is a bare `ret`,
  `0x13768`–`0x1377c` is a tail-call thunk into `zesu_raw_alloc`, `0x130fc`–`0x13108` is a store
  block. They are unowned, not absent.
- Every address in the region database appears in the objdump. The database invents nothing.

**The corpus is the 3369 owned rows** — `zesu_decode_raw` 3341, `memmove` 19, `memcpy` 9 — because
only those carry `owner`, `reads`, `writes`, `memory`, `transfer`, `liveIn`/`liveOut`, `scc` and
`loop`. Every rate below is against 3369. Results say nothing about `zesu_raw_sink_checksum`.

One structural fact shapes everything: the binary is essentially **one function**. Inlining put
3341 of 3369 instructions inside `zesu_decode_raw`, spread over 111 active owners (function
instances). "Owner support" below means distinct function instances, not distinct ELF symbols.

## 2. Why raw n-gram frequency is the wrong instrument here

Three failure modes, all of which bite on this binary:

**Self-overlap.** The most frequent 20-gram at register-set granularity has 31 raw occurrences. It
is a tandem repeat inside an unrolled byte copy, present in **2** owners, with **4** non-overlapping
occurrences. Ranking by raw count puts an unrolled loop at the top of a list of reuse candidates.

**Abstraction level dominates.** At exact-word granularity, repetition dies at n≈10 — one repeated
10-gram, zero 12-grams. At register-role granularity, repeats survive past n=20. Any claim about
"which n matters" is a claim about the token level, not about the binary, unless the level is
stated.

**One hot symbol.** `lbu`, `ld`, `sd`, `slli` and `or` are the majority of the stream. Against an
i.i.d. null, `lbu lbu lbu lbu` at 131 occurrences is unremarkable; against a null that preserves
per-segment composition, the question becomes interesting.

## 3. Method

**What an n-gram is.** A window of n instructions at consecutive addresses inside one straight-line
segment, mapped through a tokeniser τ. Two windows match iff their token sequences are equal. The
levels form a lattice of quotients, and only the last two are opcode-only:

| level | token | matching is equality… |
|---|---|---|
| L0 | the 32-bit instruction word | literally |
| L1 | mnemonic + register operands + immediates | modulo encoding |
| L2 | mnemonic + register names, positional | modulo immediates |
| **L3** | **mnemonic + α-renamed register tuple** | **up to a bijection on registers fixing `sp`/`gp`/`ra`/`zero`/`tp`** |
| L4 | mnemonic | on opcodes |
| L5 | Lean instruction class | on opcode classes |
| DAG | dependence-graph isomorphism class | up to register bijection *and* valid re-scheduling |

L3 is the operative level, and it is not an opcode sequence: it carries the whole register-sharing
pattern. In `lbu(r0,r1) lbu(r2,r1) lbu(r3,r1) lbu(r4,r1)` the repeated `r1` asserts that all four
loads share a base register and that the four destinations are distinct — dataflow structure that
L4 discards as `lbu lbu lbu lbu`. Formally, two windows match at L3 iff their mnemonics agree
pairwise and some bijection on non-pinned register names carries one operand sequence to the other.

Two consequences. L3 tokens are **window-relative**, so there is no fixed alphabet and ordinary
string matching does not apply — which is why the suffix array covers the context-free levels only
and L3 closed patterns are computed directly. And **immediates are excluded from the L3 match** by
design, because they become lemma arguments; §6 measures how many arguments that actually is,
rather than assuming.

An L3 motif corresponds to exactly one `Seg`-valued theorem, with the α-renamed registers and the
surviving immediates as its arguments.

**Segmentation.** Maximal straight-line runs: break after any instruction whose `transfer` is not
`ordinary`, and before any instruction with more than one predecessor. 314 segments, mean length
10.7, longest 476. Motifs never cross a boundary, because a `Seg` lemma cannot.

**No fixed n.** For the fixed token levels a suffix array with Kasai LCP enumerates all maximal
repeats at every length. For L3 the renaming is window-relative, so a fixed token stream cannot
represent it; closed motifs are computed directly instead, keeping only those no extension
preserves the occurrence set. Both give closed patterns, so the result set is a property of the
binary rather than of the enumeration.

**Four counts per motif**, never one: raw occurrences, non-overlapping occurrences (greedy
leftmost, exact for fixed length), owner support (function instances containing a whole
occurrence), and tandem structure (smallest period `p`; `p < n` means an unrolled loop, which
belongs to an induction lemma and is reported separately).

**Significance.** Westfall–Young max-statistic permutation test at the α level, 5000 resamples
against three nulls that permute whole instructions and recompute the renaming:

- **N1** draws a mnemonic sequence from a fitted order-1 chain, then draws a real instruction of
  that mnemonic — adjacent-pair structure and per-mnemonic operand distributions both survive.
- **N2** permutes instructions within each straight-line segment — preserves each segment's exact
  multiset, so it tests ordering and register linkage alone.
- **N3** permutes instructions within each owner — preserves each function instance's composition
  while destroying the ordering it shares with other instances, which is the claim reuse rests on.

The reported p is the **worst case across all three**. Comparing against the distribution of the
family-wise *maximum* already adjusts for every motif of that length, so no further multiplicity
correction is applied — Benjamini–Hochberg on top would correct twice.

**Payoff.** Only one authoring rate in `PLAN_PROOF_PATTERNS.md` is a measurement rather than an
estimate: −19 lines per register-write step. Gross saving is therefore
`(non-overlapping − 1) × register-write steps × 19`, and instructions that are not register-write
steps are counted as unestimated rather than assigned an invented rate. The authoring cost of a new
lemma was never measured, so it is reported as a break-even threshold, not filled in.

## 4. Controls

The analysis is only worth as much as its ability to return nothing.

- **Shuffled corpus.** The whole significance test is re-run with a structure-free corpus. A
  working test reports approximately no significant lengths.
- **Planted motif.** A synthetic motif of known length is planted a known number of times in a
  shuffled corpus; the enumerator must recover both.
- **Scheduler-invariance check with a failing control.** The canonical DAG form must survive random
  valid re-schedulings of real windows, *and* a deliberately order-dependent form must break under
  the same re-schedulings. Invariance alone proves nothing — a constant function would pass it.
- **Cross-target.** The mnemonic-level pipeline is run against `reth-keccak` to separate compiler
  and ABI idioms from SSZ-specific ones.

Two defects in this study were caught by the third control and fixed. Weisfeiler–Leman colour ties
were broken by original instruction index, which reintroduced the very scheduling dependence the
canonical form exists to remove; ties are now resolved by individualisation-refinement under a
budget, and budget-capped windows are marked instead of being reported as exact. Separately, the
region database reports no reads or writes for `jalr`, which let a re-scheduling hoist a call above
the `auipc` setting up its link; source operands are now unioned into the reads and a control
transfer is pinned last in its segment.

## 5. The length spectrum: which n matters is a fact about the token level

Repeated windows per length, per level:

| level | n=2 | n=4 | n=6 | n=8 | n=10 | n=12 | n=16 | n=20 | n=24 | n=30 | n=40 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| L0 exact word | 159 | 49 | 19 | 7 | 1 | **0** | 0 | 0 | 0 | 0 | 0 |
| L1 mnemonic+operands | 166 | 50 | 19 | 7 | 1 | **0** | 0 | 0 | 0 | 0 | 0 |
| L2 mnemonic+registers | 343 | 199 | 119 | 76 | 60 | 49 | 40 | 33 | 29 | 20 | 13 |
| L3 α-renamed | 245 | 324 | 246 | 193 | 160 | 113 | 74 | 55 | 43 | 20 | 13 |
| L4 mnemonic | 128 | 269 | 250 | 220 | 211 | 200 | 165 | 135 | 101 | 66 | 39 |
| L5 Lean class | 56 | 235 | 275 | 240 | 224 | 210 | 168 | 139 | 107 | 69 | 41 |

**Byte-identical code repeats almost not at all.** At L0 there is one repeated 10-gram in the whole
binary and no repeated 12-gram. Any proof-reuse scheme keyed on literal instruction words is capped
at very short runs. Everything below depends on abstracting the registers.

The 4–12 range is a reasonable place to look at L3, where the curve peaks at n=4 and still has 113
repeated windows at n=12. At L4/L5 the curve barely decays out to n=40, but those levels discard
the register linkage a lemma needs, so their long motifs are not directly usable.

## 6. Motifs

668 closed α-motifs. **236 are self-contained** — statable as one `Seg` lemma. The rest are
disqualified, and the reasons are informative:

| count | reason |
|---|---|
| 273 | some occurrences cross an owner boundary |
| 88 | confined to one function instance |
| 66 | contains a control transfer |
| 5 | tandem repeat (an unrolled loop) |

Only 5 tandem repeats survive to this stage, because closure already collapses the tandem family
into one representative. The dominant disqualifier is owner straddling: a window that begins in one
inlined instance and ends in another is not a lemma about either.

599 motifs were tested (lengths 2–12; no self-contained motif is longer). **11 are significant** at
family-wise p < 0.05, taking the worst case over all three nulls.

| n | raw | non-overlap | owners | p | gross lines | motif |
|---|---|---|---|---|---|---|
| 5 | 47 | 47 | 24 | 0.0002 | 4370 | `lbu(r0,r1) lbu(r2,r1) lbu(r3,r1) lbu(r4,r1) slli(r0,r0)` |
| 6 | 34 | 34 | 21 | 0.0002 | 3762 | …+ `or(r0,r0,r2)` |
| 8 | 17 | 17 | 16 | 0.0002 | 2432 | …+ `slli(r3,r3) slli(r4,r4)` |
| 5 | 18 | 18 | 17 | 0.0002 | 1615 | `lbu(r0,r1) slli(r2,r2) or(r2,r2,r3) slli(r4,r4) slli(r0,r0)` |
| 9 | 10 | 10 | 10 | 0.0002 | 1539 | …+ `or(r3,r4,r3)` |
| 4 | 21 | 21 | 20 | 0.0012 | 1520 | `slli(r0,r0) or(r0,r0,r1) slli(r2,r2) slli(r3,r3)` |
| 8 | 10 | 10 | 10 | 0.0002 | 1368 | `lbu ×4 slli slli slli or` |
| 5 | 11 | 10 | 5 | 0.0006 | 855 | `ld(r0,sp) ld(r1,sp) or(r0,r1,r0) ld(r1,sp) ld(r2,sp)` |
| 9 | 5 | 5 | 5 | 0.0002 | 684 | `lbu ×4 slli or slli slli or` (variant) |
| 6 | 6 | 6 | 6 | 0.0104 | 570 | `lbu slli or slli slli or` |
| 6 | 12 | 8 | 4 | 0.0008 | 532 | `lui(r0) add(r0,sp,r0) sd(r1,r0)` ×2 |

**These are not 11 independent wins.** Nine of the eleven are nested variants of one idiom — the
four-byte little-endian read that assembles `lbu` bytes with `slli`/`or`. They are genuinely
distinct closed patterns (different occurrence sets), but one lemma family covers them. The honest
reading is *one high-value idiom with a support/length trade-off*, plus two smaller ones: a
stack-reload-and-combine (`ld ld or ld ld`, 5 owners) and a large-offset stack store
(`lui add sd` ×2, 4 owners).

p = 0.0002 is the resolution floor at 5000 resamples, not a point estimate.

### How many immediate arguments a lemma actually needs

Immediates are excluded from the L3 match by design, because they become lemma arguments. Counting
distinct immediate *tuples* is a poor summary of what that costs: it cannot distinguish "one base
offset varies" from "every slot varies independently", and those differ by an order of magnitude in
authoring cost. Each slot is therefore classified as constant across occurrences, a fixed offset
from one shared base, or genuinely free:

| motif | n | sites | owners | slots | constant | tied to one base | free | **lemma immediate args** |
|---|---|---|---|---|---|---|---|---|
| `slli or slli slli` | 4 | 21 | 20 | 3 | 3 (8, 16, 24) | 0 | 0 | **0** |
| `lbu ×4 slli or` | 6 | 34 | 21 | 5 | 1 (8) | 4 | 0 | **1** |
| `lbu ×4 slli or slli slli` | 8 | 17 | 16 | 7 | 3 (8, 16, 24) | 4 | 0 | **1** |
| `lbu slli or slli slli` | 5 | 18 | 17 | 4 | 3 (8, 16, 24) | 1 | 0 | **1** |
| `lbu ×4 slli` | 5 | 47 | 24 | 5 | 1 (8) | 1 | 3 | **4** |
| `ld ld or ld ld` | 5 | 10 | 5 | 4 | 0 | 2 | 2 | **3** |
| `lui add sd` ×2 | 6 | 8 | 4 | 4 | 2 | 2 | 0 | **1** |

Nine of the eleven significant motifs have **zero genuinely free slots**. The n=8 form is fully
pinned: across all 17 occurrences the shifts are 8, 16 and 24 without exception and the four load
offsets are always `(b+1, b, b+2, b+3)` for a single varying base `b`:

```
lbu b+1 | lbu b+0 | lbu b+2 | lbu b+3 | slli 8 | or | slli 16 | slli 24
```

Those constants are the finding, not decoration. Shifts of exactly 8/16/24 over four consecutive
bytes are little-endian u32 assembly, which confirms the motif is the semantic operation and not a
coincidental opcode shape. The lemma takes **one** immediate.

The `lbu ×4 slli` motif inverts the usual trade-off and is the reason this decomposition matters.
It has the highest raw support of any motif — 47 sites in 24 instances — but shortening the window
admits sites whose load offsets follow *different* arrangements, so 3 of its 5 slots become
genuinely free. **Support bought by shortening a motif is support under a weaker invariant.** Raw
occurrence count would have ranked it first; it is the worst-parameterised entry on the list.

### What did not repeat usefully

The `zesu_decode_raw` prologue and epilogue are found — an 11-instruction
`addi sp,sp,-N; sd ra; sd s0..s8` at `0x10444` and `0x132a0`, and the matching
`ld ×9; addi sp,sp,N; ret` at `0x10508` and `0x13350` — but each occurs in only **2** owners. The
binary has 12 real stack frames with differing register sets, so ABI prologue/epilogue is not a
reuse opportunity here. Under the one measured rate, the prologue's payoff is 19 gross lines with
10 unestimated store steps: not worth a lemma.

## 7. Controls

| control | result |
|---|---|
| Shuffled corpus | 1 of 22 tests significant (n=2, p = 0.0144) — the nominal 5% rate |
| Planted motif | length 7, planted 9, recovered 9 |
| Scheduler invariance | 0 failures in 1194–1580 re-schedulings per length; order-dependent control fails 789–1560 of the same |
| Cross-target | 52 of 1453 mnemonic motifs shared with `reth-keccak` |

The shuffled-corpus result is the important one, and it did not come back at zero. One test in
twenty-two clearing 0.05 is what a correctly calibrated test produces on noise; a pipeline that
returned exactly zero would be evidence of a stuck test, not a good one.

The cross-target control separates cleanly. Every shared motif is a pure `sd`/`ld` run — spill,
reload, callee-saved save and restore, present in any compiled binary. The `lbu`/`slli`/`or` family
does not appear in `reth-keccak` at all. So the significant motifs above are SSZ decoding, not
compiler boilerplate, and a lemma for them serves this target rather than any target.

Observed owner support against the three nulls, at the family-wise maximum:

| n | observed | N1 max | N2 max | N3 max |
|---|---|---|---|---|
| 2 | 48 | 10 | 35 | **48** |
| 3 | 46 | 3 | 12 | 23 |
| 4 | 43 | 1 | 6 | 9 |
| 6 | 21 | 1 | 3 | 4 |
| 8 | 16 | 0 | 2 | 3 |
| 12 | 8 | 0 | 2 | 2 |

N3 (within-owner permutation) is by far the strongest null, as it should be — it is the one that
directly attacks the cross-instance sharing claim. At n=2 it matches the observed value exactly, so
2-grams are not significant. From n=4 up, the observed value exceeds the maximum over 5000
resamples of every null.

## 8. Scheduler invariance bought less than expected, except at n=8

The reconnaissance predicted that instruction scheduling fragments one idiom into many
sequence-distinct variants, and that grouping windows by dependence-graph class would recover a
large amount of reuse. **That prediction was mostly wrong.** Measured on the identical subset of
windows whose canonical form is exact:

| n | windows | distinct sequences | distinct DAG classes | class reduction | best owner support | best non-overlap |
|---|---|---|---|---|---|---|
| 4 | 2446 | 1049 | 859 | 18.1% | 43 → 43 | 88 → 90 |
| 6 | 2123 | 1259 | 1140 | 9.5% | 21 → 21 | 34 → 34 |
| 8 | 1927 | 1318 | 1245 | 5.5% | **16 → 19** | **17 → 27** |
| 12 | 1688 | 1295 | 1272 | 1.8% | 8 → 8 | 9 → 9 |

Class reduction falls as n grows, so the long-motif fragmentation at n≥10 is mostly genuinely
different code, not re-scheduling of the same code.

The exception is real and it lands on the motif that matters. At n=8 — exactly the length of the
complete four-byte read — grouping by dependence graph lifts the best motif from 16 owners to 19
and from 17 non-overlapping occurrences to **27, a 59% increase**. The compiler schedules the four
`lbu` loads and the `slli`/`or` combining tree differently at different call sites while emitting
the same dependence graph. A scheduler-invariant combinator would pay for itself on this one idiom
and essentially nowhere else.

Earlier per-length figures computed over unequal subsets overstated the reduction, because
budget-capped windows were excluded from the class count but not from the sequence count. The table
above uses one subset for both.

## 9. Shortlist

Ranked by measured value, not by p-value. Gross lines are
`(non-overlapping − 1) × register-write steps × 19`, using the only measured rate available; the
lemma authoring cost is unmeasured, so each entry states the break-even instead of a net.

Ranked by value *per unit of authoring cost*, which means support and immediate-argument count
together, not gross lines alone.

1. **Fixed-shift combine, n=4** (`slli or slli slli`). 21 sites in 20 instances, gross 1520 lines.
   **Zero immediate arguments** — shifts are 8/16/24 at every occurrence — and `memory` is empty,
   so it needs no memory frame. The cheapest lemma on the list to state, and nearly the broadest.
   Write this one first.

2. **Byte-load and first combine, n=6** (`lbu ×4; slli; or`). 34 sites in 21 instances, gross 3762
   lines, **one** immediate argument (the base offset; the shift is constant 8). The best support
   available at a one-argument cost.

3. **Four-byte little-endian read, n=8.** 17 sites in 16 instances, or **27 sites in 19 instances**
   stated over the dependence graph rather than the emitted order. Gross 2432 lines, one immediate
   argument, all steps register-write steps, memory reads only, no control transfer. Fewer sites
   than entry 2 but it pins all three shifts, so it is the form that states the whole u32 read as
   one semantic step. Take this over entry 2 if the proof wants the complete operation rather than
   the widest reuse.
   Sites: `0x105a0, 0x107d0, 0x111fc, 0x11220, 0x119f4, 0x11a58, 0x11ae0, 0x11ce4, 0x122b4,
   0x12334, 0x124f4, 0x127e8, 0x1295c, 0x12ae4, 0x12b5c, 0x12d70, 0x13380`.

4. **Large-offset stack store, n=6** (`lui; add sp; sd` twice). 8 sites in 4 instances, one
   immediate argument, gross 532 lines with **14 unestimated store steps** — the store shape has no
   measured rate, so this entry's value is unknown and probably understated.

5. **Stack reload and combine, n=5** (`ld ld or ld ld`). 10 sites in 5 instances, gross 855 lines,
   but **3 immediate arguments** and no constant slots. Weakest invariant on the list.

Entries 1–3 are the same idiom family at three lengths. Write one of them, not all three.

**Not recommended: `lbu ×4; slli` at n=5**, despite having the highest raw payoff on the list (47
sites, 24 instances, gross 4370 lines). Three of its five immediate slots are genuinely free, so
its extra support comes under a materially weaker invariant than entries 2 and 3. It is the entry a
frequency-ranked list would have put first.

## 10. Limitations

- **One measured rate.** −19 lines per register-write step is the only authoring figure in
  `PLAN_PROOF_PATTERNS.md` that was measured. Stores, branches and transfers are counted as
  unestimated. Entry 5 above is the case where that matters most.
- **Lemma cost is not modelled.** Every payoff is gross. A lemma that costs more than its gross
  figure is a loss, and nothing here says what one costs.
- **`liveOutAtExit` is a union across occurrences**, so it bounds rather than states how much a
  lemma must expose.
- **Budget-capped canonicalisation.** 70–94 windows per length at n≥6 hit the individualisation
  budget and are marked approximate; they are excluded from class counts, which is why §8 recomputes
  on a common subset.
- **Corpus is `zesu_decode_raw` plus `memcpy`/`memmove`.** `zesu_raw_sink_checksum` (451
  instructions) has no owner metadata and is outside every number here.
- **What the L3 token drops.** Immediates (recovered separately in §6), branch targets, and the
  identity of the memory object a load or store touches. Access width and signedness survive,
  because they are encoded in the mnemonic — `lbu`, `lb` and `lw` are distinct at L3 but collapse
  to `LOAD` at L5.
- **Motifs are linear, not path-sensitive.** A window is consecutive addresses inside one
  straight-line segment. Nothing here searches CFG paths, so an idiom split across a branch is
  invisible to this analysis.
- **Nothing is proved.** This ranks candidates. No `Seg` lemma is written, and no claim about Level
  3 or Level 4 follows from it.

## 11. Incidental finding

21 `MULDIV` instructions (`mul`, `divu`, `remu`, `remuw`, `divuw`, …) have no class lemma in
`BinaryFv/Zesu/MachineExecution/InstructionClassSteps.lean`. Every other mnemonic in the corpus maps
to an implemented class. The tool names `MULDIV` separately rather than folding it into `RTYPE` so
the gap is visible.

