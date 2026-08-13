# What a motif lemma saves in lines

Measured against the real Zesu SSZ decode endpoint (`zesu-ssz-decode.o`, `.text` sha256
`40396298bca935a5…`). Every number comes from a Lean file that builds.

**Primary metric: lines.** Elaboration time is reported separately in
`motif-lemma-measurements.md` and is a CI cost, not this.

## 1. Result

Five cases produced numbers. Three are `BLOCKED` — see §4, and the reason they are blocked is the
most useful thing in this document.

| case | motif | n | sites | baseline (1 site) | lemma | per application | no lemma | with lemma | **saved** | break-even sites |
|---|---|---|---|---|---|---|---|---|---|---|
| C2 | `mv addi` | 2 | 45 | 20 | 23 | 13 | 900 | 608 | **32%** | 3.3 |
| C3 | `ld ld addi` | 3 | 13 | 24 | 27 | 13 | 312 | 196 | **37%** | 2.5 |
| D | `addi mv mv auipc` | 4 | 21 | 28 | 31 | 13 | 588 | 304 | **48%** | 2.1 |
| A | `mem.readInt` | 10 | 7 | 52 | 55 | 13 | 364 | 146 | **60%** | 1.4 |
| G | `decodeTxFields` tail | 32 | 5 | 136 | 139 | 13 | 680 | 204 | **70%** | 1.1 |
| **all five** | | | | | | | **2844** | **1458** | **49%** | |

**The saving rises monotonically with `n`: 32% → 37% → 48% → 60% → 70%**, across a 16× range in
`n`. That is what the n-gram study's
`uses × (n−1)` predicts, and it is now measured rather than assumed.

**Every case pays.** Break-even is 1.1 to 3.3 sites and every case has more sites than that. Even
the shortest motif — `mv addi` at n=2, the case most likely to come back negative — saves 32% across
its 45 sites.

Case G is the important one: n=32, a **mixed** chain of 25 register writes, 4 stores and 3 more
register writes, composed with `Seg.step` and `Seg.stepStore`. It extends the validated range from
n=10 to n=32 and it is the only case whose break-even is near 1 — a lemma there pays at two sites.

### Why the numbers take this shape

The baseline grows with `n` — one composition block per instruction, ~4 lines each — while the
application is flat at **13 lines regardless of `n`**. The lemma costs the baseline plus 3 lines. So

```
saved  =  1 − (baseline + 3 + s·13) / (s · baseline),    baseline ≈ 4n + 12
```

The saving rises with `n` because the baseline does and the application does not. That is the
mechanism behind `uses × (n−1)`, and the five measured points fit it.

### One caveat on the 12-line application

Each `site_*` is a standalone theorem, so it restates its whole context — `own`, `exit`,
`childSummary`, `W`, `M`, `base`, `cur`, `kv`, and seven hypotheses. Inside a larger proof where
that context is already in scope, an application is closer to one line. The measured **49% is
therefore a lower bound**; with one-line applications the same five cases give 2844 → 366 lines, or
**87%**.

Both bounds are reported because which applies depends on how the covering is organised, and that
is not decided.

## 2. Side conditions the study's model does not price

Both were found by writing the lemma. Neither appears in `uses × (n−1)`.

- **`adv` — `Sail.BitVec.addInt q 4 = q + 4`.** The concrete baseline gets this by `decide`, because
  its addresses are literals. A lemma over a symbolic `start` cannot, so it becomes a hypothesis.
  Cost: one argument per site, not per instruction. Small, but real, and it exists only because of
  the generalisation.
- **Address association.** Writing the addresses as `start + 4k` fails: `(start + 4k) + 4` and
  `start + 4(k+1)` are not definitionally equal for `BitVec`, so every step needs a rewrite. Nesting
  them as `((start + 4) + 4) + …` avoids it entirely. This is a constraint on how a motif lemma may
  be *stated*, discoverable only by stating one.

Neither is a register-distinctness hypothesis, which is what the study predicted would be the
unpriced cost. Those did not appear, because `Seg.step` takes `destination : W dest` and
`keep : RegsOutside …` as parameters that the caller already carries per segment.

## 3. Method

Both sides of every comparison come from one generator, `tools/generate_motif_case.py`, so neither
can be terser than the other by accident. Each case file holds:

1. `baselineChain` — `n` chained `Seg.step`s at one concrete site. What an author writes today.
2. `motifCase` — the same thing stated once, over a symbolic `start`.
3. `site_*` — one application per site, at every listed site.

The per-instruction `Runs (try_step …)` premises are arguments **on both sides**. They are per-site
semantics that neither a chain nor a lemma removes, so counting them on one side would rig the
result. What is measured is the *composition* — which `PLAN_PROOF_PATTERNS.md` identified as the
remaining bulk that the step-layer toolkit does not reach.

Line counts exclude comments and blanks, by the same rule everywhere:
`grep -vE '^\s*(--|/-|\*|-/)?\s*$'`.

## 4. BLOCKED, and why it matters

| case | motif | n | sites | reason |
|---|---|---|---|---|
| B | `mem.writeInt` | 15 | 6 | **its instances are not contiguous** — see below |
| F | `rawAlloc`/`rawRemap` | 4 | 3 | ends in `jalr`; `Seg` cannot state a transfer |
| E | `sizeClassOfBytes` | 78 | 4 | 48 of 78 are control transfers |

**Case B is not a linear motif at all.** Its `mem.writeInt` instances are non-contiguous: the
instance entered at `0x2cc0` holds 16 program counters spread over 36 instruction slots, and the six
instances interleave — four of the six site pairs overlap. The scheduler wove them together. There
is no 15-instruction linear window at those addresses to state a lemma over, so the address list the
campaign inherited for Case B does not describe a motif.

That is a defect in how the case was specified, not in the lemma: the list came from *instance
bodies*, and an instance body is a set of program counters, not a run.

`Seg.step` states a **register-writing fall-through** instruction. A store or a transfer cannot
produce `afterRegisterWrite`, so a chain of `Seg.step`s does not describe the code at those
addresses.

**All of these generated files typechecked** on the first attempt, before the store and transfer
kinds were handled. They built clean and produced plausible savings — B 66%, G 71%, E 71%, F 19%.
Those numbers were worthless: `StepData.run` is a *hypothesis*, so nothing forces it satisfiable at
the real address, and at those sites it was not.

G was then done properly with a mixed `Seg.step`/`Seg.stepStore` chain and is now a measured case at
70%. B, E and F remain blocked. The lesson stands for all four.

This is the single most important methodological point in the campaign: **a Lean file that builds is
not evidence that it says anything about the binary.** The check that caught it was cross-referencing
every case's addresses against the CFG's mnemonics, not the compiler.

`Seg.stepStore` reached G. E and F contain transfers and need `FunctionInstanceContract` instead;
B needs a non-linear motif form that does not exist.

## 5. What this says about the n-gram study's ranking

The study ranked 149 candidate lemmas by `uses × (n−1)` and its §5 flagged the unpriced cost as
register-distinctness hypotheses.

- **The ranking's shape is confirmed** on the five cases that could be measured: saving rises
  monotonically with `n` across n = 2, 3, 4, 10, 32.
- **The predicted unpriced cost did not appear.** Two different side conditions did.
- **The ranking now holds to n = 32**, once stores are composed with `Seg.stepStore`. Case G is a
  mixed chain and behaves exactly as the trend predicts.
- **Control transfers remain outside the measurement.** E and F need `FunctionInstanceContract`, and
  E is the study's single largest prize at 7.0% of the binary.

So the study's ordering is confirmed over `n` from 2 to 32 for straight-line code, and unvalidated
for motifs containing control transfers. Case B shows a separate hazard the study's site counts do
not expose: an "instance" is a set of program counters, and the scheduler may interleave several so
that no linear window exists.

## 6. Provenance

| artifact | file |
|---|---|
| generator (both sides) | `tools/generate_motif_case.py` |
| cases | `BinaryFv/Zesu/Motifs/Case{A,C2,C3,D,G}.lean` |
| composition primitive | `BinaryFv/RiscV/Elfling/Seg.lean:step` |
| post-state | `BinaryFv/RiscV/Step/RegisterWrite.lean` |
| image and geometry | `tools/generate_zesu_program.py`, nix `zesuSszDecodeProgramLean` |
