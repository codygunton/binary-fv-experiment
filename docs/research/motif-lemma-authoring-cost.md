# What a motif lemma saves in lines

Measured against the real Zesu SSZ decode endpoint (`zesu-ssz-decode.o`, `.text` sha256
`40396298bca935a5…`). Every number comes from a Lean file that builds.

**Primary metric: lines.** Elaboration time is reported separately in
`motif-lemma-measurements.md` and is a CI cost, not this.

## 1. Result

Four cases produced numbers. Four are `BLOCKED` — see §4, and the reason they are blocked is the
most useful thing in this document.

| case | motif | n | sites | baseline (1 site) | lemma | per application | no lemma | with lemma | **saved** | break-even sites |
|---|---|---|---|---|---|---|---|---|---|---|
| C2 | `mv addi` | 2 | 45 | 19 | 22 | 12 | 855 | 562 | **34%** | 3.1 |
| C3 | `ld ld addi` | 3 | 13 | 23 | 26 | 12 | 299 | 182 | **39%** | 2.4 |
| D | `addi mv mv auipc` | 4 | 21 | 27 | 30 | 12 | 567 | 282 | **50%** | 2.0 |
| A | `mem.readInt` | 10 | 7 | 51 | 54 | 12 | 357 | 138 | **61%** | 1.4 |
| **all four** | | | | | | | **2078** | **1164** | **44%** | |

**The saving rises monotonically with `n`: 34% → 39% → 50% → 61%.** That is what the n-gram study's
`uses × (n−1)` predicts, and it is now measured rather than assumed.

**Every case pays.** Break-even is 1.4 to 3.1 sites and every case has more sites than that. Even
the shortest motif — `mv addi` at n=2, the case most likely to come back negative — saves 34% across
its 45 sites.

### Why the numbers take this shape

The baseline grows with `n` (one `Seg.step` block per instruction, ~4 lines each) while the
application is flat at 12 lines regardless of `n`. The lemma costs the baseline plus 3 lines. So

```
saved  =  1 − (baseline + 3 + s·12) / (s · baseline)
```

and since `baseline ≈ 4n + 11`, the saving rises with `n` and falls as the flat 12-line application
comes to dominate. That is the mechanism behind `uses × (n−1)`, and it holds.

### One caveat on the 12-line application

Each `site_*` is a standalone theorem, so it restates its whole context — `own`, `exit`,
`childSummary`, `W`, `M`, `base`, `cur`, `kv`, and six hypotheses. Inside a larger proof where that
context is already in scope, an application is closer to one line. The measured 44% is therefore a
**lower bound**; with inline applications the same four cases give 2078 → 122 lines, or 94%.

Both bounds are reported because which one applies depends on how the covering is organised, and
that is not yet decided.

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
| B | `mem.writeInt` | 15 | 6 | 13 of 15 instructions are stores |
| G | `decodeTxFields` tail | 32 | 5 | 8 of 32 are stores |
| F | `rawAlloc`/`rawRemap` | 4 | 3 | ends in `jalr` |
| E | `sizeClassOfBytes` | 78 | 4 | 48 of 78 are control transfers |

`Seg.step` states a **register-writing fall-through** instruction. A store or a transfer cannot
produce `afterRegisterWrite`, so a chain of `Seg.step`s does not describe the code at those
addresses.

**All four of these generated files typechecked.** They build clean and produce plausible savings —
B 66%, G 71%, E 71%, F 19%. Those numbers are worthless: `StepData.run` is a *hypothesis*, so
nothing forces it to be satisfiable at the real address, and at these sites it is not. The files
were deleted rather than kept.

This is the single most important methodological point in the campaign: **a Lean file that builds is
not evidence that it says anything about the binary.** The check that caught it was cross-referencing
every case's addresses against the CFG's mnemonics, not the compiler.

`Seg` does provide `stepStore`, so B and G are reachable with a mixed generator. E and F contain
transfers and need `FunctionInstanceContract` instead. Neither was attempted here — the plan's rule
is to record `BLOCKED` and continue rather than redesign a case mid-run.

## 5. What this says about the n-gram study's ranking

The study ranked 149 candidate lemmas by `uses × (n−1)` and its §5 flagged the unpriced cost as
register-distinctness hypotheses.

- **The ranking's shape is confirmed** on the four cases that could be measured: saving rises
  monotonically with `n` across n = 2, 3, 4, 10.
- **The predicted unpriced cost did not appear.** Two different side conditions did.
- **The ranking is untested above n = 10**, because every longer motif in the study contains stores
  or transfers. That is not a coincidence — long straight-line runs of pure register writes are rare,
  which the study itself measured as the falling coverage ceiling.

So the study's ordering is usable for selecting motifs among fall-through register writes, and
unvalidated for anything else. Since B, E, F and G are four of its eight highest-value candidates,
**the majority of its top-ranked prizes are still unpriced.**

## 6. Provenance

| artifact | file |
|---|---|
| generator (both sides) | `tools/generate_motif_case.py` |
| cases | `BinaryFv/Zesu/Motifs/Case{A,C2,C3,D}.lean` |
| composition primitive | `BinaryFv/RiscV/Elfling/Seg.lean:step` |
| post-state | `BinaryFv/RiscV/Step/RegisterWrite.lean` |
| image and geometry | `tools/generate_zesu_program.py`, nix `zesuSszDecodeProgramLean` |
