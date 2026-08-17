# Repeated patterns in the hLevel2 proof, and what they cost

Analysis of `BinaryFv/Zesu/MachineExecution` at `origin/main` **`9935fb21`** (PR #96, the merged
`root_compliance hLevel2`). Read-only: this report changes no proof code.

The n-gram technique was built for the compiled instruction stream. It applies unchanged to the
proof text, and the proof text is where the immediate savings are. This report measures them and
costs each one.

---

## 1. The rate

Proof cost scales with the RISC-V covered, so lines per instruction is the number that matters.

| | |
|---|---|
| `BinaryFv/Zesu` total | 33,644 lines |
| `BinaryFv/Zesu/MachineExecution` | **24,719 code lines** in 683 declarations |
| distinct instruction addresses named | **488** |
| **rate** | **51 lines per instruction** |
| the whole 4435-instruction endpoint at that rate | **≈226,000 lines** |
| `Level1WriteSuccessSteps.lean` alone | 17,243 lines |

The rate was 33 lines per instruction on the pre-merge branch and is now 51. That is not a
regression in quality — the newer code proves harder things — but it does mean the extrapolation
moved from ≈146,000 lines to ≈226,000.

**Composition is 79.5% of the corpus.** Classifying each declaration by how many distinct addresses
it names:

| bucket | declarations | lines | share |
|---|---|---|---|
| names no address (generic) | 208 | 2,823 | 11.3% |
| names one address | 90 | 2,276 | 9.1% |
| **names two or more (composition)** | **384** | **19,776** | **79.5%** |

## 2. The proof text repeats as heavily as the binary

One item per code line, normalised, matched only inside a single declaration — a pattern may not
cross a `theorem`, because a lemma extracted from it would have to be applied inside one.

At `L2_locals` (hex addresses, numerals, and state/step local names abstracted):

| n | distinct | repeated | most-repeated | lines covered | share |
|---|---|---|---|---|---|
| 2 | 13,829 | 2,578 | 363 | 12,968 | **52.5%** |
| 4 | 16,141 | 2,040 | 159 | 9,596 | **38.8%** |
| 8 | 16,788 | 1,310 | 41 | 6,912 | **28.0%** |
| 16 | 15,488 | 600 | 19 | 3,984 | **16.1%** |

Coverage is a **greedy disjoint** cover. A run of five identical lines gives four overlapping 2-line
windows, and counting all four would report more covered lines than the corpus holds.

### The controls pass decisively

| n | real | shuffled within declaration | ratio |
|---|---|---|---|
| 2 | 52.5% | 15.7% | 3.3× |
| 4 | 38.8% | 0.8% | 50× |
| 6 | 32.1% | 0.0% | 661× |
| ≥8 | 28.0% | **0.0%** | ∞ |

Shuffling preserves each declaration's length and its multiset of lines, and destroys only the
order. From n=6 up the shuffled corpus returns nothing. **The repetition is real order structure,
not an artefact of some lines being common.**

Planted control: a synthetic 7-line pattern injected 9 times into shuffled text was recovered 9
times, at the right length. **PASS.**

### The cascade — the hierarchical greedy strategy, on proof text

At each length, cover **every** pattern that still repeats, taking the most-placed first; then drop
to n−1 on what remains. The strategy does not stop at one pattern per length.

**Where to stop is a cost question, and the data answers it.** A pattern is worth a lemma only if
the lines it recovers exceed the lines the lemma costs to author. Recovered is
`sites × (n − 1)`, because one copy stays inside the lemma. The measured authoring cost of a
class-style lemma on this target is **39 to 83 lines** (`InstructionClassSteps.lean`, six
declarations, 391 code lines).

| band | lemmas | sites | lines recovered | **per lemma** | cumulative lemmas | cumulative cover |
|---|---|---|---|---|---|---|
| n ≥ 64 | 1 | 3 | 261 | **261.0** | 1 | 1.1% |
| 32–63 | 10 | 20 | 918 | **91.8** | 11 | 4.9% |
| 16–31 | 53 | 173 | 3,404 | **64.2** | 64 | 19.3% |
| 10–15 | 77 | 190 | 2,105 | 27.3 | 141 | 28.6% |
| 8–9 | 55 | 143 | 1,043 | 19.0 | 196 | 33.4% |
| 6–7 | 71 | 167 | 901 | 12.7 | 267 | 37.7% |
| 5 | 69 | 167 | 668 | 9.7 | 336 | 41.1% |
| 4 | 105 | 250 | 750 | 7.1 | 441 | 45.2% |
| 3 | 165 | 427 | 854 | 5.2 | 606 | 50.3% |
| 2 | 301 | 753 | 753 | 2.5 | 907 | 56.4% |

**Stop at n = 16.** Down to that band a lemma returns 64 lines and costs 39 to 83, so the head of the
curve pays for itself and little more. Below n = 16 every band loses money: at 10–15 a lemma returns
27 lines against the same cost, and at n = 2 it returns 2.5. The cascade's own coverage figure keeps
rising to 56.4%, but **the coverage below n = 16 is not recoverable by one lemma per pattern at any
price.** Reaching it needs a different mechanism, and §5 names one.

**The proof text is more fragmented than the binary.** The same cascade on the instruction stream
reaches 74.2% with 149 patterns; here it takes 907 patterns to reach 56.4%.

## 3. Where a lemma exists to be extracted

Patterns ranked by lines recoverable, `(disjoint sites − 1) × n`, keeping one copy inside the lemma:

| lines | n | sites | owners | representative site |
|---|---|---|---|---|
| **546** | 14 | 40 | 40 | `Level0MainSteps.writeSuccessMemcpyCallBaseStep` |
| **510** | 15 | 35 | 35 | `Level0MainSteps.main_li_zero_step` |
| 396 | 22 | 19 | 19 | `Level0MainSteps.writeSuccessMemcpyCallBaseStep` |
| 366 | 2 | 184 | 80 | `Level0MainSteps.writeSuccessMemcpyCallBaseStep` |
| 365 | 5 | 74 | 74 | `Level0MainSteps.writeSuccessMemcpyCallBaseStep` |
| 328 | 2 | 165 | 41 | `Level1WriteSuccessSteps.writeSuccessAllocateFrame` |
| 322 | 23 | 15 | 15 | `Level0MainSteps.main_li_zero_step` |
| 288 | 16 | 19 | 19 | `Level0MainSteps.main_success_exit_call_step` |

Every top pattern has **one owner per site**. These are not loops inside one theorem; they are the
same block written out in dozens of different theorems.

---

## 4. The opportunities, costed — three that survive, one retracted

Read this section together with §5. Everything here is a **repetition** candidate: repeated text
lifted into a lemma and applied at each site. §5 describes the stronger mechanism the instrument
cannot rank, and revises the shape of the fix for Opportunities 2 and 3.

### Opportunity 1 — class-layer adoption. **RETRACTED. The measurement does not support it.**

An earlier draft of this report called this the largest prize, at 6,326 lines. **That claim is
withdrawn.** Two errors and one measurement retire it.

**First error — the class layer has seven lemmas, not five.** `configuredAuipcStep` and
`configuredJalrCallStep` live in `Level0MainSteps.lean`, not in `InstructionClassSteps.lean`, and the
first count missed them. They are the second and third most used lemmas in the layer.

| lemma | uses | where declared |
|---|---|---|
| `configuredRegisterWriteStep` | 29 | `InstructionClassSteps.lean` |
| `configuredAuipcStep` | 22 | **`Level0MainSteps.lean`** |
| `configuredJalrCallStep` | 21 | **`Level0MainSteps.lean`** |
| `configuredDwordStoreStep` | 7 | `InstructionClassSteps.lean` |
| `configuredRetStep` | 4 | `InstructionClassSteps.lean` |
| `configuredJStep` | 3 | `InstructionClassSteps.lean` |
| `configuredDwordLoadStep` | 3 | `InstructionClassSteps.lean` |

**Second error — the corrected counts are much smaller.** Against all seven names:

| | theorems | lines |
|---|---|---|
| mention `try_step` | 226 | 8,251 |
| use a class lemma (all 7) | **86** | **3,097** |
| do not | **140** | **5,154** |

So adoption is 38% of stepping theorems, not one fifth.

**The measurement that retires it.** Normalise by instructions covered, which is the metric this
whole effort turns on:

| group | theorems | lines | address mentions | **lines per address** |
|---|---|---|---|---|
| uses a class lemma | 86 | 3,097 | 485 | **6.4** |
| hand-rolled | 140 | 5,154 | 932 | **5.5** |

**A theorem that uses the class layer costs more lines per instruction, not fewer.** The point
estimate goes the wrong way. The comparison is confounded — the two groups do not step the same
instruction shapes — so the right reading is not "the class layer is harmful" but **"there is no
evidence that adopting it reduces lines per instruction, and what evidence exists points the other
way."**

**Why the hypothesis failed.** The class layer is a per-instruction tool, and the hand-rolled lines
are not per-instruction cost:

| hand-rolled theorems by addresses named | theorems | lines |
|---|---|---|
| 0 addresses | 11 | 176 |
| 1 address | 12 | 496 |
| 2–4 addresses | 14 | 409 |
| **5–9 addresses** | **89** | **3,215** |
| 10 or more | 14 | 858 |

**79% of the 5,154 lines sit in theorems that name five or more addresses.** Those theorems compose;
they do not step one instruction. A per-instruction lemma cannot reach their bulk, whatever its
design. The composition layer is the target, which is Opportunity 4 and `Seg`, not this.

### Opportunity 2 — the decode-context block, 40 sites, no lemma

The most valuable single pattern: **14 lines at 40 disjoint sites in 40 distinct theorems, across 4
files** (`Level0MainSteps` 19, `Level2RuntimeLeaves` 14, `Level1WriteSuccessSteps` 4,
`Level1DecodeInputSteps` 3). **546 lines recoverable.**

```lean
have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
    some Privilege.Machine := by
  calc
    _ = state.regs.get? cur_privilege := by
      simpa [tryStepControlFlowAfterIncrement] using
        writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
    _ = some Privilege.Machine := configured.normal.2.1
have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = …
```

These are the two register reads `decode_run` consults, so every site that discharges a `decode`
premise needs them. `privilegeAfter` is mentioned 251 times and `seccfgAfter` 248 times, in 194
theorems.

**The pre-wipe design had a lemma for exactly this.** `decoderDecodeContextOfDecoderAgree` at
`d0f50581`, whose note read: *"The two post-increment register reads `decode_run` consults. Every
call site of the class step lemmas below opens by destructuring this, which is what makes their
`decode` premise automatic."* Main has no equivalent.

**The quantified lemma this re-derives already exists.** `ConfiguredMachine.lean` declares

```lean
theorem agree_tryStepIncrement_instructionPreserved (state : State) :
    Agree instructionPreserved state (tryStepControlFlowAfterIncrement state)
```

`instructionPreserved r` is `platformPreserved r ∧ r ≠ x1`, and `platformPreserved` lists
`cur_privilege` and `mseccfg` among its eighteen registers. **So this one statement, quantified over
every preserved register, already implies both `privilegeAfter` and `seccfgAfter`.** The 14-line
`calc` block at each of the 40 sites is a hand re-derivation of two instances of it.

The compact idiom also already exists, in `AbstractPremise.lean:122`:

```lean
((agree cur_privilege (by simp [platformPreserved])).trans privilegeRead)
```

That is one line where the site writes six.

**Cost, and the better shape of the fix.** Do not add a lemma and apply it 40 times. Extend
`ConfiguredMachinePre.stepContext`, which already exists and already returns four post-increment
facts, to return these two as well. Every site that calls it then gets them at **zero** cost rather
than one line, and no site can derive them wrongly. See §5 for why that distinction matters more than
the 546 lines.

**What could go wrong:** the 40 sites are verbatim-identical after abstracting only local names, so
the risk is low. Two real cautions. `configured.normal.2.1` is a projection path into a structure, so
check that every site projects the same way. And a second increment function exists —
`tryStepStoreAfterIncrement`, used at `Level0MainSteps.lean:594` — so the store path needs its own
instance of the same treatment.

### Opportunity 3 — the region-membership proof, 182 sites

`(by unfold writeSuccessParentPc; exact ⟨(0x…, 0x…), by …, by …, by …⟩)` appears **182 times across
58 theorems** in `Level1WriteSuccessSteps.lean`, at roughly two lines each — **≈364 lines**, and it
is the n=2 pattern with 184 sites in the table above.

A site reads, verbatim, at `Level1WriteSuccessSteps.lean:296`:

```lean
(by unfold writeSuccessParentPc; exact
  ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
```

**A tactic for exactly this shape exists and has zero uses.** `BinaryFv/ProofProgress/OwnedPc.lean`
declares the `owned_pc` macro, whose own doc reads *"Prove literal membership in a generated
function's ranges, or literal nonmembership in its exits."* Outside its own file it is used **0
times**.

**Cost, and the better shape of the fix.** A lemma parameterised by the address pair leaves a
one-line application at every site. A tactic takes no arguments at all, so it leaves one token.
Prefer the tactic: a sibling of `owned_pc` for `writeSuccessParentPc` is roughly 15 lines and reduces
each of the 182 sites to `by owned_region`.

**What could go wrong:** `owned_pc` targets `functionInstanceExecutionPcs` on a generated
`FunctionInstance`, and `writeSuccessParentPc` is a bespoke region predicate. So `owned_pc` will not
apply unchanged, and the claim here is that its *pattern* transfers, not its code. Expect roughly
half of the 364 lines from a lemma, and nearly all of them from a tactic.

### Opportunity 4 — motif lemmas over the instruction runs

Measured on branch `motif-lemmas`: **32% of lines saved at n=2 rising to 70% at n=32**, break-even
between 1.1 and 3.3 sites, five cases that build. Composition is 79.5% of this corpus, which is the
bucket those lemmas reduce.

**Cost:** already measured. The blocker is not the technique but its reach — three of eight cases
were blocked, two on control transfers needing `FunctionInstanceContract`, one because the
`mem.writeInt` instances are not contiguous.

---

## 5. Two ways to remove a repeated obligation, and why the instrument only sees one

Every opportunity above assumes one mechanism: find repeated text, lift it into a lemma, apply the
lemma at each site. Call that **repetition**. A second mechanism exists, and it is stronger:
restructure the argument so the obligation is proved once for all sites and **never arises at a site
again**. Call that **quantification**.

The difference is not stylistic. It is the difference between two cost curves. With `s` sites and a
block of `n` lines:

| mechanism | total cost | cost of one more site |
|---|---|---|
| written out at every site | `n · s` | `n` |
| **repetition** — a lemma applied `s` times | `n + a·s`, where `a` is the application | `a` |
| **quantification** — proved once, never restated | `n` | **0** |

Repetition shrinks the constant. Quantification removes the dependence on `s` altogether. Only the
second one stops the proof growing with the binary, which is the property this whole effort needs.

**This codebase already has three quantification mechanisms, all of them working.**

1. **Carry the fact in the hypothesis bundle.** `ConfiguredMachinePre` holds `normal`,
   `retiredCounter`, `mstatusStoreMode`, `seccfgPresent`, `htifDisabled`, `platform` and
   `landingPad`. Any fact inside it costs a site nothing, because a site reads it as a projection.
2. **Make the premise an `autoParam`.** The class layer does this 37 times. The site writes no
   argument, and the elaborator discharges it.
3. **Quantify the transport once.** `agree_tryStepIncrement_instructionPreserved` states that the
   counter increment preserves *every* preserved register. It is one statement, not eighteen, and not
   one per site.

**`privilegeAfter` is a repetition where a quantification already existed.** The fact is that
`cur_privilege` still reads `Machine` after the counter increment. That is invariant preservation,
and mechanism 3 already proves it in general. Instead, 40 theorems each re-derive two instances by
hand, in 14 lines. The correct fix puts the two reads into what `stepContext` returns — mechanism 1 —
and the per-site cost becomes zero instead of one line.

**The instruction the user gave is the right test.** Nobody would prove, for each machine step, that
the configuration matches `RV64IM_Zicclsm`. You state it once as an invariant and show every step
preserves it. `ConfiguredMachinePre` is precisely that construction, and every obligation that
belongs inside it and is instead re-derived per site is the same mistake at smaller scale.

**This is a blind spot in the instrument, and it biases the ranking.** The cascade ranks repeated
*text*. A quantification makes text vanish that the cascade never flagged, because after the
restructuring the obligation is written nowhere. So the instrument systematically over-values
repetition and under-values quantification. Read §3 and §4 as a ranking of repetition candidates
only. **The cascade's tail below n = 16, which no lemma can pay for, is exactly where
quantification is the only mechanism left.**

The practical rule this yields, for each candidate: before writing a lemma, ask whether the
obligation is an invariant of the machine or of the region. If it is, it belongs in the bundle or in
an `autoParam`, and a lemma applied `s` times is the wrong fix even though it is the fix the
line-count ranking recommends.

## 6. What this analysis cannot see

- **A share is not a saving.** 52.5% of lines sit in a repeated 2-line pattern. That says the text
  repeats; it does not say a lemma can absorb it. Section 4 costs the four cases where a specific
  lemma is nameable. The rest of the 56.4% cascade coverage has no named extraction and should not
  be counted as recoverable.
- **The normaliser can merge lines that differ in ways that matter.** The rules are listed in
  `tools/ngram_lean.py` so a reader can judge them. The top pattern was spot-checked by hand at its
  first site in `Level0MainSteps.lean:362` and is verbatim as reported.
- **No α analogue.** In machine code, α renaming maps registers to roles by first use, so two
  windows differing by a consistent renaming become equal. Lean identifiers have no comparable
  positional structure. Inventing one would produce a number that looks like the machine-code figure
  and means something else. The gap is left open.
- **Opportunity 1 was wrong, and the compiler could not have caught it.** Its 6,326 lines were an
  upper bound that this report first presented as the top prize. Two name-set errors and one
  normalisation by instructions covered retired it. **A count of repeated lines is not evidence that
  the lever which removes them works.** See §4, Opportunity 1.
- **Repetition is measured; quantification is not.** §5 states the bias. The cascade cannot rank a
  restructuring, because after the restructuring there is no text left to match.
- **Elaboration time is not measured here.** It is a CI cost, reported separately in
  `motif-lemma-measurements.md`, and it moves opposite to line count: an `autoParam` removes lines
  without removing the work the kernel does.

---

## 7. Method and reproduction

`tools/ngram_lean.py` supplies the four target-specific concerns — item, segment, levels, owner —
and imports `maximal_repeats`, `non_overlapping` and `smallest_period` from `tools/ngram_motifs.py`.

**Deviation from the plan, recorded:** the plan called for a shared `TokenStream` record that both
the machine-code adapters and the proof-text adapter build. What exists is a `ProofStream` with
those four fields plus imports of the leaf functions. The covering in `census` is a re-implementation
rather than a reuse of the dashboard's cascade. The upside is that `ngram_motifs.py` was not touched
at all, which makes the regression check trivially true; the downside is that the two coverings are
now separate code and could drift. **Unify them before either is changed again.**

```bash
# the census, all four levels, with both controls
python3 tools/ngram_lean.py BinaryFv/Zesu/MachineExecution --all-levels --out-json out/lean.json

# regression: the machine-code instrument must be byte-identical
python3 tools/ngram_dashboard.py --cfg result-zesu-ssz-decode-cfg/zesu-cfg.json \
  --out-json out/dash.json --out-html out/dash.html
```

Line counts exclude blanks and comments, by the same rule everywhere. Verification run for this
report: regression **PASS** (byte-identical), shuffled control **PASS**, planted control **PASS**
(9 of 9), hand spot-check **PASS**.

## 8. What the branch cleanup lost — a full audit

The `ssz-ngram-study` branch had been deleted locally and on `origin`. Its tip, `d51c280b`, survived
unreferenced in the object store, and this report's tooling and the study's two reports were
recovered from it. **Unreferenced objects do not survive a `git gc`**, so I created the branch again
at `d51c280b` and pushed it.

That prompted the wider question, so I audited the whole object store rather than the one branch.

| | |
|---|---|
| unreachable commits | **2,919** |
| of those, tips (no unreachable child) | **262** |
| tips whose tree is byte-identical to a reachable commit | **259** |
| tips holding content found nowhere reachable | **3** |

Most of the 2,919 are ordinary debris: `git stash` entries, `WIP on <branch>` snapshots,
worktree-cleanup commits from 2026-08-07, and pre-amend versions of commits whose final form is on
`main`. The tree-identity check is the useful one, because a commit whose tree already exists under a
live ref holds nothing that can be lost.

**Three tips remained. Two files are the whole loss** — the unfinished `read_input` proof, which
exists in two different unreachable versions:

| file | at `647eb2f0` (the archive) | at `5d5f9e7a1` (a later variant) |
|---|---|---|
| `BinaryFv/Zesu/MachineExecution/ReadInputProof.lean` | 142 lines | 109 lines |
| `BinaryFv/Zesu/MachineExecution/ReadInputSteps.lean` | 208 lines | 156 lines |
| **total** | **350 lines** | **265 lines** |

The deletion was deliberate. Commit `647eb2f0` is titled *"Archive unfinished read-input proof"* and
it grew both files by 92 lines before they left the tree. **But the archive was never given a ref, so
"archived" meant "deleted at the next `git gc`".** The other content in those three tips is `deps/`
submodule pointers, which are commit identifiers rather than files and are not lost.

**Verdict: 350 lines of deliberately-archived, unfinished proof were the only casualty.** Nothing any
live branch depends on was lost, and no reachable history is missing. I gave both versions a ref:

| tag | commit | holds |
|---|---|---|
| `archive/read-input-unfinished` | `647eb2f0` | the archive commit, 350 lines |
| `archive/read-input-unfinished-variant` | `5d5f9e7a1` | the later 265-line variant |

This branch also carries copies of `docs/research/zesu-ssz-endpoint-motifs.md` and
`docs/research/binary-ngram-motifs.md` against a repeat of the same failure.

**The general lesson.** "Archive" in a commit message is not an archive. Three separate pieces of work
on this project — the n-gram study branch, the `read_input` proof, and this report's own tooling —
were one `git gc` from permanent loss while their commit messages said they were kept. Only a ref
keeps anything.
