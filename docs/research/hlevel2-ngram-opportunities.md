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

Longest repeated length first, cover its sites disjointly, drop to n−1 on what remains:

| lengths used | patterns | coverage |
|---|---|---|
| n ≥ 16 | 65 | 19.3% |
| n ≥ 10 | 142 | 28.6% |
| n ≥ 8 | 197 | 33.4% |
| n ≥ 4 | 442 | 45.2% |
| **n ≥ 2** | **908** | **56.4%** |

**The proof text is more fragmented than the binary.** The same cascade on the instruction stream
reaches 74.2% with 149 patterns; here it takes 908 patterns to reach 56.4%. The head of the curve is
efficient — 65 patterns recover 19.3%, about 4,800 lines — and the tail is not.

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

## 4. The four opportunities, costed

### Opportunity 1 — the class layer exists and four fifths of stepping bypasses it

`InstructionClassSteps.lean` supplies five class lemmas — `configuredRegisterWriteStep`,
`configuredDwordLoadStep`, `configuredDwordStoreStep`, `configuredJStep`, `configuredRetStep` — with
the right design: the four image byte reads and the destination disequalities are `autoParam`s.

| | theorems | lines |
|---|---|---|
| mention `try_step` | 225 | 8,304 |
| use a `configured*Step` lemma | 43 | 1,978 |
| **do not** | **182** | **6,326** |

Largest offenders: `writeSuccessIntCallHandoff` (256 lines), `writeSuccessForkNameBooleanCallHandoff`
(250), `writeSuccessLateOptionalHandoff` (229), `writeSuccessSliceCallSetup` (194).

**Cost:** the largest prize and the largest diff. Not all 6,326 lines are recoverable — some of those
theorems step instruction shapes the five lemmas do not cover, notably calls and slices. **How many
is unmeasured**, and measuring it means classifying each of the 182 by the instruction shape it
steps. That is the next measurement, not a conclusion.

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

**Cost:** one lemma taking `configured` and returning the two reads, plus 40 call-site edits. It is
pure deletion and it has a working precedent. **The cheapest real win in this report.**

**What could go wrong:** the 40 sites are verbatim-identical after abstracting only local names, so
the risk is low. But `configured.normal.2.1` is a projection path into a structure, and if different
sites project differently the lemma needs the projection as a parameter. Check before writing.

### Opportunity 3 — the region-membership proof, 182 sites

`(by unfold writeSuccessParentPc; exact ⟨(0x…, 0x…), by …, by …, by …⟩)` appears **182 times across
58 theorems** in `Level1WriteSuccessSteps.lean`, at roughly two lines each — **≈364 lines**, and it
is the n=2 pattern with 184 sites in the table above.

**Cost:** one lemma parameterised by the address pair. Mechanical.

**What could go wrong:** the two addresses differ per site, so the lemma takes them as arguments and
each site keeps a one-line application. The saving is the `unfold … exact ⟨…, by …, by …, by …⟩`
scaffolding, not the addresses. Expect roughly half of the 364 lines, not all of them.

### Opportunity 4 — motif lemmas over the instruction runs

Measured on branch `motif-lemmas`: **32% of lines saved at n=2 rising to 70% at n=32**, break-even
between 1.1 and 3.3 sites, five cases that build. Composition is 79.5% of this corpus, which is the
bucket those lemmas reduce.

**Cost:** already measured. The blocker is not the technique but its reach — three of eight cases
were blocked, two on control transfers needing `FunctionInstanceContract`, one because the
`mem.writeInt` instances are not contiguous.

---

## 5. What this analysis cannot see

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
- **Opportunity 1 is not costed to a line.** Its 6,326 lines are an upper bound, not a saving.
- **Elaboration time is not measured here.** It is a CI cost, reported separately in
  `motif-lemma-measurements.md`, and it moves opposite to line count: an `autoParam` removes lines
  without removing the work the kernel does.

---

## 6. Method and reproduction

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

## 7. One operational note

The `ssz-ngram-study` branch no longer exists locally or on `origin`. Its tip, `d51c280b`, is still
reachable in the object store, and this report's tooling and the study's two reports were recovered
from it. **Those objects are unreferenced and a `git gc` will drop them.** If the study's reports
are wanted, they need a ref. This branch carries copies of
`docs/research/zesu-ssz-endpoint-motifs.md` and `docs/research/binary-ngram-motifs.md` for that
reason.
