# Selecting motifs by DAG class instead of sequence

The n-gram study's reconnaissance item 4 said the instruction scheduler fragments long motifs, so
sequence-exact n-grams **undercount** reuse, and called this *"the single most important
methodological consequence"*. Its method §5 required counting motifs by rescheduling-invariant DAG
class as well as by token sequence, because *"the gap between the two counts is the quantity of
interest"*.

The study built `dag_canonical_form` and validated it (0 failures in 2460 reschedulings against a
control that fails ~2216). **It never used it to select cases.** The motif campaign then picked all
eight of its cases as sequence-exact contiguous windows — exactly the undercounting the study warned
about. This closes that gap.

## 1. The result: it depends entirely on the token level, and the study's headline reading is wrong

Distinct classes among admissible windows (one basic block, one function instance, no transfer):

| n | windows | L5 class | L4 opcode | L2 registers | L3 α-roles | **DAG** |
|---|---|---|---|---|---|---|
| 2 | 2841 | 47 | 176 | 1364 | 478 | **353** |
| 3 | 2284 | 139 | 327 | 1345 | 708 | **580** |
| 4 | 1893 | 266 | 448 | 1236 | 778 | **690** |
| 6 | 1366 | 423 | 535 | 996 | 734 | **685** |
| 8 | 1047 | 467 | 529 | 817 | 647 | **613** |
| 10 | 826 | 452 | 488 | 675 | 570 | **550** |

The DAG relative to each level — **negative means the DAG splits, positive means it merges**:

| n | vs L5 class | vs L4 opcode | vs L2 registers | vs L3 α-roles |
|---|---|---|---|---|
| 2 | −651% | −101% | **+74%** | **+26%** |
| 3 | −317% | −77% | **+57%** | **+18%** |
| 4 | −159% | −54% | **+44%** | **+11%** |
| 6 | −62% | −28% | **+31%** | **+7%** |
| 8 | −31% | −16% | **+25%** | **+5%** |
| 10 | −22% | −13% | **+19%** | **+4%** |

## 2. What this means

**Against the levels the campaign actually used, the DAG makes things worse, not better.** The
campaign selected at instruction-class level (L5), where the DAG produces **7.5× more classes** at
n=2 and 22% more at n=10. Selecting cases by DAG class would give *more* motifs with *fewer* sites
each — the opposite of what a motif lemma wants.

The reason is that a DAG carries information a class sequence has discarded. Two `LOAD LOAD` windows
look identical at L5; the DAG separates the one where the second load depends on the first from the
one where they are independent. At L5 and L4 the DAG is a **refinement**, not a coarsening.

**The predicted merging is real, but only against register-bearing levels, and it is modest.**
Against L2 (concrete register names) the DAG merges 19–74%, and against L3 (α-renamed roles) 4–26%.
Both effects shrink as `n` grows — the opposite of the study's expectation that fragmentation would
bite hardest at n ≥ 10.

**So finding 4 is half right.** The scheduler does fragment, and the DAG does reunite what it
fragmented — but only relative to a level that still distinguishes registers, and the effect is
largest at n=2 where it matters least. The study's own remedy (move to instruction-class tokens,
which is what the covering does) already absorbs most of the fragmentation, and the DAG on top of
that only re-splits.

## 3. Consequences for the campaign

- **No case changes shape.** All five measured cases were selected at L5, where the DAG only splits.
  Re-selecting by DAG class would produce a different, larger, worse-supported candidate set.
- **Case B is still not a linear motif.** `mem.writeInt`'s instances are non-contiguous — 16 pcs over
  36 slots, four of six site pairs overlapping. The DAG does not help: it is a canonical form for a
  *window*, and B has no window. What B needs is a motif stated over a pc-set, which neither `Seg`
  nor the study's machinery provides.
- **The 149-lemma covering stands as selected.** Its L5 basis is the level at which the DAG has
  nothing to add.

## 4. Cost

`dag_canonical_form` is Weisfeiler-Leman refinement plus individualisation-refinement under a leaf
budget of 256. It is slow: ~40 minutes for the six lengths above over 10,257 windows. Windows where
the budget was exceeded are marked `approx:` — 0 at n ≤ 4, 4 at n=6, 29 at n=8, 50 at n=10 — and are
excluded from any exactness claim.

## 5. Reproduce

`scratchpad/dag2.py`, using `dag_canonical_form` and `alpha_keys` from
`tools/ngram_motifs.py` on the `ssz-ngram-study` branch, against
`result-zesu-ssz-decode-cfg/zesu-cfg.json`.
