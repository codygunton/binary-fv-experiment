# S24 step 1: fit count (assertion form and leaf check)

Programme plan revision 3, S24 steps 1 and 2. Tier 2 (S24Fit), 2026-11-28, on `exec-spike` `0ad2d297` (S22 `8b63dd09` + S29). Read-only evaluation: nothing was built.

## Counts

- assertions: 102 of 104 (98.1%)
- leaves: 92 of 245 (37.6%)

The leaf count is over the 245 leaves of the plan text: the map leaves of the functions first proved after revision 2 as of `9b0235d3` (`alt_fl_alloc.alloc`/`free`, `scratch_arena.free`/`remap`, three `mem.rotate` copies, two `mergeInPlace` copies). `scratch_arena.alloc` merged in S22 and adds 13: over all 258 map leaves the count is 95 of 258 (36.8%). `memmove`, `memset`, `zkvm_sha256`, `sparseRoot` and `progressiveRootAt` have no per-leaf map records (no `Plan`, or `PlanR` leaves proved in bulk per cut), so their assertions are counted and their leaves are not.

## Step 2: decision

Thresholds: at least 60% of the assertions and at least 40% of the leaves. Assertions 98.1% pass; leaves 37.6% (92/245; 36.8% over all 258) fail. **Decision: stop S24 and S25** (contingency "S24, S25": cheaper models are used for proofs only); continue with S26 to S28 using Prop assertions. S26 step 4 (assertion replay) is skipped.

Sensitivity (leaves over 245; each line adds to the one above):

| Reading | Fit | Share |
|---|---|---|
| Rubric below (strict) | 92 | 37.6% |
| + facts the shared prep macros derive from the opaque `Round` atom counted once (`len_round`, `strOk_round` twice each) | 100 | 40.8% |
| + a piecewise model function (`sizeClassOfBytes`, `remapOut`) evaluated by one unfolding and `if` splits counted as linear | 157 | 64.1% |
| + one new combined lemma each for "swap then next pair" and "swap then reversal done" | 172 | 70.2% |

The second line alone already reaches the threshold on the 245 basis (100/245, 40.8%) but not over all 258 map leaves (103/258, 39.9%). It reads "at most one application" as one lemma *kind*: the eight leaves apply `len_round` or `strOk_round` once per compared element (twice). The rubric counts applications, as S25's `leaf_check` (one tagged lemma per atom, no chaining) would; the margin is one leaf group either way.

The largest swing is the third line: 52 of the 245 leaves are the size-class searches of `alloc` and `free`. Their exit goal is `a0 = sizeClassOfBytes len` on an interval of `len`; `omega` does not split `if` (checked: `omega` fails on `(if x ≤ 8 then 1 else 2) = 1` from `x ≤ 5`), so S25's `leaf_check` as specified (matching, `omega`/`bv_omega`, one tagged lemma by head) does not close them without a new lemma per interval or an `if`-splitting step. Under the plan's wording ("a step lemma that already exists") they miss. Adding `split`-then-`omega` for `if` chains of linear conditions to `leaf_check` would move them, and the five `remap` leaves, to fit; that is a change to S25's specification, which is the coordinator's call.

## Rubric

Assertion classes (S24 step 1): (a) register and frame-slot equations over named logical variables (any term on the right, e.g. `ptr m + w (48 * i)`, `slicePtr (el G as)`); (b) memory facts over those variables (`SliceIs`, `Items`, `BytesAt`, `FrameAt`, frame copies, `rd … = some …`, `SameOutside W m₀ m`, `Present`); (c) linear facts (Presburger, including implications and disjunctions, `/`, `%` by constants, `min`, `max`); (d) named predicate atoms over logical variables and the entry machine, carried unchanged (`Pre`, `Round`, `First`, `Last`, `MidR`, `JoinR`, `MergeOf`, `PreEq` on the entry memory, `¬ Fits g.e`). An assertion fits when it can be rewritten, with the same meaning, into a conjunction of (a)–(d) under existentials; a conditional register equation is written as `r = v` plus a linear implication on `v`. It misses when a conjunct needs an atom over the *current* machine's memory or registers that is not (a) or (b), since such an atom can be neither matched across writes nor evaluated on a snapshot. Named predicates such as `Common`, `Keep`, `Mid`, `Saved` fit because they unfold to (a) and (b).

Leaf (S24 step 1, read against S25 step 1): fit when the exit goal closes by

1. matching: symbolic register values, memory read/written by the run, write-set framing (`SameOutside`, `Common`, saved slots), the prologue's and epilogue's saved registers, the machine-level part of a store step (`step_none`, `step_copy`, `step_swap`, `entry_step`, `step_frame`, `slot_at`, `items_keep`), path conditions as hypotheses, definitional unfolding of the target's abbreviations (`R3`, `G1`…), and linear bounds that follow from `Pre`;
2. linear arithmetic decided by `omega`/`bv_omega`: constants, constant shifts and low masks, `min`/`max`, word/`toNat` conversions without wrap (`w_inj`, `ult_w`, `add_big`);
3. and at most one application of an existing lemma beyond 1 and 2: a model lemma (`first_step`, `items_rev`, `rev_short`, `revAt_zero`, …), an end lemma (`epi_post`, `early_post`), a budget lemma (`Kstep`, `Nat.mul_le_mul_left`), or a fact derived from an opaque atom (`len_round`, `strOk_round`, `round_sortedB`, `sc_le`). Each application counts, including a second use of the same lemma.

A leaf misses when it needs two or more such applications, a case analysis or quantifier step proved by hand, nonlinear arithmetic with no existing lemma (shift or mask by a variable, product of variables), `if` splitting of a model function, or an end assertion that misses. For the rotate and mergeInPlace leaves the count is taken from the proof text (each counted lemma and the counted lemmas inside the shared macros `istep`, `fpprep`, `lpprep`, `fcprep`, `lcprep`); for six `C11564` leaves the macro's `len_round` facts were removed and the module re-checked (`lake env lean`, 130 s): they are unused there, so those six count without them. The whole-leaf lemmas of `alloc`, `free` and `scratch_arena` were read one by one. Closed automatically (`auto:infeasible`) counts as fit. Budgets are part of the exit goal.

Miss tags in the leaf table: `near` = piecewise model function by `if` splits (third line of the sensitivity table); `helper` = misses only by atom-derived facts used twice; `combined` = two model lemmas a single new combined lemma would replace.

## Where the leaves miss

| Reason | Leaves |
|---|---|
| size-class evaluation (`sizeClassOfBytes` `if` chain) | 52 |
| reversal boundary: several `revAt`/`rev` identities | 27 |
| swap plus one `revAt` identity | 15 |
| round transition: two or more round lemmas (and nonlinear budget) | 12 |
| binary-search probe: comparison lemma + search step + sortedness | 11 |
| heap-model return (allocator invariant lemmas) | 8 |
| equal-prefix extension by hand | 8 |
| atom-derived bounds/footprint used twice | 8 |
| shift or mask by a variable | 6 |
| `remapOut` `if` chain | 5 |
| other: `sc_pos` + `cls_lt22` and a case split on a disjunction of `FreePre` | 1 |

## Assertions

| Function | Cut | Assertion | Classes | Class | Note |
|---|---|---|---|---|---|
| `alt_fl_alloc.alloc` | `0x80042494` | `AE` | a c d | fit | `m = g.m`, pc, `AllocPre` carried |
| `alt_fl_alloc.alloc` | `0x8004267c` | `AJ1` | a b c d | fit | regs = entry or `ofNat (scOf g)`; `mem = entry`; `alOf g = 4 → scOf g ≤ 1` linear over the atom term `scOf` |
| `alt_fl_alloc.alloc` | `0x80042680` | `AJ2` | a b c d | fit | conditional equation `alOf = 4 → a3 = max scOf 1` written as `a3 = v` (a) and `alOf = 4 → v = max scOf 1` (c) |
| `alt_fl_alloc.alloc` | `0x800426a0` | `AP` | a b c d | fit | `ClassOk g k` with `k = a3` is linear; `a1 = 0xa0534000 + 8k` |
| `alt_fl_alloc.alloc` | `0x800426a8` | `AP1` | a b c d | fit | head cell `rd g.m (flBase + 8k) = some a0` (b), `a0 ≠ 0` (c) |
| `alt_fl_alloc.alloc` | `0x80042740` | `AB` | a b c d | fit | `∃ k`, `a1 = a3 = classBytes k` |
| `alt_fl_alloc.alloc` | `0x80042760` | `AT` | a b c d | fit | `Rounded`: register, `HEAP_POS` word, linear bounds, `SameOutside` |
| `alt_fl_alloc.alloc` | `0x800426e0` | `AO` | a b c d | fit | `scOf g = 22` |
| `alt_fl_alloc.alloc` | `0x80042708` | `AO2` | a b c d | fit | `Rounded` as in `AT` |
| `alt_fl_alloc.free` | `0x80041f38` | `AFE` | a c d | fit | entry |
| `alt_fl_alloc.free` | `0x80042130` | `AFJ1` | a b c d | fit | `Saved`: frame words + `SameOutside` (b); implication linear |
| `alt_fl_alloc.free` | `0x80042134` | `AFJ2` | a b c d | fit | conditional equation via a fresh variable, as `AJ2` |
| `alt_fl_alloc.free` | `0x80042170` | `AFF` | a b c d | fit | `fsc g < 22`, `a0 = 0xa0534000 + 8 fsc` |
| `scratch_arena.alloc` | `0x800db7a4` | `AE` | a c d | fit | entry |
| `scratch_arena.alloc` | `0x800db7e4` | `AJ` | a b c d | fit | `FrRegs` (a), `FrMem` frame slots (a), `a0 = chunks e` (entry word), `SameOutside`, `Present` (b) |
| `scratch_arena.alloc` | `0x800db820` | `AS` | a b c d | fit | `¬ Fits g.e` is an atom over the entry machine, carried unchanged |
| `scratch_arena.alloc` | `0x800db87c` | `AR` | — | miss | `Out g m`: a disjunction on `a0 = 0` whose branches carry `A.Heap … m` and `Priv` facts about the *current* memory (the callee's outcome); neither a memory fact nor an atom over logical variables, and not linear |
| `scratch_arena.alloc` | `0x800db880` | `AN` | — | miss | contains `Out g m` as `AR` |
| `scratch_arena.free` | `0x800db904` | `fsAE` | a c d | fit | entry |
| `scratch_arena.free` | `0x800db90c` | `fsAJ` | a b c d | fit | registers = entry but `a0`; `mem = entry`; `a0 = chunks e ≠ 0` |
| `scratch_arena.remap` | `0x800db944` | `rsAE` | a c d | fit | entry |
| `scratch_arena.remap` | `0x800db94c` | `rsAJ` | a b c d | fit | as `fsAJ` with `a3` |
| `memmove` | `0x800e06d0` | entry (`Pre`) | a c d | fit | no plan: straight-line proof; the only cut point is the entry |
| `memset` | `0x800e06f0` | entry (`Pre`) | a c d | fit | no plan: proof by run lemmas; the only cut point is the entry |
| `mem.rotate__anon_8330` | `entry` | `cE` | a c d | fit | `mh = m`, pc, `Pre` |
| `mem.rotate__anon_8330` | `o1` | OuterA .one | a b c d | fit | `Pre` (d), `Common` = register/frame-slot equations + `SameOutside` + rodata (a, b), `∃ i`, `2i+2 ≤ L` (c), `SliceIs … (revAt …)` (b), `RegsAre` (a) |
| `mem.rotate__anon_8330` | `i1` | InnerA .one | a b c d | fit | as `OuterA` with `∃ i k`, `k < E`, byte pointers `lo`, `hi` (a) |
| `mem.rotate__anon_8330` | `o2` | OuterA .two | a b c d | fit | as above |
| `mem.rotate__anon_8330` | `i2` | InnerA .two | a b c d | fit | as above |
| `mem.rotate__anon_8330` | `o3` | OuterA .three | a b c d | fit | as above |
| `mem.rotate__anon_8330` | `i3` | InnerA .three | a b c d | fit | as above |
| `mem.rotate__anon_8330` | `epi` | `EpiA` | b d | fit | `SliceIs … (G3 c m)` |
| `mem.rotate__anon_10572` | `entry` | `cE` | a c d | fit | `mh = m`, pc, `Pre` |
| `mem.rotate__anon_10572` | `o1` | OuterA .one | a b c d | fit | `Pre` (d), `Common` = register/frame-slot equations + `SameOutside` + rodata (a, b), `∃ i`, `2i+2 ≤ L` (c), `SliceIs … (revAt …)` (b), `RegsAre` (a) |
| `mem.rotate__anon_10572` | `i1` | InnerA .one | a b c d | fit | as `OuterA` with `∃ i k`, `k < E`, byte pointers `lo`, `hi` (a) |
| `mem.rotate__anon_10572` | `o2` | OuterA .two | a b c d | fit | as above |
| `mem.rotate__anon_10572` | `i2` | InnerA .two | a b c d | fit | as above |
| `mem.rotate__anon_10572` | `o3` | OuterA .three | a b c d | fit | as above |
| `mem.rotate__anon_10572` | `i3` | InnerA .three | a b c d | fit | as above |
| `mem.rotate__anon_10572` | `epi` | `EpiA` | b d | fit | `SliceIs … (G3 c m)` |
| `mem.rotate__anon_12629` | `entry` | `cE` | a c d | fit | `mh = m`, pc, `Pre` |
| `mem.rotate__anon_12629` | `o1` | OuterA .one | a b c d | fit | `Pre` (d), `Common` = register/frame-slot equations + `SameOutside` + rodata (a, b), `∃ i`, `2i+2 ≤ L` (c), `SliceIs … (revAt …)` (b), `RegsAre` (a) |
| `mem.rotate__anon_12629` | `i1` | InnerA .one | a b c d | fit | as `OuterA` with `∃ i k`, `k < E`, byte pointers `lo`, `hi` (a) |
| `mem.rotate__anon_12629` | `o2` | OuterA .two | a b c d | fit | as above |
| `mem.rotate__anon_12629` | `i2` | InnerA .two | a b c d | fit | as above |
| `mem.rotate__anon_12629` | `o3` | OuterA .three | a b c d | fit | as above |
| `mem.rotate__anon_12629` | `i3` | InnerA .three | a b c d | fit | as above |
| `mem.rotate__anon_12629` | `epi` | `EpiA` | b d | fit | `SliceIs … (G3 c m)` |
| `sort.block.mergeInPlace__anon_7964` | `entry` | `xE` | a c d | fit | entry |
| `sort.block.mergeInPlace__anon_7964` | `cOut` | `aOut` | a b c d | fit | `At` (`Pre`, pc, `Common`), `Items G` (b), `Round` (d), `as < ae` (c), `RegsAre` (a) |
| `sort.block.mergeInPlace__anon_7964` | `cFj` | `aFj` | a b c d | fit | `FirstS` (d over logical variables) |
| `sort.block.mergeInPlace__anon_7964` | `cF` | `aF` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_7964` | `cFp` | `aFp` | a b c d | fit | frame copy `∀ j < 32, mem (f + 32 + j) = G as j` (b) |
| `sort.block.mergeInPlace__anon_7964` | `cFc` | `aFc` | a b c d | fit | `∀ j < k, G x j = G as j`: a fact over logical variables, written as a named atom (d); two frame copies (b) |
| `sort.block.mergeInPlace__anon_7964` | `cR0` | `aR0` | a b c d | fit | `MidR` (d) |
| `sort.block.mergeInPlace__anon_7964` | `cR1` | `aR1` | a b c d | fit | `Items (revAt …)` (b), `2i+2 ≤ ae - as` (c) |
| `sort.block.mergeInPlace__anon_7964` | `cS0` | `aS0` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_7964` | `cS1` | `aS1` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_7964` | `cT0` | `aT0` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_7964` | `cT1` | `aT1` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_7964` | `cJ` | `aJ` | a b c d | fit | `Items (R3 …)` |
| `sort.block.mergeInPlace__anon_7964` | `cL` | `aL` | a b c d | fit | `LastS` (d) |
| `sort.block.mergeInPlace__anon_7964` | `cLp` | `aLp` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_7964` | `cLc` | `aLc` | a b c d | fit | as `aFc` |
| `sort.block.mergeInPlace__anon_7964` | `cLj` | `aLj` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_7964` | `cEp` | `aEp` | b d | fit | `MergeOf` (d) |
| `sort.block.mergeInPlace__anon_11564` | `entry` | `xE` | a c d | fit | entry |
| `sort.block.mergeInPlace__anon_11564` | `cOut` | `aOut` | a b c d | fit | `At` adds `SlotsAre` (frame-slot equations, a) |
| `sort.block.mergeInPlace__anon_11564` | `cFv` | `aFv` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cF` | `aF` | a b c d | fit | registers hold `slicePtr (el G as)`, `sliceLen …` (terms over logical variables) |
| `sort.block.mergeInPlace__anon_11564` | `cFp` | `aFp` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cFn` | `aFn` | a b c d | fit | `PreEq m x y n`: string bytes of the *entry* memory, a named atom (d) |
| `sort.block.mergeInPlace__anon_11564` | `cFc` | `aFc` | a b c d | fit | `k < min …`, `slicePtr ≠ slicePtr` (c), `PreEq` (d) |
| `sort.block.mergeInPlace__anon_11564` | `cFj` | `aFj` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cR0` | `aR0` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cR1` | `aR1` | a b c d | fit | rotation state in frame slots (`rotS`, a) |
| `sort.block.mergeInPlace__anon_11564` | `cS0` | `aS0` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cS1` | `aS1` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cT0` | `aT0` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cT1` | `aT1` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cJ` | `aJ` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cLv` | `aLv` | a b c d | fit | `AsL`: `sl 0x48 - sl 0x30 + sl 0x50 = as`, slots (a) and linear (c) |
| `sort.block.mergeInPlace__anon_11564` | `cL` | `aL` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cLp` | `aLp` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cLn` | `aLn` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cLc` | `aLc` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cLj` | `aLj` | a b c d | fit |  |
| `sort.block.mergeInPlace__anon_11564` | `cEp` | `aEp` | b d | fit | `MergeOf` (d) |
| `zkvm_sha256` | `0x800ea180` | entry (`Pre`) | a c d | fit | no `Plan`: segment lemmas; the assertions are the segment boundaries |
| `zkvm_sha256` | `0x800ea1ec` | `Mid` ∧ `FrameAt 8 (leBytes H0)` ∧ a0, a1 | a b d | fit | `Mid`: `sp`, saved registers (a), saved words, bump words, `SameOutside` (b) |
| `zkvm_sha256` | `0x800ea210` | `UAt` | a b c d | fit | state `FrameAt 8 (leBytes (foldBlocks msg i))` (b), `64(i+1) ≤ n` (c) |
| `zkvm_sha256` | `0x800ea260` | `AAt` | a b c d | fit | adds the parameter block words (b), `a0 % 8 = 0` (c) |
| `zkvm_sha256` | `0x800ea280` | `TAt` | a b c d | fit | `a3 = 64 ⌊n/64⌋`, `a4 = n % 64` (a, c) |
| `zkvm_sha256` | `0x800ea2b8` | `PAt` | a b c d | fit | `tailBuf` at `0x28` (b) |
| `zkvm_sha256` | `0x800ea394` | `OAt` | b d | fit | `FrameAt 8 (leBytes (finish …))` |
| `ssz_output.sparseRoot` | `entry` | `AE` | a c d | fit | entry |
| `ssz_output.sparseRoot` | `pc70` | `A70` | a b c d | fit | `Fr`/`Keep`: registers, saved words, `SameOutside`, `Preserved` (a, b, d); `s5 = 1 <<< (depth-1)` a register equation whose value is a term of an entry variable; `BytesAt … leftRoot` (b) |
| `ssz_output.sparseRoot` | `pcC4` | AC k (one cut point, 26 plan cuts) | a b c d | fit | `s4 = k`, `depth = k+1`, `len ≤ half` (c) |
| `ssz_output.sparseRoot` | `pc94` | `A94` | a b c d | fit | both roots (b), `half < len` (c) |
| `ssz_output.sparseRoot` | `pc54` | `A54` | a b c d | fit | `s2 ∈ {fb+8, fb+0x88, zero chunk}`: `s2 = v` (a) and a disjunction of linear equalities (c); `BytesAt m s2 (sparseRoot …)` (b) |
| `ssz_output.progressiveRootAt` | `entry` | `AE` | a c d | fit | entry |
| `ssz_output.progressiveRootAt` | `pcS` | `AS` | a b c d | fit | `Keep`, `s3 = ofNat (sz g)`, `BytesAt … leftRoot` (b) |
| `ssz_output.progressiveRootAt` | `pcR` | `AR` | b d | fit | both roots (b) |
| `ssz_output.progressiveRootAt` | `pcH` | `AH` | b d | fit | `BytesAt … (progressiveRootAt …)` (b) |

## Leaves

| Function | Leaf | Class | Counted lemmas | Reason | Tag |
|---|---|---|---|---|---|
| `alt_fl_alloc.free` | `leaf_80041f38_0` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_1` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_2` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_3` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_4` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_5` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_6` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_7` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_8` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_9` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_10` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_11` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_12` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_13` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_14` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_15` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_16` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_17` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_18` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_19` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_20` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_21` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_22` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_23` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_24` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80041f38_25` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.free` | `leaf_80042130_0` | fit |  | registers and frame matched, `max` linear |  |
| `alt_fl_alloc.free` | `leaf_80042134_0` | miss |  | return: `heap_frame` + `erase_ok` + `priv_erase` (heap model) |  |
| `alt_fl_alloc.free` | `leaf_80042134_1` | fit |  | `cls_lt22` (one lemma); `<<< 3` constant shift |  |
| `alt_fl_alloc.free` | `leaf_80042134_2` | miss |  | `sc_pos` + `cls_lt22` and a case split on a disjunction of `FreePre` |  |
| `alt_fl_alloc.free` | `leaf_80042134_3` | miss |  | return: `heap_frame` + `erase_ok` + `priv_erase` (heap model) |  |
| `alt_fl_alloc.free` | `leaf_80042170_0` | miss |  | the push: `word_split`, `push_ok`, heap-model post lemmas |  |
| `alt_fl_alloc.alloc` | `leaf_80042494_0` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_1` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_2` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_3` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_4` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_5` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_6` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_7` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_8` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_9` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_10` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_11` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_12` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_13` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_14` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_15` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_16` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_17` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_18` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_19` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_20` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_21` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_22` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_23` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_24` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_80042494_25` | miss |  | evaluating `sizeClassOfBytes` on the path's interval: unfold + case split over its 23-way `if` chain (`cls_sem`/`sc_tac`) plus `sc_le`; omega does not split `if`; no existing lemma gives the class from the bounds | near |
| `alt_fl_alloc.alloc` | `leaf_8004267c_0` | fit |  | registers and memory matched, `max` linear |  |
| `alt_fl_alloc.alloc` | `leaf_80042680_0` | fit |  | `sc_le` (one lemma) + omega over the atom `scOf`; `<<< 3` constant shift |  |
| `alt_fl_alloc.alloc` | `leaf_80042680_1` | fit |  | `sc_le` (one lemma) + omega |  |
| `alt_fl_alloc.alloc` | `leaf_80042680_2` | fit |  | `sc_le` (one lemma) + omega |  |
| `alt_fl_alloc.alloc` | `leaf_80042680_3` | fit |  | `sc_le` (one lemma) + omega |  |
| `alt_fl_alloc.alloc` | `leaf_800426a0_0` | miss |  | infeasibility needs `8 << k < 1 << log2_align` false: shifts by a variable (nonlinear) |  |
| `alt_fl_alloc.alloc` | `leaf_800426a0_1` | miss |  | block size `classBytes k = 8 << k`: shift by a variable (nonlinear) |  |
| `alt_fl_alloc.alloc` | `leaf_800426a0_2` | fit |  | head cell read matched; `fl_cell` address (one lemma); bv_omega |  |
| `alt_fl_alloc.alloc` | `leaf_800426a8_0` | miss |  | heap-model reasoning: `pop_head`, `pop_ok`, `post_block`, `free_blk_priv`, `priv_cell` |  |
| `alt_fl_alloc.alloc` | `leaf_800426e0_0` | miss |  | rounding `HEAP_POS` up: `and` with the variable mask `(1 << a) - 1` (nonlinear) |  |
| `alt_fl_alloc.alloc` | `leaf_800426e0_1` | miss |  | rounding `HEAP_POS` up: `and` with the variable mask `(1 << a) - 1` (nonlinear) |  |
| `alt_fl_alloc.alloc` | `leaf_80042708_0` | miss |  | return: `bump_ok` + `post_block` + `bump_priv` (heap model) |  |
| `alt_fl_alloc.alloc` | `leaf_80042708_1` | miss |  | return null: `bump_ok` + `post_null` (heap model), case split |  |
| `alt_fl_alloc.alloc` | `leaf_80042740_0` | miss |  | rounding `HEAP_POS` up: `and` with the variable mask `classBytes k - 1` (nonlinear) |  |
| `alt_fl_alloc.alloc` | `leaf_80042740_1` | miss |  | rounding `HEAP_POS` up: `and` with the variable mask `classBytes k - 1` (nonlinear) |  |
| `alt_fl_alloc.alloc` | `leaf_80042760_0` | miss |  | return: `bump_ok` + `post_block` + `bump_priv` (heap model) |  |
| `alt_fl_alloc.alloc` | `leaf_80042760_1` | miss |  | return null: `bump_ok` + `post_null` (heap model), case split |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f388_0` | fit | `early_post` | one lemma: `early_post` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f388_1` | fit | `early_post` | one lemma: `early_post` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f388_2` | miss | `Qf_entry` `round_init` | 2 lemma applications: `Qf_entry`, `round_init` (nonlinear budget fact) |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f3dc_0` | fit | `first_empty` | one lemma: `first_empty` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f3dc_1` | fit | `first_init` | one lemma: `first_init` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f3f8_0` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f3f8_1` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f3fc_0` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f43c_0` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f460_0` | miss | `cmp_ne` `first_step` `round_sortedB` | 3 lemma applications: `cmp_ne`, `first_step`, `round_sortedB` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f460_1` | miss | `cmp_ne` `first_step` `round_sortedB` | 3 lemma applications: `cmp_ne`, `first_step`, `round_sortedB` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f460_2` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f460_3` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f460_4` | miss |  | extends the equal-prefix fact `∀ j < k, …` to `k + 1` by hand (case split on `j`) |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f460_5` | miss | `cmp_all` `first_step` `round_sortedB` | extends the equal-prefix fact `∀ j < k, …` to `k + 1` by hand (case split on `j`); also `cmp_all`, `first_step`, `round_sortedB` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f4ac_0` | fit | `rev_short` | one lemma: `rev_short` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f4ac_1` | fit | `revAt_zero` | one lemma: `revAt_zero` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f4d0_0` | fit | `items_rev` | one lemma: `items_rev` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f4d0_1` | miss | `items_rev` `revAt_full` | 2 lemma applications: `items_rev`, `revAt_full` | combined |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f69c_0` | fit | `rev_short` | one lemma: `rev_short` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f69c_1` | fit | `revAt_zero` | one lemma: `revAt_zero` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f6c4_0` | fit | `items_rev` | one lemma: `items_rev` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f6c4_1` | miss | `items_rev` `revAt_full` | 2 lemma applications: `items_rev`, `revAt_full` | combined |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f890_0` | fit | `rev_short` | one lemma: `rev_short` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f890_1` | fit | `revAt_zero` | one lemma: `revAt_zero` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f8ac_0` | fit | `items_rev` | one lemma: `items_rev` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004f8ac_1` | miss | `items_rev` `revAt_full` | 2 lemma applications: `items_rev`, `revAt_full` | combined |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fa78_0` | miss | `round_done` `join_of_mid` | 2 lemma applications: `round_done`, `join_of_mid` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fa78_1` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fa78_2` | fit |  | closed automatically (auto:infeasible): infeasible by linear arithmetic |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fa78_3` | miss | `join_of_mid` `last_init` `Qf_le` | 3 lemma applications: `join_of_mid`, `last_init`, `Qf_le` (nonlinear budget fact) |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fab0_0` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004faf0_0` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fb14_0` | miss | `cmp_ne` `last_step` `round_sortedA` | 3 lemma applications: `cmp_ne`, `last_step`, `round_sortedA` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fb14_1` | miss | `cmp_ne` `last_step` `round_sortedA` | 3 lemma applications: `cmp_ne`, `last_step`, `round_sortedA` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fb14_2` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fb14_3` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fb14_4` | miss |  | extends the equal-prefix fact `∀ j < k, …` to `k + 1` by hand (case split on `j`) |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fb14_5` | miss | `cmp_all` `last_step` `round_sortedA` | extends the equal-prefix fact `∀ j < k, …` to `k + 1` by hand (case split on `j`); also `cmp_all`, `last_step`, `round_sortedA` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004faac_0` | miss | `round_done` `round_of_last` | 2 lemma applications: `round_done`, `round_of_last` |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004faac_1` | miss | `last_curr` `round_of_last` `Qf_step` `bud_step` | 4 lemma applications: `last_curr`, `round_of_last`, `Qf_step`, `bud_step` (nonlinear budget fact) |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004faac_2` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_7964` | `leaf_8004fb54_0` | fit | `epi_post` | one lemma: `epi_post` |  |
| `mem.rotate__anon_8330` | `leaf_8006464c_0` | miss | `rev_short` `rev_short` `rev_short` | 3 lemma applications: `rev_short`, `rev_short`, `rev_short` |  |
| `mem.rotate__anon_8330` | `leaf_8006464c_1` | miss | `revAt_zero` `rev_short` `rev_short` | 3 lemma applications: `revAt_zero`, `rev_short`, `rev_short` |  |
| `mem.rotate__anon_8330` | `leaf_8006464c_2` | miss | `revAt_zero` `rev_short` | 2 lemma applications: `revAt_zero`, `rev_short` |  |
| `mem.rotate__anon_8330` | `leaf_8006464c_3` | fit | `revAt_zero` | one lemma: `revAt_zero` |  |
| `mem.rotate__anon_8330` | `leaf_80064688_0` | fit |  | matching and linear arithmetic only |  |
| `mem.rotate__anon_8330` | `leaf_8006469c_0` | fit | `inner_step` | one lemma: `inner_step` |  |
| `mem.rotate__anon_8330` | `leaf_8006469c_1` | miss | `inner_step` `slice_next` | 2 lemma applications: `inner_step`, `slice_next` | combined |
| `mem.rotate__anon_8330` | `leaf_8006469c_2` | miss | `inner_step` `slice_end` `rev_short` `rev_short` | 4 lemma applications: `inner_step`, `slice_end`, `rev_short`, `rev_short` |  |
| `mem.rotate__anon_8330` | `leaf_8006469c_3` | miss | `inner_step` `slice_end` `revAt_zero` `rev_short` | 4 lemma applications: `inner_step`, `slice_end`, `revAt_zero`, `rev_short` |  |
| `mem.rotate__anon_8330` | `leaf_8006469c_4` | miss | `inner_step` `slice_end` `revAt_zero` | 3 lemma applications: `inner_step`, `slice_end`, `revAt_zero` |  |
| `mem.rotate__anon_8330` | `leaf_800646f8_0` | fit |  | matching and linear arithmetic only |  |
| `mem.rotate__anon_8330` | `leaf_8006470c_0` | fit | `inner_step` | one lemma: `inner_step` |  |
| `mem.rotate__anon_8330` | `leaf_8006470c_1` | miss | `inner_step` `slice_next` | 2 lemma applications: `inner_step`, `slice_next` | combined |
| `mem.rotate__anon_8330` | `leaf_8006470c_2` | miss | `inner_step` `slice_end` `rev_short` | 3 lemma applications: `inner_step`, `slice_end`, `rev_short` |  |
| `mem.rotate__anon_8330` | `leaf_8006470c_3` | miss | `inner_step` `slice_end` `revAt_zero` | 3 lemma applications: `inner_step`, `slice_end`, `revAt_zero` |  |
| `mem.rotate__anon_8330` | `leaf_80064758_0` | fit |  | matching and linear arithmetic only |  |
| `mem.rotate__anon_8330` | `leaf_8006476c_0` | fit | `inner_step` | one lemma: `inner_step` |  |
| `mem.rotate__anon_8330` | `leaf_8006476c_1` | miss | `inner_step` `slice_next` | 2 lemma applications: `inner_step`, `slice_next` | combined |
| `mem.rotate__anon_8330` | `leaf_8006476c_2` | miss | `inner_step` `slice_end` | 2 lemma applications: `inner_step`, `slice_end` |  |
| `mem.rotate__anon_8330` | `leaf_80064798_0` | fit | `epi_post` | one lemma: `epi_post` |  |
| `mem.rotate__anon_10572` | `leaf_8007cc68_0` | miss | `rev_short` `rev_short` `rev_short` | 3 lemma applications: `rev_short`, `rev_short`, `rev_short` |  |
| `mem.rotate__anon_10572` | `leaf_8007cc68_1` | miss | `revAt_zero` `rev_short` `rev_short` | 3 lemma applications: `revAt_zero`, `rev_short`, `rev_short` |  |
| `mem.rotate__anon_10572` | `leaf_8007cc68_2` | miss | `revAt_zero` `rev_short` | 2 lemma applications: `revAt_zero`, `rev_short` |  |
| `mem.rotate__anon_10572` | `leaf_8007cc68_3` | fit | `revAt_zero` | one lemma: `revAt_zero` |  |
| `mem.rotate__anon_10572` | `leaf_8007cc9c_0` | fit |  | matching and linear arithmetic only |  |
| `mem.rotate__anon_10572` | `leaf_8007ccb0_0` | fit | `inner_step` | one lemma: `inner_step` |  |
| `mem.rotate__anon_10572` | `leaf_8007ccb0_1` | miss | `inner_step` `slice_next` | 2 lemma applications: `inner_step`, `slice_next` | combined |
| `mem.rotate__anon_10572` | `leaf_8007ccb0_2` | miss | `inner_step` `slice_end` `rev_short` `rev_short` | 4 lemma applications: `inner_step`, `slice_end`, `rev_short`, `rev_short` |  |
| `mem.rotate__anon_10572` | `leaf_8007ccb0_3` | miss | `inner_step` `slice_end` `revAt_zero` `rev_short` | 4 lemma applications: `inner_step`, `slice_end`, `revAt_zero`, `rev_short` |  |
| `mem.rotate__anon_10572` | `leaf_8007ccb0_4` | miss | `inner_step` `slice_end` `revAt_zero` | 3 lemma applications: `inner_step`, `slice_end`, `revAt_zero` |  |
| `mem.rotate__anon_10572` | `leaf_8007cd08_0` | fit |  | matching and linear arithmetic only |  |
| `mem.rotate__anon_10572` | `leaf_8007cd1c_0` | fit | `inner_step` | one lemma: `inner_step` |  |
| `mem.rotate__anon_10572` | `leaf_8007cd1c_1` | miss | `inner_step` `slice_next` | 2 lemma applications: `inner_step`, `slice_next` | combined |
| `mem.rotate__anon_10572` | `leaf_8007cd1c_2` | miss | `inner_step` `slice_end` `rev_short` | 3 lemma applications: `inner_step`, `slice_end`, `rev_short` |  |
| `mem.rotate__anon_10572` | `leaf_8007cd1c_3` | miss | `inner_step` `slice_end` `revAt_zero` | 3 lemma applications: `inner_step`, `slice_end`, `revAt_zero` |  |
| `mem.rotate__anon_10572` | `leaf_8007cd6c_0` | fit |  | matching and linear arithmetic only |  |
| `mem.rotate__anon_10572` | `leaf_8007cd80_0` | fit | `inner_step` | one lemma: `inner_step` |  |
| `mem.rotate__anon_10572` | `leaf_8007cd80_1` | miss | `inner_step` `slice_next` | 2 lemma applications: `inner_step`, `slice_next` | combined |
| `mem.rotate__anon_10572` | `leaf_8007cd80_2` | miss | `inner_step` `slice_end` | 2 lemma applications: `inner_step`, `slice_end` |  |
| `mem.rotate__anon_10572` | `leaf_8007cdac_0` | fit | `epi_post` | one lemma: `epi_post` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ddc_0` | miss | `round_done` `round_init` | 2 lemma applications: `round_done`, `round_init` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ddc_1` | miss | `round_done` `round_init` | 2 lemma applications: `round_done`, `round_init` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ddc_2` | miss | `round_init` `entry_bound` | 2 lemma applications: `round_init`, `entry_bound` (nonlinear budget fact) |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098e60_0` | fit | `first_empty` | one lemma: `first_empty` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098e60_1` | fit | `mul_le_mul_left` | one lemma: `mul_le_mul_left` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098e78_0` | fit | `first_init` | one lemma: `first_init` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ea8_0` | fit | `Kstep` | one lemma: `Kstep` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098e8c_0` | miss | `ltBy_slice_eq` `first_step` `round_sortedB` | 3 lemma applications: `ltBy_slice_eq`, `first_step`, `round_sortedB` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ea4_0` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ea4_1` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ec0_0` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ec0_1` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ec0_2` | miss | `len_round` `len_round` | 2 lemma applications: `len_round`, `len_round` (bounds/footprint derived from the opaque `Round` atom) | helper |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ec0_3` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ec0_4` | miss | `len_round` `len_round` | 2 lemma applications: `len_round`, `len_round` (bounds/footprint derived from the opaque `Round` atom) | helper |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ee0_0` | miss | `strOk_round` `strOk_round` `len_round` `len_round` `ltBy_slice_ne` `first_step` `round_sortedB` | 7 lemma applications: `strOk_round`, `strOk_round`, `len_round`, `len_round`, `ltBy_slice_ne`, `first_step`, `round_sortedB` (bounds/footprint derived from the opaque `Round` atom) |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ee0_1` | miss | `strOk_round` `strOk_round` `len_round` `len_round` `ltBy_slice_ne` `first_step` `round_sortedB` | 7 lemma applications: `strOk_round`, `strOk_round`, `len_round`, `len_round`, `ltBy_slice_ne`, `first_step`, `round_sortedB` (bounds/footprint derived from the opaque `Round` atom) |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ee0_2` | miss | `strOk_round` `strOk_round` `len_round` `len_round` | 4 lemma applications: `strOk_round`, `strOk_round`, `len_round`, `len_round` (bounds/footprint derived from the opaque `Round` atom) | helper |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ee0_3` | miss | `strOk_round` `strOk_round` `len_round` `len_round` | 4 lemma applications: `strOk_round`, `strOk_round`, `len_round`, `len_round` (bounds/footprint derived from the opaque `Round` atom) | helper |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ee0_4` | miss | `strOk_round` `strOk_round` `len_round` `len_round` | extends the equal-prefix fact `∀ j < k, …` to `k + 1` by hand (case split on `j`); also `strOk_round`, `strOk_round`, `len_round`, `len_round` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098ee0_5` | miss | `strOk_round` `strOk_round` `len_round` `len_round` | extends the equal-prefix fact `∀ j < k, …` to `k + 1` by hand (case split on `j`); also `strOk_round`, `strOk_round`, `len_round`, `len_round` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098f2c_0` | fit | `rev_short` | one lemma: `rev_short` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098f2c_1` | fit | `revAt_zero` | one lemma: `revAt_zero` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098f78_0` | fit | `items_rev` | one lemma: `items_rev` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80098f78_1` | miss | `items_rev` `revAt_full` | 2 lemma applications: `items_rev`, `revAt_full` | combined |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099188_0` | fit | `rev_short` | one lemma: `rev_short` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099188_1` | fit | `revAt_zero` | one lemma: `revAt_zero` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800991d8_0` | fit | `items_rev` | one lemma: `items_rev` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800991d8_1` | miss | `items_rev` `revAt_full` | 2 lemma applications: `items_rev`, `revAt_full` | combined |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800993e8_0` | fit | `rev_short` | one lemma: `rev_short` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800993e8_1` | fit | `revAt_zero` | one lemma: `revAt_zero` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_8009941c_0` | fit | `items_rev` | one lemma: `items_rev` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_8009941c_1` | miss | `items_rev` `revAt_full` | 2 lemma applications: `items_rev`, `revAt_full` | combined |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099634_0` | miss | `round_done` `join_of_mid` | 2 lemma applications: `round_done`, `join_of_mid` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099634_1` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099634_2` | fit |  | closed automatically (auto:infeasible): infeasible by linear arithmetic |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099634_3` | miss | `mul_le_mul_left` `Qf_le` `join_of_mid` | 3 lemma applications: `mul_le_mul_left`, `Qf_le`, `join_of_mid` (nonlinear budget fact) |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099668_0` | fit | `last_init` | one lemma: `last_init` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_8009968c_0` | fit | `Kstep` | one lemma: `Kstep` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996f8_0` | miss | `ltBy_slice_eq` `last_step` `round_sortedA` | 3 lemma applications: `ltBy_slice_eq`, `last_step`, `round_sortedA` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996f8_1` | miss | `ltBy_slice_eq` `last_step` `round_sortedA` | 3 lemma applications: `ltBy_slice_eq`, `last_step`, `round_sortedA` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099688_0` | miss | `round_of_last` `round_done` | 2 lemma applications: `round_of_last`, `round_done` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099688_1` | miss | `last_curr` `Qf_step` `round_of_last` | 3 lemma applications: `last_curr`, `Qf_step`, `round_of_last` (nonlinear budget fact) |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099688_2` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996a4_0` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996a4_1` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996a4_2` | miss | `len_round` `len_round` | 2 lemma applications: `len_round`, `len_round` (bounds/footprint derived from the opaque `Round` atom) | helper |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996a4_3` | fit |  | matching and linear arithmetic only |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996a4_4` | miss | `len_round` `len_round` | 2 lemma applications: `len_round`, `len_round` (bounds/footprint derived from the opaque `Round` atom) | helper |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996c4_0` | miss | `strOk_round` `strOk_round` `len_round` `len_round` `ltBy_slice_ne` `last_step` `round_sortedA` | 7 lemma applications: `strOk_round`, `strOk_round`, `len_round`, `len_round`, `ltBy_slice_ne`, `last_step`, `round_sortedA` (bounds/footprint derived from the opaque `Round` atom) |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996c4_1` | miss | `strOk_round` `strOk_round` `len_round` `len_round` `ltBy_slice_ne` `last_step` `round_sortedA` | 7 lemma applications: `strOk_round`, `strOk_round`, `len_round`, `len_round`, `ltBy_slice_ne`, `last_step`, `round_sortedA` (bounds/footprint derived from the opaque `Round` atom) |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996c4_2` | miss | `strOk_round` `strOk_round` `len_round` `len_round` | 4 lemma applications: `strOk_round`, `strOk_round`, `len_round`, `len_round` (bounds/footprint derived from the opaque `Round` atom) | helper |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996c4_3` | miss | `strOk_round` `strOk_round` `len_round` `len_round` | 4 lemma applications: `strOk_round`, `strOk_round`, `len_round`, `len_round` (bounds/footprint derived from the opaque `Round` atom) | helper |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996c4_4` | miss | `strOk_round` `strOk_round` `len_round` `len_round` | extends the equal-prefix fact `∀ j < k, …` to `k + 1` by hand (case split on `j`); also `strOk_round`, `strOk_round`, `len_round`, `len_round` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_800996c4_5` | miss | `strOk_round` `strOk_round` `len_round` `len_round` | extends the equal-prefix fact `∀ j < k, …` to `k + 1` by hand (case split on `j`); also `strOk_round`, `strOk_round`, `len_round`, `len_round` |  |
| `sort.block.mergeInPlace__anon_11564` | `leaf_80099708_0` | fit | `epi_post` | one lemma: `epi_post` |  |
| `mem.rotate__anon_12629` | `leaf_800a8f30_0` | miss | `rev_short` `rev_short` `rev_short` | 3 lemma applications: `rev_short`, `rev_short`, `rev_short` |  |
| `mem.rotate__anon_12629` | `leaf_800a8f30_1` | miss | `revAt_zero` `rev_short` `rev_short` | 3 lemma applications: `revAt_zero`, `rev_short`, `rev_short` |  |
| `mem.rotate__anon_12629` | `leaf_800a8f30_2` | miss | `revAt_zero` `rev_short` | 2 lemma applications: `revAt_zero`, `rev_short` |  |
| `mem.rotate__anon_12629` | `leaf_800a8f30_3` | fit | `revAt_zero` | one lemma: `revAt_zero` |  |
| `mem.rotate__anon_12629` | `leaf_800a8f5c_0` | fit |  | matching and linear arithmetic only |  |
| `mem.rotate__anon_12629` | `leaf_800a8f70_0` | fit | `inner_step` | one lemma: `inner_step` |  |
| `mem.rotate__anon_12629` | `leaf_800a8f70_1` | miss | `inner_step` `slice_next` | 2 lemma applications: `inner_step`, `slice_next` | combined |
| `mem.rotate__anon_12629` | `leaf_800a8f70_2` | miss | `inner_step` `slice_end` `rev_short` `rev_short` | 4 lemma applications: `inner_step`, `slice_end`, `rev_short`, `rev_short` |  |
| `mem.rotate__anon_12629` | `leaf_800a8f70_3` | miss | `inner_step` `slice_end` `revAt_zero` `rev_short` | 4 lemma applications: `inner_step`, `slice_end`, `revAt_zero`, `rev_short` |  |
| `mem.rotate__anon_12629` | `leaf_800a8f70_4` | miss | `inner_step` `slice_end` `revAt_zero` | 3 lemma applications: `inner_step`, `slice_end`, `revAt_zero` |  |
| `mem.rotate__anon_12629` | `leaf_800a8fbc_0` | fit |  | matching and linear arithmetic only |  |
| `mem.rotate__anon_12629` | `leaf_800a8fd0_0` | fit | `inner_step` | one lemma: `inner_step` |  |
| `mem.rotate__anon_12629` | `leaf_800a8fd0_1` | miss | `inner_step` `slice_next` | 2 lemma applications: `inner_step`, `slice_next` | combined |
| `mem.rotate__anon_12629` | `leaf_800a8fd0_2` | miss | `inner_step` `slice_end` `rev_short` | 3 lemma applications: `inner_step`, `slice_end`, `rev_short` |  |
| `mem.rotate__anon_12629` | `leaf_800a8fd0_3` | miss | `inner_step` `slice_end` `revAt_zero` | 3 lemma applications: `inner_step`, `slice_end`, `revAt_zero` |  |
| `mem.rotate__anon_12629` | `leaf_800a9014_0` | fit |  | matching and linear arithmetic only |  |
| `mem.rotate__anon_12629` | `leaf_800a9028_0` | fit | `inner_step` | one lemma: `inner_step` |  |
| `mem.rotate__anon_12629` | `leaf_800a9028_1` | miss | `inner_step` `slice_next` | 2 lemma applications: `inner_step`, `slice_next` | combined |
| `mem.rotate__anon_12629` | `leaf_800a9028_2` | miss | `inner_step` `slice_end` | 2 lemma applications: `inner_step`, `slice_end` |  |
| `mem.rotate__anon_12629` | `leaf_800a9054_0` | fit | `epi_post` | one lemma: `epi_post` |  |
| `scratch_arena.alloc` | `leaf_800db7a4_0` | fit |  | prologue matched (`entry_exit`); `¬ Fits` from `chunks = 0` by unfolding the atom |  |
| `scratch_arena.alloc` | `leaf_800db7a4_1` | fit |  | prologue matched (`entry_exit`) |  |
| `scratch_arena.alloc` | `leaf_800db7e4_0` | fit |  | `eval_align2` (one lemma: the masked sum is `alignUp`) + linear |  |
| `scratch_arena.alloc` | `leaf_800db7e4_1` | miss |  | fast-path return: `eval_align2`, `chunk` arithmetic, `ret_ok`, `returns_in`, `pres_from`, case split |  |
| `scratch_arena.alloc` | `leaf_800db7e4_2` | miss |  | infeasible only by `chunk_arith` + `alignUp_bounds` (two lemmas) |  |
| `scratch_arena.alloc` | `leaf_800db820_0` | miss |  | call leaf: `newSize` (`max`, saturating doubling) by `need_eval` + `sat_eval` + `if`; target `AR` not in the form |  |
| `scratch_arena.alloc` | `leaf_800db820_1` | miss |  | call leaf: `newSize` by `need_eval` + `sat_eval` + `if`; target `AR` not in the form |  |
| `scratch_arena.alloc` | `leaf_800db820_2` | miss |  | call leaf: `newSize` by `need_eval` + `if`; target `AR` not in the form |  |
| `scratch_arena.alloc` | `leaf_800db820_3` | miss |  | call leaf: `newSize` by `need_eval` + `if`; target `AR` not in the form |  |
| `scratch_arena.alloc` | `leaf_800db87c_0` | miss |  | source `AR` not in the form (`Out`); return by `ret_ok` + `returns_in` + case split on `Out` |  |
| `scratch_arena.alloc` | `leaf_800db87c_1` | miss |  | source `AR` not in the form (`Out`) |  |
| `scratch_arena.alloc` | `leaf_800db880_0` | miss |  | source `AN` not in the form; slow-path return: chunk header writes, `newSize_24`, `live_ok`, `priv_not_live`, … |  |
| `scratch_arena.alloc` | `leaf_800db880_1` | miss |  | source `AN` not in the form; infeasible by `newSize_lt`/`newSize_ge`/`pow_le_pow_right`/`alignUp_bounds` |  |
| `scratch_arena.free` | `leaf_800db904_0` | fit |  | return with `chunks = 0`: registers and memory matched |  |
| `scratch_arena.free` | `leaf_800db904_1` | fit |  | registers matched; `chunks ≠ 0` from the condition |  |
| `scratch_arena.free` | `leaf_800db90c_0` | fit |  | `used_eval` (memory read matched); the post's `if` decided by the path condition |  |
| `scratch_arena.free` | `leaf_800db90c_1` | fit |  | `used_eval` (memory read matched); the post's `if` decided by the path condition |  |
| `scratch_arena.remap` | `leaf_800db944_0` | fit |  | return with `chunks = 0`: `remapOut` reduces by `chunks = 0`, registers matched |  |
| `scratch_arena.remap` | `leaf_800db944_1` | fit |  | registers matched (bv_omega) |  |
| `scratch_arena.remap` | `leaf_800db94c_0` | miss |  | `remapOut` unfolded and its nested `if`s split (`rs_sem`: `split`, `simp_all`, omega); omega does not split `if`; no existing lemma per branch | near |
| `scratch_arena.remap` | `leaf_800db94c_1` | miss |  | `remapOut` unfolded and its nested `if`s split (`rs_sem`: `split`, `simp_all`, omega); omega does not split `if`; no existing lemma per branch | near |
| `scratch_arena.remap` | `leaf_800db94c_2` | miss |  | `remapOut` unfolded and its nested `if`s split (`rs_sem`: `split`, `simp_all`, omega); omega does not split `if`; no existing lemma per branch | near |
| `scratch_arena.remap` | `leaf_800db94c_3` | miss |  | `remapOut` unfolded and its nested `if`s split (`rs_sem`: `split`, `simp_all`, omega); omega does not split `if`; no existing lemma per branch | near |
| `scratch_arena.remap` | `leaf_800db94c_4` | miss |  | `remapOut` unfolded and its nested `if`s split (`rs_sem`: `split`, `simp_all`, omega); omega does not split `if`; no existing lemma per branch | near |
