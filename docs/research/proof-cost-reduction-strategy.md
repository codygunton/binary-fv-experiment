# Strategy for reducing proof cost on the Zesu SSZ endpoint

A decision record. It captures what the pattern-analysis work established, which of its own
conclusions it retracted, and the two mechanisms that remain. Written for a reader who did not take
part in the discussion.

Companion documents:

- `hlevel2-ngram-opportunities.md` — the measurements this record reasons about.
- `motif-lemma-authoring-cost.md` — the five measured lemma cases, on branch `motif-lemmas`.
- `zesu-ssz-endpoint-motifs.md`, `binary-ngram-motifs.md` — the original binary study, on branch
  `ssz-ngram-study`.

---

## 1. The problem, stated in the units that matter

Proof cost scales with the quantity of RISC-V that the proof covers. **Lines of Lean for each
instruction covered** is therefore the metric, and every other figure in this record exists to
explain that one.

The figures below are joined against the correct build artifact. §6 records an earlier version of
this table that used the wrong one, and what changed.

| | |
|---|---|
| `BinaryFv/Zesu/MachineExecution` on `main` at `9935fb21` | 24,719 code lines in 683 declarations |
| hex literals in that corpus | 489 |
| of those, **real instruction addresses** in the endpoint image | **296** |
| instructions in the endpoint image | **7,222** |
| **coverage** | **4.1%** |
| **rate** | **83.5 lines of Lean for each instruction** |
| the whole endpoint at that rate | **≈603,000 lines** |

Only 296 of the 489 hex literals are instruction addresses. The rest are immediates, region bounds
and encoding bytes. Joining against the image is what separates them, and no earlier figure in this
project did that join.

**Two of these numbers are much worse than previously reported.** The rate was reported as 51 and is
83.5. The endpoint was reported as 4,435 instructions and is 7,222. The extrapolation therefore moves
from ≈226,000 lines to **≈603,000**. Both errors came from the artifact mismatch in §6, and both moved
in the same direction: the effort is larger than the earlier reports said.

---

## 2. What was measured, and what the measurement is worth

The instrument finds repeated n-grams. It was built for the compiled instruction stream, and it
applies unchanged to the text of the proof.

**The proof text repeats as heavily as the binary.** At the level where hex addresses, numerals, and
local state and step names are abstracted, 52.5% of lines sit inside a repeated 2-line pattern, and
28.0% inside a repeated 8-line pattern. Coverage is a greedy disjoint cover, not a union of
overlapping windows.

**The controls are decisive.** Shuffling lines inside each declaration preserves the length of each
declaration and its multiset of lines, and destroys only the order. That shuffle returns 15.7% at
n=2, 0.8% at n=4, and **0.0% from n=6 upward**, against 28.0% real. A planted 7-line pattern was
recovered 9 times of 9. The repetition is real structure in the order of the lines.

**Composition is 79.5% of the corpus** — 384 declarations naming two or more addresses, holding
19,776 lines. That is the bucket any pattern lemma reduces.

### What a share is not

52.5% of lines sitting inside a repeated pair of lines says the text repeats. It does not say a
lemma can absorb the repetition. Every figure in this record that is a *share* is a bound on what
could be replaced, never a saving. The record costs the cases where a specific lemma or tactic is
nameable, and says so explicitly where none is.

---

## 3. Where to stop, and the error that had to be corrected first

The covering strategy is hierarchical and greedy. At each length it finds every pattern that still
repeats, covers the sites of the pattern with the most sites, repeats until nothing at that length
repeats, and only then moves down one length. It does not stop at one pattern for each length.

**The first answer to "where do we stop" was n = 16, and it was wrong.** It compared lines recovered
for each lemma against a flat 39–83 line authoring cost taken from `InstructionClassSteps.lean`. Two
things are wrong with that comparison. The authoring cost is not flat, because a longer pattern costs
more to state — roughly 21 lines at n=2 rising to 105 at n=32, by the campaign's own numbers. And the
campaign had **already measured the quantity that decides this**: the break-even *site* count, which
falls as n rises, from 3.3 sites at n=2 to 1.1 sites at n=32.

The correct test compares sites for each lemma against that break-even. Sites for each lemma is
nearly flat at 2.5 across every band, so the falling break-even decides alone.

| band | lemmas | sites | sites for each lemma | break-even | margin | verdict |
|---|---|---|---|---|---|---|
| n ≥ 64 | 1 | 3 | 3.00 | 1.10 | 2.73× | pays |
| 32–63 | 10 | 20 | 2.00 | 1.10 | 1.82× | pays |
| 16–31 | 53 | 173 | 3.26 | 1.25 | 2.61× | pays |
| 10–15 | 77 | 190 | 2.47 | 1.37 | 1.80× | pays |
| **8–9** | 55 | 143 | 2.60 | 1.57 | **1.65×** | **pays** |
| 6–7 | 71 | 167 | 2.35 | 1.81 | 1.30× | marginal |
| 4–5 | 174 | 417 | 2.40 | 2.04 | 1.17× | marginal |
| 3 | 165 | 427 | 2.59 | 2.50 | 1.04× | marginal |
| 2 | 301 | 753 | 2.50 | 3.30 | 0.76× | loses |

**Stop at n = 8.** It is the last band that clears break-even with margin. The arithmetic still
passes down to n = 3, but the margin thins to noise and the library grows fast for little return:

| floor | lemmas in the library | lines recovered | lines for each lemma |
|---|---|---|---|
| 16 | 64 | 4,583 | 71.6 |
| **8** | **196** | **7,731** | **39.4** |
| 4 | 441 | 10,050 | 22.8 |
| 2 | 907 | 11,657 | 12.9 |

Moving the floor from 8 to 4 adds **245 lemmas to recover 2,319 lines**. Library size is itself a
cost, because somebody must find the right idiom among the entries.

**The general lesson.** The stopping point was decided twice from the same data and got two different
answers, because the first attempt invented a cost model while a measured one already existed. Prefer
a measured break-even to a modelled one.

---

## 4. The distinction that reorganises everything: repetition against quantification

There are two ways to remove a repeated obligation, and they have different cost curves.

- **Repetition** moves the repeated text into a lemma. Each site then applies that lemma.
- **Quantification** changes the argument so the obligation is proved one time for all sites. The
  obligation then never appears at a site again.

Take `s` sites and a block of `n` lines.

| mechanism | total cost | cost of one more site |
|---|---|---|
| the site writes the block | `n · s` | `n` |
| **repetition** — one lemma, `s` applications | `n + a·s` | `a` |
| **quantification** — stated one time | `n` | **0** |

Repetition makes the constant smaller. Quantification removes the dependence on `s`. **Only
quantification stops the proof growing with the binary**, which is the property the effort needs.

The boundary is easiest to see in a case nobody would get wrong. Nobody proves, for each machine
step, that the configuration matches `RV64IM_Zicclsm`. You state it one time as an invariant, show
that each step preserves it, and no step mentions it again. `ConfiguredMachinePre` is exactly that
construction. Every obligation that belongs inside it, and is instead re-derived at each site, is the
same mistake at a smaller scale.

### Three quantification mechanisms already work in this codebase

1. **A fact carried in the hypothesis bundle.** `ConfiguredMachinePre` holds `normal`,
   `retiredCounter`, `mstatusStoreMode`, `seccfgPresent`, `htifDisabled`, `platform` and
   `landingPad`. A site reads any of them as a projection, at no cost.
2. **An `autoParam` premise.** `InstructionClassSteps.lean` uses 37 of them. The site writes no
   argument and the elaborator discharges it.
3. **A quantified transport.** `agree_tryStepIncrement_instructionPreserved` states that the counter
   increment preserves *every* preserved register. It is one statement, not eighteen, and not one for
   each site.

### The worked example: `privilegeAfter`

Forty theorems each contain a fourteen-line block that derives two facts — `cur_privilege` still
reads `Machine` after the counter increment, and `mseccfg` still reads its bits. Those are the two
register reads `decode_run` consults.

Both facts are instances of mechanism 3, which already exists:

```lean
theorem agree_tryStepIncrement_instructionPreserved (state : State) :
    Agree instructionPreserved state (tryStepControlFlowAfterIncrement state)
```

`instructionPreserved r` is `platformPreserved r ∧ r ≠ x1`, and `platformPreserved` lists eighteen
registers including `cur_privilege` and `mseccfg`. The compact form of the derivation also already
exists, at `AbstractPremise.lean:122`:

```lean
((agree cur_privilege (by simp [platformPreserved])).trans privilegeRead)
```

One line, where each of the forty sites writes six.

**So the fix is not a new lemma applied forty times.** `ConfiguredMachinePre.stepContext` already
returns four facts about the state after the increment. Extend it to return these two. The cost for
each site becomes zero rather than one line, and no site can derive them wrongly. A second increment
function exists, `tryStepStoreAfterIncrement`, so the store path needs the same treatment.

The same argument applies to the 182-site region-membership proof. It wants a **tactic**, not a lemma
parameterised by the address pair, because a tactic takes no arguments at all. `owned_pc` already
exists in `BinaryFv/ProofProgress/OwnedPc.lean` and has **zero uses outside its own file**, while 182
sites write three `native_decide` calls by hand for the same job.

### The instrument cannot see quantification, and that biases its ranking

The covering ranks repeated *text*. A quantification removes text the covering never found, because
after the change the obligation is written nowhere. The ranking therefore values repetition too
highly and quantification too low.

The two conclusions of §3 and §4 meet. The covering tail below n = 8 is not worth one lemma for each
pattern. Quantification is the only mechanism that reaches it.

**The rule to apply before writing any pattern lemma.** Ask whether the obligation is an invariant of
the machine or of the region. If it is, it belongs in the bundle or in an `autoParam`, and a lemma
applied `s` times is the wrong fix — even when the line-count ranking recommends it.

---

## 5. A retraction, and why the compiler could not have caught it

An earlier draft named class-layer adoption the largest opportunity, at 6,326 lines. **That claim is
withdrawn.** Two counting errors and one normalisation retired it.

**The layer has seven lemmas, not five.** `configuredAuipcStep` and `configuredJalrCallStep` live in
`Level0MainSteps.lean`, not in `InstructionClassSteps.lean`, and the first search missed both. They
rank second and third in the layer by use, at 22 and 21.

**The corrected counts are much smaller.** 86 of 226 stepping theorems use the layer, not 43. The
theorems that do not hold 5,154 lines, not 6,326.

**The normalisation that retired it.** Divide by the instructions each group covers:

| group | theorems | lines | address mentions | lines for each address |
|---|---|---|---|---|
| uses a class lemma | 86 | 3,097 | 485 | **6.4** |
| writes the step by hand | 140 | 5,154 | 932 | **5.5** |

A theorem that uses the class layer costs *more* lines for each instruction. The two groups do not
step the same instruction shapes, so the comparison is not clean, and the honest reading is not that
the layer is harmful. It is that **no evidence shows the layer reduces lines for each instruction,
and what evidence exists points the other way.**

The reason is visible once the lines are grouped by how many addresses each theorem names. **79% of
the 5,154 lines are in theorems naming five or more addresses.** Those theorems compose; they do not
step one instruction. A lemma for one instruction cannot reach that bulk, whatever its design.

**A count of repeated lines is never evidence that the lever which removes them works.** This
retraction, and the four worthless generated cases in §7, are the same failure at two scales.

---

## 6. The whole binary study measured the wrong artifact. **Now resolved.**

Every figure in the original binary study — 4,435 instructions, 159 function instances, 74.2%
coverage by 149 patterns, and the candidate lists the lemma campaign worked from — describes an
**ELF64 RISC-V relocatable object** with sha256 `a387cf56…`. `main` does not prove anything about that
object. It proves against an **ELF64 RISC-V linked executable** with sha256 `6e7dbca1…`, the image
`GeneratedLevel1.lean` pins as `"ELF PT_LOAD memory image"`.

**How it was caught.** `writeSuccessMemcpyCallBaseStep` proves that `0x14d78` holds an `auipc` with
bytes `97 b0 ff ff`. Those bytes occur zero times in the object's CFG, whose highest program counter
is `0x4548`, and no constant load base maps `main`'s addresses onto it.

**The cause was a stale build result, not a design fault.** `result-zesu-ssz-decode-cfg` pointed at
revision `6acdbd9`, whose sibling output is named `…-rv64im-object-…`. The current
`nix/analysis.nix:41` already builds `zesuSszDecodeCfg` from `bin/zesu-ssz-decode`, the linked ELF.

**`nix build .#zesuSszDecodeCfg` resolved it, and the join is now verified by bytes:**

| check | result |
|---|---|
| CFG sha256 against `GeneratedLevel1.artifactSha256` | `6e7dbca17f09…` — **identical** |
| CFG `identityScope` against `GeneratedLevel1.artifactIdentityScope` | `ELF PT_LOAD memory image` — **identical** |
| `0x14d78` in the CFG | `auipc ra, 0xffffb`, bytes `97b0ffff` — **matches what `main` proves** |

### What changed once the artifacts agreed

| quantity | on the object (reported before) | on the endpoint image (correct) |
|---|---|---|
| instructions | 4,435 | **7,222** |
| functions | 37 | **52** |
| function instances | 159 | **234** |
| inlined instances | 123 | **187** |
| addresses proven by `main` | "488" (unjoined literals) | **296** |
| coverage | ~11% | **4.1%** |
| lines for each instruction | 51 | **83.5** |
| endpoint extrapolation | ≈226,000 | **≈603,000** |

**Every quantitative claim in `zesu-ssz-endpoint-motifs.md` and `binary-ngram-motifs.md` is about the
wrong binary, and so is every candidate address in `PLAN_MOTIF_LEMMAS.md`.** The campaign's five
measured savings rates are still meaningful, because they measure the *cost of a lemma against its
own baseline* and do not depend on which image the addresses came from. The break-even curve in §3
therefore survives. The rankings, coverage shares and address lists do not, and must be recomputed.

**The lesson is the same one as §5 and §8.** A tool that runs, and output that looks right, are not
evidence that the input was the intended object. Pin the artifact by hash and assert the hash against
what the proof pins, as a gate. This project already had the hash on both sides and never compared
them.

---

## 7. Reuse across function instances is much smaller than it looks

A natural plan is to prove one instance of a function and reuse the proof at its siblings. The data
limits it sharply. Every function with two or more instances in the endpoint image, with `main`'s
proven addresses joined in:

**First, a definition that a previous draft of this section got wrong.** Instance coverage is a
*fraction*, not a flag. An earlier version counted an instance as "proven" when the proof cited **one**
of its program counters. By that measure two instances of `sizeClassOfBytes` looked proven; in fact the
better of the two cites 3 of its 78 program counters. "Cited" and "proven" are different claims, and
only the fraction supports either.

**Measured properly, across all 234 instances in the image:**

| instance coverage | instances |
|---|---|
| ≥ 90% of program counters cited | **9** |
| ≥ 50% | 10 |
| more than 0% | 49 |
| **untouched** | **185** |

**185 of 234 instances are completely untouched.** Nine are essentially complete.

Every function with two or more instances:

| function | instances | shapes | ≥90% | >0% | untouched | instrs | % of image |
|---|---|---|---|---|---|---|---|
| `mem.readInt` | 27 | 15 | 0 | 0 | 27 | 363 | 5.0% |
| `mem.Allocator.allocAdvancedWithRetAddr` | 8 | 7 | 0 | 0 | 8 | 327 | 4.5% |
| `alt_fl_alloc.sizeClass` | 4 | 3 | 0 | 2 | 2 | 330 | 4.6% |
| **`alt_fl_alloc.sizeClassOfBytes`** | **4** | **1** | **0** | **2** | **2** | **312** | **4.3%** |
| `ssz.readU32` | 15 | 9 | 0 | 0 | 15 | 147 | 2.0% |
| `ssz.readU64` | 8 | 5 | 0 | 0 | 8 | 142 | 2.0% |
| `ssz.decode__struct_1051.f` | 5 | 5 | 0 | 0 | 5 | 59 | 0.8% |
| `ssz_decode_observation.Encoder.raw` | 23 | 6 | **3** | 11 | 12 | 52 | 0.7% |
| `extern_io.write_output` | 23 | 6 | **3** | 11 | 12 | 52 | 0.7% |
| `math.mul__anon_1837` | 9 | 7 | 0 | 0 | 9 | 43 | 0.6% |
| `mem.Allocator.rawRemap` | 3 | 2 | 0 | 0 | 3 | 18 | 0.2% |
| `mem.Allocator.rawFree` | 3 | 2 | 0 | 0 | 3 | 14 | 0.2% |
| `mem.Allocator.rawAlloc` | 3 | 2 | 0 | 0 | 3 | 12 | 0.2% |
| `mem.writeInt` | 4 | 4 | 0 | 0 | 4 | 8 | 0.1% |

**Exactly one function has all its instances sharing one opcode shape:** `sizeClassOfBytes`, with all
four contiguous. Every other function splits, because the compiler specialised each call site.
`mem.readInt` has 27 instances and 15 shapes. `allocAdvancedWithRetAddr` has 8 instances and 7 shapes.

**So the reusable unit is not the function instance. It is the shape** — the opcode or class sequence,
which is what the covering already finds. A list of idioms and a list of motifs are therefore the same
list.

### The transfer opportunity is almost empty

A plan to transfer an existing instance proof to its siblings has **one** candidate: the
`ssz_decode_observation.Encoder.raw` / `extern_io.write_output` pair, with 3 instances at ≥90% and 12
untouched, worth 52 instructions — **0.7% of the image**. The two rows report identical figures, so one
is probably inlined into the other and the evidence generator must resolve that rather than
double-count it.

No other function has a single instance at even 50%. **There is essentially no existing per-instance
work to transfer.**

### The real opportunity is reuse within new work

`sizeClassOfBytes` remains the best pilot, but for the opposite reason to the one a previous draft
gave. It is not half proven. It is **entirely unproven, with the cleanest possible reuse structure**:

- 4 instances, **1 opcode shape**, 4 of 4 contiguous;
- 78 instructions each, **312 instructions = 4.3% of the image**;
- one lemma, applied four times, for 4.3% of the endpoint.

That is a larger prize than the whole transfer list, and it tests the pipeline on new work, which is
what the remaining 95.9% of the image consists of.

**Contiguity is a second hard gate.** `rawRemap` and `rawFree` are 0 of 3 contiguous. `Seg` cannot
state a non-contiguous instance at all, because the scheduler interleaved copies. An instance is a
*set* of program counters, not a run, and the evidence file must carry that flag or agents will spend
effort on impossible tasks.

---

## 8. The failure mode that any generated-starter workflow will scale up

Four generated case files typechecked and reported savings of 66%, 71%, 71% and 19%. **Those numbers
were worthless.** `StepData.run` is a hypothesis, nothing forced it satisfiable at the real address,
and at those sites it was not. The files were deleted.

**The compiler did not catch it and could not.** What caught it was cross-referencing every case's
addresses against the CFG's mnemonics.

A pipeline that emits starter files with `sorry` industrialises this. A file with a wrong hypothesis
will be filled, will compile, and will prove nothing about the binary. Any such pipeline therefore
needs, as a blocking gate that runs before an agent sees the file:

1. every address in a starter file checked against the CFG's mnemonic and bytes;
2. a mutation test on the gate itself, proving the gate can fail.

The second item is not optional. A `#guard` file in this project once produced empty output because
doc comments preceded the commands, and the empty output read as success. Flipping 17740 to 17741
produced the same empty output, which proved the check had no power.

Two smaller constraints. `tools/check_lean_trust.py` forbids `sorry`, so starter files need a staging
area the trust gate excludes. And `native_decide` costs 84.8ms each, with an 18.6-minute floor already
measured for the full covering, so the generator needs a budget for each instance.

---

## 9. What follows

Two plans carry this forward. They live in `docs/ai/plan/` and are not committed.

| plan | scope |
|---|---|
| `PLAN_HLEVEL2_REWRITE.md` | Clean the pattern tooling, then rewrite the hLevel2 proof with these strategies as a PR stack whose final step shows the line reduction. |
| `PLAN_PROOF_EVIDENCE_PIPELINE.md` | Evidence gathering for every function instance, then motif annotation and idiom hinting, with the docs and agent setup to make proof writing a small-scope task. |

Ordering that follows from this record:

1. **Recompute the covering on the endpoint image.** §6 is resolved, but every ranking, coverage share
   and candidate address in the two study reports and in `PLAN_MOTIF_LEMMAS.md` describes the wrong
   binary. Recompute before using any of them. Add the artifact-hash assertion as a gate so this
   cannot recur.
2. **Build the §8 gate before any starter file is generated**, and mutation-test the gate itself.
3. **Prefer quantification to repetition** wherever §4's rule applies. Take the three named cases
   first — extend `stepContext`, add the region tactic, and cover the store-path variant — because
   each is pure deletion with a working precedent.
4. **Set the pattern-lemma floor at n = 8**, from §3.
5. **Pilot on `sizeClassOfBytes`.** One shape, four contiguous instances, two already proven. If a
   pipeline cannot make that case cheap, a 196-entry library will not help.

### The honest summary of where the effort stands

Coverage is **4.1%** of the endpoint, at **83.5 lines for each instruction**, extrapolating to
**≈603,000 lines**. The three retractions in this record all moved the same way: the work is bigger,
and the measured levers are weaker, than the earlier reports claimed. The two mechanisms that survive
scrutiny are quantification, which has no measured ceiling yet, and pattern lemmas at n ≥ 8, which are
measured and bounded. Nothing in this record shows that repetition alone closes a 603,000-line gap.
