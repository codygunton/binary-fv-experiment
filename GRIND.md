# GRIND.md — simp and grind set conventions

This document is the single source of truth for how this repository organizes `simp`-based and
`grind`-based proof automation. Read it before writing a closing tactic that more than one proof
will use, before adding a `@[simp]` or `@[grind =]` attribute to a shared lemma, and before
proposing a new named set.

`AGENTS.md` links here from its proof-automation section. Do not duplicate this content there.

---

## 0. Read this first — what is built, and the four rules that matter

Everything below section 1 was written before the mechanisms existed. This section is what was
actually built and measured; where it disagrees with a later section, it wins.

### What exists

| mechanism | where | what it removes |
|---|---|---|
| 13 instruction-class lemmas | `Zesu/MachineExecution/InstructionClassSteps.lean` | a 40–80 line single-instruction proof becomes one call; every obligation is an `autoParam` the caller never writes |
| write-set frame | `RiscV/Logic/RegisterAgree.lean`, `RiscV/Step/ControlFlow.lean` | `WritesOnlyRegs W s t` states a step's write set once; any read outside it is a membership check |
| **the frame multi-pattern** | `RegisterAgree.lean` §Automation | `grind` walks a chain of write-set facts itself and discharges the membership condition |
| hypothetical decode | `InstructionClassSteps.lean` | the class lemma derives its own decode context; the caller supplies nothing |
| `Seg` / `ConfinedPrefix` | `Seg.lean`, `SequentialSplice.lean` §6 | straight-line segment composition |

The repository's **only two grind registrations** are:

```lean
attribute [grind →] Agree.trans
grind_pattern WritesOnlyRegs.get => WritesOnlyRegs W s t, t.regs.get? r
```

### Rule 1 — you need a multi-pattern when the conclusion and the antecedent each omit what the other has

This is the single most useful thing learned, and it is stated too weakly in section 5. Both
registrations that pay in this repository needed a multi-pattern, and both were **rejected outright**
by the single-sided attributes — not silently inert, but a hard error naming the problem:

```
`@[grind ←] theorem WritesOnlyRegs.get` failed to find patterns in the theorem's conclusion
`@[grind →] theorem WritesOnlyRegs.get` failed to find patterns in the antecedents of the theorem
```

The conclusion `t.regs.get? r = s.regs.get? r` never mentions the write set `W`; the antecedent
`WritesOnlyRegs W s t` never mentions the register `r`. Neither side alone determines the
instantiation. The pattern over **both** determines all four variables.

**The tell:** a lemma of the form "given a fact about a *set*, conclude something about a *member*"
always has this shape, because the set and the member never appear together in one subterm. Reach for
`grind_pattern` immediately rather than trying attributes first.

### Rule 2 — the payoff is (sites × lines saved) − setup, and the setup is not zero

The mechanism above pays enormously in one place and is **net negative** in another, for a reason
worth internalising:

- **Composition ladders — pays.** A proof carrying *n* registers through *m* steps writes one `have`
  per (register × step). One `have w := <transformer>_writes …` per step collapses the whole product.
  Measured: four registers through two steps close in **one `grind`**, replacing ~8 `have`s / ~32
  lines. Five wrapper composition proofs, −112 lines, elaboration time unchanged (363 s → 362 s);
  fourteen `DecodeInlineProof` compositions, −117; `memcpy_adv` 534 → 271.

  *A correction to an earlier claim in this file's history: Lean does **not** parallelize elaboration
  within a module. Measured at 135% CPU across 34 threads — one core. Summing profiler tactic times
  and comparing to wall-clock does not show parallelism, because those times are nested and
  double-count. Module elaboration time is a serial segment of the build; see `AGENTS.md` on module
  granularity.*

  **Arming it costs one line, not three.** Write

  ```lean
  have w : WritesOnlyRegs _ s t := <shape>_writes _ _ _ _ _
  ```

  — the write set and every explicit argument unify against the `let`-bound alias. The explicit
  ascription is what makes it match a goal stated in terms of a project wrapper def; `..` does *not*
  work in place of the underscores, because `WritesOnlyRegs` unfolds to a Pi and over-applies.
- **Isolated reads — does not pay, and was reverted.** Replacing `(...).get x2 (by decide)` with
  `have w := …_writes …` plus `grind` is *two lines replacing two lines*. Applied to 53 such sites
  across four files it came to **net +6 lines**.

So before applying any mechanism in bulk: count the sites, and count what one invocation *costs*.
The rate at which a mechanism collapses its best case tells you nothing about its average case.

**Three registrations have now been built, verified, and reverted for having no population.** All
three were correct; none had enough to automate. Do not rebuild them without new evidence:

| rule | why it was reverted |
|---|---|
| per-address instruction fact table (`bc83463`) | duplicated `MachineRegions.words`, which already exists and is already consumed |
| memory-side `WritesOnlyWithin.get` multi-pattern (`f78d965`) | works through unions, chains and symbolic bases — but only ~31 links tree-wide sit in chains of 3+ |
| `Agree.get` multi-pattern + `platformPreserved_apply` | works, and needs **no** per-site setup since the `Agree` is already in scope — but only **11** multi-line Agree-derived reads exist tree-wide; the other 27 are already one-liners like `(agree misa (by simp [platformPreserved])).trans misaBaseRead`, where `grind` saves one line |

The `Agree.get` case is the sharpest lesson, because it looked like the *best* candidate on the
count that first came to hand — 239 register-carrying `have`s across 56 theorems holding an `Agree`
hypothesis. Nearly all of those carries turned out to go through a **write set**, not the `Agree`,
and the ones that did use the `Agree` were already terse. **Count the sites in the shape the rule
actually matches, not the sites that merely mention its hypothesis.** The working patch is preserved
in the session scratchpad if a memory- or agreement-heavy layer ever grows the population.

### Rule 3 — know which kind of side condition you have, because one kind is fatal

The multi-pattern only works if `grind` can discharge the membership obligation. Three cases, all
measured here:

- **Decidable by `decide`** — registers. `RegSet.only` and `RegSet.union` are `@[reducible]`
  precisely so typeclass synthesis can build the `Decidable` instance; without it every `(by decide)`
  fails with `failed to synthesize Decidable`. A regression `example` in `RegisterAgree.lean` pins
  this. **This is the case that works best.**
- **Arithmetic** — memory regions. `Region := Nat → Prop`, so `¬ range base size a` is an arithmetic
  obligation, not a decidable one. Registering the membership equivalences (`range_apply` etc.) as
  `@[grind =]` lets `grind` see through the constructors and hand the residue to its arithmetic core.
  This *works* — verified through unions, chains, and a symbolic base separated by a hypothesis — but
  see rule 2: in this repository it had only ~31 links to collapse and was reverted. The technique is
  in commit `f78d965` if a memory-heavy layer ever needs it.
- **Not decidable at all** — `platformPreserved`. `WritesOnlyRegs.agree` (write set ⇒ `Agree`)
  **cannot be a grind rule**, with or without a multi-pattern. Its `RegSet.Disjoint P W` side
  condition bottoms out in `¬ platformPreserved r`, and `platformPreserved` is a plain `def`. That is
  exactly why the existing disjointness lemmas case-split its eighteen disjuncts by hand. Do not
  retry this; the two-line chained form is minimal.

### Rule 4 — the verification traps here are worse than the proofs

Three checks in this project reported the *opposite* of the truth. All three were mine.

- **Stale `.olean`.** `lake env lean <consumer>` elaborates only that file and resolves imports from
  the `.olean`s that already exist. After editing a framework module, a consumer check is meaningless
  until `lake build <that module>` runs. This caught two people on the same file the same day — once
  hiding a real failure, once manufacturing two fake errors that caused a working mechanism to be
  reported as broken. **Always `lake build` the edited module first.**
- **A strip test on a site where the mechanism was never load-bearing.** Deleting the boilerplate from
  a file whose call sites all had the hypotheses in scope proved nothing; the failing shape
  (`f pre.machine (Agree.refl state)`) lived in a different file. Pick the proving ground by the shape
  that fails, not by convenience.
- **A negative control that cannot fire.** `fail_if_success grind` passes both when the rule correctly
  refuses *and* when the goal was malformed. Run the meta-control: point `fail_if_success` at a case
  that **is** derivable and confirm it reports "the tactic succeeded but was expected to fail."

For a goal that is genuinely underivable, the control must wrap the `have` — `fail_if_success (have :
G := by grind)` — because there is no proof of `G` for the check to sit inside. Place it *before* the
`have`s that would make the goal derivable, so a failure is the rule declining rather than a
contradiction. Keeping a few of these in the file permanently is cheap and worth it.

A fourth trap, this one about the goal rather than the check: **a control whose goal is false proves
nothing either.** I wrote `Agree platformPreserved s t ⊢ t.regs.get? x2 = …` as a power check and
concluded the rule was broken. `x2` is not in `platformPreserved` — it holds `x1` and seventeen CSRs
— so `grind` was right to fail. Read the predicate's definition before writing a test against it.

### Rule 5 — a deleted theorem still compiles, so the compiler cannot guard a refactor

**This is the most dangerous rule here.** Every other failure mode in this document announces itself
as a build error. This one does not: if a refactor, a merge resolution, or an over-eager `simp`
cleanup *removes* a declaration, the file still elaborates. Nothing references it, so nothing breaks.

It happened on a real merge. `ssz-level1` had moved ahead and both sides had rewritten the same proof
bodies; a hunk-level resolution silently dropped two theorems, **one of them newly added upstream**,
and the merged file compiled clean. It was caught only by diffing theorem-name sets.

**Do this on every merge, every large refactor, and before every commit that deletes anything:**

```bash
comm -23 <(git show <other>:path | grep -oE '^(private )?(theorem|lemma) [A-Za-z0-9_]+' | awk '{print $NF}' | sort) \
         <(grep -oE '^(private )?(theorem|lemma) [A-Za-z0-9_]+' path | awk '{print $NF}' | sort)
```

Empty output means nothing was lost. A non-empty result is either a bug or an intentional deletion
you must be able to name and justify. Track the whole-repo count too — it must never drop:

```bash
git grep -chE '^(@\[[^]]*\]\s*)?(private )?(theorem|lemma) ' <rev> -- 'BinaryFv/**/*.lean' | awk '{s+=$1} END {print s}'
```

**When a merge conflicts inside proof bodies both sides rewrote, take the other side wholesale for
that file and re-apply your work on top.** Losing your own refactor is cheap; losing someone else's
theorem is not, and you cannot tell the difference by building.

### Rule 6 — a skip is a verdict on one lever, not on a file

Work in this tree is done by passes, each applying one mechanism. When a pass reports "skipped", it
means *that mechanism* did not apply. It does **not** mean the theorem is irreducible or that the
file is finished — and reading it that way is what makes work look exhausted when it is not.

Concretely: after a pass reported diminishing returns at −23.6%, re-measuring per *theorem* rather
than per *file* found **859 lines still servable by the class lemmas**, eight of them in a file
logged as effectively complete. Pressing on took the total to −27.2%.

Its sibling: **re-test a blocker before trusting it.** Two of the largest wins in this project were
sitting behind written-down verdicts that predated the tools which dissolve them —
`MemcpyProof` ("takes `retired` universally, so the class lemmas don't apply" — true of the class
lemmas, false of the write-set frame, −318 lines) and `HasExactErePrefixProof` (a conclusion-shape
mismatch that did not exist, because the conclusion was a *reducible* `abbrev` for exactly what the
class lemmas produce).

**Write verdicts that name the mechanism they block.** "Blocked" with no named mechanism is a note to
re-test, not a result. Re-measure after every round rather than trusting the previous round's
inventory.

### Rule 7 — triage a theorem by its premise bundle, not by how it looks

Before attempting any migration, check what the theorem *carries*. This decides servability outright
and saves a wasted attempt:

| the theorem has | class lemmas can serve it? |
|---|---|
| `DecoderMachinePre` + `Agree platformPreserved` | yes — plain lemma names |
| `DecoderMachinePre` + `Agree decoderPreserved` | yes — the `…OfDecoderAgree` siblings |
| `ExitPlatform`, `RawResultMachinePre`, `InstructionStepPlatform` | **no** — different bundle entirely |
| a conclusion `∀ retired, …` | **no** — the lemmas conclude `∃ retired, …`, and `∀ retired, P` does not follow from `∃ retired, P`. This is logical strength, not a unification failure, and no amount of massaging fixes it |
| generic over a symbolic `pc`, or a store target `stackBase + off` for symbolic `stackBase` | **no** — `pcIn`/`allowed`/`aligned` are `native_decide`/`decide` autoParams and cannot discharge a symbol |

Also check *what the theorem proves*, not which lemmas it cites. A theorem that mentions `try_step`
more than once, or concludes a `Trace`/`SegmentChain`, is a **composition** and wants the write-set
frame; a theorem concluding one `Runs (try_step …)` is a **step** and wants a class lemma. Value and
classification lemmas are neither. Counting "theorems that do not cite a class lemma" as migration
targets inflates the estimate badly — it sweeps in every composition and every definition.

### Rule 8 — syntax counts locate bulk; they do not identify repetition

A line-category count over proof bodies will tell you where the lines are and mislead you about why.
Measuring "39% of these lines are argument continuations" led to an autoParam campaign that recovered
9 lines; the actual causes were invisible to the count because **repetition looks like ordinary
content**.

The shapes that were actually costing lines, worth checking for by hand:

- **A closed sub-proof pasted verbatim.** One was 21 lines with *no free variables at all*, inlined
  three times — and the identical extraction already existed one level up in the import graph.
- **An un-named per-step bundle.** Eleven steps each rebuilt the same two records from the same five
  facts through a four-`have` block. One helper: −99 lines over ten sites.
- **Local twins of lemmas that already exist upstream and are already imported.** Six of them in one
  file. Two were *named in the upstream file's own doc comments* as twins awaiting deduplication.
- **A postcondition re-stated per retained fact.** Consumers of a twelve-conjunct result each
  re-declared five to nine of them with full type annotations; one `rw … at` retypes them in place.
- **Projection chains** — `payload.2.2.2.2.2.2.2.1`, one `have` per field, where an `obtain` does it.
- **A long type spelled in proof-internal `have` annotations.** A five-line type at thirteen sites; a
  `private abbrev` collapses each to one. (Occurrences in *statements* are a different matter — see
  the invariant below.)
- **A side-condition list that is always the same tactic.** Five conditions spelled across five lines
  at fourteen sites, all `by simp [decoderPreserved, platformPreserved]`; `<;> simp [...]` closes
  them. Worth −53.

**`maxHeartbeats` overrides are a symptom, not a setting.** Four `set_option maxHeartbeats 1000000`
in one file all became removable once its duplication was gone — the theorems then compiled at
`50000`, four times *under* the default. Treat an override as a marker of duplicated or unfactored
work, and re-check it after any reduction rather than carrying it forward.

### The invariant everything rests on: never change a theorem statement

Every pass in this project changed proof bodies only. That is not fastidiousness — it buys three
things that are hard to get any other way:

- **The work is splittable by technique.** Because no statement moved, any subset of the changes
  compiles as long as the toolkit is present, which is what allowed a 25-commit branch to be
  re-cut as a four-PR stack, one per technique, with the top provably identical to the original.
- **A reviewer can trust the diff.** A changed proof cannot weaken a claim; a changed statement can.
- **Mutation testing stays meaningful.** Non-vacuity checks mutate an operand and expect rejection;
  that only proves something if the statement is fixed.

When a reduction genuinely needs a statement change — bundling loose hypotheses into a structure is
the usual case, and is worth about −45 lines where two theorems share a long prelude — land it as its
own clearly-labelled change, never folded into a body-only pass.

### Splitting work into a stacked PR series — the check that is not the compiler

Body-only changes make a branch splittable by technique, but "no statement changed" does **not** mean
any subset compiles. A pass also *adds* declarations — private helpers, extracted lemmas, write-set
facts — and a file in an earlier PR that references one defined in a later PR breaks, even though
nothing about it looks wrong. Both breakages found while cutting this stack were of exactly that
shape, and neither was visible from imports alone: one file needed a lemma extracted in a later PR's
file, another needed a `_writes` helper added there.

Do not guess the coupling from the import graph. Compute it: enumerate every declaration the work
*adds* (diff the declaration-name sets per file, base versus head), map each to the PR that defines
it, then grep for references and flag any referencing file assigned to an **earlier** PR than its
definer. Zero violations is the precondition for cutting; anything else names the file to move and
where to move it.

That check runs in seconds and found the one remaining violation after a full 5-minute build had
found only the first. Run it before every build, not after.

Two cheap invariants worth asserting on the finished stack: the top branch's tree should be
**identical** to the un-split branch (`git diff <top> <original>` empty), which proves nothing was
lost or duplicated in the division; and each PR should be built standalone, since a stack that only
builds at the tip is not reviewable one PR at a time.

### Concurrency: agents in one worktree can destroy each other's work

Two agents editing disjoint *files* in one worktree are still not isolated. One ran `git stash` to
get a clean timing baseline; `stash` is repo-wide, so it silently reverted the other agent's live
file to HEAD mid-task. The second agent noticed its edits had vanished, re-applied them, and shipped
correctly — but that recovery was luck, not design.

Rules: **never run a repo-wide `git` command** (`stash`, `checkout`, `restore`, `clean`, `reset`)
from an agent working alongside others — scope every path explicitly.

**`git add -A` and `git commit -a` belong on that list, and they are the easy ones to miss** because
they are not destructive: they *capture* rather than discard. The coordinator doing docs work while a
sweep agent was mid-run committed seven files of unverified, in-progress proof edits under a commit
message describing only the documentation. Nothing was lost, but the history now misattributes the
work and the commit was never verified as a unit. Stage explicit paths — `git add <path> <path>` —
whenever anything else is live in the tree, and check `git status` before every commit rather than
after. To get a clean baseline for
timing, read the file from git (`git show HEAD:path`) into a scratch copy instead of mutating the
tree. If a stash does happen, do not drop it: it may be the only copy of another agent's state.

### Two syntax facts that cost real time

- `grind [...]` brackets accept only **bare identifiers**, not applied terms: `grind [foo x y]` is a
  parse error. They also reject facts already reachable from context as "redundant parameter". The
  reliable idiom is a local `have := <term>` before a bare `grind`.
- **A `rw … at h₁ h₂ h₃` location list must stay on ONE line.** A continuation line parses as a new
  tactic, so the rewrite half-applies and the rest silently does nothing. It compiles or fails for
  reasons that look unrelated to the real cause.
- When an intermediate state is a `let`-bound alias for a project wrapper def
  (`wrapperAfterDwordStore`, `rawResultAfterDiscriminant`, …) rather than a raw `afterRegisterWrite`
  application, the introduced `have` needs an **explicit type ascription in the alias's name**.
  Otherwise its inferred type mentions the unfolded primitive, which does not syntactically match the
  goal — `grind` does not delta-unfold semireducible defs, by design (see the 18×–126× rule).

### Correction to section 5's depth claim

Section 5 says chains close at 1–3 hops and fail at 4–5. That is true of **frame-fact chaining through
equalities**. It is *not* true of the write-set multi-pattern, which chains arbitrarily deep because
each hop is one E-match rather than a rewrite: a four-step chain with three simultaneous register
reads closes with a bare `grind` in ~1 s. Depth is a property of the mechanism, not of `grind`.

---

## 1. Why

`decodeInline_first_argument_setup` in `BinaryFv/Zesu/MachineExecution/DecodeInlineProof.lean` steps
through four instructions in about 110 lines. Each instruction costs an `obtain` of the step lemma,
a `let` naming the successor state, a `have` re-deriving `Agree platformPreserved`, a `have`
re-deriving the `PC` value, and one `have` per register whose value the next step needs:

```lean
have input2 : s2.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
  simp [s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, pre.inputValue]
```

That `have` answers "what does `regs.get? x8` read after `afterRegisterWrite` runs". It is a general
fact about `afterRegisterWrite`, but it is stated for one concrete state, used once, and discarded.
The next step asks the same question about `x9` and pays again.

Measured over PR #60 (`ssz-level1`, 70 Lean files, 29,587 added lines):

| Quantity | Count |
|---|---|
| `have` | 3,784 |
| `obtain` | 827 |
| proof lines vs signature lines | 26,585 vs 10,330 |
| occurrences of `tryStepControlFlowAfterRetired` | 539 |
| `Agree.trans` | 95 |
| `apply RegionPcs.iff_inRanges.mpr` | 129 |
| `apply functionInstanceExecutionPcs_iff_ranges.mpr` | 110 |
| the literal line `(by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)` | 112 |

Three costs follow. Adding an observer to a step means editing every proof that steps through it.
Reviewers read the same unfolding list hundreds of times. And a proof that needs a fact nobody
named yet re-derives it inline rather than adding it once.

The fix is to name each recurring fact once in a scoped set, expose one tactic that closes the class
of goals, and migrate consumers to it. A new fact then costs one line that every consumer picks up.

## 2. What is different here from a repository that writes its own assembly

This matters for which conventions transfer, so it is stated before the rules.

`EvmAsm` (github.com/codygunton/evm-asm) authors its RISC-V program through a Lean DSL and proves
facts about what it wrote. This repository does the opposite: `zesu_decode_raw` is compiled by an
external toolchain, pinned as an ELF, and decoded through Sail. We prove facts about a binary we do
not control.

Three consequences:

- **The set of state transformers is closed.** `afterRegisterWrite`, `coreControlFlowNextState`,
  `tryStepControlFlowAfterIncrement`, `tryStepControlFlowAfterRetired`,
  `tryStepControlFlowAfterTick`, and the memory stores are fixed by the RISC-V step semantics and by
  `BinaryFv/RiscV/Step`. They do not grow as we prove more. A repository that writes its own
  assembly gains a new transformer every time it adds a DSL macro. Ours is enumerable today, so a
  set indexed by transformer can be checked for completeness rather than merely extended.
- **The set of state observations is likewise closed**: the architectural registers, `mem`, the CSRs
  named in `DecoderMachinePre`, and the predicates we define over them.
- **No proof cost can be removed by changing the target.** `EvmAsm` can rename an offset, restructure
  a block, or mark a definition `@[irreducible]` to make a proof cheaper. We cannot. Every reduction
  must come from how the proof is written, which raises the value of this work relative to that
  repository rather than lowering it.

One opportunity follows that `EvmAsm` structurally cannot have. Our address literals never drift
while the binary is pinned, but every one of them changes together when the binary is regenerated.
`tools/generate_elfling_program.py` already emits the address-bearing program. Address facts should
therefore be **generated from that artifact alongside it**, not hand-enumerated in a Lean file that
must be re-derived after regeneration. `EvmAsm` enumerates its `signExtend12` offsets by hand
because it is authoring them; we extract ours, so we can emit them. The survey should report whether
this is worth doing and how many facts it would cover.

## 2a. What we are optimising

Three costs, ranked. They usually agree; where they conflict, this order decides.

1. **Tokens spent writing proofs.** The binding constraint. Measured proxy: how many names an author
   must know or discover to write a step. Across `MachineExecution/` there are 2,715 `simp` call
   sites citing **8,500 name-citations** from 624 distinct names, mean 3.1 per call, max 36. Six
   names carry 35% of it. Every citation is an act of recall or search.
2. **Build time.** `Level2Epilogue.lean` elaborates in 51.7 s, 33% of it in `simp` across 996 calls.
3. **Source lines.** A proxy for both, and the one most likely to mislead — see the note below.

**A tactic macro decouples cost 1 from cost 2.** The author writes one name; what runs inside is
invisible to them. So optimise a macro's *internals* for build time and its *surface* for authoring
cost. An internal `first | grind | (simp only […]; closer)` ordering is a build-time decision only.

**The design target is one macro name per goal class, with a predictable domain and an informative
failure.** The in-repo proof that this works is `decode_run` (`DecodeTactic.lean:21`): used 246
times, and no author has ever needed to know what is inside it. Four such names —
frame, region-membership, fetch, address — would replace most of the 624.

Two consequences that do not follow from line counts:

- **A correct lemma that is expensive to *invoke* is under-used.**
  `afterRegisterWrite_register` states the single most-repeated goal in the PR exactly. It has **49
  external call sites, against 192 inline re-derivations that unfold `afterRegisterWrite` by hand —
  20% adoption**. Citing it requires six positional arguments plus five explicit disequalities,
  while the `simp` list above it is copy-pasteable. Invocation cost is a first-class design
  constraint, not a detail.

  *(An earlier revision of this document said "used twice repo-wide". That was wrong — one survey
  area reported 2 where two others reported 48 and 50, and the wrong figure was carried forward. The
  finding survives as under-adoption rather than total avoidance, and the expected payoff is
  correspondingly smaller. Recount before quoting any figure here; see section 8's Stage 0 note.)*
- **Predictability beats speed.** A tactic that closes at chain depth 3, fails at 4, and needs
  `(ematch := 40) (gen := 20)` at depth 10 is expensive even when fast, because each failure is
  opaque and starts a guess loop. Prefer a convention that always works — one hop per `have` — over
  a budget that usually does.

## 3. Two sets, kept separate

Do not put everything in one set. Two distinct kinds of fact appear in these proofs and they need
different treatment.

**Step-unfolding facts** are definitional: `afterRegisterWrite`, `coreControlFlowNextState`,
`tryStepControlFlowAfterIncrement`, `tryStepControlFlowAfterRetired`, `tryStepControlFlowAfterTick`,
`Std.ExtDHashMap.get?_insert`. These belong in a **named simp set only**. They must not be
registered for `grind`: `grind` will keep unfolding them and can loop. `EvmAsm` reached the same
conclusion independently for its Sail monad plumbing and keeps its `sail_step` set simp-only for
exactly this reason.

**Frame facts** state what one observation reads after one transformer runs, in the shape

```lean
observer (transformer state args …) = <expression in terms of state>
```

These are ordinary equations, are safe for `grind`, and are what makes chained reasoning collapse.
They are the set worth building.

The `Agree platformPreserved base state` family sits awkwardly across this split, because it relates
two states rather than observing one. See section 3a, which is the more general answer.

## 3a. The write-set frame — BUILT (`784ab8a`, automated in `1b40460`)

> **Status corrected.** This section was written as a proposal and its "currently missing" framing is
> obsolete. The design below was built essentially as described and is live in
> `RiscV/Logic/RegisterAgree.lean` and `RiscV/Step/ControlFlow.lean`. Read section 0 for what it
> automates and where it does and does not pay; the design rationale below is still accurate.

A grid of frame facts is O(observations × transformers) lemmas and **does not generalise across
observations**: every new observation needs a new row against every transformer. With 141 function
instances still to prove, that is the wrong asymptotic.

The general mechanism already has its primitives in this repository and they are unused.

**What exists.** `RiscV/Logic/Framing.lean` defines `RegisterEqualOutside before after written` and
`MemoryEqualOutside before after address`, with `writeReg_register_frame` and
`writeByte_memory_frame` proving them for a single write. `RiscV/Logic/RegisterAgree.lean` defines
`Agree (P : Register → Prop) base t` — already set-indexed — with `refl`, `trans`, and `weaken`. Its
docstring states the intended design:

> Machine loops instantiate `P` with the complement of the write set of the loop body, giving the
> usual "stable registers are preserved" relation.

**What is missing.** Measured: `RegisterEqualOutside` is used in **2** places outside its defining
file, `MemoryEqualOutside` in **0**, and **no lemma anywhere derives `Agree` from a write set** —
while 140 lemmas prove `Agree` by hand, one per transformer.

Two gaps cause that:

1. `RegisterEqualOutside` takes a **single** `written : Register`. But the real transformers write
   sets: `afterRegisterWrite` writes destination, `nextPC`, `PC`, `minstret`, and
   `minstret_increment` — five. A single-write frame cannot state one step, so chaining it is no
   cheaper than the inline `simp`.
2. Because there is no write-set bridge, `P` gets instantiated with two fixed hand-chosen sets.
   `platformPreserved` is an 18-way disjunction of `x1` and 17 CSRs and holds **no other
   general-purpose register**, so every read of `x2`, `x8`–`x13`, or `x18` through a step falls
   outside it and is re-derived inline. That is the origin of the two largest measured rows: 284
   `executeState` re-proofs across 23 files and 181 `afterRegisterWrite` re-proofs across 15.

**The three declarations that close it:**

```lean
def EqualOutside (before after : State) (W : Register → Prop) : Prop :=
  ∀ r, ¬ W r → after.regs.get? r = before.regs.get? r

theorem EqualOutside.trans :                       -- the frame rule
    EqualOutside s t A → EqualOutside t u B → EqualOutside s u (fun r => A r ∨ B r)

theorem agree_of_disjoint :                        -- the missing bridge
    EqualOutside s t W → (∀ r, P r → ¬ W r) → Agree P s t
```

Then one write-set lemma per transformer (five of them, a closed set), and the cost model changes
shape: **O(steps) to compose a trace's write set once, then O(1) per observation** — a `decide` on
membership — instead of O(steps × observations) hand-derived facts. For the 19-step wrapper prefix
with nine observations that is 28 obligations instead of 171.

**Why this is the generalising answer**, and the reason it outranks the grid:

- It is **observation-agnostic.** Any register outside the write set is preserved whether or not
  anyone anticipated caring about it. New observations cost nothing.
- It is **instance-agnostic.** Write sets are a function of the instruction encoding, which
  `tools/generate_elfling_program.py` already extracts, so they can be generated for all 141
  function instances rather than hand-written per function.
- It subsumes `platformPreserved` and `decoderPreserved` rather than replacing them: both follow
  from `agree_of_disjoint` by `decide`, so no existing consumer changes.
- On the section 2a metric it is the cheapest surface in the survey: the author writes no register
  names at all, only the step, and membership discharges automatically.

The memory side is the same shape with `Region` in place of the register predicate; `Region`,
`Region.union`, and disjointness lemmas already exist in `Zesu/Contracts/Footprint.lean`, which is
a **read**-footprint logic for value representations and is a separate, working use of the same idea.

**Status: designed from measurement, not yet tested.** The probe is small — define the three
declarations, give `afterRegisterWrite` its write-set lemma, and check that a `have` currently
costing a six-name `simp` closes by `decide`. Do that before phase 2 commits to grid shape.

## 4. Registering a set

### Layout A — grind only

Use when every consumer calls the tactic macro and nobody needs `simp only [my_set]`.

```lean
namespace BinaryFv.RiscV.MyDomain

@[grind =] theorem foo_after_bar : observe (bar s) = observe s := by …

/-- Close a MyDomain goal. -/
macro "my_domain" : tactic => `(tactic| grind)

end BinaryFv.RiscV.MyDomain
```

### Layout B — grind plus a named simp set

Lean forbids using an attribute in the file that declares it, so a named simp set needs two files.

- `MyDomainAttr.lean`: `register_simp_attr my_domain`
- `MyDomain.lean`: `@[my_domain, grind =] theorem …`, then the tactic macro.

The step-unfolding set of section 3 must use Layout B and omit `grind =`.

### Tactic macro shape

```lean
macro "my_domain" : tactic =>
  `(tactic| first
    | grind
    | (simp only [my_domain]; <closer matching the goal class>))
```

The fallback branch is not a concession. It makes migration safe, and how often it fires is the
measurement of how much `grind` actually covers — see section 9's audit check.

## 5. Rules of thumb

### Registration

- **Scope the attribute; do not use the global `@[simp]` set.** The step-unfolding facts in section 3
  are far too aggressive for the default simp set and will derail unrelated proofs. Always name the
  attribute.
- **Dual-register frame facts as `@[my_attr, grind =]`** so `simp only [my_attr]` users and `grind`
  users see one vocabulary.
- **A frame fact whose right-hand side is an `if` gets `@[grind =]` without `@[simp]`.** simp would
  rewrite goals into a branch; `grind` handles the branch natively.
- **Use `attribute [grind =]`, never a per-call `grind [lemma]` hint list.** Measured on one goal:
  110 ms via hint list, 4.2 ms via the attribute — 26×, and not index warm-up (verified on a
  single-declaration file).
- **A `grind_pattern` is needed when automatic inference leaves a variable undetermined** — not
  because a step can fail. The survey measured this directly: **0 of ~250 frame cells across ten
  areas are implication-shaped**, because every successor is named as a total function of its
  predecessor (`afterRegisterWrite state pc retired d v`) with the fallibility pushed into an
  existential over `retired`, which no observation reads. Automatic inference then determines every
  variable and fires unaided. Write a multi-pattern only for the minority where it does not — three
  such cells were found, e.g. `fallThroughMem`, where `{X with regs := …}.mem` reduces the insert
  away and leaves `rd`, `v` unknown; supplying the pattern turned a failing 25.5 ms `grind` into a
  7.58 ms success. Always verify the lemma fires; a registered lemma that never matches looks like
  coverage while providing none.
- **What cannot be a trigger term.** Both were hit during the survey:
  - **Anything containing `BitVec.ofNat`.** `grind` normalises `BitVec.ofNat 64 0x102f8` to
    `66296#64`, so the wrapper is gone from the E-graph and the pattern can never match. This fails
    **silently** — `ematch` ran 0.006 ms with all trigger terms sitting in the equivalence classes.
    Index by `BitVec 64` directly. This repository has 2,765 `BitVec.ofNat 64 0x` literals.
  - **A variable determined only through an `Eq`.** `grind_pattern thm => …, before.regs.get? x2 =
    some v, …` is rejected with *"invalid pattern, (non-forbidden) application expected"*. Restate
    the lemma in the frame shape `observer after = observer before` so no value variable needs
    determining.
- **Orientation matters.** `s.regs.get? R = (view s).f` lets `grind` chain (3.93 ms);
  `(view s).f = s.regs.get? R` does not (measured failure).
- **A frame lemma whose RHS is address arithmetic is inert on its own.** Three areas traced `grind`
  firing `afterRegisterWrite_pc` correctly, building the right equivalence class, then stalling
  because it cannot evaluate `Sail.BitVec.addInt 66444#64 4 = 66448#64`; adding `Sail.BitVec.addInt`
  as an unfold hint does not rescue it, and the same goal **passes** when the RHS is left unreduced.
  Every `*_pc` cell therefore needs a literal-normalisation companion. See section 2 — this makes
  generated address facts a precondition, not an optimisation.
- **`Std.ExtDHashMap.get?_insert` is already `@[grind =]` upstream.** Do not re-register it; Lean
  warns. All 645 in-repo citations of it are simp-list entries a frame lemma makes unnecessary.
- **`Agree` chaining needs one hint, not a reformulation.** Registering `Agree.trans` as
  `@[grind →]` chains four to ten `Agree`s automatically (0.062–5.0 s across three areas); bare
  `grind` fails, and unfolding `Agree` itself costs 0.90–1.31 s. Restating `Agree` as a
  `platformView` projection is **not** settled: it is measurably better for chaining (0.62 s bare
  `grind` on a 5-hop chain where the relation form fails) but does not help instantiation at a
  register, and its own frame lemmas are expensive (14.4 s failure, 3.27 s at `ematch := 40`,
  against `simp` at 0.25 s). Do not adopt it without a dedicated probe.
- **Put facts in a sub-namespace** so file-private lemmas in consumer files do not collide.
  Attributes and tactic macros are reachable without `open`.

### Don'ts

- **Do not register step-unfolding definitions for `grind`** (section 3). This is the survey's
  best-evidenced rule. Five areas measured the penalty at 18× to 126× (e.g. 665 ms against 7.6 ms
  for the equivalent `simp`), and one ran it as a controlled A/B on a single goal: with the four
  step-unfolding *definitions* as hints `grind` **fails**; with eleven pure **frame facts**
  registered `@[grind =]` and no unfolding, bare `grind` closes the same goal in 0.16 s.
- **Do not expect `grind` to close a deep chain.** With frame facts registered, register-survival
  chains close at 1–3 hops and fail at 4–5 with defaults; `(ematch := 20)` recovers 6–8; depth 10
  fails at `ematch := 20`, `40`, and `100`, and needs `(ematch := 40) (gen := 20)` — `gen` alone
  does not suffice. A tactic macro must therefore carry explicit budgets and a `simp` fallback.
  This does not block a per-`have` migration, since real proofs advance one hop per `have`, but it
  rules out collapsing a whole multi-instruction prefix into one `grind`.
- **Do not `grind` through `@[irreducible]` definitions.** `grind` respects irreducibility and cannot
  see through them; use `delta` first or a different mechanism.
- **Do not `grind` goals carrying many separation or footprint atoms.** Congruence reasoning degrades
  as the atom count grows. `Contracts/Footprint.lean` obligations are the likely case here.
- **Do not replace proofs that are already one line.** This is for collapsing repeated multi-line
  chains, not for making unrelated proofs look alike.
- **Do not use a grindset where a decision procedure already closes the goal.** The region-membership
  and instruction-word obligations behind the 129 `RegionPcs.iff_inRanges.mpr` and 112 repeated
  `native_decide` argument lists are not `grind` targets. They want a macro or a packaged lemma.

### Performance

- **Benchmark before bulk migration.** Run `lake build <module>` before and after. Reject the
  migration if it slows the module by more than 10%.
- **Cap a set at about 50 facts**; split by sub-domain beyond that. The frame-fact grid is roughly
  22 observations by 15 transformers, so it will need several sets split by transformer family.
- **Watch the global `@[grind =]` index.** Cheap facts are fine in bulk, but heavy or narrow rules
  slow every `grind` call in the repository. Prefer registering those in the named simp set only and
  reaching them with `grind [my_attr]`.

## 6. When to open a new set

A new set should:

- close a class of goals recurring in at least three unrelated files — otherwise an inline lemma is
  correct;
- hold at most 50 facts on first landing;
- ship with its tactic macro and one migrated file in the same change, as evidence it pays;
- come with a before-and-after `lake build` time for that file, recorded in the change description.

Extend an existing set instead when the new fact is the same class of goal.

## 7. Sets currently in the repository

There is still **no named simp set and no `register_simp_attr`** — deliberately. What exists is two
grind registrations, both narrow, both with negative controls in the same file.

| Registration | File | Closes | Controls |
|---|---|---|---|
| `attribute [grind →] Agree.trans` | `RiscV/Logic/RegisterAgree.lean` | agreement chains stated by endpoints | 3- and 5-link chains close; a **gapped** chain and a **reversed** chain both still fail |
| `grind_pattern WritesOnlyRegs.get => WritesOnlyRegs W s t, t.regs.get? r` | same | a register read through any chain of steps whose write sets are known, membership condition included | a register the chain **writes** must still fail; so must a bookkeeping register |

Nothing that unfolds a step definition is registered, and nothing should be — see section 5's
best-evidenced rule (18×–126×).

**Why no named simp set yet.** The frame-fact grid that would populate one is largely obviated: the
class lemmas discharge those obligations as `autoParam`s, and the write-set pattern handles reads.
A set should be opened only when section 6's bar is met by goals those two do *not* reach.

**Every registration must ship with a control that fails.** Both above do. Without the negative
cases, a rule that silently ignored its side condition would satisfy every positive test — and the
positive tests are the ones you are tempted to write.

**Grandfathering note.** An empty table does not mean no simp attributes exist. There are 35 uses of
the **global** `@[simp]` set, which section 5's first rule forbids for new work:
`MemoryRepresentation/EntryOffsets.lean` 9, `Entrypoints/ZesuDecodeRaw/Classify.lean` 7,
`Entrypoints/ZesuDecodeRaw/Accessors.lean` 7, `MemoryRepresentation/ChainOffsets.lean` 6,
`Entrypoints/ZesuDecodeRaw/DecodeGlue.lean` 3, `RiscV/Elfling/SentinelBridgeWitness.lean` 2,
`Entrypoints/ZesuDecodeRaw/Runner.lean` 1. They are narrow projections on decoder-local datatypes,
not step-unfolding facts, so they are left alone; do not add more.

## 8. Rollout

> **Status: phases 0–4 are done or superseded; the "pending" markers below are historical.** What
> actually landed, measured against branch base `8a85d1c`:
>
> | | |
> |---|---|
> | 12 big proof files | 21,384 → 17,019 lines = **−20.4%** |
> | best individual files | −28% to −31% |
> | library added (a one-time charge) | ~2,000 lines |
>
> **What the plan got wrong, kept because the error is instructive.** Phase 3 lists `Agree` chaining
> as a headline item on the strength of three areas measuring `@[grind →] Agree.trans` as sufficient.
> It *is* sufficient, and it is registered — but its reach is tiny. Of 98 `Agree.trans` uses, nearly
> all are single-link with a **constructed** second argument
> (`Agree.trans agree1 (afterRegisterWrite_agree (by simp [...]))`), which no chaining rule collapses.
> Perhaps 4–6 sites are genuine multi-link chains. The survey measured *whether the tactic works*
> without measuring *how many sites have the shape it works on*. That is rule 2 in section 0, and it
> is the most expensive recurring mistake in this project.
>
> Two mechanisms were also built and **reverted for having no consumer population**: a per-address
> instruction-fact table that duplicated `MachineRegions.words` (`bc83463`, reverted `6626781`), and
> the memory-side grind rule (`f78d965`, reverted `5dfbe96`). Both were correct and tested. Neither
> had anything to automate. **Count the sites before building the artifact.**
>
> Remaining opportunity, measured: 8,333 raw lines inside PR #60's files, split roughly evenly
> between never-migrated files (4,202, over half of it `MemcpyProof.lean`) and unexploited depth in
> partly-migrated files (4,131).

Ordered by measured lines removed per unit of risk, from the ten-area survey. Each phase is one
reviewable change following section 6. **Phases 0 and 1 are not sets** — they must land first,
because a set landed on top of the current duplication would preserve it.

**Status legend:** landed · in progress · pending.

### Phase 0 — pending — deletions and one-line reuse, no new automation

Six independent changes, each verifiable on its own:

| Item | Payoff | Evidence |
|---|---|---|
| `functionInstanceExecutionPcs_of_inRanges`, composing the two `.mpr`s that always co-occur | **110 sites** | typechecked during the survey; belongs in `RiscV/Elfling/ProgramGeometry.lean` |
| Delete `RawResultProof.lean:29-172` | 144 lines | duplicates all nine lemmas of `RegisterWriteStep.lean:18-228`, which is the later and more general copy; no import cycle blocks it |
| Collapse `RawErrorProof.lean:25-81` | 57 lines | verified by `rfl` that `rawErrorAfterAuipc state r = afterRegisterWrite state (BitVec.ofNat 64 0x13780) r x10 …` |
| Remove 61 byte-identical `have` blocks | ~120 lines | six are character-for-character identical inside one theorem body |
| Batch the per-byte `native_decide` obligations into per-function table proofs | **~40 s of build time** | cost is fixed per invocation (101 ms for 1 byte, 110 ms for 28), so 448 invocations become ~15 |
| Import `tryStepControlFlowAfterRetired_pc` where it already exists and is unused | 2 sites, plus precedent | `RiscV/Elfling/SentinelBridge.lean:67` |

**Do not** remove the 34 `have privilege` / `have mseccfg` bindings that a textual scan reports as
unreferenced. `decode_run` ends in `simp only […, *]` and consumes them from the local context by
type; removing them was tested and fails at `decode_run`.

### Phase 1 — pending — the parameterised instruction-step lemma

Largest single item in the survey and **not** a grindset. 24 theorems totalling 1,376 lines in
`DecodeInlineProof.lean` are the identical `decoderRegisterWriteStep` skeleton differing only in a
pc literal, four instruction bytes, a word literal, imm, rs, rd, and one source-read hypothesis; the
retry path is 58% a masked-equivalent re-derivation of the first path across 17 theorem pairs.
`decoderRegisterWriteStep` (`HasExactErePrefixProof.lean:257`) is already the generic step.

The apparent blocker dissolves: `rX_x<n>_run` / `wX_x<n>_run` are already macro-generated from a
table at `RegisterRuns.lean:54-71`, so a `regidx`-indexed version is mechanical.

**Estimate ~1,180 lines file-wide** — roughly four times any single grind proposal — with no new
automation surface and no new failure modes. Per-instruction arguments are exactly the
address-bearing facts `tools/generate_elfling_program.py` already emits, so call sites are a
generation candidate (section 2).

### Phase 1a — pending — probe the write-set frame before phase 2 picks a shape

Section 3a argues the write-set frame generalises where a frame grid does not. It is a design, not
a measurement. Probe it first, because the answer decides whether phase 2 builds ~300 grid cells or
~5 write-set lemmas plus a bridge:

1. Define `EqualOutside`, `EqualOutside.trans`, `agree_of_disjoint` in `RiscV/Logic/Framing.lean`.
2. Give `afterRegisterWrite` its write-set lemma (destination, `nextPC`, `PC`, `minstret`,
   `minstret_increment`).
3. Check that a `have` currently costing a six-name `simp` closes by membership `decide`.
4. Check `Agree platformPreserved` and `Agree decoderPreserved` both fall out of `agree_of_disjoint`
   without touching a consumer.
5. Measure elaboration against the current `simp` on the same goals.

If it holds, phase 2 becomes five write-set lemmas and the grid is unnecessary for register
observations. If it does not, phase 2 proceeds as written and this entry records why.

### Phase 2 — pending — one frame set, keyed to the shared transformers

**Scope discipline is the whole point of this phase.** Independent areas proposed sets keyed to
their own local composites (`wrapperAfter*`, `allocatorAfter*`, the jump composite,
`rawErrorAfter*`). Landing those as separate sets would institutionalise the duplication rather
than remove it: eleven successor-state definitions each carry a hand-rolled
`_agree`/`_mem`/`_pc`/`_retired_present` family (27, 11, 9, 3 theorems respectively), and every one
is a composition of the same four transformers in `Step/ControlFlow.lean`.

So: **collapse the ad-hoc composites into instances of `afterRegisterWrite` first, then build one
set keyed to the five shared transformers** in `Step/ControlFlow.lean` and `Step/Call.lean`.

Measured demand, recounted with an explicit predicate (Stage 0 below), not taken from the survey:

An **inline frame re-derivation** is a `simp`/`simpa`/`dsimp`/`rw` whose bracket cites
`Std.ExtDHashMap.get?_insert` (so it is reading a register) **and** at least one step-unfolding
definition (so the author unfolded rather than citing a frame lemma). By that predicate:

| Row | Inline re-derivations | Files |
|---|---|---|
| **All rows** | **528** | 24 |
| `coreControlFlowNextState ∘ tryStepControlFlowAfterIncrement` (the `executeState` row) | **465** | 24 |
| citing `afterRegisterWrite` | **192** | 15 |

The second row's lemma **already exists** — `afterRegisterWrite_register`, with **49 external call
sites, i.e. 20% adoption**. Two independent ergonomic causes were diagnosed: six positional
arguments plus five explicit disequalities make citing it longer than re-deriving it, and
`let`-bound successor states hide it. Both the write-set frame (section 3a) and a grindset address
the disequalities; only the write-set frame addresses the positional arguments.

The reproducible counting script is
`scratchpad/count_rederivations.py` — rerun it rather than quoting these numbers second-hand.

Layout B, `@[riscv_frame, grind =]` for `unchanged`/`derived` cells, `@[grind =]` alone for
conditional ones, plus the literal-normalisation companion from section 5. Macro carries
`(ematch := 40) (gen := 20)` and a `simp only [riscv_frame]` fallback.

Expect roughly 1,900–2,000 lines across the ten surveyed areas, but land it one file at a time with
the section 6 build-time measurement each time.

### Phase 3 — pending — `Agree` chaining

Register `Agree.trans` as `@[grind →]`. Three areas measured that alone as sufficient (0.062–5.0 s
for four to ten chained `Agree`s). The `platformView` projection restatement is **deferred pending
its own probe** — see section 5 for the conflicting measurements.

### Phase 4 — pending — generated fetch and region facts

Not a grindset; `grind` fails outright on both populations (1.33–1.41 ms, no progress). Emit
per-address `readFileByte?` / `fetchWord` identities and region-membership facts from
`tools/generate_elfling_program.py` alongside the image, as a named simp set with no `grind =`.
One area counted 68 such facts for its two files alone, which **exceeds the 50-fact cap**, so this
must be split one generated module per `functionInstance_*`. The in-repo precedent is `decode_run`
(`DecodeTactic.lean:21`), a macro used 246 times; the fetch side has no equivalent and should get
one. `SentinelAssembly.lean:608-712` is 105 lines producing six theorems for two functions with
identical bodies — generate them too.

### Baseline for the section 6 gate

Measured on this worktree, warm: `lake build BinaryFv` completes at 339 cached jobs.
Direct elaboration of the heaviest surveyed module, `Level2Epilogue.lean`, is **51.7 s** (an
independent survey measurement put it at 50.9 s), of which profiling attributes **16.55 s (33%) to
`simp` across 996 calls**. `Level2Tag0PostCopy.lean` is 10.6 s. Compare against these when landing
any phase.

The build also emits **24 `linter.unusedSimpArgs` warnings**, i.e. sites where the repeated
unfolding bundle carries lemmas that goal does not need — a mechanical, if small, confirmation that
the bundle is copied rather than composed.

## 8a. Writing a NEW machine proof — the shape to reach for

Everything above is about removing structure already written. This is how to not write it in the
first place. If you are proving that a compiled function does what its contract says, follow this.

**Do not hand-derive a single instruction.** Find the class lemma for its mnemonic in
`InstructionClassSteps.lean` and call it. You supply the state, the machine and agreement facts, the
program counter and the instruction fields; you supply *nothing else* — the fetch bytes, the base
encoding, the decode, the fit bound and the register disequalities are all `autoParam`s. If a
mnemonic has no class lemma, add one beside its siblings rather than inlining a proof; the family is
parameterised, so a new width or signedness is usually an instance rather than a new lemma.

**State each step's write set, once.** A step lemma should conclude
`WritesOnlyRegs W s t` — not a list of per-register preservation facts. `W` is
`RegSet.union stepBookkeeping (RegSet.only destination)` for a register write; keep the parametric
half (`only destination`) structurally separate from the closed half so `RegSet.Disjoint.union` can
split it. Never widen a parametric set into a closed over-approximation: that turns the disjointness
obligation into something false for `platformPreserved`.

**Then never carry a register by hand.** In the composition proof, write one
`have w := <transformer>_writes …` per step and let `grind` produce every register read through it.
Do not write the `have`-per-(register × step) ladder; that ladder is the single largest cost in this
proof tree and it is now unnecessary.

**Compose at a fixed write set, not by unioning.** Widen each step with `WritesOnlyRegs.mono` into
the write set of the whole function, then compose with `trans_same`. Composing with `trans` and
letting the set grow builds an `Or`-chain one disjunct per instruction, and at roughly eight steps
the `Decidable` instance for a membership goal exceeds `synthInstance.maxSize` and aborts before the
kernel sees it.

**Keep `Agree` derivation to the two-line chained form.** It cannot be automated (section 0, rule 3),
so do not fight it.

**State frame facts as `observer after = observer before`.** Both write-set relations are oriented
this way, which is why the bridge to `Agree` is a term with no `Eq.symm` in it. A frame lemma stated
the other way makes every downstream use carry a symmetry step, and — per section 5 — an orientation
that reads `(view s).f = s.regs.get? R` measurably fails to chain where the reverse succeeds.

**Prefer a predicate over a list for any register or address set.** `Register → Prop` lets a set hold
a *variable* element (a `destination` or a `linkReg`), destructures under `rintro (rfl | rfl)`, and
needs no coercion to meet `Agree`/`platformPreserved`/`decoderPreserved`, which are already that type.

**Two things worth doing before you write the proof at all.** Look up the instruction in
`build/machine-regions-lean/machine-regions.json`, which already carries every address's mnemonic,
operands and register read/write sets — do not re-derive from bytes. And check whether the fact you
are about to generate already exists under another name by grepping for its **validation theorem**
(`native_decide.*programImage`) rather than its name; a duplicate built under a different name is
invisible to a name search.

## 9. Maintenance

When a set lands, add its row to section 7 and its phase status to section 8. When a lesson
generalizes beyond one change, add it to section 5.

Audit each set when a third set is about to land, and every six months thereafter:

1. **Dead facts.** Remove a suspect lemma, rebuild dependent modules, see whether anything fails. If
   nothing does, delete it.
2. **Fallback rate.** Find where the macro's `first` block falls through to the simp branch. A
   recurring shape means either a missing `grind` hint or a permanent exception worth recording.
3. **Patterns that never fire.** For each `grind_pattern`, confirm at least one consumer goal
   instantiates it. This is the failure mode specific to our fallible-step statements.
4. **Build time.** Re-measure the representative module against the baseline recorded when the set
   landed. More than 10% slower with no offsetting reduction means shrink or retire.
5. **Consumer count.** Fewer than three consumer files means inline it and retire the set.

## 10. References

- `docs/agents/proof-pattern-survey.md` — the survey that populates sections 7 and 8.
- Lean `grind` reference: <https://lean-lang.org/doc/reference/latest/The--grind--tactic/>.
- `Init.Grind` in the Lean source for the `@[grind =]`, `@[grind →]`, `@[grind cases]` variants.
- `Veir/Rewriter/LinkedList/GetSet.lean` in github.com/opencompl/veir — 264 frame facts over 23
  observations and 11 transformers, proved by `grind`, with 101 explicit `grind_pattern`
  declarations for its fallible transformers. The closest published example of the grid in section 3.

## 11. CI gates — run BOTH, and run them per branch

`nix/proof.nix` enforces two independent layer rules. A review caught this stack failing the second
because only the first had been checked:

```bash
# 1. the RISC-V/Binary layers must not import the Zesu target
grep -rn '^import BinaryFv\.Zesu' BinaryFv/RiscV/ BinaryFv/Binary/

# 2. native_decide is not permitted in the generic RISC-V/Binary layers
grep -rn 'native_decide' BinaryFv/RiscV/ BinaryFv/Binary/

# 3. no standalone `sorry`
grep -Rnw --include='*.lean' -e '^[[:space:]]*sorry[[:space:]]*$' BinaryFv/
```

All three must be empty. Two things about gate 2 in particular:

- **It greps for the string, so a docstring trips it.** Prose explaining why a tactic uses
  `native_decide` fails the build just as surely as the tactic does. Reword the prose or move the
  whole thing.
- **The rule has a reason, and it constrains design.** The fixed-artifact exception covers closed
  facts about the pinned ELF; such facts are *target* facts by construction, so no generic module may
  state one. A tactic that decides its side conditions against the generated program tables therefore
  belongs in the Zesu layer, however generic its statement looks. `owned_pc` and
  `ConfinedPrefix.ownStep'` live in `Zesu/MachineExecution/OwnedPc.lean` for exactly this reason —
  `ownStep'` has to move with the tactic because its `autoParam` defaults must parse where it is
  declared. Everything genuinely generic (`reindex`, `trans'`, `consume`, `confined_steps`) stays put.

**Run these on every branch of a stack, not just the tip.** A gate is per-commit in CI, so a stack
whose tip passes can still have three red PRs beneath it.

## 12. Do not expand a combinator before it has a second consumer

`Seg` is the standing example, and the constraint is external review's, not ours: it has **one** real
consumer, exercising only its register-write and jump steps, and its store/memory interface is
untested. Keep it — it earns its place where it is used — but do not extend it until a second real
composition benefits.

This is the same failure this project already paid for four times (section 0, rule 2): a correct,
well-tested abstraction with no population. The tell is an interface with more cases than callers.

## 13. The heartbeat budget is the authoring-time guardrail

The expensive idiom here does not fail — it **succeeds, slowly**. That is why documentation alone
never stopped it, and why a CI gate is the wrong instrument: by the time CI rejects, the agent has
already paid to write the proof and must pay again to rewrite it. The feedback has to land inside the
edit loop.

`maxHeartbeats` does exactly that, and it is already in the language.

Measured on `Level2WrapperProof.lean`:

| ceiling | outcome |
|---|---|
| `5000000` (what the file set) | **succeeds in 364 s** |
| `400000` (the default) | **fails in 29 s**, errors pointing at the exact offending lines |

The slow proofs exist *because* the ceiling was raised. Raising it converts "this proof is the wrong
shape" into "this proof is merely slow", and slow proofs compile, get accepted, and merge. Every
expensive idiom found in this repository lives under a raised ceiling.

`MemcpyProof` is the proof that a low ceiling is achievable rather than aspirational: four
`maxHeartbeats 1000000` overrides removed, after which those theorems compiled at **50,000** — eight
times *under* the default. The overrides were masking duplication, not paying for hard proofs.

**Policy.** Do not raise `maxHeartbeats`. A proof that needs more is telling you its shape is wrong;
change the proof. If a raise is genuinely unavoidable, it needs a written reason naming what is
irreducibly expensive — and that reason is reviewable in a way "it was slow" is not.

**Sequencing matters.** Cap the ceiling only *after* the fast path exists and is reachable. Capping
first leaves an agent with a failing build and no route through, which is worse than the slow proof.
The order is: make the frame lemma reachable, register the grind pattern, sweep the sites, then set
the ceiling from measurement — per file, at what it actually needs once the sites are fixed.

**Why the ceiling beats a lint.** A lint enumerates known-bad patterns and misses the next one. The
budget is indifferent to *how* a proof got expensive: it catches the pattern nobody has thought of
yet, at the line, in seconds.

## 14. The frame-fact grid, and what filling a column is actually worth

Section 5 predicted this grid — roughly 22 observations by 15 transformers, of which about 30 cells
were named. Filling one column measured what an empty cell costs, and the answer was **not** what was
predicted.

**The column.** 25 `@[grind =] …_mem` equations, one per memory-preserving transformer, each `rfl`.
Before them `grind` could not close a memory transport at any real site: the sites go through project
wrapper definitions, and grind does not delta-unfold semireducible defs. The transports were
registered and inert.

**What it is worth, measured — and it is not speed.** The column was filled on the premise that
`simpa [<step definitions>] using h` dominated build time at 24-36 s a call. That premise came from
summing nested profiler times and was arithmetically impossible: a module elaborating in 364 s on one
core cannot contain 636 s of tactic work. Two clean A/Bs on a quiet machine, on 100%-converted files:

| file | `simpa` | `grind` |
|---|---|---|
| `ParserBlocks` (21 sites) | 10.37 s | 10.92 s |
| `BlobScheduleAndResultStores` (68 sites) | 39.3 s | 42.4 s |

**`grind` is 6-8% slower, and the line count is identical** (2151→2151, 4415→4415). A sweep of 167
sites was reverted on this evidence.

**So why keep the column?** Because its value is *availability*, not speed. With it, an agent writing
a new proof types `grind` — one word, no lemma name, no definition name — and therefore cannot type
`simpa [five state definitions]`, which is the idiom that actually costs 20-100x. Paying 6-8% to make
the cheap path the obvious one is a good trade. Rewriting proofs that are already one cheap line is
not; those are different questions and only the first has a yes.

**Not every cell exists, and inventing one would be unsound.** Six transformers genuinely write
memory; `mem = mem` is false for them. That they reject `rfl` was verified by probe, not inferred
from their names. A frame fact asserted for a transformer that lacks it is automation that lies.

**Three of the 37 candidates were not transformers at all** — `SailM` actions writing CSRs, with no
`.mem` projection. Check the type before writing the lemma.

### The obligation

A new `State → State` definition is **unfinished** until its frame facts exist: `_mem` if it preserves
memory, `_pc`, `_retired`, and a `_writes` register write set. Each is one line and usually `rfl`.
Skipping them does not fail anything — it removes the one-word path for every future call site, which
is how the expensive idiom spreads.

Search pattern note: `def .*After[A-Za-z]+` misses transformers whose name *ends* in `After`. There
are 14 such, and grepping only the first form is why they were initially missed.
