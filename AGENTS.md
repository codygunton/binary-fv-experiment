# Repository instructions

These instructions apply repository-wide.

## Objective

- The final goal is to prove that the shipped Zesu `zesu_decode_raw` implementation conforms to the
  pinned Ethereum SSZ specification. State how local proof or tooling work advances that goal.
- Preserve useful earlier work, but do not retain a theorem, contract, or abstraction merely because
  it already exists. Reject or replace statements whose machine assumptions are false.

## Proof navigation

- `root_compliance` is the single public entry theorem for the compliance proof. Reserve the `root_`
  prefix for it: no theorem or definition in its transitive dependency tree may begin with `root_`.
  A reader searching for `root_compliance` must immediately find the unique top of the proof tree.
- Every conditional refinement level must expose a named edge that converts that level's assumptions
  into its parent's assumptions. The parent theorem must call that edge explicitly; do not leave the
  composition implicit in a bundle of hypotheses.
- Name refinement edges for the direction they establish, such as `exportedContracts_of_level1`.
  Keep logical premises distinct from bytecode-coverage obligations retained for later runtime proofs.

## Refinement strategy

- Work top-down from the exported program: state a conditional theorem over its immediate machine
  regions, prove the small regions, and further resolve only the large regions.
- At every level, select exactly the immediate calls in the reviewed call flamegraph for the function
  being resolved. Restate that function's contract in terms of contracts for those selected calls; do
  not substitute deeper descendants because their statements happen to be available. If the UI's
  hierarchy disagrees with the reviewed call relation, record and correct that discrepancy instead of
  silently changing the theorem's function set.
- Prove every selected function that calls no other selected function. Also prove the machine
  instructions owned by the parent but not owned by any selected child. A selected function that is
  too large to prove becomes the parent resolved at the next level.
- The theorem for each level must visibly consume every selected contract and derive the same
  meaningful parent contract. Keep that conditional parent result valid while deeper functions remain
  unproved; a list of unused contracts is not a refinement.
- Treat each resolution depth as a reviewable stacked change. Do not introduce a flat catalog of all
  discovered functions as though it were the proof architecture.
- Contracts describe actual optimized machine-code boundaries. Inlined source functions do not obey
  a source-level RISC-V function ABI; apply ABI assumptions only at genuine calls.
- Bind every semantic or ghost value used by a contract to registers or memory at that boundary.

## Contract admission

- Before investing in a proof, require three checks: structural correspondence to the production ELF,
  semantic review against source/specification, and empirical tests for every measurable clause.
- Use the production ELF for machine observations and an independently built source probe as an
  oracle. Add focused negative or mutation tests showing that each checker rejects relevant faults.
- Evidence guides admission but is not a proof. Record unmeasured clauses and failures explicitly.
- Use generated, source-derived Lean identifiers for function instances. Do not select proof objects
  through numeric catalog positions or string names.

## Compiler evidence

- Prefer LLVM outputs as the common source for symbols, call structure, inlining, and interfaces.
  Use disassembly and generated control-flow regions to check the final machine code.
- DWARF augments LLVM evidence with source identity and locations; it does not override instructions in
  the shipped binary.

## Documentation language

- Comments, docstrings, READMEs, plans, and status notes must use concrete project terms. Do not use
  generic jargon when the specific declaration, artifact, proof relationship, or machine-code region
  can be named.
- Introduce specialized terms with enough local context to identify what they mean here. For example,
  say “the theorem converting `Level1ContractAssumptions` into `ExportedContractAssumptions`” before
  calling it a “refinement edge,” and name the exact theorem meant by “root” or “parent.”
- Avoid context-free labels such as “foundation,” “admission,” “spine,” “layer,” “closure,” or
  “machinery.” If one is useful, accompany it with the concrete files, declarations, checks, or
  dependency relation it summarizes.
- Documentation should let a reader follow the proof and build artifacts without first learning an
  agent's private vocabulary.

## Loops

- Prove loops with an invariant or recursive theorem plus a decreasing measure or justified bound.
  Do not unroll a loop merely because observed test inputs make it short; runtime-dependent lengths are
  compatible with an inductive proof.

## Proof automation

- [`GRIND.md`](GRIND.md) is the single source of truth for named `simp` and `grind` sets: which facts
  belong in which kind of set, the attribute variants, the two-file constraint on named simp
  attributes, the entry criteria for a new set, and the registry of sets that exist. Read it before
  adding a shared `@[simp]` or `@[grind =]` attribute or writing a closing tactic more than one proof
  will call. Do not duplicate its content here.
### The budget is the guardrail — do not raise it

**`maxHeartbeats` is capped at the ambient value. Raising it is forbidden without a written reason.**

This is the single most important rule here, and it is a *time* rule, not a style rule. The expensive
idiom in this repository does not fail — it succeeds, slowly. `simp [<step definitions>]` is a
universal solvent: it eventually closes almost any goal by unfolding the machine state, at 24-36
seconds a call. An agent writing one gets a green tick and moves on, and the cost lands on everyone
later. Measured: 279 such sites, and one file where twenty of them account for essentially the whole
364-second build.

Those sites exist because the ceiling was raised to let them through. At the *default* ceiling that
same file fails in **29 seconds**, pointing at the exact offending lines. That is the feedback you
want — in your own edit loop, in seconds, at the line — not from CI after the proof is written.

So: if a proof needs more heartbeats, **the proof is the wrong shape**. Stop and change the proof.
`MemcpyProof` carried four `maxHeartbeats 1000000` overrides; once its duplication was removed the
same theorems compiled at **50,000**, eight times *under* the default. The overrides were never
load-bearing.

### Before writing a proof, find your goal in this table

Do not search for a tactic. Look the goal up. Every row is measured.

The right-hand column is what costs 20x-100x, not 6%. `grind` itself is marginally *slower* than a
terse hand-written `simpa` — about 6-8% — and saves no lines. Its value is that it needs **no names**,
so reaching for it is what stops you writing the multi-definition unfolding in the third column. Use
it for new proofs; do not rewrite existing one-line proofs to use it.

| your goal | write this | never write |
|---|---|---|
| one machine instruction executes | the class lemma for its mnemonic (`InstructionClassSteps.lean`) — one call, obligations are `autoParam`s | a hand-derived fetch/decode/execute/retire chain |
| a register's value survives a step | `have w : WritesOnlyRegs _ s t := <shape>_writes _ _ _ _ _` then `grind` | `simp [<step defs>, Std.ExtDHashMap.get?_insert]` |
| several registers across several steps | the same **one** `have` per step, then `grind` for all of them | one `have` per (register × step) |
| a memory-shaped fact survives a step | `grind` — no lemma or definition name needed | `simpa [<state defs>, <wrapper>, afterRegisterWrite_mem] using h` |
| agreement across a step | `(…_writes …).agree …`, or the chained two-line form | a `cases register <;> simp_all` over every register |
| a pc/exit membership for a literal address | `owned_pc`, or the `regionPc`/`notExitPc` autoParams | a hand-written `native_decide` block |
| an instruction's bytes or operands | look it up in `build/machine-regions-lean/machine-regions.json` | decode it from byte literals by hand |

If your goal is not in the table and you are about to reach for `simp [<a state definition>]`: that is
the anti-pattern this table exists to prevent. Ask for a frame lemma instead — the answer is almost
always that one exists, or should, and is three lines.

### Elaboration cost: find it by bisect, and suspect defeq before tactics

Build time here is dominated by a handful of pathological *declarations*, not by proof volume. The
spread across modules is 250x per line. Three rules, each bought with a measurement:

**1. Profile with `-Dtrace.profiler=true`, reading `Elab.definition.value` and per-tactic
durations.** That attributes cost to a single tactic, which is what you need.

Two traps, both of which cost real time here:

- **Do not sum the plain profiler's tactic times.** They are reported *inclusively*, so nested entries
  double-count and can total more than the file's own wall-clock. Summing them produced three separate
  wrong conclusions in one session, including a 167-site rewrite reverted for measuring slower.
- **Do not trust `head -n` wall-clock bisection either.** Lean elaborates declarations in parallel, so
  truncating the file misattributes cost to neighbours. A "160 s region" identified this way turned
  out to be one theorem at 153 s, with the two neighbours it implicated costing 3.5 s and 4.6 s. It is
  useful as a first cut to find the *file region*, but never as the attribution you act on. (And if you
  do use it: `head -n <line-of-X>` truncates *before* X, so a delta belongs to the **previous**
  declaration.)

**2. Suspect definitional equality before you suspect tactics.** The most expensive single thing in
this repository was `canonicalContractParams.env.image` versus `Artifacts.programImage` — definitionally
equal, but deciding it re-parses the entire pinned ELF, about 29 s. The give-away: the site looked like
an expensive `simpa [bigConfig, bigEnv] using code`, and replacing it with a bare `exact code` cost
**exactly the same**. If stripping a simp set changes nothing, the tactic was never the cost.

Two fixes, in order of preference:

- **Make the huge definition `@[irreducible]`.** `Artifacts.programImage` is a `match` on a parsed ELF;
  marking it irreducible stopped every defeq from re-parsing it and took `Level2Capstone` 86 s to 2 s,
  `Level2WrapperProof` 235 s to 140 s, with `native_decide` unaffected because compilation ignores
  reducibility.
- **Write the transport in term mode, not through `simp`.** The worst single tactic found in this
  repository was `simpa [<let-alias>, afterRegisterWrite_mem] using <previous>` at **187 s**: `simp`
  zeta-expands the whole `let`-chain, then `isDefEq` re-unifies two nine-deep state records. The term
  form `codeIntact_of_mem_eq (afterRegisterWrite_mem s pc r d v) prev` never builds that term, because
  the frame equation is `rfl` by construction. Two modules went 428 s to 89 s on this alone.
- **Pay the defeq once in a transport lemma** and route call sites through it. Note the statement
  matters: through `CodeIntact` it exhausts the recursion depth, and even the projection equation fails
  at `rfl` because `rfl` unfolds both sides. `by simp only [theEnvDef]` reduces the projection
  syntactically and closes in seconds.

**3. Watch for superlinear scopes.** A `structure` whose fields mix representation levels — bitvector
equalities beside `.toNat` equalities about the same values — costs far more than its parts: 4 of one
kind cost 3.6 s, 2 of the other 1.1 s, all six together **62 s**. The cost is `mk.injEq` generation
over the telescope (`set_option genInjectivity false` takes the same structure 179 s to 1.1 s).
Splitting the structure along the representation boundary, composed back with `extends`, measured
178 s to 3.7 s and keeps every consumer's statement byte-identical. The same facts as *loose theorem
binders* cost nothing, so this is `structure` elaboration specifically.

**Try the change rather than modelling it.** Every isolated micro-benchmark in this project either
misled or cost more than just applying the edit and timing the module. Apply, measure the module,
revert if flat — reverting is cheap and a flat result is information.

### Module scope: keep the dependency graph flat and wide

Lean elaborates a module on one core; Lake parallelizes across modules only. A module's elaboration
time is therefore a serial segment of the build, and a chain of modules is a critical path that no
number of cores can shorten. This build was **996 s of critical path out of 1009 s** — nine modules in
a queue, one core busy, sixty-three idle.

**Target: no module over ~60 s.** Check with `lake build <module>`, which prints the time.

**Measure time, never line count.** Line count is a useless proxy here — the spread is 250x:

| module | | ms/line |
|---|---|---|
| `Level2OutcomeEpilogue` | 131 lines / 169 s | **1290** |
| `Level2Capstone` | 276 lines / 86 s | 312 |
| `Level2WrapperProof` | 1900 lines / 353 s | 186 |
| `BlobScheduleAndResultStores` | **4416 lines** / 40 s | 9 |
| `MemcpyProof` | 1791 lines / 7 s | 4 |

The largest file in the repository builds in 40 s and needs no attention; a 131-line file with seven
declarations takes 169 s. Splitting by size sends you after the wrong files.

**Two different problems, two different fixes.**

*Accidental chaining.* Modules that do not use each other's proofs still queue behind one another,
because a later one needs a single small thing from an earlier one — a structure, one lemma. Measured
here: `Level2Capstone` waited 192 s on `Level2OutcomeDispatch` for `WrapperTerminalRouteFrame`, a
**structure definition**. Move the small thing into its own module that both import, and the two
expensive modules elaborate concurrently. Two such moves cut this build 1234→1009 s, measured cold at
both ends, changing no proof.

*A genuinely expensive module.* Split it along a **dependency layer** — the declarations that
reference nothing else in the file can become their own module and elaborate in parallel. Never split
down the middle of a chain of dependent declarations; that just makes two serial modules out of one.
`Level2WrapperProof` split this way: 57 declarations out, 38 s off the path.

**When you add a module, check what it will wait for**, not just what it needs. `import` is a
scheduling decision as much as a namespace one.

### One function instance is at least two modules: steps, then composition

Lean elaborates a file **serially** — measured at 135% CPU across 34 threads, i.e. one core. Lake
parallelizes across *modules* only. So a module's elaboration time is a serial segment of the build,
and a chain of big modules is a critical path no number of cores can shorten.

Measured on this repository: the critical path is ~1245 s of a ~1050 s wall-clock build, with 1076 s
of it in five proof modules that import one another in a line. **86% of the total work is on the
critical path**, on a 64-core machine. Adding cores does nothing; splitting a module into a *chain*
does nothing either. Only widening the graph helps.

The proofs are shaped to allow that, if you write them that way. `Level2WrapperProof` has 97
declarations of which **47 depend on nothing else in the file** — the single-instruction step lemmas
— narrowing to a spine of compositions 11 deep. The steps can all elaborate in parallel; only the
spine is inherently serial.

**So: put the step lemmas for a function instance in their own module, and the compositions that
consume them in another.** `<Instance>Steps.lean` then `<Instance>Proof.lean`. Step lemmas do not
reference each other, so several instances' step modules build simultaneously; the composition
modules chain, and are much smaller.

**Target: no module over ~60 s.** Not a style preference — a module over that is a serial segment
everyone waits on, and with 141 function instances still to prove the convention chosen now is
multiplied by 141. If a module exceeds it, split it along a dependency layer (declarations that
reference nothing else in the file), never down the middle of the spine.

Check yours before adding it: `lake build <module>` prints the elaboration time.

### Contract-statement modules must not import proof modules

The single largest build win in this project came from moving **two declarations**, and this is the
rule that would have prevented the problem.

Lean elaborates a module on one core, so a module's time is a serial segment of the build. If a
contract-statement module imports a proof module, every module downstream of that contract is
sequenced *after* the proof — however unrelated they are. Here `Level2Contracts.lean` (239 lines) had
picked up one proof import for **one identifier**, and that put a 361 s module behind a 275 s one.
Moving the bridging declarations into their own modules cut the whole build by **18.2%** — measured,
cold full builds at both ends: **1234 s → 1009 s** — changing no proof.

So: a module that *states* contracts imports only what the statements need. When a statement genuinely
needs a fact from a proof, put the bridging declaration in its own module and let the consumers that
already depend on the proof import that. Its cost is then paid only by things that were paying it
anyway.

Watch for the second-order case: after breaking one such edge, a consumer that had been resolving a
name *transitively* through the contract module suddenly needs a direct import, which restores the
dependency on a shorter path. Re-check the closure after every fix.

### Answer dependency questions from the import graph, not from a build

Every question in this area — what waits on what, which import costs what, whether an edge is real —
is answerable from the import graph in **under a second**. Builds here cost minutes. Probe first,
build last.

The graph is not just fast, it is *accurate*. A critical-path model built from the import graph plus
per-module elaboration times predicted 1245 s → 1004 s for a change that measured **1234 s → 1009 s**
— under 1% error at both ends. Trust it for deciding what to do; measure only to confirm the result
you are going to write down.

The technique that found both choke points: **delete an import from the small file at the top of the
dependency and read which errors appear.** Four probes at about a second each, on a 239-line file
whose dependents are enormous, located what no amount of building the 361 s module would have shown.
Probe the cheap file at the top, not the expensive one at the bottom.

**Do not conclude an import is dead from a name scan.** "Imports X but references none of X's
declaration names" produced a confident false positive worth an apparent 621 s; the module genuinely
needed a name the scan had missed. Confirm by deleting the import and compiling — that is the only
check that cannot lie to you.

### If you define a new state transformer, you owe it a frame equation

This is what keeps the automation from silently decaying, and it is cheap.

Every `def` producing a `State` from a `State` needs, beside it:

```lean
@[grind =] theorem <name>_mem (…explicit args…) : (<name> …).mem = state.mem := rfl
```

Without it `grind` cannot see through your definition — it does not delta-unfold semireducible defs,
deliberately — so every downstream memory-transport proof silently falls back to the 25-37 second
`simpa`. That is exactly how 279 such sites accumulated: the wrapper definitions were added without
their frame equations, and each call site then paid for it.

**If your transformer writes memory, do NOT write that equation.** `mem = mem` is false for it and
`rfl` will not close it. Six transformers here are in that class; they have no `_mem` lemma on
purpose. State what it writes instead, in the shape of `storeRetirement_mem_writes`.

The same applies to any other observation your transformer preserves — `_pc`, `_retired`, and the
register write set (`_writes`). A transformer landing without its frame facts is unfinished work, not
a small omission: it is the difference between a downstream proof being one word and being forty
lines.

### Non-negotiables

- **Never change a theorem statement.** Only proof bodies. This is what makes the work splittable by
  technique, lets a reviewer trust a diff, and keeps mutation testing meaningful. A reduction that
  genuinely needs a statement change lands as its own labelled commit.
- **Never unfold a step definition inside `simp`/`grind`.** Measured at 18x-126x, five times
  independently. `GRIND.md` section 3.
- **`lake build <module>` before checking any consumer of a module you edited.** `lake env lean`
  resolves imports from the prebuilt `.olean`, so the check otherwise measures the old code.
- **A deleted theorem still compiles.** Before any merge or refactor that removes something, diff the
  declaration-name sets. `GRIND.md` section 0, rule 5.
- **Run all three CI gates locally** (`GRIND.md` section 11) — including that `native_decide` is
  forbidden in `BinaryFv/RiscV/` and `BinaryFv/Binary/`, docstrings included.

Full reasoning, measurements and the four mechanisms that were built and reverted: `GRIND.md`
section 0.

## Verification

- Use focused Lean targets and evidence tests while iterating. Run the full `lake build` at coherent
  checkpoints, before committing proof changes, and before claiming a completed chunk.
- Regenerate compiler-derived artifacts from the current branch. Shared worktree build artifacts may
  accelerate compilation, but stale generated inputs or `.olean` files are not evidence.
- Keep the generated flamegraph proof status current. Selected but unproved functions are red,
  selected functions under active proof are yellow, proved functions are green, and unselected
  functions are blue.

## Pull request descriptions

- Name every theorem or other statement proved by the PR and state what each proof establishes.
- Name every theorem, contract, assumption, or proof obligation weakened by the PR and describe the
  weakening precisely. This includes adding assumptions, narrowing inputs, weakening conclusions,
  replacing a proof with an axiom or placeholder, and reducing machine-code or specification coverage.
- If the PR proves no new statements or weakens none, say so explicitly. Do not make reviewers infer
  either fact from the diff.
