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

Do not search for a tactic. Look the goal up. Every row is measured, and the wrong choice is 20x-100x
slower rather than wrong.

| your goal | write this | never write |
|---|---|---|
| one machine instruction executes | the class lemma for its mnemonic (`InstructionClassSteps.lean`) — one call, obligations are `autoParam`s | a hand-derived fetch/decode/execute/retire chain |
| a register's value survives a step | `have w : WritesOnlyRegs _ s t := <shape>_writes _ _ _ _ _` then `grind` | `simp [<step defs>, Std.ExtDHashMap.get?_insert]` |
| several registers across several steps | the same **one** `have` per step, then `grind` for all of them | one `have` per (register × step) |
| a memory-shaped fact survives a step | `grind` (the transports and `_mem` frame equations are registered) | `simpa [<state defs>, <wrapper>, afterRegisterWrite_mem] using h` |
| agreement across a step | `(…_writes …).agree …`, or the chained two-line form | a `cases register <;> simp_all` over every register |
| a pc/exit membership for a literal address | `owned_pc`, or the `regionPc`/`notExitPc` autoParams | a hand-written `native_decide` block |
| an instruction's bytes or operands | look it up in `build/machine-regions-lean/machine-regions.json` | decode it from byte literals by hand |

If your goal is not in the table and you are about to reach for `simp [<a state definition>]`: that is
the anti-pattern this table exists to prevent. Ask for a frame lemma instead — the answer is almost
always that one exists, or should, and is three lines.

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
