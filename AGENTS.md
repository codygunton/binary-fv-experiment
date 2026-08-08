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
- The sole conditional argument of `root_compliance` is the proof-progress gauge. Name it `hLevelN`,
  where Level N is the deepest reviewed UI depth whose function contracts have not all been
  discharged. Each stacked refinement PR replaces `hLevelN` with `hLevel(N+1)`; do not retain both.
  After the final level is discharged, `root_compliance` has no proof argument.
- The type of `hLevelN` must contain only outstanding contracts for function instances selected at
  UI Level N. Make this syntactically visible in a named `LevelNContractAssumptions` definition or
  structure. It must not contain a deeper descendant's contract, a parent-route theorem, a semantic
  oracle premise, an instruction-coverage fact, or an ad hoc machine-state hypothesis.
- Expose a named theorem converting `LevelNContractAssumptions` into the preceding level's
  assumptions, and make `root_compliance` call the chain explicitly. Prove parent-owned instructions,
  route coverage, and already-closed leaf contracts inside that conversion. If any such fact remains
  an assumption, Level N is not complete and the root parameter must remain `hLevel(N-1)`.

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
- A level assumption may omit a selected leaf only when a named unconditional theorem discharges that
  leaf in the level conversion. Construct a visible selected-contract bundle there—for example,
  filling proved allocator and `memcpy` fields while taking only the unresolved inlined-`decode`
  contract from `hLevel2`—so readers can still audit every immediate UI child.
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

### Reuse the concrete proof APIs before restating their mechanism

- For a computed `Option.map` or `Except.toOption.map` whose scrutinee is pinned artifact data, use
  `BinaryFv.Option.getD_map_of_eq_some`, `BinaryFv.Option.getD_map_eq_true_of_eq_some`,
  `BinaryFv.Except.getD_map_toOption_of_eq_ok`, or
  `BinaryFv.Except.getD_map_toOption_eq_true_of_eq_ok` from `BinaryFv/Option.lean`. Keep the mapped
  body named and pass it explicitly; do not unfold the pinned dispatch at each consumer.
- A representation `.rebase` theorem and `MemoryBytes.rebase` must state
  `ByteWindowRelocation before after source destination width` explicitly. Use
  `ByteWindowRelocation.atOffset` for a sub-window. Keep `statelessInputHeapRegion` as the public
  nested-union contract; use `mem_statelessInputHeapRegion` with a member of
  `statelessInputHeapRegions` only to supply membership evidence inside a proof.
- Generated Sail register-run proofs remain in leaf-local modules. Use only an already consumed
  concrete `rX_bits_run_xN` or `wX_bits_run_xN` wrapper; add a generated wrapper only for a real
  consumer. For a shared Machine-mode data address, use the access- and width-indexed
  `get_transformed_data_addr_machine_data_run` from `Instruction/Execute/DataAddress.lean`, while
  retaining its load/store compatibility wrappers at existing callers. `RetirementContext` remains
  the counter-premise definition used by `StepCounters`.
- `DataMMIOAddressExcluded` must not get a global `Decidable` instance and concrete Zesu proofs must
  not native-evaluate it. Prove concrete ranges through CanonicalEntry's
  `dataMMIOAddressExcluded_of_layout` (or its load/store compatibility wrappers), then pass that
  proof to the MMIO run theorem. Use `DataPmaAccess` for shared PMA facts.
- Use `GeneratedWordStep.generatedRegisterWriteStep` only when the site has
  `fileBytesLoadedFaithfully`, `readFileByte?`, and `DecoderMachinePre`; for example,
  `decodeInline_first_result_pointer_step` supplies explicit `.ITYPE` decode and
  `execute_ITYPE_run` premises. Do not force this interface onto a `matchesMemory`/`readByte?`
  proof: `BlobScheduleAndResultStores` has that different evidence shape, and no valid bridge has
  been established.
- Before composing local successor states, search for the existing owned route. For the tag-three
  dispatch this is `wrapper_dispatch_tag3_owned_terminal_route` in
  `Level2OutcomeDispatch.lean`, backed by `Seg`; projecting its route is preferable to rebuilding
  five `let`-bound post-states. Introduce `Seg` only after profiling identifies a successor-state
  composition as the cost.

### Build shape: what parallelising can and cannot buy

Measured on this project, and each number changed a decision:

- **The whole build is 125s wall / 800s user = ~7 of 64 cores.** It is chain-bound, not CPU-bound.
- **One module runs on ~1.25 cores.** Lean elaborates a module essentially serially; Lake
  parallelises only *across* modules. So a wide module is a serial segment of the build however
  independent its contents are.
- **The critical path is ~123s of the 125s**, and there are *four near-equal chains*. Fixing the
  single biggest module bought **3s**, because the second chain was only 3s shorter. Before
  optimising anything, compute what the path becomes *after* the fix -- "it is the biggest module"
  is not a reason.

**Splitting modules was tried project-wide and reverted. Do not reach for it.** Splitting the four
biggest modules by dependency layer -- 118 machine-named files -- bought **12.5s** (110s vs 122.7s)
and cost 121 files, 23 declarations that silently lost `private`, and **63s more CPU** than it saved
in wall. The names carried no meaning (`DecodeInlineProof/L2_8.lean`), the parent module became an
empty shim, and files were grouped by dependency depth rather than topic. See `128fe43`.

Two things make it unattractive even where it works:

- **It only applies to flat piles.** `BlobScheduleAndResultStores` (128 declarations, nearly all
  independent) split cleanly, 41s to 28s. `DecodeInlineProof`, `Level2Epilogue` and
  `Level2OutcomeDispatch` have **zero contiguous cut points** -- step one feeds step two feeds the
  composition. And where the cost sits in a *single* declaration, no partition subdivides it: one
  theorem in `Level2Epilogue` was 27s on its own.
- **`private` is module-scoped.** Moving a declaration away from its dependents forces you to make it
  public. That is an API change made by a refactoring script, not by a person.

If you still need it, cut only at points no later declaration crosses, and enumerate `private
theorem` and `set_option ... in` when you do -- missing three `private`s cut a real dependency, and
`set_option ... in` modifies the *next* declaration, so orphaning it leaves a dangling `in`.

**The alternative that actually paid: make the expensive declaration cheap.** Same module,
`Level2Epilogue`, **47s to 12s in one file** with no new modules -- see the agreement-frame rule
below and the duplicate-block rule above it.

**You cannot delete an unused import.** Lean imports are transitive re-exports, so `B` importing `A`
without using any of `A`'s declarations is *not* dead: consumers of `B` may be relying on `B` to
re-export `A`. A 62-edge rewrite justified by "B never names anything from A" broke four modules in
unrelated parts of the tree and was reverted wholesale. The condition to check is over `B`'s whole
dependent cone, not over `B`.

**Not all of the build is the theorem.** `root_compliance` needs 153 modules and builds in 83s; the
full library is 241 modules and 126s. Generated-artifact validation is real kernel-checked evidence
but nothing in the conformance argument depends on it, which is why it lives in the separate
`BinaryFv.Evidence` target. Check whether the work you are optimising is on the path to the theorem
at all.

### Elaboration cost: find it by bisect, and suspect defeq before tactics

Build time here is dominated by a handful of pathological *declarations*, not by proof volume. The
spread across modules is 250x per line. Three rules, each bought with a measurement:

**1. Profile with the profiler. Always `-Dtrace.profiler=true`, never `-Dprofiler=true`.**

```bash
lake env lean --tstack=65536 -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 <File>.lean
```

This is the *only* instrument here that names the declaration it is timing. It prints a nested tree:

```
[Elab.async] [313.34] Lean.addDecl
  [Kernel] [313.34] typechecking declarations [Validation.witnessValid_some]   <-- the answer
```

Read all three layers before concluding — they mean different things and the fix differs:
`Elab.definition.value` / `Elab.step` is **elaboration** (tactics, defeq, unification), `Kernel` is
**final typechecking of the proof term** (Lean already accepted it; the kernel is re-checking it).
Note the top offender may sit under a bare `Lean.addDecl` async block with NO
`Elab.definition.value` above it — a pure kernel cost has no tactic to blame, so a search restricted
to `Elab.definition.value` silently misses exactly the worst cases.

**`-Dprofiler=true` emits `type checking took 313s` with no declaration name and no source
position.** It cannot attribute anything. Reaching for it costs an hour and produces confident wrong
answers: it drove three rounds of invalid elimination here (see trap 3) before `trace.profiler`
named the culprit in one run. If you find yourself inferring which declaration is slow, stop — you
are using the wrong flag.

**Read the per-tactic tree, not just the per-declaration total.** This is what finally located the
11.4s `stackAgree`, after two wrong guesses at the same theorem: lower the threshold and the tree
nests tactic steps under the declaration, so the offending `have` is named directly.

```bash
lake env lean --tstack=65536 -Dtrace.profiler=true -Dtrace.profiler.threshold=400 <File>.lean
```

**For a shareable profile, `-Dtrace.profiler.output=<file>.json` writes Firefox Profiler format**,
loadable at profiler.firefox.com. In the UI use the **inverted call stack** to rank by *self* time.
Two cautions: the file has no declaration-level frames -- its frames are trace classes (`Kernel`,
`Elab.step: …simpAll`) -- and its sample weights come from the trace tree, not from sampling, so they
carry the same inclusive-overlap problem as the text output. Proportions are informative; absolute
per-declaration numbers are not there to be read off.

Three traps, all of which cost real time here:

- **Do not sum the plain profiler's tactic times.** They are reported *inclusively*, so nested entries
  double-count and can total more than the file's own wall-clock. Summing them produced three separate
  wrong conclusions in one session, including a 167-site rewrite reverted for measuring slower.
- **Do not trust `head -n` wall-clock bisection either.** Lean elaborates declarations in parallel, so
  truncating the file misattributes cost to neighbours. A "160 s region" identified this way turned
  out to be one theorem at 153 s, with the two neighbours it implicated costing 3.5 s and 4.6 s. It is
  useful as a first cut to find the *file region*, but never as the attribution you act on. (And if you
  do use it: `head -n <line-of-X>` truncates *before* X, so a delta belongs to the **previous**
  declaration.)
- **Never attribute by elimination — `sorry` one declaration, keep the rest.** Two ways this lies.
  If the cost is *shared* (a forced value, a kernel cache), removing one payer just hands the bill to
  the next, and every variant looks guilty. And it only tests what you actually varied: three rounds
  of sorrying the three `native_decide`s here all reported ~293 s, "proving" each in turn, when the
  real cost was an ordinary transport lemma that no variant ever touched. Elimination is only valid
  when you have *positively* measured each candidate alone.

**1b. Kernel cost is a separate disease from elaboration cost, and the fix is different.** When
`[Kernel]` dominates, the tactics are *already done* — Lean accepted the proof and the kernel is
re-checking the term it produced. Rewriting tactics will not help; the term itself is wrong-shaped.

The single worst declaration in this repository was of this kind: `witnessValid_some`, a four-line
transport lemma, cost **313 s of kernel time in a 321 s module** -- 91% of the entire project build,
in a file whose elaboration totalled 23 ms. It read

```lean
have h := witnessValidC_true
unfold witnessValidC at h      -- puts the concrete `controlFlow?` into the rewrite motive
rw [hn] at h
simpa only [...] using h
```

`unfold`+`rw` specialises a general fact *at the use site*, so the motive the kernel must check
mentions `controlFlow?` and the generated 3369-element arrays -- and checking it re-runs the Sail
decoder inside the kernel. Swapping `simpa` for `simp only`+`exact` changed nothing (308 s): the
tactic was never the cost.

**The fix is to move the transport into a lemma that is generic in the data**, so the kernel checks
it once against variables:

```lean
private theorem getD_map_eq_true {α} {o : Option α} {f : α → Bool} {a : α}
    (ho : o = some a) (h : (o.map f).getD false = true) : f a = true := by
  subst ho; simpa using h

theorem witnessValid_some (hn : controlFlow? = some nodes) : witnessValidAt nodes = true :=
  getD_map_eq_true (f := witnessValidAt) hn witnessValidC_true
```

**313 s -> 3 s, statement byte-identical.** Two things are load-bearing, and skipping either
reproduces the blow-up in the *elaborator* instead:

- **Leave nothing to unification.** With `f` implicit, solving `?f` made the elaborator unfold
  `controlFlow?` and die on `maximum recursion depth`. Name the map body as its own `def`
  (`witnessValidAt`) and pass it explicitly, so both `o` and `f` are already determined.
- **The named body must not mention the dispatching `Option`.** `witnessValidC` becomes
  `(controlFlow?.map witnessValidAt).getD false` -- one delta step to match, no reduction.

Generalising: **any `unfold`/`rw`/`subst` whose motive captures a heavy constant is a kernel bomb** --
"heavy" meaning anything whose value is computed rather than written down: a parsed ELF, a resolved
symbol table, a decoded program, a generated array. The constant does not have to appear in the
*statement*; `unfold`ing a three-line definition that merely mentions it is enough.

The second instance found was exactly this, and it was four bombs at once. `executeDecode` is

```lean
def executeDecode (input : ByteArray) : Except ExecutionError DecodeOutcome :=
  match runnerSymbols with
  | none => .error .invalidArtifact
  | some symbols => runAnswer (runZesuDecodeRaw symbols input)
```

Three lines -- but `unfold executeDecode` leaves that `match` in the motive, and the kernel resolves
the ELF symbol table to check it. Four separate proofs unfolded it and each paid: 22.6 s, 21.5 s,
21.3 s, 21.4 s. One `executeDecode_some` lemma stating the dispatch against a *variable* `symbols`,
with all four sites rewritten through it, took the module **89 s -> 24 s**.

So the rule has a cheap form: **if a definition mentioning a heavy constant is unfolded at more than
one site, state its characterising equation once and rewrite through it.** You are not optimising a
proof, you are refusing to re-verify the same reduction N times.

**The one-line check before you write the proof.** Is the scrutinee of any `match` you are about to
unfold a *computed* constant? If yes, name the branch body and transport through a lemma generic in
the scrutinee. Concretely, prefer

```lean
def check : Bool := (heavy.toOption.map checkAt).getD false   -- determined by a transport lemma
```

over

```lean
def check : Bool := match heavy with | .ok x => <body> | .error _ => false   -- stuck; kernel re-reduces
```

Four modules on this project's critical path -- `GeneratedReachabilityExact`, `Layout`, `Preflight`,
`Runner` -- each cost ~23 s for exactly this, and all four dropped under 1 s. Nothing was shared
between them because oleans store terms, not reduction results: every module that leaves a `match`
stuck on the parsed ELF re-parses it in full.

A corollary worth knowing before you optimise a slow `native_decide`: **check what else in the module
forces the same value first.** `canonicalResultBuffer_ne_zero` profiled at 22.9 s and looked like an
expensive `native_decide`; it was not, and it vanished when an unrelated declaration in the same
module stopped forcing the artifact. Whichever declaration forces a heavy value first pays, and the
others can look guilty by overlapping it.

**Reverted here, so you do not repeat it:** replacing six of `wrapper_epilogue_to_exit`'s register
bullets with the write-set frame (`wrapperAfterFinalStackRestore_writes` + `.get r`) is better
hygiene and the codebase even records the frame lemma as missing -- but it measured *slower*, 26.7 s
to 30.7 s with `by decide` and 28.2 s with `of_decide_eq_true rfl`. The frame is the right tool when
it replaces a *composition* of steps; against a single `afterRegisterWrite` whose `simp` set is
already direct, the membership obligation costs more than it saves.

Counter-example worth keeping in mind: `forwardClosed_some` does the same `unfold`+`rw` over the same
generated arrays and costs under 1 s. The shape is a *suspect*, not a verdict -- which is exactly why
you profile instead of guessing.

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

### `let`-bound successor states are the dominant elaboration cost

A composition proof usually names its intermediate machine states with `let`:

```lean
let s7 := afterRegisterWrite s6 pc r7 x9 v
let s8 := afterRegisterWrite s7 …
…
refine ⟨final, ?_, confined, pc11, finalStack, finalInput, …⟩   -- 13 components
```

Every component's type mentions `final`, which is `let`-bound to a chain six deep. Unifying each
component against the goal's expected type **zeta-expands that whole chain**, once per component. That
single `refine` measured **~95 s** — against 15 s for the other 23 declarations in its module
combined.

Measure it this way, because nothing else attributes correctly: replace a proof body with `sorry` and
read the delta. In this file `sorry`ing seven candidate theorems took it 140 s to 15 s, and leaving
one live at a time showed six cost ~1 s and one cost 110 s. The profiler could not split them — with
async elaboration it reported ~150 s for each of the seven — and `head -n` truncation smears cost
across neighbours for the same reason.

**What does not fix it**, all measured: `clear_value` on the chain (the component types were already
built against the transparent value, so they then mismatch), swapping `rfl` for an explicit
`afterRegisterWrite_mem` chain (the `_`s cannot be synthesised), and `WritesOnlyRegs` + `grind` (two
`grind failed`, no gain).

**What does — use `Seg`.** It exists for exactly this and is measured: rewriting one prologue with it
took the proof **110 s → 0.8 s** and its module **126 s → 19 s**, statement untouched, body 119 → 87
lines.

`Seg` makes the successor state *existentially opaque*: every combinator concludes
`∃ next, Seg … next …`, so you write `obtain ⟨next, seg⟩ := seg.step …` and never name a post-state.
The deep term is never constructed, so nothing can zeta-expand it. It accumulates `trace`, `confined`,
`writes` (register frame), `mem` (`WritesOnlyWithin` over a `Region`), and `regs` (`RegsHold`,
last-write-wins — the write frame only says which registers were left *alone*, so written values must
be carried positively).

**Recognising the ritual it replaces**, ~206 occurrences across 9 files:

```lean
obtain ⟨rN, runN⟩ := someStep …
let sN := afterRegisterWrite s(N-1) pc rN dest val
have pcN … ; have agreeN … ; have retiredN … ; have codeN …     -- six haves per instruction
…
have prefixN := wrapperOwnStep … ; confined_steps [prefix6, …]   -- then rebuild the trace by hand
```

Each instruction's six `have`s become one `obtain ⟨_, seg⟩ := seg.step …`, and the whole trailing
`prefixN`/`confined_steps`/`Trace.snoc` block becomes `seg.confined` and `seg.trace`. The incoming
context is the *same four expressions at every step*: `agree.trans (seg.agree disjoint)`,
`seg.retired`, `codeIntact_of_mem_eq (seg.memEq noMemory_empty) code`, `seg.atPc`. Pass `_` for each
step lemma's `stepNo` and let unification pick `a + n`, which sidesteps all the `fromStep + 6 + 1`
versus `+ 3` defeq work.

**Three things that need judgement, not pattern-matching:**

1. **Choose `W` once, up front** — enumerate every register the whole segment writes before starting.
   The `destination` arguments are positional `Or.inr (Or.inl rfl)` terms, so inserting a register
   later renumbers them all.
2. **Register lifetimes.** A register written twice in one segment needs `Seg.forget` at the right
   point: `Seg.step` unconditionally records `⟨dest, value⟩`, so a later overwrite makes the `keep`
   obligation *correctly* false. `forget` weakens the recorded list along `sub : ∀ p ∈ kv', p ∈ kv`,
   which is `by simp` at any concrete list.
3. **Shapes that are not `step`/`stepJump`.** A step lemma bundling an extra conjunct into its `∃`
   needs a short adapter. **Stores have no `Seg` combinator at all**, and would be the first users of
   its memory interface with a non-empty `Region` — try one store site before committing to a sweep.

Two frictions the docstrings do not mention: `by decide` stops closing `keep` once a recorded value is
symbolic (use `of_decide_eq_true rfl`), and `Seg.memEq noMemory_empty` discharges every memory
obligation in one line when the segment is register-only.

### Module scope: keep the dependency graph flat and wide

Lean elaborates a module on one core; Lake parallelizes across modules only. A module's elaboration
time is therefore a serial segment of the build, and a chain of modules is a critical path that no
number of cores can shorten. This build was **996 s of critical path out of 1009 s** — nine modules in
a queue, one core busy, sixty-three idle.

**Target: no module over ~15 s** (the build is now ~123s end to end; the old 60s target dates from
when it was 1009s). Check with `lake build <module>`, which prints the time. Reach that by making the
expensive declarations cheap, not by splitting the file -- see the splitting verdict above.

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

*A genuinely expensive module.* Move out a **semantically coherent group** that references nothing
else in the file — step lemmas, a frame kit, a structure definition — into a module with a name that
says what it holds. `Level2WrapperProof` split this way: 57 step lemmas out, 38 s off the path, and
the result is still navigable.

What does **not** work is applying that mechanically: chunking a file into machine-named
`L<layer>_<chunk>` modules was tried across four modules and reverted (see the splitting verdict
above). The difference is not the technique, it is whether the new module boundary means something to
a reader. Never split down the middle of a chain of dependent declarations either; that just makes
two serial modules out of one.

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

**Target: no module over ~15 s** (the figure was 60 s when the build was 1009 s; it is now ~123 s).
Not a style preference — a module over that is a serial segment everyone waits on, and with 141
function instances still to prove the convention chosen now is multiplied by 141. Reach it by making
the expensive declarations cheap; if the module is genuinely a pile of independent lemmas, move a
named group out, never a machine-named chunk and never down the middle of the spine.

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

### Agreement across a step is a frame fact, never a case split

The single most expensive tactic found in this project:

```lean
have stackAgree : Agree decoderPreserved afterS2 afterStack := by
  intro register preserved
  cases register <;> simp only [...] at preserved ⊢ <;> simp_all [decoderPreserved, platformPreserved]
```

**11.4s of one theorem's 13.3s**, 8.5s of it in the closing `simp_all`. It splits all forty-odd
RISC-V registers against a six-deep state term to prove something disjointness settles without
looking at the state at all. The step writes only the bookkeeping registers and `x2`; write it as

```lean
have stackAgree : Agree decoderPreserved afterS2 afterStack :=
  (wrapperAfterFinalStackRestore_writes afterS2 retiredStack _).agree decoderPreserved_disjoint_sp
```

and it is free. `WritesOnlyRegs.agree` and `RegSet.Disjoint.{union, only}` already exist; a preserved
predicate needs its disjointness proved once (`decoderPreserved_disjoint` just inherits
`platformPreserved_disjoint`, since `decoderPreserved r = r ≠ x1 ∧ platformPreserved r`).

**The counter-case, because the same tool has the opposite verdict two lines away.** Using the write
set for the individual register *reads* -- `(…_writes …).get r (by decide)` in place of a direct
`simp` that reads one field -- measured **slower**: 26.7s to 30.7s, and 28.2s with
`of_decide_eq_true rfl`. The frame pays against a proof that would otherwise case-split every
register; it does not pay against a `simp` already reading one field. Measure, do not generalise.

### Before you optimise a proof, check whether it is proved twice

`wrapper_epilogue_to_exit` and `wrapper_epilogue_complete` opened with a **character-identical
34-line block** -- a stack restore, a register reload, and eight facts about the result -- so all of
it, including the agreement case-split above, elaborated twice. Eight named lemmas replaced it.

Finding these is mechanical: hash every window of N consecutive indented lines across the proof files
and report windows occurring more than once. Filter out repeated *signatures* (hypothesis lists on
class lemmas are legitimately similar); what you want is repeated tactic blocks.

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
- Update `tools/contract-target-curation/proof-progress.json` at every completed refinement
  checkpoint, before reporting or committing the checkpoint, so the production call-hierarchy
  flamegraph reflects the theorem just proved. Unconditionally proved functions are green.
  Green/yellow stripes require all parent-owned machine instructions to be proved with only immediate
  child function contracts assumed. Active proof work is yellow, contract-only functions are
  yellow/red striped, and functions with none of those are red.

## Pull request descriptions

- Name every theorem or other statement proved by the PR and state what each proof establishes.
- Name every theorem, contract, assumption, or proof obligation weakened by the PR and describe the
  weakening precisely. This includes adding assumptions, narrowing inputs, weakening conclusions,
  replacing a proof with an axiom or placeholder, and reducing machine-code or specification coverage.
- If the PR proves no new statements or weakens none, say so explicitly. Do not make reviewers infer
  either fact from the diff.
