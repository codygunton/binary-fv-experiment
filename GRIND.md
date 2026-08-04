# GRIND.md — simp and grind set conventions

This document is the single source of truth for how this repository organizes `simp`-based and
`grind`-based proof automation. Read it before writing a closing tactic that more than one proof
will use, before adding a `@[simp]` or `@[grind =]` attribute to a shared lemma, and before
proposing a new named set.

`AGENTS.md` links here from its proof-automation section. Do not duplicate this content there.

**Status: skeleton.** Section 7's registry is empty and section 8 has no phases yet. Both are filled
from the survey described in [`docs/agents/proof-pattern-survey.md`](docs/agents/proof-pattern-survey.md),
which is running now. Do not land a new set before its survey row exists.

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
two states rather than observing one. See section 4's note on projections.

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

None. The repository has zero `@[grind …]` attributes and zero `register_simp_attr`.

| Set | File | Closes | Facts | Status | PR |
|---|---|---|---|---|---|
| _(none yet)_ | | | | | |

**Grandfathering note.** An empty table does not mean no simp attributes exist. There are 35 uses of
the **global** `@[simp]` set, which section 5's first rule forbids for new work:
`MemoryRepresentation/EntryOffsets.lean` 9, `Entrypoints/ZesuDecodeRaw/Classify.lean` 7,
`Entrypoints/ZesuDecodeRaw/Accessors.lean` 7, `MemoryRepresentation/ChainOffsets.lean` 6,
`Entrypoints/ZesuDecodeRaw/DecodeGlue.lean` 3, `RiscV/Elfling/SentinelBridgeWitness.lean` 2,
`Entrypoints/ZesuDecodeRaw/Runner.lean` 1. They are narrow projections on decoder-local datatypes,
not step-unfolding facts, so they are left alone; do not add more.

## 8. Rollout

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

### Phase 2 — pending — one frame set, keyed to the shared transformers

**Scope discipline is the whole point of this phase.** Independent areas proposed sets keyed to
their own local composites (`wrapperAfter*`, `allocatorAfter*`, the jump composite,
`rawErrorAfter*`). Landing those as separate sets would institutionalise the duplication rather
than remove it: eleven successor-state definitions each carry a hand-rolled
`_agree`/`_mem`/`_pc`/`_retired_present` family (27, 11, 9, 3 theorems respectively), and every one
is a composition of the same four transformers in `Step/ControlFlow.lean`.

So: **collapse the ad-hoc composites into instances of `afterRegisterWrite` first, then build one
set keyed to the five shared transformers** in `Step/ControlFlow.lean` and `Step/Call.lean`.

Measured demand for the two largest rows:

| Row | Inline re-proofs | Files |
|---|---|---|
| `coreControlFlowNextState ∘ tryStepControlFlowAfterIncrement` (the `executeState` row) | **284** | 23 |
| `afterRegisterWrite` register survival | **181** | 15 |

The second row's lemma **already exists** — `afterRegisterWrite_register` — and is used twice in the
entire repository. Two independent ergonomic causes were diagnosed: it takes five explicit
disequality arguments, so citing it is longer than re-deriving it; and `let`-bound successor states
hide it. A grindset fixes both, because `grind` discharges those disequalities itself (they are 22%
of all obligations in one area, 169 and 81 in two others).

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
