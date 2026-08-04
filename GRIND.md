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
- **A frame fact about a step that can fail needs an explicit `grind_pattern`.** Our steps are stated
  as `∃ retired, Runs (try_step stepNo false) state …`, so the successor state is bound by a
  hypothesis rather than being a function application of the predecessor. Automatic pattern
  inference then determines only the successor and leaves the other variables unknown, and the
  lemma silently never fires. Write a multi-pattern naming enough terms to determine every variable:

  ```lean
  grind_pattern pc_after_step => Runs (try_step stepNo false) state, some after, after.regs.get? PC
  ```

  Verify the lemma fires. A registered lemma that never matches is worse than no lemma, because it
  looks like coverage.
- **Prefer a projection to a relation.** `Agree platformPreserved base state` is a relation between
  two states, so it does not fit the frame-fact shape and its chaining is written by hand — 95
  `Agree.trans` calls. If it is restated as equality of a projection, `platformView base =
  platformView state`, congruence closure chains it with no user effort. The survey should test
  this on `platformPreserved`, `decoderPreserved`, and `DecoderMachinePre` before it is adopted.
- **Put facts in a sub-namespace** so file-private lemmas in consumer files do not collide.
  Attributes and tactic macros are reachable without `open`.

### Don'ts

- **Do not register step-unfolding definitions for `grind`** (section 3).
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

None yet. This table is populated by the survey.

| Set | File | Closes | Facts | Status | PR |
|---|---|---|---|---|---|
| _(empty)_ | | | | | |

## 8. Rollout

No phases yet. Phases are proposed from the survey's findings, ordered by measured lines removed per
unit of risk, and each is one reviewable change following section 6.

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
