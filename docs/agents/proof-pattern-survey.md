# Proof-pattern survey

This survey measures where the writing in PR #60 (`ssz-level1`) went and what would remove it. Its
output populates sections 7 and 8 of [`GRIND.md`](../../GRIND.md).

You have been assigned one area. Read [`GRIND.md`](../../GRIND.md) sections 1–5 first; they define
the two kinds of set, the attribute variants, and the constraints your proposal must satisfy. This
document defines only what you return.

**Report what you measured, not what you expect.** A count you did not take is worth less than an
absent row. If a question does not apply to your area, say so and say why.

## Scope

Only files listed in your assignment. Do not edit proofs. You may add scratch files under
`/tmp` and you may run `lake build <module>` and the Lean LSP tools, but leave the tree unchanged.

The build in this worktree is warm: `lake build BinaryFv` completes with 339 cached jobs. A focused
`lake build BinaryFv.Zesu.MachineExecution.<Module>` is the fast inner loop. Do not run
`nix build`.

## What to return

Six sections, in this order. Keep it terse; tables over prose.

### 1. Goal population counts

Classify every tactic block in your area into exactly one population and give counts. These decide
whether `grind` is even the right instrument, so they come first.

| Population | Definition | Your count |
|---|---|---|
| P1 frame | reads an observation off a state after a transformer ran | |
| P2 address arithmetic | `BitVec` arithmetic, `sign_extend`, offset computation | |
| P3 membership and decoding | region membership, instruction words, `native_decide` obligations | |
| P4 other | anything else — describe the largest three | |

### 2. The two axes

List every **state observation** read in your area (`regs.get? PC`, `.mem`, `RetiredCounterPresent`,
`Agree platformPreserved`, …) with its occurrence count, and every **state transformer** that
produces a successor state, with its occurrence count.

Mark each observation as a projection of one state or a relation between two. Relations are the
candidates for the projection reformulation in `GRIND.md` section 5.

### 3. The frame grid

For each (observation, transformer) pair that occurs in your area, one row:

| Observation | Transformer | Named lemma? | Inline re-proofs | RHS shape |
|---|---|---|---|---|

- **Named lemma?** — the existing lemma's name, or `absent`.
- **Inline re-proofs** — how many times a `have` in your area proves this pair inline instead. **This
  column is the payoff estimate.** Give the file:line of two examples.
- **RHS shape** — `unchanged`, `conditional` (an `if`), or `derived` (some other expression). This
  determines the attribute per `GRIND.md` section 5.

Then state: how many grid cells are named, how many are absent, and the total inline re-proof count.

### 4. Fallible-step check

Our steps are stated as `∃ retired, Runs (try_step stepNo false) state …`, so a frame lemma about
them is implication-shaped and needs an explicit `grind_pattern` (`GRIND.md` section 5).

Report: how many of your area's grid cells are implication-shaped, and for **one** of them, write the
multi-pattern you would use and name which variable each listed term determines. If you can test
whether it fires, report that; if not, say it is untested.

### 5. Proposed set

At most two proposals. For each:

- name, and which of the two kinds in `GRIND.md` section 3 it is;
- Layout A or B, and why;
- the facts it would hold, and the count;
- the three-unrelated-files check from `GRIND.md` section 6 — name the files;
- **estimated lines removed**, and how you computed it;
- what it does *not* cover in your area.

If your area does not justify a set, say so. That is a real finding, not a failure.

### 6. Grind viability evidence

Pick three representative goals from your largest population. For each, record what closes it and how
long, using `lean_multi_attempt` or a scratch file:

| Goal (file:line) | Population | Existing tactic | `grind` | `grind` + hints | Time delta |
|---|---|---|---|---|---|

State plainly if `grind` fails on all three. `GRIND.md` section 2 explains why we expect it to lose
on P2 and P3, so a negative result there is expected and useful. Do not tune a hint set until it
passes and then report only the passing configuration; report what you tried.

## What not to do

- Do not propose a set without the file-count check and a line estimate.
- Do not register anything, edit proofs, or add attributes. This survey only measures.
- Do not report a `grind` success without its time, or a failure without what you tried.
- Do not recommend the global `@[simp]` set for anything.
- Do not describe a pattern you did not count.
