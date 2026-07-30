# Salvaged uncommitted work — 2026-07-30

These are working-tree changes rescued from agent worktrees under `.claude/worktrees/`, which are
temporary and get reaped. Nothing here was ever on a branch.

- `task6av.patch` — **already landed** as `a7ff2e8`. Kept for provenance.
- `integrate-emitted-bodies.patch` — **not landed.** All five 6a-ii contract families plus the 6a-v
  restructure, on the correct base, with the `Bool → Prop` mirror converses that license a `post = ok`
  and the gates that render tautological conjuncts as gaps instead of passes.

  It fails to build with **exactly one error in 6,106 lines**: a verbatim duplicate of
  `instances_never_entered`. Delete those seven lines and it builds green (177/177), reaching
  **post 13 decided, 11 refutations, 2 licensed passes** — the first passes in the project resting on
  a proved converse rather than an asserted one — with the ledger green at the untouched heartbeat
  budget. Verified by the salvage pass, not by me.

  It supersedes the `task-6a-ii-allocator` and `task-6a-ii-results` commits, which sit two commits
  behind and would revert `edeb57f`.
- `integrate-emitted-bodies-STATUS.md` — that agent's own notes.

Apply with `git apply` from the branch of record. `task6av.patch` is already applied; do not reapply.
