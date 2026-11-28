## S11

**Measured.** `budget_auto` evaluates a cut's budget at its literal address (`measure_norm`) and
closes it with `omega`. It closes the budget stage on every leaf of the five plans: 124/643 before,
643/643 after. `oblig_auto` (region normal form, `sym_rw`, `omega`/`bv_omega`/`region_arith`,
opened assertions) closes the obligation stage on 71/186 leaves that have obligations; before it
was 58/186. Per plan: F6 27/27 (was 20), TX 21/23 (was 15), F1 6/6, F2 17/17, DTF 0/113. Leaves
closed whole: 17/643 before and after. Every leaf that passes both stages fails at the exit goal
(postcondition, next cut's assertion, callee precondition), which S11 does not address.

**Hand lines.** 39 TX budget sub-proofs became `budget_auto` (TX leaf files: 70 lines deleted, 39
added). The toy return leaf of `Test/Vc.lean` (23 lines) is now closed by `zesu_auto`.

**Build time.** Failures are cheap: `zesu_auto` runs one pass per leaf (`leaf_diag` proves the leaf
or names the stage that stopped it), and `zesu_apply` skips lemmas about other functions' `Env`.
TX `zesu_auto` now runs after the facts.

- Fn/TX: 366 s → 92 s.
- Fn/F6: 132 s → 55 s.
- F1/Vc: 46 s → 20 s.
- F2/Vc: 35 s → 19 s.
- DTF/Vc: 308 s, against 304 s for the old tactics in W. Budgets passing did not bring back the
  897 s regression.

**Cost.** Ledger item 2 (S11Auto): $15.07 for the session, $13.86 of it inside items.

**Forecast.** Budgets are no longer a residual class. The 386 manual or open `budget` leaves of
S10's class table need no hand budget proof in future plans. Obligations close when the bound is
linear in the assertion's facts:
- loop cursors under an invariant (F6),
- the saved `ra` with a fact (TX).

They stay manual when the bound comes from decoder semantics:
- TX `10c_3` and `1a0_3`;
- DTF's 113 byte-loop and call-argument reads under `PlainA ∨ RetA`.

The automation gate (60% whole-leaf share) is not moved by S11. The next lever is the exit stage
(`post`, `cut`, `callee-pre`, `tail`).
