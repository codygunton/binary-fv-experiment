## S12

**Proved.** 14 instruction forms, each with decoder, executor, soundness and Sail simulation
cases (`sail_step_sim` covers all 46 `Instr` constructors): `xor addiw bge lwu srliw subw lh ori
srl divu remu slliw slti slt`. An undecodable word (`unimp`, any form the decoder lacks) now ends
a path with a leaf whose obligation `Oblig.unreachable` never holds, so the leaf is a goal that
the path is infeasible; before, the whole run failed.

**Not proved (contingency).** `srai`: the generated Sail model implements the arithmetic shift as
a rotation, so the simulation goal is false; fixing it needs a regenerated `sail-riscv-lean`.
`maxu packh pack rev8 bext bset bclri clz`: the compiled model has no bit-manipulation
instructions. Goals and evidence in `OPEN/forms/`.

**Measured.** Target functions blocked: 132 → 33 (with any blocker 133 → 34; blocked only by
missing non-CSR forms 103 → 4). The 33 still blocked: CSRs 16, unsupported forms 14 (srai and
the bit-manipulation forms), irreducible 7, unresolved indirect calls 6, unresolved indirect
jumps 2, compressed 2, `ecall` 2 (a function can have several).

**Cost (ledger).** 14 closed forms $7.23 (mean $0.52, range $0.30–$1.31, 1–3 minutes each);
the two open items $1.01; `unimp` $3.86; stage total in items $12.87, session $15.45.

**Forecast implication.** A form costs about half a dollar once the executor, soundness and
simulation patterns exist, so forms are a negligible share of the total. The remaining
form blockers depend on the Sail model, not on proof effort: regenerating the model with the B/Zbkb
extensions and a corrected arithmetic shift would unblock the last 14 form-blocked functions.

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
