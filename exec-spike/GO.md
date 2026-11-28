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
