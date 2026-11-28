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

## S14

**Defined.** Registry `ZesuExec/Service/` (495 lines with `Service.lean`), one file per CSR, each
citing `/home/cody/zisk` (eed62f4d9) file:line: `0x813` DMA memcpy, register and immediate count
(`Memcpy.lean`, 109 lines; keeps `ziskMemcpy` and relates it, `ziskMemcpyMem_eq`); `0x816` DMA
memset, both forms (`Memset.lean`, 62); `0x805` SHA-256 compression plus the full SHA-256 model
(`Sha256f.lean`, 116); `0xf12` marchid read, the exit `ecall` (`ziskExit`) and `ZiskBoot`
(`Arch.lean`, 52); shared vocabulary (`Basic.lean`, 116). `next` takes a service step at a word
the decoder does not know; `SailReaches` gained the matching constructor (STATEMENTS.md S14).

**Tested** (`tools/svc_test.py`, 100 random cases per check, the Lean registry evaluated vs
`ziskemu`; `map/svc_test.json`, `map/svc_test_relaxed12.json`):

| check | result |
|---|---|
| 0x813 register count | copy and registers 100/100; staging word 0/100 (`Layout.extraParams` 0xa0400f00, ZisK 0xa0000f00) |
| 0x813 immediate count | 100/100 |
| 0x816 register count | 100/100 |
| 0x816 immediate count | pinned ziskemu panics on load (`riscv2zisk_context.rs:695`); 100/100 on `ziskemu-relaxed12` |
| 0x805 | 100/100 |
| 0xf12 (after `ZiskBoot`) | 100/100 |
| exit `ecall` output | 100/100 |
| `memmove` run by ziskemu vs `MemcpyPost` | window, registers 100/100; staging word 0/100 (same cause) |
| `memset` run by ziskemu vs `Memset.Post` | 100/100 |

Trust metric: 4 CSR numbers defined (`map/reviews.json` `csr`), 3 emulator-tested clean
(`0x816`, `0x805`, `0xf12`); `0x813` fails only on the staging cell.

**Proved.** `memmove_spec`/`memmove_sail` (memcpy's contract, bound 3) and `memset_spec`/
`memset_sail` (bound 10; the indirect jump resolved inside the proof: `0x800e0720 + 16 (a1 & 0xff)`,
a 256-entry table checked by kernel evaluation, `Fn/Memset/Table.lean`, ~200 s), each with
`pre_nonvacuous`; snapshot check = the `fn-memmove`/`fn-memset` emulator rows above (real ZisK
instead of Unicorn, which has no ZisK CSRs). Proof lines: memmove 98, memset 336.

**Not proved.** `zkvm_sha256`: contains `rev8` (S12: no Zbb in the Sail model). Contingency taken:
drafted service contract (STATEMENTS.md S14) with the Lean SHA-256 model (agrees with `hashlib`);
no `next` intercept (coordinator: rule 11). The `fn-sha256` emulator check in `svc_test.py`
does not work yet: with the binary's whole `.text` linked in, ziskemu-relaxed12 ends the run
before the harness dumps (all-zero output); not diagnosed.

**Findings.** (1) The pinned ZisK cannot load the target ELF (immediate-count memset).
(2) `Layout.extraParams` is wrong vs ZisK (`OPEN/services/extra_params.md`).

**Cost.** One ledger item (id 20, 07:10–08:00Z); dollars come from `zmap merge`.

**Forecast implication.** A short service-only function costs a hand proof of ~100–300 lines
against `next`; a CSR the executor meets inline still ends a symbolic path (an executor rule that
turns a service site into a call-like leaf is the next step for functions with inline CSRs).
