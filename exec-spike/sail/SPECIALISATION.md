# Specialisation of sail-riscv 65ddde80 for the Zesu profile

Two patches against the pinned sail-riscv source, applied by `zesuSailRiscvRaw` in
`nix/proof.nix` before the stock `postPatch`. The generated tree is committed at
`exec-spike/sail-riscv-lean` and checked by `nix build .#zesuSailRiscvLeanRegenerationCheck`.
The third patch, `00-sail-lean-asr.patch`, is a fix to the Sail compiler's library (not to the
model; see `PROVENANCE.md`); the module list (S12b) adds `Zba;Zbb;Zbs;Zbkb`.

## `01-profile-config.patch`: changed configuration keys (`config/config.json.in`)

| Key | Stock | Zesu |
|---|---|---|
| `memory.pmp.count` | 16 | 0 |
| `memory.pmp.usable_count` | 16 | 0 |
| `memory.regions` | ROM `0x1000+0x1000` (IOMemory), MMIO `0x2000000+0x10000000`, RAM `0x80000000+0x80000000` | input `0x40000000+0x40000000` (IOMemory, not cacheable, not coherent; r, not w, not x), ROM `0x80000000+0x8000000` (IOMemory, not cacheable, not coherent; r, not w, x), RAM `0xa0000000+0x20000000` (MainMemory, not cacheable; r, w, not x); all other attributes copied from the stock RAM region. The read-only regions are IOMemory because the model's validator (`check_pma_region`) requires MainMemory to be readable and writable |
| `platform.clint.supported` | true | false |
| `platform.simple_interrupt_generator.supported` | true | false |
| `extensions.S.supported` | true | false |
| `extensions.U.supported` | true | false |
| `extensions.Sv32.supported` | `@CONFIG_XLEN_IS_32@` | false |
| `extensions.Sv39.supported` | `@CONFIG_XLEN_IS_64@` | false |
| `extensions.Sv48.supported` | `@CONFIG_XLEN_IS_64@` | false |
| `extensions.Sv57.supported` | `@CONFIG_XLEN_IS_64@` | false |
| `extensions.Ssccptr.supported` | true | false |
| `extensions.Sscofpmf.supported` | true | false |
| `extensions.Sscounterenw.supported` | true | false |
| `extensions.Sstc.supported` | true | false |
| `extensions.Sstvala.supported` | true | false |
| `extensions.Svade.supported` | true | false |
| `extensions.Svadu.supported` | true | false |
| `extensions.Svinval.supported` | true | false |
| `extensions.Svrsw60t59b.supported` | `@CONFIG_XLEN_IS_64@` | false |
| `extensions.Svnapot.supported` | `@CONFIG_XLEN_IS_64@` | false |
| `extensions.Ssnpm.supported` | `@CONFIG_XLEN_IS_64@` | false |
| `extensions.Svpbmt.supported` | `@CONFIG_XLEN_IS_64@` | false |
| `extensions.Svvptc.supported` | true | false |

The S-mode extensions (`Ss*`, `Sv*`, `Ssnpm`) are disabled because S and Sv39 are: the model's
own `config_is_valid` rejects Svrsw60t59b, Ssccptr, Svade, Svadu, Svpbmt, Svnapot, Svvptc
(`check_mmu_config`) and Sstvala (`check_misc_extension_dependencies`) without them; the rest
depend on S by definition. RAM is not cacheable because `Ziccif` (kept: disabling it turns the
4-byte fetch into two 2-byte fetches) requires every cacheable coherent main-memory region to be
executable, and RAM is not (`check_mem_layout`); `cacheable` is read only by the validator. With these keys
`config_is_valid` holds, so `init_model ""` runs (engine A of `zesu-difftest`).

`dtb_address` (`0x1000`) is unchanged: the model's validator accepts it.

## `02-specialise.patch`: hunks

Every hunk replaces a definition body by its value under the profile and carries a
`// ZESU-SPEC <class> <justification>` comment. Invariants: I1 `cur_privilege = Machine`;
I2 `mip & mie = 0`; I3 `htif_tohost_base = None`; I4 `hart_state = HART_ACTIVE`; and, beyond the
plan's fixed list, I5 `elp = NO_LP_EXPECTED` and I6 `mstatus.MPRV = 0` (see the notes).

| File | Definition | Class | Justification | Lines removed |
|---|---|---|---|---|
| `model/pmp/pmp_control.sail` | `pmpCheck` | C | `memory.pmp.count = 0`, so `sys_pmp_count == 0` and the stock body returns `None()` | 28 |
| `model/sys/platform.sail` | `within_clint` | C | `platform.clint.supported = false`: `plat_have_clint` is false | 10 |
| `model/sys/platform.sail` | `within_sig` | C | `platform.simple_interrupt_generator.supported = false`: `plat_have_sig` is false | 7 |
| `model/sys/platform.sail` | `within_htif_writable` (and so `within_htif_readable`) | R (I3) | `htif_tohost_base = None` takes the `None()` arm | 4 |
| `model/extensions/I/jalr_seq.sail` | `execute JALR` | C | Zicsr is not compiled, so `currentlyEnabled(Ext_Zicfilp)` is false and `update_elp_state(rs1)` has no effect | 1 |
| `model/postlude/step.sail` | `run_hart_active`, `F_RVC` arm | R (I5) | the landing-pad trap is taken only when `elp = LP_EXPECTED` | 8 |
| `model/postlude/step.sail` | `run_hart_active`, `F_Base` arm | R (I5) | as above | 14 |
| `model/postlude/step.sail` | `try_step` | R (I4) | `hart_state = HART_ACTIVE` selects `run_hart_active` | 4 |
| `model/sys/vmem.sail` | `translateAddr` | R (I1, I6) | effective privilege Machine, `translationMode(Machine) = Bare`: address unchanged; the shadow-stack access fault is kept | 59 |
| `model/sys/sys_control.sail` | `dispatchInterrupt` | R (I2) | no pending enabled interrupt: `getPendingSet` returns `None()` | 7 |

No trap outcome was deleted: illegal instruction, access faults, misaligned fetch and `ecall`
paths are untouched; `translateAddr` keeps the shadow-stack fault. No hunk was dropped.

Notes on classes (deviations from the plan's classification, recorded in `LOG.md`):

- The plan lists the landing-pad hunks of `run_hart_active` as Class C. They are not equal for
  every state: the stock body reads the register `elp`, which the compiled model can hold at
  `LP_EXPECTED` in an arbitrary state (`zicfilp_restore_elp_on_xret` writes it on `mret`/`sret`
  because `hartSupports(Ext_Zicfilp)` is true). They are therefore Class R under I5
  `elp = NO_LP_EXPECTED`, which `reset_elp` establishes and no instruction of F0–F6, `alloc`,
  `free` changes. The `JALR` hunk is Class C as planned.
- `translateAddr` is equal under I1 only when `mstatus.MPRV = 0` (otherwise `effectivePrivilege`
  uses `mstatus.MPP` for data accesses). `legalize_mstatus` forces `MPRV = 0` when U is not
  supported, so I6 holds on every state reached through CSR writes; `Configured` states it.
- `dispatchInterrupt`: the stock `getPendingSet` also asserts `currentlyEnabled(Ext_S) |
  mideleg = 0`; under the profile (S unsupported) the stock body fails that assertion when
  `mideleg ≠ 0`. The specialised body returns `None()` there instead.
