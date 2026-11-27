# exec-spike log

Times local (2026-11-27). GNU time: `/usr/bin/time` is not installed on this host; every
`/usr/bin/time -v` of the plan runs as `/home/cody/.cache/zesu-tmp/exec-spike/gtime/bin/time -v`
(nixpkgs `time-1.10`).

## S0 — workspace and baseline
- Worktree `.worktrees/exec-spike`, branch `exec-spike` from `main` 38a3a14a.
- `nix build .#sailRiscvLean -o build/sail-riscv-lean`: ok (6 s).
- B0 `lake build BinaryFv`: ok, 91 jobs, wall 64.2 s, user 121.3 s, sys 41.0 s, peak RSS 1.83 GiB.
- `nix build -L .#sailRiscvLeanRegenerationCheck`: running (log `~/.cache/zesu-tmp/exec-spike/regen.log`).
- Package `exec-spike/` created (lakefile as in the plan); `sail-riscv-lean` = copy of `generated/sail-riscv-lean`.
- Interface files written and built: `ZesuExec/{Machine,Decode,Image,Service,Logic}.lean`
  (`lake build ZesuExec.Logic` ok). Deviation: `step` also requires `pc % 4 = 0` (Sail's fetch
  check without Zca); `Reaches.trans`, `Reaches.loop`, `memcpy_spec` proved.

## S2
- SnapDiff, 2026-11-27: S2 steps 4–5 (difftest, engine B). Gate part: **pass**, 45/45 `agree`.
  - `tools/snap.py` imports zesislar `origin/main` 1dd527a9b `tools/oblig/exec/run.py` (read-only
    worktree `~/.cache/zesu-tmp/exec-spike/zesislar-main`). Deviation from run.py: its bump-allocator
    hooks on `alloc/resize/remap/free` are removed, so Unicorn runs the real `alt_fl_alloc.alloc`,
    `remap` (F0) and `free` through the vtable; only the `memcpy` hook (ZisK service) stays. The
    initial list buffer is still placed by run.py's setup at `0xb0000000` (not by `alloc`).
  - Snapshot (`zesu-snap/1`, `test/snapshots/<Fn>/<id>.json`, 2.1 MB): entry `pc`, `x1..x31`,
    every byte of each 4 KiB page (clipped to rodata/input/RAM) the run reads or writes, plus
    memcpy src/dst, scratch word, argument ranges and ELF RAM data; exit `pc`, `x1..x31`, changed
    bytes, Unicorn instruction count. 16–32 KiB of memory per snapshot.
  - Inputs: F1 = zesislar's 15 `keysEnsureCapacity` rows (no-growth, growth from cap 0, growth
    with remap-null → alloc + memcpy + free) + 4 in `tools/snap_inputs/keysEnsureCapacity.json`
    (shrink request, grow to 200, byte-size overflow → OutOfMemory, 2^30 request refused by the
    real allocator → OutOfMemory). F2 = zesislar's 26 `decodeItem` rows (strings, lists,
    length-of-length 1–8, truncated/too-long errors, empty input).
  - `ZesuExec/Test/Difftest.lean`: compares pc, x1..x31, every entry byte (changed → exit value,
    else entry value) and transitions = Unicorn instruction count. Negative checks (mutated
    exit reg, exit byte, missing entry page, count) each print `DIFFER` and exit 1.
  - Measurements: `lake build zesu-difftest` 3.4 s wall, 925 MB peak RSS; snapshots 1.6 s for
    all 41 base inputs; 45 difftest runs 9.3 s wall total (~0.2 s each). F1 runs 29–187
    transitions, F2 15–75.
  - Next: `for f in test/snapshots/F{1,2}/*.json; do lake exe zesu-difftest --fn $(basename $(dirname $f)) --snap $f; done`.

## S4 — executor (coordinator)
- 2026-11-27: `Sym/{Types,Env,Smart,Exec,Tactic}.lean` written and built. Address forms: `lit` (rodata),
  `ptr r off`, `ptr r off + idx`, `ptr r off + (idx << k)`. Loads: fast path when the newest
  overlapping write (or `known` entry) has the same offset and width, else byte-by-byte `cat`.
  Symbolic `jalr` targets emit `Oblig.aligned t 4`.
- Measurement (S4 step 5, early): `sym_run` over F1 from entry, `cuts := []`, fuel 400: 8 leaves
  (3 `ret`, 5 `call`), whole file (elaboration + compiled eval + kernel `Eq.refl` check)
  1.20 s wall, 1.52 GB peak RSS. Within the 60 s / 8 GiB gate; no representation change needed.
- Next: `Sym/SmartLemmas.lean`, `Sym/Sound.lean` (`stepI_sound`, `run_sound`).
- 2026-11-27: `Sym/{SmartLemmas,MemLemmas,LoadStore,Sound}.lean` built. `run_sound` proved
  (`#print axioms`: propext, Classical.choice, Quot.sound). Deviations from the plan's statement:
  extra hypothesis `RodataLoaded img m` (needed for literal rodata loads) and extra conclusion
  `SameOutside (InWritable env S) m m'`; `Match` carries `regsLen : S.regs.length = 32`.
  `bv_decide` was removed (its proofs add `_native.bv_decide` axioms); bit-level proofs instead.
  Literal `jalr` targets also check `t < 2^64`.

## S1 — specialised Sail model (TrackT)
- 2026-11-27 01:45 TrackT: S0 gate confirmed (`regen.log`: "Generated source matches", EXIT 0).
  Scratch worktree `~/.cache/zesu-tmp/exec-spike/sail-riscv` (branch `zesu-spec`, pin 65ddde80).
- Patches `sail/01-profile-config.patch` (config keys) and `sail/02-specialise.patch` (10 hunks:
  C `pmpCheck`, `within_clint`, `within_sig`, `execute JALR`; R `within_htif_writable` (I3),
  `run_hart_active` landing pad ×2 (I5), `try_step` selector (I4), `translateAddr` (I1+I6),
  `dispatchInterrupt` (I2)). No hunk dropped. Deviations (see `sail/SPECIALISATION.md`): the
  landing-pad hunks are Class R under an extra invariant I5 `elp = NO_LP_EXPECTED` (the plan calls
  them C, but the stock body reads `elp`); `translateAddr` also needs I6 `mstatus.MPRV = 0`.
  `dtb_address` left unchanged (Lean generation does not validate the configuration).
- `nix/proof.nix`: `zesuSailRiscvRaw` (= `sailRiscvRegeneratedRaw.overrideAttrs` with `patches`),
  `zesuSailRiscvLean`, `zesuSailRiscvLeanRegenerationCheck`, exported via `proof.public`.
  `nix build -L .#zesuSailRiscvLean`: ok, 6 min 57 s wall. Result copied to `sail-riscv-lean`.
  `nix build -L .#zesuSailRiscvLeanRegenerationCheck`: "Generated source matches", EXIT 0.
- Effect in the generated Lean: `pmpCheck`, `dispatchInterrupt`, `within_clint`, `within_sig`,
  `within_htif_*`, `within_mmio_*` became pure functions; `translateAddr` reads no register.
- Three variants, `lake build LeanRV64DExecutable` in scratch packages (24 cores via `taskset`):

  | Variant | files | lines | wall | user | peak RSS | defs reachable / registers read (`tools/reach.py`, addi via `execute_ITYPE`) |
  |---|---|---|---|---|---|---|
  | stock (committed tree) | 111 | 54,283 | 66.1 s | 123.0 s | 1.83 GiB | 474 / 87 |
  | config patch only | 111 | 54,283 | 59.6 s | 113.9 s | 1.82 GiB | 474 / 87 |
  | both patches | 111 | 54,175 | 60.9 s | 115.1 s | 1.83 GiB | 331 / 76 |

  The configuration alone changes only inlined constants (same line count, same reach).
  `reach.py` counts textually, including the trap-handling paths of `try_step`.
- Gate S1: passed on the top rung (both patches). `sail/PROVENANCE.md`, `sail/SPECIALISATION.md`.
- Next: S3 step 1-2 (`tools/closure.py` copied 55 modules, no `BinaryFv.Zesu` import, no
  `native_decide`); repair against the specialised tree.
- 2026-11-27: `Test/Sym.lean` builds: all 32 `Instr` constructors (the plan's list of "33 forms"
  names 32 mnemonics) agree between `stepI` and `exec`; refusals of
  `csrrs`, store past end, odd halfword load hold (`decide +kernel`). Gate S4 met.

## S5 — functions (coordinator)
- 2026-11-27: `Fn/Common.lean` (entry state/env, `entry_match`, `entry_wf`, `inWritable_entry`).
  F0 `f0_spec : Spec zesuImage 0x8004218c 9 Pre Post` proved; axioms standard; `Fn/F0/Proof`
  builds in ~1 s.
- 2026-11-27 ProveF2: F2 `rlp.decodeItem` proved. `f2_spec : Spec zesuImage 0x800d6960 75 Pre Post`;
  `#print axioms` = propext, Classical.choice, Quot.sound (`#guard_msgs` in `Fn/F2/Proof.lean`).
  Three `sym_run`s, cuts = the loop heads `0x800d6a24`, `0x800d6ac4`, fuel 100: entry 11 leaves
  (9 returns, 2 loop entries), each loop head 3 leaves (back edge, error, success); `run` never
  returned `none` (no unaligned access). Loops: invariant `Inv` (length bytes read `j` of `w`,
  accumulator = big-endian value), induction on `w - 1 - j` (`loop_reaches`), 5 instructions per
  back edge, at most 17 for the last trip; tight bound 23 + 7*5 + 17 = 75 (expected 75), so
  `Reaches.loop` (bound `(μ+1)*c`) was not used. Loop-head states are `entryState` with `var 32` =
  bytes read and `var 33` = caller `s0` (generic `entry_match_vars` in `Fn/F2/Lemmas.lean`).
  Clean `lake build ZesuExec.Fn.F2.Proof` (F2 modules only; dependencies built): 8.05 s wall,
  13.7 s user, peak RSS 1.96 GiB; `Proof.lean` alone 5.4 s. The three `sym_run`s alone (scratch
  file): 1.69 s wall, 1.58 GiB peak (bare import 0.68 s, 1.37 GiB). Lines: Spec 158, Regions 47,
  Proof 738, Lemmas 399. Non-vacuity `example : ∃ m, Pre m` (witness with input `[0x00]`).
  `STATEMENTS.md` `## F2` lists Pre/Post beside the Rocq definitions and 8 deliberate differences.

## Verification tools
- ImageCheck 2026-11-27: `tools/check_image.sh [Gen.lean] [ELF]` (item 9): parses every
  `Seg`/`RoSeg` in `ZesuExec/Image/Gen.lean`, compares each word with the encoding
  `llvm-objdump -d --start-address --stop-address` prints at that address (flags missing, extra
  and non-4-byte encodings) and each rodata byte with `.rodata` dumped by `llvm-objcopy
  --dump-section`. Result: 10 text segments, 1138 words matched; 1 rodata segment, 32 bytes
  matched; 0 mismatches; exit 0. A copy of Gen.lean with one word and one byte changed gives
  5 mismatches (the word occurs in 4 segments), exit 1.
- `tools/verify.sh [--build]`: items 2 (plan regex plus `bv_decide` outside backticks, `unsafe`
  only in `Sym/Tactic.lean`), 3 (plan file list, missing globs skipped; 18 files), 9; item 1
  only with `--build`. Result: 2 PASS, 3 PASS, 9 PASS; exit 0. The only `bv_decide` text in
  `ZesuExec bfv` is backticked prose in `bfv/BinaryFv/RiscV/Model/SailEnumAux.lean`.

## S3 — Sail link (TrackT, TrackT2)
- 2026-11-27 TrackT: step 1 `tools/closure.py` (55 modules, no `BinaryFv.Zesu`, no
  `native_decide`). Step 2 done: all 55 `bfv` modules build against the specialised tree
  (`/home/cody/.cache/zesu-tmp/exec-spike/bin/bfvbuild` EXIT 0); removed-feature premises
  (PMP, MMIO, landing pad, interrupts, waiting-hart selector) deleted, docstrings say
  "exec-spike repair:"; every `bv_decide` replaced (all 1981 theorems: standard axioms only).
- Step 3: `ZesuExec/Sail/Rel.lean` (`Configured` 12 fields incl. I1–I6, `configuredB` +
  `configuredB_sound`, `xreg`, `xreg_type`, `Rel`, `toSail`) checks with `lake env lean`.
  Deviations: `Rel.regs` reads through `cast (xreg_type i).symm` (`RegisterType (xreg i)` does
  not reduce for open `i`); `Rel.code` covers only words inside `.text` (needed so RAM stores
  preserve it).
- Step 5 measurement: the generic per-form statement works (no per-word fallback needed):
  `dec_<form>` over symbolic operand fields, ~0.2 s each, whole file 7 s. 23/33 proved;
  open: `dec_jal`, branches ×5, stores ×4 — only the final immediate-reassembly equality
  (`ofNat a ++ ofNat b … = ofNat (…)`) remains; goals in `OPEN/S3/decode_immediates.goals.txt`.
- Not started: `decode_sound` assembly, `Forms/sim_*`, `Step.lean`, `Run.lean`, engine A.
- Next: fix the append finisher in `dec_tac` (`simp` leaves the `+++` goal before `apply
  BitVec.eq_of_toNat_eq`; the standalone `simp only [toNat_append_add, toNat_ofNat]; omega`
  proof works), then `lake build ZesuExec.Sail.Decode`.
- 2026-11-27 coordinator: F1 `f1_spec (A : AllocAssumptions zesuImage) L items : Spec zesuImage
  0x800cb40c 197 (Pre A L items) (Post A L items)` proved (`#guard_msgs` axioms: standard).
  Seven `sym_run`s (entry, after remap, after alloc ×2, after memcpy ×2, after free); paths
  29 / 112 / 123 / 137 / 197 steps; bound 197 equals the plan's expected value. Infeasible leaves
  closed from conditions (growth below 2^32 never overflows). Helper modules: `Fn/Assumed.lean`
  (`AllocAssumptions`: abstract `Heap L m`, `Priv L`, `alloc_spec` 53, `free_spec` 42),
  `Fn/Stage.lean` (`after_call_ov`, `run_reaches'`, memcpy byte lemmas, `returns_leaf`),
  `Fn/Preserve.lean` (`Reaches.preserve`: presence and bytes below RAM survive every run).
  `lake build ZesuExec.Fn.F1.Proof` (deps built): 5.0 s wall, 1.81 GB peak. Lines: Spec 95,
  Regions 28, Runs 29, Proof 1310. Non-vacuity example for F1 still to add.
- 2026-11-27 TrackT2: `dec_tac` finisher fixed (`rw [toNat_append_add]` instead of `simp only`:
  the generated `+++` carries instance widths `1+8+1+10` that `simp` does not unify); all 32
  `dec_<form>` proved; `decode_sound` (`ZesuExec/Sail/Decode.lean`) by splitting `decodeNat` with
  `ite_imp` (`split at h` exceeds simp's step limit on the 32-way `if` chain).
- TrackT2: rung = S1 as built (both patches; no fallback). `ZesuExec/Sail/Forms/`: `Common.lean`
  (`sim_of_exec`: generic lift of an `execute` run from `T s pc` through `runHartActiveControlFlow`
  + `tryStepGenericRetires`; `sim_wreg`, `sim_fall`, `sim_ctl`; `rX_rg_run`/`wX_rg_run` for any
  `Fin 32`; PMA matching of the three profile regions), `Mem.lean` (byte lists, `loadPma`,
  `storePma`, `sim_store_of_exec`), `RegWrite.lean` (16 forms), `Branch.lean` (5), `Jump.lean`
  (jal, jalr), `Load.lean` (5), `Store.lean` (4). All 32 `Instr` constructors proved: no `Proved`
  restriction. `Step.lean` `sail_step_sim`; `Run.lean` `SailReaches`, `sail_reaches` (service case
  builds `sailMemcpy m s`); `Axioms.lean` `#guard_msgs` `#print axioms` = [propext,
  Classical.choice, Quot.sound] for `decode_sound`, `sail_step_sim`, `sail_reaches`.
  Fresh build of all `ZesuExec.Sail.*` (bfv cached): 22.3 s wall, 95 s CPU, 2.3 GB peak; slowest
  modules Decode 8.1 s, Forms.Common 8.2 s, the rest ≤ 1.3 s each.
- TrackT2 engine A (`ZesuExec/Test/DifftestSail.lean`, wired into `Difftest.lean`): the model's
  root module `LeanRV64DExecutable` declares the Sail simulator's `main` (clash with
  `zesu-difftest`'s), so `bfv/.../Model/{State,Abi}.lean` now import its 13 submodules, and
  `ZesuExec/Sail/ModelInit.lean` copies `sail_model_init` verbatim (`InitCheck.modelInit_eq : modelInit
  = sail_model_init () := rfl`). Initial state: `modelInit`, then zero for the 14 registers the
  Lean backend leaves absent (its `initialize_registers` is empty; the C emulator zeroes undefined
  registers), then the model's `reset ()`. `init_model` is not used: the model's own
  `config_is_valid` rejects the S1 profile configuration (`check_mmu_config`: Svrsw60t59b, Ssccptr,
  Svade, Svadu still enabled with S/Sv39 disabled; `check_mem_layout` (`check_pma_regions`);
  `check_misc_extension_dependencies`) — an S1 configuration issue, not fixed here.
  `configuredB` holds on every initial state. Result: `zesu-difftest` prints `agree … sail = machine
  = unicorn … configuredB` on all 19 F1 and 26 F2 snapshots (45/45; ≤ 0.95 s, 82 MB each).
  `OPEN/S3/decode_immediates.goals.txt` removed (resolved).
- Gate S3: PASS. Next: S6 (`Fn/<Id>/Sail.lean`) uses `sail_reaches` unrestricted.
