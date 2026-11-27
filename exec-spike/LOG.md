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
- 2026-11-27 TrackT2: configuration fixed so the model's own `config_is_valid` holds (it failed
  `check_mmu_config`, `check_mem_layout`, `check_misc_extension_dependencies`). `01-profile-config.patch`
  now also disables Ssccptr, Sscofpmf, Sscounterenw, Sstc, Sstvala, Svade, Svadu, Svinval,
  Svrsw60t59b, Svnapot, Ssnpm, Svpbmt, Svvptc (S-mode/Sv* dependants); input and ROM regions are
  IOMemory, not cacheable, not coherent (the validator requires MainMemory to be read-write); RAM is
  not cacheable (Ziccif requires cacheable coherent main memory to be executable). Attempt 1 also
  disabled Ziccif: that turns the 4-byte fetch into two 2-byte fetches and broke
  `bfv/.../Platform/Fetch.lean`; reverted in attempt 2 in favour of the non-cacheable RAM.
  Regeneration (`nix build .#zesuSailRiscvLean`, 408 s) changed only `PlatformConfig.lean`
  (`hartSupports`), `ValidateConfig.lean` and the root `sail_model_init` (region attributes);
  regeneration check passes. Repairs: `Rel.zesuPma` takes the memory type; `ModelInit.lean`
  re-copied (`modelInit_eq` by `rfl` holds). All 55 `bfv` modules, `ZesuExec.Sail.*` (incl. the
  `#guard_msgs` axioms check) and `ZesuExec.Fn.F{0,1,2}.Sail` build; rebuild of model + S3 59 s
  wall. Engine A now runs `init_model ""` (validator + reset); the zero-init of the 14 registers the
  Lean backend leaves absent is still needed (without it `init_model` throws `Unreachable`).
  Three-way `zesu-difftest`: 45/45 agree, `configuredB` on every initial state. Rung unchanged:
  both patches. PROVENANCE sha256 of `01-profile-config.patch` updated; SPECIALISATION lists keys.

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
- 2026-11-27 ProveF2: F3 `rlp_decode.nextUint64` proved. `f3_spec : Spec zesuImage 0x800d6274 160
  Pre Post`, axioms standard (`#guard_msgs` in `Fn/F3/Proof.lean`). Uses `F2.f2_spec` for the
  decodeItem call (black box, `Reaches.preserve` + `Reaches.trans`). Three `sym_run`s, cuts =
  return point `0x800d62b8` and loop head `0x800d6318`: entry → call (1 leaf, 17 steps); return
  point (5 leaves: 3 error returns, empty payload, loop entry; ≤ 26 steps); loop (back edge 5,
  exit 20). The state after the call is not `S.override`: decodeItem writes its outcome inside
  F3's frame, which `after_call` forbids, so the return point and the loop head are fresh
  `entryState`s matched against machine-level invariants (`CallState`, `Inv`) through
  `F2.entry_match_vars`; the saved `ra, s0..s4` are `known` frame words (`var 33..38`). Bound
  17 + 75 + 13 + 7*5 + 20 = 160 (tight, payload of 8 bytes). Clean `lake build
  ZesuExec.Fn.F3.Proof` (F3 modules only): 7.35 s wall, 12.7 s user, peak RSS 1.76 GiB;
  `Proof.lean` 4.0 s. Lines: Spec 157, Regions 58, Proof 1057, Lemmas 148. Non-vacuity example
  (slice `{0xa0003000, 1}`, input `[0x00]`). `STATEMENTS.md` `## F3`: 9 deliberate differences.
  Next: F6 `decodeParentHeader`.
- 2026-11-27 ProveF2: F2/F3 switched to `Fn.zesu_rodata_range` after the image gained
  `0x80114fb8:80`, `0x801152b0:16`; `lake build ZesuExec.Fn.F3.Proof` passes (also rebuilds F2).
  F6 open, not started in Lean: findings and design in `OPEN/F6/plan.md` (all 20 call segments
  evaluate with the extended image; contract files and line ranges; F3-style fresh cut states per
  call because the callees write inside F6's frame; loops as in F3). Next: `Fn/F6/Spec.lean`
  (candidate walk over `F2.decode`, 80-byte result, scratch word, `headerFits` in `Pre`), then
  Regions/Proof per the plan; `lake build ZesuExec.Fn.F6.Proof`.

- 2026-11-27 F45: F4 `array_list.Aligned([32]u8,null).toOwnedSlice` and F5
  `array_list.Aligned(input.AccessListEntry,null).toOwnedSlice` proved.
  `f4_spec (A) L items : Spec zesuImage 0x800d677c 194 …`, `f5_spec … 0x800d6554 204 …`; axioms
  standard (`#guard_msgs`). Bounds equal the expected 194 / 204 (own 87 / 97 + remap 9 + alloc 53
  + memcpy 3 + free 42). One shared statement `ToOwned.Pre eb` / `ToOwned.Post eb empty`
  (`F4/Spec.lean`), shared regions (frame 96, result 24, header 24, allocator object 16) and
  generic lemmas (`F4/Lemmas.lean`: `Entry`, `Inv`, `alloc_step`, `free_step`, `copy_step`,
  `remap_step`, `success_post`, `oom_post`, `empty_post`); per function six `sym_run`s (entry 12
  leaves, after free(len 0) 4, after remap 3, after alloc 2, after memcpy 2, after free 1), `run`
  never returned `none` (no unaligned access). Infeasible leaves (ptr 0, length > capacity 0,
  length·eb overflow) closed from `Pre`. F5 = F4's proof text with `slli 5 + slli 3` / `mulhu 40`
  lemmas and its own addresses/budgets. Non-vacuity: `ToOwned.pre_satisfiable`
  (`F4/Witness.lean`), an `example` in each Proof. Clean build of the F4/F5 modules (deps
  built) `lake build ZesuExec.Fn.F4.Proof ZesuExec.Fn.F5.Proof`: 6.9 s wall, peak RSS 1.77 GB
  (Runs 3.2 s / 3.5 s, Lemmas 3.1 s, Proof 1.6 s / 1.7 s). Lines: F4 Spec 134, Regions 32,
  Runs 30, Lemmas 968, Witness 115, Proof 330; F5 Spec 26, Runs 31, Proof 338.
- 2026-11-27 F6: `f6_spec : Spec zesuImage 0x800d5cb8 2178 Pre Post`
  (`rlp_decode.decodeParentHeader`) proved; `#guard_msgs` axioms: `propext`, `Classical.choice`,
  `Quot.sound`. Callees `F2.f2_spec` (17 calls), `F3.f3_spec` (3), `memcpy_spec` (tail). Files
  `ZesuExec/Fn/F6/`: `Spec` 187 lines (`fieldWalk`/`walk` = the Rocq candidate walk over
  `F2.decode`, `headerFits`, `ResultOK`, `ErrorOK`, `Pre`, `Post`, non-vacuity `example`),
  `Regions` 90, `Runs` 35 (24 `sym_run`s: entry, 20 return points, 3 loop heads), `Lemmas` 1277
  (frame invariant `Fr`, cut environment `envC`, `Fr.of_leaf`, `dcall`/`ncall` = the callees as
  machine steps, outcome readers, `memcpy_exit`, `err_exit`, `succ_exit`, walk steps,
  `decode_fits`), `Proof` 1751 (one theorem per cut from `after18` back to `after0`, generic
  `loop_gen` for the three byte loops, `skip_req` for fields 0..7, `opt_skip` for 12..13,
  `f6_spec`). Bound 2178 = 423 own steps + 17 · 75 + 3 · 160 on the longest path (all 19 fields,
  8-byte integers). `lake build ZesuExec.Fn.F6.Proof` (deps built) passes; per module
  `lake env lean`: Spec 0.9 s, Regions 0.8 s, Runs 9.7 s, Lemmas 4.1 s, Proof 5.2 s; peak ≤ 1.8 GB.
  `OPEN/F6/plan.md` removed (resolved). `ZesuExec.lean` (root, not F6's) does not import F6 yet.

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

## S6

- S6: step 2. `vendor/evm-sail-lean` (already tracked since e9fd6eea) is byte-identical to
  `W/generated/evm-sail-lean` (EVM-Sail d0e4aabd, `diff -r` empty). Its modules already
  `import Sail`; `nix/evm-sail.nix` only installs lean-sail 79b4d085 as the `Sail` package, and
  the package's `sail-riscv-lean/Sail{,/*}.lean` is byte-identical to that lean-sail source
  (`diff -q` per file), so no import rewrite is needed. `lake build Evm.Lib.Rlp.Decoding`
  (`rlp_decode_item`; Sail lib cached, 14 Evm modules): 16.7 s wall, 21.2 s user, 1.88 GB peak.
  `lake build Evm.Lib.Ssz.StatelessInput` (`decode_parent_header_fields`, 21 more modules):
  21.0 s wall, 30.7 s user, 3.24 GB peak. No fallback.
- S6: step 3, F2. `ZesuExec/Compliance/`: `SailRun.lean` (`SailRegs`, `hostOf`, run lemmas for
  `pure`/`throw`/`<$>`/`>>=` through `StateT HostState (EStateM …)`), `RlpItem.lean`
  (`uint64_width_eval`, `ref_hdr_eval`, `decode_item_eval`: `rlp_decode_item` in closed form
  `sailItem`), `KnownBugs.lean` (the 13 Rocq classes), `F2.lean` (`f2_candidate_agrees`,
  `f2_compliance`, `f2_compliance_sail`; `#guard_msgs` axioms standard three for all three).
  Candidate reused: `Fn.F2.decode`/`result40`. `lake build ZesuExec.Compliance.F2` passes;
  per-module `lake env lean`: SailRun 0.8 s, RlpItem 1.3 s, KnownBugs 0.4 s, F2 1.4 s, ≤ 1.6 GB.
  Lines: 52 + 148 + 58 + 265.
- S6: F3 not started: `Fn/F3/Proof.lean` has no `f3_spec` yet (`OPEN/S6/README.md`). F6 not
  attempted. `ZesuExec/Axioms.lean` not edited (not mine): guards live in `Compliance/F2.lean`.
- S6: F3. `ZesuExec/Compliance/RlpUint.lean` (`uint_canonical_short` = `uintCanon`,
  `uint_canonical_long`, `decode_uint64_eval`); `RlpItem.lean`'s width lemmas now take any slice
  offset. `ZesuExec/Compliance/F3.lean`: Sail side `sailNext` = `rlp_decode_item` then
  `rlp_decode_uint64`, advance by the field's full length (what
  `_rec_decode_parent_header_fields` does at fields 17/18); `f3_candidate_agrees` with
  `rlpUintNonCanonical` the only excusing class (wrap impossible: header ≤ 9, payload ≤ 8),
  `f3_compliance`, `f3_compliance_sail` (via `sail_reaches`, as `f3_sail`); `#guard_msgs` axioms
  standard three. Witnesses `82 00 01` (bug) and `82 01 00` (agree). `lake build
  ZesuExec.Compliance.F2 ZesuExec.Compliance.F3` passes; per module: RlpItem 1.4 s, RlpUint 1.7 s,
  F3 1.5 s, ≤ 1.6 GB. Lines: RlpUint 145, F3 310.
- S6: F6. `Compliance/RlpItem.lean`/`RlpUint.lean` generalised to cursors at any offset
  (`SliceAt hs o xs`; `uintCanon` now on the item's byte list). `Compliance/ParentHeaderSail.lean`:
  `decode_word_eval`, `decode_u256_eval`, `run_readReg`, `fields_eval` (`_rec_decode_parent_header_fields`
  = `fieldsSpec`, register `k_execution_profile` holding `prof`), `node_cursor_eval`, `parent_eval`
  (`parentAction` = `sailParent`). `Compliance/ParentHeaderAgree.lean`: candidate trace `scan`, the
  ten parent-header trigger classes, `stepOK`, `walk_agree`, `parent_agree`. `Compliance/F6.lean`:
  `f6_candidate_agrees`, `f6_compliance`, `f6_compliance_sail`; `#guard_msgs` standard three.
  Witness `c0` (missing field). `lake build ZesuExec.Compliance.F2 ZesuExec.Compliance.F3
  ZesuExec.Compliance.F6` passes; per module ParentHeaderSail 1.8 s, ParentHeaderAgree 1.7 s,
  F6 1.6 s, ≤ 1.7 GB. Lines: 395 + 566 + 163.

## Programme plan (ZESU_VERIFICATION_PROGRAMME_PLAN.md)

- S0 (2026-11-27): head 7a9e7da8 (no upstream configured; pull skipped). `lake build` 247 jobs, cached, 1 s; `tools/verify.sh` items 2, 3, 9 PASS. Gate S0 passed.
- S1 (2026-11-27): `tools/zmap/` (`elfread.py`, `analyze.py`, `hints.py`, `ledger.py`, `__main__.py`;
  `vendor/dwarf.py`, `vendor/inventory.py` copied unchanged from zesislar `tools/stock_zisk/`).
  `python3 -m zmap build` (from `tools/`) runs in 12 s (analysis 2 s, DWARF 8 s) and writes
  `map/static.json` (12.8 MB, compact JSON; addresses are integers). Census reproduced: 524 functions,
  278,372 instructions, 39,926 blocks; 504 indirect call sites (493 table-heuristic, 11 unresolved),
  193 other indirect jumps (18 resolved jump tables, 175 unresolved: 174 in
  `interpreter.runDispatch__anon_13271`, whose table base is built in the previous block, so the
  block-local rule does not apply; 1 in `memset`). Reachable from `_start` by direct and tail calls
  alone: 195 functions, 202,867 instructions (= plan census); with table candidates `target` = 206
  functions, 203,606 instructions; `maybe` 14; `other` 304. 4 function-pointer tables in `.rodata`
  (4, 4, 17, 4 slots). Hints: `code_dwarf` accepted the object (388 anchors), 32,591 of 39,926 blocks
  have a source hint, 26,503 an inlined-function name; `hints_error` null.
  Heuristic tests matched without changes: `txAccessList`'s three indirect calls (`0x8000033c`,
  `0x800003d0`, `0x80000428`, each `ld` from the allocator vtable at slots 2, 0, 3) have candidates
  `alt_fl_alloc.remap`/`alloc`/`free` among 4 each; `decodeTxFields`'s `jalr zero,0(a0)` at
  `0x80000584` loads from `0x80110050 + ((a2 & 0xff) << 3)` (auipc/addi base), 5 entries inside the
  function (`0x80000588 0x800005dc 0x8000069c 0x8000075c 0x8000081c`), the 6th word is outside.
  Two deviations from the literal S1 text, both recorded in the code: (1) `irreducible` is an edge to
  an earlier address that is not a back edge *and* lies on a cycle of the graph without back edges;
  the literal rule flagged 266 functions for layout jumps to lower addresses (e.g. `txAccessList`
  `0x80000368 -> 0x800002ec`); now 7 functions. (2) Calls to functions that never return (greatest
  fixpoint over the call graph; 12 functions, the Rust panic/`handle_error` family and `_start`) have
  no fall-through edge and their return sites are not cut points (`calls[].noreturn: true`); the
  fall-through after `panic_nounwind_fmt` in `rem_long` had made a false cycle. Path counts treat a
  resolved jump table as a leaf end (the executor's `jumpInd`). Extra fields: `jump_tables`,
  `noreturn` per function, `hints` (helper evidence) at top level, `tables[].kind` `fnptr`|`jump`.
  `python3 -m unittest discover -s tools/zmap/tests`: 15 tests OK (2.3 s; structural counts, loop
  heads `0x800000c4`/`0x8000018c`, `ensureTotalCapacity` 107/no loop/4 calls, `decodeItem` 2 loop heads,
  `_start` in target, heuristics, committed `static.json` agrees with a fresh build). Ledger
  `map/ledger.jsonl` created (S0 and S1 infra items). Gate S1 passed.
- S2 (2026-11-27): `ZesuExec/Vc/` `Types` (`Callee`, `Cut`, `Plan`, `Callee.memcpy` from
  `memcpy_spec`), `Goals` (`CutOK`, `ExitGoal`, `LeafGoal`), `Sound` (`vc_sound`, strong induction on
  the budget via `run_sound`, `RunsIn.trans`, callee `spec`; `AllL`/`idxQ`/`forall_mem_of_idx`),
  `Assemble` (`zesuExt`, `zesu_plan`, `zesu_auto`, `zesu_assemble`, placeholder tactics
  `leaf_auto`/`cut_auto` that `fail` until S4, extendable by `macro_rules`), `Legacy` (F0-F6 entries
  and theorem names), `Status` + `lean_exe «zesu-status»`. `Test/Vc.lean`: toy
  `li a0,3; L: addi; bnez a0,L; ret`, 2 cuts / 3 leaves; `zesu_auto` closes 0 of 5; all hand-proved
  gives `Toy.reach` (axioms standard three, guarded; used to derive a `Spec`); `Toy2` without leaf
  `80000004_1` gives `Toy2.Open` with exactly that field (`#guard_msgs` on `#print`), `reach_from`, no
  `reach`; legacy names checked to exist. `Axioms.lean`: `vc_sound` guarded, standard three.
  `tools/verify.sh` unsafe allowlist now also `ZesuExec/Vc/`. Deviations from the plan text:
  `ExitOk` for `.call` gives `pc = target`, so the call case of `LeafGoal` needs `m'.pc.toNat = k.entry`
  proved from it (kept as stated); `Plan.leaves`/`cuts` are looked up by evaluating the plan with
  compiled code (`evalExpr`), so a plan must be computable and its cut pcs distinct;
  fixed statements `F.cut_<pc> : CutOK F.plan F.plan.cuts[i]!`,
  `F.leaf_<pc>_<j> : LeafGoal F.plan F.plan.cuts[i]! (F.plan.leaves <pc>)[j]!` (checked by `isDefEq`
  before use); `hruns` is re-proved by kernel `Eq.refl` per cut (each run evaluated once more by the
  kernel, as `sym_run` does), `hpos` by kernel `decide`; `zesu-status` reads the extension entries
  of the imported `ZesuExec` environment (no `loadExts`), skips plans under `ZesuExec.Test`, emits
  `assembled`, integer `entry`/`target` (`target_sym` for symbolic exits), `steps` relative to the cut,
  and `names`; for plan functions `<f>_spec` etc. are looked up as `<fn lowercased>_spec` in `F`'s
  namespace or its parent. `lake build` 253 jobs OK; `tools/verify.sh` 2, 3, 9 PASS; `lake exe
  zesu-status | jq .` valid, F0-F6 `legacy: true` with spec/sail true, compliance true for F2, F3, F6.
  No elaborator fallback needed (no `gen-vc`). Gate S2 passed.
- S3 (2026-11-27): `tools/zmap/` `merge.py` (states by the plan's first-applies rule, leaf-to-CFG join by
  cut pc and exit target, ledger totals per function and kind with status ids such as `F1`/`TX`
  mapped to `f_<entry>`, `trust` list), `workqueue.py` (queue order of the plan; card and next action),
  commands `merge`, `queue`, `show`, `next`, `site`; `Makefile` target `map` (static rebuilt only when
  the ELF hash differs from `static.json`'s; status from `lake exe zesu-status` (S2, a0b9205e) into
  `map/status.json`; merge; queue; site). `map/reviews.json`: F1-F6 transcribed/unreviewed, F0
  draft/unreviewed (sources from STATEMENTS.md), assumed `alt_fl_alloc.alloc`/`free`, service `memcpy`.
  Page `W/tools/binary-regions-ui/map.html` (link added in `index.html`'s header): tabs Overview
  (treemap by state; area instructions / log10 leaves_estimate / open items; set filter; search),
  Function (CFG at precomputed x,y; cuts, loop heads, joins, call kinds, blocker sites, back and
  table edges, leaf arcs coloured auto/manual/open; card, leaves, source hints), Calls, Queue, Cost,
  Trust; data from `map-data.js` (`window.ZMAP`, `window.ZQUEUE`), opens from file://; opened from
  `tools/binary-regions-ui/` it loads `../../exec-spike/map/site/map-data.js`. `map/site/` is
  generated (gitignored); `map.json` (13 MB), `status.json`, `queue.json`, `QUEUE.md` committed.
  `tools/verify.sh` gains "map freshness": fails if `map.json` is missing or older than `static.json`
  or `status.json`, or `status.json` differs from the current `lake exe zesu-status` output.
  Gate: `make -C tools/zmap map` OK (3 s with lake cached); `tools/verify.sh` 2, 3, 9, map freshness
  PASS; headless Chromium on `file://…/map/site/map.html` (dump-dom and screenshots
  `/home/cody/.cache/zesu-tmp/zmap/overview.png`, `tx.png`): header text "524 functions ·
  closed+compliance 3 · closed+sail 4 · assumed 3 · blocked 318 · ready 18 · waiting 46 · out 132"
  (F2, F3, F6 closed+compliance; F0, F1, F4, F5 closed+sail); all six tabs render without page
  errors; `txAccessList` shows 53 blocks, 2 loop heads, 15 cuts, 11 joins. `zmap show f_800cb40c`
  prints F1's card (state closed+sail, legacy, f1_spec/f1_sail). `zmap next` head: 18 `ready`
  functions (bottom-up), then 44 blocker classes by target-set instructions. Note: `blocked` precedes
  `out` in the rule order, so 318 includes functions outside the target set. Unit tests 18 OK
  (merge/queue on the legacy fixture `tests/fixtures/status_legacy.json`, tests only). Gate S3 passed.
- S6-prep (2026-11-27, TX `rlp_decode.txAccessList`): `ZesuExec/Fn/TX/Spec.lean` transcribes
  `TxAccessListContract.v` with the reference decoder of `AccessListCandidate.v` (over `F2.decode`)
  and the domain of `TxAccessListMeaning.v`: `Params` (σ: input bytes, allocator live list), `Pre A
  g`, `OutcomeImage`, `Post A g`; the Sail half of the meaning is left to compliance (as F2).
  `decide` checks the decoder on `c0`, `80`, one entry with one key, a 19-byte address;
  `pre_nonvacuous` (input `c0`). Checked with `lake env lean ZesuExec/Fn/TX/Spec.lean` (clean, 1.5 s);
  `lake build ZesuExec.Fn.TX.Spec` not run: `ZesuExec/Sym/Tactic.lean` is modified (S4, uncommitted)
  and the build would rebuild it and everything after it under S4's build. Not imported in
  `ZesuExec.lean`. `STATEMENTS.md` section TX (8 differences), `map/reviews.json` TX
  transcribed/unreviewed, ledger `contract` item. `OPEN/TX/CUTS.md`: the 15 map cuts with segment
  exits and longest paths, regions per cut from the segment's own loads/stores, assertion content from
  the annotation rows (`loop-c4`, `loop-18c`, `join-*`, `return-d8`, `dead-3e0/344/2ec`), budgets
  (`32·len + 1130` at entry, `32·r + 1006` at `0xc4`, `10·kr + 1464 + 32·R` at `0x18c`, from the callee
  bounds and the map's longest segment paths), the image change S6 needs (only TX's 323 words; no new
  rodata). Finding: TX loads the address and key payloads from the input with `ld`/`lw` at
  `+0x130..+0x138` and `+0x1c4..+0x1d0` (unaligned for real inputs: zesislar's `one_entry_1_key` has
  the address at offset 4) and stores keys with `sd` into a keys buffer allocated with alignment 1
  (`+0x230..+0x23c`); the machine's loads/stores are aligned, so TX's runs need S5 probe 3 before S6
  step 5. Compliance check: `vendor/evm-sail-lean/Evm/Lib/Rlp/Codecs/Transactions.lean` has
  `decode_access_list` (l.180) and its entries/keys walkers, so no `compliance-spec-missing`.
  `tools/snap.py --fn TX` added: 16/16 zesislar inputs `returned` under Unicorn (real allocator);
  `zesu-difftest --fn TX` needs `Gen.TX` (image change), not wired.
- S4 (2026-11-27): `Sym/Pretty.lean` (ABI-name printers, depth-6 truncation, `Leaf.pp` against
  the cut state); `sym_run` log lines now carry the exit target and first condition. `Vc/SimpAttr`
  (`zesu_simp`), `Vc/Regions` (`Layout`, `Layout.apart`/`wf`/`inWritable_iff`/`sameOutside_frame`,
  `region_tac`), `Vc/Tactics` (`leaf_intro`, `cut_intro`, `sym_show`, `match_regs`, `leaf_norm`,
  `leaf_infeasible`, `exit_intro`, `field_auto`, `leaf_auto`/`cut_auto` as `macro_rules`).
  Deviations: `sym_show` lives in `Vc/Tactics.lean` (needs `unsafe` evaluation; allowlist kept);
  `zesu_auto` now rejects proofs containing `sorryAx` and runs tactics without error recovery (found
  while testing: a recovered error was recorded as `auto`). `Test/Auto.lean`: toy 5/5 auto,
  `Toy3.reach` axioms guarded; false leaf goals (reachable back edge asserted infeasible; wrong
  postcondition `Toy5`) fail under `fail_if_success`, `Toy5.Open` has exactly the false leaf;
  `region_tac` positive and wrong-layout tests; `sym_show` output guarded.
  `leaf_infeasible` at existing call sites: replaced where it closes the same goal — F3 `f3_conds`
  3 of 5 closing sites (kept: `Proof.lean` the `exfalso; f3_conds` at the second leaf of the
  `cases b` branch and the last `all_goals`; the 3 normalising uses stay); F6 `conds; exfalso; simp`
  8 of 14 closing sites (kept: 4 single-leaf sites, the `| none =>` site, one `all_goals try`);
  kept entirely: `f1_overflow` (2 sites; needs `g_or'`/`grown_srl59` rewriting of `|||` terms),
  `f4_infeasible`, `f5_infeasible` (derive facts inside the macro), and all `conds`/`iconds`
  normalising uses.
- S4 benchmark F2: `Fn/F2/Vc.lean` (the old `Proof.lean` renamed and converted: `loop_step` →
  `loop_leaves`, `f2_spec` body → `entry_leaves`, `loop_reaches` deleted), `Fn/F2/Proof.lean` derives
  `f2_spec` from `F2.reach` (22 lines). 3 cuts, 17 leaves, 20 items: auto 0, manual 20, open 0.
  Hand lines before 736 (Proof.lean), after 848 + 22 = 870 (+17 one-line leaf theorems + plan/cut
  definitions). `f2_spec`, `f2_sail`, F2 compliance unchanged and building.
- S4 benchmark F1 (fallback taken: conditional): `Fn/F1/Vc.lean` (561 lines): 5 cuts (entry, after
  remap/alloc/memcpy/free), 16 leaves, 21 items: auto 2 (two overflow leaves), manual 11 (entry and
  after-remap cut lemmas, entry leaves 0-4 and 7, after-remap leaves 0-2; `alloc_call` splits
  `alloc_step` for `ExitGoal`), open 8: the cut lemmas of the three join cuts and the 5 leaves of
  their runs. Join states are `genS` of the spike's two path states; their `CutOK` needs matching a
  path state against its `genS` (S5 probe 1), attempted twice in design, not proved. `F1.reach_from`
  assembles (axioms guarded); `f1_spec` keeps its spike proof; `Fn/F1/Runs.lean` and the old bodies
  are not deleted. Hand lines before 1309 + 29; after: unchanged + 561 conditional.
  `zesu-status`: F1, F2 now plan rows (legacy rows dropped for them, legacy theorem names kept).
  `lake build` 260 jobs OK; `tools/verify.sh` items 2, 3, 9 PASS; "map freshness" FAILS until
  `make -C tools/zmap map` is rerun (S3's step; `zesu-status` output changed). Gate S4: automation
  items done and tested; F2 converted; F1 conditional (fallback).
- S5 probe 3 (2026-11-27, branch `probe-unaligned`, worktree `~/.cache/zesu-tmp/zmap/wt-unaligned`):
  unaligned accesses. `Machine.load`/`Machine.store` drop natural alignment (the range must lie in
  one permitted interval, bytes present); `Sym`'s `cstCheck`, rodata and indexed loads drop their
  alignment checks (`cstCheck_spec`, `load_cst`, `load_idx` lose the alignment hypotheses);
  `run_sound` re-proved with its statement unchanged. Sail link: new
  `ZesuExec/Sail/Forms/Misaligned.lean` (no sorry): the profile has
  `plat_misaligned_access.load_store = none`, so `vmem_read_addr`/`vmem_write_addr` split a
  misaligned `2^k`-byte access into `2^k / 2^c` aligned pieces (`c` = trailing zeros of the
  address); `split_misaligned_run`, the loop lemmas `go_runs`/`go_runs_st` over
  `untilFuelM.go`, `vmem_read_addr_split_run` (the pieces assemble to the little-endian value),
  `vmem_read_any_run`, `vmem_write_addr_split_run` (memory after the pieces = the bytes of the
  value), `execute_STORE_misaligned_run`, `sim_store_of_exec'`. `sim_ld`, `sim_lw`, `sim_lhu`
  and `sim_sd`, `sim_sw`, `sim_sh` now cover both cases (aligned path unchanged); byte forms are
  always aligned. Stores to alignment-1 heap blocks (TX's keys buffer) are ordinary misaligned
  stores here. Gate: `lake build` 254 jobs OK, F0-F6 statements unchanged (proof edits only in
  `Fn/F1/Proof`, `F3/Lemmas`, `F4/Lemmas`, `F6/Lemmas`, `Preserve`: alignment arguments to
  `load_cst` dropped, unused alignment hypotheses kept as `_ha`), `Sym/Tactic.lean` untouched;
  `tools/verify.sh` all PASS; `zesu-difftest` 45/45 F1/F2 snapshots agree and, with TX in the
  image, 16/16 TX snapshots agree three ways (e.g. `one_entry_1_key`: the address payload `ld` at
  input offset 4). Test `odd_halfword_refused` replaced by `odd_halfword_accepted` and
  `halfword_past_end_refused`. Gate passed; no fallback (no `stepU`, no trust item). Image:
  `tools/gen_image.{sh,py}` add `rlp_decode.txAccessList` as `Gen.TX` (323 words; Expected table
  1249 -> 1572), `zesu-difftest` knows `--fn TX`, snapshots in `test/snapshots/TX/` (16).
  `STATEMENTS.md` notes the new meaning of `Machine.load`/`store`. 25 min.
- S7-prep (2026-11-27, branch `probe-unaligned`): DTF `rlp_decode.decodeTxFields`.
  `OPEN/DTF/BLOCKERS.md`: jump table `0x80000584` = `0x80110050 + 8·(tx_type & 0xff)`, five targets
  (types 0-4: `0x80000588 0x8000081c 0x8000069c 0x8000075c 0x800005dc`; the sixth word points
  outside), **no range check** — both callers (`decodeSingleTx`, `decodeTxItem`) reject
  `tx_type > 4`, so `Pre` carries `tx_type ≤ 4`; the 11 indirect calls are allocator vtable slots
  (alloc ×7 slot 0, remap ×2 slot 2, free ×2 slot 3); 24 misaligned sites (`to` and blob-hash copies
  from RLP payloads, odd result offsets `0x21 0xa9 0x109 0x111 0x119`), supported since probe 3.
  `ZesuExec/Fn/DTF/Spec.lean` (draft/unreviewed): reference decoder over `F2.decode` and
  `TX.candidate` (`StateT (List Byte) Option` parsers per field helper), `Pre`/`Post` with the
  `input.Transaction` layout from the debug object; `decide` on four inputs; `lake build
  ZesuExec.Fn.DTF.Spec` OK; open points in `STATEMENTS.md` § DTF (error disjunct unrestricted,
  unwritten bytes, `@intCast` truncation unchecked, heap shape, Sail agreement).
  `OPEN/DTF/CALLEES.md`: the only non-closed callee is TX (4 calls); all others closed or assumed.
  Image: `rlp_decode.decodeTxFields` added as `Gen.DTF` (2,825 words) with rodata
  `0x80110050:40` (jump table) and `0x8010fe00:8` (the `/144` multiplier); `zesu-difftest`
  knows `--fn DTF`. `Test/Decode`'s single `decide` over a per-entry `word?` lookup became
  quadratic (368 s, kernel recursion limit at 4,397 entries): replaced by two linear checks
  (`table_pairs`: the table's `(pc, word)` pairs equal the image's segments in order; every word
  decodes to its mnemonic), 3.4 s. No DTF snapshots: zesislar's runner has no `decodeTxFields`
  profile or inputs. After the image change: `lake build` OK, difftest F1 19 + F2 26 + TX 16
  agree, `tools/verify.sh` all PASS. 18 min (contract 7).
- S7-prep (2026-11-27, branch `probe-unaligned`): DTF snapshots, join cuts, legacy `v`.
  `tools/snap.py` gains `--fn DTF` with its own profile `dtf_profile` (zesislar's runner has none):
  `a0` result (0x128 bytes), `a1` allocator object, `a2` `tx_type`, `a3`/`a4` payload. Inputs
  `tools/snap_inputs/decodeTxFields.json` (19, hand-encoded RLP payloads; no EVM test vectors under
  `vendor/`): legacy (EIP-155, contract creation with data, `v_raw = 2^70+36`, `v_raw = 5`),
  2930 with one access-list entry and two keys, 1559, 4844 with two blob hashes, 7702 with two
  authorizations, a 9-byte nonce (clamped), a non-canonical `00 05` nonce (accepted), and nine
  errors (truncated, 19-byte `to`, 9-byte gas limit, 33-byte value, 19-byte access-list address,
  31-byte blob hash, byte-string authorization, list chain id, empty payload). All 19 `returned`
  under Unicorn with the expected kind; `zesu-difftest --fn DTF`: **19/19 agree** (sail = machine =
  unicorn), no disagreement. The draft `DTF.decode` (`#eval` on the same 19 payloads) gives the
  snapshots' outcome kind and the compared fields (chain id, nonce, `v`, `to` present, data length,
  access-list, blob-hash and authorization counts) on every input. zmap: `build --join-cuts` (off by
  default) adds every `join_cut_candidates` pc as a cut with `why: "join"` and recounts paths
  (`txAccessList` 15 → 21 cuts, 53 → 50 leaves; DTF 138 → 153 cuts, 527 → 478; F1 5 → 9, 20 → 18);
  `static.json` records `join_cuts`; test `JoinCuts`; 19 tests OK. Legacy `v`
  (`STATEMENTS.md` § DTF open point 3) settled against the disassembly `0x80002a88..0x80002b28`:
  `chain_id = ((v_raw-35)>>1) mod 2^64`, `v = (v_raw-35) & 1`, as `legacyV`; snapshot
  `legacy_v_huge` gives `chain_id 0`, `v 1`. 5 min.
- S6 TX steps 3-5 checkpoint (S1StaticMap, worktree `wt-unaligned`): `Fn/TX/Regions.lean` (regions,
  17 cut states), `Fn/TX/Runs.lean` (17 `sym_run`, 51 leaves, 8 s total; map estimate 53),
  `Fn/TX/Cuts.lean` (walk transcriptions `OuterWalked`/`KeysWalked`, one assertion per cut,
  call-site predicates, 8 callees as `famCallee` families, budgets, `vcPlan`; `zesu_plan TX`,
  `zesu_auto TX`: 5 of 68 items closed — leaves `25c_7`, `25c_8`, `340_4..6`). Cut rule: the 15
  default cuts plus store-site cuts `0x230`/`0x460` (executor stores only at constant region
  offsets; recorded in `OPEN/TX/CUTS.md`). Assumption interface: `AllocAssumptions.Arena` +
  `arena_split` (approved by Main; evidence and model sketch in `STATEMENTS.md`); while checking
  it found that `heap_frame` + `live_ok` force live blocks to be empty (reported; Main: option 1,
  P1Joins). Leaves: 63 open. ~45 min.
- S5-p1 (2026-11-27): join cuts. New `ZesuExec/Sym/Join.lean`: `generalise F Ss K` (F1's
  `genS`/`entryOnly`, generalised and made sound), `genEnv`, `Sym.eval_clean`,
  `Match.generalise_to` (target-`Env` form: any `env'` that agrees with `env` below `K`, on the
  regions and on clean initial bytes, reads `var (F + i)` and dirty initial bytes off the machine)
  and `Match.generalise` (plan form), axioms guarded. Deviations from the plan statement: extra
  parameter `K` (kept terms mention variables below `K`, default `F`; F1 uses 32 = entry
  variables); a register/write/known fact is kept only if every state agrees and it is *clean*
  (no `init`/`initx` of a region some state writes; a write must also be the newest write of each
  of its bytes in every state, else a dropped newer write could shadow it; the old `genS`
  membership test did not check this); dirty regions' initial bytes are re-read from the machine,
  so the conclusion is `Env.Ext env env' F 0 ∧ env'.regions = env.regions ∧ Match ∧ WF`, with
  hypothesis `∀ S' ∈ Ss, S'.regions = S.regions`. `cut_auto` is not extended: F1's three join cut
  lemmas are 3 lines each through `join_cut` (F1-specific: frame dirty, header/allocator object
  clean, `envJ`). F1 (`Fn/F1/Vc.lean`): cuts after `alloc` (join of 2), `memcpy` (1 incoming),
  `free` (join of 2: capacity 0 skips `free`) have state `generalise F [incoming] 32`; assertions
  are machine facts plus `MatchIn` (some incoming state matches under an entry-consistent `Env`).
  Runs: spike `run0, run1, run2a, run2b, run3a, run3b, run4b` (7) -> `runE, runR, runJ2, runJ3,
  runJ4` (5); run2a/2b collapse to `runJ2`, run3a/3b to `runJ3`. `freeC` now names its list
  (`freeL`: entry list + new buffer). `F1.reach` assembles: 5 cuts, 16 leaves, 21 items: auto 2,
  manual 19 (5 cut lemmas, 14 leaves), open 0 (was 8). `Fn/F1/Proof.lean` derives `f1_spec` from
  `F1.reach` (statement unchanged); `Fn/F1/Runs.lean` and the stage bodies (`stage0`-`stage4b`,
  `alloc_step`) deleted; shared lemmas kept in `Fn/F1/Lemmas.lean` (`copy_step` -> `copy_call`
  split for `ExitGoal`, `EnvOk.mem2`, `EnvOk.regions`). `Test/Budget.lean` restated on the new
  runs (same path costs 29/112/123/137/197). Hand lines before 1308 (Proof) + 29 (Runs) + 561
  (conditional Vc) = 1898; after 750 (Lemmas) + 933 (Vc) + 24 (Proof) = 1707, plus 222 generic
  (`Sym/Join.lean`). `lake build` 263 jobs OK (F3-F6, Sail, compliance build); `tools/verify.sh`
  all PASS after `make -C tools/zmap map`; `zmap show f_800cb40c`: closed+sail, reach=yes,
  leaves auto 2 / manual 14 / open 0. Gate S5.1 passed; no fallback; `join_cut_candidates` may be
  turned on. ~18 min.
- S5-fix (2026-11-27): soundness finding by S1StaticMap. `AllocAssumptions.heap_frame` (any `m'`
  agreeing with `m` on `Priv L` keeps `Heap L`) with `live_ok` (live blocks present) and
  `priv_not_live` proved every live block empty (`heap_blocks_empty`: drop a live block's bytes,
  the heap survives, presence fails), so `alloc`'s non-null branch was unsatisfiable and F1/F4/F5
  were vacuous for any real allocator. Fix: `heap_frame` also requires
  `∀ b ∈ L, Present m' b.1 b.2`; new `AllocAssumptions.heap_frame'` takes `Preserved m m'`
  instead (every run keeps present bytes present). All 18 uses re-proved (F1 Lemmas/Vc, F4
  Lemmas: `heap_frame'` with the step's `Preserved`; F1/TX `pre_nonvacuous`, F4 witness: empty
  list). New `Test/AllocModel.lean`: an `AllocAssumptions zesuImage` instance whose heap has one
  live 1-byte block (`heap_nonempty`), so `heap_blocks_empty` no longer goes through. `f*_spec`,
  `*_sail`, `*_compliance` statements textually unchanged; STATEMENTS.md updated. Built in a clean
  worktree of HEAD plus the fix: `lake build` 263 jobs OK (P2's uncommitted `Fn/F3/Proof.lean`
  edit does not build in the shared tree and is not part of this commit).
- S6 TX merge (S1StaticMap): merged exec-spike `b5baa03f` into `probe-unaligned` (LOG/ledger kept
  both sides; generated map files regenerated). `Test/AllocModel.lean`: `Arena := True`,
  `arena_split` by excluded middle (the model stays non-vacuous). `zmap`: join cuts are the
  default (`--no-join-cuts` turns them off; `analyze.build(join_cuts=True)`; `make map` rebuilds a
  static map built without them); `static.json` rebuilt (`txAccessList` 21 cuts, 50 leaves);
  tests updated (`JoinCuts`, 19 OK). TX keeps its 17-cut plan, no join cuts (reasons in
  `OPEN/TX/CUTS.md`). Full `lake build` OK.
- S5-p1b (2026-11-27): `cut_auto` closes join cuts. `Sym/Join.lean`: `joinEnv K F Ss E` (the
  join cut's `Env` over a fixed `E`), `Agrees`, `JoinIn K Ss E m` (some incoming state matches
  `m` under an `Env` agreeing with `E`), `JoinIn.ok` (cut lemma, via `Match.generalise_to`).
  `Vc/Tactics.lean`: tactic `conj_assumption` (closes a goal with a conjunct of a hypothesis,
  definitions unfolded, reducible comparison) and a second `cut_auto` rule: `cut_intro`, then
  `JoinIn.ok` for `Env.WF`/`Match`, `conj_assumption` for `JoinIn`, `RodataLoaded` and the pc.
  F1: join `Env`s are `envJ F Ss = joinEnv 32 F Ss (env0 ·.m)`; `AJ2`-`AJ4` end with
  `RodataLoaded ∧ JoinIn` (producing leaves add `hinv.ro E` and `EnvOk.agrees`); the three hand
  cut lemmas and `join_cut` deleted. `zesu_auto F1`: 21 items, auto 2 -> 5 (cut lemmas 3 of 5
  auto), manual 19 -> 16, open 0. `Fn/F1/Vc.lean` 933 -> 903 lines (`Sym/Join.lean` 222 -> 265).
  Built in a clean worktree of HEAD plus these files: `lake build` 263 jobs OK, `tools/verify.sh`
  all PASS after `make -C tools/zmap map`.
- S5-p2 (2026-11-27): callee summaries in the executor. `Sym/Summary.lean`: `Summary`
  (`bound`, `clobbers`, `result : Option Sym`, `writes : List (arg reg × bytes)`); `runWith img
  sums cuts F0 fuel pc S : Option (List LeafW)` continues through a direct call whose target has a
  summary: the state at the callee entry is recorded in a `CallRec`; after the return the
  clobbered registers are `var (F + i)` (`F = F0 + 32 * calls so far`), `a0` is the result if
  given, the written byte ranges (resolved from the argument registers to constant region places)
  become fresh initial memory, `steps += bound`. `LeafW` = `Leaf` + `calls` + written ranges, a
  separate structure, so `Leaf`, `run` and `run_sound` are untouched. `runWith_sound` (guarded):
  given per recorded call a `CallHyp` (from any machine matching the call state, reached from the
  start, the callee returns within `bound` to a `CallPost`: return pc, kept registers, result,
  bytes outside the written ranges, written bytes present, footprint in the caller's writable
  regions or a caller-chosen `X`, rodata kept; plus a caller-chosen fact `Qc`), some leaf's
  conditions hold under an `env'` that `Env.Agree`s with the start `Env` below `F0` and outside
  the written ranges; if its obligations hold, every call on its path has a `CallFact` (the
  machines at its entry and return with `Qc`, and `env'` reading the return through
  `Env.havoc`) and the machine runs to the leaf within its step count (an upper bound now),
  memory changed only in the writable regions and `X`. Obligations before a call need no
  pre-call discharge: a failing one is met by following the same `Env` to a leaf (`goW_follow`).
  Checked restrictions (`CallRec.okB`, else `runWith` = `none`): the call state, path conditions
  and result mention only variables below `F` and no initial byte of a written range; no symbolic
  write or known fact overlaps a written range. `runWith_reaches` is the `run_reaches` form.
  `Vc/RunWith.lean`: `sym_runw` (as `sym_run`, logs the calls per leaf).
  F3 (`decodeItem` inside `nextUint64`): `f3_spec` (statement unchanged) now runs
  `runW := runWith … [loopHead] 64 100 entry S0` with `decodeItemSum = ⟨75, abiClobbers, none,
  [(a0, 40)]⟩`: 5 leaves (3 error returns, empty payload, loop entry; 105–118 steps incl. 75).
  The return-site cut `0x800d62b8` is gone with its run `runR`, state `SR`, re-entry lemma
  `after_call` and `leafE`; `CallHyp` is discharged by `f2_spec` + the existing `call_state`
  (now from `FootW`), `Qc = CallState m m₂`; the leaves read decodeItem's outcome through
  `CallFact` (`envW` → `RetEnv`, shared with the loop's `envR` via `CallState.retEnv`). Runs
  3 → 2 (`runW`, `runL`), leaves 1 + 5 + 2 → 5 + 2, cut points 2 → 1 (loop head). Hand lines
  `Fn/F3/Proof.lean` 1056 → 1333 (+277: `CallHyp` footprint/frame arithmetic, `envW`,
  `CallState.of_leafW`, `leavesW` re-proved over the new `Env`); generic 763 (`Sym/Summary.lean`)
  + 54 (`Vc/RunWith.lean`). F1/`remap` half: `Fn/F0/Summary.lean` (`F0.summary = ⟨9, abiClobbers,
  some (lit 0), []⟩`, `F0.callPost`: `F0.Post` → `CallPost`); F1 not converted (owned by P1Joins,
  and F1 is a `Vc.Plan`: `vc_sound` runs `run`). The F1 change: (1) Vc: `Plan` gains
  `sums`/`F0`, `leaves` become `List LeafW`, `vc_sound` uses `runWith_sound`; `LeafGoal` takes
  `∀ env', Env.Agree (c.env g m) env' F0 l.wr` and `∀ call ∈ l.calls, CallFact …` as hypotheses;
  a new goal `CallGoal P c call` (= `CallHyp` under `c.A`) named `F.call_<pc>_<i>`; (2)
  `Fn/F1/Vc.lean`: `sums t := if t = F0.entry then some F0.summary else none`; cut `cR`
  (`0x800cb4f8`, `S1`, `AR`, `envR`, budget 148) and `remapC`/`callee 0x800cb4f8` deleted, runs
  `runE` + `runR` → one `runWith` from the entry (checked: 10 leaves = legacy 8 + 3 − the remap
  call leaf; 3 of them carry the remap call); `leaf_800cb40c_4`'s body becomes the call goal
  (`F0.Pre` from `hinv1.ro E`, `E.calleeStack`, `RetAligned` as now; `f0_spec`; `F0.callPost`
  with `E.calleeApart` for the frame and `X` = remap's 16 bytes); `runR`'s three leaf theorems
  become entry leaves with `var (64 + i)` for `var (100 + i)` (callee-saved terms are kept, so
  `envR`'s `vars 120/122` facts become entry facts). `alloc` stays a cut: its new block is a
  region that does not exist before the call, and a summary adds no region (recorded
  restriction: summaries for non-allocating callees only; `alloc`'s return site keeps its cut;
  `free` and `memcpy` not attempted, and `memcpy`'s write length is a register, not a constant
  range). `lake build` OK (all targets), `tools/verify.sh` all PASS after
  `make -C tools/zmap map`. Gate S5.2 passed for F3/decodeItem; fallback for alloc as above.
  ~75 min.
- S2-tail (2026-11-27): tail calls in the obligation framework (found converting F6: its error
  paths end with a jump to `memcpy`, `go` stops at the memcpy entry, and a cut there is impossible
  because its run is a 0-step leaf, so `hpos` fails). `Plan` gains `tail : Nat → Option (Callee σ
  img) := fun _ => none` (default: existing plans unchanged). `ExitGoal` at `.at pc`: when
  `P.tail pc = some k`, `m'.pc.toNat = k.entry ∧ k.Pre g m' ∧ k.bound ≤ rem ∧ ∀ m'', k.Post g m'
  m'' → P.Post g m''`; otherwise the cut case as before (`.jumpInd` unchanged). Helper lemmas
  `ExitGoal.at_cut` / `ExitGoal.at_tail`. `vc_sound` handles the tail case with the callee's
  `spec` (axioms unchanged). `exit_intro` picks the tail case when `P.tail pc` is `some`.
  `Test/Vc.lean`: plan `Tail` (`jal x0, memcpy` from one cut, `tail` = `Callee.memcpy`) assembles
  to `Tail.reach` with clean axioms. F1/F2 proofs unchanged; `lake build` 263 jobs OK.
- S5-p2b (2026-11-27): `runWith` in the Vc framework; F1 through `remap` without its return-site
  cut. `Sym/Summary.lean`: `runWith_sound` also gives, for leaves without summarised calls,
  `env' = env` and `SameOutside` of the writable regions only (new `goW_calls`). `Vc/SoundW.lean`:
  `PlanW extends Plan` (`sums`, `F0`, `X` callee footprint outside the caller's regions, `Qc`,
  `wleaves : Nat → List LeafW`; existing plans unchanged), `PlanW.callsAt` (distinct calls per
  cut), goals `CallGoal` (= `CallHyp` under the cut's assertion), `LeafGoalC` (leaves with calls:
  `∀ env'` agreeing with the cut `Env`, the run `RunsIn k m m'`, `CallFact`s, `FootW` footprint),
  `LeafGoalW` (plain `LeafGoal` of `P.toPlan` for call-free leaves, so their statements and proofs
  are as before); `vc_soundW` (guarded; tail case of S2-tail included). `Vc/AssembleW.lean`:
  `zesu_planw` / `zesu_autow` / `zesu_assemblew` (items `cut_`, `leaf_`, `call_<pc>_<k>`),
  tactics `leafc_intro`, `call_intro`. F1 (`Fn/F1/Vc.lean`, a `PlanW`, `sums` = `F0.summary`,
  `X` = remap's 16 bytes below F1's frame): cut `0x800cb4f8` (`cR`, `S1`, `AR`, `envR`, `remapC`,
  `runR`) gone; entry run is `runWith` (10 leaves; 4–6 carry the remap call). Old `leaf_..._4`'s
  body became `F1.call_800cb40c_0` (`f0_spec` + `F0.callPost`); old `runR` leaves 0/1/2 became
  entry leaves 4/5/6 over the entry terms (conditions moved to `env0` by `conds_env0`, `EnvOk`
  by `EnvOk.of_agree`); `alloc_call` takes the footprint with `X`. Cut points 5 → 4, runs 5 → 4,
  items 21 → 20 (4 cut lemmas, 15 leaves, 1 call goal): auto 5, manual 15, open 0 (was auto 5,
  manual 16). `Fn/F1/Vc.lean` 903 → 902 lines; generic `Vc/SoundW.lean` 136, `Vc/AssembleW.lean`
  249. `f1_spec` derived as before (`Proof.lean` unchanged); `Test/Budget.lean` restated on the
  `runWith` leaves (same costs 29/112/123/137/197). `lake build` OK, `tools/verify.sh` all PASS
  after `make -C tools/zmap map`. Gate S5.2 now passed for both halves (F3/decodeItem, F1/remap);
  alloc fallback unchanged. `zmap show f_800cb40c` still lists the static map's 5 cut points
  (S1 cut rule); the plan uses 4. ~60 min.
- S2-idx (2026-11-27): indexed callees. `Vc.Callee` gains `X : Type := Unit`; `Pre : σ → X →
  Machine → Prop`, `Post : σ → X → Machine → Machine → Prop`, `spec : ∀ g x, …`. `ExitGoal`'s
  call case is `∃ k x, P.callee r = some k ∧ … k.Pre g x m' ∧ ∀ m'', k.Post g x m' m'' → …`,
  its tail case `∃ x, …` (`ExitGoal.at_tail` likewise); `vc_sound` and `vc_soundW` pick the
  caller's `x` (`CallGoal` is about summaries and unchanged); `exit_intro` leaves `x` as a goal
  and closes it with `()` for `Unit` indices. `Callee.memcpy`, F1's `allocC` use `X := Unit`.
  F1's `freeC` is now the family over the allocator list (`X := List (Word × Nat)`), the call
  passes the list `L3`: the `freeL` workaround (list read back from `s3` inside the contract) is
  gone. Test/Vc `Tail` passes `()`. F1 20 items (auto 5, manual 15, open 0), F2 unchanged;
  `lake build` OK, `tools/verify.sh` all PASS after `make -C tools/zmap map`.
- S8 (2026-11-27): cost model tooling. `tools/zmap/costmodel.py` and subcommand
  `python3 -m zmap costmodel --map map/map.json --ledger map/ledger.jsonl --out map/COSTMODEL.md`
  (one block in `__main__.py`; run by `make -C tools/zmap map`). Sections: effort by ledger kind
  (count, median/total minutes and $), plan leaves by state and manual/open leaves by residual
  class; per function with proof material or ledger rows the static features (cuts, loops,
  calls, joins, `leaves_estimate`, instructions) beside actual leaves and ledger totals;
  auto-closed share before/after each automation item, from ledger notes
  `auto_share <fn> a/t -> a/t` (six zero-minute `rule` rows added from the counts recorded in
  this LOG: F2 0/20; F1 2/21 (S4) → 2/21 (S5-p1) → 5/21 (S5-p1b) → 5/20 (S5-p2b) → 5/20
  (S2-idx)); these rows are left out of the effort table; target set by state with feature sums
  and the median `leaves_estimate`. Rates and counts only. `tests/test_costmodel.py` (4 tests);
  `python3 -m unittest discover -s tools/zmap/tests` 22 OK. Residual classes are all `none` now:
  hand-written leaf theorems record no residual. `Test/Auto.lean` (Verification item 4, five
  `fail_if_success`) builds after S2-idx. `tools/verify.sh` all PASS.
- S6 TX step 6 progress (S1StaticMap): merged exec-spike 5de908a3 and fb4071d9 (indexed callees,
  tail, runWith, costmodel) at `68287580`; TX callees adapted to indexed `Callee` (`famCallee`
  with `X`, `ARet k site` with the index). `Fn/TX/Vc.lean`: cut lemmas `0x80000000`, `0x68`,
  `0xc4`, `0xd8`, `0x10c`, `0x15c`, `0x18c`, `0x1a0` (8 of 17); leaf `0x80000000_0`; generic
  lemmas (`pre_wf`, `pre_match`, `f2_pre`, `common_ret`, `common_f2`, `body_ok`, `payload_ok`,
  `priv_sub`, `error_post` for the 20 error-exit `ret` leaves). Open: 9 cut lemmas, 45 leaves.
  WIP (not committed, does not build): `bytes_of_present`, `init_slot`, `f2_result` in
  `/home/cody/.cache/zesu-tmp/zmap/p9/Vc_wip.lean`.
- S4-F6 (2026-11-27): F6 (`decodeParentHeader`) converted to the obligation framework
  (assumption "Legacy proofs": F1's conversion reduced hand lines, so F6 next). Plan `F6` in
  `Fn/F6/Vc.lean`: the map's 24 cuts (entry, 20 call-return points, 3 loop heads), the runs of
  `Fn/F6/Runs.lean` unchanged; callees `kD` (decodeItem/F2) and `kN` (nextUint64/F3) by return
  address, both `X := Unit` with `Preserved`; the error paths tail-call `memcpy` via `Plan.tail`
  (S2-tail, made for this). Assertions = the spike's per-cut hypotheses (`DSt`/`NSt`/`SSt`/`OSt`,
  registers, frame words, walk position) plus `Entry m` and the pc; budgets the spike's constants;
  loop heads `LInv` plus the exit's registers/walk, budget `((a2 - a1) - 1) * 5 + E` (E = 1178,
  1043, 907) read off the machine, `Env` var 32 = `a1 - a1₀`. Leaves: 74; items 98 (24 cut lemmas,
  74 leaves): auto 0, manual 98, open 0 (`zesu_auto F6` closes 0 of 74 leaf items it tries; cut
  lemmas are 1-line `cutR_ok`/`cutL_ok` wrappers of `Fr.match`). Continuation helpers split for
  `ExitGoal`: `call_d`/`call_n` (Lemmas) now return the callee precondition and a
  continuation-for-every-result instead of `Reaches`; `memcpy_exit` returns `MemcpyPre ∧ ∀ result,
  Post`; `loop_gen`'s induction replaced by `back_step` (one back edge re-establishes `LInv` at
  j+1) and `exit_last`; `entry_fr` no longer needs `Preserved`. `F6.reach` assembled with clean
  axioms (guarded in Axioms.lean); `Fn/F6/Proof.lean` derives `f6_spec` from it (statement
  unchanged); `f6_sail`, F6 compliance unchanged and build. Old stage theorems (`after0`..
  `after18`, `afterF0`, `skip_req`, `opt_skip`, `loop_gen`, `cut_reaches`) deleted. Hand lines
  before: Proof 1752 + Lemmas 1277 + Runs 35 = 3064; after: Vc 2269 + Lemmas 1259 + Proof 22 +
  Runs 35 = 3585 (+521, +17%; of Vc, 148 lines are the generated-shape `leaf_<pc>_<i>` wrappers,
  ~130 the assertion/cut/plan definitions, ~110 the generic `lg`/`call_goal`/`at_goal`/cut
  lemmas). Comparison with F1 (1898 -> 1707, -10%): F6's leaves were already per-cut in the
  spike, so the framework adds per-cut assertion definitions and per-leaf boilerplate without
  removing duplicated runs; a `zesu_assemble` option taking `∀ l ∈ runX_leaves` lemmas per cut
  (instead of one theorem per leaf) would remove the 148 wrapper lines (F6 then ~3437, +12%).
  Merged exec-spike (indexed callees 5de908a3, runWith): F6 adapted (`kD`/`kN` over `Unit`,
  `call_goal` takes `x`). runWith summaries for decodeItem could remove F6's 20 return-site cuts;
  not attempted. `lake build` 269 jobs OK; `make -C tools/zmap map`, `tools/verify.sh` all PASS;
  `zmap show f_800d5cb8`: closed+compliance, reach=yes.
- S4b (2026-11-27): automation coverage. Classification of the manual leaves by what the hand
  proof does (read, before this item): F1 13 = infeasible-by-bitvector 5 (needs `Pre`'s
  `req < 2^32` and the `grown` lemmas), callee precondition 4, postcondition 3, assertion at
  the next cut 1; F2 17 = postcondition 13 (decode semantics), assertion at the next cut 4.
  Recorded classes (`zesu_auto` now runs `leaf_diag` after a failed `leaf_auto`: the first
  stage that does not close, `class <c> <head>`; `zesu-status` reports it for manual items too;
  `costmodel` reads it): F1 oblig 3 / budget 4; F2 oblig 17; F6 oblig 27 / tail 24 /
  callee-pre 20 / cut 3; TX oblig 22 / budget 16 / callee-pre 4 / cut 4 — all functions: oblig
  69, callee-pre 24, tail 24, budget 20, cut 7 (first failing stage, so a leaf whose
  obligation is open is `oblig` whatever follows). Automation for infeasible leaves (top class
  by reading in F1): `Vc/Facts.lean` attribute `@[zesu_fact]` (lemmas deriving a fact from a
  cut's assertion) and tactic `zesu_facts` (forward chaining over the context: premises matched
  by unification, conclusion added; adds hypotheses only); a new `leaf_auto` rule (tried first,
  earlier rules unchanged on failure): `exfalso; zesu_facts`, then `leaf_norm` with
  `omega`/`bv_omega`/`simp_all`, or `simp` normal form of the conditions rewritten with the
  facts and closed by `simp`/`simp_all`; `leafc_auto` (new) does the same for leaves through
  summarised calls after `SBool.conds_agree` and `zesu_autow` now tries it. F1: six facts
  (`AE.req`, `AE.cap`, `AE.grown_or`, `AE.grown_shl5`, `AE.grown_srl59`, `AE.grown_bytes_ne`);
  hand leaves 1, 3, 9 (plain) and 4, 6 (through `remap`) deleted, `f1_overflow` deleted. F1
  items 20: auto 5 → 10 (leaves 2 → 7 of 15), manual 15 → 10; F2 0/20 unchanged (no
  infeasible leaves; its leaves need decode semantics); TX 5/68 and F6 0/74 unchanged (no
  facts declared). The second class by reading, postcondition, is per-function semantics; the
  recorded classes point at obligations (return alignment, `inBounds`) and budgets (`if` budgets)
  next, which close once the function declares its assertion facts (`@[zesu_fact]`), not
  attempted here. `Test/Auto.lean` negative tests build; `lake build` OK; zmap tests OK;
  `tools/verify.sh` all PASS after `make -C tools/zmap map`.
- S4c (2026-11-27): the two recorded top classes, `oblig` and `budget`. `Vc/Facts.lean`:
  attribute `@[zesu_oblig]` (a lemma proving `Oblig.holds env o` from assertion facts) and tactic
  `zesu_apply` (apply a tagged lemma, unifying its conclusion with the goal; its premises must be
  hypotheses or conjuncts of hypotheses, definitions unfolded). `Vc/Tactics.lean` (additive):
  `oblig_auto` (each obligation by `zesu_apply`, else normalisation and `field_auto`),
  `budget_auto` (`omega`, `decide` for budgets behind definitions, or `split` the budget's `if`s
  then `omega`), and a new `leaf_auto` rule (tried first; earlier rules unchanged on failure):
  facts, `oblig_auto`, `budget_auto`, then the exit goal as before. `leaf_diag` uses the same
  stages. Lemmas: F1 `ra_oblig` (entry), `ra_oblig_join` (join cuts); F2 `ra_oblig`,
  `loop_inb_oblig` (`j < w < len` from `Inv`), `loop_ra_oblig`, `@[zesu_simp]` `envE_size1`,
  `envE_vars`; F6 `ra_oblig` (saved `ra` under any return cut's `envC`). Classes before → after
  (first failing stage): F1 oblig 3 / budget 4 → post 3 / callee-pre 3 / cut 1; F2 oblig 17 →
  post 13 / cut 4 (now equal to the classes read off the hand proofs); F6 oblig 27 → oblig 7
  (`inBounds` at decodeItem calls and loop entries, not attempted) with 20 moved to post; TX
  unchanged (no lemmas declared on this branch); all: oblig 69 → 29, budget 20 → 16, post 0 → 36.
  Auto counts unchanged: F1 10/20, F2 0/20, F6 0/98: with obligations and budgets closed every
  remaining leaf fails at the exit goal (postcondition semantics, callee preconditions, the next
  cut's assertion, tail callee), so no hand leaf was deleted. `Test/Auto.lean` builds; `lake
  build` 258 jobs OK; `tools/verify.sh` all PASS after `make -C tools/zmap map`.
- S4d (2026-11-27, decision): exit-goal automation for F6 stopped. Residual tail/callee-pre/post/cut goals in F6 are per-field decoder correctness (SSt/DSt step over the field schedule, walk semantics), not side conditions; tagging per-field hand steps as @[zesu_fact] would relabel hand proofs as auto. Automation scope stays: infeasible leaves (zesu_fact), obligations/budgets (S4c), residual classification. No commit.
- S6.8 (2026-11-27, gate: closed, conditional on `tx_spec`): TX compliance, new files only.
  `Compliance/TXSail.lean`: EVM-Sail `decode_access_list` in closed form — pure `sailKeys`,
  `sailEntry`, `sailEntries`, `sailAccess` (address/slot counts) with `keys_eval`, `dkeys_eval`,
  `entries_eval`, `access_eval` (fuel induction over the Sail recursions; every failure is the
  `fatal_error RlpDecode` exit). `Compliance/TX.lean`: triggers of `TxAccessListBugTriggers.v`
  (`addrC`/`keyC`/`trailC` over `calls input`, `bugTrigger`), `fits_eq` (on `HeaderFits` the
  candidate's `decode` is Sail's item), `keys_rel`/`entry_rel`/`entries_rel`/`access_rel`
  (candidate counts = Sail counts or a trigger), `tx_candidate_agrees` (on `Domain`),
  `tx_compliance_of`/`tx_compliance_sail_of` taking `hspec : Spec zesuImage TX.entry bound
  (Pre A g) (Post A g)`. Sail's `encoded` span is not compared. Witnesses by `decide`: agreeing
  (1 entry, 1 key), 19-byte address, 31-byte key, trailing byte after keys. Axiom guards added
  (3). `lake build` 277 jobs OK; `tools/verify.sh` all PASS after `make -C tools/zmap map`.
- S5-p2c (2026-11-27, gate: blocked, fallback taken; no Fn/F6 change): F6 through decodeItem
  `runWith` summaries (`⟨F2.bound, abiClobbers, none, [(a0, 40)]⟩`, as F3). Measured with every
  current cut kept, one `runWith` per cut start: of the 17 cut-started runs that cross a
  decodeItem call, `runWith` returns `none` for 11 (from retS0..retS7, ret9, ret10, ret12,
  ret13); it accepts the runs from entry, ret0, ret11, ret14, ret15, ret16 (same leaf counts as
  `run`). Removing a skip return cut makes the merged run fail at the second call. Cause:
  `CallRec.okB` (S5-p2) havocs a written range into the leaf's single initial memory `mem0`, so
  a call may not write bytes the path already read. F6 reuses its outcome slots (frame 64 for
  fields 0..8, 280 for 9..11, 104 for 12..14) and branches on the previous outcome before the
  next call. Cuts/leaves/items/hand lines unchanged (24 / 74 / 98 / Vc 2276 + Lemmas 1259).
  Probe time ~2 s per `runWith` batch. Needed before this conversion: summaries that leave fresh
  symbolic writes (new variables per call) in the written range instead of havocking `mem0`
  (generic: `Sym/Summary.lean`, `runWith_sound`). Prior evidence on the line count: F3's one
  summarised call took hand lines +277. Reported to DTFPipeline. ~25 min.
- S6 TX step 6/7 (TXLeaves, 2026-11-27): merged exec-spike 8d760c3a (F6) and 9f7202ca (S4b
  `zesu_fact`). Cut lemmas: all 17 closed (`Ret.lean`: `0x1f8 0x25c 0x340 0x3d4 0x400 0x42c 0x4a0`
  via `ret_*` = `Common` + pc after each callee; `Store.lean`: `0x230 0x460`, a sixth region (slot in
  a live block, `wf_snoc`, `slot_ok`)). S4b facts (`Facts.lean`: dead-344 `a0 = 0` after remap,
  `40 c' ≠ 0`, growth `n < 2^32` with `grow_mulhu`/`grow_bytes`, `Common` at every cut, saved `ra`):
  `zesu_auto TX` re-run in `Proof.lean`, auto 5 -> 10 of 68 (`25c_2 25c_3 25c_6 340_1 340_3`).
  Hand leaves (mine, 17): `068_0..1` (`Err.lean`: `err_leaf`, `f2_result`, outcome bytes),
  `0d8_0..1` (`Outer.lean`: `outer_err`, `OuterState` over `decodeItem`), `10c_0..2`
  (`Entry.lean`), `15c_0..1`, `1a0_0..2` (`Keys.lean`), `0c4_0`, `18c_0` (`Calls.lean`); P2Summaries
  adds 5 in `Leaves2.lean` (`1f8_0 25c_0 3d4_1 340_0 4a0_1`). Counts: 68 items, 10 auto, 37 manual
  (17 cut lemmas + 20 leaves), 21 open. Gate S6 fallback: `TX.reach_from` assembled with the 21
  open leaves as fields of `TX.Open`, listed in the map and saved one goal each in `OPEN/TX/`
  (statement, residual class, `Leaf.pp`). `tx_spec`/`tx_sail` not added (needs `TX.reach`).
- S2-runs (2026-11-27, branch `dtf`, separate commit): `zesu_assemble`/`zesu_assemblew` take a
  theorem `F.run_<pc>` as the proof of that cut's run equation (`runProof?`: same head `run` /
  `runWith`, arguments and leaves matched by `isDefEq` on the arguments, the head never unfolded;
  a mismatch fails naming the cut); without one they use `Eq.refl` as before. Fixes S2's double
  check: DTF's assembly re-evaluated all 161 runs in one kernel declaration — 328 s, peak RSS
  41.8 GB, `(kernel) deterministic timeout`; with `DTF.run_<pc>` (aliases of the `sym_run`
  theorems) 11.2 s, 2.4 GB. `Test/Vc.lean`: Toy3 assembles with run theorems, Toy4's run theorem
  for the wrong cut is refused.
- S7 (2026-11-27, branch `dtf`): `rlp_decode.decodeTxFields` (DTF) through the pipeline to
  `DTF.reach_from`. **Gate S7 passed** (`DTF.reach_from` assembles, guarded in `Axioms.lean`;
  `zmap show f_8000050c`: state `conditional`, leaves auto 0 / manual 0 / open 486, cut lemmas
  manual 70 / open 91).
  - Cut points 161 (`Fn/DTF/Regions.lean`): the map's 153 (join cuts on), the 5 jump-table
    targets, 3 hand-placed (ledger `assertion` items): `0x80000574` (the jump-table load; the
    table word is region 4 because the executor reads rodata only at literal addresses),
    `0x80002138` and `0x80002434` (stores into the `txHashList` / `txAuthList` buffers; the
    executor stores only at constant region offsets). Register/frame-slot shapes, arms, `rest`
    locations and call sites per cut are generated by `OPEN/DTF/shape.py` (forward analysis).
  - Runs (`Runs.lean`): 161 `sym_run`, 486 leaves, 218 s for the module, slowest run 7.6 s
    (none near the 60 s limit, so no cuts beyond the three above). `decodeItem` summaries
    measured: `runWith` returns `none` as soon as a second call reuses the outcome slot
    (`S-0x90`), so the 63 return-site cuts stay (`OPEN/DTF/CUTS.md`; P2Summaries found the same on
    F6).
  - TX as callee: `Sig.hTX : TXSpec A` (`∀ x, Spec zesuImage TX.entry txBound (TX.Pre A x)
    (TX.Post A x)`, `txBound = 32·2^30 + 424`, TX's entry budget for the largest input area);
    the TX callee's `spec` is `σ.hTX`, so `DTF.reach_from` is conditional on TX's contract as
    well as on `DTF.Open`. TX files untouched.
  - Assertions (`Cuts.lean`): `PlainA` = pc, `Common` (frame, saved registers, `SameOutside` from
    the entry, presence, heap `Live`), `ShapeOk`, `ArmOk`, `RestOk` (the `rest` slice after `k`
    top-level items: `skip k payload`), `Extra` (table address, buffer slots, the written
    result); return sites `RetA` (call-site predicate and the callee's `Post`). Open assertion
    items (field values, per-field checks, list buffers, byte-loop state, callee indices) are
    listed in `OPEN/DTF/CUTS.md` and the ledger; the success write and every leaf needing a field
    value stay open until they are added.
  - Budgets: `K + 256·(rest length) + inner` (`K` longest path over the cut graph with callee
    bounds; byte loops `20·(end - cur)`, list loops `256·(bytes left)`); entry 34,359,750,421.
  - Counts: items 647 (161 cut lemmas, 486 leaves); `zesu_auto` 0 (262 s; needs
    `maxRecDepth 20000`, its `simp` on the 161-row table overflows the default); manual 70 (the
    cut lemmas of all jump/branch-only cuts without an extra region, one generic theorem
    `cut_plain` in `Lemmas.lean`); open 577 (91 cut lemmas, 486 leaves). First queue classes:
    `budget` (the budget lookup is behind `budgetAt`), `oblig`.
  - `lake build` 283 jobs OK (268 s from cold DTF modules, peak 2.6 GB); `tools/verify.sh` all
    PASS after `make -C tools/zmap map`; ledger +978 S7 items (980 DTF items in all).
- S7 cont. (2026-11-27, branch `dtf`, after `git merge exec-spike`, fast-forward): DTF budget
  lookups and cut lemmas. **Counts before → after: manual 70 → 150, auto 0 → 0, open 577 → 497**
  (cut lemmas open 91 → 11, leaves open 486 → 486).
  - Budget: `@[zesu_simp] budgetOf_eq` and one `budgetAt_<pc>` row per cut (`Cuts.lean`,
    generated from `budgetTable`). No leaf's first failing stage is `budget` any more (the 113
    `oblig` leaves stop before it). `zesu_auto DTF` still closes 0 of 647 (each leaf also needs
    its obligations and exit). `Vc.lean` now takes 14 min (262 s at S7); the likely cause, not
    measured, is the 161 extra `zesu_simp` rows tried by every `leaf_norm`.
  - Return sites (`Ret.lean`): "`Common` survives the call" per callee kind, modelled on TX's
    `common_ret`/`common_f2`: `common_ret` (any callee whose writes are DTF's stack below the save
    area or `Priv g.L`, given the live list after it), `ret_f2` (outcome slot `a0 = fr + k`,
    `k + 144 ≤ 0x370`), `ret_alloc` (`Live` grows by the new block, carved from `Priv g.L`),
    `ret_remap`, `ret_tx` (TX's result and `rest` slots, its stack below DTF's frame, the scratch
    word; the returned or leaked blocks it adds to the live list are `Priv g.L` by `added_priv`:
    `arena_split` at the entry and after the call, apart from the caller's blocks by `live_ok`).
    One generic theorem `cut_ret` (return-site shape vs call-site shape checked by `decide`,
    `RetCheck`) closes 76 return-site cut lemmas (63 `decodeItem`, 7 `alloc`, 2 `remap`, 4 TX).
    `IdxOk` (call-site predicate) now carries the callee's `Pre` and `Live σ m x.1 X` (allocator,
    F1, F4, TX), which `ret_alloc` needs (the block size is positive, the live list is DTF's).
  - Entry: `cut_entry` (`Avail`, the part of `Common` `Match` needs, holds at the entry machine).
    Region 4: `match_gen` (the base regions and region 4 at `a0`), `wf_slot` (`entry_wf` with
    pointwise disjointness, so a zero-length payload needs no `Apart` with the slot),
    `cut_slot` (`0x80002138`, `0x80002434`: the slot is `Priv g.L`, apart from frame, result,
    allocator object and payload by `Pre`), `cut_table` (`0x80000574`: the table word is rodata,
    `table_rodata` by `decide`).
  - Still open cut lemmas (11): 7 `memcpy` and 2 `free` returns (the destination / freed block is
    not located by the assertions: `OPEN/DTF/CUTS.md` groups 1 and 3), F1 and F4 (the list
    buffer, group 3).
  - Queue classes (486 leaves): `cut ite` 268 (`leaf_auto` stops at `if pc = entry` in
    `mkCut`), `callee-pre` 105, `oblig` 113.
  - `lake build` OK; `tools/verify.sh` all PASS after `make -C tools/zmap map`; ledger +82.
- S7 cont. (2026-11-27, branch `dtf`, `git merge exec-spike` at c6ee8585): build time, TX contract.
  - `Vc.lean` regression measured (`lake env lean -Dprofiler=true`, one run each, same machine):
    with the 161 `@[zesu_simp] budgetAt_<pc>` rows and `budgetOf_eq` **897 s** (simp 497 s,
    tactic 200 s, interpretation 122 s); with them removed (`attribute [-zesu_simp]`) **274 s**
    (simp 62 s). The simp-set size is not the cause: `leaf_norm` alone costs the same with and
    without them (4 sample leaves, 74 ms vs 77 ms). The cause is progress: with the rows
    `budget_auto` passes on every leaf whose obligations pass, so two `leaf_auto` rules and
    `leaf_diag` run the exit stage (`exit_intro`, `leaf_norm`, `field_auto`'s `simp_all`) and fail
    there, about 1.2 s more per leaf (single leaf 0x8000059c #0: 1.2 s vs 0.2 s) — for 0 more
    closed items (DTF leaves need `Common`/`RestOk`, which `field_auto` cannot prove).
  - Fix: the rows and `budgetOf_eq` removed (`budgetOf` documents why); budgets are proved in the
    hand-written leaf theorems. `Vc.lean` **265 s** in `lake build` (was ~14 min); `zesu_auto
    DTF` 0 of 647 as before; the residual class of the 268 `cut ite` leaves is `budget` again.
  - `hTX` discharged: `Sig` has no `hTX` field; the TX callee is `TX.tx_spec σ.A x.2.2` (bound
    `TX.bound` = the former `txBound`), so `DTF.reach_from` depends only on `DTF.Open`.
  - `lake build ZesuExec.Fn.DTF.Reach` OK: 647 items, 0 auto, 150 manual, 497 open.
- S6 TX second hand (P2Summaries, 2026-11-27): (1) Cuts.lean assertion fix (Main-approved, S6.6
  wrong-assertion rule): `OuterWalked`/`KeysWalked` carry `WalkFits`/`KeysFits` (HeaderFits of
  every call the rest of the walk reaches; from `Domain` at 068_3), since `EntryOk`/`AKeyStore`
  length facts need no-wrap and only `Domain` gives it; lemmas `fits_bounds`, `fits_rest`,
  `keysWalk_fuel`, `entriesWalk_fuel`, `walkFits_head/entry/tail`, `keysFits_head/tail`.
  (2) `Leaves2.lean`: `oom_err`, `rest_keep2`, `ed_congr` + `edsame_of` (EntryDone across a callee
  whose footprint is free stack / scratch / `Priv L` / other live blocks), `growing_keep`,
  `common_congr`, `alloc_congr`; leaves 1f8_0, 25c_0, 3d4_1, 340_0 (dead), 4a0_1, 400_0.
  Counts: 68 items, 10 auto, 38 manual, 20 open. Found: `Site428` requires `Copied` hence
  `Growing`'s `s11 = ec`, but leaf 400_1 sets `s11 := ec << 5` before the `free` call, so
  400_1 is unprovable until `Site428` drops that register fact (fix in Cuts.lean: move
  `m.reg 27 = o.ec` out of `Growing` into `Allocated`/`Site33c`/`Site3d0`, give `Site428` a
  copy of `Copied` without it; adjust `ret_340`/`ret_400`/`ret_42c` indices).
- S6 TX third hand (TXLeavesB, 2026-11-27): `Fn/TX/Leaves3.lean` (imports Leaves2, imported by
  Proof.lean and Grow.lean) closes leaves 068_2, 068_3, 0d8_2, 10c_3, 15c_2, 15c_3, 1a0_3,
  230_0, 230_1. Reusable: `towned_pre`/`f1_pre_tx` (callee preconditions at TX call sites),
  `after068`, `after15c`, `after230` (`slot_same`, `slot_bytes`), `frame_only`, `sl_apart`,
  `outer_frame_keep`, `ie_keep`, `ret10c'`/`ret1a0'`, input copies (`leaf_bytes`,
  `byteOf_byteList`, `byteOf_sext32`, `input_byte`, `slot_word`), `dec_ptr_str`, `dec_hpos`.
  The generic write-leaf helpers moved to Leaves2 (TXLeavesC). Proof build at 00fdea01 had 14 open;
  1f8_1 and 4a0_0 went back to TXLeavesC unstarted.
- S6 TX third hand (TXLeavesC, 2026-11-27): Cuts.lean: `s11 = ec` moved out of `Growing` into
  `Site33c`/`Site3d0`/`Site3fc` (the `free` leaf overwrites `s11`; `Copied`/`Allocated`
  unchanged). `Fn/TX/Grow.lean` closes 3d4_0, 400_1, 42c_0, 25c_1, 25c_4, 25c_5, 340_2;
  `Fn/TX/Finish.lean` closes 460_0, 460_1. Reusable: `live_of_heap` (new blocks are in
  `Priv g.L` via `arena_split`), `erase_perm`, `live_perm`, `Grown`/`ELNoHdr`/`grown_keep`
  (EntryDone without header/copy B), `ret25c`, `grow25c` (+`growS_eval`), `ret400_copied`,
  `at42c`, `after460`, `walked_step`, `frame_leaf_so`, `fr_in`, `wr_miss`, `edsame_frame`,
  `leaf_copy`, `fw_same`, `cframe_keep`, `callee_frame`, `memcpy_pre`, `ctx_eval`, `shl5/3/40`.
  Still open: 4a0_0 (success exit; needs an `ok_post` analogue of `error_post` with the
  `OutcomeImage .ok` heap `L.erase (ep,40ec) ++ [(p',40n)] ~ g.L ++ returnedBlocks`) and
  1f8_1, which is BLOCKED by F1's contract: `F1.Post`'s no-growth branch (`req ≤ c`) does not
  state `BytesAt m' p items`, while its `SameOutside` lets F1 write the list buffer, so the keys
  stored so far are not known after `ensureTotalCapacity` returns. Fix: add `BytesAt m' p items`
  to that branch of `F1.Post` (Fn/F1/Spec.lean) and reprove it in F1 (the early-exit path writes
  only its frame). TX.reach / tx_spec / tx_sail / compliance not assembled.
- S6 TX finish (TXFinish, 2026-11-27): F1's contract is not changed (rule 7); its plan's Post is
  `PostKeep := Post ∧ (req ≤ capacity → BytesAt m' p items)` (`Fn/F1/Vc.lean`): leaf 0 (no
  growth) writes only F1's frame and the header (its `InWritable` is frame ∪ header, the buffer
  is apart by `oldNotOwn`), the other exits grow or fail and take the conjunct vacuously.
  `f1_spec_keep` (new) is `F1.reach`; `f1_spec` is derived by dropping the conjunct
  (`git diff 7a9e7da8 -- Fn/F1/Spec.lean`: no statement change). TX's `f1C` uses
  `f1_spec_keep`. `Fn/TX/Room.lean`: `after1f8` (the keys loop state after F1 returned 0, both
  branches; grown buffer `{p', grown(n+1)}` via `live_of_heap`/`erase_perm`, footprint through
  `edsame_of`), `ie_same`, leaf 1f8_1. `Fn/TX/Vc.lean`: `error_post` refactored onto
  `exit_post` (epilogue, registers, `rest`), `ok_post` (`OutcomeImage .ok` from `okWrites` and a
  live list `L ~ g.L ++ returnedBlocks`). `Fn/TX/Done.lean`: `accepted_of` (walked payload →
  `candidate = accepted done (itemConsumed h p)`), leaf 4a0_0 (F5's empty and success branches;
  keys slices survive F5 by `live_apart`). `zesu_assemble TX`: 68 items, 10 auto, 58 manual,
  0 open → `TX.reach`. `tx_spec : Spec zesuImage 0x80000000 bound (Pre A g) (Post A g)` with
  `bound := 32·2^30 + 424` (`len_le`: the input is in the input buffer or RAM); `tx_sail`
  (`Fn/TX/Sail.lean`). Compliance: `Compliance/TX.lean`, `TXSail.lean` taken from exec-spike
  (258a3dba, unchanged since), `tx_compliance`/`tx_compliance_sail` specialise the `_of` forms
  to `tx_spec`; `zesu-status` finds compliance theorems under `ZesuExec.Compliance.<F>`
  (`complianceName`). Axioms guards for `f1_spec_keep`, `TX.reach`, `tx_spec`, `tx_sail` and the
  five compliance theorems. `lake build` OK; `make -C tools/zmap map`; `tools/verify.sh` all PASS;
  `zmap show f_80000000`: closed+compliance.
