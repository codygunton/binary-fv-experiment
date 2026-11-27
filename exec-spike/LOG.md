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
