# Where ZisK stages the `memcpy` count (S14 finding)

**Resolved** (branch `xparams`): `Layout.extraParams := 0xa0000f00`, snapshots re-taken with the
runner's `ZISK_SCRATCH` overridden by `tools/snap.py`, proofs and witnesses repaired, `svc_test`
`0x813-reg`/`fn-memmove` 100/100 on the staging word. STATEMENTS.md "Correction: memcpy staging
address". The text below is the original finding.

**Finding.** `Layout.extraParams = 0xa0400f00` (`ZesuExec/Machine.lean`, copied from zesislar
`ZesuSsz/Contracts/ZiskRuntime.v:19`) is not where ZisK stages the count. ZisK `eed62f4d9` stages
it at `EXTRA_PARAMS_ADDR = SYS_ADDR + 0x0F00 = 0xa0000f00` (`/home/cody/zisk/core/src/mem.rs:113`
`SYS_ADDR = RAM_ADDR = 0xa0000000`, `:147` `EXTRA_PARAMS_ADDR`).

**The binary names no address.** `memcpy` at `0x800e06c0` is

    800e06c0: 8135a073  csrs 0x813, a1
    800e06c4: 00c50033  add  zero, a0, a2
    800e06c8: 00008067  ret

The staging address is chosen by ZisK's transpiler, not by the program: `csrs 0x813, rs` followed
by `add x0, rd, rcount` becomes `sd rcount, [EXTRA_PARAMS_ADDR]` then `dma_memcpy`
(`core/src/riscv2zisk_context.rs:1994-2008` `transpile_dma_memcpy_memcmp_pattern`, `:719-736`
`create_set_precompiles_param_op`, `:105-114` the fused `add`; the op reads the count back,
`core/src/operations/dma_memcpy.rs:20-23`). So every `0x813` site of the binary (memcpy, memmove,
the inline sites) writes 8 bytes at `0xa0000f00` on real ZisK.

**Emulator evidence.** `ziskemu` built from eed62f4d9 (S14), program
`a1=0xa0100000 a0=0xa0100010 a2=5; csrs 0x813,a1; add zero,a0,a2`, then dump of the 8 bytes at
`0xa0000f00` and at `0xa0400f00`: `0xa0000f00` holds `5`, `0xa0400f00` holds `0`
(repeated over 100 random cases by `tools/svc_test.py`, check `memcpy-staging`).

**Snapshots do not catch it.** `tools/snap.py` reuses zesislar's Unicorn runner
(`tools/oblig/exec/run.py:74` `ZISK_SCRATCH = 0xa0400f00`, `:295-305` `_memcpy` hook), which
writes the same wrong cell; difftest agreement is by construction, not against ZisK.

**Consequence.** `ziskMemcpy` (and `MemcpyPost`) says the service writes `0xa0400f00..+8` and
leaves `0xa0000f00..+8` alone; ZisK does the reverse. Every theorem that uses `memcpy_spec`
(F1, F4, F6, TX, DTF) is about a service whose write set is mis-modelled in those 16 bytes. The
copy itself (destination bytes, registers, `pc`) is modelled as ZisK does it (same emulator
check). Fix: set `Layout.extraParams := 0xa0000f00`, repair the proofs that use its numeric value
(disjointness from the stack/heap regions; `0xa0000f00` lies in ZisK's SYS area at the bottom of
the program's stack range `0xa0000000..0xa0400000`), and change `ZISK_SCRATCH` in the snapshot
path. Scheduled by the coordinator after S13.
