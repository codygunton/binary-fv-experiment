# S12 forms left unsupported

Plan S12 contingency: these forms keep no decoder, executor or soundness case, and the target
functions that use them stay blocked on the map (`tools/zmap/analyze.py` `FORMS` omits them).

## `srai` (7 target functions): the model's arithmetic shift is a rotation

`Srai.lean` (beside this file, outside the library). The generated
`shift_bits_right_arith` (`sail-riscv-lean/LeanRV64DExecutable/Prelude.lean:381`) is
`BitVec.rotateRight`, so the model's `srai`, `sra`, `sraiw` and `sraw` rotate. `srai 1, 1` is
`2^63` in the model and `0` in RISC-V (both checked by `decide` in `Srai.lean`). The simulation
goal `sim_srai` is false for a `Machine.exec` that shifts arithmetically, as ZisK and Unicorn do.
Fix: regenerate `sail-riscv-lean` with `shift_bits_right_arith value shift =
value.sshiftRight shift.toNat` (a change to the Lean prelude of the generated tree, outside S12).

## `maxu packh pack rev8 bext bset bclri clz` (Zbb, Zbkb, Zbs): not in the compiled model

The compiled model has no bit-manipulation instructions. `inductive instruction`
(`sail-riscv-lean/LeanRV64DExecutable/Defs.lean:293`) has exactly the constructors
`ILLEGAL C_ILLEGAL LPAD UTYPE JAL JALR BTYPE ITYPE SHIFTIOP RTYPE LOAD STORE ADDIW RTYPEW
SHIFTIWOP FENCE_TSO FENCE ECALL MRET SRET EBREAK WFI SFENCE_VMA MUL DIV REM MULW DIVW REMW`, and
`currentlyEnabled` (`PlatformConfig.lean:1422`) has no clause for `Ext_B`, `Ext_Zbb`, `Ext_Zbkb`
or `Ext_Zbs` (they fall to `| _ => pure false`). The model's decoder therefore returns `ILLEGAL`
for these words, and `decode_sound` (`ZesuExec/Sail/Decode.lean`) cannot hold for them: a
`try_step` on such a word traps instead of retiring. The open goal for each form is the pair
`dec_<form>` and `sim_<form>` against a model that compiles `model/extensions/B/*.sail` and
`model/extensions/K/zbkb_insts.sail`; it needs the `zesuSailRiscvLean` build to include those
files (`hartSupports`, `PlatformConfig.lean:976`, already marks `B` and `Zbkb` supported; in the
stock model `Zbb` and `Zbs` are enabled through `B`).

| form | extension | target functions blocked (map before S12) | sample word |
|---|---|---|---|
| `maxu` | Zbb | 3 | `0x0ac7f633` at `0x800e1800` |
| `packh` | Zbkb | 3 | `0x0862f2b3` at `0x800e18d8` |
| `pack` | Zbkb | 3 | `0x094ac933` at `0x800e8fe0` |
| `rev8` | Zbb | 2 | `0x6b86d593` at `0x800e9060` |
| `bext` | Zbs | 2 | `0x49465633` at `0x800e5b68` |
| `bset` | Zbs | 2 | `0x29461633` at `0x800e5b88` |
| `bclri` | Zbs | 1 | `0x4bf51a93` at `0x800e8a34` |
| `clz` | Zbb | 1 | `0x60069793` at `0x8010f910` |
