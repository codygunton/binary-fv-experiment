# S12 forms left unsupported

Plan S12 contingency: these forms keep no decoder, executor or soundness case, and the target
functions that use them stay blocked on the map (`tools/zmap/analyze.py` `FORMS` omits them).

`srai` was here until S12b: the generated `shift_bits_right_arith` was `BitVec.rotateRight`
because Sail 0.20.1's library bound `sail_arith_shiftright` to it for Lean. S12b regenerated the
model with the upstream fix (`sail/00-sail-lean-asr.patch`, `sail/PROVENANCE.md`) and added the
form (`dec_srai`, `sim_srai`).

## `maxu packh pack rev8 bext bset bclri clz` (Zbb, Zbkb, Zbs)

Until S12b the compiled model had no bit-manipulation instructions. S12b compiles
`Zba;Zbb;Zbs;Zbkb` (`sail/PROVENANCE.md`); the forms are added one by one.

| form | extension | target functions blocked (map before S12b) | sample word |
|---|---|---|---|
| `maxu` | Zbb | 3 | `0x0ac7f633` at `0x800e1800` |
| `packh` | Zbkb | 3 | `0x0862f2b3` at `0x800e18d8` |
| `pack` | Zbkb | 3 | `0x094ac933` at `0x800e8fe0` |
| `rev8` | Zbb | 2 | `0x6b86d593` at `0x800e9060` |
| `bext` | Zbs | 2 | `0x49465633` at `0x800e5b68` |
| `bset` | Zbs | 2 | `0x29461633` at `0x800e5b88` |
| `bclri` | Zbs | 1 | `0x4bf51a93` at `0x800e8a34` |
| `clz` | Zbb | 1 | `0x60069793` at `0x8010f910` |
