# S12 forms left unsupported: none since S12b

S12 left nine forms open (plan S12 contingency); S12b closed all of them after regenerating
`sail-riscv-lean` (`sail/PROVENANCE.md`).

- `srai`: the generated `shift_bits_right_arith` was `BitVec.rotateRight` because Sail 0.20.1's
  library bound `sail_arith_shiftright` to it for Lean (`srai 1, 1` was `2^63` in the model).
  Fixed by `sail/00-sail-lean-asr.patch` (upstream rems-project/sail 895028208155); the old
  counterexample is now refuted by `decide` (`ZesuExec/Sail/Forms/RegWrite.lean`, after
  `shiftI_srai`). Form: `dec_srai`, `sim_srai`.
- `maxu packh pack rev8 bext bset bclri clz` (Zbb, Zbkb, Zbs): the model had no
  bit-manipulation instructions. The S12b build compiles `Zba;Zbb;Zbs;Zbkb`; `Configured.misa`
  also fixes `misa.B = 1` (Zbb and Zbs are enabled through `B`). Forms: `dec_<form>` in
  `ZesuExec/Sail/Decode.lean`, `sim_<form>` in `ZesuExec/Sail/Forms/Bitmanip.lean`.
