import BinaryFv.RiscV.Instruction.Decode
import BinaryFv.Keccak.Reth.Proof.Store.Decode

/-!
# Generated-decoder facts for the `xor_block` instruction words

Each theorem states that the generated Sail decoder (`ext_decode`) maps a concrete instruction word
occurring in `xor_block` (0x10c6c) to its AST node, exactly as `ext_decode_sd_run` does for the
store.  The decoder evaluates `currentlyEnabled Ext_Zicfilp` before opcode matching (reading
`cur_privilege` and, in machine mode, `mseccfg` via `get_xLPE`); the decoded result is independent of
their *values* but the run throws `Unreachable` when they are absent, so both register-presence
hypotheses are required (they hold on any configured machine).  Every proof is the identical
`unfold`/`extDecode_eq`/`simp only`/`rfl` sequence; no `native_decide`.

The 32 distinct words and their decoded AST nodes are catalogued in each theorem name.  Register
indices follow the ABI: `a0..a7 = x10..x17`, `ra = x1`, `t0 = x5`.  This is the stage-5 mechanical
fetch/decode groundwork for `xor_block`; the `or`/`slli`/`xor` shapes reuse the stage-4-validated
`RTYPE`/`SHIFTIOP` decodes, and `ret`/`sd` re-derive the stage-2/stage-4 words under fresh names.
-/

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

/-- The shared decode-run tactic: unfold the run, rewrite to the backwards decoder, evaluate the
`Ext_Zicfilp` gate against the two register-presence facts, and close by reflexivity. -/
local macro "decode_run" : tactic =>
  `(tactic|
    (unfold Runs
     rw [extDecode_eq]
     simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
       PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
       EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get, *]
     rfl))

variable (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
include privRead mseccfgRead

/-! ## Entry (0x10c6c–0x10c70) -/

/-- `li a2, 136` = `addi a2, x0, 136` at `0x10c6c` (loop count = rate). -/
theorem ext_decode_li_a2_136_run :
    Runs (ext_decode (0x08800613 : BitVec 32)) state state
      (.ITYPE (136#12, .Regidx 0#5, .Regidx 12#5, .ADDI)) := by decode_run

/-- `beqz a2, 0x10ce8` = `beq a2, x0, +0x78` at `0x10c70` (skip loop when count = 0; not taken). -/
theorem ext_decode_beqz_a2_run :
    Runs (ext_decode (0x06060c63 : BitVec 32)) state state
      (.BTYPE (0x78#13, .Regidx 0#5, .Regidx 12#5, .BEQ)) := by decode_run

/-! ## Loop body: low 32 bits (0x10c74–0x10c94) -/

/-- `lbu a3, 1(a1)` at `0x10c74` (`a3 = src[1]`). -/
theorem ext_decode_lbu_a3_a1_1_run :
    Runs (ext_decode (0x0015c683 : BitVec 32)) state state
      (.LOAD (1#12, .Regidx 11#5, .Regidx 13#5, true, 1)) := by decode_run

/-- `lbu a4, 2(a1)` at `0x10c78` (`a4 = src[2]`). -/
theorem ext_decode_lbu_a4_a1_2_run :
    Runs (ext_decode (0x0025c703 : BitVec 32)) state state
      (.LOAD (2#12, .Regidx 11#5, .Regidx 14#5, true, 1)) := by decode_run

/-- `lbu a5, 3(a1)` at `0x10c7c` (`a5 = src[3]`). -/
theorem ext_decode_lbu_a5_a1_3_run :
    Runs (ext_decode (0x0035c783 : BitVec 32)) state state
      (.LOAD (3#12, .Regidx 11#5, .Regidx 15#5, true, 1)) := by decode_run

/-- `lbu a6, 0(a1)` at `0x10c80` (`a6 = src[0]`). -/
theorem ext_decode_lbu_a6_a1_0_run :
    Runs (ext_decode (0x0005c803 : BitVec 32)) state state
      (.LOAD (0#12, .Regidx 11#5, .Regidx 16#5, true, 1)) := by decode_run

/-- `slli a3, a3, 0x8` at `0x10c84` (`a3 = src[1] << 8`). -/
theorem ext_decode_slli_a3_8_run :
    Runs (ext_decode (0x00869693 : BitVec 32)) state state
      (.SHIFTIOP (8#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) := by decode_run

/-- `slli a4, a4, 0x10` at `0x10c88` (`a4 = src[2] << 16`). -/
theorem ext_decode_slli_a4_16_run :
    Runs (ext_decode (0x01071713 : BitVec 32)) state state
      (.SHIFTIOP (16#6, .Regidx 14#5, .Regidx 14#5, .SLLI)) := by decode_run

/-- `slli a5, a5, 0x18` at `0x10c8c` (`a5 = src[3] << 24`). -/
theorem ext_decode_slli_a5_24_run :
    Runs (ext_decode (0x01879793 : BitVec 32)) state state
      (.SHIFTIOP (24#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by decode_run

/-- `or a3, a3, a6` at `0x10c90` (`a3 = src[1]<<8 | src[0]`). -/
theorem ext_decode_or_a3_a3_a6_run :
    Runs (ext_decode (0x0106e6b3 : BitVec 32)) state state
      (.RTYPE (.Regidx 16#5, .Regidx 13#5, .Regidx 13#5, .OR)) := by decode_run

/-- `or a4, a5, a4` at `0x10c94` (`a4 = src[3]<<24 | src[2]<<16`). -/
theorem ext_decode_or_a4_a5_a4_run :
    Runs (ext_decode (0x00e7e733 : BitVec 32)) state state
      (.RTYPE (.Regidx 14#5, .Regidx 15#5, .Regidx 14#5, .OR)) := by decode_run

/-! ## Loop body: high 32 bits (0x10c98–0x10cb8) -/

/-- `lbu a5, 5(a1)` at `0x10c98` (`a5 = src[5]`). -/
theorem ext_decode_lbu_a5_a1_5_run :
    Runs (ext_decode (0x0055c783 : BitVec 32)) state state
      (.LOAD (5#12, .Regidx 11#5, .Regidx 15#5, true, 1)) := by decode_run

/-- `lbu a6, 4(a1)` at `0x10c9c` (`a6 = src[4]`). -/
theorem ext_decode_lbu_a6_a1_4_run :
    Runs (ext_decode (0x0045c803 : BitVec 32)) state state
      (.LOAD (4#12, .Regidx 11#5, .Regidx 16#5, true, 1)) := by decode_run

/-- `lbu a7, 6(a1)` at `0x10ca0` (`a7 = src[6]`). -/
theorem ext_decode_lbu_a7_a1_6_run :
    Runs (ext_decode (0x0065c883 : BitVec 32)) state state
      (.LOAD (6#12, .Regidx 11#5, .Regidx 17#5, true, 1)) := by decode_run

/-- `lbu t0, 7(a1)` at `0x10ca4` (`t0 = src[7]`). -/
theorem ext_decode_lbu_t0_a1_7_run :
    Runs (ext_decode (0x0075c283 : BitVec 32)) state state
      (.LOAD (7#12, .Regidx 11#5, .Regidx 5#5, true, 1)) := by decode_run

/-- `slli a5, a5, 0x8` at `0x10ca8` (`a5 = src[5] << 8`). -/
theorem ext_decode_slli_a5_8_run :
    Runs (ext_decode (0x00879793 : BitVec 32)) state state
      (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by decode_run

/-- `or a5, a5, a6` at `0x10cac` (`a5 = src[5]<<8 | src[4]`). -/
theorem ext_decode_or_a5_a5_a6_run :
    Runs (ext_decode (0x0107e7b3 : BitVec 32)) state state
      (.RTYPE (.Regidx 16#5, .Regidx 15#5, .Regidx 15#5, .OR)) := by decode_run

/-- `slli a7, a7, 0x10` at `0x10cb0` (`a7 = src[6] << 16`). -/
theorem ext_decode_slli_a7_16_run :
    Runs (ext_decode (0x01089893 : BitVec 32)) state state
      (.SHIFTIOP (16#6, .Regidx 17#5, .Regidx 17#5, .SLLI)) := by decode_run

/-- `slli t0, t0, 0x18` at `0x10cb4` (`t0 = src[7] << 24`). -/
theorem ext_decode_slli_t0_24_run :
    Runs (ext_decode (0x01829293 : BitVec 32)) state state
      (.SHIFTIOP (24#6, .Regidx 5#5, .Regidx 5#5, .SLLI)) := by decode_run

/-- `or a6, t0, a7` at `0x10cb8` (`a6 = src[7]<<24 | src[6]<<16`). -/
theorem ext_decode_or_a6_t0_a7_run :
    Runs (ext_decode (0x0112e833 : BitVec 32)) state state
      (.RTYPE (.Regidx 17#5, .Regidx 5#5, .Regidx 16#5, .OR)) := by decode_run

/-! ## Loop body: pointer/count updates, lane assembly, XOR, store (0x10cbc–0x10ce4) -/

/-- `addi a2, a2, -8` at `0x10cbc` (`count -= 8`; `-8` is `0xff8#12`). -/
theorem ext_decode_addi_a2_a2_m8_run :
    Runs (ext_decode (0xff860613 : BitVec 32)) state state
      (.ITYPE (0xff8#12, .Regidx 12#5, .Regidx 12#5, .ADDI)) := by decode_run

/-- `addi a1, a1, 8` at `0x10cc0` (`src += 8`). -/
theorem ext_decode_addi_a1_a1_8_run :
    Runs (ext_decode (0x00858593 : BitVec 32)) state state
      (.ITYPE (8#12, .Regidx 11#5, .Regidx 11#5, .ADDI)) := by decode_run

/-- `or a3, a4, a3` at `0x10cc4` (`a3 = low32 = src[3..0] LE`). -/
theorem ext_decode_or_a3_a4_a3_run :
    Runs (ext_decode (0x00d766b3 : BitVec 32)) state state
      (.RTYPE (.Regidx 13#5, .Regidx 14#5, .Regidx 13#5, .OR)) := by decode_run

/-- `ld a4, 0(a0)` at `0x10cc8` (`a4 = state lane`; signed doubleword load). -/
theorem ext_decode_ld_a4_a0_run :
    Runs (ext_decode (0x00053703 : BitVec 32)) state state
      (.LOAD (0#12, .Regidx 10#5, .Regidx 14#5, false, 8)) := by decode_run

/-- `or a5, a6, a5` at `0x10ccc` (`a5 = high32 = src[7..4] LE`). -/
theorem ext_decode_or_a5_a6_a5_run :
    Runs (ext_decode (0x00f867b3 : BitVec 32)) state state
      (.RTYPE (.Regidx 15#5, .Regidx 16#5, .Regidx 15#5, .OR)) := by decode_run

/-- `slli a5, a5, 0x20` at `0x10cd0` (`a5 <<= 32`). -/
theorem ext_decode_slli_a5_32_run :
    Runs (ext_decode (0x02079793 : BitVec 32)) state state
      (.SHIFTIOP (32#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by decode_run

/-- `or a3, a5, a3` at `0x10cd4` (`a3 = full 64-bit LE input lane`). -/
theorem ext_decode_or_a3_a5_a3_run :
    Runs (ext_decode (0x00d7e6b3 : BitVec 32)) state state
      (.RTYPE (.Regidx 13#5, .Regidx 15#5, .Regidx 13#5, .OR)) := by decode_run

/-- `xor a3, a4, a3` at `0x10cd8` (`a3 = state lane XOR input lane`). -/
theorem ext_decode_xor_a3_a4_a3_run :
    Runs (ext_decode (0x00d746b3 : BitVec 32)) state state
      (.RTYPE (.Regidx 13#5, .Regidx 14#5, .Regidx 13#5, .XOR)) := by decode_run

/-- `sd a3, 0(a0)` at `0x10cdc` (`state lane := a3`; identical to the stage-2 proven store). -/
theorem ext_decode_sd_a3_a0_run :
    Runs (ext_decode (0x00d53023 : BitVec 32)) state state
      (.STORE (0#12, .Regidx 13#5, .Regidx 10#5, 8)) := by decode_run

/-- `addi a0, a0, 8` at `0x10ce0` (`dst += 8`). -/
theorem ext_decode_addi_a0_a0_8_run :
    Runs (ext_decode (0x00850513 : BitVec 32)) state state
      (.ITYPE (8#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) := by decode_run

/-- `bnez a2, 0x10c74` = `bne a2, x0, -0x70` at `0x10ce4` (loop back-edge; `-0x70` is `0x1f90#13`). -/
theorem ext_decode_bnez_a2_run :
    Runs (ext_decode (0xf80618e3 : BitVec 32)) state state
      (.BTYPE (0x1f90#13, .Regidx 0#5, .Regidx 12#5, .BNE)) := by decode_run

/-! ## Return (0x10ce8) -/

/-- `ret` = `jalr x0, 0(ra)` at `0x10ce8`. -/
theorem ext_decode_ret_run :
    Runs (ext_decode (0x00008067 : BitVec 32)) state state
      (.JALR (0#12, .Regidx 1#5, .Regidx 0#5)) := by decode_run

end BinaryFv.Keccak
