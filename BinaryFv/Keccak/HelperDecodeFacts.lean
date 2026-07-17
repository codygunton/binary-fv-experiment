import BinaryFv.RiscV.HartPrimitives
import BinaryFv.RiscV.Framing

/-!
# Generated-decoder facts for the memory-helper instruction words

Each theorem states that the generated Sail decoder (`ext_decode`) maps a concrete instruction word
occurring in `memcpy` (0x10d18), `memset` (0x10d3c), or `copy_from_slice_impl` (0x10c44) to its AST
node, exactly as `ext_decode_sd_run` does for the `xor_block` store.  The decoder evaluates
`currentlyEnabled Ext_Zicfilp` before opcode matching (reading `cur_privilege` and, in machine mode,
`mseccfg` via `get_xLPE`); the decoded result is independent of their *values* but the run throws
`Unreachable` when they are absent, so both register-presence hypotheses are required (they hold on
any configured machine).  Every proof is the identical `unfold`/`extDecode_eq`/`simp only`/`rfl`
sequence; no `native_decide`.

The 21 distinct words and their decoded AST nodes are catalogued in each theorem name.  Register
indices follow the ABI: `a0..a5 = x10..x15`, `ra = x1`, `t1 = x6`.
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

/-! ## Shared by memcpy and memset -/

/-- `li a5, 0` = `addi a5, x0, 0` at `0x10d18` / `0x10d3c`. -/
theorem ext_decode_li_a5_0_run :
    Runs (ext_decode (0x00000793 : BitVec 32)) state state
      (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI)) := by decode_run

/-- `bne a5, a2, +8` at `0x10d1c` / `0x10d40` (the copy/set loop test). -/
theorem ext_decode_bne_a5_a2_run :
    Runs (ext_decode (0x00c79463 : BitVec 32)) state state
      (.BTYPE (8#13, .Regidx 12#5, .Regidx 15#5, .BNE)) := by decode_run

/-- `ret` = `jalr x0, 0(ra)` at `0x10d20` / `0x10d44`. -/
theorem ext_decode_ret_run :
    Runs (ext_decode (0x00008067 : BitVec 32)) state state
      (.JALR (0#12, .Regidx 1#5, .Regidx 0#5)) := by decode_run

/-- `add a4, a0, a5` at `0x10d2c` / `0x10d48` (`a4 = dst + i`). -/
theorem ext_decode_add_a4_a0_a5_run :
    Runs (ext_decode (0x00f50733 : BitVec 32)) state state
      (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)) := by decode_run

/-- `addi a5, a5, 1` at `0x10d30` / `0x10d50` (`i++`). -/
theorem ext_decode_addi_a5_a5_1_run :
    Runs (ext_decode (0x00178793 : BitVec 32)) state state
      (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)) := by decode_run

/-! ## memcpy-specific (0x10d18) -/

/-- `add a3, a1, a5` at `0x10d24` (`a3 = src + i`). -/
theorem ext_decode_add_a3_a1_a5_run :
    Runs (ext_decode (0x00f586b3 : BitVec 32)) state state
      (.RTYPE (.Regidx 15#5, .Regidx 11#5, .Regidx 13#5, .ADD)) := by decode_run

/-- `lbu a3, 0(a3)` at `0x10d28` (`a3 = mem[src+i]`). -/
theorem ext_decode_lbu_a3_a3_run :
    Runs (ext_decode (0x0006c683 : BitVec 32)) state state
      (.LOAD (0#12, .Regidx 13#5, .Regidx 13#5, true, 1)) := by decode_run

/-- `sb a3, 0(a4)` at `0x10d34` (`mem[dst+i] = a3`). -/
theorem ext_decode_sb_a3_a4_run :
    Runs (ext_decode (0x00d70023 : BitVec 32)) state state
      (.STORE (0#12, .Regidx 13#5, .Regidx 14#5, 1)) := by decode_run

/-- `j 0x10d1c` at `0x10d38` (back-edge, byte offset `-28`). -/
theorem ext_decode_j_memcpy_run :
    Runs (ext_decode (0xfe5ff06f : BitVec 32)) state state
      (.JAL (0x1FFFE4#21, .Regidx 0#5)) := by decode_run

/-! ## memset-specific (0x10d3c) -/

/-- `sb a1, 0(a4)` at `0x10d4c` (`mem[dst+i] = byteval`). -/
theorem ext_decode_sb_a1_a4_run :
    Runs (ext_decode (0x00b70023 : BitVec 32)) state state
      (.STORE (0#12, .Regidx 11#5, .Regidx 14#5, 1)) := by decode_run

/-- `j 0x10d40` at `0x10d54` (back-edge, byte offset `-20`). -/
theorem ext_decode_j_memset_run :
    Runs (ext_decode (0xfedff06f : BitVec 32)) state state
      (.JAL (0x1FFFEC#21, .Regidx 0#5)) := by decode_run

/-! ## copy_from_slice_impl (0x10c44) -/

/-- `mv a4, a1` = `addi a4, a1, 0` at `0x10c44` (save `dst_len`). -/
theorem ext_decode_mv_a4_a1_run :
    Runs (ext_decode (0x00058713 : BitVec 32)) state state
      (.ITYPE (0#12, .Regidx 11#5, .Regidx 14#5, .ADDI)) := by decode_run

/-- `bne a1, a3, +0x14` at `0x10c48` (length-mismatch test; not taken when `dst_len = src_len`). -/
theorem ext_decode_bne_a1_a3_run :
    Runs (ext_decode (0x00d59a63 : BitVec 32)) state state
      (.BTYPE (20#13, .Regidx 13#5, .Regidx 11#5, .BNE)) := by decode_run

/-- `mv a1, a2` = `addi a1, a2, 0` at `0x10c4c` (`a1 = src_ptr`). -/
theorem ext_decode_mv_a1_a2_run :
    Runs (ext_decode (0x00060593 : BitVec 32)) state state
      (.ITYPE (0#12, .Regidx 12#5, .Regidx 11#5, .ADDI)) := by decode_run

/-- `mv a2, a4` = `addi a2, a4, 0` at `0x10c50` (`a2 = len`). -/
theorem ext_decode_mv_a2_a4_run :
    Runs (ext_decode (0x00070613 : BitVec 32)) state state
      (.ITYPE (0#12, .Regidx 14#5, .Regidx 12#5, .ADDI)) := by decode_run

/-- `auipc t1, 0x0` at `0x10c54`. -/
theorem ext_decode_auipc_t1_run :
    Runs (ext_decode (0x00000317 : BitVec 32)) state state
      (.UTYPE (0#20, .Regidx 6#5, .AUIPC)) := by decode_run

/-- `jr 196(t1)` = `jalr x0, 196(t1)` at `0x10c58` (tail-call `memcpy`, no link). -/
theorem ext_decode_jr_t1_run :
    Runs (ext_decode (0x0c430067 : BitVec 32)) state state
      (.JALR (0xc4#12, .Regidx 6#5, .Regidx 0#5)) := by decode_run

/-- `mv a0, a4` = `addi a0, a4, 0` at `0x10c5c` (panic branch, dead). -/
theorem ext_decode_mv_a0_a4_run :
    Runs (ext_decode (0x00070513 : BitVec 32)) state state
      (.ITYPE (0#12, .Regidx 14#5, .Regidx 10#5, .ADDI)) := by decode_run

/-- `mv a1, a3` = `addi a1, a3, 0` at `0x10c60` (panic branch, dead). -/
theorem ext_decode_mv_a1_a3_run :
    Runs (ext_decode (0x00068593 : BitVec 32)) state state
      (.ITYPE (0#12, .Regidx 13#5, .Regidx 11#5, .ADDI)) := by decode_run

/-- `auipc ra, 0xfffff` at `0x10c64` (panic branch, dead). -/
theorem ext_decode_auipc_ra_run :
    Runs (ext_decode (0xfffff097 : BitVec 32)) state state
      (.UTYPE (0xfffff#20, .Regidx 1#5, .AUIPC)) := by decode_run

/-- `jalr 1164(ra)` at `0x10c68` (call `len_mismatch_fail`, panic branch, dead). -/
theorem ext_decode_jalr_ra_run :
    Runs (ext_decode (0x48c080e7 : BitVec 32)) state state
      (.JALR (0x48c#12, .Regidx 1#5, .Regidx 1#5)) := by decode_run

end BinaryFv.Keccak
