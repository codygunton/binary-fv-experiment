import BinaryFv.Keccak.SpecBridge.Lanes
import BinaryFv.Keccak.Reth.Proof.Helpers.Memcpy
import BinaryFv.Keccak.Reth.Proof.XorBlock.Decode
import BinaryFv.Keccak.Reth.Proof.XorBlock.Fetch
import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import Spec.Keccak.Keccak256

/-!
# The `xor_block` (0x10c6c) Keccak absorb loop, proved through the generated `try_step`

`xor_block(state, input, count)` XORs a 136-byte (17-lane) rate block into the Keccak sponge state,
one 64-bit little-endian lane per iteration:

```
0x10c6c li   a2,136          ; count = rate = 136
0x10c70 beqz a2,0x10ce8      ; skip if count == 0 (not taken)
        ; LOOP HEAD 0x10c74 (29-instruction body):
0x10c74 lbu  a3,1(a1)   0x10c78 lbu  a4,2(a1)   0x10c7c lbu  a5,3(a1)   0x10c80 lbu  a6,0(a1)
0x10c84 slli a3,a3,0x8  0x10c88 slli a4,a4,0x10 0x10c8c slli a5,a5,0x18
0x10c90 or   a3,a3,a6   0x10c94 or   a4,a5,a4
0x10c98 lbu  a5,5(a1)   0x10c9c lbu  a6,4(a1)   0x10ca0 lbu  a7,6(a1)   0x10ca4 lbu  t0,7(a1)
0x10ca8 slli a5,a5,0x8  0x10cac or   a5,a5,a6   0x10cb0 slli a7,a7,0x10 0x10cb4 slli t0,t0,0x18
0x10cb8 or   a6,t0,a7
0x10cbc addi a2,a2,-8   0x10cc0 addi a1,a1,8
0x10cc4 or   a3,a4,a3   0x10cc8 ld   a4,0(a0)   0x10ccc or   a5,a6,a5
0x10cd0 slli a5,a5,0x20 0x10cd4 or   a3,a5,a3   0x10cd8 xor  a3,a4,a3
0x10cdc sd   a3,0(a0)   0x10ce0 addi a0,a0,8   0x10ce4 bnez a2,0x10c74
0x10ce8 ret
```

The 8 `lbu` + 6 `slli` + 6 `or` assemble the 8 input bytes into the 64-bit little-endian lane
(`leWord`); the `ld` reads the state lane, `xor` XORs, `sd` writes the lane back.  The genuine
platform / data-access preconditions (fetch, `phys_access_check`, MMIO, byte ownership) are carried
abstractly in the loop invariant, exactly the stage-2 trust boundary established by memcpy.  This
file reuses the register-agnostic framing helpers proved in `MemcpyContract`.
-/

namespace BinaryFv.Keccak.XorBlock

open BinaryFv.Binary
open BinaryFv.Keccak.SpecBridge

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open BinaryFv.Keccak
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Deliverable 1a: the `xor` execute contract

`execute_RTYPE rs2 rs1 rd XOR` computes `rs1 ^^^ rs2`, mirroring `execute_RTYPE_or_run`. -/

theorem execute_RTYPE_xor_run (state sFinal : State) (rs2 rs1 rd : regidx)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (rs1Val ^^^ rs2Val)) state sFinal ()) :
    Runs (execute_RTYPE rs2 rs1 rd .XOR) state sFinal (.Retire_Success ()) := by
  unfold execute_RTYPE
  refine Runs.bind (Runs.bind hrs1 (Runs.bind hrs2 rfl)) ?_
  refine Runs.bind hwrite ?_
  rfl

/-! ## Deliverable 1b: register read/write reductions

The body reads/writes the ABI registers `t0 = x5`, `a0..a7 = x10..x17`.  Each `rX_bits`/`wX_bits`
reduction is the memcpy pattern specialized to the concrete register index, generated uniformly by a
local macro. -/

local macro "gen_reg_lemmas" idx:num " ↦ " reg:ident " , " rname:ident " , " wname:ident : command =>
  `(theorem $rname (s : State) (v : BitVec 64) (h : s.regs.get? $reg = some v) :
      Runs (rX_bits (.Regidx (BitVec.ofNat 5 $idx))) s s v := by
    have rk : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [rX_bits, rX, rk, h, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
      regval_from_reg]

  theorem $wname (s : State) (data : BitVec 64) :
      Runs (wX_bits (.Regidx (BitVec.ofNat 5 $idx)) data) s
        { s with regs := s.regs.insert $reg data } () := by
    have rk : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [wX_bits, wX, PreSail.writeReg, rk, EStateM.run, EStateM.bind, EStateM.modifyGet,
      EStateM.pure, EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet, modify,
      xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
      encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
      LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg])

gen_reg_lemmas 5 ↦ x5 , rX_x5_run , wX_x5_run
gen_reg_lemmas 10 ↦ x10 , rX_x10_run , wX_x10_run
gen_reg_lemmas 11 ↦ x11 , rX_x11_run , wX_x11_run
gen_reg_lemmas 12 ↦ x12 , rX_x12_run , wX_x12_run
gen_reg_lemmas 13 ↦ x13 , rX_x13_run , wX_x13_run
gen_reg_lemmas 14 ↦ x14 , rX_x14_run , wX_x14_run
gen_reg_lemmas 15 ↦ x15 , rX_x15_run , wX_x15_run
gen_reg_lemmas 16 ↦ x16 , rX_x16_run , wX_x16_run
gen_reg_lemmas 17 ↦ x17 , rX_x17_run , wX_x17_run

/-! ## Deliverable 1c: normalizing the generated shift amount

The generated `SLLI` write value is `shift_bits_left x (extractLsb sh (log2_xlen -i 1) 0)`; on RV64
`log2_xlen = 6`, so the shift count is the low 6 bits of the 6-bit immediate `sh` — i.e. `sh` itself.
This normalizes it to the plain `x <<< sh.toNat`. -/

theorem slli_amount (x : BitVec 64) (sh : BitVec 6) :
    Sail.shift_bits_left x
      (Sail.BitVec.extractLsb sh (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
      = x <<< sh.toNat := by
  have hhi : (LeanRV64DExecutable.Functions.log2_xlen -i 1) = 5 := rfl
  rw [hhi]
  unfold Sail.shift_bits_left Sail.BitVec.extractLsb
  bv_decide

/-! ## Deliverable 3: the little-endian byte-assembly bridge

The 8 `lbu` + 6 `slli` + 6 `or` compose the 8 input bytes into the 64-bit little-endian lane, which
is exactly `SepLogic.leWord` of those bytes.  This is a pure `BitVec` identity (`bv_decide`) over the
zero-extended, shifted, and or-ed bytes, structured to match the exact association the machine
produces (`low32 = a4|||a3`, `high32 = a6|||a5`, lane `= (high32 <<< 32) ||| low32`). -/

theorem assemble_leWord (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((zero_extend (m := 64) b7 <<< 24 ||| zero_extend (m := 64) b6 <<< 16) |||
        (zero_extend (m := 64) b5 <<< 8 ||| zero_extend (m := 64) b4)) <<< 32) |||
      ((zero_extend (m := 64) b3 <<< 24 ||| zero_extend (m := 64) b2 <<< 16) |||
        (zero_extend (m := 64) b1 <<< 8 ||| zero_extend (m := 64) b0)))
      = BitVec.cast (by rfl) (leWord [b0, b1, b2, b3, b4, b5, b6, b7]) := by
  simp only [leWord, List.length_cons, List.length_nil, zero_extend, Sail.BitVec.zeroExtend]
  bv_decide

/-- Concrete shift-by-8. -/
theorem slli_amt8 (x : BitVec 64) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (8#6)
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) = x <<< 8 := by
  have hhi : (LeanRV64DExecutable.Functions.log2_xlen -i 1) = 5 := rfl
  rw [hhi]; unfold Sail.shift_bits_left Sail.BitVec.extractLsb; bv_decide

/-- Concrete shift-by-16. -/
theorem slli_amt16 (x : BitVec 64) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (16#6)
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) = x <<< 16 := by
  have hhi : (LeanRV64DExecutable.Functions.log2_xlen -i 1) = 5 := rfl
  rw [hhi]; unfold Sail.shift_bits_left Sail.BitVec.extractLsb; bv_decide

/-- Concrete shift-by-24. -/
theorem slli_amt24 (x : BitVec 64) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (24#6)
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) = x <<< 24 := by
  have hhi : (LeanRV64DExecutable.Functions.log2_xlen -i 1) = 5 := rfl
  rw [hhi]; unfold Sail.shift_bits_left Sail.BitVec.extractLsb; bv_decide

/-- Concrete shift-by-32. -/
theorem slli_amt32 (x : BitVec 64) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (32#6)
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) = x <<< 32 := by
  have hhi : (LeanRV64DExecutable.Functions.log2_xlen -i 1) = 5 := rfl
  rw [hhi]; unfold Sail.shift_bits_left Sail.BitVec.extractLsb; bv_decide

/-! ## Framing infrastructure specialized to the `xor_block` write set

The loop body may write `PC`, `nextPC`, `minstret`, `minstret_increment`, and the GPRs
`t0 = x5`, `a0..a7 = x10..x17`.  Everything outside this set (`W`) is stable; `StableAgree`-equal
states carry the abstract platform / data-access premises across the body's register writes. -/

/-- Registers the `xor_block` loop body does not write. -/
@[reducible] def NonW (r : Register) : Prop :=
  r ≠ PC ∧ r ≠ nextPC ∧ r ≠ minstret ∧ r ≠ minstret_increment ∧
    r ≠ x5 ∧ r ≠ x10 ∧ r ≠ x11 ∧ r ≠ x12 ∧ r ≠ x13 ∧ r ≠ x14 ∧ r ≠ x15 ∧ r ≠ x16 ∧ r ≠ x17

/-- Two states agree on every register the loop body does not write. -/
def StableAgree (base t : State) : Prop := Agree NonW base t

theorem StableAgree.refl (s : State) : StableAgree s s := Agree.refl s

theorem StableAgree.trans {a b c : State} (h1 : StableAgree a b) (h2 : StableAgree b c) :
    StableAgree a c := fun r hr => (h2 r hr).trans (h1 r hr)

/-! ### Private register-file framing helpers (redefined; the `MemcpyContract` originals are private) -/

private theorem coreNextPc (Y : State) (pc : BitVec 64) :
    (coreControlFlowNextState Y pc).regs.get? nextPC = some (Sail.BitVec.addInt pc 4) := by
  change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
  rw [Std.ExtDHashMap.get?_insert]; simp

private theorem coreGetInc (Y : State) (pc : BitVec 64) (r : Register) (hnp : r ≠ nextPC) :
    (coreControlFlowNextState Y pc).regs.get? r = Y.regs.get? r := by
  simpa [coreControlFlowNextState] using
    writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

private theorem gpFrameNextPc (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (hrd : nextPC ≠ rd) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC =
      some (Sail.BitVec.addInt pc 4) := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC
      = (coreControlFlowNextState Y pc).regs.get? nextPC :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd nextPC v hrd
    _ = some (Sail.BitVec.addInt pc 4) := coreNextPc Y pc

private theorem gpFrameGet (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (r : Register) (hrd : r ≠ rd) (hnp : r ≠ nextPC) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? r = Y.regs.get? r := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? r
      = (coreControlFlowNextState Y pc).regs.get? r :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd r v hrd
    _ = Y.regs.get? r := coreGetInc Y pc r hnp

/-- Bridge a stable register read through the counter-increment and `nextPC` writes of the execute
state, back to a `StableAgree`-equal base. -/
theorem coreGetStable {s : State} (s_k : State) (pc : BitVec 64) (r : Register) (hr : NonW r)
    (hSt : StableAgree s s_k) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s_k) pc).regs.get? r =
      s.regs.get? r := by
  rw [coreGetInc (tryStepControlFlowAfterIncrement s_k) pc r hr.2.1,
    afterIncGet s_k r hr.2.2.2.1]
  exact hSt r hr

theorem coreStableAgree {s : State} (s_k : State) (pc : BitVec 64) (hSt : StableAgree s s_k) :
    StableAgree s (coreControlFlowNextState (tryStepControlFlowAfterIncrement s_k) pc) :=
  fun r hr => coreGetStable s_k pc r hr hSt

/-! ### The generic fall-through GP-register step

Any body instruction whose `execute` retires writing a single GPR `rd := v` (the `slli`/`or`/`addi`/
`xor` ALU ops and the `lbu`/`ld` loads) is lifted through the generated `try_step` by
`tryStepFallThroughRetires` plus the four register-file frame facts. -/

theorem gpStep (stepNo : Nat) (state : State) (pc retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (inst : instruction)
    (rd : Register) (v : RegisterType rd)
    (plat : StepPlatform state pc b0 b1 b2 b3 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (base : BaseInstructionEncoding b0)
    (decode : Runs (ext_decode (fetchWord b0 b1 b2 b3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) inst)
    (exec : Runs (execute inst)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
          rd v }
      (.Retire_Success ()))
    (hnp : nextPC ≠ rd) (hhart : hart_state ≠ rd) (hminc : minstret_increment ≠ rd)
    (hmin : minstret ≠ rd) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
            rd v }
        (Sail.BitVec.addInt pc 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, _privRead, _mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  exact tryStepFallThroughRetires stepNo state _ pc retired inhibit config
    b0 b1 b2 b3 inst platform noMMIO bytes interrupts base decode notExpected exec
    (gpFrameNextPc _ _ rd _ hnp)
    (gpFrameGet _ _ rd _ hart_state hhart (by decide))
    (gpFrameGet _ _ rd _ minstret_increment hminc (by decide))
    (gpFrameGet _ _ rd _ minstret hmin (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ### Execute-dispatch builders for the register-only body ops

Each reduces `execute (.SHIFTIOP/.RTYPE/.ITYPE …)` to the single-`insert` post-state from the
generated execute contracts, threading the register reads and write.  The `slli` builder normalizes
the generated `shift_bits_left … (extractLsb …)` to the plain `x <<< shamt.toNat` via `slli_amount`. -/

theorem slliExec (core sFinal : State) (r : BitVec 5) (shamt : BitVec 6) (rVal : BitVec 64)
    (hread : Runs (rX_bits (.Regidx r)) core core rVal)
    (hwrite : Runs (wX_bits (.Regidx r) (rVal <<< shamt.toNat)) core sFinal ()) :
    Runs (execute (.SHIFTIOP (shamt, .Regidx r, .Regidx r, .SLLI))) core sFinal
      (.Retire_Success ()) := by
  change Runs (execute_SHIFTIOP shamt (.Regidx r) (.Regidx r) .SLLI) _ _ _
  refine execute_SHIFTIOP_slli_run core sFinal shamt (.Regidx r) (.Regidx r) rVal hread ?_
  rw [slli_amount]; exact hwrite

theorem orExec (core sFinal : State) (rs2 rs1 rd : BitVec 5) (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits (.Regidx rs1)) core core rs1Val)
    (hrs2 : Runs (rX_bits (.Regidx rs2)) core core rs2Val)
    (hwrite : Runs (wX_bits (.Regidx rd) (rs1Val ||| rs2Val)) core sFinal ()) :
    Runs (execute (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR))) core sFinal
      (.Retire_Success ()) := by
  change Runs (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .OR) _ _ _
  exact execute_RTYPE_or_run core sFinal (.Regidx rs2) (.Regidx rs1) (.Regidx rd)
    rs1Val rs2Val hrs1 hrs2 hwrite

theorem xorExec (core sFinal : State) (rs2 rs1 rd : BitVec 5) (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits (.Regidx rs1)) core core rs1Val)
    (hrs2 : Runs (rX_bits (.Regidx rs2)) core core rs2Val)
    (hwrite : Runs (wX_bits (.Regidx rd) (rs1Val ^^^ rs2Val)) core sFinal ()) :
    Runs (execute (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .XOR))) core sFinal
      (.Retire_Success ()) := by
  change Runs (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .XOR) _ _ _
  exact execute_RTYPE_xor_run core sFinal (.Regidx rs2) (.Regidx rs1) (.Regidx rd)
    rs1Val rs2Val hrs1 hrs2 hwrite

theorem addiExec (core sFinal : State) (imm : BitVec 12) (r : BitVec 5) (rVal : BitVec 64)
    (hr : Runs (rX_bits (.Regidx r)) core core rVal)
    (hwrite : Runs (wX_bits (.Regidx r) (rVal + sign_extend (m := 64) imm)) core sFinal ()) :
    Runs (execute (.ITYPE (imm, .Regidx r, .Regidx r, .ADDI))) core sFinal (.Retire_Success ()) := by
  change Runs (execute_ITYPE imm (.Regidx r) (.Regidx r) .ADDI) _ _ _
  exact execute_ITYPE_addi_run core sFinal imm (.Regidx r) (.Regidx r) rVal hr hwrite

/-! ## Deliverable 2a: register-only body step lemmas (slli / or / xor / addi) -/

theorem step_slli_10c84 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c84) 0x93#8 0x96#8 0x86#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c84)).regs.get? x13 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c84)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c84)).regs.insert x13 (v1 <<< 8) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c84) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x96#8 0x86#8 0x00#8 = (0x00869693 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x96#8 0x86#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (8#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a3_8_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c84)) _ (13#5) (8#6) v1
    (rX_x13_run _ v1 hv1) (wX_x13_run _ (v1 <<< (8#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c84) retired mseccfgBits inhibit config
    0x93#8 0x96#8 0x86#8 0x00#8 (.SHIFTIOP (8#6, .Regidx 13#5, .Regidx 13#5, .SLLI))
    x13 (v1 <<< 8) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10c88 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c88) 0x13#8 0x17#8 0x07#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c88)).regs.get? x14 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c88)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c88)).regs.insert x14 (v1 <<< 16) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c88) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x13#8 0x17#8 0x07#8 0x01#8 = (0x01071713 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x17#8 0x07#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (16#6, .Regidx 14#5, .Regidx 14#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a4_16_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c88)) _ (14#5) (16#6) v1
    (rX_x14_run _ v1 hv1) (wX_x14_run _ (v1 <<< (16#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c88) retired mseccfgBits inhibit config
    0x13#8 0x17#8 0x07#8 0x01#8 (.SHIFTIOP (16#6, .Regidx 14#5, .Regidx 14#5, .SLLI))
    x14 (v1 <<< 16) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10c8c (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c8c) 0x93#8 0x97#8 0x87#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c8c)).regs.get? x15 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c8c)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c8c)).regs.insert x15 (v1 <<< 24) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c8c) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x97#8 0x87#8 0x01#8 = (0x01879793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x97#8 0x87#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (24#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a5_24_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c8c)) _ (15#5) (24#6) v1
    (rX_x15_run _ v1 hv1) (wX_x15_run _ (v1 <<< (24#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c8c) retired mseccfgBits inhibit config
    0x93#8 0x97#8 0x87#8 0x01#8 (.SHIFTIOP (24#6, .Regidx 15#5, .Regidx 15#5, .SLLI))
    x15 (v1 <<< 24) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10ca8 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ca8) 0x93#8 0x97#8 0x87#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca8)).regs.get? x15 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca8)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca8)).regs.insert x15 (v1 <<< 8) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca8) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x97#8 0x87#8 0x00#8 = (0x00879793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x97#8 0x87#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a5_8_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca8)) _ (15#5) (8#6) v1
    (rX_x15_run _ v1 hv1) (wX_x15_run _ (v1 <<< (8#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10ca8) retired mseccfgBits inhibit config
    0x93#8 0x97#8 0x87#8 0x00#8 (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI))
    x15 (v1 <<< 8) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10cb0 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cb0) 0x93#8 0x98#8 0x08#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb0)).regs.get? x17 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb0)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb0)).regs.insert x17 (v1 <<< 16) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb0) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x98#8 0x08#8 0x01#8 = (0x01089893 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x98#8 0x08#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (16#6, .Regidx 17#5, .Regidx 17#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a7_16_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb0)) _ (17#5) (16#6) v1
    (rX_x17_run _ v1 hv1) (wX_x17_run _ (v1 <<< (16#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cb0) retired mseccfgBits inhibit config
    0x93#8 0x98#8 0x08#8 0x01#8 (.SHIFTIOP (16#6, .Regidx 17#5, .Regidx 17#5, .SLLI))
    x17 (v1 <<< 16) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10cb4 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cb4) 0x93#8 0x92#8 0x82#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb4)).regs.get? x5 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb4)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb4)).regs.insert x5 (v1 <<< 24) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb4) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x92#8 0x82#8 0x01#8 = (0x01829293 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x92#8 0x82#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (24#6, .Regidx 5#5, .Regidx 5#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_t0_24_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb4)) _ (5#5) (24#6) v1
    (rX_x5_run _ v1 hv1) (wX_x5_run _ (v1 <<< (24#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cb4) retired mseccfgBits inhibit config
    0x93#8 0x92#8 0x82#8 0x01#8 (.SHIFTIOP (24#6, .Regidx 5#5, .Regidx 5#5, .SLLI))
    x5 (v1 <<< 24) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_slli_10cd0 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cd0) 0x93#8 0x97#8 0x07#8 0x02#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd0)).regs.get? x15 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd0)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd0)).regs.insert x15 (v1 <<< 32) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd0) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x97#8 0x07#8 0x02#8 = (0x02079793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x97#8 0x07#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (32#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by
    rw [wordEq]; exact ext_decode_slli_a5_32_run _ privRead mseccfgBits mseccfgRead
  have exec := slliExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd0)) _ (15#5) (32#6) v1
    (rX_x15_run _ v1 hv1) (wX_x15_run _ (v1 <<< (32#6).toNat))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cd0) retired mseccfgBits inhibit config
    0x93#8 0x97#8 0x07#8 0x02#8 (.SHIFTIOP (32#6, .Regidx 15#5, .Regidx 15#5, .SLLI))
    x15 (v1 <<< 32) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10c90 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c90) 0xb3#8 0xe6#8 0x06#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c90)).regs.get? x13 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c90)).regs.get? x16 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c90)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c90)).regs.insert x13 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c90) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0xe6#8 0x06#8 0x01#8 = (0x0106e6b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe6#8 0x06#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 16#5, .Regidx 13#5, .Regidx 13#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a3_a3_a6_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c90)) _ (16#5) (13#5) (13#5) v1 v2
    (rX_x13_run _ v1 hv1) (rX_x16_run _ v2 hv2) (wX_x13_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c90) retired mseccfgBits inhibit config
    0xb3#8 0xe6#8 0x06#8 0x01#8 (.RTYPE (.Regidx 16#5, .Regidx 13#5, .Regidx 13#5, .OR))
    x13 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10c94 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c94) 0x33#8 0xe7#8 0xe7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c94)).regs.get? x15 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c94)).regs.get? x14 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c94)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c94)).regs.insert x14 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c94) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x33#8 0xe7#8 0xe7#8 0x00#8 = (0x00e7e733 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0xe7#8 0xe7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 14#5, .Regidx 15#5, .Regidx 14#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a4_a5_a4_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c94)) _ (14#5) (15#5) (14#5) v1 v2
    (rX_x15_run _ v1 hv1) (rX_x14_run _ v2 hv2) (wX_x14_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c94) retired mseccfgBits inhibit config
    0x33#8 0xe7#8 0xe7#8 0x00#8 (.RTYPE (.Regidx 14#5, .Regidx 15#5, .Regidx 14#5, .OR))
    x14 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10cac (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cac) 0xb3#8 0xe7#8 0x07#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cac)).regs.get? x15 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cac)).regs.get? x16 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cac)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cac)).regs.insert x15 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cac) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0xe7#8 0x07#8 0x01#8 = (0x0107e7b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe7#8 0x07#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 16#5, .Regidx 15#5, .Regidx 15#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a5_a5_a6_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cac)) _ (16#5) (15#5) (15#5) v1 v2
    (rX_x15_run _ v1 hv1) (rX_x16_run _ v2 hv2) (wX_x15_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cac) retired mseccfgBits inhibit config
    0xb3#8 0xe7#8 0x07#8 0x01#8 (.RTYPE (.Regidx 16#5, .Regidx 15#5, .Regidx 15#5, .OR))
    x15 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10cb8 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cb8) 0x33#8 0xe8#8 0x12#8 0x01#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb8)).regs.get? x5 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb8)).regs.get? x17 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb8)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb8)).regs.insert x16 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb8) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x33#8 0xe8#8 0x12#8 0x01#8 = (0x0112e833 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0xe8#8 0x12#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 17#5, .Regidx 5#5, .Regidx 16#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a6_t0_a7_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cb8)) _ (17#5) (5#5) (16#5) v1 v2
    (rX_x5_run _ v1 hv1) (rX_x17_run _ v2 hv2) (wX_x16_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cb8) retired mseccfgBits inhibit config
    0x33#8 0xe8#8 0x12#8 0x01#8 (.RTYPE (.Regidx 17#5, .Regidx 5#5, .Regidx 16#5, .OR))
    x16 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10cc4 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cc4) 0xb3#8 0x66#8 0xd7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc4)).regs.get? x14 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc4)).regs.get? x13 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc4)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc4)).regs.insert x13 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc4) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0x66#8 0xd7#8 0x00#8 = (0x00d766b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x66#8 0xd7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 13#5, .Regidx 14#5, .Regidx 13#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a3_a4_a3_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc4)) _ (13#5) (14#5) (13#5) v1 v2
    (rX_x14_run _ v1 hv1) (rX_x13_run _ v2 hv2) (wX_x13_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cc4) retired mseccfgBits inhibit config
    0xb3#8 0x66#8 0xd7#8 0x00#8 (.RTYPE (.Regidx 13#5, .Regidx 14#5, .Regidx 13#5, .OR))
    x13 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10ccc (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ccc) 0xb3#8 0x67#8 0xf8#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ccc)).regs.get? x16 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ccc)).regs.get? x15 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ccc)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ccc)).regs.insert x15 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ccc) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0x67#8 0xf8#8 0x00#8 = (0x00f867b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x67#8 0xf8#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 16#5, .Regidx 15#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a5_a6_a5_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ccc)) _ (15#5) (16#5) (15#5) v1 v2
    (rX_x16_run _ v1 hv1) (rX_x15_run _ v2 hv2) (wX_x15_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10ccc) retired mseccfgBits inhibit config
    0xb3#8 0x67#8 0xf8#8 0x00#8 (.RTYPE (.Regidx 15#5, .Regidx 16#5, .Regidx 15#5, .OR))
    x15 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_or_10cd4 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cd4) 0xb3#8 0xe6#8 0xd7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd4)).regs.get? x15 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd4)).regs.get? x13 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd4)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd4)).regs.insert x13 (v1 ||| v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd4) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0xe6#8 0xd7#8 0x00#8 = (0x00d7e6b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0xe6#8 0xd7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 13#5, .Regidx 15#5, .Regidx 13#5, .OR)) := by
    rw [wordEq]; exact ext_decode_or_a3_a5_a3_run _ privRead mseccfgBits mseccfgRead
  have exec := orExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd4)) _ (13#5) (15#5) (13#5) v1 v2
    (rX_x15_run _ v1 hv1) (rX_x13_run _ v2 hv2) (wX_x13_run _ (v1 ||| v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cd4) retired mseccfgBits inhibit config
    0xb3#8 0xe6#8 0xd7#8 0x00#8 (.RTYPE (.Regidx 13#5, .Regidx 15#5, .Regidx 13#5, .OR))
    x13 (v1 ||| v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_xor_10cd8 (stepNo : Nat) (state : State) (v1 v2 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cd8) 0xb3#8 0x46#8 0xd7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd8)).regs.get? x14 = some v1)
    (hv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd8)).regs.get? x13 = some v2) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd8)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd8)).regs.insert x13 (v1 ^^^ v2) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd8) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0xb3#8 0x46#8 0xd7#8 0x00#8 = (0x00d746b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x46#8 0xd7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 13#5, .Regidx 14#5, .Regidx 13#5, .XOR)) := by
    rw [wordEq]; exact ext_decode_xor_a3_a4_a3_run _ privRead mseccfgBits mseccfgRead
  have exec := xorExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cd8)) _ (13#5) (14#5) (13#5) v1 v2
    (rX_x14_run _ v1 hv1) (rX_x13_run _ v2 hv2) (wX_x13_run _ (v1 ^^^ v2))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cd8) retired mseccfgBits inhibit config
    0xb3#8 0x46#8 0xd7#8 0x00#8 (.RTYPE (.Regidx 13#5, .Regidx 14#5, .Regidx 13#5, .XOR))
    x13 (v1 ^^^ v2) plat counters (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_addi_10cbc (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cbc) 0x13#8 0x06#8 0x86#8 0xff#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cbc)).regs.get? x12 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cbc)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cbc)).regs.insert x12 (v1 + sign_extend (m := 64) 0xff8#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cbc) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x13#8 0x06#8 0x86#8 0xff#8 = (0xff860613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x86#8 0xff#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0xff8#12, .Regidx 12#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_addi_a2_a2_m8_run _ privRead mseccfgBits mseccfgRead
  have exec := addiExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cbc)) _ (0xff8#12) (12#5) v1
    (rX_x12_run _ v1 hv1) (wX_x12_run _ (v1 + sign_extend (m := 64) 0xff8#12))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cbc) retired mseccfgBits inhibit config
    0x13#8 0x06#8 0x86#8 0xff#8 (.ITYPE (0xff8#12, .Regidx 12#5, .Regidx 12#5, .ADDI))
    x12 (v1 + sign_extend (m := 64) 0xff8#12) plat counters
    (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_addi_10cc0 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10cc0) 0x93#8 0x85#8 0x85#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc0)).regs.get? x11 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc0)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc0)).regs.insert x11 (v1 + sign_extend (m := 64) 8#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc0) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x93#8 0x85#8 0x85#8 0x00#8 = (0x00858593 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x85#8 0x85#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (8#12, .Regidx 11#5, .Regidx 11#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_addi_a1_a1_8_run _ privRead mseccfgBits mseccfgRead
  have exec := addiExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10cc0)) _ (8#12) (11#5) v1
    (rX_x11_run _ v1 hv1) (wX_x11_run _ (v1 + sign_extend (m := 64) 8#12))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10cc0) retired mseccfgBits inhibit config
    0x93#8 0x85#8 0x85#8 0x00#8 (.ITYPE (8#12, .Regidx 11#5, .Regidx 11#5, .ADDI))
    x11 (v1 + sign_extend (m := 64) 8#12) plat counters
    (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

theorem step_addi_10ce0 (stepNo : Nat) (state : State) (v1 retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ce0) 0x13#8 0x05#8 0x85#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hv1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce0)).regs.get? x10 = some v1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce0)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce0)).regs.insert x10 (v1 + sign_extend (m := 64) 8#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce0) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x13#8 0x05#8 0x85#8 0x00#8 = (0x00850513 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x85#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (8#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_addi_a0_a0_8_run _ privRead mseccfgBits mseccfgRead
  have exec := addiExec (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce0)) _ (8#12) (10#5) v1
    (rX_x10_run _ v1 hv1) (wX_x10_run _ (v1 + sign_extend (m := 64) 8#12))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10ce0) retired mseccfgBits inhibit config
    0x13#8 0x05#8 0x85#8 0x00#8 (.ITYPE (8#12, .Regidx 10#5, .Regidx 10#5, .ADDI))
    x10 (v1 + sign_extend (m := 64) 8#12) plat counters
    (by unfold BaseInstructionEncoding; decide) decode exec
    (by decide) (by decide) (by decide) (by decide)

/-! ## Deliverable 2b: memory body step lemmas (`lbu` / `ld` / `sd`)

The load/store data-access preconditions — effective-address resolution, alignment, byte ownership,
`phys_access_check`, MMIO decision, and the physical read/write — are carried abstractly, exactly the
stage-2 trust boundary. -/

/-- `lbu` at 0x10c74 into `x13` from `1(a1)`. -/
theorem step_lbu_10c74 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c74) 0x83#8 0xc6#8 0x15#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 1#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)).regs.insert x13 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c74) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x83#8 0xc6#8 0x15#8 0x00#8 = (0x0015c683 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc6#8 0x15#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (1#12, .Regidx 11#5, .Regidx 13#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a3_a1_1_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (1#12, .Regidx 11#5, .Regidx 13#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)).regs.insert x13 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 1#12 (.Regidx 11#5) (.Regidx 13#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 1#12 (.Regidx 11#5) (.Regidx 13#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x13_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c74) retired mseccfgBits inhibit config
    0x83#8 0xc6#8 0x15#8 0x00#8 (.LOAD (1#12, .Regidx 11#5, .Regidx 13#5, true, 1))
    x13 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10c78 into `x14` from `2(a1)`. -/
theorem step_lbu_10c78 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c78) 0x03#8 0xc7#8 0x25#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 2#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)).regs.insert x14 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c78) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x03#8 0xc7#8 0x25#8 0x00#8 = (0x0025c703 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc7#8 0x25#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (2#12, .Regidx 11#5, .Regidx 14#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a4_a1_2_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (2#12, .Regidx 11#5, .Regidx 14#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)).regs.insert x14 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 2#12 (.Regidx 11#5) (.Regidx 14#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 2#12 (.Regidx 11#5) (.Regidx 14#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x14_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c78) retired mseccfgBits inhibit config
    0x03#8 0xc7#8 0x25#8 0x00#8 (.LOAD (2#12, .Regidx 11#5, .Regidx 14#5, true, 1))
    x14 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10c7c into `x15` from `3(a1)`. -/
theorem step_lbu_10c7c (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c7c) 0x83#8 0xc7#8 0x35#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 3#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)).regs.insert x15 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c7c) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x83#8 0xc7#8 0x35#8 0x00#8 = (0x0035c783 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc7#8 0x35#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (3#12, .Regidx 11#5, .Regidx 15#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a5_a1_3_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (3#12, .Regidx 11#5, .Regidx 15#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)).regs.insert x15 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 3#12 (.Regidx 11#5) (.Regidx 15#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 3#12 (.Regidx 11#5) (.Regidx 15#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x15_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c7c) retired mseccfgBits inhibit config
    0x83#8 0xc7#8 0x35#8 0x00#8 (.LOAD (3#12, .Regidx 11#5, .Regidx 15#5, true, 1))
    x15 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10c80 into `x16` from `0(a1)`. -/
theorem step_lbu_10c80 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c80) 0x03#8 0xc8#8 0x05#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 0#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)).regs.insert x16 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c80) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x03#8 0xc8#8 0x05#8 0x00#8 = (0x0005c803 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc8#8 0x05#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0#12, .Regidx 11#5, .Regidx 16#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a6_a1_0_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (0#12, .Regidx 11#5, .Regidx 16#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)).regs.insert x16 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 0#12 (.Regidx 11#5) (.Regidx 16#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 0#12 (.Regidx 11#5) (.Regidx 16#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x16_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c80) retired mseccfgBits inhibit config
    0x03#8 0xc8#8 0x05#8 0x00#8 (.LOAD (0#12, .Regidx 11#5, .Regidx 16#5, true, 1))
    x16 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10c98 into `x15` from `5(a1)`. -/
theorem step_lbu_10c98 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c98) 0x83#8 0xc7#8 0x55#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 5#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)).regs.insert x15 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c98) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x83#8 0xc7#8 0x55#8 0x00#8 = (0x0055c783 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc7#8 0x55#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (5#12, .Regidx 11#5, .Regidx 15#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a5_a1_5_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (5#12, .Regidx 11#5, .Regidx 15#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)).regs.insert x15 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 5#12 (.Regidx 11#5) (.Regidx 15#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 5#12 (.Regidx 11#5) (.Regidx 15#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x15_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c98) retired mseccfgBits inhibit config
    0x83#8 0xc7#8 0x55#8 0x00#8 (.LOAD (5#12, .Regidx 11#5, .Regidx 15#5, true, 1))
    x15 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10c9c into `x16` from `4(a1)`. -/
theorem step_lbu_10c9c (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c9c) 0x03#8 0xc8#8 0x45#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 4#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)).regs.insert x16 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c9c) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x03#8 0xc8#8 0x45#8 0x00#8 = (0x0045c803 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc8#8 0x45#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (4#12, .Regidx 11#5, .Regidx 16#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a6_a1_4_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (4#12, .Regidx 11#5, .Regidx 16#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)).regs.insert x16 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 4#12 (.Regidx 11#5) (.Regidx 16#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 4#12 (.Regidx 11#5) (.Regidx 16#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x16_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c9c) retired mseccfgBits inhibit config
    0x03#8 0xc8#8 0x45#8 0x00#8 (.LOAD (4#12, .Regidx 11#5, .Regidx 16#5, true, 1))
    x16 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10ca0 into `x17` from `6(a1)`. -/
theorem step_lbu_10ca0 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ca0) 0x83#8 0xc8#8 0x65#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 6#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)).regs.insert x17 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca0) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x83#8 0xc8#8 0x65#8 0x00#8 = (0x0065c883 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc8#8 0x65#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (6#12, .Regidx 11#5, .Regidx 17#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a7_a1_6_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (6#12, .Regidx 11#5, .Regidx 17#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)).regs.insert x17 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 6#12 (.Regidx 11#5) (.Regidx 17#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 6#12 (.Regidx 11#5) (.Regidx 17#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x17_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10ca0) retired mseccfgBits inhibit config
    0x83#8 0xc8#8 0x65#8 0x00#8 (.LOAD (6#12, .Regidx 11#5, .Regidx 17#5, true, 1))
    x17 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10ca4 into `x5` from `7(a1)`. -/
theorem step_lbu_10ca4 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ca4) 0x83#8 0xc2#8 0x75#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 7#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)).regs.insert x5 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca4) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x83#8 0xc2#8 0x75#8 0x00#8 = (0x0075c283 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc2#8 0x75#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (7#12, .Regidx 11#5, .Regidx 5#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_t0_a1_7_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (7#12, .Regidx 11#5, .Regidx 5#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)).regs.insert x5 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 7#12 (.Regidx 11#5) (.Regidx 5#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 7#12 (.Regidx 11#5) (.Regidx 5#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x5_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10ca4) retired mseccfgBits inhibit config
    0x83#8 0xc2#8 0x75#8 0x00#8 (.LOAD (7#12, .Regidx 11#5, .Regidx 5#5, true, 1))
    x5 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `ld a4, 0(a0)` (aligned double-word load, `rd = a4 = x14`, `rs1 = a0 = x10`). -/
theorem ldStep (stepNo : Nat) (state : State)
    (pc srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 8))
    (inhibit : BitVec 32) (config : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (plat : StepPlatform state pc b0 b1 b2 b3 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (base : BaseInstructionEncoding b0)
    (decode : Runs (ext_decode (fetchWord b0 b1 b2 b3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0#12, .Regidx 10#5, .Regidx 14#5, false, 8)))
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get?
      mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get?
      cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) 0#12)
      (Load Data) 8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcAddrBits) 8 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 8 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 8 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).mem.get?
        (srcAddrBits.toNat + i) = some (leBytes 8 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
            x14 v }
        (Sail.BitVec.addInt pc 4) retired) false := by
  have exec : Runs (execute (.LOAD (0#12, .Regidx 10#5, .Regidx 14#5, false, 8)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
          x14 v } (.Retire_Success ()) := by
    change Runs (execute_LOAD 0#12 (.Regidx 10#5) (.Regidx 14#5) false 8) _ _ _
    exact execute_LOAD_ld_run _ _ 0#12 (.Regidx 10#5) (.Regidx 14#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg aligned physAccess noMMIOr hmem
      (wX_x14_run _ v)
  exact gpStep stepNo state pc retired mseccfgBits inhibit config b0 b1 b2 b3
    (.LOAD (0#12, .Regidx 10#5, .Regidx 14#5, false, 8)) x14 v
    plat counters base decode exec (by decide) (by decide) (by decide) (by decide)

/-- `sd a3, 0(a0)` (aligned double-word store, data `a3 = x13`, address `a0 = x10`); opaque
post-write state `s'`. -/
theorem sdStep (stepNo : Nat) (state s' : State)
    (pc dstAddrBits mstatusBits retired mseccfgBits : BitVec 64) (dataBits : BitVec (8 * 8))
    (inhibit : BitVec 32) (config : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (plat : StepPlatform state pc b0 b1 b2 b3 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (base : BaseInstructionEncoding b0)
    (decode : Runs (ext_decode (fetchWord b0 b1 b2 b3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (0#12, .Regidx 13#5, .Regidx 10#5, 8)))
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get?
      mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get?
      cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hx13 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? x13
      = some dataBits)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) 0#12)
      (Store Data) 8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstAddrBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr dstAddrBits) 8 = true)
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstAddrBits) 8 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) none)
    (noMMIOw : Runs (within_mmio_writable (physaddr.Physaddr dstAddrBits) 8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) false)
    (hwrite : Runs (PreSail.writeBytes dstAddrBits.toNat dataBits)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) s' true) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, _privRead, _mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have exec : Runs (execute (.STORE (0#12, .Regidx 13#5, .Regidx 10#5, 8)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) s'
      (.Retire_Success ()) := by
    change Runs (execute_STORE 0#12 (.Regidx 13#5) (.Regidx 10#5) 8) _ _ _
    exact execute_STORE_dword_run _ s' (.Regidx 13#5) (.Regidx 10#5) dstAddrBits mstatusBits dataBits
      mstatusReadX privReadX mprvZero (rX_x13_run _ dataBits hx13) addrReg aligned physAccess
      noMMIOw hwrite
  have regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs :=
    writeBytes_preserves_regs dstAddrBits.toNat dataBits _ s' hwrite
  refine tryStepFallThroughRetires stepNo state s' pc retired inhibit config b0 b1 b2 b3
    (.STORE (0#12, .Regidx 13#5, .Regidx 10#5, 8)) platform noMMIO bytes interrupts base decode
    notExpected exec ?_ ?_ ?_ ?_ hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead
  · rw [regsEq]; exact coreNextPc _ _
  · rw [regsEq]; exact coreGetInc _ _ hart_state (by decide)
  · rw [regsEq]; exact coreGetInc _ _ minstret_increment (by decide)
  · rw [regsEq]; exact coreGetInc _ _ minstret (by decide)

/-! ## Deliverable 2c: control-flow body step lemmas (`bnez` / `ret`) and entry (`li` / `beqz`) -/

/-- Reading `x0` yields the hard-wired zero register. -/
theorem rX_x0_run (s : State) : Runs (rX_bits (.Regidx (BitVec.ofNat 5 0))) s s zero_reg := by
  have rk : (Sail.BitVec.toNatInt (BitVec.ofNat 5 0)).toNat = 0 := by decide
  unfold Runs
  simp [rX_bits, rX, rk, EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad,
    regval_from_reg]

/-- `bnez a2` = `bne a2, x0`: runs to `a2v != zero_reg`. -/
theorem bTypeTaken_bnez_run (s : State) (a2v : BitVec 64) (h12 : s.regs.get? x12 = some a2v) :
    Runs (bTypeTaken (.Regidx 0#5) (.Regidx 12#5) .BNE) s s (a2v != zero_reg) := by
  unfold bTypeTaken
  refine Runs.bind (rX_x12_run s a2v h12) ?_
  refine Runs.bind (rX_x0_run s) ?_
  rfl

/-- `beqz a2` = `beq a2, x0`: runs to `a2v == zero_reg`. -/
theorem bTypeTaken_beqz_run (s : State) (a2v : BitVec 64) (h12 : s.regs.get? x12 = some a2v) :
    Runs (bTypeTaken (.Regidx 0#5) (.Regidx 12#5) .BEQ) s s (a2v == zero_reg) := by
  unfold bTypeTaken
  refine Runs.bind (rX_x12_run s a2v h12) ?_
  refine Runs.bind (rX_x0_run s) ?_
  rfl

/-- `bnez a2, 0x10c74` at 0x10ce4, taken (`a2 ≠ 0`): back-edge to the loop head. -/
theorem step_bnez_taken (stepNo : Nat) (state : State) (pcVal a2v retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10ce4)).regs.get? x12 = some a2v)
    (hne : a2v ≠ zero_reg)
    (hpcRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10ce4)).regs.get? PC = some pcVal)
    (misaBits : BitVec 64)
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10ce4)).regs.get? misa = some misaBits)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) (0x1f90#13)) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) (0x1f90#13)) 1 = 0#1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10ce4) (pcVal + sign_extend (m := 64) (0x1f90#13)))
        (pcVal + sign_extend (m := 64) (0x1f90#13)) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0xe3#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0xe3#8 0x18#8 0x06#8 0xf8#8 = (0xf80618e3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xe3#8 0x18#8 0x06#8 0xf8#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x1f90#13, .Regidx 0#5, .Regidx 12#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bnez_a2_run _ privRead mseccfgBits mseccfgRead
  have hcondEq : (a2v != zero_reg) = true := by rw [bne_iff_ne]; exact hne
  have hcond : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 12#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      true := by
    have := bTypeTaken_bnez_run _ a2v h12; rwa [hcondEq] at this
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      pcVal :=
    readReg_run _ PC pcVal hpcRead
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x10ce4) pcVal retired
    (0x1f90#13) (.Regidx 0#5) (.Regidx 12#5) .BNE inhibit config 0xe3#8 0x18#8 0x06#8 0xf8#8
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected
    hcond hpc halign hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead

/-- `bnez a2, 0x10c74` at 0x10ce4, NOT taken (`a2 = 0`): falls through to `ret` at 0x10ce8. -/
theorem step_bnez_not_taken (stepNo : Nat) (state : State) (a2v retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10ce4)).regs.get? x12 = some a2v)
    (heq : a2v = zero_reg) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce4) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0xe3#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0xe3#8 0x18#8 0x06#8 0xf8#8 = (0xf80618e3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xe3#8 0x18#8 0x06#8 0xf8#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x1f90#13, .Regidx 0#5, .Regidx 12#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bnez_a2_run _ privRead mseccfgBits mseccfgRead
  have hcond : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 12#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      false := by
    have := bTypeTaken_bnez_run _ a2v h12
    rwa [show (a2v != zero_reg) = false by rw [heq]; simp] at this
  exact tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10ce4) retired
    (0x1f90#13) (.Regidx 0#5) (.Regidx 12#5) .BNE inhibit config 0xe3#8 0x18#8 0x06#8 0xf8#8
    platform noMMIO bytes interrupts base decode notExpected hcond hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- `ret` (`jalr x0, 0(ra)`) at 0x10ce8: returns with `PC = ra` (bit 0 cleared). -/
theorem step_ret (stepNo : Nat) (state : State)
    (rs1Val retired mseccfgBits misaBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ce8) 0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      rs1Val)
    (hbit1 : Sail.BitVec.access rs1Val 1 = 0#1)
    (hElp : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      ())
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10ce8)).regs.get? misa = some misaBits) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8)
          (Sail.BitVec.update rs1Val 0 0#1))
        (Sail.BitVec.update rs1Val 0 0#1) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x67#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x67#8 0x80#8 0x00#8 0x00#8 = (0x00008067 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x67#8 0x80#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0#12, .Regidx 1#5, zreg)) := by
    rw [wordEq]; exact ext_decode_ret_run _ privRead mseccfgBits mseccfgRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce8) 4) := by
    unfold get_next_pc; exact readReg_run _ nextPC _ (coreNextPc _ _)
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepRetRetires stepNo state (BitVec.ofNat 64 0x10ce8) retired (.Regidx 1#5)
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce8) 4) rs1Val inhibit config
    0x67#8 0x80#8 0x00#8 0x00#8 (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base
    decode notExpected hElp hlink hrs1 hbit1 hzca hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- Entry `li a2, 136` (`addi a2, x0, 136`) at 0x10c6c. -/
theorem step_li_a2 (stepNo : Nat) (state : State) (retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c6c) 0x13#8 0x06#8 0x80#8 0x08#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c6c)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x13#8 0x06#8 0x80#8 0x08#8 = (0x08800613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x80#8 0x08#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (136#12, .Regidx 0#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_li_a2_136_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (136#12, .Regidx 0#5, .Regidx 12#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c6c))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c6c)) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 136#12 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    exact execute_ITYPE_addi_run _ _ 136#12 (.Regidx 0#5) (.Regidx 12#5) zero_reg (rX_x0_run _)
      (wX_x12_run _ (zero_reg + sign_extend (m := 64) 136#12))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c6c) retired mseccfgBits inhibit config
    0x13#8 0x06#8 0x80#8 0x08#8 (.ITYPE (136#12, .Regidx 0#5, .Regidx 12#5, .ADDI))
    x12 (zero_reg + sign_extend (m := 64) 136#12) plat counters
    (by unfold BaseInstructionEncoding; decide) decode exec (by decide) (by decide) (by decide)
    (by decide)

/-- Entry `beqz a2, 0x10ce8` at 0x10c70, NOT taken (`a2 = 136 ≠ 0`): falls through to the loop
head at 0x10c74. -/
theorem step_beqz_not_taken (stepNo : Nat) (state : State) (a2v retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c70) 0x63#8 0x0c#8 0x06#8 0x06#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c70)).regs.get? x12 = some a2v)
    (hne : a2v ≠ zero_reg) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c70))
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x0c#8 0x06#8 0x06#8 = (0x06060c63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x0c#8 0x06#8 0x06#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x78#13, .Regidx 0#5, .Regidx 12#5, .BEQ)) := by
    rw [wordEq]; exact ext_decode_beqz_a2_run _ privRead mseccfgBits mseccfgRead
  have hcond : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 12#5) .BEQ)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c70))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c70))
      false := by
    have := bTypeTaken_beqz_run _ a2v h12
    rwa [show (a2v == zero_reg) = false by
      rw [beq_eq_false_iff_ne]; exact hne] at this
  exact tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10c70) retired
    (0x78#13) (.Regidx 0#5) (.Regidx 12#5) .BEQ inhibit config 0x63#8 0x0c#8 0x06#8 0x06#8
    platform noMMIO bytes interrupts base decode notExpected hcond hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-! ## Deliverable 4a: the 8-byte store's concrete memory effect

`writeBytes a v` (width 8) inserts the little-endian bytes of `v` at `a, a+1, …, a+7`.  `insertWord`
names that post-state; the two `get?` lemmas read the stored window and the disjoint complement. -/

/-- The byte-map after an 8-byte little-endian store of `v` at `a`. -/
def insertWord (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec (8 * 8)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((mem.insert a (v.extractLsb' 0 8)).insert (a + 1) (v.extractLsb' 8 8)).insert
    (a + 2) (v.extractLsb' 16 8)).insert (a + 3) (v.extractLsb' 24 8)).insert
    (a + 4) (v.extractLsb' 32 8)).insert (a + 5) (v.extractLsb' 40 8)).insert
    (a + 6) (v.extractLsb' 48 8)).insert (a + 7) (v.extractLsb' 56 8))

/-- The generated fixed-width store of a 64-bit word inserts its 8 little-endian bytes. -/
theorem writeBytes_word_run (s : State) (a : Nat) (v : BitVec (8 * 8)) :
    Runs (PreSail.writeBytes a v) s { s with mem := insertWord s.mem a v } true := by
  rw [writeBytes_eq]
  have hlist : (List.ofFn (fun i : Fin 8 => (a + i.val, v.extractLsb' (8 * i.val) 8)))
      = [(a, v.extractLsb' 0 8), (a + 1, v.extractLsb' 8 8), (a + 2, v.extractLsb' 16 8),
         (a + 3, v.extractLsb' 24 8), (a + 4, v.extractLsb' 32 8), (a + 5, v.extractLsb' 40 8),
         (a + 6, v.extractLsb' 48 8), (a + 7, v.extractLsb' 56 8)] := by
    simp [List.ofFn_succ, List.ofFn_zero]
  rw [hlist]
  simp only [List.forM]
  have hinner : Runs
      (do
        writeByte a (v.extractLsb' 0 8); writeByte (a + 1) (v.extractLsb' 8 8)
        writeByte (a + 2) (v.extractLsb' 16 8); writeByte (a + 3) (v.extractLsb' 24 8)
        writeByte (a + 4) (v.extractLsb' 32 8); writeByte (a + 5) (v.extractLsb' 40 8)
        writeByte (a + 6) (v.extractLsb' 48 8); writeByte (a + 7) (v.extractLsb' 56 8)
        pure PUnit.unit)
      s { s with mem := insertWord s.mem a v } PUnit.unit := by
    refine Runs.bind (writeByte_run s a _) ?_
    refine Runs.bind (writeByte_run _ (a + 1) _) ?_
    refine Runs.bind (writeByte_run _ (a + 2) _) ?_
    refine Runs.bind (writeByte_run _ (a + 3) _) ?_
    refine Runs.bind (writeByte_run _ (a + 4) _) ?_
    refine Runs.bind (writeByte_run _ (a + 5) _) ?_
    refine Runs.bind (writeByte_run _ (a + 6) _) ?_
    refine Runs.bind (writeByte_run _ (a + 7) _) ?_
    rfl
  exact Runs.bind hinner rfl

/-- The `i`-th little-endian byte of a 64-bit word. -/
theorem leBytes_extractLsb (v : BitVec (8 * 8)) (i : Nat) (hi : i < 8) :
    (leBytes 8 v)[i]'(by rw [leBytes_length]; exact hi) = v.extractLsb' (8 * i) 8 := by
  simp only [leBytes, List.getElem_ofFn]

/-- Reading a byte inside the stored 8-byte window. -/
theorem insertWord_get_in (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec (8 * 8))
    (i : Nat) (hi : i < 8) :
    (insertWord mem a v).get? (a + i) = some (v.extractLsb' (8 * i) 8) := by
  unfold insertWord
  match i, hi with
  | 0, _ =>
    rw [getInsertNe _ (a + 7) (a + 0) _ (by omega), getInsertNe _ (a + 6) (a + 0) _ (by omega), getInsertNe _ (a + 5) (a + 0) _ (by omega), getInsertNe _ (a + 4) (a + 0) _ (by omega), getInsertNe _ (a + 3) (a + 0) _ (by omega), getInsertNe _ (a + 2) (a + 0) _ (by omega), getInsertNe _ (a + 1) (a + 0) _ (by omega)]
    exact getInsertEq _ _ _
  | 1, _ =>
    rw [getInsertNe _ (a + 7) (a + 1) _ (by omega), getInsertNe _ (a + 6) (a + 1) _ (by omega), getInsertNe _ (a + 5) (a + 1) _ (by omega), getInsertNe _ (a + 4) (a + 1) _ (by omega), getInsertNe _ (a + 3) (a + 1) _ (by omega), getInsertNe _ (a + 2) (a + 1) _ (by omega)]
    exact getInsertEq _ _ _
  | 2, _ =>
    rw [getInsertNe _ (a + 7) (a + 2) _ (by omega), getInsertNe _ (a + 6) (a + 2) _ (by omega), getInsertNe _ (a + 5) (a + 2) _ (by omega), getInsertNe _ (a + 4) (a + 2) _ (by omega), getInsertNe _ (a + 3) (a + 2) _ (by omega)]
    exact getInsertEq _ _ _
  | 3, _ =>
    rw [getInsertNe _ (a + 7) (a + 3) _ (by omega), getInsertNe _ (a + 6) (a + 3) _ (by omega), getInsertNe _ (a + 5) (a + 3) _ (by omega), getInsertNe _ (a + 4) (a + 3) _ (by omega)]
    exact getInsertEq _ _ _
  | 4, _ =>
    rw [getInsertNe _ (a + 7) (a + 4) _ (by omega), getInsertNe _ (a + 6) (a + 4) _ (by omega), getInsertNe _ (a + 5) (a + 4) _ (by omega)]
    exact getInsertEq _ _ _
  | 5, _ =>
    rw [getInsertNe _ (a + 7) (a + 5) _ (by omega), getInsertNe _ (a + 6) (a + 5) _ (by omega)]
    exact getInsertEq _ _ _
  | 6, _ =>
    rw [getInsertNe _ (a + 7) (a + 6) _ (by omega)]
    exact getInsertEq _ _ _
  | 7, _ =>
    exact getInsertEq _ _ _

/-- Reading a byte outside the stored 8-byte window is unchanged. -/
theorem insertWord_get_out (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec (8 * 8))
    (b : Nat) (h : ∀ i : Nat, i < 8 → b ≠ a + i) :
    (insertWord mem a v).get? b = mem.get? b := by
  unfold insertWord
  rw [getInsertNe _ (a + 7) b _ (Ne.symm (h 7 (by omega))),
    getInsertNe _ (a + 6) b _ (Ne.symm (h 6 (by omega))),
    getInsertNe _ (a + 5) b _ (Ne.symm (h 5 (by omega))),
    getInsertNe _ (a + 4) b _ (Ne.symm (h 4 (by omega))),
    getInsertNe _ (a + 3) b _ (Ne.symm (h 3 (by omega))),
    getInsertNe _ (a + 2) b _ (Ne.symm (h 2 (by omega))),
    getInsertNe _ (a + 1) b _ (Ne.symm (h 1 (by omega))),
    getInsertNe _ a b _ (Ne.symm (h 0 (by omega)))]

/-- Storing an 8-byte word at addresses the image does not back preserves `matchesMemory`. -/
theorem matchesMemory_insertWord (image : ProgramImage) (mem : Std.ExtHashMap Nat (BitVec 8))
    (addr : Nat) (data : BitVec (8 * 8)) (hm : image.matchesMemory mem)
    (hnone : ∀ i : Nat, i < 8 → image.readByte? (addr + i) = none) :
    image.matchesMemory (insertWord mem addr data) := by
  intro a byte ha
  by_cases hin : addr ≤ a ∧ a < addr + 8
  · obtain ⟨h1, h2⟩ := hin
    have hn : image.readByte? a = none := by
      have := hnone (a - addr) (by omega)
      rwa [show addr + (a - addr) = a by omega] at this
    rw [hn] at ha; simp at ha
  · rw [insertWord_get_out mem addr data a (fun i hi => by omega)]; exact hm a byte ha

/-! ### Deliverable 4a (cont.): the rate-window memory frame

`xor_block` writes exactly the 136-byte rate window `[state0, state0+136)`: every store lands at
`state0 + 8k + i` with `k < 17` and `i < 8`.  We therefore track the *exact memory delta* relative to
a fixed reference state with the same `MemFramed` idiom the `memcpy` / `memset` / `copy_from_slice`
capstones export (`BinaryFv.Keccak.HelperFraming`), instantiated at `dst := state0`, `n := 136`.

The frame is the general conclusion: the capacity lanes (`17 ≤ m < 25`), the input block and the code
image all sit *outside* the rate window, so their preservation is derived from it rather than tracked
as independent ad-hoc conclusions.  The three lemmas below are the `xor_block` instances of
`HelperFraming`'s `frame_insert_step` / `MemFramed.mem_unchanged_outside` reading idiom, plus the
`toNat` plumbing for the concrete width `136`. -/

/-- The rate window is 136 bytes wide. -/
theorem rateWidth_toNat : (BitVec.ofNat 64 136).toNat = 136 := by decide

/-- Read the rate-window frame at an address outside `[state0, state0+136)`. -/
theorem memFramed_rate_apply {state0 : BitVec 64} {sref s : State}
    (h : MemFramed state0 (BitVec.ofNat 64 136) sref s) (addr : Nat)
    (haddr : ∀ j : Nat, j < 136 → addr ≠ (state0 + BitVec.ofNat 64 j).toNat) :
    s.mem.get? addr = sref.mem.get? addr :=
  h addr (fun j hj => haddr j (by rw [rateWidth_toNat] at hj; exact hj))

/-- Package a pointwise outside-the-rate-window agreement as a `MemFramed`. -/
theorem memFramed_rate_intro {state0 : BitVec 64} {sref s : State}
    (h : ∀ addr : Nat, (∀ j : Nat, j < 136 → addr ≠ (state0 + BitVec.ofNat 64 j).toNat) →
      s.mem.get? addr = sref.mem.get? addr) :
    MemFramed state0 (BitVec.ofNat 64 136) sref s :=
  fun addr haddr => h addr (fun j hj => haddr j (by rw [rateWidth_toNat]; exact hj))

/-- The lane store at `state0 + 8k` (`k < 17`) lands inside the rate window, so it never disturbs the
already-framed complement.  This is the `xor_block` (8 bytes at a time) analogue of
`HelperFraming.frame_insert_step`, and is the per-iteration step the loop invariant re-establishes. -/
theorem frame_rate_store {state0 : BitVec 64} {sref : State}
    {mem : Std.ExtHashMap Nat (BitVec 8)} {k : Nat} {v : BitVec (8 * 8)}
    (hstateFits : state0.toNat + 200 ≤ 2 ^ 64) (hk : k < 17)
    (hframe : ∀ addr : Nat, (∀ j : Nat, j < 136 → addr ≠ (state0 + BitVec.ofNat 64 j).toNat) →
      mem.get? addr = sref.mem.get? addr) :
    ∀ addr : Nat, (∀ j : Nat, j < 136 → addr ≠ (state0 + BitVec.ofNat 64 j).toNat) →
      (insertWord mem (state0 + BitVec.ofNat 64 (8 * k)).toNat v).get? addr
        = sref.mem.get? addr := by
  intro addr haddr
  rw [insertWord_get_out _ _ _ _ (fun i hi => by
    have h' := haddr (8 * k + i) (by omega)
    rw [dstAddr_toNat state0 (8 * k + i) (by omega)] at h'
    rw [dstAddr_toNat state0 (8 * k) (by omega)]
    omega)]
  exact hframe addr haddr

/-- Code-image preservation *derived from the frame*: the image backs no byte of the 200-byte state
region (`hstateImg`), hence none of the rate window either, and every address outside that window is
left untouched by a framed run. -/
theorem matchesMemory_of_rate_frame {state0 : BitVec 64} {sref s : State} {image : ProgramImage}
    (hframe : MemFramed state0 (BitVec.ofNat 64 136) sref s)
    (hstateImg : ∀ j : Nat, j < 200 → image.readByte? (state0 + BitVec.ofNat 64 j).toNat = none)
    (hm : image.matchesMemory sref.mem) :
    image.matchesMemory s.mem := by
  intro addr byte hread
  by_cases hin : ∃ j : Nat, j < 136 ∧ addr = (state0 + BitVec.ofNat 64 j).toNat
  · obtain ⟨j, hj, rfl⟩ := hin
    rw [hstateImg j (by omega)] at hread
    exact absurd hread (by simp)
  · rw [memFramed_rate_apply hframe addr (fun j hj heq => hin ⟨j, hj, heq⟩)]
    exact hm addr byte hread

/-! ## Deliverable 4b: loop invariant and abstract configured-machine premises

Mirrors `MemcpyContract`'s `MemcpyInv` / `AbstractPlatform` / `AbstractDataAccess` for `xor_block`.
`origLane m` is the original 64-bit state word of lane `m`; `inByte j` the input byte at
`input0 + j`; `inputLane k` the little-endian input lane (matching `assemble_leWord`). -/

/-- The little-endian 64-bit input lane assembled from the 8 input bytes at `input0 + 8k`. -/
def inputLane (inByte : Nat → BitVec 8) (k : Nat) : BitVec 64 :=
  BitVec.cast (by rfl) (leWord [inByte (8 * k + 0), inByte (8 * k + 1), inByte (8 * k + 2),
    inByte (8 * k + 3), inByte (8 * k + 4), inByte (8 * k + 5), inByte (8 * k + 6),
    inByte (8 * k + 7)])

/-- Instruction fetch addresses of `xor_block` (entry, 29 body instructions, exit). -/
@[reducible] def IsBodyPc (pc : BitVec 64) : Prop :=
  pc = BitVec.ofNat 64 0x10c6c ∨ pc = BitVec.ofNat 64 0x10c70 ∨ pc = BitVec.ofNat 64 0x10c74 ∨
  pc = BitVec.ofNat 64 0x10c78 ∨ pc = BitVec.ofNat 64 0x10c7c ∨ pc = BitVec.ofNat 64 0x10c80 ∨
  pc = BitVec.ofNat 64 0x10c84 ∨ pc = BitVec.ofNat 64 0x10c88 ∨ pc = BitVec.ofNat 64 0x10c8c ∨
  pc = BitVec.ofNat 64 0x10c90 ∨ pc = BitVec.ofNat 64 0x10c94 ∨ pc = BitVec.ofNat 64 0x10c98 ∨
  pc = BitVec.ofNat 64 0x10c9c ∨ pc = BitVec.ofNat 64 0x10ca0 ∨ pc = BitVec.ofNat 64 0x10ca4 ∨
  pc = BitVec.ofNat 64 0x10ca8 ∨ pc = BitVec.ofNat 64 0x10cac ∨ pc = BitVec.ofNat 64 0x10cb0 ∨
  pc = BitVec.ofNat 64 0x10cb4 ∨ pc = BitVec.ofNat 64 0x10cb8 ∨ pc = BitVec.ofNat 64 0x10cbc ∨
  pc = BitVec.ofNat 64 0x10cc0 ∨ pc = BitVec.ofNat 64 0x10cc4 ∨ pc = BitVec.ofNat 64 0x10cc8 ∨
  pc = BitVec.ofNat 64 0x10ccc ∨ pc = BitVec.ofNat 64 0x10cd0 ∨ pc = BitVec.ofNat 64 0x10cd4 ∨
  pc = BitVec.ofNat 64 0x10cd8 ∨ pc = BitVec.ofNat 64 0x10cdc ∨ pc = BitVec.ofNat 64 0x10ce0 ∨
  pc = BitVec.ofNat 64 0x10ce4 ∨ pc = BitVec.ofNat 64 0x10ce8

/-- Abstract configured-machine fetch/decode platform (stage-2 trust boundary). -/
def AbstractPlatform (base : State) : Prop :=
  BinaryFv.RiscV.AbstractPlatform NonW IsBodyPc base

/-- Abstract Zicfilp landing-pad update for the leaf `ret` (stage-2 trust boundary). -/
def AbstractElp (base : State) : Prop :=
  BinaryFv.RiscV.AbstractElp NonW (fun r => r = .Regidx 1#5) base

/-- Abstract load/store data-access preconditions for lane `k`: the 8 single-byte input loads (via
`a1 = input0 + 8k`), the 8-byte state-lane load and store (via `a0 = state0 + 8k`).  Never discharged
here (the stage-2 trust boundary). -/
def AbstractDataAccess (state0 input0 : BitVec 64) (base : State) : Prop :=
  ∀ (k : Nat) (t : State), k < 17 → StableAgree base t →
    (t.regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) →
      ∀ j : Nat, j < 8 →
        Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) (BitVec.ofNat 12 j))
          (Load Data) 1) t t
          (.Ext_DataAddr_OK (virtaddr.Virtaddr (input0 + BitVec.ofNat 64 (8 * k + j)))) ∧
        Runs (phys_access_check (Load Data) PBMT_PMA .Machine
          (physaddr.Physaddr (input0 + BitVec.ofNat 64 (8 * k + j))) 1 false) t t none ∧
        Runs (within_mmio_readable (physaddr.Physaddr (input0 + BitVec.ofNat 64 (8 * k + j))) 1)
          t t false) ∧
    (t.regs.get? x10 = some (state0 + BitVec.ofNat 64 (8 * k)) →
      (Runs (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) 0#12) (Load Data) 8)
          t t (.Ext_DataAddr_OK (virtaddr.Virtaddr (state0 + BitVec.ofNat 64 (8 * k)))) ∧
        is_aligned_vaddr (virtaddr.Virtaddr (state0 + BitVec.ofNat 64 (8 * k))) 8 = true ∧
        Runs (phys_access_check (Load Data) PBMT_PMA .Machine
          (physaddr.Physaddr (state0 + BitVec.ofNat 64 (8 * k))) 8 false) t t none ∧
        Runs (within_mmio_readable (physaddr.Physaddr (state0 + BitVec.ofNat 64 (8 * k))) 8)
          t t false) ∧
      (Runs (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) 0#12) (Store Data) 8)
          t t (.Ext_DataAddr_OK (virtaddr.Virtaddr (state0 + BitVec.ofNat 64 (8 * k)))) ∧
        is_aligned_vaddr (virtaddr.Virtaddr (state0 + BitVec.ofNat 64 (8 * k))) 8 = true ∧
        Runs (phys_access_check (Store Data) PBMT_PMA .Machine
          (physaddr.Physaddr (state0 + BitVec.ofNat 64 (8 * k))) 8 false) t t none ∧
        Runs (within_mmio_writable (physaddr.Physaddr (state0 + BitVec.ofNat 64 (8 * k))) 8)
          t t false))

theorem AbstractPlatform.mono {s s' : State} (h : StableAgree s s') (hp : AbstractPlatform s) :
    AbstractPlatform s' :=
  BinaryFv.RiscV.AbstractPlatform.mono h hp

theorem AbstractElp.mono {s s' : State} (h : StableAgree s s') (he : AbstractElp s) :
    AbstractElp s' :=
  BinaryFv.RiscV.AbstractElp.mono h he

theorem AbstractDataAccess.mono {state0 input0 : BitVec 64} {s s' : State} (h : StableAgree s s')
    (hd : AbstractDataAccess state0 input0 s) : AbstractDataAccess state0 input0 s' :=
  fun k t hk hst => hd k t hk (fun r hr => (hst r hr).trans (h r hr))

theorem StableAgree.afterInc {base t : State} (h : StableAgree base t) :
    StableAgree base (tryStepControlFlowAfterIncrement t) :=
  fun r hr => (afterIncGet t r hr.2.2.2.1).trans (h r hr)

/-- Assemble a `StepPlatform` bundle from the abstract platform field. -/
theorem mkStepPlatform {s : State} (s_k : State) (mseccfgBits pc : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hplat : AbstractPlatform s) (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hSt : StableAgree s s_k)
    (hPCafter : (tryStepControlFlowAfterIncrement s_k).regs.get? PC = some pc)
    (hbody : IsBodyPc pc)
    (hbytes : FetchBytesAt (tryStepControlFlowAfterIncrement s_k) pc b0 b1 b2 b3) :
    StepPlatform s_k pc b0 b1 b2 b3 mseccfgBits := by
  have hStA : StableAgree s (tryStepControlFlowAfterIncrement s_k) := hSt.afterInc
  obtain ⟨hfbp, hmmio, hint, hlp⟩ := hplat _ pc hStA hPCafter hbody
  exact ⟨hfbp, hmmio, hbytes, hint, hlp, (hStA cur_privilege (by decide)).trans hcur,
    (hStA mseccfg (by decide)).trans hmseccfg⟩

/-! ### `StableAgree` per-transition preservation -/

/-- A GP-writing fall-through retirement only writes registers in `W`. -/
theorem stableAgree_gp (base : State) (pc ret : BitVec 64) (rd : Register) (v : RegisterType rd)
    (hrdW : rd = x5 ∨ rd = x10 ∨ rd = x11 ∨ rd = x12 ∨ rd = x13 ∨ rd = x14 ∨ rd = x15 ∨
      rd = x16 ∨ rd = x17) :
    StableAgree base (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  have hrd : r ≠ rd := by rcases hrdW with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact hr.2.2.2.2.1 | exact hr.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.1
      | exact hr.2.2.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.2.2.2.1
      | exact hr.2.2.2.2.2.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.2.2.2.2.2.1 | exact hr.2.2.2.2.2.2.2.2.2.2.2.2
  rw [retiredFrameGet _ _ _ r hr.1 hr.2.2.1]
  show ((coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert rd v).get? r
      = base.regs.get? r
  rw [gpFrameGet (tryStepControlFlowAfterIncrement base) pc rd v r hrd hr.2.1]
  exact afterIncGet base r hr.2.2.2.1

/-- A taken-branch / jump retirement only writes registers in `W`. -/
theorem stableAgree_jump (base : State) (pc tgt ret : BitVec 64) :
    StableAgree base (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt) tgt ret) := by
  intro r hr
  rw [jumpRetiredGet base pc tgt ret r hr.1 hr.2.2.1 hr.2.1 hr.2.2.2.1]

/-- A not-taken branch retirement only writes registers in `W`. -/
theorem stableAgree_notTaken (base : State) (pc ret : BitVec 64) :
    StableAgree base (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  rw [retiredFrameGet _ _ _ r hr.1 hr.2.2.1, coreGetInc _ pc r hr.2.1]
  exact afterIncGet base r hr.2.2.2.1

/-- Read a register untouched by a not-taken branch retirement (works for `W` registers too, as long
as it is not one of the four control registers). -/
theorem notTakenGet (base : State) (pc ret : BitVec 64) (r : Register)
    (hPC : r ≠ PC) (hmr : r ≠ minstret) (hnpc : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret).regs.get? r = base.regs.get? r := by
  rw [retiredFrameGet _ _ _ r hPC hmr, coreGetInc _ pc r hnpc]
  exact afterIncGet base r hmi

/-- A memory-writing (`sd`) retirement only writes registers in `W`. -/
theorem stableAgree_store (base s' : State) (pc ret : BitVec 64)
    (regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs) :
    StableAgree base (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  rw [retiredFrameGet _ _ _ r hr.1 hr.2.2.1, regsEq,
    coreGetInc (tryStepControlFlowAfterIncrement base) pc r hr.2.1]
  exact afterIncGet base r hr.2.2.2.1

/-! ### The loop invariant at the loop head `0x10c74` -/

/-- The `xor_block` loop invariant: about to run iteration `k` at the loop head `0x10c74`.

`sref` is the fixed reference state the compositional frame is measured against (the caller's entry
state): `hstable` and `hframe` say the run so far has touched no register outside `W` and no memory
outside the 136-byte rate window. -/
structure XorBlockInv (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (sref : State) (k : Nat) (s : State) :
    Prop where
  hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10c74)
  ha0 : s.regs.get? x10 = some (state0 + BitVec.ofNat 64 (8 * k))
  ha1 : s.regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k))
  ha2 : s.regs.get? x12 = some (BitVec.ofNat 64 (136 - 8 * k))
  hra : s.regs.get? x1 = some retAddr
  hcur : s.regs.get? cur_privilege = some Privilege.Machine
  hmstatus : s.regs.get? mstatus = some mstatusBits
  hmprv : _get_Mstatus_MPRV mstatusBits = 0#1
  hmseccfg : s.regs.get? mseccfg = some mseccfgBits
  hhart : s.regs.get? hart_state = some (.HART_ACTIVE ())
  hinhibit : s.regs.get? mcountinhibit = some inhibit
  hnotInhibited : _get_Counterin_IR inhibit = 0#1
  hcfg : s.regs.get? minstretcfg = some cfg
  hmachineEnabled : _get_CountSmcntrpmf_MINH cfg = 0#1
  hminstret : ∃ v, s.regs.get? minstret = some v
  himageEq : Artifact.programImage = .ok image
  hmatches : image.matchesMemory s.mem
  hunproc : ∀ m i : Nat, k ≤ m → m < 25 → i < 8 →
    s.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat = some ((origLane m).extractLsb' (8 * i) 8)
  hproc : ∀ m i : Nat, m < k → i < 8 →
    s.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat =
      some ((origLane m ^^^ inputLane inByte m).extractLsb' (8 * i) 8)
  hinput : ∀ j : Nat, j < 136 → s.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (inByte j)
  hk : k ≤ 17
  hstateFits : state0.toNat + 200 ≤ 2 ^ 64
  hinputFits : input0.toNat + 136 ≤ 2 ^ 64
  hstateImg : ∀ j : Nat, j < 200 → image.readByte? (state0 + BitVec.ofNat 64 j).toNat = none
  hdisj : ∀ j j' : Nat, j < 200 → j' < 136 →
    (state0 + BitVec.ofNat 64 j).toNat ≠ (input0 + BitVec.ofNat 64 j').toNat
  hplat : AbstractPlatform s
  hdata : AbstractDataAccess state0 input0 s
  hElp : AbstractElp s
  /-- Register frame: nothing outside `W` has been written since `sref`. -/
  hstable : StableAgree sref s
  /-- Memory frame: nothing outside the 136-byte rate window has been written since `sref`. -/
  hframe : MemFramed state0 (BitVec.ofNat 64 136) sref s

/-! ### Arithmetic and register-tracking helpers for the advance -/

/-- Read a GP register through the counter-increment / `nextPC` writes back to the pre-step state. -/
theorem coreGetGP (sN : State) (pc : BitVec 64) (r : Register) (hnp : r ≠ nextPC)
    (hmi : r ≠ minstret_increment) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement sN) pc).regs.get? r =
      sN.regs.get? r :=
  (coreGetInc (tryStepControlFlowAfterIncrement sN) pc r hnp).trans (afterIncGet sN r hmi)

/-- `sign_extend` of the 12-bit `8`. -/
theorem sext8 : sign_extend (m := 64) (8#12) = BitVec.ofNat 64 8 := by
  simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide

/-- `sign_extend` of the 12-bit `-8` (`0xff8`). -/
theorem sextm8 : sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (2 ^ 64 - 8) := by
  simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide

/-- Advancing a base pointer by 8 (`a0 += 8`, `a1 += 8`). -/
theorem incBy8 (X : BitVec 64) (k : Nat) :
    X + BitVec.ofNat 64 (8 * k) + sign_extend (m := 64) 8#12 = X + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [sext8, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- Decrementing the counter by 8 (`a2 -= 8`). -/
theorem decBy8 (k : Nat) (hk : k ≤ 16) :
    BitVec.ofNat 64 (136 - 8 * k) + sign_extend (m := 64) (0xff8#12)
      = BitVec.ofNat 64 (136 - 8 * (k + 1)) := by
  rw [sextm8]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The counter `136 - 8k` is nonzero as a bit-vector for `k < 17`. -/
theorem a2_ne_zero (k : Nat) (hk : k < 17) : BitVec.ofNat 64 (136 - 8 * k) ≠ zero_reg := by
  intro heq
  have h1 : (BitVec.ofNat 64 (136 - 8 * k)).toNat = (zero_reg : BitVec 64).toNat := by rw [heq]
  rw [BitVec.toNat_ofNat] at h1
  have hz : (zero_reg : BitVec 64).toNat = 0 := by decide
  rw [hz] at h1
  have hbound : 8 * k < 136 := by omega
  omega

/-- The counter `136 - 8k` is zero as a bit-vector when `k = 17`. -/
theorem a2_eq_zero : BitVec.ofNat 64 (136 - 8 * 17) = zero_reg := by decide

/-! ## Deliverable 4c: the 28-instruction body core (0x10c74 → 0x10ce4)

`AtBnez k' s` is the machine positioned at the loop-test `0x10ce4` after `k'` lanes have been XORed
(`a0=state0+8k'`, `a1=input0+8k'`, `a2=136-8k'`).  It is `XorBlockInv k'` with `PC = 0x10ce4`. -/

structure AtBnez (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (sref : State) (k' : Nat) (s : State) :
    Prop where
  hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10ce4)
  ha0 : s.regs.get? x10 = some (state0 + BitVec.ofNat 64 (8 * k'))
  ha1 : s.regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k'))
  ha2 : s.regs.get? x12 = some (BitVec.ofNat 64 (136 - 8 * k'))
  hra : s.regs.get? x1 = some retAddr
  hcur : s.regs.get? cur_privilege = some Privilege.Machine
  hmstatus : s.regs.get? mstatus = some mstatusBits
  hmprv : _get_Mstatus_MPRV mstatusBits = 0#1
  hmseccfg : s.regs.get? mseccfg = some mseccfgBits
  hhart : s.regs.get? hart_state = some (.HART_ACTIVE ())
  hinhibit : s.regs.get? mcountinhibit = some inhibit
  hnotInhibited : _get_Counterin_IR inhibit = 0#1
  hcfg : s.regs.get? minstretcfg = some cfg
  hmachineEnabled : _get_CountSmcntrpmf_MINH cfg = 0#1
  hminstret : ∃ v, s.regs.get? minstret = some v
  himageEq : Artifact.programImage = .ok image
  hmatches : image.matchesMemory s.mem
  hunproc : ∀ m i : Nat, k' ≤ m → m < 25 → i < 8 →
    s.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat = some ((origLane m).extractLsb' (8 * i) 8)
  hproc : ∀ m i : Nat, m < k' → i < 8 →
    s.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat =
      some ((origLane m ^^^ inputLane inByte m).extractLsb' (8 * i) 8)
  hinput : ∀ j : Nat, j < 136 → s.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (inByte j)
  hk : k' ≤ 17
  hstateFits : state0.toNat + 200 ≤ 2 ^ 64
  hinputFits : input0.toNat + 136 ≤ 2 ^ 64
  hstateImg : ∀ j : Nat, j < 200 → image.readByte? (state0 + BitVec.ofNat 64 j).toNat = none
  hdisj : ∀ j j' : Nat, j < 200 → j' < 136 →
    (state0 + BitVec.ofNat 64 j).toNat ≠ (input0 + BitVec.ofNat 64 j').toNat
  hplat : AbstractPlatform s
  hdata : AbstractDataAccess state0 input0 s
  hElp : AbstractElp s
  /-- Register frame: nothing outside `W` has been written since `sref`. -/
  hstable : StableAgree sref s
  /-- Memory frame: nothing outside the 136-byte rate window has been written since `sref`. -/
  hframe : MemFramed state0 (BitVec.ofNat 64 136) sref s

/-! ## Deliverable 4c (cont.): the 28-instruction body core proof -/

set_option maxHeartbeats 8000000 in
/-- One 28-instruction body pass (loop head `0x10c74` → loop test `0x10ce4`): XORs input lane `k`
into state lane `k` and advances `a0`/`a1`/`a2`, landing in `AtBnez (k+1)`. -/
theorem xorblock_body_core (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (sref : State) (start k : Nat) (s : State)
    (hk : k < 17)
    (hInv : XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref k s) :
    ∃ s28, Trace (start + k * 29) 28 s s28 ∧
      AtBnez state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg origLane inByte sref
        (k + 1) s28 := by
  obtain ⟨retired0, hret0⟩ := hInv.hminstret
  have hsf := hInv.hstateFits
  have hSt0 : StableAgree s s := StableAgree.refl s
  -- Step 0: lbu at 0x10c74
  have hbytes0 : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74) 0x83#8 0xc6#8 0x15#8 0x00#8 :=
    fetchBytesAt_10c74 (tryStepControlFlowAfterIncrement s) image hInv.himageEq hInv.hmatches
  have hplat0 : StepPlatform s (BitVec.ofNat 64 0x10c74) 0x83#8 0xc6#8 0x15#8 0x00#8 mseccfgBits :=
    mkStepPlatform s mseccfgBits (BitVec.ofNat 64 0x10c74) 0x83#8 0xc6#8 0x15#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg (StableAgree.refl s) ((afterIncGet s PC (by decide)).trans hInv.hPC) (by decide) hbytes0
  have hcnt0 : StepCounters s retired0 inhibit cfg := ⟨hInv.hhart, hInv.hinhibit, hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hret0⟩
  have hx11c0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)).regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s (BitVec.ofNat 64 0x10c74) x11 (by decide) (by decide)).trans hInv.ha1)
  obtain ⟨addr0, phys0, mmio0⟩ :=
    (hInv.hdata k (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)) hk (coreStableAgree s (BitVec.ofNat 64 0x10c74) (StableAgree.refl s))).1 hx11c0 1 (by decide)
  have hbyte0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)).mem.get? (input0 + BitVec.ofNat 64 (8 * k + 1)).toNat = some (inByte (8 * k + 1)) :=
    hInv.hinput (8 * k + 1) (by omega)
  have h0 := step_lbu_10c74 (start + k * 29 + 0) s (input0 + BitVec.ofNat 64 (8 * k + 1)) mstatusBits retired0 mseccfgBits
    (inByte (8 * k + 1)) inhibit cfg hplat0 hcnt0 ((coreGetStable s (BitVec.ofNat 64 0x10c74) mstatus (by decide) (StableAgree.refl s)).trans hInv.hmstatus) ((coreGetStable s (BitVec.ofNat 64 0x10c74) cur_privilege (by decide) (StableAgree.refl s)).trans hInv.hcur) hInv.hmprv
    addr0 phys0 mmio0 (leBytes_one_mem _ _ (inByte (8 * k + 1)) hbyte0)
  have hSt1 : StableAgree s _ := hSt0.trans (stableAgree_gp s (BitVec.ofNat 64 0x10c74) retired0 x13 (zero_extend (m := 64) (inByte (8 * k + 1))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hPC1 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)).regs.insert x13 (zero_extend (m := 64) (inByte (8 * k + 1))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c74) 4) retired0
  have hmin1 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)).regs.insert x13 (zero_extend (m := 64) (inByte (8 * k + 1))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c74) 4) retired0
  have hmem1 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)).regs.insert x13 (zero_extend (m := 64) (inByte (8 * k + 1))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c74) 4) retired0).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s (BitVec.ofNat 64 0x10c74) x13 (zero_extend (m := 64) (inByte (8 * k + 1)))).trans rfl)
  have hw13s1 : _ = some (zero_extend (m := 64) (inByte (8 * k + 1))) :=
    (fallThroughRetiredRd s (BitVec.ofNat 64 0x10c74) retired0 x13 (zero_extend (m := 64) (inByte (8 * k + 1))) (by decide) (by decide))
  have hw10s1 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c74) retired0 x13 (zero_extend (m := 64) (inByte (8 * k + 1))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.ha0
  have hw11s1 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c74) retired0 x13 (zero_extend (m := 64) (inByte (8 * k + 1))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.ha1
  have hw12s1 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c74) retired0 x13 (zero_extend (m := 64) (inByte (8 * k + 1))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.ha2
  generalize hgen0 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c74)).regs.insert x13 (zero_extend (m := 64) (inByte (8 * k + 1))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c74) 4) retired0 = s1 at h0 hSt1 hPC1 hmin1 hmem1 hw13s1 hw10s1 hw11s1 hw12s1

  -- Step 1: lbu at 0x10c78
  have hbytes1 : FetchBytesAt (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78) 0x03#8 0xc7#8 0x25#8 0x00#8 :=
    fetchBytesAt_10c78 (tryStepControlFlowAfterIncrement s1) image hInv.himageEq (hmem1.symm ▸ hInv.hmatches)
  have hplat1 : StepPlatform s1 (BitVec.ofNat 64 0x10c78) 0x03#8 0xc7#8 0x25#8 0x00#8 mseccfgBits :=
    mkStepPlatform s1 mseccfgBits (BitVec.ofNat 64 0x10c78) 0x03#8 0xc7#8 0x25#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt1 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c74) 4 = BitVec.ofNat 64 0x10c78 from by decide) ▸ hPC1) (by decide) hbytes1
  have hcnt1 : StepCounters s1 (Sail.BitVec.addInt retired0 1) inhibit cfg := ⟨(hSt1 hart_state (by decide)).trans hInv.hhart, (hSt1 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt1 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin1⟩
  have hx11c1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)).regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s1 (BitVec.ofNat 64 0x10c78) x11 (by decide) (by decide)).trans hw11s1)
  obtain ⟨addr1, phys1, mmio1⟩ :=
    (hInv.hdata k (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)) hk (coreStableAgree s1 (BitVec.ofNat 64 0x10c78) hSt1)).1 hx11c1 2 (by decide)
  have hbyte1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)).mem.get? (input0 + BitVec.ofNat 64 (8 * k + 2)).toNat = some (inByte (8 * k + 2)) :=
    hmem1.symm ▸ hInv.hinput (8 * k + 2) (by omega)
  have h1 := step_lbu_10c78 (start + k * 29 + 1) s1 (input0 + BitVec.ofNat 64 (8 * k + 2)) mstatusBits (Sail.BitVec.addInt retired0 1) mseccfgBits
    (inByte (8 * k + 2)) inhibit cfg hplat1 hcnt1 ((coreGetStable s1 (BitVec.ofNat 64 0x10c78) mstatus (by decide) hSt1).trans hInv.hmstatus) ((coreGetStable s1 (BitVec.ofNat 64 0x10c78) cur_privilege (by decide) hSt1).trans hInv.hcur) hInv.hmprv
    addr1 phys1 mmio1 (leBytes_one_mem _ _ (inByte (8 * k + 2)) hbyte1)
  have hSt2 : StableAgree s _ := hSt1.trans (stableAgree_gp s1 (BitVec.ofNat 64 0x10c78) (Sail.BitVec.addInt retired0 1) x14 (zero_extend (m := 64) (inByte (8 * k + 2))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have hPC2 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)).regs.insert x14 (zero_extend (m := 64) (inByte (8 * k + 2))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c78) 4) (Sail.BitVec.addInt retired0 1)
  have hmin2 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)).regs.insert x14 (zero_extend (m := 64) (inByte (8 * k + 2))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c78) 4) (Sail.BitVec.addInt retired0 1)
  have hmem2 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)).regs.insert x14 (zero_extend (m := 64) (inByte (8 * k + 2))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c78) 4) (Sail.BitVec.addInt retired0 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s1 (BitVec.ofNat 64 0x10c78) x14 (zero_extend (m := 64) (inByte (8 * k + 2)))).trans hmem1)
  have hw14s2 : _ = some (zero_extend (m := 64) (inByte (8 * k + 2))) :=
    (fallThroughRetiredRd s1 (BitVec.ofNat 64 0x10c78) (Sail.BitVec.addInt retired0 1) x14 (zero_extend (m := 64) (inByte (8 * k + 2))) (by decide) (by decide))
  have hw10s2 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s1 (BitVec.ofNat 64 0x10c78) (Sail.BitVec.addInt retired0 1) x14 (zero_extend (m := 64) (inByte (8 * k + 2))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s1
  have hw11s2 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s1 (BitVec.ofNat 64 0x10c78) (Sail.BitVec.addInt retired0 1) x14 (zero_extend (m := 64) (inByte (8 * k + 2))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s1
  have hw12s2 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s1 (BitVec.ofNat 64 0x10c78) (Sail.BitVec.addInt retired0 1) x14 (zero_extend (m := 64) (inByte (8 * k + 2))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s1
  have hw13s2 : _ = some (zero_extend (m := 64) (inByte (8 * k + 1))) :=
    (fallThroughRetiredGet s1 (BitVec.ofNat 64 0x10c78) (Sail.BitVec.addInt retired0 1) x14 (zero_extend (m := 64) (inByte (8 * k + 2))) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s1
  generalize hgen1 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c78)).regs.insert x14 (zero_extend (m := 64) (inByte (8 * k + 2))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c78) 4) (Sail.BitVec.addInt retired0 1) = s2 at h1 hSt2 hPC2 hmin2 hmem2 hw14s2 hw10s2 hw11s2 hw12s2 hw13s2

  -- Step 2: lbu at 0x10c7c
  have hbytes2 : FetchBytesAt (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c) 0x83#8 0xc7#8 0x35#8 0x00#8 :=
    fetchBytesAt_10c7c (tryStepControlFlowAfterIncrement s2) image hInv.himageEq (hmem2.symm ▸ hInv.hmatches)
  have hplat2 : StepPlatform s2 (BitVec.ofNat 64 0x10c7c) 0x83#8 0xc7#8 0x35#8 0x00#8 mseccfgBits :=
    mkStepPlatform s2 mseccfgBits (BitVec.ofNat 64 0x10c7c) 0x83#8 0xc7#8 0x35#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt2 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c78) 4 = BitVec.ofNat 64 0x10c7c from by decide) ▸ hPC2) (by decide) hbytes2
  have hcnt2 : StepCounters s2 (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) inhibit cfg := ⟨(hSt2 hart_state (by decide)).trans hInv.hhart, (hSt2 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt2 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin2⟩
  have hx11c2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)).regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s2 (BitVec.ofNat 64 0x10c7c) x11 (by decide) (by decide)).trans hw11s2)
  obtain ⟨addr2, phys2, mmio2⟩ :=
    (hInv.hdata k (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)) hk (coreStableAgree s2 (BitVec.ofNat 64 0x10c7c) hSt2)).1 hx11c2 3 (by decide)
  have hbyte2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)).mem.get? (input0 + BitVec.ofNat 64 (8 * k + 3)).toNat = some (inByte (8 * k + 3)) :=
    hmem2.symm ▸ hInv.hinput (8 * k + 3) (by omega)
  have h2 := step_lbu_10c7c (start + k * 29 + 2) s2 (input0 + BitVec.ofNat 64 (8 * k + 3)) mstatusBits (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) mseccfgBits
    (inByte (8 * k + 3)) inhibit cfg hplat2 hcnt2 ((coreGetStable s2 (BitVec.ofNat 64 0x10c7c) mstatus (by decide) hSt2).trans hInv.hmstatus) ((coreGetStable s2 (BitVec.ofNat 64 0x10c7c) cur_privilege (by decide) hSt2).trans hInv.hcur) hInv.hmprv
    addr2 phys2 mmio2 (leBytes_one_mem _ _ (inByte (8 * k + 3)) hbyte2)
  have hSt3 : StableAgree s _ := hSt2.trans (stableAgree_gp s2 (BitVec.ofNat 64 0x10c7c) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 3))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have hPC3 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)).regs.insert x15 (zero_extend (m := 64) (inByte (8 * k + 3))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c7c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
  have hmin3 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)).regs.insert x15 (zero_extend (m := 64) (inByte (8 * k + 3))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c7c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
  have hmem3 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)).regs.insert x15 (zero_extend (m := 64) (inByte (8 * k + 3))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c7c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s2 (BitVec.ofNat 64 0x10c7c) x15 (zero_extend (m := 64) (inByte (8 * k + 3)))).trans hmem2)
  have hw15s3 : _ = some (zero_extend (m := 64) (inByte (8 * k + 3))) :=
    (fallThroughRetiredRd s2 (BitVec.ofNat 64 0x10c7c) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 3))) (by decide) (by decide))
  have hw10s3 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s2 (BitVec.ofNat 64 0x10c7c) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 3))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s2
  have hw11s3 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s2 (BitVec.ofNat 64 0x10c7c) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 3))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s2
  have hw12s3 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s2 (BitVec.ofNat 64 0x10c7c) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 3))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s2
  have hw13s3 : _ = some (zero_extend (m := 64) (inByte (8 * k + 1))) :=
    (fallThroughRetiredGet s2 (BitVec.ofNat 64 0x10c7c) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 3))) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s2
  have hw14s3 : _ = some (zero_extend (m := 64) (inByte (8 * k + 2))) :=
    (fallThroughRetiredGet s2 (BitVec.ofNat 64 0x10c7c) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 3))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s2
  generalize hgen2 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c7c)).regs.insert x15 (zero_extend (m := 64) (inByte (8 * k + 3))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c7c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) = s3 at h2 hSt3 hPC3 hmin3 hmem3 hw15s3 hw10s3 hw11s3 hw12s3 hw13s3 hw14s3

  -- Step 3: lbu at 0x10c80
  have hbytes3 : FetchBytesAt (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80) 0x03#8 0xc8#8 0x05#8 0x00#8 :=
    fetchBytesAt_10c80 (tryStepControlFlowAfterIncrement s3) image hInv.himageEq (hmem3.symm ▸ hInv.hmatches)
  have hplat3 : StepPlatform s3 (BitVec.ofNat 64 0x10c80) 0x03#8 0xc8#8 0x05#8 0x00#8 mseccfgBits :=
    mkStepPlatform s3 mseccfgBits (BitVec.ofNat 64 0x10c80) 0x03#8 0xc8#8 0x05#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt3 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c7c) 4 = BitVec.ofNat 64 0x10c80 from by decide) ▸ hPC3) (by decide) hbytes3
  have hcnt3 : StepCounters s3 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) inhibit cfg := ⟨(hSt3 hart_state (by decide)).trans hInv.hhart, (hSt3 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt3 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin3⟩
  have hx11c3 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)).regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s3 (BitVec.ofNat 64 0x10c80) x11 (by decide) (by decide)).trans hw11s3)
  obtain ⟨addr3, phys3, mmio3⟩ :=
    (hInv.hdata k (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)) hk (coreStableAgree s3 (BitVec.ofNat 64 0x10c80) hSt3)).1 hx11c3 0 (by decide)
  have hbyte3 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)).mem.get? (input0 + BitVec.ofNat 64 (8 * k + 0)).toNat = some (inByte (8 * k + 0)) :=
    hmem3.symm ▸ hInv.hinput (8 * k + 0) (by omega)
  have h3 := step_lbu_10c80 (start + k * 29 + 3) s3 (input0 + BitVec.ofNat 64 (8 * k + 0)) mstatusBits (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) mseccfgBits
    (inByte (8 * k + 0)) inhibit cfg hplat3 hcnt3 ((coreGetStable s3 (BitVec.ofNat 64 0x10c80) mstatus (by decide) hSt3).trans hInv.hmstatus) ((coreGetStable s3 (BitVec.ofNat 64 0x10c80) cur_privilege (by decide) hSt3).trans hInv.hcur) hInv.hmprv
    addr3 phys3 mmio3 (leBytes_one_mem _ _ (inByte (8 * k + 0)) hbyte3)
  have hSt4 : StableAgree s _ := hSt3.trans (stableAgree_gp s3 (BitVec.ofNat 64 0x10c80) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 0))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have hPC4 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)).regs.insert x16 (zero_extend (m := 64) (inByte (8 * k + 0))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c80) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
  have hmin4 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)).regs.insert x16 (zero_extend (m := 64) (inByte (8 * k + 0))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c80) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
  have hmem4 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)).regs.insert x16 (zero_extend (m := 64) (inByte (8 * k + 0))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c80) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s3 (BitVec.ofNat 64 0x10c80) x16 (zero_extend (m := 64) (inByte (8 * k + 0)))).trans hmem3)
  have hw16s4 : _ = some (zero_extend (m := 64) (inByte (8 * k + 0))) :=
    (fallThroughRetiredRd s3 (BitVec.ofNat 64 0x10c80) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 0))) (by decide) (by decide))
  have hw10s4 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s3 (BitVec.ofNat 64 0x10c80) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 0))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s3
  have hw11s4 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s3 (BitVec.ofNat 64 0x10c80) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 0))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s3
  have hw12s4 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s3 (BitVec.ofNat 64 0x10c80) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 0))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s3
  have hw13s4 : _ = some (zero_extend (m := 64) (inByte (8 * k + 1))) :=
    (fallThroughRetiredGet s3 (BitVec.ofNat 64 0x10c80) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 0))) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s3
  have hw14s4 : _ = some (zero_extend (m := 64) (inByte (8 * k + 2))) :=
    (fallThroughRetiredGet s3 (BitVec.ofNat 64 0x10c80) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 0))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s3
  have hw15s4 : _ = some (zero_extend (m := 64) (inByte (8 * k + 3))) :=
    (fallThroughRetiredGet s3 (BitVec.ofNat 64 0x10c80) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 0))) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s3
  generalize hgen3 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c80)).regs.insert x16 (zero_extend (m := 64) (inByte (8 * k + 0))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c80) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) = s4 at h3 hSt4 hPC4 hmin4 hmem4 hw16s4 hw10s4 hw11s4 hw12s4 hw13s4 hw14s4 hw15s4

  -- Step 4: slli at 0x10c84
  have hbytes4 : FetchBytesAt (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c84) 0x93#8 0x96#8 0x86#8 0x00#8 :=
    fetchBytesAt_10c84 (tryStepControlFlowAfterIncrement s4) image hInv.himageEq (hmem4.symm ▸ hInv.hmatches)
  have hplat4 : StepPlatform s4 (BitVec.ofNat 64 0x10c84) 0x93#8 0x96#8 0x86#8 0x00#8 mseccfgBits :=
    mkStepPlatform s4 mseccfgBits (BitVec.ofNat 64 0x10c84) 0x93#8 0x96#8 0x86#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt4 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c80) 4 = BitVec.ofNat 64 0x10c84 from by decide) ▸ hPC4) (by decide) hbytes4
  have hcnt4 : StepCounters s4 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) inhibit cfg := ⟨(hSt4 hart_state (by decide)).trans hInv.hhart, (hSt4 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt4 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin4⟩
  have hr13s4 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c84)).regs.get? x13 = some (zero_extend (m := 64) (inByte (8 * k + 1))) := ((coreGetGP s4 (BitVec.ofNat 64 0x10c84) x13 (by decide) (by decide)).trans hw13s4)
  have h4 := step_slli_10c84 (start + k * 29 + 4) s4 (zero_extend (m := 64) (inByte (8 * k + 1))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat4 hcnt4 hr13s4
  have hSt5 : StableAgree s _ := hSt4.trans (stableAgree_gp s4 (BitVec.ofNat 64 0x10c84) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hPC5 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c84)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c84)).regs.insert x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c84) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1)
  have hmin5 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c84)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c84)).regs.insert x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c84) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1)
  have hmem5 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c84)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c84)).regs.insert x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c84) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s4 (BitVec.ofNat 64 0x10c84) x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8)).trans hmem4)
  have hw13s5 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) :=
    (fallThroughRetiredRd s4 (BitVec.ofNat 64 0x10c84) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) (by decide) (by decide))
  have hw10s5 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s4 (BitVec.ofNat 64 0x10c84) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s4
  have hw11s5 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s4 (BitVec.ofNat 64 0x10c84) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s4
  have hw12s5 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s4 (BitVec.ofNat 64 0x10c84) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s4
  have hw14s5 : _ = some (zero_extend (m := 64) (inByte (8 * k + 2))) :=
    (fallThroughRetiredGet s4 (BitVec.ofNat 64 0x10c84) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s4
  have hw15s5 : _ = some (zero_extend (m := 64) (inByte (8 * k + 3))) :=
    (fallThroughRetiredGet s4 (BitVec.ofNat 64 0x10c84) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s4
  have hw16s5 : _ = some (zero_extend (m := 64) (inByte (8 * k + 0))) :=
    (fallThroughRetiredGet s4 (BitVec.ofNat 64 0x10c84) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s4
  generalize hgen4 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c84)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c84)).regs.insert x13 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c84) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) = s5 at h4 hSt5 hPC5 hmin5 hmem5 hw13s5 hw10s5 hw11s5 hw12s5 hw14s5 hw15s5 hw16s5

  -- Step 5: slli at 0x10c88
  have hbytes5 : FetchBytesAt (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c88) 0x13#8 0x17#8 0x07#8 0x01#8 :=
    fetchBytesAt_10c88 (tryStepControlFlowAfterIncrement s5) image hInv.himageEq (hmem5.symm ▸ hInv.hmatches)
  have hplat5 : StepPlatform s5 (BitVec.ofNat 64 0x10c88) 0x13#8 0x17#8 0x07#8 0x01#8 mseccfgBits :=
    mkStepPlatform s5 mseccfgBits (BitVec.ofNat 64 0x10c88) 0x13#8 0x17#8 0x07#8 0x01#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt5 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c84) 4 = BitVec.ofNat 64 0x10c88 from by decide) ▸ hPC5) (by decide) hbytes5
  have hcnt5 : StepCounters s5 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt5 hart_state (by decide)).trans hInv.hhart, (hSt5 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt5 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin5⟩
  have hr14s5 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c88)).regs.get? x14 = some (zero_extend (m := 64) (inByte (8 * k + 2))) := ((coreGetGP s5 (BitVec.ofNat 64 0x10c88) x14 (by decide) (by decide)).trans hw14s5)
  have h5 := step_slli_10c88 (start + k * 29 + 5) s5 (zero_extend (m := 64) (inByte (8 * k + 2))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat5 hcnt5 hr14s5
  have hSt6 : StableAgree s _ := hSt5.trans (stableAgree_gp s5 (BitVec.ofNat 64 0x10c88) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have hPC6 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c88)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c88)).regs.insert x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c88) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1)
  have hmin6 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c88)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c88)).regs.insert x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c88) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1)
  have hmem6 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c88)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c88)).regs.insert x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c88) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s5 (BitVec.ofNat 64 0x10c88) x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)).trans hmem5)
  have hw14s6 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) :=
    (fallThroughRetiredRd s5 (BitVec.ofNat 64 0x10c88) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) (by decide) (by decide))
  have hw10s6 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s5 (BitVec.ofNat 64 0x10c88) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s5
  have hw11s6 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s5 (BitVec.ofNat 64 0x10c88) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s5
  have hw12s6 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s5 (BitVec.ofNat 64 0x10c88) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s5
  have hw13s6 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) :=
    (fallThroughRetiredGet s5 (BitVec.ofNat 64 0x10c88) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s5
  have hw15s6 : _ = some (zero_extend (m := 64) (inByte (8 * k + 3))) :=
    (fallThroughRetiredGet s5 (BitVec.ofNat 64 0x10c88) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s5
  have hw16s6 : _ = some (zero_extend (m := 64) (inByte (8 * k + 0))) :=
    (fallThroughRetiredGet s5 (BitVec.ofNat 64 0x10c88) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s5
  generalize hgen5 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c88)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c88)).regs.insert x14 ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c88) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) = s6 at h5 hSt6 hPC6 hmin6 hmem6 hw14s6 hw10s6 hw11s6 hw12s6 hw13s6 hw15s6 hw16s6

  -- Step 6: slli at 0x10c8c
  have hbytes6 : FetchBytesAt (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10c8c) 0x93#8 0x97#8 0x87#8 0x01#8 :=
    fetchBytesAt_10c8c (tryStepControlFlowAfterIncrement s6) image hInv.himageEq (hmem6.symm ▸ hInv.hmatches)
  have hplat6 : StepPlatform s6 (BitVec.ofNat 64 0x10c8c) 0x93#8 0x97#8 0x87#8 0x01#8 mseccfgBits :=
    mkStepPlatform s6 mseccfgBits (BitVec.ofNat 64 0x10c8c) 0x93#8 0x97#8 0x87#8 0x01#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt6 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c88) 4 = BitVec.ofNat 64 0x10c8c from by decide) ▸ hPC6) (by decide) hbytes6
  have hcnt6 : StepCounters s6 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt6 hart_state (by decide)).trans hInv.hhart, (hSt6 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt6 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin6⟩
  have hr15s6 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10c8c)).regs.get? x15 = some (zero_extend (m := 64) (inByte (8 * k + 3))) := ((coreGetGP s6 (BitVec.ofNat 64 0x10c8c) x15 (by decide) (by decide)).trans hw15s6)
  have h6 := step_slli_10c8c (start + k * 29 + 6) s6 (zero_extend (m := 64) (inByte (8 * k + 3))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat6 hcnt6 hr15s6
  have hSt7 : StableAgree s _ := hSt6.trans (stableAgree_gp s6 (BitVec.ofNat 64 0x10c8c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have hPC7 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10c8c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10c8c)).regs.insert x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c8c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1)
  have hmin7 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10c8c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10c8c)).regs.insert x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c8c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1)
  have hmem7 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10c8c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10c8c)).regs.insert x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c8c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s6 (BitVec.ofNat 64 0x10c8c) x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24)).trans hmem6)
  have hw15s7 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) :=
    (fallThroughRetiredRd s6 (BitVec.ofNat 64 0x10c8c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) (by decide) (by decide))
  have hw10s7 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s6 (BitVec.ofNat 64 0x10c8c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s6
  have hw11s7 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s6 (BitVec.ofNat 64 0x10c8c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s6
  have hw12s7 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s6 (BitVec.ofNat 64 0x10c8c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s6
  have hw13s7 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) :=
    (fallThroughRetiredGet s6 (BitVec.ofNat 64 0x10c8c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s6
  have hw14s7 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) :=
    (fallThroughRetiredGet s6 (BitVec.ofNat 64 0x10c8c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s6
  have hw16s7 : _ = some (zero_extend (m := 64) (inByte (8 * k + 0))) :=
    (fallThroughRetiredGet s6 (BitVec.ofNat 64 0x10c8c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s6
  generalize hgen6 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10c8c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10c8c)).regs.insert x15 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c8c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) = s7 at h6 hSt7 hPC7 hmin7 hmem7 hw15s7 hw10s7 hw11s7 hw12s7 hw13s7 hw14s7 hw16s7

  -- Step 7: or at 0x10c90
  have hbytes7 : FetchBytesAt (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90) 0xb3#8 0xe6#8 0x06#8 0x01#8 :=
    fetchBytesAt_10c90 (tryStepControlFlowAfterIncrement s7) image hInv.himageEq (hmem7.symm ▸ hInv.hmatches)
  have hplat7 : StepPlatform s7 (BitVec.ofNat 64 0x10c90) 0xb3#8 0xe6#8 0x06#8 0x01#8 mseccfgBits :=
    mkStepPlatform s7 mseccfgBits (BitVec.ofNat 64 0x10c90) 0xb3#8 0xe6#8 0x06#8 0x01#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt7 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c8c) 4 = BitVec.ofNat 64 0x10c90 from by decide) ▸ hPC7) (by decide) hbytes7
  have hcnt7 : StepCounters s7 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt7 hart_state (by decide)).trans hInv.hhart, (hSt7 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt7 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin7⟩
  have hra7 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90)).regs.get? x13 = some ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) := ((coreGetGP s7 (BitVec.ofNat 64 0x10c90) x13 (by decide) (by decide)).trans hw13s7)
  have hrb7 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90)).regs.get? x16 = some (zero_extend (m := 64) (inByte (8 * k + 0))) := ((coreGetGP s7 (BitVec.ofNat 64 0x10c90) x16 (by decide) (by decide)).trans hw16s7)
  have h7 := step_or_10c90 (start + k * 29 + 7) s7 ((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) (zero_extend (m := 64) (inByte (8 * k + 0))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat7 hcnt7 hra7 hrb7
  have hSt8 : StableAgree s _ := hSt7.trans (stableAgree_gp s7 (BitVec.ofNat 64 0x10c90) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hPC8 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90)).regs.insert x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c90) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1)
  have hmin8 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90)).regs.insert x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c90) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1)
  have hmem8 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90)).regs.insert x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c90) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s7 (BitVec.ofNat 64 0x10c90) x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))).trans hmem7)
  have hw13s8 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredRd s7 (BitVec.ofNat 64 0x10c90) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) (by decide) (by decide))
  have hw10s8 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s7 (BitVec.ofNat 64 0x10c90) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s7
  have hw11s8 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s7 (BitVec.ofNat 64 0x10c90) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s7
  have hw12s8 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s7 (BitVec.ofNat 64 0x10c90) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s7
  have hw14s8 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) :=
    (fallThroughRetiredGet s7 (BitVec.ofNat 64 0x10c90) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s7
  have hw15s8 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) :=
    (fallThroughRetiredGet s7 (BitVec.ofNat 64 0x10c90) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s7
  have hw16s8 : _ = some (zero_extend (m := 64) (inByte (8 * k + 0))) :=
    (fallThroughRetiredGet s7 (BitVec.ofNat 64 0x10c90) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s7
  generalize hgen7 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s7) (BitVec.ofNat 64 0x10c90)).regs.insert x13 (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c90) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) = s8 at h7 hSt8 hPC8 hmin8 hmem8 hw13s8 hw10s8 hw11s8 hw12s8 hw14s8 hw15s8 hw16s8

  -- Step 8: or at 0x10c94
  have hbytes8 : FetchBytesAt (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94) 0x33#8 0xe7#8 0xe7#8 0x00#8 :=
    fetchBytesAt_10c94 (tryStepControlFlowAfterIncrement s8) image hInv.himageEq (hmem8.symm ▸ hInv.hmatches)
  have hplat8 : StepPlatform s8 (BitVec.ofNat 64 0x10c94) 0x33#8 0xe7#8 0xe7#8 0x00#8 mseccfgBits :=
    mkStepPlatform s8 mseccfgBits (BitVec.ofNat 64 0x10c94) 0x33#8 0xe7#8 0xe7#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt8 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c90) 4 = BitVec.ofNat 64 0x10c94 from by decide) ▸ hPC8) (by decide) hbytes8
  have hcnt8 : StepCounters s8 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt8 hart_state (by decide)).trans hInv.hhart, (hSt8 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt8 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin8⟩
  have hra8 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94)).regs.get? x15 = some ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) := ((coreGetGP s8 (BitVec.ofNat 64 0x10c94) x15 (by decide) (by decide)).trans hw15s8)
  have hrb8 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94)).regs.get? x14 = some ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) := ((coreGetGP s8 (BitVec.ofNat 64 0x10c94) x14 (by decide) (by decide)).trans hw14s8)
  have h8 := step_or_10c94 (start + k * 29 + 8) s8 ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat8 hcnt8 hra8 hrb8
  have hSt9 : StableAgree s _ := hSt8.trans (stableAgree_gp s8 (BitVec.ofNat 64 0x10c94) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have hPC9 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94)).regs.insert x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c94) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin9 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94)).regs.insert x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c94) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem9 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94)).regs.insert x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c94) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s8 (BitVec.ofNat 64 0x10c94) x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16))).trans hmem8)
  have hw14s9 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredRd s8 (BitVec.ofNat 64 0x10c94) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) (by decide) (by decide))
  have hw10s9 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s8 (BitVec.ofNat 64 0x10c94) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s8
  have hw11s9 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s8 (BitVec.ofNat 64 0x10c94) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s8
  have hw12s9 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s8 (BitVec.ofNat 64 0x10c94) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s8
  have hw13s9 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s8 (BitVec.ofNat 64 0x10c94) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s8
  have hw15s9 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) :=
    (fallThroughRetiredGet s8 (BitVec.ofNat 64 0x10c94) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s8
  have hw16s9 : _ = some (zero_extend (m := 64) (inByte (8 * k + 0))) :=
    (fallThroughRetiredGet s8 (BitVec.ofNat 64 0x10c94) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s8
  generalize hgen8 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x10c94)).regs.insert x14 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c94) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) = s9 at h8 hSt9 hPC9 hmin9 hmem9 hw14s9 hw10s9 hw11s9 hw12s9 hw13s9 hw15s9 hw16s9

  -- Step 9: lbu at 0x10c98
  have hbytes9 : FetchBytesAt (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98) 0x83#8 0xc7#8 0x55#8 0x00#8 :=
    fetchBytesAt_10c98 (tryStepControlFlowAfterIncrement s9) image hInv.himageEq (hmem9.symm ▸ hInv.hmatches)
  have hplat9 : StepPlatform s9 (BitVec.ofNat 64 0x10c98) 0x83#8 0xc7#8 0x55#8 0x00#8 mseccfgBits :=
    mkStepPlatform s9 mseccfgBits (BitVec.ofNat 64 0x10c98) 0x83#8 0xc7#8 0x55#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt9 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c94) 4 = BitVec.ofNat 64 0x10c98 from by decide) ▸ hPC9) (by decide) hbytes9
  have hcnt9 : StepCounters s9 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt9 hart_state (by decide)).trans hInv.hhart, (hSt9 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt9 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin9⟩
  have hx11c9 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)).regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s9 (BitVec.ofNat 64 0x10c98) x11 (by decide) (by decide)).trans hw11s9)
  obtain ⟨addr9, phys9, mmio9⟩ :=
    (hInv.hdata k (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)) hk (coreStableAgree s9 (BitVec.ofNat 64 0x10c98) hSt9)).1 hx11c9 5 (by decide)
  have hbyte9 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)).mem.get? (input0 + BitVec.ofNat 64 (8 * k + 5)).toNat = some (inByte (8 * k + 5)) :=
    hmem9.symm ▸ hInv.hinput (8 * k + 5) (by omega)
  have h9 := step_lbu_10c98 (start + k * 29 + 9) s9 (input0 + BitVec.ofNat 64 (8 * k + 5)) mstatusBits (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    (inByte (8 * k + 5)) inhibit cfg hplat9 hcnt9 ((coreGetStable s9 (BitVec.ofNat 64 0x10c98) mstatus (by decide) hSt9).trans hInv.hmstatus) ((coreGetStable s9 (BitVec.ofNat 64 0x10c98) cur_privilege (by decide) hSt9).trans hInv.hcur) hInv.hmprv
    addr9 phys9 mmio9 (leBytes_one_mem _ _ (inByte (8 * k + 5)) hbyte9)
  have hSt10 : StableAgree s _ := hSt9.trans (stableAgree_gp s9 (BitVec.ofNat 64 0x10c98) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 5))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have hPC10 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)).regs.insert x15 (zero_extend (m := 64) (inByte (8 * k + 5))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c98) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin10 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)).regs.insert x15 (zero_extend (m := 64) (inByte (8 * k + 5))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c98) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem10 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)).regs.insert x15 (zero_extend (m := 64) (inByte (8 * k + 5))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c98) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s9 (BitVec.ofNat 64 0x10c98) x15 (zero_extend (m := 64) (inByte (8 * k + 5)))).trans hmem9)
  have hw15s10 : _ = some (zero_extend (m := 64) (inByte (8 * k + 5))) :=
    (fallThroughRetiredRd s9 (BitVec.ofNat 64 0x10c98) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 5))) (by decide) (by decide))
  have hw10s10 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s9 (BitVec.ofNat 64 0x10c98) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 5))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s9
  have hw11s10 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s9 (BitVec.ofNat 64 0x10c98) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 5))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s9
  have hw12s10 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s9 (BitVec.ofNat 64 0x10c98) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 5))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s9
  have hw13s10 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s9 (BitVec.ofNat 64 0x10c98) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 5))) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s9
  have hw14s10 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s9 (BitVec.ofNat 64 0x10c98) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 5))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s9
  have hw16s10 : _ = some (zero_extend (m := 64) (inByte (8 * k + 0))) :=
    (fallThroughRetiredGet s9 (BitVec.ofNat 64 0x10c98) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (zero_extend (m := 64) (inByte (8 * k + 5))) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s9
  generalize hgen9 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s9) (BitVec.ofNat 64 0x10c98)).regs.insert x15 (zero_extend (m := 64) (inByte (8 * k + 5))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c98) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) = s10 at h9 hSt10 hPC10 hmin10 hmem10 hw15s10 hw10s10 hw11s10 hw12s10 hw13s10 hw14s10 hw16s10

  -- Step 10: lbu at 0x10c9c
  have hbytes10 : FetchBytesAt (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c) 0x03#8 0xc8#8 0x45#8 0x00#8 :=
    fetchBytesAt_10c9c (tryStepControlFlowAfterIncrement s10) image hInv.himageEq (hmem10.symm ▸ hInv.hmatches)
  have hplat10 : StepPlatform s10 (BitVec.ofNat 64 0x10c9c) 0x03#8 0xc8#8 0x45#8 0x00#8 mseccfgBits :=
    mkStepPlatform s10 mseccfgBits (BitVec.ofNat 64 0x10c9c) 0x03#8 0xc8#8 0x45#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt10 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c98) 4 = BitVec.ofNat 64 0x10c9c from by decide) ▸ hPC10) (by decide) hbytes10
  have hcnt10 : StepCounters s10 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt10 hart_state (by decide)).trans hInv.hhart, (hSt10 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt10 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin10⟩
  have hx11c10 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)).regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s10 (BitVec.ofNat 64 0x10c9c) x11 (by decide) (by decide)).trans hw11s10)
  obtain ⟨addr10, phys10, mmio10⟩ :=
    (hInv.hdata k (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)) hk (coreStableAgree s10 (BitVec.ofNat 64 0x10c9c) hSt10)).1 hx11c10 4 (by decide)
  have hbyte10 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)).mem.get? (input0 + BitVec.ofNat 64 (8 * k + 4)).toNat = some (inByte (8 * k + 4)) :=
    hmem10.symm ▸ hInv.hinput (8 * k + 4) (by omega)
  have h10 := step_lbu_10c9c (start + k * 29 + 10) s10 (input0 + BitVec.ofNat 64 (8 * k + 4)) mstatusBits (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    (inByte (8 * k + 4)) inhibit cfg hplat10 hcnt10 ((coreGetStable s10 (BitVec.ofNat 64 0x10c9c) mstatus (by decide) hSt10).trans hInv.hmstatus) ((coreGetStable s10 (BitVec.ofNat 64 0x10c9c) cur_privilege (by decide) hSt10).trans hInv.hcur) hInv.hmprv
    addr10 phys10 mmio10 (leBytes_one_mem _ _ (inByte (8 * k + 4)) hbyte10)
  have hSt11 : StableAgree s _ := hSt10.trans (stableAgree_gp s10 (BitVec.ofNat 64 0x10c9c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 4))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have hPC11 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)).regs.insert x16 (zero_extend (m := 64) (inByte (8 * k + 4))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c9c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin11 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)).regs.insert x16 (zero_extend (m := 64) (inByte (8 * k + 4))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c9c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem11 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)).regs.insert x16 (zero_extend (m := 64) (inByte (8 * k + 4))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c9c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s10 (BitVec.ofNat 64 0x10c9c) x16 (zero_extend (m := 64) (inByte (8 * k + 4)))).trans hmem10)
  have hw16s11 : _ = some (zero_extend (m := 64) (inByte (8 * k + 4))) :=
    (fallThroughRetiredRd s10 (BitVec.ofNat 64 0x10c9c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 4))) (by decide) (by decide))
  have hw10s11 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s10 (BitVec.ofNat 64 0x10c9c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 4))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s10
  have hw11s11 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s10 (BitVec.ofNat 64 0x10c9c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 4))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s10
  have hw12s11 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s10 (BitVec.ofNat 64 0x10c9c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 4))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s10
  have hw13s11 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s10 (BitVec.ofNat 64 0x10c9c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 4))) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s10
  have hw14s11 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s10 (BitVec.ofNat 64 0x10c9c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 4))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s10
  have hw15s11 : _ = some (zero_extend (m := 64) (inByte (8 * k + 5))) :=
    (fallThroughRetiredGet s10 (BitVec.ofNat 64 0x10c9c) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (zero_extend (m := 64) (inByte (8 * k + 4))) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s10
  generalize hgen10 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s10) (BitVec.ofNat 64 0x10c9c)).regs.insert x16 (zero_extend (m := 64) (inByte (8 * k + 4))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c9c) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s11 at h10 hSt11 hPC11 hmin11 hmem11 hw16s11 hw10s11 hw11s11 hw12s11 hw13s11 hw14s11 hw15s11

  -- Step 11: lbu at 0x10ca0
  have hbytes11 : FetchBytesAt (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0) 0x83#8 0xc8#8 0x65#8 0x00#8 :=
    fetchBytesAt_10ca0 (tryStepControlFlowAfterIncrement s11) image hInv.himageEq (hmem11.symm ▸ hInv.hmatches)
  have hplat11 : StepPlatform s11 (BitVec.ofNat 64 0x10ca0) 0x83#8 0xc8#8 0x65#8 0x00#8 mseccfgBits :=
    mkStepPlatform s11 mseccfgBits (BitVec.ofNat 64 0x10ca0) 0x83#8 0xc8#8 0x65#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt11 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c9c) 4 = BitVec.ofNat 64 0x10ca0 from by decide) ▸ hPC11) (by decide) hbytes11
  have hcnt11 : StepCounters s11 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt11 hart_state (by decide)).trans hInv.hhart, (hSt11 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt11 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin11⟩
  have hx11c11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)).regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s11 (BitVec.ofNat 64 0x10ca0) x11 (by decide) (by decide)).trans hw11s11)
  obtain ⟨addr11, phys11, mmio11⟩ :=
    (hInv.hdata k (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)) hk (coreStableAgree s11 (BitVec.ofNat 64 0x10ca0) hSt11)).1 hx11c11 6 (by decide)
  have hbyte11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)).mem.get? (input0 + BitVec.ofNat 64 (8 * k + 6)).toNat = some (inByte (8 * k + 6)) :=
    hmem11.symm ▸ hInv.hinput (8 * k + 6) (by omega)
  have h11 := step_lbu_10ca0 (start + k * 29 + 11) s11 (input0 + BitVec.ofNat 64 (8 * k + 6)) mstatusBits (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    (inByte (8 * k + 6)) inhibit cfg hplat11 hcnt11 ((coreGetStable s11 (BitVec.ofNat 64 0x10ca0) mstatus (by decide) hSt11).trans hInv.hmstatus) ((coreGetStable s11 (BitVec.ofNat 64 0x10ca0) cur_privilege (by decide) hSt11).trans hInv.hcur) hInv.hmprv
    addr11 phys11 mmio11 (leBytes_one_mem _ _ (inByte (8 * k + 6)) hbyte11)
  have hSt12 : StableAgree s _ := hSt11.trans (stableAgree_gp s11 (BitVec.ofNat 64 0x10ca0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 (zero_extend (m := 64) (inByte (8 * k + 6))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
  have hPC12 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)).regs.insert x17 (zero_extend (m := 64) (inByte (8 * k + 6))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin12 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)).regs.insert x17 (zero_extend (m := 64) (inByte (8 * k + 6))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem12 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)).regs.insert x17 (zero_extend (m := 64) (inByte (8 * k + 6))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s11 (BitVec.ofNat 64 0x10ca0) x17 (zero_extend (m := 64) (inByte (8 * k + 6)))).trans hmem11)
  have hw17s12 : _ = some (zero_extend (m := 64) (inByte (8 * k + 6))) :=
    (fallThroughRetiredRd s11 (BitVec.ofNat 64 0x10ca0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 (zero_extend (m := 64) (inByte (8 * k + 6))) (by decide) (by decide))
  have hw10s12 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s11 (BitVec.ofNat 64 0x10ca0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 (zero_extend (m := 64) (inByte (8 * k + 6))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s11
  have hw11s12 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s11 (BitVec.ofNat 64 0x10ca0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 (zero_extend (m := 64) (inByte (8 * k + 6))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s11
  have hw12s12 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s11 (BitVec.ofNat 64 0x10ca0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 (zero_extend (m := 64) (inByte (8 * k + 6))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s11
  have hw13s12 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s11 (BitVec.ofNat 64 0x10ca0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 (zero_extend (m := 64) (inByte (8 * k + 6))) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s11
  have hw14s12 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s11 (BitVec.ofNat 64 0x10ca0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 (zero_extend (m := 64) (inByte (8 * k + 6))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s11
  have hw15s12 : _ = some (zero_extend (m := 64) (inByte (8 * k + 5))) :=
    (fallThroughRetiredGet s11 (BitVec.ofNat 64 0x10ca0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 (zero_extend (m := 64) (inByte (8 * k + 6))) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s11
  have hw16s12 : _ = some (zero_extend (m := 64) (inByte (8 * k + 4))) :=
    (fallThroughRetiredGet s11 (BitVec.ofNat 64 0x10ca0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 (zero_extend (m := 64) (inByte (8 * k + 6))) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s11
  generalize hgen11 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s11) (BitVec.ofNat 64 0x10ca0)).regs.insert x17 (zero_extend (m := 64) (inByte (8 * k + 6))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s12 at h11 hSt12 hPC12 hmin12 hmem12 hw17s12 hw10s12 hw11s12 hw12s12 hw13s12 hw14s12 hw15s12 hw16s12

  -- Step 12: lbu at 0x10ca4
  have hbytes12 : FetchBytesAt (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4) 0x83#8 0xc2#8 0x75#8 0x00#8 :=
    fetchBytesAt_10ca4 (tryStepControlFlowAfterIncrement s12) image hInv.himageEq (hmem12.symm ▸ hInv.hmatches)
  have hplat12 : StepPlatform s12 (BitVec.ofNat 64 0x10ca4) 0x83#8 0xc2#8 0x75#8 0x00#8 mseccfgBits :=
    mkStepPlatform s12 mseccfgBits (BitVec.ofNat 64 0x10ca4) 0x83#8 0xc2#8 0x75#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt12 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca0) 4 = BitVec.ofNat 64 0x10ca4 from by decide) ▸ hPC12) (by decide) hbytes12
  have hcnt12 : StepCounters s12 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt12 hart_state (by decide)).trans hInv.hhart, (hSt12 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt12 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin12⟩
  have hx11c12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)).regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s12 (BitVec.ofNat 64 0x10ca4) x11 (by decide) (by decide)).trans hw11s12)
  obtain ⟨addr12, phys12, mmio12⟩ :=
    (hInv.hdata k (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)) hk (coreStableAgree s12 (BitVec.ofNat 64 0x10ca4) hSt12)).1 hx11c12 7 (by decide)
  have hbyte12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)).mem.get? (input0 + BitVec.ofNat 64 (8 * k + 7)).toNat = some (inByte (8 * k + 7)) :=
    hmem12.symm ▸ hInv.hinput (8 * k + 7) (by omega)
  have h12 := step_lbu_10ca4 (start + k * 29 + 12) s12 (input0 + BitVec.ofNat 64 (8 * k + 7)) mstatusBits (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    (inByte (8 * k + 7)) inhibit cfg hplat12 hcnt12 ((coreGetStable s12 (BitVec.ofNat 64 0x10ca4) mstatus (by decide) hSt12).trans hInv.hmstatus) ((coreGetStable s12 (BitVec.ofNat 64 0x10ca4) cur_privilege (by decide) hSt12).trans hInv.hcur) hInv.hmprv
    addr12 phys12 mmio12 (leBytes_one_mem _ _ (inByte (8 * k + 7)) hbyte12)
  have hSt13 : StableAgree s _ := hSt12.trans (stableAgree_gp s12 (BitVec.ofNat 64 0x10ca4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 (zero_extend (m := 64) (inByte (8 * k + 7))) (Or.inl rfl))
  have hPC13 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)).regs.insert x5 (zero_extend (m := 64) (inByte (8 * k + 7))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin13 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)).regs.insert x5 (zero_extend (m := 64) (inByte (8 * k + 7))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem13 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)).regs.insert x5 (zero_extend (m := 64) (inByte (8 * k + 7))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s12 (BitVec.ofNat 64 0x10ca4) x5 (zero_extend (m := 64) (inByte (8 * k + 7)))).trans hmem12)
  have hw5s13 : _ = some (zero_extend (m := 64) (inByte (8 * k + 7))) :=
    (fallThroughRetiredRd s12 (BitVec.ofNat 64 0x10ca4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 (zero_extend (m := 64) (inByte (8 * k + 7))) (by decide) (by decide))
  have hw10s13 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s12 (BitVec.ofNat 64 0x10ca4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 (zero_extend (m := 64) (inByte (8 * k + 7))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s12
  have hw11s13 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s12 (BitVec.ofNat 64 0x10ca4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 (zero_extend (m := 64) (inByte (8 * k + 7))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s12
  have hw12s13 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s12 (BitVec.ofNat 64 0x10ca4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 (zero_extend (m := 64) (inByte (8 * k + 7))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s12
  have hw13s13 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s12 (BitVec.ofNat 64 0x10ca4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 (zero_extend (m := 64) (inByte (8 * k + 7))) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s12
  have hw14s13 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s12 (BitVec.ofNat 64 0x10ca4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 (zero_extend (m := 64) (inByte (8 * k + 7))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s12
  have hw15s13 : _ = some (zero_extend (m := 64) (inByte (8 * k + 5))) :=
    (fallThroughRetiredGet s12 (BitVec.ofNat 64 0x10ca4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 (zero_extend (m := 64) (inByte (8 * k + 7))) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s12
  have hw16s13 : _ = some (zero_extend (m := 64) (inByte (8 * k + 4))) :=
    (fallThroughRetiredGet s12 (BitVec.ofNat 64 0x10ca4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 (zero_extend (m := 64) (inByte (8 * k + 7))) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s12
  have hw17s13 : _ = some (zero_extend (m := 64) (inByte (8 * k + 6))) :=
    (fallThroughRetiredGet s12 (BitVec.ofNat 64 0x10ca4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 (zero_extend (m := 64) (inByte (8 * k + 7))) x17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw17s12
  generalize hgen12 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s12) (BitVec.ofNat 64 0x10ca4)).regs.insert x5 (zero_extend (m := 64) (inByte (8 * k + 7))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s13 at h12 hSt13 hPC13 hmin13 hmem13 hw5s13 hw10s13 hw11s13 hw12s13 hw13s13 hw14s13 hw15s13 hw16s13 hw17s13

  -- Step 13: slli at 0x10ca8
  have hbytes13 : FetchBytesAt (tryStepControlFlowAfterIncrement s13) (BitVec.ofNat 64 0x10ca8) 0x93#8 0x97#8 0x87#8 0x00#8 :=
    fetchBytesAt_10ca8 (tryStepControlFlowAfterIncrement s13) image hInv.himageEq (hmem13.symm ▸ hInv.hmatches)
  have hplat13 : StepPlatform s13 (BitVec.ofNat 64 0x10ca8) 0x93#8 0x97#8 0x87#8 0x00#8 mseccfgBits :=
    mkStepPlatform s13 mseccfgBits (BitVec.ofNat 64 0x10ca8) 0x93#8 0x97#8 0x87#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt13 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca4) 4 = BitVec.ofNat 64 0x10ca8 from by decide) ▸ hPC13) (by decide) hbytes13
  have hcnt13 : StepCounters s13 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt13 hart_state (by decide)).trans hInv.hhart, (hSt13 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt13 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin13⟩
  have hr15s13 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s13) (BitVec.ofNat 64 0x10ca8)).regs.get? x15 = some (zero_extend (m := 64) (inByte (8 * k + 5))) := ((coreGetGP s13 (BitVec.ofNat 64 0x10ca8) x15 (by decide) (by decide)).trans hw15s13)
  have h13 := step_slli_10ca8 (start + k * 29 + 13) s13 (zero_extend (m := 64) (inByte (8 * k + 5))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat13 hcnt13 hr15s13
  have hSt14 : StableAgree s _ := hSt13.trans (stableAgree_gp s13 (BitVec.ofNat 64 0x10ca8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have hPC14 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s13) (BitVec.ofNat 64 0x10ca8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s13) (BitVec.ofNat 64 0x10ca8)).regs.insert x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin14 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s13) (BitVec.ofNat 64 0x10ca8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s13) (BitVec.ofNat 64 0x10ca8)).regs.insert x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem14 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s13) (BitVec.ofNat 64 0x10ca8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s13) (BitVec.ofNat 64 0x10ca8)).regs.insert x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s13 (BitVec.ofNat 64 0x10ca8) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8)).trans hmem13)
  have hw15s14 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) :=
    (fallThroughRetiredRd s13 (BitVec.ofNat 64 0x10ca8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) (by decide) (by decide))
  have hw5s14 : _ = some (zero_extend (m := 64) (inByte (8 * k + 7))) :=
    (fallThroughRetiredGet s13 (BitVec.ofNat 64 0x10ca8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw5s13
  have hw10s14 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s13 (BitVec.ofNat 64 0x10ca8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s13
  have hw11s14 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s13 (BitVec.ofNat 64 0x10ca8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s13
  have hw12s14 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s13 (BitVec.ofNat 64 0x10ca8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s13
  have hw13s14 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s13 (BitVec.ofNat 64 0x10ca8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s13
  have hw14s14 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s13 (BitVec.ofNat 64 0x10ca8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s13
  have hw16s14 : _ = some (zero_extend (m := 64) (inByte (8 * k + 4))) :=
    (fallThroughRetiredGet s13 (BitVec.ofNat 64 0x10ca8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s13
  have hw17s14 : _ = some (zero_extend (m := 64) (inByte (8 * k + 6))) :=
    (fallThroughRetiredGet s13 (BitVec.ofNat 64 0x10ca8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) x17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw17s13
  generalize hgen13 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s13) (BitVec.ofNat 64 0x10ca8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s13) (BitVec.ofNat 64 0x10ca8)).regs.insert x15 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s14 at h13 hSt14 hPC14 hmin14 hmem14 hw15s14 hw5s14 hw10s14 hw11s14 hw12s14 hw13s14 hw14s14 hw16s14 hw17s14

  -- Step 14: or at 0x10cac
  have hbytes14 : FetchBytesAt (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac) 0xb3#8 0xe7#8 0x07#8 0x01#8 :=
    fetchBytesAt_10cac (tryStepControlFlowAfterIncrement s14) image hInv.himageEq (hmem14.symm ▸ hInv.hmatches)
  have hplat14 : StepPlatform s14 (BitVec.ofNat 64 0x10cac) 0xb3#8 0xe7#8 0x07#8 0x01#8 mseccfgBits :=
    mkStepPlatform s14 mseccfgBits (BitVec.ofNat 64 0x10cac) 0xb3#8 0xe7#8 0x07#8 0x01#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt14 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca8) 4 = BitVec.ofNat 64 0x10cac from by decide) ▸ hPC14) (by decide) hbytes14
  have hcnt14 : StepCounters s14 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt14 hart_state (by decide)).trans hInv.hhart, (hSt14 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt14 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin14⟩
  have hra14 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac)).regs.get? x15 = some ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) := ((coreGetGP s14 (BitVec.ofNat 64 0x10cac) x15 (by decide) (by decide)).trans hw15s14)
  have hrb14 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac)).regs.get? x16 = some (zero_extend (m := 64) (inByte (8 * k + 4))) := ((coreGetGP s14 (BitVec.ofNat 64 0x10cac) x16 (by decide) (by decide)).trans hw16s14)
  have h14 := step_or_10cac (start + k * 29 + 14) s14 ((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) (zero_extend (m := 64) (inByte (8 * k + 4))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat14 hcnt14 hra14 hrb14
  have hSt15 : StableAgree s _ := hSt14.trans (stableAgree_gp s14 (BitVec.ofNat 64 0x10cac) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have hPC15 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac)).regs.insert x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cac) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin15 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac)).regs.insert x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cac) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem15 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac)).regs.insert x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cac) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s14 (BitVec.ofNat 64 0x10cac) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))).trans hmem14)
  have hw15s15 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) :=
    (fallThroughRetiredRd s14 (BitVec.ofNat 64 0x10cac) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) (by decide) (by decide))
  have hw5s15 : _ = some (zero_extend (m := 64) (inByte (8 * k + 7))) :=
    (fallThroughRetiredGet s14 (BitVec.ofNat 64 0x10cac) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw5s14
  have hw10s15 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s14 (BitVec.ofNat 64 0x10cac) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s14
  have hw11s15 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s14 (BitVec.ofNat 64 0x10cac) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s14
  have hw12s15 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s14 (BitVec.ofNat 64 0x10cac) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s14
  have hw13s15 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s14 (BitVec.ofNat 64 0x10cac) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s14
  have hw14s15 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s14 (BitVec.ofNat 64 0x10cac) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s14
  have hw16s15 : _ = some (zero_extend (m := 64) (inByte (8 * k + 4))) :=
    (fallThroughRetiredGet s14 (BitVec.ofNat 64 0x10cac) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s14
  have hw17s15 : _ = some (zero_extend (m := 64) (inByte (8 * k + 6))) :=
    (fallThroughRetiredGet s14 (BitVec.ofNat 64 0x10cac) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) x17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw17s14
  generalize hgen14 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s14) (BitVec.ofNat 64 0x10cac)).regs.insert x15 (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cac) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s15 at h14 hSt15 hPC15 hmin15 hmem15 hw15s15 hw5s15 hw10s15 hw11s15 hw12s15 hw13s15 hw14s15 hw16s15 hw17s15

  -- Step 15: slli at 0x10cb0
  have hbytes15 : FetchBytesAt (tryStepControlFlowAfterIncrement s15) (BitVec.ofNat 64 0x10cb0) 0x93#8 0x98#8 0x08#8 0x01#8 :=
    fetchBytesAt_10cb0 (tryStepControlFlowAfterIncrement s15) image hInv.himageEq (hmem15.symm ▸ hInv.hmatches)
  have hplat15 : StepPlatform s15 (BitVec.ofNat 64 0x10cb0) 0x93#8 0x98#8 0x08#8 0x01#8 mseccfgBits :=
    mkStepPlatform s15 mseccfgBits (BitVec.ofNat 64 0x10cb0) 0x93#8 0x98#8 0x08#8 0x01#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt15 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cac) 4 = BitVec.ofNat 64 0x10cb0 from by decide) ▸ hPC15) (by decide) hbytes15
  have hcnt15 : StepCounters s15 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt15 hart_state (by decide)).trans hInv.hhart, (hSt15 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt15 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin15⟩
  have hr17s15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s15) (BitVec.ofNat 64 0x10cb0)).regs.get? x17 = some (zero_extend (m := 64) (inByte (8 * k + 6))) := ((coreGetGP s15 (BitVec.ofNat 64 0x10cb0) x17 (by decide) (by decide)).trans hw17s15)
  have h15 := step_slli_10cb0 (start + k * 29 + 15) s15 (zero_extend (m := 64) (inByte (8 * k + 6))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat15 hcnt15 hr17s15
  have hSt16 : StableAgree s _ := hSt15.trans (stableAgree_gp s15 (BitVec.ofNat 64 0x10cb0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))
  have hPC16 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s15) (BitVec.ofNat 64 0x10cb0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s15) (BitVec.ofNat 64 0x10cb0)).regs.insert x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin16 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s15) (BitVec.ofNat 64 0x10cb0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s15) (BitVec.ofNat 64 0x10cb0)).regs.insert x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem16 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s15) (BitVec.ofNat 64 0x10cb0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s15) (BitVec.ofNat 64 0x10cb0)).regs.insert x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s15 (BitVec.ofNat 64 0x10cb0) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)).trans hmem15)
  have hw17s16 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) :=
    (fallThroughRetiredRd s15 (BitVec.ofNat 64 0x10cb0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) (by decide) (by decide))
  have hw5s16 : _ = some (zero_extend (m := 64) (inByte (8 * k + 7))) :=
    (fallThroughRetiredGet s15 (BitVec.ofNat 64 0x10cb0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw5s15
  have hw10s16 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s15 (BitVec.ofNat 64 0x10cb0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s15
  have hw11s16 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s15 (BitVec.ofNat 64 0x10cb0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s15
  have hw12s16 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s15 (BitVec.ofNat 64 0x10cb0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s15
  have hw13s16 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s15 (BitVec.ofNat 64 0x10cb0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s15
  have hw14s16 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s15 (BitVec.ofNat 64 0x10cb0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s15
  have hw15s16 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) :=
    (fallThroughRetiredGet s15 (BitVec.ofNat 64 0x10cb0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s15
  have hw16s16 : _ = some (zero_extend (m := 64) (inByte (8 * k + 4))) :=
    (fallThroughRetiredGet s15 (BitVec.ofNat 64 0x10cb0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s15
  generalize hgen15 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s15) (BitVec.ofNat 64 0x10cb0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s15) (BitVec.ofNat 64 0x10cb0)).regs.insert x17 ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s16 at h15 hSt16 hPC16 hmin16 hmem16 hw17s16 hw5s16 hw10s16 hw11s16 hw12s16 hw13s16 hw14s16 hw15s16 hw16s16

  -- Step 16: slli at 0x10cb4
  have hbytes16 : FetchBytesAt (tryStepControlFlowAfterIncrement s16) (BitVec.ofNat 64 0x10cb4) 0x93#8 0x92#8 0x82#8 0x01#8 :=
    fetchBytesAt_10cb4 (tryStepControlFlowAfterIncrement s16) image hInv.himageEq (hmem16.symm ▸ hInv.hmatches)
  have hplat16 : StepPlatform s16 (BitVec.ofNat 64 0x10cb4) 0x93#8 0x92#8 0x82#8 0x01#8 mseccfgBits :=
    mkStepPlatform s16 mseccfgBits (BitVec.ofNat 64 0x10cb4) 0x93#8 0x92#8 0x82#8 0x01#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt16 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb0) 4 = BitVec.ofNat 64 0x10cb4 from by decide) ▸ hPC16) (by decide) hbytes16
  have hcnt16 : StepCounters s16 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt16 hart_state (by decide)).trans hInv.hhart, (hSt16 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt16 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin16⟩
  have hr5s16 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s16) (BitVec.ofNat 64 0x10cb4)).regs.get? x5 = some (zero_extend (m := 64) (inByte (8 * k + 7))) := ((coreGetGP s16 (BitVec.ofNat 64 0x10cb4) x5 (by decide) (by decide)).trans hw5s16)
  have h16 := step_slli_10cb4 (start + k * 29 + 16) s16 (zero_extend (m := 64) (inByte (8 * k + 7))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat16 hcnt16 hr5s16
  have hSt17 : StableAgree s _ := hSt16.trans (stableAgree_gp s16 (BitVec.ofNat 64 0x10cb4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) (Or.inl rfl))
  have hPC17 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s16) (BitVec.ofNat 64 0x10cb4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s16) (BitVec.ofNat 64 0x10cb4)).regs.insert x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin17 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s16) (BitVec.ofNat 64 0x10cb4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s16) (BitVec.ofNat 64 0x10cb4)).regs.insert x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem17 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s16) (BitVec.ofNat 64 0x10cb4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s16) (BitVec.ofNat 64 0x10cb4)).regs.insert x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s16 (BitVec.ofNat 64 0x10cb4) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24)).trans hmem16)
  have hw5s17 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) :=
    (fallThroughRetiredRd s16 (BitVec.ofNat 64 0x10cb4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) (by decide) (by decide))
  have hw10s17 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s16 (BitVec.ofNat 64 0x10cb4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s16
  have hw11s17 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s16 (BitVec.ofNat 64 0x10cb4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s16
  have hw12s17 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s16 (BitVec.ofNat 64 0x10cb4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s16
  have hw13s17 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s16 (BitVec.ofNat 64 0x10cb4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s16
  have hw14s17 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s16 (BitVec.ofNat 64 0x10cb4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s16
  have hw15s17 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) :=
    (fallThroughRetiredGet s16 (BitVec.ofNat 64 0x10cb4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s16
  have hw16s17 : _ = some (zero_extend (m := 64) (inByte (8 * k + 4))) :=
    (fallThroughRetiredGet s16 (BitVec.ofNat 64 0x10cb4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s16
  have hw17s17 : _ = some ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) :=
    (fallThroughRetiredGet s16 (BitVec.ofNat 64 0x10cb4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) x17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw17s16
  generalize hgen16 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s16) (BitVec.ofNat 64 0x10cb4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s16) (BitVec.ofNat 64 0x10cb4)).regs.insert x5 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s17 at h16 hSt17 hPC17 hmin17 hmem17 hw5s17 hw10s17 hw11s17 hw12s17 hw13s17 hw14s17 hw15s17 hw16s17 hw17s17

  -- Step 17: or at 0x10cb8
  have hbytes17 : FetchBytesAt (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8) 0x33#8 0xe8#8 0x12#8 0x01#8 :=
    fetchBytesAt_10cb8 (tryStepControlFlowAfterIncrement s17) image hInv.himageEq (hmem17.symm ▸ hInv.hmatches)
  have hplat17 : StepPlatform s17 (BitVec.ofNat 64 0x10cb8) 0x33#8 0xe8#8 0x12#8 0x01#8 mseccfgBits :=
    mkStepPlatform s17 mseccfgBits (BitVec.ofNat 64 0x10cb8) 0x33#8 0xe8#8 0x12#8 0x01#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt17 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb4) 4 = BitVec.ofNat 64 0x10cb8 from by decide) ▸ hPC17) (by decide) hbytes17
  have hcnt17 : StepCounters s17 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt17 hart_state (by decide)).trans hInv.hhart, (hSt17 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt17 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin17⟩
  have hra17 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8)).regs.get? x5 = some ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) := ((coreGetGP s17 (BitVec.ofNat 64 0x10cb8) x5 (by decide) (by decide)).trans hw5s17)
  have hrb17 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8)).regs.get? x17 = some ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) := ((coreGetGP s17 (BitVec.ofNat 64 0x10cb8) x17 (by decide) (by decide)).trans hw17s17)
  have h17 := step_or_10cb8 (start + k * 29 + 17) s17 ((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat17 hcnt17 hra17 hrb17
  have hSt18 : StableAgree s _ := hSt17.trans (stableAgree_gp s17 (BitVec.ofNat 64 0x10cb8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have hPC18 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8)).regs.insert x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin18 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8)).regs.insert x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem18 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8)).regs.insert x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s17 (BitVec.ofNat 64 0x10cb8) x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16))).trans hmem17)
  have hw16s18 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) :=
    (fallThroughRetiredRd s17 (BitVec.ofNat 64 0x10cb8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) (by decide) (by decide))
  have hw10s18 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s17 (BitVec.ofNat 64 0x10cb8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s17
  have hw11s18 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s17 (BitVec.ofNat 64 0x10cb8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s17
  have hw12s18 : _ = some (BitVec.ofNat 64 (136 - 8 * k)) :=
    (fallThroughRetiredGet s17 (BitVec.ofNat 64 0x10cb8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s17
  have hw13s18 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s17 (BitVec.ofNat 64 0x10cb8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s17
  have hw14s18 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s17 (BitVec.ofNat 64 0x10cb8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s17
  have hw15s18 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) :=
    (fallThroughRetiredGet s17 (BitVec.ofNat 64 0x10cb8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s17
  generalize hgen17 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s17) (BitVec.ofNat 64 0x10cb8)).regs.insert x16 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s18 at h17 hSt18 hPC18 hmin18 hmem18 hw16s18 hw10s18 hw11s18 hw12s18 hw13s18 hw14s18 hw15s18

  -- Step 18: addia2 at 0x10cbc
  have hbytes18 : FetchBytesAt (tryStepControlFlowAfterIncrement s18) (BitVec.ofNat 64 0x10cbc) 0x13#8 0x06#8 0x86#8 0xff#8 :=
    fetchBytesAt_10cbc (tryStepControlFlowAfterIncrement s18) image hInv.himageEq (hmem18.symm ▸ hInv.hmatches)
  have hplat18 : StepPlatform s18 (BitVec.ofNat 64 0x10cbc) 0x13#8 0x06#8 0x86#8 0xff#8 mseccfgBits :=
    mkStepPlatform s18 mseccfgBits (BitVec.ofNat 64 0x10cbc) 0x13#8 0x06#8 0x86#8 0xff#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt18 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cb8) 4 = BitVec.ofNat 64 0x10cbc from by decide) ▸ hPC18) (by decide) hbytes18
  have hcnt18 : StepCounters s18 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt18 hart_state (by decide)).trans hInv.hhart, (hSt18 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt18 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin18⟩
  have hr12s18 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s18) (BitVec.ofNat 64 0x10cbc)).regs.get? x12 = some (BitVec.ofNat 64 (136 - 8 * k)) := ((coreGetGP s18 (BitVec.ofNat 64 0x10cbc) x12 (by decide) (by decide)).trans hw12s18)
  have h18 := step_addi_10cbc (start + k * 29 + 18) s18 (BitVec.ofNat 64 (136 - 8 * k)) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat18 hcnt18 hr12s18
  have hSt19 : StableAgree s _ := hSt18.trans (stableAgree_gp s18 (BitVec.ofNat 64 0x10cbc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hPC19 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s18) (BitVec.ofNat 64 0x10cbc)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s18) (BitVec.ofNat 64 0x10cbc)).regs.insert x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cbc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin19 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s18) (BitVec.ofNat 64 0x10cbc)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s18) (BitVec.ofNat 64 0x10cbc)).regs.insert x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cbc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem19 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s18) (BitVec.ofNat 64 0x10cbc)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s18) (BitVec.ofNat 64 0x10cbc)).regs.insert x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cbc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s18 (BitVec.ofNat 64 0x10cbc) x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12)).trans hmem18)
  have hw12s19 : _ = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (fallThroughRetiredRd s18 (BitVec.ofNat 64 0x10cbc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) (by decide) (by decide)).trans (congrArg some (decBy8 k (by omega)))
  have hw10s19 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s18 (BitVec.ofNat 64 0x10cbc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s18
  have hw11s19 : _ = some (input0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s18 (BitVec.ofNat 64 0x10cbc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s18
  have hw13s19 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s18 (BitVec.ofNat 64 0x10cbc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s18
  have hw14s19 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s18 (BitVec.ofNat 64 0x10cbc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s18
  have hw15s19 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) :=
    (fallThroughRetiredGet s18 (BitVec.ofNat 64 0x10cbc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s18
  have hw16s19 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) :=
    (fallThroughRetiredGet s18 (BitVec.ofNat 64 0x10cbc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s18
  generalize hgen18 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s18) (BitVec.ofNat 64 0x10cbc)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s18) (BitVec.ofNat 64 0x10cbc)).regs.insert x12 ((BitVec.ofNat 64 (136 - 8 * k)) + sign_extend (m := 64) 0xff8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cbc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s19 at h18 hSt19 hPC19 hmin19 hmem19 hw12s19 hw10s19 hw11s19 hw13s19 hw14s19 hw15s19 hw16s19

  -- Step 19: addia1 at 0x10cc0
  have hbytes19 : FetchBytesAt (tryStepControlFlowAfterIncrement s19) (BitVec.ofNat 64 0x10cc0) 0x93#8 0x85#8 0x85#8 0x00#8 :=
    fetchBytesAt_10cc0 (tryStepControlFlowAfterIncrement s19) image hInv.himageEq (hmem19.symm ▸ hInv.hmatches)
  have hplat19 : StepPlatform s19 (BitVec.ofNat 64 0x10cc0) 0x93#8 0x85#8 0x85#8 0x00#8 mseccfgBits :=
    mkStepPlatform s19 mseccfgBits (BitVec.ofNat 64 0x10cc0) 0x93#8 0x85#8 0x85#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt19 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cbc) 4 = BitVec.ofNat 64 0x10cc0 from by decide) ▸ hPC19) (by decide) hbytes19
  have hcnt19 : StepCounters s19 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt19 hart_state (by decide)).trans hInv.hhart, (hSt19 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt19 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin19⟩
  have hr11s19 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s19) (BitVec.ofNat 64 0x10cc0)).regs.get? x11 = some (input0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s19 (BitVec.ofNat 64 0x10cc0) x11 (by decide) (by decide)).trans hw11s19)
  have h19 := step_addi_10cc0 (start + k * 29 + 19) s19 (input0 + BitVec.ofNat 64 (8 * k)) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat19 hcnt19 hr11s19
  have hSt20 : StableAgree s _ := hSt19.trans (stableAgree_gp s19 (BitVec.ofNat 64 0x10cc0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) (Or.inr (Or.inr (Or.inl rfl))))
  have hPC20 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s19) (BitVec.ofNat 64 0x10cc0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s19) (BitVec.ofNat 64 0x10cc0)).regs.insert x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin20 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s19) (BitVec.ofNat 64 0x10cc0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s19) (BitVec.ofNat 64 0x10cc0)).regs.insert x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem20 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s19) (BitVec.ofNat 64 0x10cc0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s19) (BitVec.ofNat 64 0x10cc0)).regs.insert x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s19 (BitVec.ofNat 64 0x10cc0) x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12)).trans hmem19)
  have hw11s20 : _ = some (input0 + BitVec.ofNat 64 (8 * (k + 1))) :=
    (fallThroughRetiredRd s19 (BitVec.ofNat 64 0x10cc0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) (by decide) (by decide)).trans (congrArg some (incBy8 input0 k))
  have hw10s20 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s19 (BitVec.ofNat 64 0x10cc0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s19
  have hw12s20 : _ = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (fallThroughRetiredGet s19 (BitVec.ofNat 64 0x10cc0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s19
  have hw13s20 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) :=
    (fallThroughRetiredGet s19 (BitVec.ofNat 64 0x10cc0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s19
  have hw14s20 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s19 (BitVec.ofNat 64 0x10cc0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s19
  have hw15s20 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) :=
    (fallThroughRetiredGet s19 (BitVec.ofNat 64 0x10cc0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s19
  have hw16s20 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) :=
    (fallThroughRetiredGet s19 (BitVec.ofNat 64 0x10cc0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s19
  generalize hgen19 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s19) (BitVec.ofNat 64 0x10cc0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s19) (BitVec.ofNat 64 0x10cc0)).regs.insert x11 ((input0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s20 at h19 hSt20 hPC20 hmin20 hmem20 hw11s20 hw10s20 hw12s20 hw13s20 hw14s20 hw15s20 hw16s20

  -- Step 20: or at 0x10cc4
  have hbytes20 : FetchBytesAt (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4) 0xb3#8 0x66#8 0xd7#8 0x00#8 :=
    fetchBytesAt_10cc4 (tryStepControlFlowAfterIncrement s20) image hInv.himageEq (hmem20.symm ▸ hInv.hmatches)
  have hplat20 : StepPlatform s20 (BitVec.ofNat 64 0x10cc4) 0xb3#8 0x66#8 0xd7#8 0x00#8 mseccfgBits :=
    mkStepPlatform s20 mseccfgBits (BitVec.ofNat 64 0x10cc4) 0xb3#8 0x66#8 0xd7#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt20 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc0) 4 = BitVec.ofNat 64 0x10cc4 from by decide) ▸ hPC20) (by decide) hbytes20
  have hcnt20 : StepCounters s20 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt20 hart_state (by decide)).trans hInv.hhart, (hSt20 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt20 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin20⟩
  have hra20 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4)).regs.get? x14 = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) := ((coreGetGP s20 (BitVec.ofNat 64 0x10cc4) x14 (by decide) (by decide)).trans hw14s20)
  have hrb20 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4)).regs.get? x13 = some (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) := ((coreGetGP s20 (BitVec.ofNat 64 0x10cc4) x13 (by decide) (by decide)).trans hw13s20)
  have h20 := step_or_10cc4 (start + k * 29 + 20) s20 (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat20 hcnt20 hra20 hrb20
  have hSt21 : StableAgree s _ := hSt20.trans (stableAgree_gp s20 (BitVec.ofNat 64 0x10cc4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hPC21 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4)).regs.insert x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin21 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4)).regs.insert x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem21 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4)).regs.insert x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s20 (BitVec.ofNat 64 0x10cc4) x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))).trans hmem20)
  have hw13s21 : _ = some ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) :=
    (fallThroughRetiredRd s20 (BitVec.ofNat 64 0x10cc4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) (by decide) (by decide))
  have hw10s21 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s20 (BitVec.ofNat 64 0x10cc4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s20
  have hw11s21 : _ = some (input0 + BitVec.ofNat 64 (8 * (k + 1))) :=
    (fallThroughRetiredGet s20 (BitVec.ofNat 64 0x10cc4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s20
  have hw12s21 : _ = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (fallThroughRetiredGet s20 (BitVec.ofNat 64 0x10cc4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s20
  have hw14s21 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) :=
    (fallThroughRetiredGet s20 (BitVec.ofNat 64 0x10cc4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s20
  have hw15s21 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) :=
    (fallThroughRetiredGet s20 (BitVec.ofNat 64 0x10cc4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s20
  have hw16s21 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) :=
    (fallThroughRetiredGet s20 (BitVec.ofNat 64 0x10cc4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s20
  generalize hgen20 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s20) (BitVec.ofNat 64 0x10cc4)).regs.insert x13 ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s21 at h20 hSt21 hPC21 hmin21 hmem21 hw13s21 hw10s21 hw11s21 hw12s21 hw14s21 hw15s21 hw16s21

  -- Step 21: ld at 0x10cc8
  have hbytes21 : FetchBytesAt (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8) 0x03#8 0x37#8 0x05#8 0x00#8 :=
    fetchBytesAt_10cc8 (tryStepControlFlowAfterIncrement s21) image hInv.himageEq (hmem21.symm ▸ hInv.hmatches)
  have hplat21 : StepPlatform s21 (BitVec.ofNat 64 0x10cc8) 0x03#8 0x37#8 0x05#8 0x00#8 mseccfgBits :=
    mkStepPlatform s21 mseccfgBits (BitVec.ofNat 64 0x10cc8) 0x03#8 0x37#8 0x05#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt21 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc4) 4 = BitVec.ofNat 64 0x10cc8 from by decide) ▸ hPC21) (by decide) hbytes21
  have hcnt21 : StepCounters s21 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt21 hart_state (by decide)).trans hInv.hhart, (hSt21 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt21 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin21⟩
  have hx10c21 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)).regs.get? x10 = some (state0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s21 (BitVec.ofNat 64 0x10cc8) x10 (by decide) (by decide)).trans hw10s21)
  obtain ⟨ldaddr21, ldalign21, ldphys21, ldmmio21⟩ :=
    ((hInv.hdata k (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)) hk (coreStableAgree s21 (BitVec.ofNat 64 0x10cc8) hSt21)).2 hx10c21).1
  have hldmem21 : ∀ (i : Nat) (h : i < (leBytes 8 (origLane k)).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)).mem.get? ((state0 + BitVec.ofNat 64 (8 * k)).toNat + i) = some (leBytes 8 (origLane k))[i] := by
    intro i hi; rw [leBytes_length] at hi
    rw [leBytes_extractLsb (origLane k) i hi]
    have haddr : (state0 + BitVec.ofNat 64 (8 * k)).toNat + i = (state0 + BitVec.ofNat 64 (8 * k + i)).toNat := by
      rw [dstAddr_toNat state0 (8 * k) (by omega), dstAddr_toNat state0 (8 * k + i) (by omega)]; omega
    rw [haddr]
    exact hmem21.symm ▸ hInv.hunproc k i (Nat.le_refl k) (by omega) hi
  have h21 := ldStep (start + k * 29 + 21) s21 (BitVec.ofNat 64 0x10cc8) (state0 + BitVec.ofNat 64 (8 * k)) mstatusBits (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    (origLane k) inhibit cfg 0x03#8 0x37#8 0x05#8 0x00#8 hplat21 hcnt21 (by unfold BaseInstructionEncoding; decide)
    (by rw [show fetchWord 0x03#8 0x37#8 0x05#8 0x00#8 = (0x00053703 : BitVec 32) by decide]; exact ext_decode_ld_a4_a0_run _ hplat21.2.2.2.2.2.1 mseccfgBits hplat21.2.2.2.2.2.2)
    ((coreGetStable s21 (BitVec.ofNat 64 0x10cc8) mstatus (by decide) hSt21).trans hInv.hmstatus) ((coreGetStable s21 (BitVec.ofNat 64 0x10cc8) cur_privilege (by decide) hSt21).trans hInv.hcur) hInv.hmprv ldaddr21 ldalign21 ldphys21 ldmmio21 hldmem21
  have hSt22 : StableAgree s _ := hSt21.trans (stableAgree_gp s21 (BitVec.ofNat 64 0x10cc8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x14 (origLane k) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have hPC22 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)).regs.insert x14 (origLane k) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin22 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)).regs.insert x14 (origLane k) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem22 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)).regs.insert x14 (origLane k) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s21 (BitVec.ofNat 64 0x10cc8) x14 (origLane k)).trans hmem21)
  have hw14s22 : _ = some (origLane k) :=
    (fallThroughRetiredRd s21 (BitVec.ofNat 64 0x10cc8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x14 (origLane k) (by decide) (by decide))
  have hw10s22 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s21 (BitVec.ofNat 64 0x10cc8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x14 (origLane k) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s21
  have hw11s22 : _ = some (input0 + BitVec.ofNat 64 (8 * (k + 1))) :=
    (fallThroughRetiredGet s21 (BitVec.ofNat 64 0x10cc8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x14 (origLane k) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s21
  have hw12s22 : _ = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (fallThroughRetiredGet s21 (BitVec.ofNat 64 0x10cc8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x14 (origLane k) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s21
  have hw13s22 : _ = some ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) :=
    (fallThroughRetiredGet s21 (BitVec.ofNat 64 0x10cc8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x14 (origLane k) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s21
  have hw15s22 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) :=
    (fallThroughRetiredGet s21 (BitVec.ofNat 64 0x10cc8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x14 (origLane k) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw15s21
  have hw16s22 : _ = some (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) :=
    (fallThroughRetiredGet s21 (BitVec.ofNat 64 0x10cc8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x14 (origLane k) x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw16s21
  generalize hgen21 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s21) (BitVec.ofNat 64 0x10cc8)).regs.insert x14 (origLane k) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s22 at h21 hSt22 hPC22 hmin22 hmem22 hw14s22 hw10s22 hw11s22 hw12s22 hw13s22 hw15s22 hw16s22

  -- Step 22: or at 0x10ccc
  have hbytes22 : FetchBytesAt (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc) 0xb3#8 0x67#8 0xf8#8 0x00#8 :=
    fetchBytesAt_10ccc (tryStepControlFlowAfterIncrement s22) image hInv.himageEq (hmem22.symm ▸ hInv.hmatches)
  have hplat22 : StepPlatform s22 (BitVec.ofNat 64 0x10ccc) 0xb3#8 0x67#8 0xf8#8 0x00#8 mseccfgBits :=
    mkStepPlatform s22 mseccfgBits (BitVec.ofNat 64 0x10ccc) 0xb3#8 0x67#8 0xf8#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt22 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cc8) 4 = BitVec.ofNat 64 0x10ccc from by decide) ▸ hPC22) (by decide) hbytes22
  have hcnt22 : StepCounters s22 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt22 hart_state (by decide)).trans hInv.hhart, (hSt22 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt22 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin22⟩
  have hra22 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc)).regs.get? x16 = some (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) := ((coreGetGP s22 (BitVec.ofNat 64 0x10ccc) x16 (by decide) (by decide)).trans hw16s22)
  have hrb22 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc)).regs.get? x15 = some (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) := ((coreGetGP s22 (BitVec.ofNat 64 0x10ccc) x15 (by decide) (by decide)).trans hw15s22)
  have h22 := step_or_10ccc (start + k * 29 + 22) s22 (((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat22 hcnt22 hra22 hrb22
  have hSt23 : StableAgree s _ := hSt22.trans (stableAgree_gp s22 (BitVec.ofNat 64 0x10ccc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have hPC23 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc)).regs.insert x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ccc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin23 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc)).regs.insert x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ccc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem23 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc)).regs.insert x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ccc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s22 (BitVec.ofNat 64 0x10ccc) x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4)))))).trans hmem22)
  have hw15s23 : _ = some ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) :=
    (fallThroughRetiredRd s22 (BitVec.ofNat 64 0x10ccc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) (by decide) (by decide))
  have hw10s23 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s22 (BitVec.ofNat 64 0x10ccc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s22
  have hw11s23 : _ = some (input0 + BitVec.ofNat 64 (8 * (k + 1))) :=
    (fallThroughRetiredGet s22 (BitVec.ofNat 64 0x10ccc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s22
  have hw12s23 : _ = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (fallThroughRetiredGet s22 (BitVec.ofNat 64 0x10ccc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s22
  have hw13s23 : _ = some ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) :=
    (fallThroughRetiredGet s22 (BitVec.ofNat 64 0x10ccc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s22
  have hw14s23 : _ = some (origLane k) :=
    (fallThroughRetiredGet s22 (BitVec.ofNat 64 0x10ccc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s22
  generalize hgen22 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s22) (BitVec.ofNat 64 0x10ccc)).regs.insert x15 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ccc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s23 at h22 hSt23 hPC23 hmin23 hmem23 hw15s23 hw10s23 hw11s23 hw12s23 hw13s23 hw14s23

  -- Step 23: slli at 0x10cd0
  have hbytes23 : FetchBytesAt (tryStepControlFlowAfterIncrement s23) (BitVec.ofNat 64 0x10cd0) 0x93#8 0x97#8 0x07#8 0x02#8 :=
    fetchBytesAt_10cd0 (tryStepControlFlowAfterIncrement s23) image hInv.himageEq (hmem23.symm ▸ hInv.hmatches)
  have hplat23 : StepPlatform s23 (BitVec.ofNat 64 0x10cd0) 0x93#8 0x97#8 0x07#8 0x02#8 mseccfgBits :=
    mkStepPlatform s23 mseccfgBits (BitVec.ofNat 64 0x10cd0) 0x93#8 0x97#8 0x07#8 0x02#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt23 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10ccc) 4 = BitVec.ofNat 64 0x10cd0 from by decide) ▸ hPC23) (by decide) hbytes23
  have hcnt23 : StepCounters s23 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt23 hart_state (by decide)).trans hInv.hhart, (hSt23 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt23 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin23⟩
  have hr15s23 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s23) (BitVec.ofNat 64 0x10cd0)).regs.get? x15 = some ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) := ((coreGetGP s23 (BitVec.ofNat 64 0x10cd0) x15 (by decide) (by decide)).trans hw15s23)
  have h23 := step_slli_10cd0 (start + k * 29 + 23) s23 ((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat23 hcnt23 hr15s23
  have hSt24 : StableAgree s _ := hSt23.trans (stableAgree_gp s23 (BitVec.ofNat 64 0x10cd0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have hPC24 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s23) (BitVec.ofNat 64 0x10cd0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s23) (BitVec.ofNat 64 0x10cd0)).regs.insert x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin24 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s23) (BitVec.ofNat 64 0x10cd0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s23) (BitVec.ofNat 64 0x10cd0)).regs.insert x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem24 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s23) (BitVec.ofNat 64 0x10cd0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s23) (BitVec.ofNat 64 0x10cd0)).regs.insert x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s23 (BitVec.ofNat 64 0x10cd0) x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32)).trans hmem23)
  have hw15s24 : _ = some (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) :=
    (fallThroughRetiredRd s23 (BitVec.ofNat 64 0x10cd0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) (by decide) (by decide))
  have hw10s24 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s23 (BitVec.ofNat 64 0x10cd0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s23
  have hw11s24 : _ = some (input0 + BitVec.ofNat 64 (8 * (k + 1))) :=
    (fallThroughRetiredGet s23 (BitVec.ofNat 64 0x10cd0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s23
  have hw12s24 : _ = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (fallThroughRetiredGet s23 (BitVec.ofNat 64 0x10cd0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s23
  have hw13s24 : _ = some ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) :=
    (fallThroughRetiredGet s23 (BitVec.ofNat 64 0x10cd0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw13s23
  have hw14s24 : _ = some (origLane k) :=
    (fallThroughRetiredGet s23 (BitVec.ofNat 64 0x10cd0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s23
  generalize hgen23 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s23) (BitVec.ofNat 64 0x10cd0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s23) (BitVec.ofNat 64 0x10cd0)).regs.insert x15 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s24 at h23 hSt24 hPC24 hmin24 hmem24 hw15s24 hw10s24 hw11s24 hw12s24 hw13s24 hw14s24

  -- Step 24: or at 0x10cd4
  have hbytes24 : FetchBytesAt (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4) 0xb3#8 0xe6#8 0xd7#8 0x00#8 :=
    fetchBytesAt_10cd4 (tryStepControlFlowAfterIncrement s24) image hInv.himageEq (hmem24.symm ▸ hInv.hmatches)
  have hplat24 : StepPlatform s24 (BitVec.ofNat 64 0x10cd4) 0xb3#8 0xe6#8 0xd7#8 0x00#8 mseccfgBits :=
    mkStepPlatform s24 mseccfgBits (BitVec.ofNat 64 0x10cd4) 0xb3#8 0xe6#8 0xd7#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt24 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd0) 4 = BitVec.ofNat 64 0x10cd4 from by decide) ▸ hPC24) (by decide) hbytes24
  have hcnt24 : StepCounters s24 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt24 hart_state (by decide)).trans hInv.hhart, (hSt24 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt24 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin24⟩
  have hra24 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4)).regs.get? x15 = some (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) := ((coreGetGP s24 (BitVec.ofNat 64 0x10cd4) x15 (by decide) (by decide)).trans hw15s24)
  have hrb24 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4)).regs.get? x13 = some ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) := ((coreGetGP s24 (BitVec.ofNat 64 0x10cd4) x13 (by decide) (by decide)).trans hw13s24)
  have h24 := step_or_10cd4 (start + k * 29 + 24) s24 (((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat24 hcnt24 hra24 hrb24
  have hSt25 : StableAgree s _ := hSt24.trans (stableAgree_gp s24 (BitVec.ofNat 64 0x10cd4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hPC25 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4)).regs.insert x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin25 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4)).regs.insert x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem25 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4)).regs.insert x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s24 (BitVec.ofNat 64 0x10cd4) x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))).trans hmem24)
  have hw13s25 : _ = some ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) :=
    (fallThroughRetiredRd s24 (BitVec.ofNat 64 0x10cd4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) (by decide) (by decide))
  have hw10s25 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s24 (BitVec.ofNat 64 0x10cd4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s24
  have hw11s25 : _ = some (input0 + BitVec.ofNat 64 (8 * (k + 1))) :=
    (fallThroughRetiredGet s24 (BitVec.ofNat 64 0x10cd4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s24
  have hw12s25 : _ = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (fallThroughRetiredGet s24 (BitVec.ofNat 64 0x10cd4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s24
  have hw14s25 : _ = some (origLane k) :=
    (fallThroughRetiredGet s24 (BitVec.ofNat 64 0x10cd4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw14s24
  generalize hgen24 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s24) (BitVec.ofNat 64 0x10cd4)).regs.insert x13 ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd4) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s25 at h24 hSt25 hPC25 hmin25 hmem25 hw13s25 hw10s25 hw11s25 hw12s25 hw14s25

  -- Step 25: xor at 0x10cd8
  have hbytes25 : FetchBytesAt (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8) 0xb3#8 0x46#8 0xd7#8 0x00#8 :=
    fetchBytesAt_10cd8 (tryStepControlFlowAfterIncrement s25) image hInv.himageEq (hmem25.symm ▸ hInv.hmatches)
  have hplat25 : StepPlatform s25 (BitVec.ofNat 64 0x10cd8) 0xb3#8 0x46#8 0xd7#8 0x00#8 mseccfgBits :=
    mkStepPlatform s25 mseccfgBits (BitVec.ofNat 64 0x10cd8) 0xb3#8 0x46#8 0xd7#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt25 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd4) 4 = BitVec.ofNat 64 0x10cd8 from by decide) ▸ hPC25) (by decide) hbytes25
  have hcnt25 : StepCounters s25 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt25 hart_state (by decide)).trans hInv.hhart, (hSt25 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt25 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin25⟩
  have hra25 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8)).regs.get? x14 = some (origLane k) := ((coreGetGP s25 (BitVec.ofNat 64 0x10cd8) x14 (by decide) (by decide)).trans hw14s25)
  have hrb25 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8)).regs.get? x13 = some ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) := ((coreGetGP s25 (BitVec.ofNat 64 0x10cd8) x13 (by decide) (by decide)).trans hw13s25)
  have h25 := step_xor_10cd8 (start + k * 29 + 25) s25 (origLane k) ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat25 hcnt25 hra25 hrb25
  have hSt26 : StableAgree s _ := hSt25.trans (stableAgree_gp s25 (BitVec.ofNat 64 0x10cd8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hPC26 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8)).regs.insert x13 ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin26 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8)).regs.insert x13 ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem26 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8)).regs.insert x13 ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = s.mem :=
    (retiredMem _ _ _).trans ((fallThroughMem s25 (BitVec.ofNat 64 0x10cd8) x13 ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0)))))))).trans hmem25)
  have hw13s26 : _ = some ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))) :=
    (fallThroughRetiredRd s25 (BitVec.ofNat 64 0x10cd8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))) (by decide) (by decide))
  have hw10s26 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) :=
    (fallThroughRetiredGet s25 (BitVec.ofNat 64 0x10cd8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))) x10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw10s25
  have hw11s26 : _ = some (input0 + BitVec.ofNat 64 (8 * (k + 1))) :=
    (fallThroughRetiredGet s25 (BitVec.ofNat 64 0x10cd8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s25
  have hw12s26 : _ = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (fallThroughRetiredGet s25 (BitVec.ofNat 64 0x10cd8) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x13 ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s25
  generalize hgen25 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s25) (BitVec.ofNat 64 0x10cd8)).regs.insert x13 ((origLane k) ^^^ ((((((zero_extend (m := 64) (inByte (8 * k + 7))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 6))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 5))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 4))))) <<< 32) ||| ((((zero_extend (m := 64) (inByte (8 * k + 3))) <<< 24) ||| ((zero_extend (m := 64) (inByte (8 * k + 2))) <<< 16)) ||| (((zero_extend (m := 64) (inByte (8 * k + 1))) <<< 8) ||| (zero_extend (m := 64) (inByte (8 * k + 0))))))) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd8) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s26 at h25 hSt26 hPC26 hmin26 hmem26 hw13s26 hw10s26 hw11s26 hw12s26

  -- Step 26: sd at 0x10cdc
  have hbytes26 : FetchBytesAt (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc) 0x23#8 0x30#8 0xd5#8 0x00#8 :=
    fetchBytesAt_10cdc (tryStepControlFlowAfterIncrement s26) image hInv.himageEq (hmem26.symm ▸ hInv.hmatches)
  have hplat26 : StepPlatform s26 (BitVec.ofNat 64 0x10cdc) 0x23#8 0x30#8 0xd5#8 0x00#8 mseccfgBits :=
    mkStepPlatform s26 mseccfgBits (BitVec.ofNat 64 0x10cdc) 0x23#8 0x30#8 0xd5#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt26 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cd8) 4 = BitVec.ofNat 64 0x10cdc from by decide) ▸ hPC26) (by decide) hbytes26
  have hcnt26 : StepCounters s26 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt26 hart_state (by decide)).trans hInv.hhart, (hSt26 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt26 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin26⟩
  have hx13c26 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)).regs.get? x13 = some (origLane k ^^^ inputLane inByte k) := by
    have h := ((coreGetGP s26 (BitVec.ofNat 64 0x10cdc) x13 (by decide) (by decide)).trans hw13s26)
    rwa [assemble_leWord (inByte (8 * k + 0)) (inByte (8 * k + 1)) (inByte (8 * k + 2)) (inByte (8 * k + 3)) (inByte (8 * k + 4)) (inByte (8 * k + 5)) (inByte (8 * k + 6)) (inByte (8 * k + 7))] at h
  have hx10c26 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)).regs.get? x10 = some (state0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s26 (BitVec.ofNat 64 0x10cdc) x10 (by decide) (by decide)).trans hw10s26)
  obtain ⟨sdaddr26, sdalign26, sdphys26, sdmmio26⟩ :=
    ((hInv.hdata k (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)) hk (coreStableAgree s26 (BitVec.ofNat 64 0x10cdc) hSt26)).2 hx10c26).2
  have hwrite26 := writeBytes_word_run (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)) (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k)
  have h26 := sdStep (start + k * 29 + 26) s26 _ (BitVec.ofNat 64 0x10cdc) (state0 + BitVec.ofNat 64 (8 * k)) mstatusBits (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    (origLane k ^^^ inputLane inByte k) inhibit cfg 0x23#8 0x30#8 0xd5#8 0x00#8 hplat26 hcnt26 (by unfold BaseInstructionEncoding; decide)
    (by rw [show fetchWord 0x23#8 0x30#8 0xd5#8 0x00#8 = (0x00d53023 : BitVec 32) by decide]; exact ext_decode_sd_a3_a0_run _ hplat26.2.2.2.2.2.1 mseccfgBits hplat26.2.2.2.2.2.2)
    ((coreGetStable s26 (BitVec.ofNat 64 0x10cdc) mstatus (by decide) hSt26).trans hInv.hmstatus) ((coreGetStable s26 (BitVec.ofNat 64 0x10cdc) cur_privilege (by decide) hSt26).trans hInv.hcur) hInv.hmprv hx13c26 sdaddr26 sdalign26 sdphys26 sdmmio26 hwrite26
  have hSt27 : StableAgree s _ := hSt26.trans (stableAgree_store s26 { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)) with mem := insertWord (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)).mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) } (BitVec.ofNat 64 0x10cdc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) rfl)
  have hPC27 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)) with mem := insertWord (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)).mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cdc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin27 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)) with mem := insertWord (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)).mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cdc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem27 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)) with mem := insertWord (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)).mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cdc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = insertWord s.mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) := by
    exact congrArg (fun mm => insertWord mm (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k)) hmem26
  have hw10s27 : _ = some (state0 + BitVec.ofNat 64 (8 * k)) := (sbRetiredGet s26 { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)) with mem := insertWord (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)).mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) } (BitVec.ofNat 64 0x10cdc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) rfl x10 (by decide) (by decide) (by decide) (by decide)).trans hw10s26
  have hw11s27 : _ = some (input0 + BitVec.ofNat 64 (8 * (k + 1))) := (sbRetiredGet s26 { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)) with mem := insertWord (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)).mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) } (BitVec.ofNat 64 0x10cdc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) rfl x11 (by decide) (by decide) (by decide) (by decide)).trans hw11s26
  have hw12s27 : _ = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) := (sbRetiredGet s26 { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)) with mem := insertWord (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)).mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) } (BitVec.ofNat 64 0x10cdc) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) rfl x12 (by decide) (by decide) (by decide) (by decide)).trans hw12s26
  generalize hgen26 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)) with mem := insertWord (coreControlFlowNextState (tryStepControlFlowAfterIncrement s26) (BitVec.ofNat 64 0x10cdc)).mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10cdc) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s27 at h26 hSt27 hPC27 hmin27 hmem27 hw10s27 hw11s27 hw12s27
  have hmatchesW : image.matchesMemory (insertWord s.mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k)) :=
    matchesMemory_insertWord image s.mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) hInv.hmatches
      (fun i hi => by
        have h := hInv.hstateImg (8 * k + i) (by omega)
        rwa [show (state0 + BitVec.ofNat 64 (8 * k)).toNat + i = (state0 + BitVec.ofNat 64 (8 * k + i)).toNat by
          rw [dstAddr_toNat state0 (8 * k) (by omega), dstAddr_toNat state0 (8 * k + i) (by omega)]; omega] )

  -- Step 27: addia0 at 0x10ce0
  have hbytes27 : FetchBytesAt (tryStepControlFlowAfterIncrement s27) (BitVec.ofNat 64 0x10ce0) 0x13#8 0x05#8 0x85#8 0x00#8 :=
    fetchBytesAt_10ce0 (tryStepControlFlowAfterIncrement s27) image hInv.himageEq (hmem27.symm ▸ hmatchesW)
  have hplat27 : StepPlatform s27 (BitVec.ofNat 64 0x10ce0) 0x13#8 0x05#8 0x85#8 0x00#8 mseccfgBits :=
    mkStepPlatform s27 mseccfgBits (BitVec.ofNat 64 0x10ce0) 0x13#8 0x05#8 0x85#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt27 ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10cdc) 4 = BitVec.ofNat 64 0x10ce0 from by decide) ▸ hPC27) (by decide) hbytes27
  have hcnt27 : StepCounters s27 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) inhibit cfg := ⟨(hSt27 hart_state (by decide)).trans hInv.hhart, (hSt27 mcountinhibit (by decide)).trans hInv.hinhibit, (hSt27 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin27⟩
  have hr10s27 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s27) (BitVec.ofNat 64 0x10ce0)).regs.get? x10 = some (state0 + BitVec.ofNat 64 (8 * k)) := ((coreGetGP s27 (BitVec.ofNat 64 0x10ce0) x10 (by decide) (by decide)).trans hw10s27)
  have h27 := step_addi_10ce0 (start + k * 29 + 27) s27 (state0 + BitVec.ofNat 64 (8 * k)) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) mseccfgBits
    inhibit cfg hplat27 hcnt27 hr10s27
  have hSt28 : StableAgree s _ := hSt27.trans (stableAgree_gp s27 (BitVec.ofNat 64 0x10ce0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x10 ((state0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) (Or.inr (Or.inl rfl)))
  have hPC28 := afterIncRetiredPC { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s27) (BitVec.ofNat 64 0x10ce0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s27) (BitVec.ofNat 64 0x10ce0)).regs.insert x10 ((state0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmin28 := retiredMinstret { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s27) (BitVec.ofNat 64 0x10ce0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s27) (BitVec.ofNat 64 0x10ce0)).regs.insert x10 ((state0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
  have hmem28 : (tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s27) (BitVec.ofNat 64 0x10ce0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s27) (BitVec.ofNat 64 0x10ce0)).regs.insert x10 ((state0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)).mem = insertWord s.mem (state0 + BitVec.ofNat 64 (8 * k)).toNat (origLane k ^^^ inputLane inByte k) :=
    (retiredMem _ _ _).trans ((fallThroughMem s27 (BitVec.ofNat 64 0x10ce0) x10 ((state0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12)).trans hmem27)
  have hw10s28 : _ = some (state0 + BitVec.ofNat 64 (8 * (k + 1))) :=
    (fallThroughRetiredRd s27 (BitVec.ofNat 64 0x10ce0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x10 ((state0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) (by decide) (by decide)).trans (congrArg some (incBy8 state0 k))
  have hw11s28 : _ = some (input0 + BitVec.ofNat 64 (8 * (k + 1))) :=
    (fallThroughRetiredGet s27 (BitVec.ofNat 64 0x10ce0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x10 ((state0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw11s27
  have hw12s28 : _ = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (fallThroughRetiredGet s27 (BitVec.ofNat 64 0x10ce0) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) x10 ((state0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw12s27
  generalize hgen27 : tryStepControlFlowAfterRetired { (coreControlFlowNextState (tryStepControlFlowAfterIncrement s27) (BitVec.ofNat 64 0x10ce0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s27) (BitVec.ofNat 64 0x10ce0)).regs.insert x10 ((state0 + BitVec.ofNat 64 (8 * k)) + sign_extend (m := 64) 8#12) } (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce0) 4) (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) = s28 at h27 hSt28 hPC28 hmin28 hmem28 hw10s28 hw11s28 hw12s28
  refine ⟨s28, ?_, ?_⟩
  · trace_steps [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
      h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  refine ⟨?_, hw10s28, hw11s28, hw12s28,
    (hSt28 x1 (by decide)).trans hInv.hra,
    (hSt28 cur_privilege (by decide)).trans hInv.hcur,
    (hSt28 mstatus (by decide)).trans hInv.hmstatus,
    hInv.hmprv, (hSt28 mseccfg (by decide)).trans hInv.hmseccfg,
    (hSt28 hart_state (by decide)).trans hInv.hhart,
    (hSt28 mcountinhibit (by decide)).trans hInv.hinhibit,
    hInv.hnotInhibited, (hSt28 minstretcfg (by decide)).trans hInv.hcfg,
    hInv.hmachineEnabled, ⟨_, hmin28⟩, hInv.himageEq, ?_, ?_, ?_, ?_,
    (by omega), hInv.hstateFits, hInv.hinputFits, hInv.hstateImg, hInv.hdisj,
    AbstractPlatform.mono hSt28 hInv.hplat, AbstractDataAccess.mono hSt28 hInv.hdata,
    AbstractElp.mono hSt28 hInv.hElp, hInv.hstable.trans hSt28, ?_⟩
  · -- hPC
    exact (afterIncGet s28 PC (by decide)).symm.trans
      ((show Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce0) 4 = BitVec.ofNat 64 0x10ce4 from by decide)
        ▸ hPC28)
  · -- hmatches
    exact hmem28.symm ▸ hmatchesW
  · -- hunproc (lanes ≥ k+1 unchanged)
    intro m i hm hm2 hi
    rw [hmem28, insertWord_get_out _ _ _ _ (fun i' hi' => by
      rw [dstAddr_toNat state0 (8 * k) (by omega), dstAddr_toNat state0 (8 * m + i) (by omega)]
      omega)]
    exact hInv.hunproc m i (by omega) hm2 hi
  · -- hproc (lanes < k unchanged; lane k newly stored)
    intro m i hm hi
    rw [hmem28]
    rcases Nat.lt_or_ge m k with hlt | hge
    · rw [insertWord_get_out _ _ _ _ (fun i' hi' => by
        rw [dstAddr_toNat state0 (8 * k) (by omega), dstAddr_toNat state0 (8 * m + i) (by omega)]
        omega)]
      exact hInv.hproc m i hlt hi
    · have hmk : m = k := by omega
      subst hmk
      rw [show (state0 + BitVec.ofNat 64 (8 * m + i)).toNat
            = (state0 + BitVec.ofNat 64 (8 * m)).toNat + i from by
          rw [dstAddr_toNat state0 (8 * m) (by omega), dstAddr_toNat state0 (8 * m + i) (by omega)]
          omega]
      rw [insertWord_get_in _ _ _ i hi]
  · -- hinput (input region preserved)
    intro j hj
    rw [hmem28, insertWord_get_out _ _ _ _ (fun i' hi' => by
      rw [show (state0 + BitVec.ofNat 64 (8 * k)).toNat + i'
            = (state0 + BitVec.ofNat 64 (8 * k + i')).toNat from by
          rw [dstAddr_toNat state0 (8 * k) (by omega), dstAddr_toNat state0 (8 * k + i') (by omega)]
          omega]
      exact (hInv.hdisj (8 * k + i') j (by omega) hj).symm)]
    exact hInv.hinput j hj
  · -- hframe (the lane store stays inside the rate window)
    refine memFramed_rate_intro (fun addr haddr => ?_)
    rw [hmem28]
    exact frame_rate_store hInv.hstateFits hk
      (fun a ha => memFramed_rate_apply hInv.hframe a ha) addr haddr

/-! ## Deliverable 4d: one taken loop iteration `xorblock_adv` -/

set_option maxHeartbeats 2000000 in
/-- One taken loop iteration (`k < 16`, so the back-edge `bnez` is taken): a length-29 trace from the
loop head `0x10c74` back to itself, re-establishing `XorBlockInv (k+1)`. -/
theorem xorblock_adv (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (sref : State) (start k : Nat) (s : State)
    (hk16 : k < 16)
    (hInv : XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref k s) :
    ∃ s', Trace (start + k * 29) 29 s s' ∧
      XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
        origLane inByte sref (k + 1) s' := by
  obtain ⟨s28, htr, hAt⟩ := xorblock_body_core state0 input0 retAddr image mseccfgBits mstatusBits
    inhibit cfg origLane inByte sref start k s (by omega) hInv
  obtain ⟨retired28, hret28⟩ := hAt.hminstret
  have hbytes28 : FetchBytesAt (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4)
      0xe3#8 0x18#8 0x06#8 0xf8#8 :=
    fetchBytesAt_10ce4 _ image hAt.himageEq hAt.hmatches
  have hplat28 : StepPlatform s28 (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8 mseccfgBits :=
    mkStepPlatform s28 mseccfgBits (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8
      hAt.hplat hAt.hcur hAt.hmseccfg (StableAgree.refl s28)
      ((afterIncGet s28 PC (by decide)).trans hAt.hPC) (by decide) hbytes28
  have hcnt28 : StepCounters s28 retired28 inhibit cfg :=
    ⟨hAt.hhart, hAt.hinhibit, hAt.hcfg, hAt.hnotInhibited, hAt.hmachineEnabled, hret28⟩
  have h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28)
      (BitVec.ofNat 64 0x10ce4)).regs.get? x12 = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (coreGetGP s28 (BitVec.ofNat 64 0x10ce4) x12 (by decide) (by decide)).trans hAt.ha2
  have hpcread : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28)
      (BitVec.ofNat 64 0x10ce4)).regs.get? PC = some (BitVec.ofNat 64 0x10ce4) :=
    (coreGetGP s28 (BitVec.ofNat 64 0x10ce4) PC (by decide) (by decide)).trans hAt.hPC
  obtain ⟨misaBits, _, _, hmisaA, _⟩ := hplat28.1
  have hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28)
      (BitVec.ofNat 64 0x10ce4)).regs.get? misa = some misaBits :=
    (coreGetInc (tryStepControlFlowAfterIncrement s28) _ misa (by decide)).trans hmisaA
  have hsum : BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)
      = BitVec.ofNat 64 0x10c74 := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have halign : Sail.BitVec.access (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) 0 = 0#1 := by rw [hsum]; decide
  have hbit1 : Sail.BitVec.access (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) 1 = 0#1 := by rw [hsum]; decide
  have hbnez := step_bnez_taken (start + k * 29 + 28) s28 (BitVec.ofNat 64 0x10ce4)
    (BitVec.ofNat 64 (136 - 8 * (k + 1))) retired28 mseccfgBits inhibit cfg hplat28 hcnt28 h12
    (a2_ne_zero (k + 1) (by omega)) hpcread misaBits hmisa halign hbit1
  have hSj : StableAgree s28 (tryStepControlFlowAfterRetired (controlFlowJumpState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13))) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28) :=
    stableAgree_jump s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28
  have hmemj : (tryStepControlFlowAfterRetired (controlFlowJumpState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13))) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28).mem = s28.mem :=
    (retiredMem _ _ _).trans (jumpMem s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)))
  refine ⟨(tryStepControlFlowAfterRetired (controlFlowJumpState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13))) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28), by simpa using Trace.append htr (Trace.one _ _ _ hbnez), ?_⟩
  refine ⟨?_, (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 x10 (by decide) (by decide) (by decide) (by decide)).trans hAt.ha0,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 x11 (by decide) (by decide) (by decide) (by decide)).trans hAt.ha1,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 x12 (by decide) (by decide) (by decide) (by decide)).trans hAt.ha2,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 x1 (by decide) (by decide) (by decide) (by decide)).trans hAt.hra,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 cur_privilege (by decide) (by decide) (by decide) (by decide)).trans hAt.hcur,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 mstatus (by decide) (by decide) (by decide) (by decide)).trans hAt.hmstatus,
    hAt.hmprv, (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 mseccfg (by decide) (by decide) (by decide) (by decide)).trans hAt.hmseccfg,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 hart_state (by decide) (by decide) (by decide) (by decide)).trans hAt.hhart,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 mcountinhibit (by decide) (by decide) (by decide) (by decide)).trans hAt.hinhibit,
    hAt.hnotInhibited, (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 minstretcfg (by decide) (by decide) (by decide) (by decide)).trans hAt.hcfg,
    hAt.hmachineEnabled, ⟨_, retiredMinstret _ _ _⟩, hAt.himageEq, ?_, ?_, ?_, ?_,
    (by omega), hAt.hstateFits, hAt.hinputFits, hAt.hstateImg, hAt.hdisj,
    AbstractPlatform.mono hSj hAt.hplat, AbstractDataAccess.mono hSj hAt.hdata,
    AbstractElp.mono hSj hAt.hElp, hAt.hstable.trans hSj, ?_⟩
  · rw [retiredGetPC _ _ _, hsum]
  · rw [hmemj]; exact hAt.hmatches
  · intro m i hm hm2 hi; rw [hmemj]; exact hAt.hunproc m i hm hm2 hi
  · intro m i hm hi; rw [hmemj]; exact hAt.hproc m i hm hi
  · intro j hj; rw [hmemj]; exact hAt.hinput j hj
  · -- hframe (the taken back-edge writes no memory)
    exact memFramed_rate_intro (fun addr haddr => by
      rw [hmemj]; exact memFramed_rate_apply hAt.hframe addr haddr)

/-! ## Deliverable 5a: the whole 16-iteration taken loop `xorblock_loop` -/

/-- The 16 taken back-edge iterations from `XorBlockInv 0` to `XorBlockInv 16`. -/
theorem xorblock_loop (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (sref : State) (start : Nat) (s0 : State)
    (hInv0 : XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref 0 s0) :
    ∃ sN, Trace start (16 * 29) s0 sN ∧
      XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
        origLane inByte sref 16 sN :=
  Trace.invariantIterate (L := 29) (start := start)
    (Inv := fun k s => XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref k s) 16
    (fun k s hk hInv => xorblock_adv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref start k s hk hInv)
    hInv0

/-! ## Deliverable 5b: the final iteration and return `xorblock_exit` -/

set_option maxHeartbeats 2000000 in
/-- The 17th (last) iteration and return: run the body once more from `XorBlockInv 16` (`bnez` now
NOT taken, since `a2` reaches `0`), then `ret`.  The framed conclusion exposes the exact memory
delta: the 17 rate lanes are XORed, the 8 capacity lanes and the input block are preserved, the code
image (`matchesMemory`) is preserved, `PC = ra`, and — the general frame — every register outside `W`
and every byte outside the rate window still agrees with the reference state `sref`. -/
theorem xorblock_exit (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (sref : State) (start : Nat) (s : State)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hInv : XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref 16 s) :
    ∃ s'', Trace (start + 16 * 29) 30 s s'' ∧
      s''.regs.get? PC = some (Sail.BitVec.update retAddr 0 0#1) ∧
      s''.regs.get? x10 = some (state0 + BitVec.ofNat 64 136) ∧
      s''.regs.get? x11 = some (input0 + BitVec.ofNat 64 136) ∧
      s''.regs.get? x1 = some retAddr ∧
      (∀ m i : Nat, m < 17 → i < 8 → s''.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat
        = some ((origLane m ^^^ inputLane inByte m).extractLsb' (8 * i) 8)) ∧
      (∀ m i : Nat, 17 ≤ m → m < 25 → i < 8 → s''.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat
        = some ((origLane m).extractLsb' (8 * i) 8)) ∧
      (∀ j : Nat, j < 136 → s''.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (inByte j)) ∧
      image.matchesMemory s''.mem ∧
      StableAgree sref s'' ∧
      MemFramed state0 (BitVec.ofNat 64 136) sref s'' := by
  obtain ⟨s28, htr, hAt⟩ := xorblock_body_core state0 input0 retAddr image mseccfgBits mstatusBits
    inhibit cfg origLane inByte sref start 16 s (by omega) hInv
  obtain ⟨retired28, hret28⟩ := hAt.hminstret
  -- bnez NOT taken (a2 = 0)
  have hbytes28 : FetchBytesAt (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4)
      0xe3#8 0x18#8 0x06#8 0xf8#8 := fetchBytesAt_10ce4 _ image hAt.himageEq hAt.hmatches
  have hplat28 : StepPlatform s28 (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8 mseccfgBits :=
    mkStepPlatform s28 mseccfgBits (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8
      hAt.hplat hAt.hcur hAt.hmseccfg (StableAgree.refl s28)
      ((afterIncGet s28 PC (by decide)).trans hAt.hPC) (by decide) hbytes28
  have hcnt28 : StepCounters s28 retired28 inhibit cfg :=
    ⟨hAt.hhart, hAt.hinhibit, hAt.hcfg, hAt.hnotInhibited, hAt.hmachineEnabled, hret28⟩
  have h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28)
      (BitVec.ofNat 64 0x10ce4)).regs.get? x12 = some (BitVec.ofNat 64 (136 - 8 * 17)) :=
    (coreGetGP s28 (BitVec.ofNat 64 0x10ce4) x12 (by decide) (by decide)).trans hAt.ha2
  have hbnez := step_bnez_not_taken (start + 16 * 29 + 28) s28 (BitVec.ofNat 64 (136 - 8 * 17))
    retired28 mseccfgBits inhibit cfg hplat28 hcnt28 h12 a2_eq_zero
  have hSt1 : StableAgree s28 _ := stableAgree_notTaken s28 (BitVec.ofNat 64 0x10ce4) retired28
  have hmem1 : _ = s28.mem := notTakenMem s28 (BitVec.ofNat 64 0x10ce4) retired28
  have hPC1 := afterIncRetiredPC
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce4) 4) retired28
  have hmin1 := retiredMinstret
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce4) 4) retired28
  have hx10_1 : _ = some (state0 + BitVec.ofNat 64 (8 * 17)) :=
    (notTakenGet s28 (BitVec.ofNat 64 0x10ce4) retired28 x10 (by decide) (by decide) (by decide)
      (by decide)).trans hAt.ha0
  have hx11_1 : _ = some (input0 + BitVec.ofNat 64 (8 * 17)) :=
    (notTakenGet s28 (BitVec.ofNat 64 0x10ce4) retired28 x11 (by decide) (by decide) (by decide)
      (by decide)).trans hAt.ha1
  have hx1_1 : _ = some retAddr :=
    (notTakenGet s28 (BitVec.ofNat 64 0x10ce4) retired28 x1 (by decide) (by decide) (by decide)
      (by decide)).trans hAt.hra
  generalize hgen1 : tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce4) 4) retired28 = s29
    at hbnez hSt1 hmem1 hPC1 hmin1 hx10_1 hx11_1 hx1_1
  -- ret at 0x10ce8
  have hsum : Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce4) 4 = BitVec.ofNat 64 0x10ce8 := by decide
  have hbytes2 : FetchBytesAt (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8)
      0x67#8 0x80#8 0x00#8 0x00#8 :=
    fetchBytesAt_10ce8 _ image hAt.himageEq (hmem1.symm ▸ hAt.hmatches)
  have hplat2 : StepPlatform s29 (BitVec.ofNat 64 0x10ce8) 0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits :=
    mkStepPlatform s29 mseccfgBits (BitVec.ofNat 64 0x10ce8) 0x67#8 0x80#8 0x00#8 0x00#8
      hAt.hplat hAt.hcur hAt.hmseccfg hSt1 (hsum ▸ hPC1) (by decide) hbytes2
  have hcnt2 : StepCounters s29 (Sail.BitVec.addInt retired28 1) inhibit cfg :=
    ⟨(hSt1 hart_state (by decide)).trans hAt.hhart, (hSt1 mcountinhibit (by decide)).trans hAt.hinhibit,
      (hSt1 minstretcfg (by decide)).trans hAt.hcfg, hAt.hnotInhibited, hAt.hmachineEnabled, hmin1⟩
  have hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8))
      retAddr :=
    rX_bits_x1_run _ retAddr ((coreGetStable s29 _ x1 (by decide) hSt1).trans hAt.hra)
  obtain ⟨misaBits, _, _, hmisaA, _⟩ := hplat2.1
  have hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s29)
      (BitVec.ofNat 64 0x10ce8)).regs.get? misa = some misaBits :=
    (coreGetInc (tryStepControlFlowAfterIncrement s29) _ misa (by decide)).trans hmisaA
  have hElp1 : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8)) () :=
    hAt.hElp _ (.Regidx 1#5) rfl (coreStableAgree s29 (BitVec.ofNat 64 0x10ce8) hSt1)
  have hret := step_ret (start + 16 * 29 + 29) s29 retAddr (Sail.BitVec.addInt retired28 1)
    mseccfgBits misaBits inhibit cfg hplat2 hcnt2 hrs1 hretAlign hElp1 hmisa
  have hSt2 : StableAgree s28 _ :=
    hSt1.trans (stableAgree_jump s29 (BitVec.ofNat 64 0x10ce8)
      (Sail.BitVec.update retAddr 0 0#1) (Sail.BitVec.addInt retired28 1))
  have hmem2 : _ = s28.mem :=
    (retiredMem (controlFlowJumpState (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8)
      (Sail.BitVec.update retAddr 0 0#1)) (Sail.BitVec.update retAddr 0 0#1)
      (Sail.BitVec.addInt retired28 1)).trans
      ((jumpMem s29 (BitVec.ofNat 64 0x10ce8) (Sail.BitVec.update retAddr 0 0#1)).trans hmem1)
  refine ⟨_, ?_, retiredGetPC _ _ _,
    (jumpRetiredGet s29 (BitVec.ofNat 64 0x10ce8) (Sail.BitVec.update retAddr 0 0#1)
      (Sail.BitVec.addInt retired28 1) x10 (by decide) (by decide) (by decide) (by decide)).trans
      hx10_1,
    (jumpRetiredGet s29 (BitVec.ofNat 64 0x10ce8) (Sail.BitVec.update retAddr 0 0#1)
      (Sail.BitVec.addInt retired28 1) x11 (by decide) (by decide) (by decide) (by decide)).trans
      hx11_1,
    (jumpRetiredGet s29 (BitVec.ofNat 64 0x10ce8) (Sail.BitVec.update retAddr 0 0#1)
      (Sail.BitVec.addInt retired28 1) x1 (by decide) (by decide) (by decide) (by decide)).trans
      hx1_1, ?_, ?_, ?_, ?_, hAt.hstable.trans hSt2, ?_⟩
  · exact by simpa using Trace.append htr (Trace.step _ _ _ _ _ hbnez (Trace.one _ _ _ hret))
  · intro m i hm hi; rw [hmem2]; exact hAt.hproc m i (by omega) hi
  · intro m i hm hm2 hi; rw [hmem2]; exact hAt.hunproc m i hm hm2 hi
  · intro j hj; rw [hmem2]; exact hAt.hinput j hj
  · rw [hmem2]; exact hAt.hmatches
  · -- the general memory frame (the two exit steps write no memory)
    exact memFramed_rate_intro (fun addr haddr => by
      rw [hmem2]; exact memFramed_rate_apply hAt.hframe addr haddr)

/-! ## Deliverable 5c: the capstone `xor_block_contract`

DESIGN NOTE (fetch-fact transparency).  This contract depends on the parser-derived fetch facts
(`XorBlockArtifactFetch`) ONLY through their `FetchBytesAt` conclusions — routed through the step
lemmas and `mkStepPlatform` — never through their `native_decide` internals.  That part of the trust
story stands: the fetch facts are closed statements about the pinned Nix-built ELF, and nothing about
the execution semantics, framing or spec correspondence below is decided natively.

CORRECTION (2026-07-16).  An earlier version of this note went on to claim that swapping the fetch
facts for kernel-checked versions would drop `Lean.ofReduceBool` / `Lean.trustCompiler` from this
theorem's axiom footprint.  That claim is FALSE and has been removed.  `bv_decide` discharges its
goals by checking an LRAT certificate whose evaluation goes through `Lean.reduceBool`, so *every*
`bv_decide` call that actually reaches the SAT backend contributes those two axioms on its own,
independently of any artifact fact.  `assemble_leWord` above is a pure `BitVec` identity with no
artifact dependency at all, and already carries them; so do the `Spec` bridges in deliverable 6.
(`bv_decide` calls closed by `bv_normalize` preprocessing alone — `slli_amount`, `li_val`, `sext8` —
do not.)  The honest statement is: this theorem's `Lean.ofReduceBool` / `Lean.trustCompiler`
footprint has two independent sources, the artifact fetch facts and the `bv_decide` LRAT checker, and
removing the former alone would not drop them. -/

/-- The entry `li a2, 136` value equals `136`. -/
theorem li_val : zero_reg + sign_extend (m := 64) 136#12 = BitVec.ofNat 64 136 := by
  have hz : (zero_reg : BitVec 64) = 0#64 := rfl
  rw [hz]
  simp only [sign_extend, Sail.BitVec.signExtend]
  bv_decide

set_option maxHeartbeats 2000000 in
/-- CAPSTONE.  `xor_block(state, input, 136)` at `0x10c6c`, run through the authoritative generated
`try_step` from a configured machine: a single `2 + 16*29 + 30 = 496`-step trace to the caller
(`PC = ra`), after which the 17 rate state lanes at `state0 + 8m` (`m < 17`) each hold
`origLane m ^^^ inputLane inByte m`.

The compositional side of the contract is exported as the *general* frame, not as a list of selected
observations:

* `MemFramed state0 136 s s''` — the exact memory delta.  `s''` agrees with the entry state `s` at
  every address the 136-byte rate window `[state0, state0+136)` does not cover, for an **arbitrary**
  address; the immediately following conjunct is the no-wraparound reading of that
  (`addr < state0` or `state0 + 136 ≤ addr` implies `s''.mem addr = s.mem addr`).
* `StableAgree s s''` — the register frame.  Every register outside `xor_block`'s written set
  `W = {PC, nextPC, minstret, minstret_increment, x5, x10..x17}` still holds its entry value.  This
  is honest about `W`: `a0`/`a1` are advanced by 136 and `a2`/`t0`/`a3..a7` are clobbered, so no
  preservation is claimed for them.

The capacity-lane (`17 ≤ m < 25`), input-block and code-image conclusions are kept, but are now
*derived from* the memory frame (all three regions lie outside the rate window) rather than tracked
as independent ad-hoc conclusions. -/
theorem xor_block_contract (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (start : Nat) (s : State)
    (hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10c6c))
    (ha0 : s.regs.get? x10 = some state0) (ha1 : s.regs.get? x11 = some input0)
    (hra : s.regs.get? x1 = some retAddr)
    (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmstatus : s.regs.get? mstatus = some mstatusBits) (hmprv : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hhart : s.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hinhibit : s.regs.get? mcountinhibit = some inhibit)
    (hnotInhibited : _get_Counterin_IR inhibit = 0#1)
    (hcfg : s.regs.get? minstretcfg = some cfg) (hmachineEnabled : _get_CountSmcntrpmf_MINH cfg = 0#1)
    (hminstret : ∃ v, s.regs.get? minstret = some v)
    (himageEq : Artifact.programImage = .ok image) (hmatches : image.matchesMemory s.mem)
    (hstate : ∀ m i : Nat, m < 25 → i < 8 →
      s.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat = some ((origLane m).extractLsb' (8 * i) 8))
    (hinput : ∀ j : Nat, j < 136 → s.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (inByte j))
    (hstateFits : state0.toNat + 200 ≤ 2 ^ 64) (hinputFits : input0.toNat + 136 ≤ 2 ^ 64)
    (hstateImg : ∀ j : Nat, j < 200 → image.readByte? (state0 + BitVec.ofNat 64 j).toNat = none)
    (hdisj : ∀ j j' : Nat, j < 200 → j' < 136 →
      (state0 + BitVec.ofNat 64 j).toNat ≠ (input0 + BitVec.ofNat 64 j').toNat)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hplat : AbstractPlatform s) (hdata : AbstractDataAccess state0 input0 s) (hElp : AbstractElp s) :
    ∃ s'', Trace start (2 + 16 * 29 + 30) s s'' ∧
      s''.regs.get? PC = some (Sail.BitVec.update retAddr 0 0#1) ∧
      s''.regs.get? x10 = some (state0 + BitVec.ofNat 64 136) ∧
      s''.regs.get? x11 = some (input0 + BitVec.ofNat 64 136) ∧
      s''.regs.get? x1 = some retAddr ∧
      (∀ m i : Nat, m < 17 → i < 8 → s''.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat
        = some ((origLane m ^^^ inputLane inByte m).extractLsb' (8 * i) 8)) ∧
      (∀ m i : Nat, 17 ≤ m → m < 25 → i < 8 → s''.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat
        = some ((origLane m).extractLsb' (8 * i) 8)) ∧
      (∀ j : Nat, j < 136 → s''.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (inByte j)) ∧
      image.matchesMemory s''.mem ∧
      MemFramed state0 (BitVec.ofNat 64 136) s s'' ∧
      (∀ addr : Nat, addr < state0.toNat ∨ state0.toNat + 136 ≤ addr →
        s''.mem.get? addr = s.mem.get? addr) ∧
      StableAgree s s'' := by
  obtain ⟨retired0, hret0⟩ := hminstret
  -- Entry step 0: li a2, 136 at 0x10c6c.
  have hbytesE : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c)
      0x13#8 0x06#8 0x80#8 0x08#8 := fetchBytesAt_10c6c _ image himageEq hmatches
  have hplatE : StepPlatform s (BitVec.ofNat 64 0x10c6c) 0x13#8 0x06#8 0x80#8 0x08#8 mseccfgBits :=
    mkStepPlatform s mseccfgBits (BitVec.ofNat 64 0x10c6c) 0x13#8 0x06#8 0x80#8 0x08#8
      hplat hcur hmseccfg (StableAgree.refl s) ((afterIncGet s PC (by decide)).trans hPC)
      (by decide) hbytesE
  have hcntE : StepCounters s retired0 inhibit cfg :=
    ⟨hhart, hinhibit, hcfg, hnotInhibited, hmachineEnabled, hret0⟩
  have hli := step_li_a2 start s retired0 mseccfgBits inhibit cfg hplatE hcntE
  have hStE : StableAgree s _ :=
    stableAgree_gp s (BitVec.ofNat 64 0x10c6c) retired0 x12 (zero_reg + sign_extend (m := 64) 136#12)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hmemE : _ = s.mem :=
    (retiredMem { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4) retired0).trans
      (fallThroughMem s (BitVec.ofNat 64 0x10c6c) x12 (zero_reg + sign_extend (m := 64) 136#12))
  have hPCE := afterIncRetiredPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
        (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4) retired0
  have hminE := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
        (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4) retired0
  have hx12E : _ = some (BitVec.ofNat 64 136) :=
    (fallThroughRetiredRd s (BitVec.ofNat 64 0x10c6c) retired0 x12
      (zero_reg + sign_extend (m := 64) 136#12) (by decide) (by decide)).trans (congrArg some li_val)
  have hx10E : _ = some state0 :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c6c) retired0 x12
      (zero_reg + sign_extend (m := 64) 136#12) x10 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ha0
  have hx11E : _ = some input0 :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c6c) retired0 x12
      (zero_reg + sign_extend (m := 64) 136#12) x11 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ha1
  have hx1E : _ = some retAddr :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c6c) retired0 x12
      (zero_reg + sign_extend (m := 64) 136#12) x1 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hra
  generalize hgenE : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
          (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4) retired0 = s1
    at hli hStE hmemE hPCE hminE hx12E hx10E hx11E hx1E
  -- Entry step 1: beqz a2 at 0x10c70 (NOT taken, a2 = 136).
  have hsumE : Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4 = BitVec.ofNat 64 0x10c70 := by decide
  have hbytes1 : FetchBytesAt (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c70)
      0x63#8 0x0c#8 0x06#8 0x06#8 := fetchBytesAt_10c70 _ image himageEq (hmemE.symm ▸ hmatches)
  have hplat1 : StepPlatform s1 (BitVec.ofNat 64 0x10c70) 0x63#8 0x0c#8 0x06#8 0x06#8 mseccfgBits :=
    mkStepPlatform s1 mseccfgBits (BitVec.ofNat 64 0x10c70) 0x63#8 0x0c#8 0x06#8 0x06#8
      hplat hcur hmseccfg hStE (hsumE ▸ hPCE) (by decide) hbytes1
  have hcnt1 : StepCounters s1 (Sail.BitVec.addInt retired0 1) inhibit cfg :=
    ⟨(hStE hart_state (by decide)).trans hhart, (hStE mcountinhibit (by decide)).trans hinhibit,
      (hStE minstretcfg (by decide)).trans hcfg, hnotInhibited, hmachineEnabled, hminE⟩
  have h12_1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10c70)).regs.get? x12 = some (BitVec.ofNat 64 136) :=
    (coreGetGP s1 (BitVec.ofNat 64 0x10c70) x12 (by decide) (by decide)).trans hx12E
  have hbeqz := step_beqz_not_taken (start + 1) s1 (BitVec.ofNat 64 136) (Sail.BitVec.addInt retired0 1)
    mseccfgBits inhibit cfg hplat1 hcnt1 h12_1 (a2_ne_zero 0 (by omega))
  have hSt1 : StableAgree s _ :=
    hStE.trans (stableAgree_notTaken s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1))
  have hmem1 : _ = s.mem :=
    (notTakenMem s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1)).trans hmemE
  have hPC1 := afterIncRetiredPC
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c70))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4) (Sail.BitVec.addInt retired0 1)
  have hmin1 := retiredMinstret
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c70))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4) (Sail.BitVec.addInt retired0 1)
  have hx12_1 : _ = some (BitVec.ofNat 64 (136 - 8 * 0)) :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1) x12 (by decide)
      (by decide) (by decide) (by decide)).trans hx12E
  have hx10_1 : _ = some state0 :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1) x10 (by decide)
      (by decide) (by decide) (by decide)).trans hx10E
  have hx11_1 : _ = some input0 :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1) x11 (by decide)
      (by decide) (by decide) (by decide)).trans hx11E
  have hx1_1 : _ = some retAddr :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1) x1 (by decide)
      (by decide) (by decide) (by decide)).trans hx1E
  have hPCval1 : (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c70))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4) (Sail.BitVec.addInt retired0 1)).regs.get? PC
      = some (BitVec.ofNat 64 0x10c74) := by
    rw [retiredGetPC, show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4
      = BitVec.ofNat 64 0x10c74 from by decide]
  generalize hgen1 : tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c70))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4) (Sail.BitVec.addInt retired0 1) = s2
    at hbeqz hSt1 hmem1 hPC1 hmin1 hx12_1 hx10_1 hx11_1 hx1_1 hPCval1
  -- Establish `XorBlockInv 0` at `s2` (PC = 0x10c74).
  -- The two entry steps write no memory, so the frame relative to `s` starts trivially.
  have hInv0 : XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte s 0 s2 := by
    refine ⟨?_, by simpa using hx10_1, by simpa using hx11_1, hx12_1, hx1_1,
      (hSt1 cur_privilege (by decide)).trans hcur,
      (hSt1 mstatus (by decide)).trans hmstatus, hmprv, (hSt1 mseccfg (by decide)).trans hmseccfg,
      (hSt1 hart_state (by decide)).trans hhart, (hSt1 mcountinhibit (by decide)).trans hinhibit,
      hnotInhibited, (hSt1 minstretcfg (by decide)).trans hcfg, hmachineEnabled, ⟨_, hmin1⟩,
      himageEq, ?_, ?_, ?_, ?_, (by omega), hstateFits, hinputFits, hstateImg, hdisj,
      AbstractPlatform.mono hSt1 hplat, AbstractDataAccess.mono hSt1 hdata,
      AbstractElp.mono hSt1 hElp, hSt1, ?_⟩
    · exact hPCval1
    · rw [hmem1]; exact hmatches
    · intro m i _ hm2 hi; rw [hmem1]; exact hstate m i hm2 hi
    · intro m i hm _; exact absurd hm (Nat.not_lt_zero m)
    · intro j hj; rw [hmem1]; exact hinput j hj
    · exact memFramed_rate_intro (fun addr _ => by rw [hmem1])
  -- Loop (16 taken iterations) then exit (final iteration + ret).
  obtain ⟨sN, htrLoop, hInvN⟩ := xorblock_loop state0 input0 retAddr image mseccfgBits mstatusBits
    inhibit cfg origLane inByte s (start + 2) s2 hInv0
  obtain ⟨s'', htrExit, hPCret, hx10N, hx11N, hx1N, hrate, _hcap, _hinp, _hcode, hstableN,
      hframeN⟩ :=
    xorblock_exit state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg origLane inByte
      s (start + 2) sN hretAlign hInvN
  -- The no-wraparound reading of the general frame.
  have hfitsRate : state0.toNat + (BitVec.ofNat 64 136).toNat ≤ 2 ^ 64 := by
    rw [rateWidth_toNat]; omega
  have houtside : ∀ addr : Nat, addr < state0.toNat ∨ state0.toNat + 136 ≤ addr →
      s''.mem.get? addr = s.mem.get? addr := fun addr hout =>
    MemFramed.mem_unchanged_outside hframeN hfitsRate addr (by rw [rateWidth_toNat]; exact hout)
  -- Capacity lanes: `8m + i ∈ [136, 200)` lies above the rate window.
  have hcap : ∀ m i : Nat, 17 ≤ m → m < 25 → i < 8 →
      s''.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat
        = some ((origLane m).extractLsb' (8 * i) 8) := by
    intro m i hm hm2 hi
    rw [houtside _ (Or.inr (by rw [dstAddr_toNat state0 (8 * m + i) (by omega)]; omega))]
    exact hstate m i hm2 hi
  -- Input block: disjoint from the state region by `hdisj`, hence outside the rate window.
  have hinp : ∀ j : Nat, j < 136 →
      s''.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (inByte j) := by
    intro j hj
    refine (MemFramed.source_preserved (src := input0) hframeN ?_ j ?_).trans (hinput j hj)
    · intro a b ha hb
      rw [rateWidth_toNat] at ha hb
      exact hdisj a b (by omega) hb
    · rw [rateWidth_toNat]; exact hj
  -- Code image: the image backs no byte of the state region, so the frame carries it.
  have hcode : image.matchesMemory s''.mem :=
    matchesMemory_of_rate_frame hframeN hstateImg hmatches
  refine ⟨s'', ?_, hPCret, hx10N, hx11N, hx1N, hrate, hcap, hinp, hcode, hframeN, houtside,
    hstableN⟩
  have htrEntry : Trace start 2 s s2 :=
    Trace.step _ _ _ _ _ hli (Trace.one _ _ _ hbeqz)
  have hcomb := Trace.append (Trace.append htrEntry htrLoop) htrExit
  simpa using hcomb

/-! ## Deliverable 6: correspondence with the executable Keccak-256 specification

`Spec.Keccak.xorBytesIntoState st input 136` (`Spec/Keccak/Keccak256.lean`) is the specification's
rate-block absorb: the 25-lane `Array UInt64` whose lane `i` is `st[i]! ^^^ Spec.Keccak.inputLane
input i` for `i < 136 / 8 = 17`, and `st[i]!` otherwise.  The machine, by contrast, works on a flat
byte memory, so the correspondence needs an explicit memory ↔ `Array UInt64` relation.  We do not
invent one: `StateImage` / `InputImage` below say the machine's memory at `state0` / `input0` *is*
the specification's own serialization (`Spec.Keccak.stateByte`, `ByteArray.data`).  They are stated
as definitions and appear as an explicit hypothesis (on the entry state) and an explicit conclusion
(on the exit state) of `xor_block_matches_spec` — the honest framing, since nothing in the machine
semantics privileges any particular lane encoding.

The two load-bearing bridges are pure `bv_decide` identities. Their LRAT certificates are checked
through native evaluation under the proof-of-concept trust policy recorded in the repository README:

* `specInputLane_toBitVec` — the machine's little-endian `leWord` of the 8 input bytes at
  `input0 + 8k` (produced by the body's 8 `lbu` + 6 `slli` + 6 `or`, cf. `assemble_leWord`) equals
  `Spec.Keccak.inputLane input k`.  This is the `UInt64 ↔ BitVec 64` bridge over the spec's
  `|||` / `<<<` / `toUInt64` fold.
* `specStateByte_toBitVec` — the machine's per-lane byte extraction `lane.extractLsb' (8i) 8` equals
  the spec's `stateByte` at flat index `8m + i`. -/

/-- BRIDGE (input lane).  The spec's `inputLane` fold over `List.range 8` — `acc ||| b <<< 8j` on
`UInt64` — is the machine's little-endian `leWord` of the same 8 bytes. -/
theorem specInputLane_toBitVec (input : ByteArray) (inByte : Nat → BitVec 8) (k : Nat)
    (hsize : input.size = 136) (hk : k < 17)
    (hb : ∀ j : Nat, j < 8 → (input.data[8 * k + j]!).toBitVec = inByte (8 * k + j)) :
    (Spec.Keccak.inputLane input k).toBitVec = inputLane inByte k := by
  unfold Spec.Keccak.inputLane inputLane
  simp only [List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil, List.foldl_append,
    hsize,
    if_pos (show 8 * k + 0 < 136 by omega), if_pos (show 8 * k + 1 < 136 by omega),
    if_pos (show 8 * k + 2 < 136 by omega), if_pos (show 8 * k + 3 < 136 by omega),
    if_pos (show 8 * k + 4 < 136 by omega), if_pos (show 8 * k + 5 < 136 by omega),
    if_pos (show 8 * k + 6 < 136 by omega), if_pos (show 8 * k + 7 < 136 by omega)]
  rw [← hb 0 (by omega), ← hb 1 (by omega), ← hb 2 (by omega), ← hb 3 (by omega),
    ← hb 4 (by omega), ← hb 5 (by omega), ← hb 6 (by omega), ← hb 7 (by omega)]
  simp only [leWord, List.length_cons, List.length_nil,
    show Nat.toUInt64 0 = (0 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 1) = (8 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 2) = (16 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 3) = (24 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 4) = (32 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 5) = (40 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 6) = (48 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 7) = (56 : UInt64) from rfl]
  bv_decide

/-- The machine memory at `[state0, state0+200)` *is* the spec's 200-byte little-endian serialization
of the 25-lane state `st` (`Spec.Keccak.stateByte`). -/
def StateImage (state0 : BitVec 64) (st : Array UInt64) (s : State) : Prop :=
  ∀ i : Nat, i < 200 →
    s.mem.get? (state0 + BitVec.ofNat 64 i).toNat = some (Spec.Keccak.stateByte st i).toBitVec

/-- The machine memory at `[input0, input0+136)` *is* the spec's 136-byte rate block. -/
def InputImage (input0 : BitVec 64) (input : ByteArray) (s : State) : Prop :=
  ∀ j : Nat, j < 136 →
    s.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (input.data[j]!).toBitVec

set_option maxHeartbeats 1000000 in
/-- SPEC CORRESPONDENCE.  Run from a configured machine whose memory holds the serialized spec state
`st` at `state0` and the spec's 136-byte rate block `input` at `input0`, the operational `xor_block`
(the same 496-step generated-`try_step` trace as `xor_block_contract`) returns to the caller with
memory holding *exactly the serialization of* `Spec.Keccak.xorBytesIntoState st input 136` — all 25
lanes, so this pins the XORed 17 rate lanes and the 8 untouched capacity lanes simultaneously.  The
input block, the code image, and the register/memory frames are carried over from the capstone. -/
theorem xor_block_matches_spec (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (st : Array UInt64) (input : ByteArray) (start : Nat) (s : State)
    (hsize : input.size = 136)
    (hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10c6c))
    (ha0 : s.regs.get? x10 = some state0) (ha1 : s.regs.get? x11 = some input0)
    (hra : s.regs.get? x1 = some retAddr)
    (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmstatus : s.regs.get? mstatus = some mstatusBits) (hmprv : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hhart : s.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hinhibit : s.regs.get? mcountinhibit = some inhibit)
    (hnotInhibited : _get_Counterin_IR inhibit = 0#1)
    (hcfg : s.regs.get? minstretcfg = some cfg) (hmachineEnabled : _get_CountSmcntrpmf_MINH cfg = 0#1)
    (hminstret : ∃ v, s.regs.get? minstret = some v)
    (himageEq : Artifact.programImage = .ok image) (hmatches : image.matchesMemory s.mem)
    (hstateImage : StateImage state0 st s) (hinputImage : InputImage input0 input s)
    (hstateFits : state0.toNat + 200 ≤ 2 ^ 64) (hinputFits : input0.toNat + 136 ≤ 2 ^ 64)
    (hstateImg : ∀ j : Nat, j < 200 → image.readByte? (state0 + BitVec.ofNat 64 j).toNat = none)
    (hdisj : ∀ j j' : Nat, j < 200 → j' < 136 →
      (state0 + BitVec.ofNat 64 j).toNat ≠ (input0 + BitVec.ofNat 64 j').toNat)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hplat : AbstractPlatform s) (hdata : AbstractDataAccess state0 input0 s) (hElp : AbstractElp s) :
    ∃ s'', Trace start (2 + 16 * 29 + 30) s s'' ∧
      s''.regs.get? PC = some (Sail.BitVec.update retAddr 0 0#1) ∧
      StateImage state0 (Spec.Keccak.xorBytesIntoState st input 136) s'' ∧
      InputImage input0 input s'' ∧
      image.matchesMemory s''.mem ∧
      MemFramed state0 (BitVec.ofNat 64 136) s s'' ∧
      StableAgree s s'' := by
  obtain ⟨s'', htr, hPCret, _hx10, _hx11, _hx1, hrate, hcap, hinp, hcode, hframe, _houtside,
      hstable⟩ :=
    xor_block_contract state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      (fun m => (st[m]!).toBitVec) (fun j => (input.data[j]!).toBitVec) start s
      hPC ha0 ha1 hra hcur hmstatus hmprv hmseccfg hhart hinhibit hnotInhibited hcfg hmachineEnabled
      hminstret himageEq hmatches
      (fun m i _hm hi =>
        (hstateImage (8 * m + i) (by omega)).trans (congrArg some (specStateByte_toBitVec st m i hi)))
      hinputImage hstateFits hinputFits hstateImg hdisj hretAlign hplat hdata hElp
  refine ⟨s'', htr, hPCret, ?_, hinp, hcode, hframe, hstable⟩
  intro i hi
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 8 ∧ i = 8 * m + r := ⟨i / 8, i % 8, by omega, by omega⟩
  rw [specStateByte_toBitVec _ m r hr, xorBytesIntoState_lane st input m (by omega)]
  rcases Nat.lt_or_ge m 17 with hm17 | hm17
  · -- rate lane: the machine's XOR is the spec's `st[m]! ^^^ inputLane input m`
    have hlane : (st[m]! ^^^ Spec.Keccak.inputLane input m).toBitVec
        = (st[m]!).toBitVec ^^^ inputLane (fun j => (input.data[j]!).toBitVec) m := by
      rw [show ((st[m]! ^^^ Spec.Keccak.inputLane input m).toBitVec)
            = st[m]!.toBitVec ^^^ (Spec.Keccak.inputLane input m).toBitVec from rfl,
        specInputLane_toBitVec input (fun j => (input.data[j]!).toBitVec) m hsize hm17
          (fun j _ => rfl)]
    rw [if_pos hm17, hrate m r hm17 hr, hlane]
  · -- capacity lane: untouched by both
    rw [if_neg (by omega)]
    exact hcap m r hm17 (by omega) hr

end BinaryFv.Keccak.XorBlock
