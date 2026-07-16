import BinaryFv.Keccak.MemcpyContract
import BinaryFv.Keccak.XorBlockDecodeFacts
import BinaryFv.Keccak.XorBlockArtifactFetch
import BinaryFv.RISCV.ShiftOrExecuteContract
import BinaryFv.RISCV.RegisterOpExecuteContract

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

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RISCV
open BinaryFv.RISCV.Sep
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
def StableAgree (base t : State) : Prop :=
  ∀ r : Register, NonW r → t.regs.get? r = base.regs.get? r

theorem StableAgree.refl (s : State) : StableAgree s s := fun _ _ => rfl

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

end BinaryFv.Keccak.XorBlock
