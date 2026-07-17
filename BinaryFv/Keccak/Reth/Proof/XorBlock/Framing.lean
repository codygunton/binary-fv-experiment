import BinaryFv.Keccak.Reth.Proof.XorBlock.ByteAssembly

/-!
# Framing specialized to the `xor_block` write set
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

theorem coreNextPc (Y : State) (pc : BitVec 64) :
    (coreControlFlowNextState Y pc).regs.get? nextPC = some (Sail.BitVec.addInt pc 4) := by
  change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
  rw [Std.ExtDHashMap.get?_insert]; simp

theorem coreGetInc (Y : State) (pc : BitVec 64) (r : Register) (hnp : r ≠ nextPC) :
    (coreControlFlowNextState Y pc).regs.get? r = Y.regs.get? r := by
  simpa [coreControlFlowNextState] using
    writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

theorem gpFrameNextPc (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (hrd : nextPC ≠ rd) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC =
      some (Sail.BitVec.addInt pc 4) := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC
      = (coreControlFlowNextState Y pc).regs.get? nextPC :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd nextPC v hrd
    _ = some (Sail.BitVec.addInt pc 4) := coreNextPc Y pc

theorem gpFrameGet (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
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

end BinaryFv.Keccak.XorBlock
