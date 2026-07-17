import BinaryFv.RiscV.Step.AbstractPremise
import BinaryFv.RiscV.Step.Context
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.Keccak.Reth.Proof.Store.StepContract
import BinaryFv.RiscV.Logic.MemFrame
import BinaryFv.Keccak.Reth.Proof.Helpers.Decode
import BinaryFv.Keccak.Reth.Proof.Helpers.Fetch
import BinaryFv.Keccak.Reth.Proof.Helpers.ArithDispatch
import BinaryFv.RiscV.Logic.LoopInduction
import BinaryFv.RiscV.Instruction.Execute.Load
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Logic.BlockStep

/-!
# `memcpy` register-write reductions
-/

namespace BinaryFv.Keccak
open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Foundational register-write facts -/

/-- Writing `a3 = x13` via `wX_bits` inserts `x13 ↦ data` and touches nothing else (the
`xreg_write_callback` is a no-op).  Same reduction as `execute_add_a3_a1_a5`, isolated to the raw
register write used by `lbu`'s destination. -/
theorem wX_bits_x13_run (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 13#5) data) s { s with regs := s.regs.insert x13 data } () := by
  have r13Nat : (Sail.BitVec.toNatInt 13#5).toNat = 13 := by decide
  unfold Runs
  simp [wX_bits, wX, PreSail.writeReg, r13Nat,
    EStateM.run, EStateM.bind, EStateM.modifyGet, EStateM.pure, EStateM.instMonad,
    MonadState.modifyGet, MonadStateOf.modifyGet, modify,
    xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
    encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
    LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg]

/-- Reading `a5 = x15` via `rX_bits`. -/
theorem rX_bits_x15_run (s : State) (v : BitVec 64) (h : s.regs.get? x15 = some v) :
    Runs (rX_bits (.Regidx 15#5)) s s v := by
  have r15 : (Sail.BitVec.toNatInt (15#5)).toNat = 15 := by decide
  unfold Runs
  simp [rX_bits, rX, r15, h, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

/-- Reading `a2 = x12` via `rX_bits`. -/
theorem rX_bits_x12_run (s : State) (v : BitVec 64) (h : s.regs.get? x12 = some v) :
    Runs (rX_bits (.Regidx 12#5)) s s v := by
  have r12 : (Sail.BitVec.toNatInt (12#5)).toNat = 12 := by decide
  unfold Runs
  simp [rX_bits, rX, r12, h, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

/-- Reading `a3 = x13` via `rX_bits` (the byte-store data source). -/
theorem rX_bits_x13_run (s : State) (v : BitVec 64) (h : s.regs.get? x13 = some v) :
    Runs (rX_bits (.Regidx 13#5)) s s v := by
  have r13 : (Sail.BitVec.toNatInt (13#5)).toNat = 13 := by decide
  unfold Runs
  simp [rX_bits, rX, r13, h, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

/-- The `bne a5, a2` branch condition (`.BNE`, `rs1 = a5 = x15`, `rs2 = a2 = x12`) runs to
`a5 != a2`. -/
theorem bTypeTaken_bne_run (s : State) (a5v a2v : BitVec 64)
    (h15 : s.regs.get? x15 = some a5v) (h12 : s.regs.get? x12 = some a2v) :
    Runs (bTypeTaken (.Regidx 12#5) (.Regidx 15#5) .BNE) s s (a5v != a2v) := by
  unfold bTypeTaken
  refine Runs.bind (rX_bits_x15_run s a5v h15) ?_
  refine Runs.bind (rX_bits_x12_run s a2v h12) ?_
  rfl

/-! ## Shared platform / counter bundles

The genuine platform preconditions (`FetchBasePlatform`, MMIO decision, interrupt exclusion,
landing-pad, decode CSRs) about the post-increment fetch state, and the retirement counter reads
about the pre-step state, are bundled once so each body-instruction step lemma consumes them
uniformly.  They are exactly the abstract configured-machine facts carried by the stage-2 store. -/

/-! ## Step 1: `bne a5, a2, 0x10d24` at the loop head `L = 0x10d1c` (taken while `i ≠ n`) -/

/-- The loop-head conditional branch, taken (`a5 = i ≠ n = a2`), lifted through the generated
`try_step`.  Fetch bytes at `0x10d1c` are `63 94 c7 00` (`00c79463 = bne a5,a2,+8`); the target is
`pc + 8 = 0x10d24`.  Post-state: `PC = nextPC = pcVal + 8`, `minstret = retired+1`. -/
theorem memcpy_step_bne_taken (stepNo : Nat) (state : State)
    (pcVal a2v retired : BitVec 64) (mseccfgBits : BitVec 64) (inhibit : BitVec 32)
    (config : BitVec 64) (i : Nat)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d1c) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d1c)).regs.get? x15 = some (BitVec.ofNat 64 i))
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d1c)).regs.get? x12 = some a2v)
    (hneq : BitVec.ofNat 64 i ≠ a2v)
    (hpcRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d1c)).regs.get? PC = some pcVal)
    (misaBits : BitVec 64)
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d1c)).regs.get? misa = some misaBits)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) (8#13)) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) (8#13)) 1 = 0#1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d1c) (pcVal + sign_extend (m := 64) (8#13)))
        (pcVal + sign_extend (m := 64) (8#13)) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8 = (0x00c79463 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (8#13, .Regidx 12#5, .Regidx 15#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bne_a5_a2_run _ privRead mseccfgBits mseccfgRead
  have hcondEq : (BitVec.ofNat 64 i != a2v) = true := by
    rw [bne_iff_ne]; exact hneq
  have hcond : Runs (bTypeTaken (.Regidx 12#5) (.Regidx 15#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d1c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d1c))
      true := by
    have := bTypeTaken_bne_run _ (BitVec.ofNat 64 i) a2v h15 h12
    rwa [hcondEq] at this
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d1c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d1c))
      pcVal :=
    readReg_run _ PC pcVal hpcRead
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d1c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d1c))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x10d1c) pcVal retired
    (8#13) (.Regidx 12#5) (.Regidx 15#5) .BNE inhibit config 0x63#8 0x94#8 0xc7#8 0x00#8
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected
    hcond hpc halign hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead

end BinaryFv.Keccak
