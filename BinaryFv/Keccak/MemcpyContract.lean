import BinaryFv.Keccak.FallThroughStepContract
import BinaryFv.Keccak.CoreStoreStepContract
import BinaryFv.Keccak.HelperFraming
import BinaryFv.Keccak.HelperDecodeFacts
import BinaryFv.Keccak.HelperArtifactFetch
import BinaryFv.Keccak.HelperArithDispatch
import BinaryFv.Keccak.LoopInduction
import BinaryFv.RiscV.LoadExecuteContract
import BinaryFv.RiscV.StoreByteExecuteContract
import BinaryFv.RiscV.BlockStep

/-!
# The `memcpy` (0x10d18) byte-copy loop, proved through the authoritative generated `try_step`

Stage 4 lifts the per-instruction `try_step` packagings (stage 3: control flow; `FallThrough` /
`GenericStep`: straight-line body) into a whole-loop contract for the leaf byte-copy helper
`memcpy` at `0x10d18`:

```
0x10d1c bne a5,a2,0x10d24   ; taken while i≠n           (loop head L)
0x10d20 ret                 ; when i==n
0x10d24 add a3,a1,a5        ; a3 = src+i
0x10d28 lbu a3,0(a3)        ; a3 = mem[src+i]
0x10d2c add a4,a0,a5        ; a4 = dst+i
0x10d30 addi a5,a5,1        ; i++
0x10d34 sb a3,0(a4)         ; mem[dst+i] = a3
0x10d38 j 0x10d1c           ; back to L
```

The genuine platform/data-access preconditions (the load/store effective-address resolution, the
`phys_access_check`, MMIO decisions, and byte ownership) are carried *abstractly* in the loop
invariant, exactly the trust boundary established by the stage-2 store (`StoreStepTriple`): they are
hypotheses about a configured machine, never discharged here, so the final axiom footprint is the
XOR/fetch baseline.
-/

namespace BinaryFv.Keccak

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

/-- The generated fetch/decode platform bundle for the body instruction at `pc`, stated about the
post-increment state `tryStepControlFlowAfterIncrement state` the generated `try_step` fetches from. -/
def StepPlatform (state : State) (pc : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (mseccfgBits : BitVec 64) : Prop :=
  FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc ∧
  FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc ∧
  FetchBytesAt (tryStepControlFlowAfterIncrement state) pc b0 b1 b2 b3 ∧
  InterruptDisabled (tryStepControlFlowAfterIncrement state) ∧
  LandingPadNotExpected (tryStepControlFlowAfterIncrement state) ∧
  (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine ∧
  (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits

/-- The retirement-counter reads about the pre-step state (`minstret` present, `mcountinhibit` /
`minstretcfg` configured so `should_inc_minstret` fires, hart active). -/
def StepCounters (state : State) (retired : BitVec 64) (inhibit : BitVec 32)
    (config : BitVec 64) : Prop :=
  state.regs.get? hart_state = some (.HART_ACTIVE ()) ∧
  state.regs.get? mcountinhibit = some inhibit ∧
  state.regs.get? minstretcfg = some config ∧
  _get_Counterin_IR inhibit = 0#1 ∧
  _get_CountSmcntrpmf_MINH config = 0#1 ∧
  state.regs.get? minstret = some retired

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

/-! ## Fall-through framing helpers

A fall-through body instruction retires with `nextPC` still at `pc + 4` and writes at most one
general-purpose register `rd` (or a memory byte, handled via `writeBytes_preserves_regs`).  These two
lemmas read the post-execute register file `(coreControlFlowNextState Y pc).regs.insert rd v` — the
`nextPC` slot at `pc + 4`, and any other stable slot back to `Y`. -/

/-- The `nextPC` slot of the post-execute state of a GP-writing fall-through instruction is `pc+4`. -/
private theorem gpFrameNextPc (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (hrd : nextPC ≠ rd) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC =
      some (Sail.BitVec.addInt pc 4) := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC
      = (coreControlFlowNextState Y pc).regs.get? nextPC :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd nextPC v hrd
    _ = some (Sail.BitVec.addInt pc 4) := by
        change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
        rw [Std.ExtDHashMap.get?_insert]; simp

/-- Any register other than `nextPC` and `rd` reads through the post-execute state of a GP-writing
fall-through instruction back to the pre-`nextPC` state `Y`. -/
private theorem gpFrameGet (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (r : Register) (hrd : r ≠ rd) (hnp : r ≠ nextPC) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? r = Y.regs.get? r := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? r
      = (coreControlFlowNextState Y pc).regs.get? r :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd r v hrd
    _ = Y.regs.get? r := by
        simpa [coreControlFlowNextState] using
          writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

/-- Bridge a register read from the pre-step state through the counter-increment and `nextPC` writes
to the execute state `coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc`. -/
theorem xGet (state : State) (pc : BitVec 64) (r : Register)
    (hnp : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? r =
      state.regs.get? r := by
  calc (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? r
      = (tryStepControlFlowAfterIncrement state).regs.get? r := by
        simpa [coreControlFlowNextState] using
          writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC r
            (Sail.BitVec.addInt pc 4) hnp
    _ = state.regs.get? r := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment r true hmi

/-! ## Step 2: `add a3, a1, a5` at `0x10d24` (`a3 = src + i`) -/

/-- The `add a3, a1, a5` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d24` are `b3 86 f5 00` (`00f586b3`); the destination write is `x13 ↦ srcVal + a5Val`. -/
theorem memcpy_step_add_a3 (stepNo : Nat) (state : State)
    (srcVal a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d24) 0xb3#8 0x86#8 0xf5#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d24)).regs.get? x11 = some srcVal)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d24)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d24) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d24)).regs.insert x13 (srcVal + a5Val) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d24) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0xb3#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0xb3#8 0x86#8 0xf5#8 0x00#8 = (0x00f586b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x86#8 0xf5#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 11#5, .Regidx 13#5, .ADD)) := by
    rw [wordEq]; exact ext_decode_add_a3_a1_a5_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.RTYPE (.Regidx 15#5, .Regidx 11#5, .Regidx 13#5, .ADD)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d24))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d24) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d24)).regs.insert x13 (srcVal + a5Val) }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 15#5) (.Regidx 11#5) (.Regidx 13#5) .ADD) _ _ _
    unfold Runs
    exact execute_add_a3_a1_a5 _ srcVal a5Val h11 h15
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d24) retired inhibit config
    0xb3#8 0x86#8 0xf5#8 0x00#8 (.RTYPE (.Regidx 15#5, .Regidx 11#5, .Regidx 13#5, .ADD))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpFrameNextPc _ _ x13 _ (by decide))
    (gpFrameGet _ _ x13 _ hart_state (by decide) (by decide))
    (gpFrameGet _ _ x13 _ minstret_increment (by decide) (by decide))
    (gpFrameGet _ _ x13 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 4: `add a4, a0, a5` at `0x10d2c` (`a4 = dst + i`) -/

/-- The `add a4, a0, a5` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d2c` are `33 07 f5 00` (`00f50733`); the destination write is `x14 ↦ dstVal + a5Val`. -/
theorem memcpy_step_add_a4 (stepNo : Nat) (state : State)
    (dstVal a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d2c) 0x33#8 0x07#8 0xf5#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h10 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d2c)).regs.get? x10 = some dstVal)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d2c)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d2c) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d2c)).regs.insert x14 (dstVal + a5Val) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d2c) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x33#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x33#8 0x07#8 0xf5#8 0x00#8 = (0x00f50733 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x07#8 0xf5#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)) := by
    rw [wordEq]; exact ext_decode_add_a4_a0_a5_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d2c))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d2c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d2c)).regs.insert x14 (dstVal + a5Val) }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 15#5) (.Regidx 10#5) (.Regidx 14#5) .ADD) _ _ _
    unfold Runs
    exact execute_add_a4_a0_a5 _ dstVal a5Val h10 h15
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d2c) retired inhibit config
    0x33#8 0x07#8 0xf5#8 0x00#8 (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpFrameNextPc _ _ x14 _ (by decide))
    (gpFrameGet _ _ x14 _ hart_state (by decide) (by decide))
    (gpFrameGet _ _ x14 _ minstret_increment (by decide) (by decide))
    (gpFrameGet _ _ x14 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 5: `addi a5, a5, 1` at `0x10d30` (`i++`) -/

/-- The `addi a5, a5, 1` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d30` are `93 87 17 00` (`00178793`); the destination write is `x15 ↦ a5Val + sext 1`. -/
theorem memcpy_step_addi_a5 (stepNo : Nat) (state : State)
    (a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d30) 0x93#8 0x87#8 0x17#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d30)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d30) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d30)).regs.insert x15 (a5Val + sign_extend (m := 64) 1#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d30) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x87#8 0x17#8 0x00#8 = (0x00178793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x87#8 0x17#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_addi_a5_a5_1_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d30))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d30) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d30)).regs.insert x15 (a5Val + sign_extend (m := 64) 1#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 1#12 (.Regidx 15#5) (.Regidx 15#5) .ADDI) _ _ _
    unfold Runs
    exact execute_addi_a5_a5_1 _ a5Val h15
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d30) retired inhibit config
    0x93#8 0x87#8 0x17#8 0x00#8 (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpFrameNextPc _ _ x15 _ (by decide))
    (gpFrameGet _ _ x15 _ hart_state (by decide) (by decide))
    (gpFrameGet _ _ x15 _ minstret_increment (by decide) (by decide))
    (gpFrameGet _ _ x15 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 7: `j 0x10d1c` at `0x10d38` (unconditional back-edge) -/

/-- `nextPC` slot of `coreControlFlowNextState Y pc` is `pc + 4`. -/
private theorem coreNextPc (Y : State) (pc : BitVec 64) :
    (coreControlFlowNextState Y pc).regs.get? nextPC = some (Sail.BitVec.addInt pc 4) := by
  change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- Any register other than `nextPC` reads through `coreControlFlowNextState Y pc` back to `Y`. -/
private theorem coreGetInc (Y : State) (pc : BitVec 64) (r : Register) (hnp : r ≠ nextPC) :
    (coreControlFlowNextState Y pc).regs.get? r = Y.regs.get? r := by
  simpa [coreControlFlowNextState] using
    writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

/-- The `j 0x10d1c` back-edge (`JAL imm x0`, `imm` byte-offset `-28`), lifted through the generated
`try_step`.  Fetch bytes at `0x10d38` are `6f f0 5f fe` (`fe5ff06f`); the jump target is
`pc + sext imm = 0x10d1c`. -/
theorem memcpy_step_j (stepNo : Nat) (state : State)
    (retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d38) 0x6f#8 0xf0#8 0x5f#8 0xfe#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d38)
          (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)))
        (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  obtain ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeRead, pcLow0, pcLow1,
    alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩ := platform
  have base : BaseInstructionEncoding 0x6f#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x6f#8 0xf0#8 0x5f#8 0xfe#8 = (0xfe5ff06f : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x6f#8 0xf0#8 0x5f#8 0xfe#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1FFFE4#21, zreg)) := by
    rw [wordEq]; exact ext_decode_j_memcpy_run _ privRead mseccfgBits mseccfgRead
  have hPCx : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d38)).regs.get? PC = some (BitVec.ofNat 64 0x10d38) := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC PC
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d38) 4) (by decide)).trans pcRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d38) 4) := by
    unfold get_next_pc
    exact readReg_run _ nextPC _ (coreNextPc _ _)
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (BitVec.ofNat 64 0x10d38) :=
    readReg_run _ PC _ hPCx
  have hmisax : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d38)).regs.get? misa = some misaBits := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC misa
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d38) 4) (by decide)).trans misaRead
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisax]
  have hsum : (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21))
      = BitVec.ofNat 64 0x10d1c := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have halign : Sail.BitVec.access
      (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)) 0 = 0#1 := by
    rw [hsum]; decide
  have hbit1 : Sail.BitVec.access
      (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)) 1 = 0#1 := by
    rw [hsum]; decide
  exact tryStepJRetires stepNo state (BitVec.ofNat 64 0x10d38) (BitVec.ofNat 64 0x10d38) retired
    (0x1FFFE4#21) inhibit config 0x6f#8 0xf0#8 0x5f#8 0xfe#8
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d38) 4) (_get_Misa_C misaBits == 1#1)
    ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeRead, pcLow0, pcLow1,
      alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩
    noMMIO bytes interrupts base decode notExpected hlink hpc halign hbit1 hzca
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 3: `lbu a3, 0(a3)` at `0x10d28` (`a3 = mem[src + i]`)

The genuine load data-access preconditions — the effective-address resolution to `src + i`, the byte
alignment (trivial), `phys_access_check` yielding no fault, the no-MMIO decision, and byte ownership
of `mem[src+i] = v` — are carried abstractly, exactly the stage-2 trust boundary. -/

/-- The `lbu a3, 0(a3)` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d28` are `83 c6 06 00` (`0006c683`); the destination write is `x13 ↦ zext₆₄ v` where `v` is the
owned source byte at `srcAddrBits` (`= src + i`). -/
theorem memcpy_step_lbu (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d28) 0x83#8 0xc6#8 0x06#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d28)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d28)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 13#5) (sign_extend (m := 64) 0#12)
      (Load Data) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcAddrBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x10d28)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d28) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d28)).regs.insert x13 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d28) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x83#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x83#8 0xc6#8 0x06#8 0x00#8 = (0x0006c683 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc6#8 0x06#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0#12, .Regidx 13#5, .Regidx 13#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a3_a3_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (0#12, .Regidx 13#5, .Regidx 13#5, true, 1)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d28) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d28)).regs.insert x13 (zero_extend (m := 64) v) }
      (.Retire_Success ()) := by
    change Runs (execute_LOAD 0#12 (.Regidx 13#5) (.Regidx 13#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 0#12 (.Regidx 13#5) (.Regidx 13#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg aligned physAccess noMMIOr hmem
      (wX_bits_x13_run _ (zero_extend (m := 64) v))
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d28) retired inhibit config
    0x83#8 0xc6#8 0x06#8 0x00#8 (.LOAD (0#12, .Regidx 13#5, .Regidx 13#5, true, 1))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpFrameNextPc _ _ x13 _ (by decide))
    (gpFrameGet _ _ x13 _ hart_state (by decide) (by decide))
    (gpFrameGet _ _ x13 _ minstret_increment (by decide) (by decide))
    (gpFrameGet _ _ x13 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 6: `sb a3, 0(a4)` at `0x10d34` (`mem[dst + i] = a3`)

The store data/address preconditions — the effective address resolving to `dst + i`, the byte
`phys_access_check`, no-MMIO, and the physical `writeBytes` — are carried abstractly (stage-2 trust
boundary).  The store's post-write state `s'` is opaque; `writeBytes_preserves_regs` recovers the
register frame. -/

/-- The `sb a3, 0(a4)` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d34` are `23 00 d7 00` (`00d70023`); the low byte of `a3 = dataBits` is written to
`dstAddrBits = dst + i`, yielding the opaque post-write state `s'`. -/
theorem memcpy_step_sb (stepNo : Nat) (state s' : State)
    (dstAddrBits mstatusBits retired mseccfgBits : BitVec 64) (dataBits : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d34) 0x23#8 0x00#8 0xd7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d34)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d34)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hx13 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d34)).regs.get? x13 = some (BitVec.setWidth 64 dataBits))
    (addrReg : Runs (get_transformed_data_addr (.Regidx 14#5) (sign_extend (m := 64) 0#12)
      (Store Data) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstAddrBits)))
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstAddrBits) 1 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      none)
    (noMMIOw : Runs (within_mmio_writable (physaddr.Physaddr dstAddrBits) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      false)
    (hwrite : Runs (PreSail.writeBytes dstAddrBits.toNat dataBits)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      s' true) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d34) 4) retired)
      false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x23#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x23#8 0x00#8 0xd7#8 0x00#8 = (0x00d70023 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x23#8 0x00#8 0xd7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (0#12, .Regidx 13#5, .Regidx 14#5, 1)) := by
    rw [wordEq]; exact ext_decode_sb_a3_a4_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.STORE (0#12, .Regidx 13#5, .Regidx 14#5, 1)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      s' (.Retire_Success ()) := by
    change Runs (execute_STORE 0#12 (.Regidx 13#5) (.Regidx 14#5) 1) _ _ _
    exact execute_STORE_byte_run _ s' (.Regidx 13#5) (.Regidx 14#5) 0#12 dstAddrBits mstatusBits
      dataBits mstatusReadX privReadX mprvZero (rX_bits_x13_run _ _ hx13) addrReg physAccess
      noMMIOw hwrite
  have regsEq : s'.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x10d34)).regs :=
    writeBytes_preserves_regs dstAddrBits.toNat dataBits _ s' hwrite
  refine tryStepFallThroughRetires stepNo state s' (BitVec.ofNat 64 0x10d34) retired inhibit config
    0x23#8 0x00#8 0xd7#8 0x00#8 (.STORE (0#12, .Regidx 13#5, .Regidx 14#5, 1))
    platform noMMIO bytes interrupts base decode notExpected exec ?_ ?_ ?_ ?_
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  · rw [regsEq]; exact coreNextPc _ _
  · rw [regsEq]; exact coreGetInc _ _ hart_state (by decide)
  · rw [regsEq]; exact coreGetInc _ _ minstret_increment (by decide)
  · rw [regsEq]; exact coreGetInc _ _ minstret (by decide)

/-! ## The loop invariant

`W` is the set of registers the loop body may write (`PC`, `nextPC`, `minstret`,
`minstret_increment`, and the scratch/index GPRs `a3 = x13`, `a4 = x14`, `a5 = x15`).  `StableAgree`
says two states agree on every register outside `W`.  The genuine platform and load/store
data-access preconditions are carried as abstract fields quantified over `StableAgree`-equal states,
so they transport across the loop body's register writes and are re-established at the next loop head
by composing with `StableAgree` — exactly the stage-2 trust boundary. -/

/-- The registers the memcpy loop body may write; everything else is stable. -/
@[reducible] def NonW (r : Register) : Prop :=
  r ≠ PC ∧ r ≠ nextPC ∧ r ≠ minstret ∧ r ≠ minstret_increment ∧
    r ≠ x13 ∧ r ≠ x14 ∧ r ≠ x15

/-- Two states agree on every register the loop body does not write. -/
def StableAgree (base t : State) : Prop :=
  ∀ r : Register, NonW r → t.regs.get? r = base.regs.get? r

/-- The instruction fetch addresses of the memcpy function (entry, loop head, ret, and body). -/
@[reducible] def IsBodyPc (pc : BitVec 64) : Prop :=
  pc = BitVec.ofNat 64 0x10d18 ∨ pc = BitVec.ofNat 64 0x10d1c ∨ pc = BitVec.ofNat 64 0x10d20 ∨
  pc = BitVec.ofNat 64 0x10d24 ∨ pc = BitVec.ofNat 64 0x10d28 ∨ pc = BitVec.ofNat 64 0x10d2c ∨
  pc = BitVec.ofNat 64 0x10d30 ∨ pc = BitVec.ofNat 64 0x10d34 ∨ pc = BitVec.ofNat 64 0x10d38

/-- Abstract configured-machine fetch/decode platform: for any state agreeing with `base` off `W`
positioned at a memcpy fetch address, the generated base-fetch path is enabled.  Never discharged
here (the stage-2 trust boundary); satisfiable because it holds of the actual configured machine at
these aligned, executable code addresses. -/
def AbstractPlatform (base : State) : Prop :=
  ∀ (t : State) (pc : BitVec 64), StableAgree base t → t.regs.get? PC = some pc → IsBodyPc pc →
    FetchBasePlatform t pc ∧ FetchMemoryNoMMIO t pc ∧ InterruptDisabled t ∧ LandingPadNotExpected t

/-- Abstract load/store data-access preconditions at every in-range offset, quantified over
`StableAgree`-equal states holding the resolved effective address in `a3`/`a4`.  Never discharged
here (the stage-2 trust boundary). -/
def AbstractDataAccess (n dst src : BitVec 64) (base : State) : Prop :=
  ∀ (j : Nat) (t : State), j < n.toNat → StableAgree base t →
    (t.regs.get? x13 = some (src + BitVec.ofNat 64 j) →
      Runs (get_transformed_data_addr (.Regidx 13#5) (sign_extend (m := 64) 0#12) (Load Data) 1)
        t t (.Ext_DataAddr_OK (virtaddr.Virtaddr (src + BitVec.ofNat 64 j))) ∧
      Runs (phys_access_check (Load Data) PBMT_PMA .Machine
        (physaddr.Physaddr (src + BitVec.ofNat 64 j)) 1 false) t t none ∧
      Runs (within_mmio_readable (physaddr.Physaddr (src + BitVec.ofNat 64 j)) 1) t t false) ∧
    (t.regs.get? x14 = some (dst + BitVec.ofNat 64 j) →
      Runs (get_transformed_data_addr (.Regidx 14#5) (sign_extend (m := 64) 0#12) (Store Data) 1)
        t t (.Ext_DataAddr_OK (virtaddr.Virtaddr (dst + BitVec.ofNat 64 j))) ∧
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine
        (physaddr.Physaddr (dst + BitVec.ofNat 64 j)) 1 false) t t none ∧
      Runs (within_mmio_writable (physaddr.Physaddr (dst + BitVec.ofNat 64 j)) 1) t t false)

/-- The abstract platform survives to a `StableAgree`-equal state. -/
theorem AbstractPlatform.mono {s s' : State} (h : StableAgree s s') (hp : AbstractPlatform s) :
    AbstractPlatform s' :=
  fun t pc hst hPC hbody => hp t pc (fun r hr => (hst r hr).trans (h r hr)) hPC hbody

/-- The abstract data access survives to a `StableAgree`-equal state. -/
theorem AbstractDataAccess.mono {n dst src : BitVec 64} {s s' : State} (h : StableAgree s s')
    (hd : AbstractDataAccess n dst src s) : AbstractDataAccess n dst src s' :=
  fun j t hj hst => hd j t hj (fun r hr => (hst r hr).trans (h r hr))

/-- Abstract Zicfilp landing-pad update for the leaf `ret` (`jalr x0, 0(ra)`): a no-op on the
configured machine (Zicfilp expects no landing pad here).  Never discharged here (stage-2 trust
boundary). -/
def AbstractElp (base : State) : Prop :=
  ∀ (t : State), StableAgree base t → Runs (update_elp_state (.Regidx 1#5)) t t ()

/-- The abstract Zicfilp update survives to a `StableAgree`-equal state. -/
theorem AbstractElp.mono {s s' : State} (h : StableAgree s s') (he : AbstractElp s) :
    AbstractElp s' :=
  fun t hst => he t (fun r hr => (hst r hr).trans (h r hr))

/-- `a5 + 1` at the loop index. -/
theorem ofNat_add_one (i : Nat) :
    BitVec.ofNat 64 i + sign_extend (m := 64) (1#12) = BitVec.ofNat 64 (i + 1) := by
  have hs : sign_extend (m := 64) (1#12) = (1 : BitVec 64) := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1]
  omega

/-- The unsigned byte load's zero-extension is the width-64 setWidth used by the byte store. -/
theorem zero_extend_setWidth (v : BitVec 8) : zero_extend (m := 64) v = BitVec.setWidth 64 v := by
  simp only [zero_extend, Sail.BitVec.zeroExtend]

/-- The memcpy loop invariant at the loop head `L = 0x10d1c` about to run iteration `i`.  `sInit` is
the fixed reference state (the caller's entry state) against which the compositional framing —
`hstable` (registers) and `hframe` (memory) — is tracked. -/
structure MemcpyInv (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (sInit : State) (i : Nat) (s : State) : Prop where
  hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10d1c)
  ha5 : s.regs.get? x15 = some (BitVec.ofNat 64 i)
  ha0 : s.regs.get? x10 = some dst
  ha1 : s.regs.get? x11 = some src
  ha2 : s.regs.get? x12 = some n
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
  hsrc : ∀ j : Nat, j < n.toNat → s.mem.get? (src + BitVec.ofNat 64 j).toNat = some (srcByte j)
  hcopy : ∀ j : Nat, j < i → s.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (srcByte j)
  hle : i ≤ n.toNat
  hnLt : n.toNat < 2 ^ 64
  hsrcFits : src.toNat + n.toNat ≤ 2 ^ 64
  hdstFits : dst.toNat + n.toNat ≤ 2 ^ 64
  hdstImg : ∀ j : Nat, j < n.toNat → image.readByte? (dst + BitVec.ofNat 64 j).toNat = none
  hdisj : ∀ j k : Nat, j < n.toNat → k < n.toNat →
    (dst + BitVec.ofNat 64 j).toNat ≠ (src + BitVec.ofNat 64 k).toNat
  hplat : AbstractPlatform s
  hdata : AbstractDataAccess n dst src s
  hElp : AbstractElp s
  /-- Every register outside the loop's write set `W` still agrees with the reference state. -/
  hstable : StableAgree sInit s
  /-- The exact memory delta so far: every address not among the copied window `[dst, dst+i)` still
  reads its reference-state value. -/
  hframe : ∀ addr : Nat, (∀ j : Nat, j < i → addr ≠ (dst + BitVec.ofNat 64 j).toNat) →
    s.mem.get? addr = sInit.mem.get? addr

/-! ### `StableAgree` algebra and per-step preservation -/

theorem StableAgree.refl (s : State) : StableAgree s s := fun _ _ => rfl

theorem StableAgree.trans {a b c : State} (h1 : StableAgree a b) (h2 : StableAgree b c) :
    StableAgree a c := fun r hr => (h2 r hr).trans (h1 r hr)

/-- The counter-increment write reads through to the base for any register other than
`minstret_increment`. -/
theorem afterIncGet (base : State) (r : Register) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterIncrement base).regs.get? r = base.regs.get? r := by
  simpa [tryStepControlFlowAfterIncrement] using
    writeReg_read_unchanged base minstret_increment r true hmi

/-- The `try_step` retirement postlude (`minstret`, `PC` writes) reads through for any register
other than those two. -/
theorem retiredFrameGet (afterExec : State) (tPC ret : BitVec 64) (r : Register)
    (hPC : r ≠ PC) (hmr : r ≠ minstret) :
    (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? r = afterExec.regs.get? r := by
  calc (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? r
      = (tryStepControlFlowAfterTick afterExec tPC).regs.get? r := by
        simpa [tryStepControlFlowAfterRetired] using
          writeReg_read_unchanged (tryStepControlFlowAfterTick afterExec tPC) minstret r
            (Sail.BitVec.addInt ret 1) hmr
    _ = afterExec.regs.get? r := by
        simpa [tryStepControlFlowAfterTick] using
          writeReg_read_unchanged afterExec PC r tPC hPC

/-- The `nextPC`-overwrite of a jump reads through for any register other than `nextPC`. -/
theorem jumpFrameGet (base : State) (pc tgt : BitVec 64) (r : Register) (hnpc : r ≠ nextPC)
    (hmi : r ≠ minstret_increment) :
    (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt).regs.get? r =
      base.regs.get? r := by
  calc (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt).regs.get? r
      = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.get? r := by
        simpa [controlFlowJumpState] using
          writeReg_read_unchanged
            (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc) nextPC r tgt hnpc
    _ = base.regs.get? r := by
        rw [coreGetInc (tryStepControlFlowAfterIncrement base) pc r hnpc]; exact afterIncGet base r hmi

/-- A taken-branch / jump `try_step` retirement only writes registers in `W`. -/
theorem stableAgree_jump (base : State) (pc tgt ret : BitVec 64) :
    StableAgree base (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt) tgt ret) := by
  intro r hr
  obtain ⟨hPC, hnpc, hmr, hmi, _, _, _⟩ := hr
  rw [retiredFrameGet _ _ _ r hPC hmr, jumpFrameGet base pc tgt r hnpc hmi]

/-- A GP-writing fall-through `try_step` retirement only writes registers in `W`
(`rd ∈ {x13, x14, x15}`). -/
theorem stableAgree_fallThrough (base : State) (pc ret : BitVec 64) (rd : Register)
    (v : RegisterType rd) (hrdW : rd = x13 ∨ rd = x14 ∨ rd = x15) :
    StableAgree base (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  obtain ⟨hPC, hnpc, hmr, hmi, h13, h14, h15⟩ := hr
  have hrd : r ≠ rd := by rcases hrdW with rfl | rfl | rfl <;> assumption
  rw [retiredFrameGet _ _ _ r hPC hmr]
  show ((coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert rd v).get? r
      = base.regs.get? r
  rw [gpFrameGet (tryStepControlFlowAfterIncrement base) pc rd v r hrd hnpc]
  exact afterIncGet base r hmi

/-- A memory-writing fall-through (`sb`) retirement leaves the register file as the plain
`coreControlFlowNextState`, hence only writes `W` registers. -/
theorem stableAgree_sb (base s' : State) (pc ret : BitVec 64)
    (regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs) :
    StableAgree base (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  obtain ⟨hPC, hnpc, hmr, hmi, _, _, _⟩ := hr
  rw [retiredFrameGet _ _ _ r hPC hmr, regsEq, coreGetInc (tryStepControlFlowAfterIncrement base) pc r hnpc]
  exact afterIncGet base r hmi

/-- The counter-increment write preserves `StableAgree` on the right. -/
theorem StableAgree.afterInc {base t : State} (h : StableAgree base t) :
    StableAgree base (tryStepControlFlowAfterIncrement t) :=
  fun r hr => (afterIncGet t r hr.2.2.2.1).trans (h r hr)

/-- Reading a stable register through the counter-increment and `nextPC` writes of the execute
state, back to a `StableAgree`-equal base. -/
theorem coreGetStable {s : State} (s_k : State) (pc : BitVec 64) (r : Register) (hr : NonW r)
    (hSt : StableAgree s s_k) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s_k) pc).regs.get? r =
      s.regs.get? r := by
  rw [coreGetInc (tryStepControlFlowAfterIncrement s_k) pc r hr.2.1, afterIncGet s_k r hr.2.2.2.1]
  exact hSt r hr

/-- The retirement postlude ticks `PC := tPC`. -/
theorem retiredGetPC (afterExec : State) (tPC ret : BitVec 64) :
    (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? PC = some tPC := by
  have h1 : (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? PC
      = (tryStepControlFlowAfterTick afterExec tPC).regs.get? PC := by
    simpa [tryStepControlFlowAfterRetired] using
      writeReg_read_unchanged (tryStepControlFlowAfterTick afterExec tPC) minstret PC
        (Sail.BitVec.addInt ret 1) (by decide)
  rw [h1]
  change (afterExec.regs.insert PC tPC).get? PC = _
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- `PC` after the retirement, seen through the next step's counter increment, is `tPC`. -/
theorem afterIncRetiredPC (afterExec : State) (tPC ret : BitVec 64) :
    (tryStepControlFlowAfterIncrement
      (tryStepControlFlowAfterRetired afterExec tPC ret)).regs.get? PC = some tPC := by
  rw [afterIncGet _ PC (by decide)]; exact retiredGetPC afterExec tPC ret

/-- `StableAgree` lifts through the counter-increment and `nextPC` writes of the execute state. -/
theorem coreStableAgree {s : State} (s_k : State) (pc : BitVec 64) (hSt : StableAgree s s_k) :
    StableAgree s (coreControlFlowNextState (tryStepControlFlowAfterIncrement s_k) pc) :=
  fun r hr => coreGetStable s_k pc r hr hSt

/-- In-range offset addressing has no wraparound. -/
theorem dstAddr_toNat (base : BitVec 64) (j : Nat) (hfit : base.toNat + j < 2 ^ 64) :
    (base + BitVec.ofNat 64 j).toNat = base.toNat + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The single little-endian byte of a width-1 word is the byte itself. -/
theorem leBytes_one_mem (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 8)
    (h : mem.get? a = some v) :
    ∀ (i' : Nat) (hi : i' < (leBytes 1 v).length),
      mem.get? (a + i') = some (leBytes 1 v)[i'] := by
  intro i' hi
  rw [leBytes_length] at hi
  obtain rfl : i' = 0 := by omega
  have hval : (leBytes 1 v)[0]'(by rw [leBytes_length]; omega) = v := by
    have hv : v.extractLsb' 0 8 = v := by apply BitVec.eq_of_getLsbD_eq; intro k hk; simp
    simp [leBytes, hv]
  simpa [hval] using h

/-- The retirement postlude sets `minstret := ret + 1`. -/
theorem retiredMinstret (afterExec : State) (tPC ret : BitVec 64) :
    (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? minstret =
      some (Sail.BitVec.addInt ret 1) := by
  change ((tryStepControlFlowAfterTick afterExec tPC).regs.insert minstret
    (Sail.BitVec.addInt ret 1)).get? minstret = _
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- Read a register untouched by a taken-branch / jump retirement (needs only the four control
registers to differ; works for `x13/x14/x15` too). -/
theorem jumpRetiredGet (base : State) (pc tgt ret : BitVec 64) (r : Register)
    (hPC : r ≠ PC) (hmr : r ≠ minstret) (hnpc : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt) tgt ret).regs.get? r =
      base.regs.get? r := by
  rw [retiredFrameGet _ _ _ r hPC hmr, jumpFrameGet base pc tgt r hnpc hmi]

/-- Read a register other than the written `rd` untouched by a GP fall-through retirement. -/
theorem fallThroughRetiredGet (base : State) (pc ret : BitVec 64) (rd : Register)
    (v : RegisterType rd) (r : Register) (hPC : r ≠ PC) (hmr : r ≠ minstret) (hrd : r ≠ rd)
    (hnpc : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret).regs.get? r = base.regs.get? r := by
  rw [retiredFrameGet _ _ _ r hPC hmr]
  show ((coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert rd v).get? r
      = base.regs.get? r
  rw [gpFrameGet (tryStepControlFlowAfterIncrement base) pc rd v r hrd hnpc]
  exact afterIncGet base r hmi

/-- The written destination register of a GP fall-through retirement holds the written value. -/
theorem fallThroughRetiredRd (base : State) (pc ret : BitVec 64) (rd : Register)
    (v : RegisterType rd) (hPC : rd ≠ PC) (hmr : rd ≠ minstret) :
    (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret).regs.get? rd = some v := by
  rw [retiredFrameGet _ _ _ rd hPC hmr]
  show ((coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert rd v).get? rd
      = some v
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- The retirement postlude does not touch memory. -/
theorem retiredMem (afterExec : State) (tPC ret : BitVec 64) :
    (tryStepControlFlowAfterRetired afterExec tPC ret).mem = afterExec.mem := rfl

/-- A jump execute does not touch memory. -/
theorem jumpMem (base : State) (pc tgt : BitVec 64) :
    (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt).mem = base.mem := rfl

/-- A GP fall-through execute does not touch memory. -/
theorem fallThroughMem (base : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd) :
    ({ coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }).mem = base.mem := rfl

/-- Read a register untouched by a memory-writing (`sb`) fall-through retirement. -/
theorem sbRetiredGet (base s' : State) (pc ret : BitVec 64)
    (regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs)
    (r : Register) (hPC : r ≠ PC) (hmr : r ≠ minstret) (hnpc : r ≠ nextPC)
    (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) ret).regs.get? r = base.regs.get? r := by
  rw [retiredFrameGet _ _ _ r hPC hmr, regsEq,
    coreGetInc (tryStepControlFlowAfterIncrement base) pc r hnpc]
  exact afterIncGet base r hmi

/-- Reading a distinct address through a memory insert. -/
theorem getInsertNe (mem : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (v : BitVec 8) (h : k ≠ a) :
    (mem.insert k v).get? a = mem.get? a := by
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]; simp [h]

/-- Reading the just-inserted address. -/
theorem getInsertEq (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8) :
    (mem.insert k v).get? k = some v := by
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]; simp

/-- Inserting a byte the image does not back preserves `matchesMemory`. -/
theorem matchesMemory_insert (image : ProgramImage) (mem : Std.ExtHashMap Nat (BitVec 8))
    (k : Nat) (v : BitVec 8) (hm : image.matchesMemory mem) (hk : image.readByte? k = none) :
    image.matchesMemory (mem.insert k v) := by
  intro a byte ha
  have hak : k ≠ a := by rintro rfl; rw [hk] at ha; exact Option.noConfusion ha
  have hget : (mem.insert k v).get? a = mem.get? a := by
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp [hak]
  rw [hget]; exact hm a byte ha

/-- Assemble a `StepPlatform` bundle from the abstract platform field, the pre-step config, and a
concrete fetch fact, for a state `StableAgree`-equal to the invariant's base positioned at `pc`. -/
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

/-- The generated fixed-width byte store inserts exactly one byte and returns `true`. -/
theorem writeBytes_byte_run (s : State) (a : Nat) (value : BitVec (8 * 1)) :
    Runs (PreSail.writeBytes a value) s { s with mem := s.mem.insert a value } true := by
  rw [writeBytes_eq]
  have hv : value.extractLsb' 0 8 = value := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp
  have hlist : (List.ofFn (fun i : Fin 1 => (a + i.val, value.extractLsb' (8 * i.val) 8)))
      = [(a, value)] := by
    rw [List.ofFn_succ, List.ofFn_zero]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, hv]
  rw [hlist]
  simp only [List.forM]
  exact Runs.bind (writeByte_run s a value) rfl

/-! ## Deliverable 2: single-iteration advance `memcpy_adv` -/

set_option maxHeartbeats 1000000 in
/-- One loop iteration (`i < n`) is a length-7 trace that copies one more byte and re-establishes the
invariant at `i + 1`. -/
theorem memcpy_adv (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (sInit : State) (start i : Nat) (s : State)
    (hi : i < n.toNat)
    (hInv : MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte sInit i s) :
    ∃ s', Trace (start + i * 7) 7 s s' ∧
      MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte sInit (i + 1) s' := by
  obtain ⟨retired0, hret0⟩ := hInv.hminstret
  have hi2 : i < 2 ^ 64 := Nat.lt_trans hi hInv.hnLt
  -- Step 0: bne a5,a2 (taken, i ≠ n), pc = 0x10d1c.
  have hbytes0 : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d1c)
      0x63#8 0x94#8 0xc7#8 0x00#8 :=
    fetchBytesAt_10d1c (tryStepControlFlowAfterIncrement s) image hInv.himageEq hInv.hmatches
  have hplat0 : StepPlatform s (BitVec.ofNat 64 0x10d1c) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits :=
    mkStepPlatform s mseccfgBits (BitVec.ofNat 64 0x10d1c) 0x63#8 0x94#8 0xc7#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg (StableAgree.refl s)
      ((afterIncGet s PC (by decide)).trans hInv.hPC) (Or.inr (Or.inl rfl)) hbytes0
  have hcnt0 : StepCounters s retired0 inhibit cfg :=
    ⟨hInv.hhart, hInv.hinhibit, hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hret0⟩
  have h15_0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d1c)).regs.get? x15 = some (BitVec.ofNat 64 i) :=
    (coreGetInc (tryStepControlFlowAfterIncrement s) _ x15 (by decide)).trans
      ((afterIncGet s x15 (by decide)).trans hInv.ha5)
  have h12_0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d1c)).regs.get? x12 = some n :=
    (coreGetStable s _ x12 (by decide) (StableAgree.refl s)).trans hInv.ha2
  have hneq0 : BitVec.ofNat 64 i ≠ n := by
    intro heq
    have h1 : (BitVec.ofNat 64 i).toNat = n.toNat := by rw [heq]
    rw [BitVec.toNat_ofNat] at h1; omega
  have hpc0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d1c)).regs.get? PC = some (BitVec.ofNat 64 0x10d1c) :=
    (coreGetInc (tryStepControlFlowAfterIncrement s) _ PC (by decide)).trans
      ((afterIncGet s PC (by decide)).trans hInv.hPC)
  obtain ⟨misaBits0, _mstatus0, _pcr0, hmisaAfter0, _rest0⟩ := hplat0.1
  have hmisa0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d1c)).regs.get? misa = some misaBits0 :=
    (coreGetInc (tryStepControlFlowAfterIncrement s) _ misa (by decide)).trans hmisaAfter0
  have hsum0 : (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) (8#13)) = BitVec.ofNat 64 0x10d24 := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have halign0 : Sail.BitVec.access (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) (8#13)) 0 = 0#1 := by
    rw [hsum0]; decide
  have hbit1_0 : Sail.BitVec.access (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) (8#13)) 1 = 0#1 := by
    rw [hsum0]; decide
  have h0 := memcpy_step_bne_taken (start + i * 7) s (BitVec.ofNat 64 0x10d1c) n retired0
    mseccfgBits inhibit cfg i hplat0 hcnt0 h15_0 h12_0 hneq0 hpc0 misaBits0 hmisa0 halign0 hbit1_0
  have hSt1 : StableAgree s _ :=
    stableAgree_jump s (BitVec.ofNat 64 0x10d1c) (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13)
      retired0
  have hPC1 := afterIncRetiredPC (controlFlowJumpState (tryStepControlFlowAfterIncrement s)
    (BitVec.ofNat 64 0x10d1c) (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13))
    (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13) retired0
  have hmin1 := retiredMinstret (controlFlowJumpState (tryStepControlFlowAfterIncrement s)
    (BitVec.ofNat 64 0x10d1c) (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13))
    (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13) retired0
  have hx15_1 : _ = some (BitVec.ofNat 64 i) :=
    (jumpRetiredGet s (BitVec.ofNat 64 0x10d1c)
      (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13) retired0 x15
      (by decide) (by decide) (by decide) (by decide)).trans hInv.ha5
  have hmem1 : _ = s.mem :=
    (retiredMem (controlFlowJumpState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d1c)
      (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13))
      (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13) retired0).trans
      (jumpMem s (BitVec.ofNat 64 0x10d1c) (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13))
  generalize hgen1 : tryStepControlFlowAfterRetired (controlFlowJumpState
      (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d1c)
      (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13))
      (BitVec.ofNat 64 0x10d1c + sign_extend (m := 64) 8#13) retired0 = s1
    at h0 hSt1 hPC1 hmin1 hx15_1 hmem1
  -- Step 1: add a3,a1,a5 (a3 = src+i), pc = 0x10d24.
  have hbytes1 : FetchBytesAt (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d24)
      0xb3#8 0x86#8 0xf5#8 0x00#8 :=
    fetchBytesAt_10d24 (tryStepControlFlowAfterIncrement s1) image hInv.himageEq
      (hmem1.symm ▸ hInv.hmatches)
  have hplat1 : StepPlatform s1 (BitVec.ofNat 64 0x10d24) 0xb3#8 0x86#8 0xf5#8 0x00#8 mseccfgBits :=
    mkStepPlatform s1 mseccfgBits (BitVec.ofNat 64 0x10d24) 0xb3#8 0x86#8 0xf5#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt1 (hsum0 ▸ hPC1) (by decide) hbytes1
  have hcnt1 : StepCounters s1 (Sail.BitVec.addInt retired0 1) inhibit cfg :=
    ⟨(hSt1 hart_state (by decide)).trans hInv.hhart,
      (hSt1 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt1 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin1⟩
  have h11_1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10d24)).regs.get? x11 = some src :=
    (coreGetStable s1 _ x11 (by decide) hSt1).trans hInv.ha1
  have h15_1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10d24)).regs.get? x15 = some (BitVec.ofNat 64 i) :=
    (coreGetInc (tryStepControlFlowAfterIncrement s1) _ x15 (by decide)).trans
      ((afterIncGet s1 x15 (by decide)).trans hx15_1)
  have h1 := memcpy_step_add_a3 (start + i * 7 + 1) s1 src (BitVec.ofNat 64 i)
    (Sail.BitVec.addInt retired0 1) mseccfgBits inhibit cfg hplat1 hcnt1 h11_1 h15_1
  have hSt2 : StableAgree s _ :=
    hSt1.trans (stableAgree_fallThrough s1 (BitVec.ofNat 64 0x10d24) (Sail.BitVec.addInt retired0 1)
      x13 (src + BitVec.ofNat 64 i) (Or.inl rfl))
  have hPC2 := afterIncRetiredPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d24) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
        (BitVec.ofNat 64 0x10d24)).regs.insert x13 (src + BitVec.ofNat 64 i) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d24) 4) (Sail.BitVec.addInt retired0 1)
  have hmin2 := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d24) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
        (BitVec.ofNat 64 0x10d24)).regs.insert x13 (src + BitVec.ofNat 64 i) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d24) 4) (Sail.BitVec.addInt retired0 1)
  have hx13_2 := fallThroughRetiredRd s1 (BitVec.ofNat 64 0x10d24) (Sail.BitVec.addInt retired0 1)
    x13 (src + BitVec.ofNat 64 i) (by decide) (by decide)
  have hx15_2 : _ = some (BitVec.ofNat 64 i) :=
    (fallThroughRetiredGet s1 (BitVec.ofNat 64 0x10d24) (Sail.BitVec.addInt retired0 1) x13
      (src + BitVec.ofNat 64 i) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hx15_1
  have hmem2 : _ = s.mem :=
    (retiredMem
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d24) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
          (BitVec.ofNat 64 0x10d24)).regs.insert x13 (src + BitVec.ofNat 64 i) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d24) 4) (Sail.BitVec.addInt retired0 1)).trans
      ((fallThroughMem s1 (BitVec.ofNat 64 0x10d24) x13 (src + BitVec.ofNat 64 i)).trans hmem1)
  generalize hgen2 : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d24) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
          (BitVec.ofNat 64 0x10d24)).regs.insert x13 (src + BitVec.ofNat 64 i) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d24) 4) (Sail.BitVec.addInt retired0 1) = s2
    at h1 hSt2 hPC2 hmin2 hx13_2 hx15_2 hmem2
  -- Step 2: lbu a3,0(a3) (a3 = mem[src+i]), pc = 0x10d28.
  have hsum24 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d24) 4 = BitVec.ofNat 64 0x10d28 := by decide
  have hbytes2 : FetchBytesAt (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10d28)
      0x83#8 0xc6#8 0x06#8 0x00#8 :=
    fetchBytesAt_10d28 (tryStepControlFlowAfterIncrement s2) image hInv.himageEq
      (hmem2.symm ▸ hInv.hmatches)
  have hplat2 : StepPlatform s2 (BitVec.ofNat 64 0x10d28) 0x83#8 0xc6#8 0x06#8 0x00#8 mseccfgBits :=
    mkStepPlatform s2 mseccfgBits (BitVec.ofNat 64 0x10d28) 0x83#8 0xc6#8 0x06#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt2 (hsum24 ▸ hPC2) (by decide) hbytes2
  have hcnt2 : StepCounters s2 (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) inhibit cfg :=
    ⟨(hSt2 hart_state (by decide)).trans hInv.hhart,
      (hSt2 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt2 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin2⟩
  have hmstat2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10d28)).regs.get? mstatus = some mstatusBits :=
    (coreGetStable s2 _ mstatus (by decide) hSt2).trans hInv.hmstatus
  have hpriv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10d28)).regs.get? cur_privilege = some Privilege.Machine :=
    (coreGetStable s2 _ cur_privilege (by decide) hSt2).trans hInv.hcur
  have hx13t2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10d28)).regs.get? x13 = some (src + BitVec.ofNat 64 i) :=
    (coreGetInc (tryStepControlFlowAfterIncrement s2) _ x13 (by decide)).trans
      ((afterIncGet s2 x13 (by decide)).trans hx13_2)
  obtain ⟨addrReg2, physAccess2, noMMIOr2⟩ :=
    (hInv.hdata i _ hi (coreStableAgree s2 (BitVec.ofNat 64 0x10d28) hSt2)).1 hx13t2
  have hbyte2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10d28)).mem.get? (src + BitVec.ofNat 64 i).toNat = some (srcByte i) :=
    hmem2 ▸ hInv.hsrc i hi
  have h2 := memcpy_step_lbu (start + i * 7 + 2) s2 (src + BitVec.ofNat 64 i) mstatusBits
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) mseccfgBits (srcByte i) inhibit cfg
    hplat2 hcnt2 hmstat2 hpriv2 hInv.hmprv addrReg2 (is_aligned_vaddr_one _) physAccess2 noMMIOr2
    (leBytes_one_mem _ _ (srcByte i) hbyte2)
  have hSt3 : StableAgree s _ :=
    hSt2.trans (stableAgree_fallThrough s2 (BitVec.ofNat 64 0x10d28)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x13 (zero_extend (m := 64) (srcByte i))
      (Or.inl rfl))
  have hPC3 := afterIncRetiredPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10d28) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
        (BitVec.ofNat 64 0x10d28)).regs.insert x13 (zero_extend (m := 64) (srcByte i)) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d28) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
  have hmin3 := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10d28) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
        (BitVec.ofNat 64 0x10d28)).regs.insert x13 (zero_extend (m := 64) (srcByte i)) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d28) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
  have hx13_3 := fallThroughRetiredRd s2 (BitVec.ofNat 64 0x10d28)
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x13 (zero_extend (m := 64) (srcByte i))
    (by decide) (by decide)
  have hx15_3 : _ = some (BitVec.ofNat 64 i) :=
    (fallThroughRetiredGet s2 (BitVec.ofNat 64 0x10d28)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x13 (zero_extend (m := 64) (srcByte i))
      x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx15_2
  have hmem3 : _ = s.mem :=
    (retiredMem
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10d28) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
          (BitVec.ofNat 64 0x10d28)).regs.insert x13 (zero_extend (m := 64) (srcByte i)) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d28) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)).trans
      ((fallThroughMem s2 (BitVec.ofNat 64 0x10d28) x13 (zero_extend (m := 64) (srcByte i))).trans
        hmem2)
  generalize hgen3 : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10d28) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
          (BitVec.ofNat 64 0x10d28)).regs.insert x13 (zero_extend (m := 64) (srcByte i)) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d28) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) = s3
    at h2 hSt3 hPC3 hmin3 hx13_3 hx15_3 hmem3
  -- Step 3: add a4,a0,a5 (a4 = dst+i), pc = 0x10d2c.
  have hsum28 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d28) 4 = BitVec.ofNat 64 0x10d2c := by decide
  have hbytes3 : FetchBytesAt (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10d2c)
      0x33#8 0x07#8 0xf5#8 0x00#8 :=
    fetchBytesAt_10d2c (tryStepControlFlowAfterIncrement s3) image hInv.himageEq
      (hmem3.symm ▸ hInv.hmatches)
  have hplat3 : StepPlatform s3 (BitVec.ofNat 64 0x10d2c) 0x33#8 0x07#8 0xf5#8 0x00#8 mseccfgBits :=
    mkStepPlatform s3 mseccfgBits (BitVec.ofNat 64 0x10d2c) 0x33#8 0x07#8 0xf5#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt3 (hsum28 ▸ hPC3) (by decide) hbytes3
  have hcnt3 : StepCounters s3
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) inhibit cfg :=
    ⟨(hSt3 hart_state (by decide)).trans hInv.hhart,
      (hSt3 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt3 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin3⟩
  have h10_3 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
      (BitVec.ofNat 64 0x10d2c)).regs.get? x10 = some dst :=
    (coreGetStable s3 _ x10 (by decide) hSt3).trans hInv.ha0
  have h15_3 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
      (BitVec.ofNat 64 0x10d2c)).regs.get? x15 = some (BitVec.ofNat 64 i) :=
    (coreGetInc (tryStepControlFlowAfterIncrement s3) _ x15 (by decide)).trans
      ((afterIncGet s3 x15 (by decide)).trans hx15_3)
  have h3 := memcpy_step_add_a4 (start + i * 7 + 3) s3 dst (BitVec.ofNat 64 i)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) mseccfgBits inhibit
    cfg hplat3 hcnt3 h10_3 h15_3
  have hSt4 : StableAgree s _ :=
    hSt3.trans (stableAgree_fallThrough s3 (BitVec.ofNat 64 0x10d2c)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x14
      (dst + BitVec.ofNat 64 i) (Or.inr (Or.inl rfl)))
  have hPC4 := afterIncRetiredPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10d2c) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
        (BitVec.ofNat 64 0x10d2c)).regs.insert x14 (dst + BitVec.ofNat 64 i) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d2c) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
  have hmin4 := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10d2c) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
        (BitVec.ofNat 64 0x10d2c)).regs.insert x14 (dst + BitVec.ofNat 64 i) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d2c) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
  have hx13_4 : _ = some (zero_extend (m := 64) (srcByte i)) :=
    (fallThroughRetiredGet s3 (BitVec.ofNat 64 0x10d2c)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x14
      (dst + BitVec.ofNat 64 i) x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hx13_3
  have hx14_4 := fallThroughRetiredRd s3 (BitVec.ofNat 64 0x10d2c)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x14
    (dst + BitVec.ofNat 64 i) (by decide) (by decide)
  have hx15_4 : _ = some (BitVec.ofNat 64 i) :=
    (fallThroughRetiredGet s3 (BitVec.ofNat 64 0x10d2c)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x14
      (dst + BitVec.ofNat 64 i) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hx15_3
  have hmem4 : _ = s.mem :=
    (retiredMem
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10d2c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
          (BitVec.ofNat 64 0x10d2c)).regs.insert x14 (dst + BitVec.ofNat 64 i) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d2c) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)).trans
      ((fallThroughMem s3 (BitVec.ofNat 64 0x10d2c) x14 (dst + BitVec.ofNat 64 i)).trans hmem3)
  generalize hgen4 : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10d2c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
          (BitVec.ofNat 64 0x10d2c)).regs.insert x14 (dst + BitVec.ofNat 64 i) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d2c) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) = s4
    at h3 hSt4 hPC4 hmin4 hx13_4 hx14_4 hx15_4 hmem4
  -- Step 4: addi a5,a5,1 (i++), pc = 0x10d30.
  have hsum2c : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d2c) 4 = BitVec.ofNat 64 0x10d30 := by decide
  have hbytes4 : FetchBytesAt (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10d30)
      0x93#8 0x87#8 0x17#8 0x00#8 :=
    fetchBytesAt_10d30 (tryStepControlFlowAfterIncrement s4) image hInv.himageEq
      (hmem4.symm ▸ hInv.hmatches)
  have hplat4 : StepPlatform s4 (BitVec.ofNat 64 0x10d30) 0x93#8 0x87#8 0x17#8 0x00#8 mseccfgBits :=
    mkStepPlatform s4 mseccfgBits (BitVec.ofNat 64 0x10d30) 0x93#8 0x87#8 0x17#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt4 (hsum2c ▸ hPC4) (by decide) hbytes4
  have hcnt4 : StepCounters s4
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) inhibit cfg :=
    ⟨(hSt4 hart_state (by decide)).trans hInv.hhart,
      (hSt4 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt4 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin4⟩
  have h15_4 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4)
      (BitVec.ofNat 64 0x10d30)).regs.get? x15 = some (BitVec.ofNat 64 i) :=
    (coreGetInc (tryStepControlFlowAfterIncrement s4) _ x15 (by decide)).trans
      ((afterIncGet s4 x15 (by decide)).trans hx15_4)
  have h4 := memcpy_step_addi_a5 (start + i * 7 + 4) s4 (BitVec.ofNat 64 i)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
      1) 1) mseccfgBits inhibit cfg hplat4 hcnt4 h15_4
  have hSt5 : StableAgree s _ :=
    hSt4.trans (stableAgree_fallThrough s4 (BitVec.ofNat 64 0x10d30)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) x15 (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) (Or.inr (Or.inr rfl)))
  have hPC5 := afterIncRetiredPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10d30) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4)
        (BitVec.ofNat 64 0x10d30)).regs.insert x15 (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d30) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1)
  have hmin5 := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10d30) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4)
        (BitVec.ofNat 64 0x10d30)).regs.insert x15 (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d30) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1)
  have hx13_5 : _ = some (zero_extend (m := 64) (srcByte i)) :=
    (fallThroughRetiredGet s4 (BitVec.ofNat 64 0x10d30)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) x15 (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) x13
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13_4
  have hx14_5 : _ = some (dst + BitVec.ofNat 64 i) :=
    (fallThroughRetiredGet s4 (BitVec.ofNat 64 0x10d30)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) x15 (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) x14
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx14_4
  have hx15_5 := fallThroughRetiredRd s4 (BitVec.ofNat 64 0x10d30)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
      1) 1) x15 (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) (by decide) (by decide)
  have hmem5 : _ = s.mem :=
    (retiredMem
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10d30) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4)
          (BitVec.ofNat 64 0x10d30)).regs.insert x15
            (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d30) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1)).trans
      ((fallThroughMem s4 (BitVec.ofNat 64 0x10d30) x15
        (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12)).trans hmem4)
  generalize hgen5 : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10d30) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4)
          (BitVec.ofNat 64 0x10d30)).regs.insert x15
            (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d30) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) = s5
    at h4 hSt5 hPC5 hmin5 hx13_5 hx14_5 hx15_5 hmem5
  -- Step 5: sb a3,0(a4) (mem[dst+i] = a3), pc = 0x10d34.
  have hsum30 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d30) 4 = BitVec.ofNat 64 0x10d34 := by decide
  have hbytes5 : FetchBytesAt (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10d34)
      0x23#8 0x00#8 0xd7#8 0x00#8 :=
    fetchBytesAt_10d34 (tryStepControlFlowAfterIncrement s5) image hInv.himageEq
      (hmem5.symm ▸ hInv.hmatches)
  have hplat5 : StepPlatform s5 (BitVec.ofNat 64 0x10d34) 0x23#8 0x00#8 0xd7#8 0x00#8 mseccfgBits :=
    mkStepPlatform s5 mseccfgBits (BitVec.ofNat 64 0x10d34) 0x23#8 0x00#8 0xd7#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt5 (hsum30 ▸ hPC5) (by decide) hbytes5
  have hcnt5 : StepCounters s5 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) inhibit cfg :=
    ⟨(hSt5 hart_state (by decide)).trans hInv.hhart,
      (hSt5 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt5 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin5⟩
  have hmstat5 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
      (BitVec.ofNat 64 0x10d34)).regs.get? mstatus = some mstatusBits :=
    (coreGetStable s5 _ mstatus (by decide) hSt5).trans hInv.hmstatus
  have hpriv5 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
      (BitVec.ofNat 64 0x10d34)).regs.get? cur_privilege = some Privilege.Machine :=
    (coreGetStable s5 _ cur_privilege (by decide) hSt5).trans hInv.hcur
  have hx13_at5 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
      (BitVec.ofNat 64 0x10d34)).regs.get? x13 = some (BitVec.setWidth 64 (srcByte i)) :=
    (coreGetInc (tryStepControlFlowAfterIncrement s5) _ x13 (by decide)).trans
      ((afterIncGet s5 x13 (by decide)).trans
        (hx13_5.trans (congrArg some (zero_extend_setWidth (srcByte i)))))
  have hx14_at5 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
      (BitVec.ofNat 64 0x10d34)).regs.get? x14 = some (dst + BitVec.ofNat 64 i) :=
    (coreGetInc (tryStepControlFlowAfterIncrement s5) _ x14 (by decide)).trans
      ((afterIncGet s5 x14 (by decide)).trans hx14_5)
  obtain ⟨addrReg5, physAccess5, noMMIOw5⟩ :=
    (hInv.hdata i _ hi (coreStableAgree s5 (BitVec.ofNat 64 0x10d34) hSt5)).2 hx14_at5
  have hwrite5 := writeBytes_byte_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10d34))
    (dst + BitVec.ofNat 64 i).toNat (srcByte i)
  have hs'mem : ({ coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
        (BitVec.ofNat 64 0x10d34) with
      mem := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
        (BitVec.ofNat 64 0x10d34)).mem.insert (dst + BitVec.ofNat 64 i).toNat (srcByte i) }).mem =
      s.mem.insert (dst + BitVec.ofNat 64 i).toNat (srcByte i) := by
    show (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
        (BitVec.ofNat 64 0x10d34)).mem.insert (dst + BitVec.ofNat 64 i).toNat (srcByte i) =
        s.mem.insert (dst + BitVec.ofNat 64 i).toNat (srcByte i)
    rw [show (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
      (BitVec.ofNat 64 0x10d34)).mem = s.mem from hmem5]
  generalize hgens' : ({ coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
        (BitVec.ofNat 64 0x10d34) with
      mem := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
        (BitVec.ofNat 64 0x10d34)).mem.insert (dst + BitVec.ofNat 64 i).toNat (srcByte i) }) = s'
    at hwrite5 hs'mem
  have h5 := memcpy_step_sb (start + i * 7 + 5) s5 s' (dst + BitVec.ofNat 64 i) mstatusBits
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
      (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) mseccfgBits (srcByte i) inhibit cfg
    hplat5 hcnt5 hmstat5 hpriv5 hInv.hmprv hx13_at5 addrReg5 physAccess5 noMMIOw5 hwrite5
  have hregsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
      (BitVec.ofNat 64 0x10d34)).regs := by rw [← hgens']
  have hSt6 : StableAgree s _ :=
    hSt5.trans (stableAgree_sb s5 s' (BitVec.ofNat 64 0x10d34)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) hregsEq)
  have hPC6 := afterIncRetiredPC s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d34) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
      (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1)
  have hmin6 := retiredMinstret s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d34) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
      (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1)
  have hx15_6 : _ = some (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) :=
    (sbRetiredGet s5 s' (BitVec.ofNat 64 0x10d34)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) hregsEq x15
      (by decide) (by decide) (by decide) (by decide)).trans hx15_5
  have hmem6 : _ = s.mem.insert (dst + BitVec.ofNat 64 i).toNat (srcByte i) :=
    (retiredMem s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d34) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1)).trans hs'mem
  generalize hgen6 : tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d34) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) = s6
    at h5 hSt6 hPC6 hmin6 hx15_6 hmem6
  -- Step 6: j 0x10d1c (back-edge), pc = 0x10d38.
  have hsum34 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d34) 4 = BitVec.ofNat 64 0x10d38 := by decide
  have hbytes6 : FetchBytesAt (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10d38)
      0x6f#8 0xf0#8 0x5f#8 0xfe#8 :=
    fetchBytesAt_10d38 (tryStepControlFlowAfterIncrement s6) image hInv.himageEq
      (hmem6.symm ▸ matchesMemory_insert image s.mem (dst + BitVec.ofNat 64 i).toNat (srcByte i)
        hInv.hmatches (hInv.hdstImg i hi))
  have hplat6 : StepPlatform s6 (BitVec.ofNat 64 0x10d38) 0x6f#8 0xf0#8 0x5f#8 0xfe#8 mseccfgBits :=
    mkStepPlatform s6 mseccfgBits (BitVec.ofNat 64 0x10d38) 0x6f#8 0xf0#8 0x5f#8 0xfe#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt6 (hsum34 ▸ hPC6) (by decide) hbytes6
  have hcnt6 : StepCounters s6 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) inhibit
      cfg :=
    ⟨(hSt6 hart_state (by decide)).trans hInv.hhart,
      (hSt6 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt6 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin6⟩
  have h6 := memcpy_step_j (start + i * 7 + 6) s6 (Sail.BitVec.addInt (Sail.BitVec.addInt
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
      1) 1) 1) mseccfgBits inhibit cfg hplat6 hcnt6
  -- Assemble the 7-step trace and re-establish the invariant at i+1.
  have hSt7 : StableAgree s _ :=
    hSt6.trans (stableAgree_jump s6 (BitVec.ofNat 64 0x10d38)
      (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21))
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1))
  have hsumJ : (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21))
      = BitVec.ofNat 64 0x10d1c := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have hmemS7 : _ = s.mem.insert (dst + BitVec.ofNat 64 i).toNat (srcByte i) :=
    (retiredMem (controlFlowJumpState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10d38)
      (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)))
      (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21))
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1)).trans
      ((jumpMem s6 (BitVec.ofNat 64 0x10d38)
        (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21))).trans hmem6)
  have htr : Trace (start + i * 7) 7 s
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10d38)
          (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)))
        (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21))
        (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
          (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1)) := by
    trace_steps [h0, h1, h2, h3, h4, h5, h6]
  refine ⟨_, htr, ?_⟩
  refine ⟨?hPC, ?ha5, ?ha0, ?ha1, ?ha2, ?hra, ?hcur, ?hmstatus, ?hmprv, ?hmseccfg, ?hhart,
      ?hinhibit, ?hnotInhibited, ?hcfg, ?hmachineEnabled, ?hminstret, ?himageEq, ?hmatches, ?hsrc,
      ?hcopy, ?hle, ?hnLt, ?hsrcFits, ?hdstFits, ?hdstImg, ?hdisj, ?hplat, ?hdata, ?hElp,
      ?hstable, ?hframe⟩
  case hPC =>
    rw [retiredGetPC _ _ _, hsumJ]
  case ha5 =>
    exact (jumpRetiredGet s6 (BitVec.ofNat 64 0x10d38)
      (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21))
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1) x15
      (by decide) (by decide) (by decide) (by decide)).trans
      (hx15_6.trans (congrArg some (ofNat_add_one i)))
  case ha0 => exact (hSt7 x10 (by decide)).trans hInv.ha0
  case ha1 => exact (hSt7 x11 (by decide)).trans hInv.ha1
  case ha2 => exact (hSt7 x12 (by decide)).trans hInv.ha2
  case hra => exact (hSt7 x1 (by decide)).trans hInv.hra
  case hcur => exact (hSt7 cur_privilege (by decide)).trans hInv.hcur
  case hmstatus => exact (hSt7 mstatus (by decide)).trans hInv.hmstatus
  case hmprv => exact hInv.hmprv
  case hmseccfg => exact (hSt7 mseccfg (by decide)).trans hInv.hmseccfg
  case hhart => exact (hSt7 hart_state (by decide)).trans hInv.hhart
  case hinhibit => exact (hSt7 mcountinhibit (by decide)).trans hInv.hinhibit
  case hnotInhibited => exact hInv.hnotInhibited
  case hcfg => exact (hSt7 minstretcfg (by decide)).trans hInv.hcfg
  case hmachineEnabled => exact hInv.hmachineEnabled
  case hminstret =>
    exact ⟨_, retiredMinstret (controlFlowJumpState (tryStepControlFlowAfterIncrement s6)
      (BitVec.ofNat 64 0x10d38) (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)))
      (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21))
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) 1)⟩
  case himageEq => exact hInv.himageEq
  case hmatches =>
    exact hmemS7.symm ▸ matchesMemory_insert image s.mem (dst + BitVec.ofNat 64 i).toNat
      (srcByte i) hInv.hmatches (hInv.hdstImg i hi)
  case hsrc =>
    intro j hj
    rw [hmemS7, getInsertNe _ _ _ _ (hInv.hdisj i j hi hj)]
    exact hInv.hsrc j hj
  case hcopy =>
    intro j hj
    rw [hmemS7]
    have hfits := hInv.hdstFits
    rcases Nat.lt_or_ge j i with hlt | hge
    · have hfit_i : dst.toNat + i < 2 ^ 64 := by omega
      have hfit_j : dst.toNat + j < 2 ^ 64 := by omega
      have hne : (dst + BitVec.ofNat 64 i).toNat ≠ (dst + BitVec.ofNat 64 j).toNat := by
        rw [dstAddr_toNat dst i hfit_i, dstAddr_toNat dst j hfit_j]; omega
      rw [getInsertNe _ _ _ _ hne]; exact hInv.hcopy j hlt
    · have hji : j = i := by omega
      subst hji
      rw [getInsertEq]
  case hle => omega
  case hnLt => exact hInv.hnLt
  case hsrcFits => exact hInv.hsrcFits
  case hdstFits => exact hInv.hdstFits
  case hdstImg => exact hInv.hdstImg
  case hdisj => exact hInv.hdisj
  case hplat => exact AbstractPlatform.mono hSt7 hInv.hplat
  case hdata => exact AbstractDataAccess.mono hSt7 hInv.hdata
  case hElp => exact AbstractElp.mono hSt7 hInv.hElp
  case hstable => exact hInv.hstable.trans hSt7
  case hframe => rw [hmemS7]; exact frame_insert_step hInv.hframe

/-! ## Deliverable 3: whole-loop trace `memcpy_loop` -/

/-- The whole byte-copy loop: `n` iterations from the `i = 0` loop head to the `i = n` loop head, a
length-`n * 7` trace establishing the invariant at `n` (all `n` bytes copied). -/
theorem memcpy_loop (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (sInit : State) (start : Nat) (s0 : State)
    (hInv0 : MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte sInit 0 s0) :
    ∃ sN, Trace start (n.toNat * 7) s0 sN ∧
      MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte sInit n.toNat sN :=
  Trace.invariantIterate (L := 7) (start := start)
    (Inv := fun i s => MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte sInit i s)
    n.toNat
    (fun i s hi hInv => memcpy_adv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte
      sInit start i s hi hInv)
    hInv0

/-! ## Exit step lemmas: `bne` not taken, then `ret` -/

/-- Reading `ra = x1` via `rX_bits`. -/
theorem rX_bits_x1_run (s : State) (v : BitVec 64) (h : s.regs.get? x1 = some v) :
    Runs (rX_bits (.Regidx 1#5)) s s v := by
  have r1 : (Sail.BitVec.toNatInt (1#5)).toNat = 1 := by decide
  unfold Runs
  simp [rX_bits, rX, r1, h, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

/-- The loop-head `bne a5, a2` NOT taken (`a5 = i = n = a2`): retires with `PC = pc + 4 = 0x10d20`. -/
theorem memcpy_step_bne_not_taken (stepNo : Nat) (state : State)
    (a2v retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64) (i : Nat)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d1c) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d1c)).regs.get? x15 = some (BitVec.ofNat 64 i))
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d1c)).regs.get? x12 = some a2v)
    (heq : BitVec.ofNat 64 i = a2v) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d1c))
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d1c) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8 = (0x00c79463 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (8#13, .Regidx 12#5, .Regidx 15#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bne_a5_a2_run _ privRead mseccfgBits mseccfgRead
  have hcond : Runs (bTypeTaken (.Regidx 12#5) (.Regidx 15#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d1c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d1c))
      false := by
    have h := bTypeTaken_bne_run _ (BitVec.ofNat 64 i) a2v h15 h12
    rwa [show (BitVec.ofNat 64 i != a2v) = false by rw [heq]; simp] at h
  exact tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10d1c) retired
    (8#13) (.Regidx 12#5) (.Regidx 15#5) .BNE inhibit config 0x63#8 0x94#8 0xc7#8 0x00#8
    platform noMMIO bytes interrupts base decode notExpected hcond hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- `ret` (`jalr x0, 0(ra)`) at `0x10d20`: retires with `PC = ra` (bit 0 cleared).  Fetch bytes are
`67 80 00 00` (`00008067`). -/
theorem memcpy_step_ret (stepNo : Nat) (state : State)
    (rs1Val retired mseccfgBits misaBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d20) 0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d20))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d20))
      rs1Val)
    (hbit1 : Sail.BitVec.access rs1Val 1 = 0#1)
    (hElp : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d20))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d20))
      ())
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d20)).regs.get? misa = some misaBits) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d20)
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
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d20))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d20))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d20) 4) := by
    unfold get_next_pc; exact readReg_run _ nextPC _ (coreNextPc _ _)
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d20))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d20))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepRetRetires stepNo state (BitVec.ofNat 64 0x10d20) retired (.Regidx 1#5)
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d20) 4) rs1Val inhibit config 0x67#8 0x80#8 0x00#8 0x00#8
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected hElp hlink
    hrs1 hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- A not-taken branch retirement only writes registers in `W`. -/
theorem stableAgree_notTaken (base : State) (pc ret : BitVec 64) :
    StableAgree base (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr
  rw [retiredFrameGet _ _ _ r hr.1 hr.2.2.1, coreGetInc _ pc r hr.2.1]
  exact afterIncGet base r hr.2.2.2.1

/-- The not-taken branch does not write memory. -/
theorem notTakenMem (base : State) (pc ret : BitVec 64) :
    (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret).mem = base.mem := rfl

/-- `li a5, 0` = `addi a5, x0, 0`: writes `x15 ↦ 0`. -/
theorem execute_li_a5_0 (state : State) :
    (execute_ITYPE 0#12 (.Regidx 0#5) (.Regidx 15#5) .ADDI).run state =
      .ok (.Retire_Success ())
        { state with regs := state.regs.insert x15 (BitVec.ofNat 64 0) } := by
  have r0Nat : (Sail.BitVec.toNatInt 0#5).toNat = 0 := by decide
  have r15Nat : (Sail.BitVec.toNatInt 15#5).toNat = 15 := by decide
  have hval : (zeros : BitVec 64) + Sail.BitVec.signExtend (0#12) 64 = BitVec.ofNat 64 0 := by
    have hz : (zeros : BitVec 64) = 0#64 := rfl
    have hse : Sail.BitVec.signExtend (0#12) 64 = (0#64 : BitVec 64) := by
      unfold Sail.BitVec.signExtend; bv_decide
    rw [hz, hse]; decide
  unfold execute_ITYPE
  simp [rX_bits, rX, wX_bits, wX, PreSail.writeReg, r0Nat, r15Nat, hval, RETIRE_SUCCESS,
    zero_reg, EStateM.run, EStateM.bind, EStateM.modifyGet, EStateM.pure,
    EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet,
    modify, xreg_write_callback,
    xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names, encdec_reg_forwards,
    encdec_reg_forwards_matches, reg_arch_name_raw_forwards, LeanRV64DExecutable.Functions.not,
    zero_extend, sign_extend, regval_into_reg, regval_from_reg]

/-- The entry `li a5, 0` at `0x10d18` (`a5 ↦ 0`), lifted through the generated `try_step`.  Fetch
bytes are `93 07 00 00` (`00000793`); `PC` ticks to the loop head `0x10d1c`. -/
theorem memcpy_step_li (stepNo : Nat) (state : State) (retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d18) 0x93#8 0x07#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d18) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d18)).regs.insert x15 (BitVec.ofNat 64 0) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d18) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x07#8 0x00#8 0x00#8 = (0x00000793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x07#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_li_a5_0_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d18))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d18) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d18)).regs.insert x15 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 0#5) (.Regidx 15#5) .ADDI) _ _ _
    unfold Runs
    exact execute_li_a5_0 _
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d18) retired inhibit config
    0x93#8 0x07#8 0x00#8 0x00#8 (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpFrameNextPc _ _ x15 _ (by decide))
    (gpFrameGet _ _ x15 _ hart_state (by decide) (by decide))
    (gpFrameGet _ _ x15 _ minstret_increment (by decide) (by decide))
    (gpFrameGet _ _ x15 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Deliverable 4: loop exit `memcpy_exit` -/

set_option maxHeartbeats 1000000 in
/-- After all `n` bytes are copied (`i = n`), the loop test falls through (`a5 = n`) and `ret`
returns: a 2-step trace to the caller with `PC = ra` (bit 0 cleared), all `n` bytes present at the
destination, and the arguments and code image preserved. -/
theorem memcpy_exit (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (sInit : State) (start : Nat) (s : State)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hInv : MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte sInit n.toNat s) :
    ∃ s'', Trace start 2 s s'' ∧
      s''.regs.get? PC = some (Sail.BitVec.update retAddr 0 0#1) ∧
      (∀ j : Nat, j < n.toNat →
        s''.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (srcByte j)) ∧
      s''.regs.get? x10 = some dst ∧ s''.regs.get? x11 = some src ∧
      s''.regs.get? x12 = some n ∧ s''.regs.get? x1 = some retAddr ∧
      image.matchesMemory s''.mem ∧
      StableAgree sInit s'' ∧ MemFramed dst n sInit s'' := by
  obtain ⟨retired0, hret0⟩ := hInv.hminstret
  -- Step 0: bne a5,a2 NOT taken (a5 = n).
  have hbytes0 : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d1c)
      0x63#8 0x94#8 0xc7#8 0x00#8 :=
    fetchBytesAt_10d1c (tryStepControlFlowAfterIncrement s) image hInv.himageEq hInv.hmatches
  have hplat0 : StepPlatform s (BitVec.ofNat 64 0x10d1c) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits :=
    mkStepPlatform s mseccfgBits (BitVec.ofNat 64 0x10d1c) 0x63#8 0x94#8 0xc7#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg (StableAgree.refl s)
      ((afterIncGet s PC (by decide)).trans hInv.hPC) (Or.inr (Or.inl rfl)) hbytes0
  have hcnt0 : StepCounters s retired0 inhibit cfg :=
    ⟨hInv.hhart, hInv.hinhibit, hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hret0⟩
  have h15_0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d1c)).regs.get? x15 = some (BitVec.ofNat 64 n.toNat) :=
    (coreGetInc (tryStepControlFlowAfterIncrement s) _ x15 (by decide)).trans
      ((afterIncGet s x15 (by decide)).trans hInv.ha5)
  have h12_0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d1c)).regs.get? x12 = some n :=
    (coreGetStable s _ x12 (by decide) (StableAgree.refl s)).trans hInv.ha2
  have heq0 : BitVec.ofNat 64 n.toNat = n := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  have hb := memcpy_step_bne_not_taken start s n retired0 mseccfgBits inhibit cfg n.toNat
    hplat0 hcnt0 h15_0 h12_0 heq0
  have hSt1 : StableAgree s _ :=
    stableAgree_notTaken s (BitVec.ofNat 64 0x10d1c) retired0
  have hPC1 := afterIncRetiredPC
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d1c))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d1c) 4) retired0
  have hmem1 : _ = s.mem := notTakenMem s (BitVec.ofNat 64 0x10d1c) retired0
  have hmin1 := retiredMinstret
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d1c))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d1c) 4) retired0
  generalize hgen1 : tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d1c))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d1c) 4) retired0 = s1
    at hb hSt1 hPC1 hmem1 hmin1
  -- Step 1: ret.
  have hsumL4 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d1c) 4 = BitVec.ofNat 64 0x10d20 := by decide
  have hbytes1 : FetchBytesAt (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d20)
      0x67#8 0x80#8 0x00#8 0x00#8 :=
    fetchBytesAt_10d20 (tryStepControlFlowAfterIncrement s1) image hInv.himageEq
      (hmem1.symm ▸ hInv.hmatches)
  have hplat1 : StepPlatform s1 (BitVec.ofNat 64 0x10d20) 0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits :=
    mkStepPlatform s1 mseccfgBits (BitVec.ofNat 64 0x10d20) 0x67#8 0x80#8 0x00#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt1 (hsumL4 ▸ hPC1) (by decide) hbytes1
  have hcnt1 : StepCounters s1 (Sail.BitVec.addInt retired0 1) inhibit cfg :=
    ⟨(hSt1 hart_state (by decide)).trans hInv.hhart,
      (hSt1 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt1 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled,
      hmin1⟩
  have hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d20))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d20))
      retAddr :=
    rX_bits_x1_run _ retAddr ((coreGetStable s1 _ x1 (by decide) hSt1).trans hInv.hra)
  obtain ⟨misaBits1, _, _, hmisaA1, _⟩ := hplat1.1
  have hmisa1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10d20)).regs.get? misa = some misaBits1 :=
    (coreGetInc (tryStepControlFlowAfterIncrement s1) _ misa (by decide)).trans hmisaA1
  have hElp1 : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d20))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d20)) () :=
    hInv.hElp _ (coreStableAgree s1 (BitVec.ofNat 64 0x10d20) hSt1)
  have hr := memcpy_step_ret (start + 1) s1 retAddr (Sail.BitVec.addInt retired0 1) mseccfgBits
    misaBits1 inhibit cfg hplat1 hcnt1 hrs1 hretAlign hElp1 hmisa1
  have hSt2 : StableAgree s _ :=
    hSt1.trans (stableAgree_jump s1 (BitVec.ofNat 64 0x10d20)
      (Sail.BitVec.update retAddr 0 0#1) (Sail.BitVec.addInt retired0 1))
  have hmem2 : _ = s.mem :=
    (retiredMem (controlFlowJumpState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d20)
      (Sail.BitVec.update retAddr 0 0#1)) (Sail.BitVec.update retAddr 0 0#1)
      (Sail.BitVec.addInt retired0 1)).trans
      ((jumpMem s1 (BitVec.ofNat 64 0x10d20) (Sail.BitVec.update retAddr 0 0#1)).trans hmem1)
  have htr : Trace start 2 s
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d20)
          (Sail.BitVec.update retAddr 0 0#1))
        (Sail.BitVec.update retAddr 0 0#1) (Sail.BitVec.addInt retired0 1)) :=
    Trace.step _ _ _ _ _ hb (Trace.one _ _ _ hr)
  refine ⟨_, htr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact retiredGetPC _ _ _
  · intro j hj; rw [hmem2]; exact hInv.hcopy j hj
  · exact (hSt2 x10 (by decide)).trans hInv.ha0
  · exact (hSt2 x11 (by decide)).trans hInv.ha1
  · exact (hSt2 x12 (by decide)).trans hInv.ha2
  · exact (hSt2 x1 (by decide)).trans hInv.hra
  · rw [hmem2]; exact hInv.hmatches
  · exact hInv.hstable.trans hSt2
  · intro addr h; rw [hmem2]; exact hInv.hframe addr h

/-! ## Deliverable 5: capstone contract `memcpy_contract` -/

set_option maxHeartbeats 1000000 in
/-- CAPSTONE.  `memcpy(dst, src, n)` at `0x10d18`, run through the authoritative generated `try_step`
from a configured machine with the abstract data-access and non-overlap preconditions: a single
`1 + n*7 + 2`-step trace (entry `li` + loop + exit) to the caller, after which every destination byte
`mem[dst+j]` equals the original source byte `mem[src+j]` (`= srcByte j`), the source region, code
image and argument registers are preserved, and `PC = ra` (bit 0 cleared). -/
theorem memcpy_contract (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (start : Nat) (s : State)
    (hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10d18))
    (ha0 : s.regs.get? x10 = some dst) (ha1 : s.regs.get? x11 = some src)
    (ha2 : s.regs.get? x12 = some n) (hra : s.regs.get? x1 = some retAddr)
    (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmstatus : s.regs.get? mstatus = some mstatusBits) (hmprv : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hhart : s.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hinhibit : s.regs.get? mcountinhibit = some inhibit) (hnotInhibited : _get_Counterin_IR inhibit = 0#1)
    (hcfg : s.regs.get? minstretcfg = some cfg) (hmachineEnabled : _get_CountSmcntrpmf_MINH cfg = 0#1)
    (hminstret : ∃ v, s.regs.get? minstret = some v)
    (himageEq : Artifact.programImage = .ok image) (hmatches : image.matchesMemory s.mem)
    (hsrc : ∀ j : Nat, j < n.toNat → s.mem.get? (src + BitVec.ofNat 64 j).toNat = some (srcByte j))
    (hnLt : n.toNat < 2 ^ 64) (hsrcFits : src.toNat + n.toNat ≤ 2 ^ 64)
    (hdstFits : dst.toNat + n.toNat ≤ 2 ^ 64)
    (hdstImg : ∀ j : Nat, j < n.toNat → image.readByte? (dst + BitVec.ofNat 64 j).toNat = none)
    (hdisj : ∀ j k : Nat, j < n.toNat → k < n.toNat →
      (dst + BitVec.ofNat 64 j).toNat ≠ (src + BitVec.ofNat 64 k).toNat)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hplat : AbstractPlatform s) (hdata : AbstractDataAccess n dst src s) (hElp : AbstractElp s) :
    ∃ s'', Trace start (1 + n.toNat * 7 + 2) s s'' ∧
      s''.regs.get? PC = some (Sail.BitVec.update retAddr 0 0#1) ∧
      (∀ j : Nat, j < n.toNat →
        s''.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (srcByte j)) ∧
      s''.regs.get? x10 = some dst ∧ s''.regs.get? x11 = some src ∧
      s''.regs.get? x12 = some n ∧ s''.regs.get? x1 = some retAddr ∧
      image.matchesMemory s''.mem ∧
      -- Compositional framing (Deliverables 1–4):
      -- every register outside `W` is preserved (in particular `x2`/`sp`, a leaf function),
      StableAgree s s'' ∧ s''.regs.get? x2 = s.regs.get? x2 ∧
      -- memory changes only inside the destination window `[dst, dst+n)`,
      MemFramed dst n s s'' ∧
      -- and the source region is preserved (from the frame plus the non-overlap premise).
      (∀ k : Nat, k < n.toNat →
        s''.mem.get? (src + BitVec.ofNat 64 k).toNat = s.mem.get? (src + BitVec.ofNat 64 k).toNat) := by
  obtain ⟨retired0, hret0⟩ := hminstret
  -- Entry: li a5, 0 at 0x10d18.
  have hbytesE : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d18)
      0x93#8 0x07#8 0x00#8 0x00#8 :=
    fetchBytesAt_10d18 (tryStepControlFlowAfterIncrement s) image himageEq hmatches
  have hplatE : StepPlatform s (BitVec.ofNat 64 0x10d18) 0x93#8 0x07#8 0x00#8 0x00#8 mseccfgBits :=
    mkStepPlatform s mseccfgBits (BitVec.ofNat 64 0x10d18) 0x93#8 0x07#8 0x00#8 0x00#8
      hplat hcur hmseccfg (StableAgree.refl s)
      ((afterIncGet s PC (by decide)).trans hPC) (Or.inl rfl) hbytesE
  have hcntE : StepCounters s retired0 inhibit cfg :=
    ⟨hhart, hinhibit, hcfg, hnotInhibited, hmachineEnabled, hret0⟩
  have hli := memcpy_step_li start s retired0 mseccfgBits inhibit cfg hplatE hcntE
  have hSt0 : StableAgree s _ :=
    stableAgree_fallThrough s (BitVec.ofNat 64 0x10d18) retired0 x15 (BitVec.ofNat 64 0)
      (Or.inr (Or.inr rfl))
  have hsum18 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d18) 4 = BitVec.ofNat 64 0x10d1c := by decide
  -- The i = 0 loop-head invariant at the post-entry state.
  have hInv0 : MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte s 0
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d18) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
            (BitVec.ofNat 64 0x10d18)).regs.insert x15 (BitVec.ofNat 64 0) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d18) 4) retired0) := by
    refine ⟨?_, ?_, (hSt0 x10 (by decide)).trans ha0, (hSt0 x11 (by decide)).trans ha1,
      (hSt0 x12 (by decide)).trans ha2, (hSt0 x1 (by decide)).trans hra,
      (hSt0 cur_privilege (by decide)).trans hcur, (hSt0 mstatus (by decide)).trans hmstatus, hmprv,
      (hSt0 mseccfg (by decide)).trans hmseccfg, (hSt0 hart_state (by decide)).trans hhart,
      (hSt0 mcountinhibit (by decide)).trans hinhibit, hnotInhibited,
      (hSt0 minstretcfg (by decide)).trans hcfg, hmachineEnabled, ⟨_, retiredMinstret _ _ _⟩,
      himageEq, ?_, ?_, ?_, Nat.zero_le _, hnLt, hsrcFits, hdstFits, hdstImg, hdisj,
      AbstractPlatform.mono hSt0 hplat, AbstractDataAccess.mono hSt0 hdata, AbstractElp.mono hSt0 hElp,
      hSt0, ?_⟩
    · rw [retiredGetPC _ _ _, hsum18]
    · exact (fallThroughRetiredRd s (BitVec.ofNat 64 0x10d18) retired0 x15 (BitVec.ofNat 64 0)
        (by decide) (by decide))
    · have hmemE : (tryStepControlFlowAfterRetired
          { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d18) with
            regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
              (BitVec.ofNat 64 0x10d18)).regs.insert x15 (BitVec.ofNat 64 0) }
          (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d18) 4) retired0).mem = s.mem :=
        (retiredMem _ _ _).trans (fallThroughMem s (BitVec.ofNat 64 0x10d18) x15 (BitVec.ofNat 64 0))
      rw [hmemE]; exact hmatches
    · intro j hj
      have hmemE : (tryStepControlFlowAfterRetired
          { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d18) with
            regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
              (BitVec.ofNat 64 0x10d18)).regs.insert x15 (BitVec.ofNat 64 0) }
          (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d18) 4) retired0).mem = s.mem :=
        (retiredMem _ _ _).trans (fallThroughMem s (BitVec.ofNat 64 0x10d18) x15 (BitVec.ofNat 64 0))
      rw [hmemE]; exact hsrc j hj
    · intro j hj; exact absurd hj (Nat.not_lt_zero j)
    · intro addr _
      have hmemE : (tryStepControlFlowAfterRetired
          { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d18) with
            regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
              (BitVec.ofNat 64 0x10d18)).regs.insert x15 (BitVec.ofNat 64 0) }
          (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d18) 4) retired0).mem = s.mem :=
        (retiredMem _ _ _).trans (fallThroughMem s (BitVec.ofNat 64 0x10d18) x15 (BitVec.ofNat 64 0))
      rw [hmemE]
  -- Loop.
  obtain ⟨sN, htrLoop, hInvN⟩ := memcpy_loop dst src n retAddr image mseccfgBits mstatusBits inhibit
    cfg srcByte s (start + 1) _ hInv0
  -- Exit.
  obtain ⟨s'', htrExit, hPCret, hcopyN, hx10, hx11, hx12, hx1N, hmatchesN, hStableExit, hFrameExit⟩ :=
    memcpy_exit dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte s
      (start + (1 + n.toNat * 7)) sN hretAlign hInvN
  refine ⟨s'', ?_, hPCret, hcopyN, hx10, hx11, hx12, hx1N, hmatchesN,
    hStableExit, hStableExit x2 (by decide), hFrameExit,
    fun k hk => MemFramed.source_preserved hFrameExit hdisj k hk⟩
  have htrLi := Trace.one _ _ _ hli
  have hcomb := Trace.append (Trace.append htrLi htrLoop) htrExit
  simpa using hcomb

end BinaryFv.Keccak
