import BinaryFv.Zesu.Artifacts.Image
import BinaryFv.Zesu.Contracts.Runtime
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.RiscV.Step.AbstractPremise
import BinaryFv.RiscV.Step.Context
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.RiscV.Logic.MemFrame
import BinaryFv.RiscV.Logic.LoopInduction
import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Instruction.Execute.Load
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Proof.ImageFetch

/-!
# The `memcpy` (0x13eb8) byte-copy loop, proved through the authoritative generated `try_step`

Stage 4 lifts the per-instruction `try_step` packagings (stage 3: control flow; `FallThrough` /
`GenericStep`: straight-line body) into a whole-loop contract for the leaf byte-copy helper
`memcpy` at `0x13eb8`:

```
0x13ebc bne a5,a2,0x13ec4   ; taken while i≠n           (loop head L)
0x13ec0 ret                 ; when i==n
0x13ec4 add a3,a1,a5        ; a3 = src+i
0x13ec8 lbu a3,0(a3)        ; a3 = mem[src+i]
0x13ecc add a4,a0,a5        ; a4 = dst+i
0x13ed0 addi a5,a5,1        ; i++
0x13ed4 sb a3,0(a4)         ; mem[dst+i] = a3
0x13ed8 j 0x13ebc           ; back to L
```

The genuine platform/data-access preconditions (the load/store effective-address resolution, the
`phys_access_check`, MMIO decisions, and byte ownership) are carried *abstractly* in the loop
invariant, exactly the trust boundary established by the stage-2 store (`StoreStepTriple`): they are
hypotheses about a configured machine, never discharged here, so the final axiom footprint is the
XOR/fetch baseline.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.Binary

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open BinaryFv.RiscV.Elfling
open BinaryFv.Binary.ProgramImage
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Foundational register-write facts -/

/-- Writing `a3 = x13`, `a4 = x14`, `a5 = x15` via `wX_bits` inserts `xk ↦ data` and touches nothing
else (the `xreg_write_callback` is a no-op).  These are the `Step/Call.lean` `wX_bits_run_xk` family
continued for the three registers this loop writes; the shared reduction lives in
`xreg_write_callback_run`. -/
theorem wX_bits_x13_run (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 13#5) data) s { s with regs := s.regs.insert x13 data } () := by
  have hidx : (Sail.BitVec.toNatInt (13#5)).toNat = 13 := rfl
  unfold Runs
  simp only [wX_bits, wX, hidx, regval_into_reg, PreSail.writeReg, EStateM.run,
    EStateM.bind, EStateM.modifyGet, EStateM.instMonad, MonadState.modifyGet,
    MonadStateOf.modifyGet, modify]
  rw [if_pos (by decide)]
  exact xreg_write_callback_run _ _ _

theorem wX_bits_x14_run (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 14#5) data) s { s with regs := s.regs.insert x14 data } () := by
  have hidx : (Sail.BitVec.toNatInt (14#5)).toNat = 14 := rfl
  unfold Runs
  simp only [wX_bits, wX, hidx, regval_into_reg, PreSail.writeReg, EStateM.run,
    EStateM.bind, EStateM.modifyGet, EStateM.instMonad, MonadState.modifyGet,
    MonadStateOf.modifyGet, modify]
  rw [if_pos (by decide)]
  exact xreg_write_callback_run _ _ _

theorem wX_bits_x15_run (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 15#5) data) s { s with regs := s.regs.insert x15 data } () := by
  have hidx : (Sail.BitVec.toNatInt (15#5)).toNat = 15 := rfl
  unfold Runs
  simp only [wX_bits, wX, hidx, regval_into_reg, PreSail.writeReg, EStateM.run,
    EStateM.bind, EStateM.modifyGet, EStateM.instMonad, MonadState.modifyGet,
    MonadStateOf.modifyGet, modify]
  rw [if_pos (by decide)]
  exact xreg_write_callback_run _ _ _

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

/-! ## Current Zesu image facts -/

private theorem memcpy_fetch (state : State) (image : ProgramImage) (address : Nat)
    (byte0 byte1 byte2 byte3 : UInt8) (imageEq : image = Artifacts.programImage)
    (loaded : image.fileBytesMatchMemory state.mem)
    (addressFits : address < 2 ^ 64 := by decide)
    (read0 : Artifacts.programImage.readFileByte? address = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (address + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (address + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (address + 3) = some byte3 := by native_decide) :
    FetchBytesAt state (BitVec.ofNat 64 address)
      (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
      (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) := by
  exact fetchBytesAt_of_file_bytes image state address addressFits loaded
    byte0 byte1 byte2 byte3 (by simpa [imageEq] using read0)
    (by simpa [imageEq] using read1) (by simpa [imageEq] using read2)
    (by simpa [imageEq] using read3)

private theorem fetchBytesAt_13eb8 (state : State) (image : ProgramImage)
    (imageEq : image = Artifacts.programImage) (loaded : image.fileBytesMatchMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x13eb8) 0x93#8 0x07#8 0x00#8 0x00#8 :=
  memcpy_fetch state image 0x13eb8 0x93 0x07 0x00 0x00 imageEq loaded

private theorem fetchBytesAt_13ebc (state : State) (image : ProgramImage)
    (imageEq : image = Artifacts.programImage) (loaded : image.fileBytesMatchMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x13ebc) 0x63#8 0x94#8 0xc7#8 0x00#8 :=
  memcpy_fetch state image 0x13ebc 0x63 0x94 0xc7 0x00 imageEq loaded

private theorem fetchBytesAt_13ec0 (state : State) (image : ProgramImage)
    (imageEq : image = Artifacts.programImage) (loaded : image.fileBytesMatchMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x13ec0) 0x67#8 0x80#8 0x00#8 0x00#8 :=
  memcpy_fetch state image 0x13ec0 0x67 0x80 0x00 0x00 imageEq loaded

private theorem fetchBytesAt_13ec4 (state : State) (image : ProgramImage)
    (imageEq : image = Artifacts.programImage) (loaded : image.fileBytesMatchMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x13ec4) 0xb3#8 0x86#8 0xf5#8 0x00#8 :=
  memcpy_fetch state image 0x13ec4 0xb3 0x86 0xf5 0x00 imageEq loaded

private theorem fetchBytesAt_13ec8 (state : State) (image : ProgramImage)
    (imageEq : image = Artifacts.programImage) (loaded : image.fileBytesMatchMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x13ec8) 0x83#8 0xc6#8 0x06#8 0x00#8 :=
  memcpy_fetch state image 0x13ec8 0x83 0xc6 0x06 0x00 imageEq loaded

private theorem fetchBytesAt_13ecc (state : State) (image : ProgramImage)
    (imageEq : image = Artifacts.programImage) (loaded : image.fileBytesMatchMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x13ecc) 0x33#8 0x07#8 0xf5#8 0x00#8 :=
  memcpy_fetch state image 0x13ecc 0x33 0x07 0xf5 0x00 imageEq loaded

private theorem fetchBytesAt_13ed0 (state : State) (image : ProgramImage)
    (imageEq : image = Artifacts.programImage) (loaded : image.fileBytesMatchMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x13ed0) 0x93#8 0x87#8 0x17#8 0x00#8 :=
  memcpy_fetch state image 0x13ed0 0x93 0x87 0x17 0x00 imageEq loaded

private theorem fetchBytesAt_13ed4 (state : State) (image : ProgramImage)
    (imageEq : image = Artifacts.programImage) (loaded : image.fileBytesMatchMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x13ed4) 0x23#8 0x00#8 0xd7#8 0x00#8 :=
  memcpy_fetch state image 0x13ed4 0x23 0x00 0xd7 0x00 imageEq loaded

private theorem fetchBytesAt_13ed8 (state : State) (image : ProgramImage)
    (imageEq : image = Artifacts.programImage) (loaded : image.fileBytesMatchMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x13ed8) 0x6f#8 0xf0#8 0x5f#8 0xfe#8 :=
  memcpy_fetch state image 0x13ed8 0x6f 0xf0 0x5f 0xfe imageEq loaded

/-! ## Shared platform / counter bundles

The genuine platform preconditions (`FetchBasePlatform`, MMIO decision, interrupt exclusion,
landing-pad, decode CSRs) about the post-increment fetch state, and the retirement counter reads
about the pre-step state, are bundled once so each body-instruction step lemma consumes them
uniformly.  They are exactly the abstract configured-machine facts carried by the stage-2 store. -/

/-! ## Step 1: `bne a5, a2, 0x13ec4` at the loop head `L = 0x13ebc` (taken while `i ≠ n`) -/

/-- The loop-head conditional branch, taken (`a5 = i ≠ n = a2`), lifted through the generated
`try_step`.  Fetch bytes at `0x13ebc` are `63 94 c7 00` (`00c79463 = bne a5,a2,+8`); the target is
`pc + 8 = 0x13ec4`.  Post-state: `PC = nextPC = pcVal + 8`, `minstret = retired+1`. -/
theorem memcpy_step_bne_taken (stepNo : Nat) (state : State)
    (pcVal a2v retired : BitVec 64) (mseccfgBits : BitVec 64) (inhibit : BitVec 32)
    (config : BitVec 64) (i : Nat)
    (plat : StepPlatform state (BitVec.ofNat 64 0x13ebc) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ebc)).regs.get? x15 = some (BitVec.ofNat 64 i))
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ebc)).regs.get? x12 = some a2v)
    (hneq : BitVec.ofNat 64 i ≠ a2v)
    (hpcRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ebc)).regs.get? PC = some pcVal)
    (misaBits : BitVec 64)
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ebc)).regs.get? misa = some misaBits)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) (8#13)) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) (8#13)) 1 = 0#1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13ebc) (pcVal + sign_extend (m := 64) (8#13)))
        (pcVal + sign_extend (m := 64) (8#13)) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8 = (0x00c79463 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (8#13, .Regidx 12#5, .Regidx 15#5, .BNE)) := by
    rw [wordEq]; decode_run
  have hcondEq : (BitVec.ofNat 64 i != a2v) = true := by
    rw [bne_iff_ne]; exact hneq
  have hcond : Runs (bTypeTaken (.Regidx 12#5) (.Regidx 15#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ebc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ebc))
      true := by
    have := bTypeTaken_bne_run _ (BitVec.ofNat 64 i) a2v h15 h12
    rwa [hcondEq] at this
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ebc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ebc))
      pcVal :=
    readReg_run _ PC pcVal hpcRead
  have hzca := currentlyEnabledZca_run _ misaBits hmisa
  exact tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x13ebc) pcVal retired
    (8#13) (.Regidx 12#5) (.Regidx 15#5) .BNE inhibit config 0x63#8 0x94#8 0xc7#8 0x00#8
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected
    hcond hpc halign hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead

/-! ## Fall-through framing helper

A fall-through body instruction retires with `nextPC` still at `pc + 4`.  The four bookkeeping
premises this induces for a GP-writing instruction are derived upstream by
`tryStepFallThroughWriteRegRetires` from the destination's four disequalities, so only the read that
bridges *into* the execute state is needed here. -/

/-- Bridge a register read from the pre-step state through the counter-increment and `nextPC` writes
to the execute state `coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc`. -/
theorem xGet (state : State) (pc : BitVec 64) (r : Register)
    (hnp : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? r =
      state.regs.get? r :=
  ((coreControlFlowNextState_writes _ pc).get r hnp).trans
    ((tryStepControlFlowAfterIncrement_writes state).get r hmi)

/-! ## Step 2: `add a3, a1, a5` at `0x13ec4` (`a3 = src + i`) -/

/-- The `add a3, a1, a5` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x13ec4` are `b3 86 f5 00` (`00f586b3`); the destination write is `x13 ↦ srcVal + a5Val`. -/
theorem memcpy_step_add_a3 (stepNo : Nat) (state : State)
    (srcVal a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x13ec4) 0xb3#8 0x86#8 0xf5#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ec4)).regs.get? x11 = some srcVal)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ec4)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x13ec4) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x13ec4)).regs.insert x13 (srcVal + a5Val) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ec4) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0xb3#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0xb3#8 0x86#8 0xf5#8 0x00#8 = (0x00f586b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x86#8 0xf5#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 11#5, .Regidx 13#5, .ADD)) := by
    rw [wordEq]; decode_run
  have exec : Runs (execute (.RTYPE (.Regidx 15#5, .Regidx 11#5, .Regidx 13#5, .ADD)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec4))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13ec4) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13ec4)).regs.insert x13 (srcVal + a5Val) }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 15#5) (.Regidx 11#5) (.Regidx 13#5) .ADD) _ _ _
    exact execute_RTYPE_run _ _ _ _ _ .ADD srcVal a5Val (rX_bits_run_x11 _ _ h11)
      (rX_bits_x15_run _ _ h15) (wX_bits_x13_run _ _)
  exact tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x13ec4) retired inhibit
    config 0xb3#8 0x86#8 0xf5#8 0x00#8 (.RTYPE (.Regidx 15#5, .Regidx 11#5, .Regidx 13#5, .ADD))
    x13 _ platform noMMIO bytes interrupts base decode notExpected exec
    (by decide) (by decide) (by decide) (by decide)
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 4: `add a4, a0, a5` at `0x13ecc` (`a4 = dst + i`) -/

/-- The `add a4, a0, a5` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x13ecc` are `33 07 f5 00` (`00f50733`); the destination write is `x14 ↦ dstVal + a5Val`. -/
theorem memcpy_step_add_a4 (stepNo : Nat) (state : State)
    (dstVal a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x13ecc) 0x33#8 0x07#8 0xf5#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h10 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ecc)).regs.get? x10 = some dstVal)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ecc)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x13ecc) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x13ecc)).regs.insert x14 (dstVal + a5Val) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ecc) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x33#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x33#8 0x07#8 0xf5#8 0x00#8 = (0x00f50733 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x07#8 0xf5#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)) := by
    rw [wordEq]; decode_run
  have exec : Runs (execute (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ecc))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13ecc) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13ecc)).regs.insert x14 (dstVal + a5Val) }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 15#5) (.Regidx 10#5) (.Regidx 14#5) .ADD) _ _ _
    exact execute_RTYPE_run _ _ _ _ _ .ADD dstVal a5Val (rX_bits_run_x10 _ _ h10)
      (rX_bits_x15_run _ _ h15) (wX_bits_x14_run _ _)
  exact tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x13ecc) retired inhibit
    config 0x33#8 0x07#8 0xf5#8 0x00#8 (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD))
    x14 _ platform noMMIO bytes interrupts base decode notExpected exec
    (by decide) (by decide) (by decide) (by decide)
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 5: `addi a5, a5, 1` at `0x13ed0` (`i++`) -/

/-- The `addi a5, a5, 1` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x13ed0` are `93 87 17 00` (`00178793`); the destination write is `x15 ↦ a5Val + sext 1`. -/
theorem memcpy_step_addi_a5 (stepNo : Nat) (state : State)
    (a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x13ed0) 0x93#8 0x87#8 0x17#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ed0)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x13ed0) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x13ed0)).regs.insert x15 (a5Val + sign_extend (m := 64) 1#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ed0) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x87#8 0x17#8 0x00#8 = (0x00178793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x87#8 0x17#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)) := by
    rw [wordEq]; decode_run
  have exec : Runs (execute (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed0))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13ed0) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13ed0)).regs.insert x15 (a5Val + sign_extend (m := 64) 1#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 1#12 (.Regidx 15#5) (.Regidx 15#5) .ADDI) _ _ _
    exact execute_ITYPE_run _ _ _ _ _ .ADDI a5Val (rX_bits_x15_run _ _ h15)
      (wX_bits_x15_run _ _)
  exact tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x13ed0) retired inhibit
    config 0x93#8 0x87#8 0x17#8 0x00#8 (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI))
    x15 _ platform noMMIO bytes interrupts base decode notExpected exec
    (by decide) (by decide) (by decide) (by decide)
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 7: `j 0x13ebc` at `0x13ed8` (unconditional back-edge) -/

/-- `nextPC` slot of `coreControlFlowNextState Y pc` is `pc + 4`. -/
private theorem coreNextPc (Y : State) (pc : BitVec 64) :
    (coreControlFlowNextState Y pc).regs.get? nextPC = some (Sail.BitVec.addInt pc 4) := by
  change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- Any register other than `nextPC` reads through `coreControlFlowNextState Y pc` back to `Y`. -/
private theorem coreGetInc (Y : State) (pc : BitVec 64) (r : Register) (hnp : r ≠ nextPC) :
    (coreControlFlowNextState Y pc).regs.get? r = Y.regs.get? r :=
  (coreControlFlowNextState_writes Y pc).get r hnp

/-- The `j 0x13ebc` back-edge (`JAL imm x0`, `imm` byte-offset `-28`), lifted through the generated
`try_step`.  Fetch bytes at `0x13ed8` are `6f f0 5f fe` (`fe5ff06f`); the jump target is
`pc + sext imm = 0x13ebc`. -/
theorem memcpy_step_j (stepNo : Nat) (state : State)
    (retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x13ed8) 0x6f#8 0xf0#8 0x5f#8 0xfe#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13ed8)
          (BitVec.ofNat 64 0x13ed8 + sign_extend (m := 64) (0x1FFFE4#21)))
        (BitVec.ofNat 64 0x13ed8 + sign_extend (m := 64) (0x1FFFE4#21)) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  obtain ⟨misaBits, _, pcRead, misaRead, _⟩ := id platform
  have base : BaseInstructionEncoding 0x6f#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x6f#8 0xf0#8 0x5f#8 0xfe#8 = (0xfe5ff06f : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x6f#8 0xf0#8 0x5f#8 0xfe#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1FFFE4#21, zreg)) := by
    rw [wordEq]; decode_run
  have hPCx : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ed8)).regs.get? PC = some (BitVec.ofNat 64 0x13ed8) := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC PC
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ed8) 4) (by decide)).trans pcRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed8))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ed8) 4) := by
    unfold get_next_pc
    exact readReg_run _ nextPC _ (coreNextPc _ _)
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed8))
      (BitVec.ofNat 64 0x13ed8) :=
    readReg_run _ PC _ hPCx
  have hmisax : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ed8)).regs.get? misa = some misaBits := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC misa
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ed8) 4) (by decide)).trans misaRead
  have hzca := currentlyEnabledZca_run _ misaBits hmisax
  have hsum : (BitVec.ofNat 64 0x13ed8 + sign_extend (m := 64) (0x1FFFE4#21))
      = BitVec.ofNat 64 0x13ebc := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have halign : Sail.BitVec.access
      (BitVec.ofNat 64 0x13ed8 + sign_extend (m := 64) (0x1FFFE4#21)) 0 = 0#1 := by
    rw [hsum]; decide
  have hbit1 : Sail.BitVec.access
      (BitVec.ofNat 64 0x13ed8 + sign_extend (m := 64) (0x1FFFE4#21)) 1 = 0#1 := by
    rw [hsum]; decide
  exact tryStepJRetires stepNo state (BitVec.ofNat 64 0x13ed8) (BitVec.ofNat 64 0x13ed8) retired
    (0x1FFFE4#21) inhibit config 0x6f#8 0xf0#8 0x5f#8 0xfe#8
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ed8) 4) (_get_Misa_C misaBits == 1#1) platform
    noMMIO bytes interrupts base decode notExpected hlink hpc halign hbit1 hzca
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 3: `lbu a3, 0(a3)` at `0x13ec8` (`a3 = mem[src + i]`)

The genuine load data-access preconditions — the effective-address resolution to `src + i`, the byte
alignment (trivial), `phys_access_check` yielding no fault, the no-MMIO decision, and byte ownership
of `mem[src+i] = v` — are carried abstractly, exactly the stage-2 trust boundary. -/

/-- The `lbu a3, 0(a3)` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x13ec8` are `83 c6 06 00` (`0006c683`); the destination write is `x13 ↦ zext₆₄ v` where `v` is the
owned source byte at `srcAddrBits` (`= src + i`). -/
theorem memcpy_step_lbu (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x13ec8) 0x83#8 0xc6#8 0x06#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ec8)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ec8)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 13#5) (sign_extend (m := 64) 0#12)
      (Load Data) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec8))
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcAddrBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec8))
      none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec8))
      false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x13ec8)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x13ec8) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x13ec8)).regs.insert x13 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ec8) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x83#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x83#8 0xc6#8 0x06#8 0x00#8 = (0x0006c683 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc6#8 0x06#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0#12, .Regidx 13#5, .Regidx 13#5, true, 1)) := by
    rw [wordEq]; decode_run
  have exec : Runs (execute (.LOAD (0#12, .Regidx 13#5, .Regidx 13#5, true, 1)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec8))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13ec8) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13ec8)).regs.insert x13 (zero_extend (m := 64) v) }
      (.Retire_Success ()) := by
    change Runs (execute_LOAD 0#12 (.Regidx 13#5) (.Regidx 13#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 0#12 (.Regidx 13#5) (.Regidx 13#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg aligned physAccess noMMIOr hmem
      (wX_bits_x13_run _ (zero_extend (m := 64) v))
  exact tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x13ec8) retired inhibit
    config 0x83#8 0xc6#8 0x06#8 0x00#8 (.LOAD (0#12, .Regidx 13#5, .Regidx 13#5, true, 1))
    x13 _ platform noMMIO bytes interrupts base decode notExpected exec
    (by decide) (by decide) (by decide) (by decide)
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 6: `sb a3, 0(a4)` at `0x13ed4` (`mem[dst + i] = a3`)

The store data/address preconditions — the effective address resolving to `dst + i`, the byte
`phys_access_check`, no-MMIO, and the physical `writeBytes` — are carried abstractly (stage-2 trust
boundary).  The store's post-write state `s'` is opaque; `writeBytes_preserves_regs` recovers the
register frame. -/

/-- The `sb a3, 0(a4)` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x13ed4` are `23 00 d7 00` (`00d70023`); the low byte of `a3 = dataBits` is written to
`dstAddrBits = dst + i`, yielding the opaque post-write state `s'`. -/
theorem memcpy_step_sb (stepNo : Nat) (state s' : State)
    (dstAddrBits mstatusBits retired mseccfgBits : BitVec 64) (dataBits : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x13ed4) 0x23#8 0x00#8 0xd7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ed4)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ed4)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hx13 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ed4)).regs.get? x13 = some (BitVec.setWidth 64 dataBits))
    (addrReg : Runs (get_transformed_data_addr (.Regidx 14#5) (sign_extend (m := 64) 0#12)
      (Store Data) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed4))
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstAddrBits)))
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstAddrBits) 1 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed4))
      none)
    (noMMIOw : Runs (within_mmio_writable (physaddr.Physaddr dstAddrBits) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed4))
      false)
    (hwrite : Runs (PreSail.writeBytes dstAddrBits.toNat dataBits)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed4))
      s' true) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ed4) 4) retired)
      false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x23#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x23#8 0x00#8 0xd7#8 0x00#8 = (0x00d70023 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x23#8 0x00#8 0xd7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (0#12, .Regidx 13#5, .Regidx 14#5, 1)) := by
    rw [wordEq]; decode_run
  have exec : Runs (execute (.STORE (0#12, .Regidx 13#5, .Regidx 14#5, 1)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ed4))
      s' (.Retire_Success ()) := by
    change Runs (execute_STORE 0#12 (.Regidx 13#5) (.Regidx 14#5) 1) _ _ _
    exact execute_STORE_byte_run _ s' (.Regidx 13#5) (.Regidx 14#5) 0#12 dstAddrBits mstatusBits
      (BitVec.setWidth 64 dataBits) mstatusReadX privReadX mprvZero
      (rX_bits_x13_run _ _ hx13) addrReg physAccess noMMIOw (by
        have lowByte : Sail.BitVec.extractLsb (BitVec.setWidth 64 dataBits) 7 0 = dataBits := by
          unfold Sail.BitVec.extractLsb
          bv_decide
        simpa [lowByte] using hwrite)
  have regsEq : s'.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x13ed4)).regs :=
    writeBytes_preserves_regs dstAddrBits.toNat dataBits _ s' hwrite
  refine tryStepFallThroughRetires stepNo state s' (BitVec.ofNat 64 0x13ed4) retired inhibit config
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
def StableAgree (base t : State) : Prop := Agree NonW base t

/-- The instruction fetch addresses of the memcpy function (entry, loop head, ret, and body). -/
@[reducible] def IsBodyPc (pc : BitVec 64) : Prop :=
  pc = BitVec.ofNat 64 0x13eb8 ∨ pc = BitVec.ofNat 64 0x13ebc ∨ pc = BitVec.ofNat 64 0x13ec0 ∨
  pc = BitVec.ofNat 64 0x13ec4 ∨ pc = BitVec.ofNat 64 0x13ec8 ∨ pc = BitVec.ofNat 64 0x13ecc ∨
  pc = BitVec.ofNat 64 0x13ed0 ∨ pc = BitVec.ofNat 64 0x13ed4 ∨ pc = BitVec.ofNat 64 0x13ed8

/-- Abstract configured-machine fetch/decode platform: for any state agreeing with `base` off `W`
positioned at a memcpy fetch address, the generated base-fetch path is enabled.  Never discharged
here (the stage-2 trust boundary); satisfiable because it holds of the actual configured machine at
these aligned, executable code addresses. -/
def AbstractPlatform (base : State) : Prop :=
  BinaryFv.RiscV.AbstractPlatform NonW IsBodyPc base

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
  BinaryFv.RiscV.AbstractPlatform.mono h hp

/-- The abstract data access survives to a `StableAgree`-equal state. -/
theorem AbstractDataAccess.mono {n dst src : BitVec 64} {s s' : State} (h : StableAgree s s')
    (hd : AbstractDataAccess n dst src s) : AbstractDataAccess n dst src s' :=
  fun j t hj hst => hd j t hj (fun r hr => (hst r hr).trans (h r hr))

/-- Abstract Zicfilp landing-pad update for the leaf `ret` (`jalr x0, 0(ra)`): a no-op on the
configured machine (Zicfilp expects no landing pad here).  Never discharged here (stage-2 trust
boundary). -/
def AbstractElp (base : State) : Prop :=
  BinaryFv.RiscV.AbstractElp NonW (fun r => r = .Regidx 1#5) base

/-- The abstract Zicfilp update survives to a `StableAgree`-equal state. -/
theorem AbstractElp.mono {s s' : State} (h : StableAgree s s') (he : AbstractElp s) :
    AbstractElp s' :=
  BinaryFv.RiscV.AbstractElp.mono h he

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

/-- The memcpy loop invariant at the loop head `L = 0x13ebc` about to run iteration `i`.  `sInit` is
the fixed reference state (the caller's entry state) against which the compositional framing —
`hstable` (registers) and `hframe` (memory) — is tracked. -/
structure MemcpyInv (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (sInit : State) (i : Nat) (s : State) : Prop where
  hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x13ebc)
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
  himageEq : image = Artifacts.programImage
  hmatches : image.fileBytesMatchMemory s.mem
  hsrc : ∀ j : Nat, j < n.toNat → s.mem.get? (src + BitVec.ofNat 64 j).toNat = some (srcByte j)
  hcopy : ∀ j : Nat, j < i → s.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (srcByte j)
  hle : i ≤ n.toNat
  hnLt : n.toNat < 2 ^ 64
  hsrcFits : src.toNat + n.toNat ≤ 2 ^ 64
  hdstFits : dst.toNat + n.toNat ≤ 2 ^ 64
  hdstImg : ∀ j : Nat, j < n.toNat → image.readFileByte? (dst + BitVec.ofNat 64 j).toNat = none
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

/-- No register outside the loop's write set is one the `try_step` bookkeeping writes. -/
theorem nonW_disjoint_bookkeeping : RegSet.Disjoint NonW stepBookkeeping :=
  fun _ hr h => h.elim hr.1 fun h => h.elim hr.2.1 fun h => h.elim hr.2.2.1 hr.2.2.2.1

/-- ... nor is it the destination of a body instruction, which is one of `a3`, `a4`, `a5`. -/
theorem nonW_disjoint (rd : Register) (hrdW : rd = x13 ∨ rd = x14 ∨ rd = x15) :
    RegSet.Disjoint NonW (RegSet.union stepBookkeeping (RegSet.only rd)) :=
  nonW_disjoint_bookkeeping.union
    (RegSet.Disjoint.only (by rcases hrdW with rfl | rfl | rfl <;> simp [NonW]))

/-- The write set of a byte-store retirement, whose post-write state is known only through its
register file: a store writes memory, so on the register side it writes exactly the bookkeeping. -/
theorem sbRetirement_writes (base s' : State) (pc ret : BitVec 64)
    (regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs) :
    WritesOnlyRegs stepBookkeeping base
      (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) ret) :=
  ((stepPremiseState_writes base pc).congr_regs regsEq).trans_same
    ((tryStepControlFlowAfterRetired_writes s' _ ret).mono
      (fun _ h => h.elim Or.inl (fun h => Or.inr (Or.inr (Or.inl h)))))

/-- The counter-increment write reads through to the base for any register other than
`minstret_increment`. -/
theorem afterIncGet (base : State) (r : Register) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterIncrement base).regs.get? r = base.regs.get? r :=
  (tryStepControlFlowAfterIncrement_writes base).get r hmi

/-- The `try_step` retirement postlude (`minstret`, `PC` writes) reads through for any register
other than those two. -/
theorem retiredFrameGet (afterExec : State) (tPC ret : BitVec 64) (r : Register)
    (hPC : r ≠ PC) (hmr : r ≠ minstret) :
    (tryStepControlFlowAfterRetired afterExec tPC ret).regs.get? r = afterExec.regs.get? r :=
  (tryStepControlFlowAfterRetired_writes afterExec tPC ret).get r (fun h => h.elim hPC hmr)

/-- The `nextPC`-overwrite of a jump reads through for any register other than `nextPC`. -/
theorem jumpFrameGet (base : State) (pc tgt : BitVec 64) (r : Register) (hnpc : r ≠ nextPC)
    (hmi : r ≠ minstret_increment) :
    (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt).regs.get? r =
      base.regs.get? r :=
  ((controlFlowJumpState_writes _ pc tgt).get r hnpc).trans (afterIncGet base r hmi)

/-- A taken-branch / jump `try_step` retirement only writes registers in `W`. -/
theorem stableAgree_jump (base : State) (pc tgt ret : BitVec 64) :
    StableAgree base (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt) tgt ret) :=
  (jumpRetirement_writes base pc tgt ret).agree nonW_disjoint_bookkeeping

/-- A GP-writing fall-through `try_step` retirement only writes registers in `W`
(`rd ∈ {x13, x14, x15}`). -/
theorem stableAgree_fallThrough (base : State) (pc ret : BitVec 64) (rd : Register)
    (v : RegisterType rd) (hrdW : rd = x13 ∨ rd = x14 ∨ rd = x15) :
    StableAgree base (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret) :=
  (RegisterWriteStep.afterRegisterWrite_writes base pc ret rd v).agree (nonW_disjoint rd hrdW)

/-- A memory-writing fall-through (`sb`) retirement leaves the register file as the plain
`coreControlFlowNextState`, hence only writes `W` registers. -/
theorem stableAgree_sb (base s' : State) (pc ret : BitVec 64)
    (regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs) :
    StableAgree base (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) ret) :=
  (sbRetirement_writes base s' pc ret regsEq).agree nonW_disjoint_bookkeeping

/-- The counter-increment write preserves `StableAgree` on the right. -/
theorem StableAgree.afterInc {base t : State} (h : StableAgree base t) :
    StableAgree base (tryStepControlFlowAfterIncrement t) :=
  fun r hr => (afterIncGet t r hr.2.2.2.1).trans (h r hr)

/-- Reading a stable register through the counter-increment and `nextPC` writes of the execute
state, back to a `StableAgree`-equal base. -/
theorem coreGetStable {s : State} (s_k : State) (pc : BitVec 64) (r : Register) (hr : NonW r)
    (hSt : StableAgree s s_k) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s_k) pc).regs.get? r =
      s.regs.get? r :=
  ((stepPremiseState_writes s_k pc).get r (nonW_disjoint_bookkeeping r hr)).trans (hSt r hr)

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
      base.regs.get? r :=
  (jumpRetirement_writes base pc tgt ret).get r
    (fun h => h.elim hPC (fun h => h.elim hnpc (fun h => h.elim hmr hmi)))

/-- Read a register other than the written `rd` untouched by a GP fall-through retirement. -/
theorem fallThroughRetiredGet (base : State) (pc ret : BitVec 64) (rd : Register)
    (v : RegisterType rd) (r : Register) (hPC : r ≠ PC) (hmr : r ≠ minstret) (hrd : r ≠ rd)
    (hnpc : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret).regs.get? r = base.regs.get? r :=
  (RegisterWriteStep.afterRegisterWrite_writes base pc ret rd v).get r
    (fun h => h.elim (fun h => h.elim hPC (fun h => h.elim hnpc (fun h => h.elim hmr hmi))) hrd)

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
    (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) ret).regs.get? r =
      base.regs.get? r :=
  (sbRetirement_writes base s' pc ret regsEq).get r
    (fun h => h.elim hPC (fun h => h.elim hnpc (fun h => h.elim hmr hmi)))

/-- Reading the just-inserted address. -/
theorem getInsertEq (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8) :
    (mem.insert k v).get? k = some v := by
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]; simp

/-- Inserting outside the ELF's file bytes preserves executable code and read-only data. -/
theorem fileBytesMatchMemory_insert (image : ProgramImage)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hm : image.fileBytesMatchMemory mem) (hk : image.readFileByte? k = none) :
    image.fileBytesMatchMemory (mem.insert k v) :=
  image.fileBytesMatchMemory_insert_non_file hk hm

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

/-- **Both premise bundles of a body step, from the invariant.**

Every one of the eleven `try_step`s in this file consumes a `StepPlatform` and a `StepCounters` about
its own pre-step state, and every one rebuilds them from the same five facts: the invariant, the
`StableAgree` reaching that state, its `PC`, its `minstret`, and a concrete fetch. The nine other
components — `hplat`, `hcur`, `hmseccfg` for the platform, `hhart`, `hinhibit`, `hcfg`,
`hnotInhibited`, `hmachineEnabled` for the counters, and the `afterIncGet` bridge from the pre-step
`PC` read to the post-increment one — are invariant fields transported by the same `StableAgree`, so
naming them at each site was pure repetition. -/
theorem mkStepBundles {dst src n retAddr mseccfgBits mstatusBits cfg pc ret : BitVec 64}
    {inhibit : BitVec 32} {image : ProgramImage} {srcByte : Nat → BitVec 8} {sInit s s_k : State}
    {i : Nat} {b0 b1 b2 b3 : BitVec 8}
    (hInv : MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte sInit i s)
    (hSt : StableAgree s s_k) (hPC : s_k.regs.get? PC = some pc) (hbody : IsBodyPc pc)
    (hmin : s_k.regs.get? minstret = some ret)
    (hbytes : FetchBytesAt (tryStepControlFlowAfterIncrement s_k) pc b0 b1 b2 b3) :
    StepPlatform s_k pc b0 b1 b2 b3 mseccfgBits ∧ StepCounters s_k ret inhibit cfg :=
  ⟨mkStepPlatform s_k mseccfgBits pc b0 b1 b2 b3 hInv.hplat hInv.hcur hInv.hmseccfg hSt
      ((afterIncGet s_k PC (by decide)).trans hPC) hbody hbytes,
    (hSt hart_state (by decide)).trans hInv.hhart,
    (hSt mcountinhibit (by decide)).trans hInv.hinhibit,
    (hSt minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin⟩

/-! ### Per-shape step post-conditions

The loop body has three retirement shapes — jump, register-writing fall-through, byte store — and at
every site the same six consequences of a step are needed: the successor state, its write set, the
`StableAgree` that write set induces, its `PC`, its `minstret`, and its memory (plus, for a register
write, the destination's new value). Packaged here once per shape, a step becomes a single `obtain`
whose successor is opaque, which is what the `generalize` blocks used to buy at five lines each.

The write set is the component that pays twice. Handing `WritesOnlyRegs` to the caller puts it in
range of `grind_pattern WritesOnlyRegs.get` (see `BinaryFv/RiscV/Logic/RegisterAgree.lean`), so every
register a step does not write is carried across any number of steps by a bare `grind`, with no
intermediate `have` and no named intermediate state. `retired` is a universal parameter here exactly
as it is in `jumpRetirement_writes`, `afterRegisterWrite_writes` and `storeRetirement_writes`
upstream, so none of this needs it existentially quantified. -/

/-- Everything a taken-branch or jump retirement establishes about its successor. -/
theorem jumpStepPost {stepNo : Nat} {base : State} {pc tgt ret : BitVec 64}
    (hrun : Runs (try_step stepNo false) base
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc tgt) tgt ret) false) :
    ∃ t, Runs (try_step stepNo false) base t false ∧
      WritesOnlyRegs stepBookkeeping base t ∧ StableAgree base t ∧
      t.regs.get? PC = some tgt ∧
      t.regs.get? minstret = some (Sail.BitVec.addInt ret 1) ∧ t.mem = base.mem :=
  let w := jumpRetirement_writes base pc tgt ret
  ⟨_, hrun, w, w.agree nonW_disjoint_bookkeeping, retiredGetPC _ tgt ret, retiredMinstret _ tgt ret,
    (retiredMem _ tgt ret).trans (jumpMem base pc tgt)⟩

/-- Everything a register-writing fall-through retirement establishes about its successor. -/
theorem gpStepPost {stepNo : Nat} {base : State} {pc ret : BitVec 64} {rd : Register}
    {v : RegisterType rd} (hrdW : rd = x13 ∨ rd = x14 ∨ rd = x15)
    (hrun : Runs (try_step stepNo false) base
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
            rd v }
        (Sail.BitVec.addInt pc 4) ret) false) :
    ∃ t, Runs (try_step stepNo false) base t false ∧
      WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only rd)) base t ∧
      StableAgree base t ∧
      t.regs.get? PC = some (Sail.BitVec.addInt pc 4) ∧
      t.regs.get? minstret = some (Sail.BitVec.addInt ret 1) ∧
      t.regs.get? rd = some v ∧ t.mem = base.mem :=
  let w := RegisterWriteStep.afterRegisterWrite_writes base pc ret rd v
  ⟨_, hrun, w, w.agree (nonW_disjoint rd hrdW), retiredGetPC _ _ ret, retiredMinstret _ _ ret,
    fallThroughRetiredRd base pc ret rd v (by rcases hrdW with rfl | rfl | rfl <;> decide)
      (by rcases hrdW with rfl | rfl | rfl <;> decide),
    (retiredMem _ _ ret).trans (fallThroughMem base pc rd v)⟩

/-- Everything a not-taken-branch retirement establishes about its successor: it falls through and
writes no register beyond the bookkeeping, so its write set is `stepBookkeeping` exactly. -/
theorem notTakenStepPost {stepNo : Nat} {base : State} {pc ret : BitVec 64}
    (hrun : Runs (try_step stepNo false) base
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
        (Sail.BitVec.addInt pc 4) ret) false) :
    ∃ t, Runs (try_step stepNo false) base t false ∧
      WritesOnlyRegs stepBookkeeping base t ∧ StableAgree base t ∧
      t.regs.get? PC = some (Sail.BitVec.addInt pc 4) ∧
      t.regs.get? minstret = some (Sail.BitVec.addInt ret 1) ∧ t.mem = base.mem :=
  let w := fallThroughRetirement_writes base pc (Sail.BitVec.addInt pc 4) ret
  ⟨_, hrun, w, w.agree nonW_disjoint_bookkeeping, retiredGetPC _ _ ret, retiredMinstret _ _ ret, rfl⟩

/-- Everything a byte-store retirement establishes about its successor.  The store's post-write state
`s'` is known only through `regsEq` and `memEq`, which is all `writeBytes` delivers. -/
theorem sbStepPost {stepNo : Nat} {base s' : State} {pc ret : BitVec 64}
    {m : Std.ExtHashMap Nat (BitVec 8)}
    (hrun : Runs (try_step stepNo false) base
      (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) ret) false)
    (regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs)
    (memEq : s'.mem = m) :
    ∃ t, Runs (try_step stepNo false) base t false ∧
      WritesOnlyRegs stepBookkeeping base t ∧ StableAgree base t ∧
      t.regs.get? PC = some (Sail.BitVec.addInt pc 4) ∧
      t.regs.get? minstret = some (Sail.BitVec.addInt ret 1) ∧ t.mem = m :=
  let w := sbRetirement_writes base s' pc ret regsEq
  ⟨_, hrun, w, w.agree nonW_disjoint_bookkeeping, retiredGetPC _ _ ret, retiredMinstret _ _ ret,
    (retiredMem s' _ ret).trans memEq⟩

/-! ## Deliverable 2: single-iteration advance `memcpy_adv` -/

/-- The seven concrete Sail steps in one loop iteration, retaining the intermediate PCs needed to
build a confined function trace rather than merely a bare execution trace. -/
def MemcpyIteration (fromStep : Nat) (start final : State) : Prop :=
  ∃ s1 s2 s3 s4 s5 s6,
    start.regs.get? PC = some (BitVec.ofNat 64 0x13ebc) ∧
    s1.regs.get? PC = some (BitVec.ofNat 64 0x13ec4) ∧
    s2.regs.get? PC = some (BitVec.ofNat 64 0x13ec8) ∧
    s3.regs.get? PC = some (BitVec.ofNat 64 0x13ecc) ∧
    s4.regs.get? PC = some (BitVec.ofNat 64 0x13ed0) ∧
    s5.regs.get? PC = some (BitVec.ofNat 64 0x13ed4) ∧
    s6.regs.get? PC = some (BitVec.ofNat 64 0x13ed8) ∧
    Runs (try_step fromStep false) start s1 false ∧
    Runs (try_step (fromStep + 1) false) s1 s2 false ∧
    Runs (try_step (fromStep + 2) false) s2 s3 false ∧
    Runs (try_step (fromStep + 3) false) s3 s4 false ∧
    Runs (try_step (fromStep + 4) false) s4 s5 false ∧
    Runs (try_step (fromStep + 5) false) s5 s6 false ∧
    Runs (try_step (fromStep + 6) false) s6 final false

/-- Prepend one retained iteration to a confined continuation. -/
theorem MemcpyIteration.prepend {fromStep count : Nat} {start final finish : State}
    (iteration : MemcpyIteration fromStep start final)
    (rest : FunctionTrace IsBodyPc (fun pc => pc = BitVec.ofNat 64 0x13ec0)
      (fromStep + 7) count final finish) :
    FunctionTrace IsBodyPc (fun pc => pc = BitVec.ofNat 64 0x13ec0)
      fromStep (count + 7) start finish := by
  rcases iteration with ⟨s1, s2, s3, s4, s5, s6, pc0, pc1, pc2, pc3, pc4, pc5, pc6,
    step0, step1, step2, step3, step4, step5, step6⟩
  have region0 : IsBodyPc (BitVec.ofNat 64 0x13ebc) := by simp [IsBodyPc]
  have region1 : IsBodyPc (BitVec.ofNat 64 0x13ec4) := by simp [IsBodyPc]
  have region2 : IsBodyPc (BitVec.ofNat 64 0x13ec8) := by simp [IsBodyPc]
  have region3 : IsBodyPc (BitVec.ofNat 64 0x13ecc) := by simp [IsBodyPc]
  have region4 : IsBodyPc (BitVec.ofNat 64 0x13ed0) := by simp [IsBodyPc]
  have region5 : IsBodyPc (BitVec.ofNat 64 0x13ed4) := by simp [IsBodyPc]
  have region6 : IsBodyPc (BitVec.ofNat 64 0x13ed8) := by simp [IsBodyPc]
  have notExit0 : BitVec.ofNat 64 0x13ebc ≠ BitVec.ofNat 64 0x13ec0 := by decide
  have notExit1 : BitVec.ofNat 64 0x13ec4 ≠ BitVec.ofNat 64 0x13ec0 := by decide
  have notExit2 : BitVec.ofNat 64 0x13ec8 ≠ BitVec.ofNat 64 0x13ec0 := by decide
  have notExit3 : BitVec.ofNat 64 0x13ecc ≠ BitVec.ofNat 64 0x13ec0 := by decide
  have notExit4 : BitVec.ofNat 64 0x13ed0 ≠ BitVec.ofNat 64 0x13ec0 := by decide
  have notExit5 : BitVec.ofNat 64 0x13ed4 ≠ BitVec.ofNat 64 0x13ec0 := by decide
  have notExit6 : BitVec.ofNat 64 0x13ed8 ≠ BitVec.ofNat 64 0x13ec0 := by decide
  rw [show count + 7 = ((((((count + 1) + 1) + 1) + 1) + 1) + 1) + 1 by omega]
  refine .step fromStep _ _ start s1 finish pc0 region0 notExit0 step0 ?_
  refine .step (fromStep + 1) _ _ s1 s2 finish pc1 region1 notExit1 step1 ?_
  refine .step (fromStep + 2) _ _ s2 s3 finish pc2 region2 notExit2 step2 ?_
  refine .step (fromStep + 3) _ _ s3 s4 finish pc3 region3 notExit3 step3 ?_
  refine .step (fromStep + 4) _ _ s4 s5 finish pc4 region4 notExit4 step4 ?_
  refine .step (fromStep + 5) _ _ s5 s6 finish pc5 region5 notExit5 step5 ?_
  refine .step (fromStep + 6) count _ s6 final finish pc6 region6 notExit6 step6 ?_
  simpa only [Nat.add_assoc] using rest

/-- One loop iteration (`i < n`) is a length-7 trace that copies one more byte and re-establishes the
invariant at `i + 1`. -/
theorem memcpy_adv (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (sInit : State) (start i : Nat) (s : State)
    (hi : i < n.toNat)
    (hInv : MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte sInit i s) :
    ∃ s', Trace (start + i * 7) 7 s s' ∧
      MemcpyIteration (start + i * 7) s s' ∧
      MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte sInit (i + 1) s' := by
  obtain ⟨retired0, hret0⟩ := hInv.hminstret
  have hi2 : i < 2 ^ 64 := Nat.lt_trans hi hInv.hnLt
  have ha5 := hInv.ha5
  -- Step 0: bne a5,a2 (taken, i ≠ n), pc = 0x13ebc.
  obtain ⟨hplat0, hcnt0⟩ := mkStepBundles hInv (StableAgree.refl s) hInv.hPC (Or.inr (Or.inl rfl))
    hret0 (fetchBytesAt_13ebc _ image hInv.himageEq hInv.hmatches)
  have hneq0 : BitVec.ofNat 64 i ≠ n := by
    intro heq
    have h1 : (BitVec.ofNat 64 i).toNat = n.toNat := by rw [heq]
    rw [BitVec.toNat_ofNat] at h1; omega
  obtain ⟨misaBits0, _mstatus0, _pcr0, hmisaAfter0, _rest0⟩ := hplat0.1
  have hsum0 : (BitVec.ofNat 64 0x13ebc + sign_extend (m := 64) (8#13))
      = BitVec.ofNat 64 0x13ec4 := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  obtain ⟨s1, h0, w0, hSt1, hPC1, hmin1, hmem1⟩ :=
    jumpStepPost (memcpy_step_bne_taken (start + i * 7) s (BitVec.ofNat 64 0x13ebc) n retired0
      _ _ _ i hplat0 hcnt0
      ((xGet s (BitVec.ofNat 64 0x13ebc) x15 (by decide) (by decide)).trans ha5)
      ((xGet s (BitVec.ofNat 64 0x13ebc) x12 (by decide) (by decide)).trans hInv.ha2) hneq0
      ((xGet s (BitVec.ofNat 64 0x13ebc) PC (by decide) (by decide)).trans hInv.hPC) misaBits0
      ((coreGetInc (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x13ebc) misa
        (by decide)).trans hmisaAfter0)
      (by rw [hsum0]; decide) (by rw [hsum0]; decide))
  -- Step 1: add a3,a1,a5 (a3 = src+i), pc = 0x13ec4.
  obtain ⟨hplat1, hcnt1⟩ := mkStepBundles hInv hSt1 (hsum0 ▸ hPC1) (by decide) hmin1
    (fetchBytesAt_13ec4 _ image hInv.himageEq (hmem1.symm ▸ hInv.hmatches))
  have hx15_1 : s1.regs.get? x15 = some (BitVec.ofNat 64 i) := by grind
  obtain ⟨s2, h1, w1, hSt12, hPC2, hmin2, hx13_2, hmem21⟩ :=
    gpStepPost (Or.inl rfl) (memcpy_step_add_a3 (start + i * 7 + 1) s1 src (BitVec.ofNat 64 i)
      _ _ _ _ hplat1 hcnt1
      ((coreGetStable s1 (BitVec.ofNat 64 0x13ec4) x11 (by decide) hSt1).trans hInv.ha1)
      ((xGet s1 (BitVec.ofNat 64 0x13ec4) x15 (by decide) (by decide)).trans hx15_1))
  have hSt2 : StableAgree s s2 := hSt1.trans hSt12
  have hmem2 : s2.mem = s.mem := hmem21.trans hmem1
  -- Step 2: lbu a3,0(a3) (a3 = mem[src+i]), pc = 0x13ec8.
  have hsum24 : Sail.BitVec.addInt (BitVec.ofNat 64 0x13ec4) 4 = BitVec.ofNat 64 0x13ec8 := by decide
  obtain ⟨hplat2, hcnt2⟩ := mkStepBundles hInv hSt2 (hsum24 ▸ hPC2) (by decide) hmin2
    (fetchBytesAt_13ec8 _ image hInv.himageEq (hmem2.symm ▸ hInv.hmatches))
  have hx13t2 := (xGet s2 (BitVec.ofNat 64 0x13ec8) x13 (by decide) (by decide)).trans hx13_2
  obtain ⟨addrReg2, physAccess2, noMMIOr2⟩ :=
    (hInv.hdata i _ hi (coreStableAgree s2 (BitVec.ofNat 64 0x13ec8) hSt2)).1 hx13t2
  have hbyte2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x13ec8)).mem.get? (src + BitVec.ofNat 64 i).toNat = some (srcByte i) :=
    hmem2 ▸ hInv.hsrc i hi
  obtain ⟨s3, h2, w2, hSt23, hPC3, hmin3, hx13_3, hmem32⟩ :=
    gpStepPost (Or.inl rfl) (memcpy_step_lbu (start + i * 7 + 2) s2 (src + BitVec.ofNat 64 i)
      mstatusBits _ _ (srcByte i) _ _ hplat2 hcnt2
      ((coreGetStable s2 (BitVec.ofNat 64 0x13ec8) mstatus (by decide) hSt2).trans hInv.hmstatus)
      ((coreGetStable s2 (BitVec.ofNat 64 0x13ec8) cur_privilege (by decide) hSt2).trans hInv.hcur)
      hInv.hmprv addrReg2 (is_aligned_vaddr_one _) physAccess2 noMMIOr2
      (leBytes_one_mem _ _ (srcByte i) hbyte2))
  have hSt3 : StableAgree s s3 := hSt2.trans hSt23
  have hmem3 : s3.mem = s.mem := hmem32.trans hmem2
  -- Step 3: add a4,a0,a5 (a4 = dst+i), pc = 0x13ecc.
  have hsum28 : Sail.BitVec.addInt (BitVec.ofNat 64 0x13ec8) 4 = BitVec.ofNat 64 0x13ecc := by decide
  obtain ⟨hplat3, hcnt3⟩ := mkStepBundles hInv hSt3 (hsum28 ▸ hPC3) (by decide) hmin3
    (fetchBytesAt_13ecc _ image hInv.himageEq (hmem3.symm ▸ hInv.hmatches))
  have hx15_3 : s3.regs.get? x15 = some (BitVec.ofNat 64 i) := by grind
  obtain ⟨s4, h3, w3, hSt34, hPC4, hmin4, hx14_4, hmem43⟩ :=
    gpStepPost (Or.inr (Or.inl rfl)) (memcpy_step_add_a4 (start + i * 7 + 3) s3 dst
      (BitVec.ofNat 64 i) _ _ _ _ hplat3 hcnt3
      ((coreGetStable s3 (BitVec.ofNat 64 0x13ecc) x10 (by decide) hSt3).trans hInv.ha0)
      ((xGet s3 (BitVec.ofNat 64 0x13ecc) x15 (by decide) (by decide)).trans hx15_3))
  have hSt4 : StableAgree s s4 := hSt3.trans hSt34
  have hmem4 : s4.mem = s.mem := hmem43.trans hmem3
  -- Step 4: addi a5,a5,1 (i++), pc = 0x13ed0.
  have hsum2c : Sail.BitVec.addInt (BitVec.ofNat 64 0x13ecc) 4 = BitVec.ofNat 64 0x13ed0 := by decide
  obtain ⟨hplat4, hcnt4⟩ := mkStepBundles hInv hSt4 (hsum2c ▸ hPC4) (by decide) hmin4
    (fetchBytesAt_13ed0 _ image hInv.himageEq (hmem4.symm ▸ hInv.hmatches))
  have hx15_4 : s4.regs.get? x15 = some (BitVec.ofNat 64 i) := by grind
  obtain ⟨s5, h4, w4, hSt45, hPC5, hmin5, hx15_5, hmem54⟩ :=
    gpStepPost (Or.inr (Or.inr rfl)) (memcpy_step_addi_a5 (start + i * 7 + 4) s4
      (BitVec.ofNat 64 i) _ _ _ _ hplat4 hcnt4
      ((xGet s4 (BitVec.ofNat 64 0x13ed0) x15 (by decide) (by decide)).trans hx15_4))
  have hSt5 : StableAgree s s5 := hSt4.trans hSt45
  have hmem5 : s5.mem = s.mem := hmem54.trans hmem4
  -- Step 5: sb a3,0(a4) (mem[dst+i] = a3), pc = 0x13ed4.
  have hsum30 : Sail.BitVec.addInt (BitVec.ofNat 64 0x13ed0) 4 = BitVec.ofNat 64 0x13ed4 := by decide
  obtain ⟨hplat5, hcnt5⟩ := mkStepBundles hInv hSt5 (hsum30 ▸ hPC5) (by decide) hmin5
    (fetchBytesAt_13ed4 _ image hInv.himageEq (hmem5.symm ▸ hInv.hmatches))
  have hx13_5 : s5.regs.get? x13 = some (zero_extend (m := 64) (srcByte i)) := by grind
  have hx14_5 : s5.regs.get? x14 = some (dst + BitVec.ofNat 64 i) := by grind
  have hx14t5 := (xGet s5 (BitVec.ofNat 64 0x13ed4) x14 (by decide) (by decide)).trans hx14_5
  obtain ⟨addrReg5, physAccess5, noMMIOw5⟩ :=
    (hInv.hdata i _ hi (coreStableAgree s5 (BitVec.ofNat 64 0x13ed4) hSt5)).2 hx14t5
  have hwrite5 := writeBytes_byte_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x13ed4))
    (dst + BitVec.ofNat 64 i).toNat (srcByte i)
  obtain ⟨s6, h5, w5, hSt56, hPC6, hmin6, hmem6⟩ :=
    sbStepPost (memcpy_step_sb (start + i * 7 + 5) s5 _ (dst + BitVec.ofNat 64 i) mstatusBits
        _ _ (srcByte i) _ _ hplat5 hcnt5
        ((coreGetStable s5 (BitVec.ofNat 64 0x13ed4) mstatus (by decide) hSt5).trans hInv.hmstatus)
        ((coreGetStable s5 (BitVec.ofNat 64 0x13ed4) cur_privilege (by decide) hSt5).trans
          hInv.hcur)
        hInv.hmprv
        ((xGet s5 (BitVec.ofNat 64 0x13ed4) x13 (by decide) (by decide)).trans
          (hx13_5.trans (congrArg some (zero_extend_setWidth (srcByte i)))))
        addrReg5 physAccess5 noMMIOw5 hwrite5)
      rfl
      (by
        show (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
            (BitVec.ofNat 64 0x13ed4)).mem.insert (dst + BitVec.ofNat 64 i).toNat (srcByte i) =
            s.mem.insert (dst + BitVec.ofNat 64 i).toNat (srcByte i)
        rw [show (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
          (BitVec.ofNat 64 0x13ed4)).mem = s.mem from hmem5])
  have hSt6 : StableAgree s s6 := hSt5.trans hSt56
  -- Step 6: j 0x13ebc (back-edge), pc = 0x13ed8.
  have hsum34 : Sail.BitVec.addInt (BitVec.ofNat 64 0x13ed4) 4 = BitVec.ofNat 64 0x13ed8 := by decide
  have hmatches6 := fileBytesMatchMemory_insert image s.mem (dst + BitVec.ofNat 64 i).toNat
    (srcByte i) hInv.hmatches (hInv.hdstImg i hi)
  obtain ⟨hplat6, hcnt6⟩ := mkStepBundles hInv hSt6 (hsum34 ▸ hPC6) (by decide) hmin6
    (fetchBytesAt_13ed8 _ image hInv.himageEq (hmem6.symm ▸ hmatches6))
  have hsumJ : (BitVec.ofNat 64 0x13ed8 + sign_extend (m := 64) (0x1FFFE4#21))
      = BitVec.ofNat 64 0x13ebc := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  obtain ⟨s7, h6, w6, hSt67, hPC7, hmin7, hmem7⟩ :=
    jumpStepPost (memcpy_step_j (start + i * 7 + 6) s6 _ _ _ _ hplat6 hcnt6)
  have hSt7 : StableAgree s s7 := hSt6.trans hSt67
  have hmemS7 : s7.mem = s.mem.insert (dst + BitVec.ofNat 64 i).toNat (srcByte i) :=
    hmem7.trans hmem6
  -- Assemble the 7-step trace and re-establish the invariant at i+1.
  have htr : Trace (start + i * 7) 7 s s7 := by trace_steps [h0, h1, h2, h3, h4, h5, h6]
  refine ⟨s7, htr, ⟨s1, s2, s3, s4, s5, s6, hInv.hPC, hsum0 ▸ hPC1, hsum24 ▸ hPC2, hsum28 ▸ hPC3,
    hsum2c ▸ hPC4, hsum30 ▸ hPC5, hsum34 ▸ hPC6, h0, h1, h2, h3, h4, h5, h6⟩, ?_⟩
  refine ⟨?hPC, ?ha5, ?ha0, ?ha1, ?ha2, ?hra, ?hcur, ?hmstatus, ?hmprv, ?hmseccfg, ?hhart,
      ?hinhibit, ?hnotInhibited, ?hcfg, ?hmachineEnabled, ?hminstret, ?himageEq, ?hmatches, ?hsrc,
      ?hcopy, ?hle, ?hnLt, ?hsrcFits, ?hdstFits, ?hdstImg, ?hdisj, ?hplat, ?hdata, ?hElp,
      ?hstable, ?hframe⟩
  case hPC => exact hsumJ ▸ hPC7
  case ha5 =>
    have hcarry : s7.regs.get? x15 = some (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) := by
      grind
    exact hcarry.trans (congrArg some (ofNat_add_one i))
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
  case hminstret => exact ⟨_, hmin7⟩
  case himageEq => exact hInv.himageEq
  case hmatches => exact hmemS7.symm ▸ hmatches6
  case hsrc =>
    intro j hj
    rw [hmemS7, getElem?_insert_ne _ _ _ _ (hInv.hdisj i j hi hj)]
    exact hInv.hsrc j hj
  case hcopy =>
    intro j hj
    rw [hmemS7]
    have hfits := hInv.hdstFits
    rcases Nat.lt_or_ge j i with hlt | hge
    · have hfit_i : dst.toNat + i < 2 ^ 64 := by omega
      have hfit_j : dst.toNat + j < 2 ^ 64 := by omega
      have hne : (dst + BitVec.ofNat 64 i).toNat ≠ (dst + BitVec.ofNat 64 j).toNat := by
        rw [windowAddr_toNat dst i hfit_i, windowAddr_toNat dst j hfit_j]; omega
      rw [getElem?_insert_ne _ _ _ _ hne]; exact hInv.hcopy j hlt
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
    (fun i s hi hInv => by
      obtain ⟨s', trace, _, invariant⟩ := memcpy_adv dst src n retAddr image mseccfgBits
        mstatusBits inhibit cfg srcByte sInit start i s hi hInv
      exact ⟨s', trace, invariant⟩)
    hInv0

/-! ## Exit step lemmas: `bne` not taken, then `ret` -/

/-- The loop-head `bne a5, a2` NOT taken (`a5 = i = n = a2`): retires with `PC = pc + 4 = 0x13ec0`. -/
theorem memcpy_step_bne_not_taken (stepNo : Nat) (state : State)
    (a2v retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64) (i : Nat)
    (plat : StepPlatform state (BitVec.ofNat 64 0x13ebc) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ebc)).regs.get? x15 = some (BitVec.ofNat 64 i))
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ebc)).regs.get? x12 = some a2v)
    (heq : BitVec.ofNat 64 i = a2v) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ebc))
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ebc) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8 = (0x00c79463 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (8#13, .Regidx 12#5, .Regidx 15#5, .BNE)) := by
    rw [wordEq]; decode_run
  have hcond : Runs (bTypeTaken (.Regidx 12#5) (.Regidx 15#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ebc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ebc))
      false := by
    have h := bTypeTaken_bne_run _ (BitVec.ofNat 64 i) a2v h15 h12
    rwa [show (BitVec.ofNat 64 i != a2v) = false by rw [heq]; simp] at h
  exact tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x13ebc) retired
    (8#13) (.Regidx 12#5) (.Regidx 15#5) .BNE inhibit config 0x63#8 0x94#8 0xc7#8 0x00#8
    platform noMMIO bytes interrupts base decode notExpected hcond hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- `ret` (`jalr x0, 0(ra)`) at `0x13ec0`: retires with `PC = ra` (bit 0 cleared).  Fetch bytes are
`67 80 00 00` (`00008067`). -/
theorem memcpy_step_ret (stepNo : Nat) (state : State)
    (rs1Val retired mseccfgBits misaBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x13ec0) 0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec0))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec0))
      rs1Val)
    (hbit1 : Sail.BitVec.access rs1Val 1 = 0#1)
    (hElp : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec0))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec0))
      ())
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ec0)).regs.get? misa = some misaBits) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec0)
          (Sail.BitVec.update rs1Val 0 0#1))
        (Sail.BitVec.update rs1Val 0 0#1) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x67#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x67#8 0x80#8 0x00#8 0x00#8 = (0x00008067 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x67#8 0x80#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0#12, .Regidx 1#5, zreg)) := by
    rw [wordEq]; decode_run
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec0))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13ec0))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ec0) 4) := by
    unfold get_next_pc; exact readReg_run _ nextPC _ (coreNextPc _ _)
  have hzca := currentlyEnabledZca_run _ misaBits hmisa
  exact tryStepRetRetires stepNo state (BitVec.ofNat 64 0x13ec0) retired (.Regidx 1#5)
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ec0) 4) rs1Val inhibit config 0x67#8 0x80#8 0x00#8 0x00#8
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected hElp hlink
    hrs1 hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- A not-taken branch retirement only writes registers in `W`. -/
theorem stableAgree_notTaken (base : State) (pc ret : BitVec 64) :
    StableAgree base (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret) :=
  (fallThroughRetirement_writes base pc (Sail.BitVec.addInt pc 4) ret).agree
    nonW_disjoint_bookkeeping

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

/-- The entry `li a5, 0` at `0x13eb8` (`a5 ↦ 0`), lifted through the generated `try_step`.  Fetch
bytes are `93 07 00 00` (`00000793`); `PC` ticks to the loop head `0x13ebc`. -/
theorem memcpy_step_li (stepNo : Nat) (state : State) (retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x13eb8) 0x93#8 0x07#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x13eb8) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x13eb8)).regs.insert x15 (BitVec.ofNat 64 0) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x13eb8) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x07#8 0x00#8 0x00#8 = (0x00000793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x07#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI)) := by
    rw [wordEq]; decode_run
  have exec : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13eb8))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13eb8) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x13eb8)).regs.insert x15 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 0#5) (.Regidx 15#5) .ADDI) _ _ _
    unfold Runs
    exact execute_li_a5_0 _
  exact tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x13eb8) retired inhibit
    config 0x93#8 0x07#8 0x00#8 0x00#8 (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI))
    x15 _ platform noMMIO bytes interrupts base decode notExpected exec
    (by decide) (by decide) (by decide) (by decide)
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Reaching the generated return exit -/

/-- Once the loop invariant reaches `i = n`, the not-taken `bne` is the final instruction owned by
the function trace. It retires to the generated `ret` exit; the caller-side transfer executes the
`ret` separately. -/
theorem memcpy_reach_ret (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (sInit : State) (start : Nat) (s : State)
    (hInv : MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte
      sInit n.toNat s) :
    ∃ final, Trace start 1 s final ∧
      Runs (try_step start false) s final false ∧
      final.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) ∧
      (∀ j : Nat, j < n.toNat →
        final.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (srcByte j)) ∧
      final.regs.get? x10 = some dst ∧ final.regs.get? x11 = some src ∧
      final.regs.get? x12 = some n ∧ final.regs.get? x1 = some retAddr ∧
      image.fileBytesMatchMemory final.mem ∧ StableAgree sInit final ∧
      MemFramed dst n sInit final ∧ RetiredCounterPresent final := by
  obtain ⟨retired, retiredRead⟩ := hInv.hminstret
  obtain ⟨platform, counters⟩ := mkStepBundles hInv (StableAgree.refl s) hInv.hPC
    (Or.inr (Or.inl rfl)) retiredRead (fetchBytesAt_13ebc _ image hInv.himageEq hInv.hmatches)
  have equal : BitVec.ofNat 64 n.toNat = n := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  have hsumL4 : Sail.BitVec.addInt (BitVec.ofNat 64 0x13ebc) 4 = BitVec.ofNat 64 0x13ec0 := by decide
  obtain ⟨final, step, w0, stable, atExit, counter, memory⟩ :=
    notTakenStepPost (memcpy_step_bne_not_taken start s n retired mseccfgBits inhibit cfg n.toNat
      platform counters
      ((xGet s (BitVec.ofNat 64 0x13ebc) x15 (by decide) (by decide)).trans hInv.ha5)
      ((xGet s (BitVec.ofNat 64 0x13ebc) x12 (by decide) (by decide)).trans hInv.ha2) equal)
  refine ⟨final, Trace.one start s final step, step, hsumL4 ▸ atExit, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ⟨_, counter⟩⟩
  · intro j hj
    rw [memory]
    exact hInv.hcopy j hj
  · exact (stable x10 (by decide)).trans hInv.ha0
  · exact (stable x11 (by decide)).trans hInv.ha1
  · exact (stable x12 (by decide)).trans hInv.ha2
  · exact (stable x1 (by decide)).trans hInv.hra
  · rw [memory]
    exact hInv.hmatches
  · exact hInv.hstable.trans stable
  · intro address outside
    rw [memory]
    exact hInv.hframe address outside

/-- Execute every remaining loop iteration and the final not-taken branch as one confined trace to
the generated `ret` exit. The recursion is over the runtime loop counter, not an unrolling limit. -/
theorem memcpy_loop_to_ret (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (sInit : State) (start i : Nat) (s : State)
    (indexBound : i ≤ n.toNat)
    (hInv : MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte
      sInit i s) :
    ∃ final,
      FunctionTrace IsBodyPc (fun pc => pc = BitVec.ofNat 64 0x13ec0)
        (start + i * 7) ((n.toNat - i) * 7 + 1) s final ∧
      final.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) ∧
      (∀ j : Nat, j < n.toNat →
        final.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (srcByte j)) ∧
      final.regs.get? x10 = some dst ∧ final.regs.get? x11 = some src ∧
      final.regs.get? x12 = some n ∧ final.regs.get? x1 = some retAddr ∧
      image.fileBytesMatchMemory final.mem ∧ StableAgree sInit final ∧
      MemFramed dst n sInit final ∧ RetiredCounterPresent final := by
  by_cases done : i = n.toNat
  · subst i
    obtain ⟨final, _, step, atExit, copied, x10Final, x11Final, x12Final, x1Final,
      imageFinal, stable, frame, counter⟩ := memcpy_reach_ret dst src n retAddr image mseccfgBits
        mstatusBits inhibit cfg srcByte sInit (start + n.toNat * 7) s hInv
    have region : IsBodyPc (BitVec.ofNat 64 0x13ebc) := by simp [IsBodyPc]
    have notExit : BitVec.ofNat 64 0x13ebc ≠ BitVec.ofNat 64 0x13ec0 := by decide
    have confined : FunctionTrace IsBodyPc (fun pc => pc = BitVec.ofNat 64 0x13ec0)
        (start + n.toNat * 7) 1 s final := by
      refine .step _ 0 _ s final final hInv.hPC region notExit step ?_
      exact .exitAt _ final _ atExit rfl
    exact ⟨final, by simpa using confined, atExit, copied, x10Final, x11Final,
      x12Final, x1Final, imageFinal, stable, frame, counter⟩
  · have beforeEnd : i < n.toNat := Nat.lt_of_le_of_ne indexBound done
    obtain ⟨next, _, iteration, nextInv⟩ := memcpy_adv dst src n retAddr image mseccfgBits
      mstatusBits inhibit cfg srcByte sInit start i s beforeEnd hInv
    obtain ⟨final, rest, atExit, copied, x10Final, x11Final, x12Final, x1Final,
      imageFinal, stable, frame, counter⟩ := memcpy_loop_to_ret dst src n retAddr image mseccfgBits
        mstatusBits inhibit cfg srcByte sInit start (i + 1) next (by omega) nextInv
    have restAtExpected : FunctionTrace IsBodyPc (fun pc => pc = BitVec.ofNat 64 0x13ec0)
        (start + i * 7 + 7) ((n.toNat - (i + 1)) * 7 + 1) next final := by
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using rest
    have combined := iteration.prepend restAtExpected
    refine ⟨final, ?_, atExit, copied, x10Final, x11Final, x12Final, x1Final,
      imageFinal, stable, frame, counter⟩
    have countArithmetic : ((n.toNat - (i + 1)) * 7 + 1) + 7 =
        (n.toNat - i) * 7 + 1 := by omega
    simpa only [countArithmetic] using combined
termination_by n.toNat - i
decreasing_by omega

/-! ## Deliverable 4: loop exit `memcpy_exit` -/

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
      image.fileBytesMatchMemory s''.mem ∧
      StableAgree sInit s'' ∧ MemFramed dst n sInit s'' := by
  obtain ⟨retired0, hret0⟩ := hInv.hminstret
  -- Step 0: bne a5,a2 NOT taken (a5 = n).
  obtain ⟨hplat0, hcnt0⟩ := mkStepBundles hInv (StableAgree.refl s) hInv.hPC (Or.inr (Or.inl rfl))
    hret0 (fetchBytesAt_13ebc _ image hInv.himageEq hInv.hmatches)
  have heq0 : BitVec.ofNat 64 n.toNat = n := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  obtain ⟨s1, hb, w0, hSt1, hPC1, hmin1, hmem1⟩ :=
    notTakenStepPost (memcpy_step_bne_not_taken start s n retired0 mseccfgBits inhibit cfg n.toNat
      hplat0 hcnt0 ((xGet s (BitVec.ofNat 64 0x13ebc) x15 (by decide) (by decide)).trans hInv.ha5)
      ((xGet s (BitVec.ofNat 64 0x13ebc) x12 (by decide) (by decide)).trans hInv.ha2) heq0)
  -- Step 1: ret.
  have hsumL4 : Sail.BitVec.addInt (BitVec.ofNat 64 0x13ebc) 4 = BitVec.ofNat 64 0x13ec0 := by decide
  obtain ⟨hplat1, hcnt1⟩ := mkStepBundles hInv hSt1 (hsumL4 ▸ hPC1) (by decide) hmin1
    (fetchBytesAt_13ec0 _ image hInv.himageEq (hmem1.symm ▸ hInv.hmatches))
  obtain ⟨misaBits1, _, _, hmisaA1, _⟩ := hplat1.1
  obtain ⟨s2, hr, w1, hSt12, hPC2, hmin2, hmem21⟩ :=
    jumpStepPost (memcpy_step_ret (start + 1) s1 retAddr _ _ misaBits1 _ _ hplat1 hcnt1
      (rX_bits_run_x1 _ retAddr
        ((coreGetStable s1 (BitVec.ofNat 64 0x13ec0) x1 (by decide) hSt1).trans hInv.hra))
      hretAlign (hInv.hElp _ (.Regidx 1#5) rfl (coreStableAgree s1 (BitVec.ofNat 64 0x13ec0) hSt1))
      ((coreGetInc (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x13ec0) misa
        (by decide)).trans hmisaA1))
  have hSt2 : StableAgree s s2 := hSt1.trans hSt12
  have hmem2 : s2.mem = s.mem := hmem21.trans hmem1
  refine ⟨s2, Trace.step _ _ _ _ _ hb (Trace.one _ _ _ hr), hPC2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [hmem2]; exact hInv.hcopy j hj
  · exact (hSt2 x10 (by decide)).trans hInv.ha0
  · exact (hSt2 x11 (by decide)).trans hInv.ha1
  · exact (hSt2 x12 (by decide)).trans hInv.ha2
  · exact (hSt2 x1 (by decide)).trans hInv.hra
  · rw [hmem2]; exact hInv.hmatches
  · exact hInv.hstable.trans hSt2
  · intro addr h; rw [hmem2]; exact hInv.hframe addr h

/-! ## Deliverable 5: capstone contract `memcpy_contract` -/

/-- CAPSTONE.  `memcpy(dst, src, n)` at `0x13eb8`, run through the authoritative generated `try_step`
from a configured machine with the abstract data-access and non-overlap preconditions: a single
`1 + n*7 + 2`-step trace (entry `li` + loop + exit) to the caller, after which every destination byte
`mem[dst+j]` equals the original source byte `mem[src+j]` (`= srcByte j`), the source region, code
image and argument registers are preserved, and `PC = ra` (bit 0 cleared). -/
theorem memcpy_contract (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (start : Nat) (s : State)
    (hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x13eb8))
    (ha0 : s.regs.get? x10 = some dst) (ha1 : s.regs.get? x11 = some src)
    (ha2 : s.regs.get? x12 = some n) (hra : s.regs.get? x1 = some retAddr)
    (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmstatus : s.regs.get? mstatus = some mstatusBits) (hmprv : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hhart : s.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hinhibit : s.regs.get? mcountinhibit = some inhibit) (hnotInhibited : _get_Counterin_IR inhibit = 0#1)
    (hcfg : s.regs.get? minstretcfg = some cfg) (hmachineEnabled : _get_CountSmcntrpmf_MINH cfg = 0#1)
    (hminstret : ∃ v, s.regs.get? minstret = some v)
    (himageEq : image = Artifacts.programImage) (hmatches : image.fileBytesMatchMemory s.mem)
    (hsrc : ∀ j : Nat, j < n.toNat → s.mem.get? (src + BitVec.ofNat 64 j).toNat = some (srcByte j))
    (hnLt : n.toNat < 2 ^ 64) (hsrcFits : src.toNat + n.toNat ≤ 2 ^ 64)
    (hdstFits : dst.toNat + n.toNat ≤ 2 ^ 64)
    (hdstImg : ∀ j : Nat, j < n.toNat → image.readFileByte? (dst + BitVec.ofNat 64 j).toNat = none)
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
      image.fileBytesMatchMemory s''.mem ∧
      -- Compositional framing (Deliverables 1–4):
      -- every register outside `W` is preserved (in particular `x2`/`sp`, a leaf function),
      StableAgree s s'' ∧ s''.regs.get? x2 = s.regs.get? x2 ∧
      -- memory changes only inside the destination window `[dst, dst+n)`,
      MemFramed dst n s s'' ∧
      -- and the source region is preserved (from the frame plus the non-overlap premise).
      (∀ k : Nat, k < n.toNat →
        s''.mem.get? (src + BitVec.ofNat 64 k).toNat = s.mem.get? (src + BitVec.ofNat 64 k).toNat) := by
  obtain ⟨retired0, hret0⟩ := hminstret
  -- Entry: li a5, 0 at 0x13eb8.
  have hbytesE : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x13eb8)
      0x93#8 0x07#8 0x00#8 0x00#8 :=
    fetchBytesAt_13eb8 (tryStepControlFlowAfterIncrement s) image himageEq hmatches
  have hplatE : StepPlatform s (BitVec.ofNat 64 0x13eb8) 0x93#8 0x07#8 0x00#8 0x00#8 mseccfgBits :=
    mkStepPlatform s mseccfgBits (BitVec.ofNat 64 0x13eb8) 0x93#8 0x07#8 0x00#8 0x00#8
      hplat hcur hmseccfg (StableAgree.refl s)
      ((afterIncGet s PC (by decide)).trans hPC) (Or.inl rfl) hbytesE
  have hcntE : StepCounters s retired0 inhibit cfg :=
    ⟨hhart, hinhibit, hcfg, hnotInhibited, hmachineEnabled, hret0⟩
  obtain ⟨s0, hli, w0, hSt0, hPC0, hmin0, hx15_0, hmem0⟩ :=
    gpStepPost (Or.inr (Or.inr rfl))
      (memcpy_step_li start s retired0 mseccfgBits inhibit cfg hplatE hcntE)
  have hsum18 : Sail.BitVec.addInt (BitVec.ofNat 64 0x13eb8) 4 = BitVec.ofNat 64 0x13ebc := by decide
  -- The i = 0 loop-head invariant at the post-entry state.
  have hInv0 : MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte s 0
      s0 :=
    ⟨hsum18 ▸ hPC0, hx15_0, (hSt0 x10 (by decide)).trans ha0, (hSt0 x11 (by decide)).trans ha1,
      (hSt0 x12 (by decide)).trans ha2, (hSt0 x1 (by decide)).trans hra,
      (hSt0 cur_privilege (by decide)).trans hcur, (hSt0 mstatus (by decide)).trans hmstatus, hmprv,
      (hSt0 mseccfg (by decide)).trans hmseccfg, (hSt0 hart_state (by decide)).trans hhart,
      (hSt0 mcountinhibit (by decide)).trans hinhibit, hnotInhibited,
      (hSt0 minstretcfg (by decide)).trans hcfg, hmachineEnabled, ⟨_, hmin0⟩, himageEq,
      (by rw [hmem0]; exact hmatches), (fun j hj => by rw [hmem0]; exact hsrc j hj),
      (fun j hj => absurd hj (Nat.not_lt_zero j)), Nat.zero_le _, hnLt, hsrcFits, hdstFits, hdstImg,
      hdisj, AbstractPlatform.mono hSt0 hplat, AbstractDataAccess.mono hSt0 hdata,
      AbstractElp.mono hSt0 hElp, hSt0, (fun addr _ => by rw [hmem0])⟩
  -- Loop.
  obtain ⟨sN, htrLoop, hInvN⟩ := memcpy_loop dst src n retAddr image mseccfgBits mstatusBits inhibit
    cfg srcByte s (start + 1) _ hInv0
  -- Exit.
  obtain ⟨s'', htrExit, hPCret, hcopyN, hx10, hx11, hx12, hx1N, hmatchesN,
    hStableExit, hFrameExit⟩ :=
    memcpy_exit dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte s
      (start + (1 + n.toNat * 7)) sN hretAlign hInvN
  refine ⟨s'', ?_, hPCret, hcopyN, hx10, hx11, hx12, hx1N, hmatchesN,
    hStableExit, hStableExit x2 (by decide), hFrameExit,
    fun k hk => MemFramed.source_preserved hFrameExit hdisj k hk⟩
  have htrLi := Trace.one _ _ _ hli
  have hcomb := Trace.append (Trace.append htrLi htrLoop) htrExit
  simpa using hcomb

/-- CAPSTONE.  `memcpy(dst, src, n)` at `0x13eb8`, run through the authoritative generated `try_step`
from a configured machine with the abstract data-access and non-overlap preconditions: a single
`1 + n*7 + 1`-step trace (entry `li` + loop + final branch) to the generated `ret` exit, after which every destination byte
`mem[dst+j]` equals the original source byte `mem[src+j]` (`= srcByte j`), the source region, code
image and argument registers are preserved, and `PC = ra` (bit 0 cleared). -/
theorem memcpy_body (dst src n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (start : Nat) (s : State)
    (hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x13eb8))
    (ha0 : s.regs.get? x10 = some dst) (ha1 : s.regs.get? x11 = some src)
    (ha2 : s.regs.get? x12 = some n) (hra : s.regs.get? x1 = some retAddr)
    (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmstatus : s.regs.get? mstatus = some mstatusBits) (hmprv : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hhart : s.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hinhibit : s.regs.get? mcountinhibit = some inhibit) (hnotInhibited : _get_Counterin_IR inhibit = 0#1)
    (hcfg : s.regs.get? minstretcfg = some cfg) (hmachineEnabled : _get_CountSmcntrpmf_MINH cfg = 0#1)
    (hminstret : ∃ v, s.regs.get? minstret = some v)
    (himageEq : image = Artifacts.programImage) (hmatches : image.fileBytesMatchMemory s.mem)
    (hsrc : ∀ j : Nat, j < n.toNat → s.mem.get? (src + BitVec.ofNat 64 j).toNat = some (srcByte j))
    (hnLt : n.toNat < 2 ^ 64) (hsrcFits : src.toNat + n.toNat ≤ 2 ^ 64)
    (hdstFits : dst.toNat + n.toNat ≤ 2 ^ 64)
    (hdstImg : ∀ j : Nat, j < n.toNat → image.readFileByte? (dst + BitVec.ofNat 64 j).toNat = none)
    (hdisj : ∀ j k : Nat, j < n.toNat → k < n.toNat →
      (dst + BitVec.ofNat 64 j).toNat ≠ (src + BitVec.ofNat 64 k).toNat)
    (hplat : AbstractPlatform s) (hdata : AbstractDataAccess n dst src s) (hElp : AbstractElp s) :
    ∃ s'', Trace start (1 + n.toNat * 7 + 1) s s'' ∧
      FunctionTrace IsBodyPc (fun pc => pc = BitVec.ofNat 64 0x13ec0)
        start (1 + n.toNat * 7 + 1) s s'' ∧
      s''.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) ∧
      (∀ j : Nat, j < n.toNat →
        s''.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (srcByte j)) ∧
      s''.regs.get? x10 = some dst ∧ s''.regs.get? x11 = some src ∧
      s''.regs.get? x12 = some n ∧ s''.regs.get? x1 = some retAddr ∧
      image.fileBytesMatchMemory s''.mem ∧
      -- Compositional framing (Deliverables 1–4):
      -- every register outside `W` is preserved (in particular `x2`/`sp`, a leaf function),
      StableAgree s s'' ∧ s''.regs.get? x2 = s.regs.get? x2 ∧
      -- memory changes only inside the destination window `[dst, dst+n)`,
      MemFramed dst n s s'' ∧
      -- and the source region is preserved (from the frame plus the non-overlap premise).
      (∀ k : Nat, k < n.toNat →
        s''.mem.get? (src + BitVec.ofNat 64 k).toNat = s.mem.get? (src + BitVec.ofNat 64 k).toNat) ∧
      RetiredCounterPresent s'' := by
  obtain ⟨retired0, hret0⟩ := hminstret
  -- Entry: li a5, 0 at 0x13eb8.
  have hbytesE : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x13eb8)
      0x93#8 0x07#8 0x00#8 0x00#8 :=
    fetchBytesAt_13eb8 (tryStepControlFlowAfterIncrement s) image himageEq hmatches
  have hplatE : StepPlatform s (BitVec.ofNat 64 0x13eb8) 0x93#8 0x07#8 0x00#8 0x00#8 mseccfgBits :=
    mkStepPlatform s mseccfgBits (BitVec.ofNat 64 0x13eb8) 0x93#8 0x07#8 0x00#8 0x00#8
      hplat hcur hmseccfg (StableAgree.refl s)
      ((afterIncGet s PC (by decide)).trans hPC) (Or.inl rfl) hbytesE
  have hcntE : StepCounters s retired0 inhibit cfg :=
    ⟨hhart, hinhibit, hcfg, hnotInhibited, hmachineEnabled, hret0⟩
  obtain ⟨s0, hli, w0, hSt0, hPC0, hmin0, hx15_0, hmem0⟩ :=
    gpStepPost (Or.inr (Or.inr rfl))
      (memcpy_step_li start s retired0 mseccfgBits inhibit cfg hplatE hcntE)
  have hsum18 : Sail.BitVec.addInt (BitVec.ofNat 64 0x13eb8) 4 = BitVec.ofNat 64 0x13ebc := by decide
  -- The i = 0 loop-head invariant at the post-entry state.
  have hInv0 : MemcpyInv dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte s 0
      s0 :=
    ⟨hsum18 ▸ hPC0, hx15_0, (hSt0 x10 (by decide)).trans ha0, (hSt0 x11 (by decide)).trans ha1,
      (hSt0 x12 (by decide)).trans ha2, (hSt0 x1 (by decide)).trans hra,
      (hSt0 cur_privilege (by decide)).trans hcur, (hSt0 mstatus (by decide)).trans hmstatus, hmprv,
      (hSt0 mseccfg (by decide)).trans hmseccfg, (hSt0 hart_state (by decide)).trans hhart,
      (hSt0 mcountinhibit (by decide)).trans hinhibit, hnotInhibited,
      (hSt0 minstretcfg (by decide)).trans hcfg, hmachineEnabled, ⟨_, hmin0⟩, himageEq,
      (by rw [hmem0]; exact hmatches), (fun j hj => by rw [hmem0]; exact hsrc j hj),
      (fun j hj => absurd hj (Nat.not_lt_zero j)), Nat.zero_le _, hnLt, hsrcFits, hdstFits, hdstImg,
      hdisj, AbstractPlatform.mono hSt0 hplat, AbstractDataAccess.mono hSt0 hdata,
      AbstractElp.mono hSt0 hElp, hSt0, (fun addr _ => by rw [hmem0])⟩
  -- Execute the runtime loop and stop at the generated return exit.
  obtain ⟨s'', htrLoop, hPCret, hcopyN, hx10, hx11, hx12, hx1N, hmatchesN,
    hStableExit, hFrameExit, hCounterExit⟩ :=
    memcpy_loop_to_ret dst src n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte s
      (start + 1) 0 _ (by omega) hInv0
  have hentryRegion : IsBodyPc (BitVec.ofNat 64 0x13eb8) := by simp [IsBodyPc]
  have hentryNotExit : BitVec.ofNat 64 0x13eb8 ≠ BitVec.ofNat 64 0x13ec0 := by decide
  have hconfined : FunctionTrace IsBodyPc (fun pc => pc = BitVec.ofNat 64 0x13ec0)
      start (1 + n.toNat * 7 + 1) s s'' := by
    have hcombined := FunctionTrace.step start _ (BitVec.ofNat 64 0x13eb8) s _ s''
      hPC hentryRegion hentryNotExit hli htrLoop
    simpa only [Nat.zero_mul, Nat.sub_zero, Nat.zero_add, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hcombined
  refine ⟨s'', hconfined.toTrace, hconfined, hPCret, hcopyN, hx10, hx11, hx12, hx1N, hmatchesN,
    hStableExit, hStableExit x2 (by decide), hFrameExit,
    fun k hk => MemFramed.source_preserved hFrameExit hdisj k hk, hCounterExit⟩

end BinaryFv.Zesu.MachineExecution
