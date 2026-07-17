import BinaryFv.Keccak.MemcpyContract

/-!
# The `memset` (0x10d3c) byte-fill loop, proved through the authoritative generated `try_step`

Stage 4 lifts the per-instruction `try_step` packagings into a whole-loop contract for the leaf
byte-fill helper `memset` at `0x10d3c`:

```
0x10d3c li   a5,0            ; entry: i=0
0x10d40 bne  a5,a2,0x10d48   ; loop head L; taken while i≠n
0x10d44 ret                  ; when i==n
0x10d48 add  a4,a0,a5        ; a4 = dst+i
0x10d4c sb   a1,0(a4)        ; mem[dst+i] = low byte of a1
0x10d50 addi a5,a5,1         ; i++
0x10d54 j    0x10d40         ; back to L
```

Registers: `a0 = dst`, `a1 = byteval`, `a2 = n`.  The loop body is a length-5 iteration: the
conditional back-edge test, the address computation `dst + i`, the constant byte store, the index
increment, and the unconditional back-edge (memcpy's body is length-7; memset simply drops the
load and the second address computation).

Everything generic — the `StableAgree` register framing off the loop-written set, the frame algebra,
the `StepPlatform`/`StepCounters` bundles, `AbstractElp`, and the per-instruction `try_step`
packagings — is reused verbatim from `MemcpyContract`.  The only new machinery is the generalized
byte store `execute_STORE_sb_full_run`, which reads an *arbitrary* register and stores its low byte
(memcpy's `execute_STORE_byte_run` bakes in a zero-extended byte, valid there because `a3` came from
`lbu`; `memset`'s `a1` is an arbitrary caller-provided value, so its low byte `a1 &&& 0xff` is stored
for any `a1`).

The genuine platform/data-access preconditions are carried *abstractly* in the loop invariant,
exactly the stage-2 trust boundary: they are hypotheses about a configured machine, never discharged
here, so the final axiom footprint is the XOR/fetch baseline.
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

/-! ## Re-derived private frame helpers (file-local copies of `MemcpyContract`'s private lemmas) -/

/-- `nextPC` slot of `coreControlFlowNextState Y pc` is `pc + 4`. -/
private theorem msCoreNextPc (Y : State) (pc : BitVec 64) :
    (coreControlFlowNextState Y pc).regs.get? nextPC = some (Sail.BitVec.addInt pc 4) := by
  change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- Any register other than `nextPC` reads through `coreControlFlowNextState Y pc` back to `Y`. -/
private theorem msCoreGetInc (Y : State) (pc : BitVec 64) (r : Register) (hnp : r ≠ nextPC) :
    (coreControlFlowNextState Y pc).regs.get? r = Y.regs.get? r := by
  simpa [coreControlFlowNextState] using
    writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

/-- The `nextPC` slot of the post-execute register file of a GP-writing fall-through instruction. -/
private theorem msGpFrameNextPc (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (hrd : nextPC ≠ rd) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC =
      some (Sail.BitVec.addInt pc 4) := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC
      = (coreControlFlowNextState Y pc).regs.get? nextPC :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd nextPC v hrd
    _ = some (Sail.BitVec.addInt pc 4) := by
        change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
        rw [Std.ExtDHashMap.get?_insert]; simp

/-- Any register other than `nextPC` and `rd` reads through the post-execute state back to `Y`. -/
private theorem msGpFrameGet (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (r : Register) (hrd : r ≠ rd) (hnp : r ≠ nextPC) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? r = Y.regs.get? r := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? r
      = (coreControlFlowNextState Y pc).regs.get? r :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd r v hrd
    _ = Y.regs.get? r := by
        simpa [coreControlFlowNextState] using
          writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

/-! ## New foundational facts for the constant byte store -/

/-- The low-byte extraction of a width-64 word is its width-8 truncation. -/
theorem extractLsb_lowbyte (x : BitVec 64) :
    Sail.BitVec.extractLsb x 7 0 = BitVec.setWidth 8 x := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  bv_decide

/-- Reading `a1 = x11` via `rX_bits` (the byte-store data source). -/
theorem rX_bits_x11_run (s : State) (v : BitVec 64) (h : s.regs.get? x11 = some v) :
    Runs (rX_bits (.Regidx 11#5)) s s v := by
  have r11 : (Sail.BitVec.toNatInt (11#5)).toNat = 11 := by decide
  unfold Runs
  simp [rX_bits, rX, r11, h, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

/-- Aligned byte store reading an *arbitrary* source register value `dataFull` and writing its low
byte `bval = extractLsb dataFull 7 0`.  Unlike `execute_STORE_byte_run` (which requires the register
to already hold a zero-extended byte `setWidth 64 dataBits`), this reads the full register and lets
the generated truncation `extractLsb (rX_bits rs2) 7 0` produce the stored byte, so it is valid for
any `a1`. -/
theorem execute_STORE_sb_full_run (s s' : State) (rs2 rs1 : regidx) (imm : BitVec 12)
    (dstBits mstatusBits dataFull : BitVec 64) (bval : BitVec (8 * 1))
    (hbval : bval = Sail.BitVec.extractLsb dataFull 7 0)
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (dataReg : Runs (rX_bits rs2) s s dataFull)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Store Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 1) s s false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat bval) s s' true) :
    Runs (execute_STORE imm rs2 rs1 1) s s' (.Retire_Success ()) := by
  subst hbval
  unfold execute_STORE
  refine Runs.bind (assert_true_run s _) ?_
  refine Runs.bind dataReg ?_
  refine Runs.bind (run_pure s _) ?_
  refine Runs.bind
    (vmem_write_byte_run s s' rs1 (sign_extend (m := 64) imm) dstBits mstatusBits _
      mstatusRead privRead mprvZero addrReg physAccess noMMIO ?hw) ?_
  case hw => exact hwrite
  exact run_pure s' _

/-! ## The memset function's fetch addresses and abstract configured-machine preconditions -/

/-- The instruction fetch addresses of the memset function (entry, loop head, ret, and body). -/
@[reducible] def MsBodyPc (pc : BitVec 64) : Prop :=
  pc = BitVec.ofNat 64 0x10d3c ∨ pc = BitVec.ofNat 64 0x10d40 ∨ pc = BitVec.ofNat 64 0x10d44 ∨
  pc = BitVec.ofNat 64 0x10d48 ∨ pc = BitVec.ofNat 64 0x10d4c ∨ pc = BitVec.ofNat 64 0x10d50 ∨
  pc = BitVec.ofNat 64 0x10d54

/-- Abstract configured-machine fetch/decode platform for memset's fetch addresses.  Never
discharged here (the stage-2 trust boundary). -/
def MsAbstractPlatform (base : State) : Prop :=
  ∀ (t : State) (pc : BitVec 64), StableAgree base t → t.regs.get? PC = some pc → MsBodyPc pc →
    FetchBasePlatform t pc ∧ FetchMemoryNoMMIO t pc ∧ InterruptDisabled t ∧ LandingPadNotExpected t

/-- The abstract platform survives to a `StableAgree`-equal state. -/
theorem MsAbstractPlatform.mono {s s' : State} (h : StableAgree s s') (hp : MsAbstractPlatform s) :
    MsAbstractPlatform s' :=
  fun t pc hst hPC hbody => hp t pc (fun r hr => (hst r hr).trans (h r hr)) hPC hbody

/-- Abstract store data-access preconditions at every in-range offset, quantified over
`StableAgree`-equal states holding the resolved effective address `dst + j` in `a4 = x14`.  memset
performs only stores, so (unlike memcpy) there is no load half.  Never discharged here. -/
def AbstractStoreAccess (n dst : BitVec 64) (base : State) : Prop :=
  ∀ (j : Nat) (t : State), j < n.toNat → StableAgree base t →
    t.regs.get? x14 = some (dst + BitVec.ofNat 64 j) →
      Runs (get_transformed_data_addr (.Regidx 14#5) (sign_extend (m := 64) 0#12) (Store Data) 1)
        t t (.Ext_DataAddr_OK (virtaddr.Virtaddr (dst + BitVec.ofNat 64 j))) ∧
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine
        (physaddr.Physaddr (dst + BitVec.ofNat 64 j)) 1 false) t t none ∧
      Runs (within_mmio_writable (physaddr.Physaddr (dst + BitVec.ofNat 64 j)) 1) t t false

/-- The abstract store access survives to a `StableAgree`-equal state. -/
theorem AbstractStoreAccess.mono {n dst : BitVec 64} {s s' : State} (h : StableAgree s s')
    (hd : AbstractStoreAccess n dst s) : AbstractStoreAccess n dst s' :=
  fun j t hj hst => hd j t hj (fun r hr => (hst r hr).trans (h r hr))

/-- Assemble a `StepPlatform` bundle from the abstract memset platform field, the pre-step config,
and a concrete fetch fact, for a state `StableAgree`-equal to the invariant's base at `pc`. -/
theorem mkMsStepPlatform {s : State} (s_k : State) (mseccfgBits pc : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hplat : MsAbstractPlatform s) (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hSt : StableAgree s s_k)
    (hPCafter : (tryStepControlFlowAfterIncrement s_k).regs.get? PC = some pc)
    (hbody : MsBodyPc pc)
    (hbytes : FetchBytesAt (tryStepControlFlowAfterIncrement s_k) pc b0 b1 b2 b3) :
    StepPlatform s_k pc b0 b1 b2 b3 mseccfgBits := by
  have hStA : StableAgree s (tryStepControlFlowAfterIncrement s_k) := hSt.afterInc
  obtain ⟨hfbp, hmmio, hint, hlp⟩ := hplat _ pc hStA hPCafter hbody
  exact ⟨hfbp, hmmio, hbytes, hint, hlp, (hStA cur_privilege (by decide)).trans hcur,
    (hStA mseccfg (by decide)).trans hmseccfg⟩

/-! ## The loop invariant -/

/-- The memset loop invariant at the loop head `L = 0x10d40` about to run iteration `i`.  `sInit` is
the fixed reference state (the caller's entry state) against which the compositional framing —
`hstable` (registers) and `hframe` (memory) — is tracked. -/
structure MemsetInv (dst n retAddr byteval : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (sInit : State) (i : Nat) (s : State) : Prop where
  hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10d40)
  ha5 : s.regs.get? x15 = some (BitVec.ofNat 64 i)
  ha0 : s.regs.get? x10 = some dst
  ha1 : s.regs.get? x11 = some byteval
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
  hset : ∀ j : Nat, j < i → s.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (BitVec.setWidth 8 byteval)
  hle : i ≤ n.toNat
  hnLt : n.toNat < 2 ^ 64
  hdstFits : dst.toNat + n.toNat ≤ 2 ^ 64
  hdstImg : ∀ j : Nat, j < n.toNat → image.readByte? (dst + BitVec.ofNat 64 j).toNat = none
  hplat : MsAbstractPlatform s
  hdata : AbstractStoreAccess n dst s
  hElp : AbstractElp s
  /-- Every register outside the loop's write set `W` still agrees with the reference state. -/
  hstable : StableAgree sInit s
  /-- The exact memory delta so far: every address not among the filled window `[dst, dst+i)` still
  reads its reference-state value. -/
  hframe : ∀ addr : Nat, (∀ j : Nat, j < i → addr ≠ (dst + BitVec.ofNat 64 j).toNat) →
    s.mem.get? addr = sInit.mem.get? addr

/-! ## Step 0: `bne a5, a2, 0x10d48` at the loop head `L = 0x10d40` (taken while `i ≠ n`) -/

/-- The loop-head conditional branch, taken (`a5 = i ≠ n = a2`), lifted through the generated
`try_step`.  Fetch bytes at `0x10d40` are `63 94 c7 00` (`00c79463 = bne a5,a2,+8`); the target is
`pc + 8 = 0x10d48`. -/
theorem memset_step_bne_taken (stepNo : Nat) (state : State)
    (pcVal a2v retired : BitVec 64) (mseccfgBits : BitVec 64) (inhibit : BitVec 32)
    (config : BitVec 64) (i : Nat)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d40) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? x15 = some (BitVec.ofNat 64 i))
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? x12 = some a2v)
    (hneq : BitVec.ofNat 64 i ≠ a2v)
    (hpcRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? PC = some pcVal)
    (misaBits : BitVec 64)
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? misa = some misaBits)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) (8#13)) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) (8#13)) 1 = 0#1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d40) (pcVal + sign_extend (m := 64) (8#13)))
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
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      true := by
    have := bTypeTaken_bne_run _ (BitVec.ofNat 64 i) a2v h15 h12
    rwa [hcondEq] at this
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      pcVal :=
    readReg_run _ PC pcVal hpcRead
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x10d40) pcVal retired
    (8#13) (.Regidx 12#5) (.Regidx 15#5) .BNE inhibit config 0x63#8 0x94#8 0xc7#8 0x00#8
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected
    hcond hpc halign hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead

/-! ## Step 1: `add a4, a0, a5` at `0x10d48` (`a4 = dst + i`) -/

/-- The `add a4, a0, a5` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d48` are `33 07 f5 00` (`00f50733`); the destination write is `x14 ↦ dstVal + a5Val`. -/
theorem memset_step_add_a4 (stepNo : Nat) (state : State)
    (dstVal a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d48) 0x33#8 0x07#8 0xf5#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h10 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d48)).regs.get? x10 = some dstVal)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d48)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d48) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d48)).regs.insert x14 (dstVal + a5Val) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d48) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x33#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x33#8 0x07#8 0xf5#8 0x00#8 = (0x00f50733 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x07#8 0xf5#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)) := by
    rw [wordEq]; exact ext_decode_add_a4_a0_a5_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d48))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d48) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d48)).regs.insert x14 (dstVal + a5Val) }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 15#5) (.Regidx 10#5) (.Regidx 14#5) .ADD) _ _ _
    unfold Runs
    exact execute_add_a4_a0_a5 _ dstVal a5Val h10 h15
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d48) retired inhibit config
    0x33#8 0x07#8 0xf5#8 0x00#8 (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD))
    platform noMMIO bytes interrupts base decode notExpected exec
    (msGpFrameNextPc _ _ x14 _ (by decide))
    (msGpFrameGet _ _ x14 _ hart_state (by decide) (by decide))
    (msGpFrameGet _ _ x14 _ minstret_increment (by decide) (by decide))
    (msGpFrameGet _ _ x14 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 2: `sb a1, 0(a4)` at `0x10d4c` (`mem[dst + i] = low byte of a1`) -/

/-- The `sb a1, 0(a4)` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d4c` are `23 00 b7 00` (`00b70023`); the low byte of `a1 = byteval` (`storedByte =
setWidth₈ byteval`) is written to `dstAddrBits = dst + i`, yielding the opaque post-write state
`s'`. -/
theorem memset_step_sb (stepNo : Nat) (state s' : State)
    (dstAddrBits mstatusBits retired mseccfgBits byteval : BitVec 64) (storedByte : BitVec (8 * 1))
    (hstored : storedByte = BitVec.setWidth 8 byteval)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d4c) 0x23#8 0x00#8 0xb7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d4c)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d4c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hx11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d4c)).regs.get? x11 = some byteval)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 14#5) (sign_extend (m := 64) 0#12)
      (Store Data) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstAddrBits)))
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstAddrBits) 1 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      none)
    (noMMIOw : Runs (within_mmio_writable (physaddr.Physaddr dstAddrBits) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      false)
    (hwrite : Runs (PreSail.writeBytes dstAddrBits.toNat storedByte)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      s' true) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d4c) 4) retired)
      false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x23#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x23#8 0x00#8 0xb7#8 0x00#8 = (0x00b70023 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x23#8 0x00#8 0xb7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (0#12, .Regidx 11#5, .Regidx 14#5, 1)) := by
    rw [wordEq]; exact ext_decode_sb_a1_a4_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.STORE (0#12, .Regidx 11#5, .Regidx 14#5, 1)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      s' (.Retire_Success ()) := by
    change Runs (execute_STORE 0#12 (.Regidx 11#5) (.Regidx 14#5) 1) _ _ _
    exact execute_STORE_sb_full_run _ s' (.Regidx 11#5) (.Regidx 14#5) 0#12 dstAddrBits mstatusBits
      byteval storedByte (hstored.trans (extractLsb_lowbyte byteval).symm) mstatusReadX privReadX
      mprvZero (rX_bits_x11_run _ _ hx11) addrReg physAccess noMMIOw hwrite
  have regsEq : s'.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x10d4c)).regs :=
    writeBytes_preserves_regs dstAddrBits.toNat storedByte _ s' hwrite
  refine tryStepFallThroughRetires stepNo state s' (BitVec.ofNat 64 0x10d4c) retired inhibit config
    0x23#8 0x00#8 0xb7#8 0x00#8 (.STORE (0#12, .Regidx 11#5, .Regidx 14#5, 1))
    platform noMMIO bytes interrupts base decode notExpected exec ?_ ?_ ?_ ?_
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  · rw [regsEq]; exact msCoreNextPc _ _
  · rw [regsEq]; exact msCoreGetInc _ _ hart_state (by decide)
  · rw [regsEq]; exact msCoreGetInc _ _ minstret_increment (by decide)
  · rw [regsEq]; exact msCoreGetInc _ _ minstret (by decide)

/-! ## Step 3: `addi a5, a5, 1` at `0x10d50` (`i++`) -/

/-- The `addi a5, a5, 1` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d50` are `93 87 17 00` (`00178793`); the destination write is `x15 ↦ a5Val + sext 1`. -/
theorem memset_step_addi_a5 (stepNo : Nat) (state : State)
    (a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d50) 0x93#8 0x87#8 0x17#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d50)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d50) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d50)).regs.insert x15 (a5Val + sign_extend (m := 64) 1#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d50) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x87#8 0x17#8 0x00#8 = (0x00178793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x87#8 0x17#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_addi_a5_a5_1_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d50))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d50) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d50)).regs.insert x15 (a5Val + sign_extend (m := 64) 1#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 1#12 (.Regidx 15#5) (.Regidx 15#5) .ADDI) _ _ _
    unfold Runs
    exact execute_addi_a5_a5_1 _ a5Val h15
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d50) retired inhibit config
    0x93#8 0x87#8 0x17#8 0x00#8 (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (msGpFrameNextPc _ _ x15 _ (by decide))
    (msGpFrameGet _ _ x15 _ hart_state (by decide) (by decide))
    (msGpFrameGet _ _ x15 _ minstret_increment (by decide) (by decide))
    (msGpFrameGet _ _ x15 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 4: `j 0x10d40` at `0x10d54` (unconditional back-edge) -/

/-- The `j 0x10d40` back-edge (`JAL imm x0`, `imm` byte-offset `-20`), lifted through the generated
`try_step`.  Fetch bytes at `0x10d54` are `6f f0 df fe` (`fedff06f`); the jump target is
`pc + sext imm = 0x10d40`. -/
theorem memset_step_j (stepNo : Nat) (state : State)
    (retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d54) 0x6f#8 0xf0#8 0xdf#8 0xfe#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d54)
          (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)))
        (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  obtain ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeRead, pcLow0, pcLow1,
    alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩ := platform
  have base : BaseInstructionEncoding 0x6f#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x6f#8 0xf0#8 0xdf#8 0xfe#8 = (0xfedff06f : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x6f#8 0xf0#8 0xdf#8 0xfe#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1FFFEC#21, zreg)) := by
    rw [wordEq]; exact ext_decode_j_memset_run _ privRead mseccfgBits mseccfgRead
  have hPCx : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d54)).regs.get? PC = some (BitVec.ofNat 64 0x10d54) := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC PC
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d54) 4) (by decide)).trans pcRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d54) 4) := by
    unfold get_next_pc
    exact readReg_run _ nextPC _ (msCoreNextPc _ _)
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (BitVec.ofNat 64 0x10d54) :=
    readReg_run _ PC _ hPCx
  have hmisax : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d54)).regs.get? misa = some misaBits := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC misa
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d54) 4) (by decide)).trans misaRead
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisax]
  have hsum : (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21))
      = BitVec.ofNat 64 0x10d40 := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have halign : Sail.BitVec.access
      (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)) 0 = 0#1 := by
    rw [hsum]; decide
  have hbit1 : Sail.BitVec.access
      (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)) 1 = 0#1 := by
    rw [hsum]; decide
  exact tryStepJRetires stepNo state (BitVec.ofNat 64 0x10d54) (BitVec.ofNat 64 0x10d54) retired
    (0x1FFFEC#21) inhibit config 0x6f#8 0xf0#8 0xdf#8 0xfe#8
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d54) 4) (_get_Misa_C misaBits == 1#1)
    ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeRead, pcLow0, pcLow1,
      alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩
    noMMIO bytes interrupts base decode notExpected hlink hpc halign hbit1 hzca
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Exit step lemmas: `bne` not taken, then `ret` -/

/-- The loop-head `bne a5, a2` NOT taken (`a5 = i = n = a2`): retires with `PC = pc + 4 = 0x10d44`. -/
theorem memset_step_bne_not_taken (stepNo : Nat) (state : State)
    (a2v retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64) (i : Nat)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d40) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? x15 = some (BitVec.ofNat 64 i))
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? x12 = some a2v)
    (heq : BitVec.ofNat 64 i = a2v) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d40) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8 = (0x00c79463 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (8#13, .Regidx 12#5, .Regidx 15#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bne_a5_a2_run _ privRead mseccfgBits mseccfgRead
  have hcond : Runs (bTypeTaken (.Regidx 12#5) (.Regidx 15#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      false := by
    have h := bTypeTaken_bne_run _ (BitVec.ofNat 64 i) a2v h15 h12
    rwa [show (BitVec.ofNat 64 i != a2v) = false by rw [heq]; simp] at h
  exact tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10d40) retired
    (8#13) (.Regidx 12#5) (.Regidx 15#5) .BNE inhibit config 0x63#8 0x94#8 0xc7#8 0x00#8
    platform noMMIO bytes interrupts base decode notExpected hcond hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- `ret` (`jalr x0, 0(ra)`) at `0x10d44`: retires with `PC = ra` (bit 0 cleared).  Fetch bytes are
`67 80 00 00` (`00008067`). -/
theorem memset_step_ret (stepNo : Nat) (state : State)
    (rs1Val retired mseccfgBits misaBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d44) 0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      rs1Val)
    (hbit1 : Sail.BitVec.access rs1Val 1 = 0#1)
    (hElp : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      ())
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d44)).regs.get? misa = some misaBits) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44)
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
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d44) 4) := by
    unfold get_next_pc; exact readReg_run _ nextPC _ (msCoreNextPc _ _)
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepRetRetires stepNo state (BitVec.ofNat 64 0x10d44) retired (.Regidx 1#5)
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d44) 4) rs1Val inhibit config 0x67#8 0x80#8 0x00#8 0x00#8
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected hElp hlink
    hrs1 hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Entry step lemma: `li a5, 0` -/

/-- The entry `li a5, 0` at `0x10d3c` (`a5 ↦ 0`), lifted through the generated `try_step`.  Fetch
bytes are `93 07 00 00` (`00000793`); `PC` ticks to the loop head `0x10d40`. -/
theorem memset_step_li (stepNo : Nat) (state : State) (retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d3c) 0x93#8 0x07#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d3c) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d3c)).regs.insert x15 (BitVec.ofNat 64 0) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d3c) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x07#8 0x00#8 0x00#8 = (0x00000793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x07#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_li_a5_0_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d3c))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d3c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d3c)).regs.insert x15 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 0#5) (.Regidx 15#5) .ADDI) _ _ _
    unfold Runs
    exact execute_li_a5_0 _
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d3c) retired inhibit config
    0x93#8 0x07#8 0x00#8 0x00#8 (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (msGpFrameNextPc _ _ x15 _ (by decide))
    (msGpFrameGet _ _ x15 _ hart_state (by decide) (by decide))
    (msGpFrameGet _ _ x15 _ minstret_increment (by decide) (by decide))
    (msGpFrameGet _ _ x15 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Deliverable: single-iteration advance `memset_adv` -/

set_option maxHeartbeats 1000000 in
/-- One loop iteration (`i < n`) is a length-5 trace that fills one more byte and re-establishes the
invariant at `i + 1`. -/
theorem memset_adv (dst n retAddr byteval : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (sInit : State) (start i : Nat) (s : State)
    (hi : i < n.toNat)
    (hInv : MemsetInv dst n retAddr byteval image mseccfgBits mstatusBits inhibit cfg sInit i s) :
    ∃ s', Trace (start + i * 5) 5 s s' ∧
      MemsetInv dst n retAddr byteval image mseccfgBits mstatusBits inhibit cfg sInit (i + 1) s' := by
  obtain ⟨retired0, hret0⟩ := hInv.hminstret
  have hi2 : i < 2 ^ 64 := Nat.lt_trans hi hInv.hnLt
  -- Step 0: bne a5,a2 taken (i ≠ n) at 0x10d40, target 0x10d48.
  have hbytes0 : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d40)
      0x63#8 0x94#8 0xc7#8 0x00#8 :=
    fetchBytesAt_10d40 (tryStepControlFlowAfterIncrement s) image hInv.himageEq hInv.hmatches
  have hplat0 : StepPlatform s (BitVec.ofNat 64 0x10d40) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits :=
    mkMsStepPlatform s mseccfgBits (BitVec.ofNat 64 0x10d40) 0x63#8 0x94#8 0xc7#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg (StableAgree.refl s)
      ((afterIncGet s PC (by decide)).trans hInv.hPC) (by decide) hbytes0
  have hcnt0 : StepCounters s retired0 inhibit cfg :=
    ⟨hInv.hhart, hInv.hinhibit, hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hret0⟩
  have h15_0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d40)).regs.get? x15 = some (BitVec.ofNat 64 i) :=
    (msCoreGetInc (tryStepControlFlowAfterIncrement s) _ x15 (by decide)).trans
      ((afterIncGet s x15 (by decide)).trans hInv.ha5)
  have h12_0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d40)).regs.get? x12 = some n :=
    (coreGetStable s _ x12 (by decide) (StableAgree.refl s)).trans hInv.ha2
  have hneq0 : BitVec.ofNat 64 i ≠ n := by
    intro heq
    have h1 : (BitVec.ofNat 64 i).toNat = n.toNat := by rw [heq]
    rw [BitVec.toNat_ofNat] at h1; omega
  have hpc0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d40)).regs.get? PC = some (BitVec.ofNat 64 0x10d40) :=
    (msCoreGetInc (tryStepControlFlowAfterIncrement s) _ PC (by decide)).trans
      ((afterIncGet s PC (by decide)).trans hInv.hPC)
  obtain ⟨misaBits0, _mstatus0, _pcr0, hmisaAfter0, _rest0⟩ := hplat0.1
  have hmisa0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d40)).regs.get? misa = some misaBits0 :=
    (msCoreGetInc (tryStepControlFlowAfterIncrement s) _ misa (by decide)).trans hmisaAfter0
  have hsum0 : (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) (8#13)) = BitVec.ofNat 64 0x10d48 := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have halign0 : Sail.BitVec.access (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) (8#13)) 0 = 0#1 := by
    rw [hsum0]; decide
  have hbit1_0 : Sail.BitVec.access (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) (8#13)) 1 = 0#1 := by
    rw [hsum0]; decide
  have h0 := memset_step_bne_taken (start + i * 5) s (BitVec.ofNat 64 0x10d40) n retired0
    mseccfgBits inhibit cfg i hplat0 hcnt0 h15_0 h12_0 hneq0 hpc0 misaBits0 hmisa0 halign0 hbit1_0
  have hSt1 : StableAgree s _ :=
    stableAgree_jump s (BitVec.ofNat 64 0x10d40) (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13)
      retired0
  have hPC1 := afterIncRetiredPC (controlFlowJumpState (tryStepControlFlowAfterIncrement s)
    (BitVec.ofNat 64 0x10d40) (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13))
    (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13) retired0
  have hmin1 := retiredMinstret (controlFlowJumpState (tryStepControlFlowAfterIncrement s)
    (BitVec.ofNat 64 0x10d40) (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13))
    (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13) retired0
  have hx15_1 : _ = some (BitVec.ofNat 64 i) :=
    (jumpRetiredGet s (BitVec.ofNat 64 0x10d40)
      (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13) retired0 x15
      (by decide) (by decide) (by decide) (by decide)).trans hInv.ha5
  have hmem1 : _ = s.mem :=
    (retiredMem (controlFlowJumpState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d40)
      (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13))
      (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13) retired0).trans
      (jumpMem s (BitVec.ofNat 64 0x10d40) (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13))
  generalize hgen1 : tryStepControlFlowAfterRetired (controlFlowJumpState
      (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d40)
      (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13))
      (BitVec.ofNat 64 0x10d40 + sign_extend (m := 64) 8#13) retired0 = s1
    at h0 hSt1 hPC1 hmin1 hx15_1 hmem1
  -- Step 1: add a4,a0,a5 (a4 = dst+i) at 0x10d48.
  have hbytes1 : FetchBytesAt (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d48)
      0x33#8 0x07#8 0xf5#8 0x00#8 :=
    fetchBytesAt_10d48 (tryStepControlFlowAfterIncrement s1) image hInv.himageEq
      (hmem1.symm ▸ hInv.hmatches)
  have hplat1 : StepPlatform s1 (BitVec.ofNat 64 0x10d48) 0x33#8 0x07#8 0xf5#8 0x00#8 mseccfgBits :=
    mkMsStepPlatform s1 mseccfgBits (BitVec.ofNat 64 0x10d48) 0x33#8 0x07#8 0xf5#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt1 (hsum0 ▸ hPC1) (by decide) hbytes1
  have hcnt1 : StepCounters s1 (Sail.BitVec.addInt retired0 1) inhibit cfg :=
    ⟨(hSt1 hart_state (by decide)).trans hInv.hhart,
      (hSt1 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt1 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin1⟩
  have h10_1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10d48)).regs.get? x10 = some dst :=
    (coreGetStable s1 _ x10 (by decide) hSt1).trans hInv.ha0
  have h15_1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10d48)).regs.get? x15 = some (BitVec.ofNat 64 i) :=
    (msCoreGetInc (tryStepControlFlowAfterIncrement s1) _ x15 (by decide)).trans
      ((afterIncGet s1 x15 (by decide)).trans hx15_1)
  have h1 := memset_step_add_a4 (start + i * 5 + 1) s1 dst (BitVec.ofNat 64 i)
    (Sail.BitVec.addInt retired0 1) mseccfgBits inhibit cfg hplat1 hcnt1 h10_1 h15_1
  have hSt2 : StableAgree s _ :=
    hSt1.trans (stableAgree_fallThrough s1 (BitVec.ofNat 64 0x10d48) (Sail.BitVec.addInt retired0 1)
      x14 (dst + BitVec.ofNat 64 i) (Or.inr (Or.inl rfl)))
  have hPC2 := afterIncRetiredPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d48) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
        (BitVec.ofNat 64 0x10d48)).regs.insert x14 (dst + BitVec.ofNat 64 i) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d48) 4) (Sail.BitVec.addInt retired0 1)
  have hmin2 := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d48) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
        (BitVec.ofNat 64 0x10d48)).regs.insert x14 (dst + BitVec.ofNat 64 i) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d48) 4) (Sail.BitVec.addInt retired0 1)
  have hx14_2 := fallThroughRetiredRd s1 (BitVec.ofNat 64 0x10d48) (Sail.BitVec.addInt retired0 1)
    x14 (dst + BitVec.ofNat 64 i) (by decide) (by decide)
  have hx15_2 : _ = some (BitVec.ofNat 64 i) :=
    (fallThroughRetiredGet s1 (BitVec.ofNat 64 0x10d48) (Sail.BitVec.addInt retired0 1) x14
      (dst + BitVec.ofNat 64 i) x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hx15_1
  have hmem2 : _ = s.mem :=
    (retiredMem
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d48) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
          (BitVec.ofNat 64 0x10d48)).regs.insert x14 (dst + BitVec.ofNat 64 i) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d48) 4) (Sail.BitVec.addInt retired0 1)).trans
      ((fallThroughMem s1 (BitVec.ofNat 64 0x10d48) x14 (dst + BitVec.ofNat 64 i)).trans hmem1)
  generalize hgen2 : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d48) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
          (BitVec.ofNat 64 0x10d48)).regs.insert x14 (dst + BitVec.ofNat 64 i) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d48) 4) (Sail.BitVec.addInt retired0 1) = s2
    at h1 hSt2 hPC2 hmin2 hx14_2 hx15_2 hmem2
  -- Step 2: sb a1,0(a4) (mem[dst+i] = low byte of a1) at 0x10d4c.
  have hsum48 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d48) 4 = BitVec.ofNat 64 0x10d4c := by decide
  have hbytes2 : FetchBytesAt (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10d4c)
      0x23#8 0x00#8 0xb7#8 0x00#8 :=
    fetchBytesAt_10d4c (tryStepControlFlowAfterIncrement s2) image hInv.himageEq
      (hmem2.symm ▸ hInv.hmatches)
  have hplat2 : StepPlatform s2 (BitVec.ofNat 64 0x10d4c) 0x23#8 0x00#8 0xb7#8 0x00#8 mseccfgBits :=
    mkMsStepPlatform s2 mseccfgBits (BitVec.ofNat 64 0x10d4c) 0x23#8 0x00#8 0xb7#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt2 (hsum48 ▸ hPC2) (by decide) hbytes2
  have hcnt2 : StepCounters s2 (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) inhibit cfg :=
    ⟨(hSt2 hart_state (by decide)).trans hInv.hhart,
      (hSt2 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt2 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin2⟩
  have hmstat2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10d4c)).regs.get? mstatus = some mstatusBits :=
    (coreGetStable s2 _ mstatus (by decide) hSt2).trans hInv.hmstatus
  have hpriv2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10d4c)).regs.get? cur_privilege = some Privilege.Machine :=
    (coreGetStable s2 _ cur_privilege (by decide) hSt2).trans hInv.hcur
  have hx11_2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10d4c)).regs.get? x11 = some byteval :=
    (coreGetStable s2 _ x11 (by decide) hSt2).trans hInv.ha1
  have hx14_at2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10d4c)).regs.get? x14 = some (dst + BitVec.ofNat 64 i) :=
    (msCoreGetInc (tryStepControlFlowAfterIncrement s2) _ x14 (by decide)).trans
      ((afterIncGet s2 x14 (by decide)).trans hx14_2)
  obtain ⟨addrReg2, physAccess2, noMMIOw2⟩ :=
    hInv.hdata i _ hi (coreStableAgree s2 (BitVec.ofNat 64 0x10d4c) hSt2) hx14_at2
  have hwrite2 := writeBytes_byte_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10d4c))
    (dst + BitVec.ofNat 64 i).toNat (BitVec.setWidth 8 byteval)
  have hs'mem : ({ coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
        (BitVec.ofNat 64 0x10d4c) with
      mem := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
        (BitVec.ofNat 64 0x10d4c)).mem.insert (dst + BitVec.ofNat 64 i).toNat
          (BitVec.setWidth 8 byteval) }).mem =
      s.mem.insert (dst + BitVec.ofNat 64 i).toNat (BitVec.setWidth 8 byteval) := by
    show (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
        (BitVec.ofNat 64 0x10d4c)).mem.insert (dst + BitVec.ofNat 64 i).toNat
          (BitVec.setWidth 8 byteval) =
        s.mem.insert (dst + BitVec.ofNat 64 i).toNat (BitVec.setWidth 8 byteval)
    rw [show (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10d4c)).mem = s.mem from hmem2]
  generalize hgens' : ({ coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
        (BitVec.ofNat 64 0x10d4c) with
      mem := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
        (BitVec.ofNat 64 0x10d4c)).mem.insert (dst + BitVec.ofNat 64 i).toNat
          (BitVec.setWidth 8 byteval) }) = s'
    at hwrite2 hs'mem
  have h2 := memset_step_sb (start + i * 5 + 2) s2 s' (dst + BitVec.ofNat 64 i) mstatusBits
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) mseccfgBits byteval
    (BitVec.setWidth 8 byteval) rfl inhibit cfg hplat2 hcnt2 hmstat2 hpriv2 hInv.hmprv hx11_2
    addrReg2 physAccess2 noMMIOw2 hwrite2
  have hregsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10d4c)).regs := by rw [← hgens']
  have hSt3 : StableAgree s _ :=
    hSt2.trans (stableAgree_sb s2 s' (BitVec.ofNat 64 0x10d4c)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) hregsEq)
  have hPC3 := afterIncRetiredPC s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d4c) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
  have hmin3 := retiredMinstret s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d4c) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
  have hx15_3 : _ = some (BitVec.ofNat 64 i) :=
    (sbRetiredGet s2 s' (BitVec.ofNat 64 0x10d4c)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) hregsEq x15
      (by decide) (by decide) (by decide) (by decide)).trans hx15_2
  have hmem3 : _ = s.mem.insert (dst + BitVec.ofNat 64 i).toNat (BitVec.setWidth 8 byteval) :=
    (retiredMem s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d4c) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)).trans hs'mem
  generalize hgen3 : tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d4c) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) = s3
    at h2 hSt3 hPC3 hmin3 hx15_3 hmem3
  -- Step 3: addi a5,a5,1 (i++) at 0x10d50.
  have hsum4c : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d4c) 4 = BitVec.ofNat 64 0x10d50 := by decide
  have hbytes3 : FetchBytesAt (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10d50)
      0x93#8 0x87#8 0x17#8 0x00#8 :=
    fetchBytesAt_10d50 (tryStepControlFlowAfterIncrement s3) image hInv.himageEq
      (hmem3.symm ▸ matchesMemory_insert image s.mem (dst + BitVec.ofNat 64 i).toNat
        (BitVec.setWidth 8 byteval) hInv.hmatches (hInv.hdstImg i hi))
  have hplat3 : StepPlatform s3 (BitVec.ofNat 64 0x10d50) 0x93#8 0x87#8 0x17#8 0x00#8 mseccfgBits :=
    mkMsStepPlatform s3 mseccfgBits (BitVec.ofNat 64 0x10d50) 0x93#8 0x87#8 0x17#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt3 (hsum4c ▸ hPC3) (by decide) hbytes3
  have hcnt3 : StepCounters s3
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) inhibit cfg :=
    ⟨(hSt3 hart_state (by decide)).trans hInv.hhart,
      (hSt3 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt3 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin3⟩
  have h15_3 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
      (BitVec.ofNat 64 0x10d50)).regs.get? x15 = some (BitVec.ofNat 64 i) :=
    (msCoreGetInc (tryStepControlFlowAfterIncrement s3) _ x15 (by decide)).trans
      ((afterIncGet s3 x15 (by decide)).trans hx15_3)
  have h3 := memset_step_addi_a5 (start + i * 5 + 3) s3 (BitVec.ofNat 64 i)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) mseccfgBits inhibit
    cfg hplat3 hcnt3 h15_3
  have hSt4 : StableAgree s _ :=
    hSt3.trans (stableAgree_fallThrough s3 (BitVec.ofNat 64 0x10d50)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x15
      (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) (Or.inr (Or.inr rfl)))
  have hPC4 := afterIncRetiredPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10d50) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
        (BitVec.ofNat 64 0x10d50)).regs.insert x15 (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d50) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
  have hmin4 := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10d50) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
        (BitVec.ofNat 64 0x10d50)).regs.insert x15 (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d50) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
  have hx15_4 := fallThroughRetiredRd s3 (BitVec.ofNat 64 0x10d50)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x15
    (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) (by decide) (by decide)
  have hmem4 : _ = s.mem.insert (dst + BitVec.ofNat 64 i).toNat (BitVec.setWidth 8 byteval) :=
    (retiredMem
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10d50) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
          (BitVec.ofNat 64 0x10d50)).regs.insert x15
            (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d50) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)).trans
      ((fallThroughMem s3 (BitVec.ofNat 64 0x10d50) x15
        (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12)).trans hmem3)
  generalize hgen4 : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10d50) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
          (BitVec.ofNat 64 0x10d50)).regs.insert x15
            (BitVec.ofNat 64 i + sign_extend (m := 64) 1#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d50) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) = s4
    at h3 hSt4 hPC4 hmin4 hx15_4 hmem4
  -- Step 4: j 0x10d40 (back-edge) at 0x10d54.
  have hsum50 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d50) 4 = BitVec.ofNat 64 0x10d54 := by decide
  have hbytes4 : FetchBytesAt (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10d54)
      0x6f#8 0xf0#8 0xdf#8 0xfe#8 :=
    fetchBytesAt_10d54 (tryStepControlFlowAfterIncrement s4) image hInv.himageEq
      (hmem4.symm ▸ matchesMemory_insert image s.mem (dst + BitVec.ofNat 64 i).toNat
        (BitVec.setWidth 8 byteval) hInv.hmatches (hInv.hdstImg i hi))
  have hplat4 : StepPlatform s4 (BitVec.ofNat 64 0x10d54) 0x6f#8 0xf0#8 0xdf#8 0xfe#8 mseccfgBits :=
    mkMsStepPlatform s4 mseccfgBits (BitVec.ofNat 64 0x10d54) 0x6f#8 0xf0#8 0xdf#8 0xfe#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt4 (hsum50 ▸ hPC4) (by decide) hbytes4
  have hcnt4 : StepCounters s4 (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
      (Sail.BitVec.addInt retired0 1) 1) 1) 1) inhibit cfg :=
    ⟨(hSt4 hart_state (by decide)).trans hInv.hhart,
      (hSt4 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt4 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hmin4⟩
  have h4 := memset_step_j (start + i * 5 + 4) s4 (Sail.BitVec.addInt (Sail.BitVec.addInt
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) 1) mseccfgBits inhibit cfg hplat4 hcnt4
  -- Assemble the 5-step trace and re-establish the invariant at i+1.
  have hSt5 : StableAgree s _ :=
    hSt4.trans (stableAgree_jump s4 (BitVec.ofNat 64 0x10d54)
      (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21))
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1))
  have hsumJ : (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21))
      = BitVec.ofNat 64 0x10d40 := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have hmemS5 : _ = s.mem.insert (dst + BitVec.ofNat 64 i).toNat (BitVec.setWidth 8 byteval) :=
    (retiredMem (controlFlowJumpState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10d54)
      (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)))
      (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21))
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1)).trans
      ((jumpMem s4 (BitVec.ofNat 64 0x10d54)
        (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21))).trans hmem4)
  have htr : Trace (start + i * 5) 5 s
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10d54)
          (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)))
        (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21))
        (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
          1) 1)) := by
    trace_steps [h0, h1, h2, h3, h4]
  refine ⟨_, htr, ?_⟩
  refine ⟨?hPC, ?ha5, ?ha0, ?ha1, ?ha2, ?hra, ?hcur, ?hmstatus, ?hmprv, ?hmseccfg, ?hhart,
      ?hinhibit, ?hnotInhibited, ?hcfg, ?hmachineEnabled, ?hminstret, ?himageEq, ?hmatches, ?hset,
      ?hle, ?hnLt, ?hdstFits, ?hdstImg, ?hplat, ?hdata, ?hElp, ?hstable, ?hframe⟩
  case hPC => rw [retiredGetPC _ _ _, hsumJ]
  case ha5 =>
    exact (jumpRetiredGet s4 (BitVec.ofNat 64 0x10d54)
      (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21))
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) x15 (by decide) (by decide) (by decide) (by decide)).trans
      (hx15_4.trans (congrArg some (ofNat_add_one i)))
  case ha0 => exact (hSt5 x10 (by decide)).trans hInv.ha0
  case ha1 => exact (hSt5 x11 (by decide)).trans hInv.ha1
  case ha2 => exact (hSt5 x12 (by decide)).trans hInv.ha2
  case hra => exact (hSt5 x1 (by decide)).trans hInv.hra
  case hcur => exact (hSt5 cur_privilege (by decide)).trans hInv.hcur
  case hmstatus => exact (hSt5 mstatus (by decide)).trans hInv.hmstatus
  case hmprv => exact hInv.hmprv
  case hmseccfg => exact (hSt5 mseccfg (by decide)).trans hInv.hmseccfg
  case hhart => exact (hSt5 hart_state (by decide)).trans hInv.hhart
  case hinhibit => exact (hSt5 mcountinhibit (by decide)).trans hInv.hinhibit
  case hnotInhibited => exact hInv.hnotInhibited
  case hcfg => exact (hSt5 minstretcfg (by decide)).trans hInv.hcfg
  case hmachineEnabled => exact hInv.hmachineEnabled
  case hminstret =>
    exact ⟨_, retiredMinstret (controlFlowJumpState (tryStepControlFlowAfterIncrement s4)
      (BitVec.ofNat 64 0x10d54) (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)))
      (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21))
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1)⟩
  case himageEq => exact hInv.himageEq
  case hmatches =>
    exact hmemS5.symm ▸ matchesMemory_insert image s.mem (dst + BitVec.ofNat 64 i).toNat
      (BitVec.setWidth 8 byteval) hInv.hmatches (hInv.hdstImg i hi)
  case hset =>
    intro j hj
    rw [hmemS5]
    have hfits := hInv.hdstFits
    rcases Nat.lt_or_ge j i with hlt | hge
    · have hfit_i : dst.toNat + i < 2 ^ 64 := by omega
      have hfit_j : dst.toNat + j < 2 ^ 64 := by omega
      have hne : (dst + BitVec.ofNat 64 i).toNat ≠ (dst + BitVec.ofNat 64 j).toNat := by
        rw [dstAddr_toNat dst i hfit_i, dstAddr_toNat dst j hfit_j]; omega
      rw [getInsertNe _ _ _ _ hne]; exact hInv.hset j hlt
    · have hji : j = i := by omega
      subst hji
      rw [getInsertEq]
  case hle => omega
  case hnLt => exact hInv.hnLt
  case hdstFits => exact hInv.hdstFits
  case hdstImg => exact hInv.hdstImg
  case hplat => exact MsAbstractPlatform.mono hSt5 hInv.hplat
  case hdata => exact AbstractStoreAccess.mono hSt5 hInv.hdata
  case hElp => exact AbstractElp.mono hSt5 hInv.hElp
  case hstable => exact hInv.hstable.trans hSt5
  case hframe => rw [hmemS5]; exact frame_insert_step hInv.hframe

/-! ## Deliverable: whole-loop trace `memset_loop` -/

/-- The whole byte-fill loop: `n` iterations from the `i = 0` loop head to the `i = n` loop head, a
length-`n * 5` trace establishing the invariant at `n` (all `n` bytes filled). -/
theorem memset_loop (dst n retAddr byteval : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (sInit : State) (start : Nat) (s0 : State)
    (hInv0 : MemsetInv dst n retAddr byteval image mseccfgBits mstatusBits inhibit cfg sInit 0 s0) :
    ∃ sN, Trace start (n.toNat * 5) s0 sN ∧
      MemsetInv dst n retAddr byteval image mseccfgBits mstatusBits inhibit cfg sInit n.toNat sN :=
  Trace.invariantIterate (L := 5) (start := start)
    (Inv := fun i s => MemsetInv dst n retAddr byteval image mseccfgBits mstatusBits inhibit cfg sInit i s)
    n.toNat
    (fun i s hi hInv => memset_adv dst n retAddr byteval image mseccfgBits mstatusBits inhibit cfg
      sInit start i s hi hInv)
    hInv0

/-! ## Deliverable: loop exit `memset_exit` -/

set_option maxHeartbeats 1000000 in
/-- After all `n` bytes are filled (`i = n`), the loop test falls through (`a5 = n`) and `ret`
returns: a 2-step trace to the caller with `PC = ra` (bit 0 cleared), all `n` bytes present at the
destination, and the arguments and code image preserved. -/
theorem memset_exit (dst n retAddr byteval : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (sInit : State) (start : Nat) (s : State)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hInv : MemsetInv dst n retAddr byteval image mseccfgBits mstatusBits inhibit cfg sInit n.toNat s) :
    ∃ s'', Trace start 2 s s'' ∧
      s''.regs.get? PC = some (Sail.BitVec.update retAddr 0 0#1) ∧
      (∀ j : Nat, j < n.toNat →
        s''.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (BitVec.setWidth 8 byteval)) ∧
      s''.regs.get? x10 = some dst ∧ s''.regs.get? x11 = some byteval ∧
      s''.regs.get? x12 = some n ∧ s''.regs.get? x1 = some retAddr ∧
      image.matchesMemory s''.mem ∧
      StableAgree sInit s'' ∧ MemFramed dst n sInit s'' := by
  obtain ⟨retired0, hret0⟩ := hInv.hminstret
  -- Step 0: bne a5,a2 NOT taken (a5 = n) at 0x10d40.
  have hbytes0 : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d40)
      0x63#8 0x94#8 0xc7#8 0x00#8 :=
    fetchBytesAt_10d40 (tryStepControlFlowAfterIncrement s) image hInv.himageEq hInv.hmatches
  have hplat0 : StepPlatform s (BitVec.ofNat 64 0x10d40) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits :=
    mkMsStepPlatform s mseccfgBits (BitVec.ofNat 64 0x10d40) 0x63#8 0x94#8 0xc7#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg (StableAgree.refl s)
      ((afterIncGet s PC (by decide)).trans hInv.hPC) (by decide) hbytes0
  have hcnt0 : StepCounters s retired0 inhibit cfg :=
    ⟨hInv.hhart, hInv.hinhibit, hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled, hret0⟩
  have h15_0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d40)).regs.get? x15 = some (BitVec.ofNat 64 n.toNat) :=
    (msCoreGetInc (tryStepControlFlowAfterIncrement s) _ x15 (by decide)).trans
      ((afterIncGet s x15 (by decide)).trans hInv.ha5)
  have h12_0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10d40)).regs.get? x12 = some n :=
    (coreGetStable s _ x12 (by decide) (StableAgree.refl s)).trans hInv.ha2
  have heq0 : BitVec.ofNat 64 n.toNat = n := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega
  have hb := memset_step_bne_not_taken start s n retired0 mseccfgBits inhibit cfg n.toNat
    hplat0 hcnt0 h15_0 h12_0 heq0
  have hSt1 : StableAgree s _ :=
    stableAgree_notTaken s (BitVec.ofNat 64 0x10d40) retired0
  have hPC1 := afterIncRetiredPC
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d40))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d40) 4) retired0
  have hmem1 : _ = s.mem := notTakenMem s (BitVec.ofNat 64 0x10d40) retired0
  have hmin1 := retiredMinstret
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d40))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d40) 4) retired0
  generalize hgen1 : tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d40))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d40) 4) retired0 = s1
    at hb hSt1 hPC1 hmem1 hmin1
  -- Step 1: ret at 0x10d44.
  have hsumL4 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d40) 4 = BitVec.ofNat 64 0x10d44 := by decide
  have hbytes1 : FetchBytesAt (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d44)
      0x67#8 0x80#8 0x00#8 0x00#8 :=
    fetchBytesAt_10d44 (tryStepControlFlowAfterIncrement s1) image hInv.himageEq
      (hmem1.symm ▸ hInv.hmatches)
  have hplat1 : StepPlatform s1 (BitVec.ofNat 64 0x10d44) 0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits :=
    mkMsStepPlatform s1 mseccfgBits (BitVec.ofNat 64 0x10d44) 0x67#8 0x80#8 0x00#8 0x00#8
      hInv.hplat hInv.hcur hInv.hmseccfg hSt1 (hsumL4 ▸ hPC1) (by decide) hbytes1
  have hcnt1 : StepCounters s1 (Sail.BitVec.addInt retired0 1) inhibit cfg :=
    ⟨(hSt1 hart_state (by decide)).trans hInv.hhart,
      (hSt1 mcountinhibit (by decide)).trans hInv.hinhibit,
      (hSt1 minstretcfg (by decide)).trans hInv.hcfg, hInv.hnotInhibited, hInv.hmachineEnabled,
      hmin1⟩
  have hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d44))
      retAddr :=
    rX_bits_x1_run _ retAddr ((coreGetStable s1 _ x1 (by decide) hSt1).trans hInv.hra)
  obtain ⟨misaBits1, _, _, hmisaA1, _⟩ := hplat1.1
  have hmisa1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10d44)).regs.get? misa = some misaBits1 :=
    (msCoreGetInc (tryStepControlFlowAfterIncrement s1) _ misa (by decide)).trans hmisaA1
  have hElp1 : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d44)) () :=
    hInv.hElp _ (.Regidx 1#5) rfl (coreStableAgree s1 (BitVec.ofNat 64 0x10d44) hSt1)
  have hr := memset_step_ret (start + 1) s1 retAddr (Sail.BitVec.addInt retired0 1) mseccfgBits
    misaBits1 inhibit cfg hplat1 hcnt1 hrs1 hretAlign hElp1 hmisa1
  have hSt2 : StableAgree s _ :=
    hSt1.trans (stableAgree_jump s1 (BitVec.ofNat 64 0x10d44)
      (Sail.BitVec.update retAddr 0 0#1) (Sail.BitVec.addInt retired0 1))
  have hmem2 : _ = s.mem :=
    (retiredMem (controlFlowJumpState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d44)
      (Sail.BitVec.update retAddr 0 0#1)) (Sail.BitVec.update retAddr 0 0#1)
      (Sail.BitVec.addInt retired0 1)).trans
      ((jumpMem s1 (BitVec.ofNat 64 0x10d44) (Sail.BitVec.update retAddr 0 0#1)).trans hmem1)
  have htr : Trace start 2 s
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10d44)
          (Sail.BitVec.update retAddr 0 0#1))
        (Sail.BitVec.update retAddr 0 0#1) (Sail.BitVec.addInt retired0 1)) :=
    Trace.step _ _ _ _ _ hb (Trace.one _ _ _ hr)
  refine ⟨_, htr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact retiredGetPC _ _ _
  · intro j hj; rw [hmem2]; exact hInv.hset j hj
  · exact (hSt2 x10 (by decide)).trans hInv.ha0
  · exact (hSt2 x11 (by decide)).trans hInv.ha1
  · exact (hSt2 x12 (by decide)).trans hInv.ha2
  · exact (hSt2 x1 (by decide)).trans hInv.hra
  · rw [hmem2]; exact hInv.hmatches
  · exact hInv.hstable.trans hSt2
  · intro addr h; rw [hmem2]; exact hInv.hframe addr h

/-! ## Deliverable: capstone contract `memset_contract` -/

set_option maxHeartbeats 1000000 in
/-- CAPSTONE.  `memset(dst, byteval, n)` at `0x10d3c`, run through the authoritative generated
`try_step` from a configured machine with the abstract store data-access precondition: a single
`1 + n*5 + 2`-step trace (entry `li` + loop + exit) to the caller, after which every destination byte
`mem[dst+j]` equals the stored low byte of `a1` (`= setWidth₈ byteval = a1 &&& 0xff`), the code image
and argument registers are preserved, and `PC = ra` (bit 0 cleared). -/
theorem memset_contract (dst n retAddr byteval : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (start : Nat) (s : State)
    (hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10d3c))
    (ha0 : s.regs.get? x10 = some dst) (ha1 : s.regs.get? x11 = some byteval)
    (ha2 : s.regs.get? x12 = some n) (hra : s.regs.get? x1 = some retAddr)
    (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmstatus : s.regs.get? mstatus = some mstatusBits) (hmprv : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hhart : s.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hinhibit : s.regs.get? mcountinhibit = some inhibit) (hnotInhibited : _get_Counterin_IR inhibit = 0#1)
    (hcfg : s.regs.get? minstretcfg = some cfg) (hmachineEnabled : _get_CountSmcntrpmf_MINH cfg = 0#1)
    (hminstret : ∃ v, s.regs.get? minstret = some v)
    (himageEq : Artifact.programImage = .ok image) (hmatches : image.matchesMemory s.mem)
    (hnLt : n.toNat < 2 ^ 64) (hdstFits : dst.toNat + n.toNat ≤ 2 ^ 64)
    (hdstImg : ∀ j : Nat, j < n.toNat → image.readByte? (dst + BitVec.ofNat 64 j).toNat = none)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hplat : MsAbstractPlatform s) (hdata : AbstractStoreAccess n dst s) (hElp : AbstractElp s) :
    ∃ s'', Trace start (1 + n.toNat * 5 + 2) s s'' ∧
      s''.regs.get? PC = some (Sail.BitVec.update retAddr 0 0#1) ∧
      (∀ j : Nat, j < n.toNat →
        s''.mem.get? (dst + BitVec.ofNat 64 j).toNat = some (BitVec.setWidth 8 byteval)) ∧
      s''.regs.get? x10 = some dst ∧ s''.regs.get? x11 = some byteval ∧
      s''.regs.get? x12 = some n ∧ s''.regs.get? x1 = some retAddr ∧
      image.matchesMemory s''.mem ∧
      -- Compositional framing (Deliverables 1, 3, 4):
      -- every register outside `W` is preserved (in particular `x2`/`sp`, a leaf function),
      StableAgree s s'' ∧ s''.regs.get? x2 = s.regs.get? x2 ∧
      -- and memory changes only inside the destination window `[dst, dst+n)`.
      MemFramed dst n s s'' := by
  obtain ⟨retired0, hret0⟩ := hminstret
  -- Entry: li a5, 0 at 0x10d3c.
  have hbytesE : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d3c)
      0x93#8 0x07#8 0x00#8 0x00#8 :=
    fetchBytesAt_10d3c (tryStepControlFlowAfterIncrement s) image himageEq hmatches
  have hplatE : StepPlatform s (BitVec.ofNat 64 0x10d3c) 0x93#8 0x07#8 0x00#8 0x00#8 mseccfgBits :=
    mkMsStepPlatform s mseccfgBits (BitVec.ofNat 64 0x10d3c) 0x93#8 0x07#8 0x00#8 0x00#8
      hplat hcur hmseccfg (StableAgree.refl s)
      ((afterIncGet s PC (by decide)).trans hPC) (by decide) hbytesE
  have hcntE : StepCounters s retired0 inhibit cfg :=
    ⟨hhart, hinhibit, hcfg, hnotInhibited, hmachineEnabled, hret0⟩
  have hli := memset_step_li start s retired0 mseccfgBits inhibit cfg hplatE hcntE
  have hSt0 : StableAgree s _ :=
    stableAgree_fallThrough s (BitVec.ofNat 64 0x10d3c) retired0 x15 (BitVec.ofNat 64 0)
      (Or.inr (Or.inr rfl))
  have hsum3c : Sail.BitVec.addInt (BitVec.ofNat 64 0x10d3c) 4 = BitVec.ofNat 64 0x10d40 := by decide
  -- The i = 0 loop-head invariant at the post-entry state.
  have hInv0 : MemsetInv dst n retAddr byteval image mseccfgBits mstatusBits inhibit cfg s 0
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d3c) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
            (BitVec.ofNat 64 0x10d3c)).regs.insert x15 (BitVec.ofNat 64 0) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d3c) 4) retired0) := by
    refine ⟨?_, ?_, (hSt0 x10 (by decide)).trans ha0, (hSt0 x11 (by decide)).trans ha1,
      (hSt0 x12 (by decide)).trans ha2, (hSt0 x1 (by decide)).trans hra,
      (hSt0 cur_privilege (by decide)).trans hcur, (hSt0 mstatus (by decide)).trans hmstatus, hmprv,
      (hSt0 mseccfg (by decide)).trans hmseccfg, (hSt0 hart_state (by decide)).trans hhart,
      (hSt0 mcountinhibit (by decide)).trans hinhibit, hnotInhibited,
      (hSt0 minstretcfg (by decide)).trans hcfg, hmachineEnabled, ⟨_, retiredMinstret _ _ _⟩,
      himageEq, ?_, ?_, Nat.zero_le _, hnLt, hdstFits, hdstImg,
      MsAbstractPlatform.mono hSt0 hplat, AbstractStoreAccess.mono hSt0 hdata,
      AbstractElp.mono hSt0 hElp, hSt0, ?_⟩
    · rw [retiredGetPC _ _ _, hsum3c]
    · exact (fallThroughRetiredRd s (BitVec.ofNat 64 0x10d3c) retired0 x15 (BitVec.ofNat 64 0)
        (by decide) (by decide))
    · have hmemE : (tryStepControlFlowAfterRetired
          { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d3c) with
            regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
              (BitVec.ofNat 64 0x10d3c)).regs.insert x15 (BitVec.ofNat 64 0) }
          (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d3c) 4) retired0).mem = s.mem :=
        (retiredMem _ _ _).trans (fallThroughMem s (BitVec.ofNat 64 0x10d3c) x15 (BitVec.ofNat 64 0))
      rw [hmemE]; exact hmatches
    · intro j hj; exact absurd hj (Nat.not_lt_zero j)
    · intro addr _
      have hmemE : (tryStepControlFlowAfterRetired
          { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10d3c) with
            regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
              (BitVec.ofNat 64 0x10d3c)).regs.insert x15 (BitVec.ofNat 64 0) }
          (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d3c) 4) retired0).mem = s.mem :=
        (retiredMem _ _ _).trans (fallThroughMem s (BitVec.ofNat 64 0x10d3c) x15 (BitVec.ofNat 64 0))
      rw [hmemE]
  -- Loop.
  obtain ⟨sN, htrLoop, hInvN⟩ := memset_loop dst n retAddr byteval image mseccfgBits mstatusBits
    inhibit cfg s (start + 1) _ hInv0
  -- Exit.
  obtain ⟨s'', htrExit, hPCret, hsetN, hx10, hx11, hx12, hx1N, hmatchesN, hStableExit, hFrameExit⟩ :=
    memset_exit dst n retAddr byteval image mseccfgBits mstatusBits inhibit cfg s
      (start + (1 + n.toNat * 5)) sN hretAlign hInvN
  refine ⟨s'', ?_, hPCret, hsetN, hx10, hx11, hx12, hx1N, hmatchesN,
    hStableExit, hStableExit x2 (by decide), hFrameExit⟩
  have htrLi := Trace.one _ _ _ hli
  have hcomb := Trace.append (Trace.append htrLi htrLoop) htrExit
  simpa using hcomb

end BinaryFv.Keccak
