import BinaryFv.Keccak.Reth.Proof.Helpers.Memcpy
import BinaryFv.Keccak.Reth.Proof.Helpers.CopyFromSliceDispatch
import BinaryFv.RiscV.Instruction.Execute.RegisterOp

/-!
# The equal-length `copy_from_slice_impl` (0x10c44) contract, through the authoritative `try_step`

`copy_from_slice_impl` (verified disassembly, ABI `a0 = dst_ptr`, `a1 = dst_len`, `a2 = src_ptr`,
`a3 = src_len`) is a *straight-line* argument-renaming shim that tail-calls `memcpy`:

```
0x10c44 mv   a4,a1          ; a4 = dst_len
0x10c48 bne  a1,a3,0x10c5c  ; length-mismatch test → panic branch (UNREACHABLE when a1 == a3)
0x10c4c mv   a1,a2          ; a1 = src_ptr
0x10c50 mv   a2,a4          ; a2 = len   (= original dst_len)
0x10c54 auipc t1,0x0        ; t1 = 0x10c54
0x10c58 jr   196(t1)        ; jump to t1+196 = 0x10d18 = memcpy
--- panic branch 0x10c5c..0x10c68 : NEVER EXECUTED on the equal-length path ---
```

This file proves the **equal-length** case (`a1 == a3`).  The `bne` at `0x10c48` compares
`a1 (= dst_len)` against `a3 (= src_len)`; when they are equal it is **not taken**, so the trace
follows `0x10c48 → 0x10c4c`, threading the three `mv`s, the `auipc`, and the `jr` tail-call into
`memcpy` at `0x10d18`.  The panic branch (`0x10c5c..0x10c68 → 0x100f0`) is therefore **demonstrably
avoided**: the assembled `Trace` steps from `0x10c48` to `0x10c4c` and never visits `0x10c5c`, and
the panic-branch decode/execute reductions are never invoked.

After the setup the machine holds `memcpy`'s calling convention (`a0 = dst_ptr`, `a1 = src_ptr`,
`a2 = len`), so the 6-instruction setup trace composes with `memcpy_contract`'s trace via
`Trace.append`.  The genuine platform / data-access preconditions of both the setup fetches and the
`memcpy` body are carried *abstractly*, exactly the stage-2 trust boundary: the setup's
`Cfs*`-flavoured abstract premises (about the entry state) transport, purely at the `StableAgree`
level, into `memcpy`'s abstract premises about the post-setup state.  No genuine PMP/PMA obligation
is discharged here, so the axiom footprint stays the XOR/fetch baseline.
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Local register read/write reductions for the copy_from_slice live path -/

/-- Writing `t1 = x6` via `wX_bits` inserts `x6 ↦ data` and touches nothing else (mirror of
`wX_bits_x13_run`). -/
theorem wX_bits_x6_run (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 6#5) data) s { s with regs := s.regs.insert x6 data } () := by
  have r6Nat : (Sail.BitVec.toNatInt 6#5).toNat = 6 := by decide
  unfold Runs
  simp [wX_bits, wX, PreSail.writeReg, r6Nat,
    EStateM.run, EStateM.bind, EStateM.modifyGet, EStateM.pure, EStateM.instMonad,
    MonadState.modifyGet, MonadStateOf.modifyGet, modify,
    xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
    encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
    LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg]

/-- Reading `a1 = x11` via `rX_bits`. -/
theorem rX_bits_x11_run (s : State) (v : BitVec 64) (h : s.regs.get? x11 = some v) :
    Runs (rX_bits (.Regidx 11#5)) s s v := by
  have r11 : (Sail.BitVec.toNatInt (11#5)).toNat = 11 := by decide
  unfold Runs
  simp [rX_bits, rX, r11, h, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

/-- Reading `t1 = x6` via `rX_bits`. -/
theorem rX_bits_x6_run (s : State) (v : BitVec 64) (h : s.regs.get? x6 = some v) :
    Runs (rX_bits (.Regidx 6#5)) s s v := by
  have r6 : (Sail.BitVec.toNatInt (6#5)).toNat = 6 := by decide
  unfold Runs
  simp [rX_bits, rX, r6, h, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

/-- The `bne a1, a3` branch condition (`.BNE`, `rs1 = a1 = x11`, `rs2 = a3 = x13`) runs to
`a1 != a3`. -/
theorem bTypeTaken_bne_a1_a3_run (s : State) (a1v a3v : BitVec 64)
    (h11 : s.regs.get? x11 = some a1v) (h13 : s.regs.get? x13 = some a3v) :
    Runs (bTypeTaken (.Regidx 13#5) (.Regidx 11#5) .BNE) s s (a1v != a3v) := by
  unfold bTypeTaken
  refine Runs.bind (rX_bits_x11_run s a1v h11) ?_
  refine Runs.bind (rX_bits_x13_run s a3v h13) ?_
  rfl

/-- `sign_extend` of `0#12` vanishes, so `mv rd, rs1 = addi rd, rs1, 0` writes `rs1` unchanged. -/
theorem add_sext_zero (x : BitVec 64) : x + sign_extend (m := 64) (0#12) = x := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  bv_decide

/-- The `auipc t1, 0x0` immediate is zero: `v + sext(0#20 ++ 0x000#12) = v`. -/
theorem add_auipc_zero (x : BitVec 64) :
    x + sign_extend (m := 64) (0#20 ++ 0x000#12) = x := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  bv_decide

/-! ## Fall-through register-file framing (local copies of the memcpy private helpers) -/

/-- The `nextPC` slot of the post-execute state of a GP-writing fall-through instruction is `pc+4`. -/
private theorem gpNextPc (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
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
private theorem gpGet (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (r : Register) (hrd : r ≠ rd) (hnp : r ≠ nextPC) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? r = Y.regs.get? r := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? r
      = (coreControlFlowNextState Y pc).regs.get? r :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd r v hrd
    _ = Y.regs.get? r := by
        simpa [coreControlFlowNextState] using
          writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

/-- `nextPC` slot of `coreControlFlowNextState Y pc` is `pc + 4`. -/
private theorem coreNextPc (Y : State) (pc : BitVec 64) :
    (coreControlFlowNextState Y pc).regs.get? nextPC = some (Sail.BitVec.addInt pc 4) := by
  change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- Any register other than `nextPC` reads through `coreControlFlowNextState Y pc` back to `Y`. -/
private theorem coreGetInc' (Y : State) (pc : BitVec 64) (r : Register) (hnp : r ≠ nextPC) :
    (coreControlFlowNextState Y pc).regs.get? r = Y.regs.get? r := by
  simpa [coreControlFlowNextState] using
    writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

/-- Any register untouched by a not-taken-branch retirement reads through to the pre-state `base`. -/
private theorem notTakenGet (base : State) (pc ret : BitVec 64) (r : Register)
    (hPC : r ≠ PC) (hmr : r ≠ minstret) (hnp : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret).regs.get? r = base.regs.get? r :=
  (retiredFrameGet _ _ _ r hPC hmr).trans
    ((coreGetInc' _ pc r hnp).trans (afterIncGet base r hmi))

/-! ## `jr` (general-immediate `jalr rd = x0`) through the generated `try_step`

`tryStepRetRetires` fixes the `jalr` immediate to `0`; the copy_from_slice tail-call `jr 196(t1)` is
`jalr x0, 196(t1)` with a *general* immediate, so we package the general case here.  The jump target
is `(rs1Val + sext imm)` with bit 0 cleared (`Sail.BitVec.update _ 0 0#1`), the link write to `x0`
is discarded, and everything else mirrors `tryStepRetRetires`. -/

/-- Writing register `x0` (`zreg`) is a no-op (local copy of the stage-3 private lemma). -/
private theorem wX_bits_zero_run (s : State) (data : BitVec 64) :
    Runs (wX_bits zreg data) s s () := by
  unfold wX_bits zreg wX
  rfl

/-- `jr imm(rs1)` = `jalr x0, imm(rs1)`, lifted through the `execute` dispatcher: reads the link and
`rs1`, forms the target `(rs1 + sext imm)` with bit 0 cleared, and discards the `x0` link. -/
theorem executeJrDispatchRuns (s : State) (imm : BitVec 12) (rs1 : regidx)
    (linkVal rs1Val : BitVec 64)
    (helpElp : Runs (update_elp_state rs1) s s ())
    (hlink : Runs (get_next_pc ()) s s linkVal)
    (hrs1 : Runs (rX_bits rs1) s s rs1Val)
    (hbit1 : Sail.BitVec.access (rs1Val + sign_extend (m := 64) imm) 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) s s zcaEnabled) :
    Runs (execute (.JALR (imm, rs1, zreg))) s
      { s with regs :=
        s.regs.insert nextPC (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) }
      (.Retire_Success ()) := by
  change Runs (execute_JALR imm rs1 zreg) s _ _
  exact execute_JALR_run s _ imm rs1 zreg linkVal rs1Val helpElp hlink hrs1 hbit1 zcaEnabled hzca
    (wX_bits_zero_run _ linkVal)

/--
Lift the general-immediate `jr imm(rs1)` (`jalr x0, imm(rs1)`) through the authoritative generated
`try_step`.  Structurally identical to `tryStepRetRetires`, but keeping `imm` general: the jump
overwrites `nextPC` with `(rs1Val + sext imm)` bit-0-cleared, the `x0` link write is discarded, so
the final state has `nextPC = PC = (rs1Val + sext imm) with bit 0 cleared`, `minstret = retired+1`,
`minstret_increment = true`, all other registers preserved.
-/
theorem tryStepJrRetires (stepNo : Nat) (state : State)
    (pc retired : BitVec 64) (rs1 : regidx) (imm : BitVec 12) (linkVal rs1Val : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (zcaEnabled : Bool)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (imm, rs1, zreg)))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (helpElp : Runs (update_elp_state rs1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) ())
    (hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) linkVal)
    (hrs1 : Runs (rX_bits rs1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) rs1Val)
    (hbit1 : Sail.BitVec.access (rs1Val + sign_extend (m := 64) imm) 1 = 0#1)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) zcaEnabled)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
          (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1))
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) retired) false := by
  have exec : Runs (execute (.JALR (imm, rs1, zreg)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)) (.Retire_Success ()) := by
    unfold controlFlowJumpState
    exact executeJrDispatchRuns
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) imm rs1 linkVal rs1Val
      helpElp hlink hrs1 hbit1 zcaEnabled hzca
  have active := runHartActiveControlFlow stepNo (tryStepControlFlowAfterIncrement state)
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)) pc byte0 byte1 byte2 byte3
    (.JALR (imm, rs1, zreg)) platform noMMIO bytes interrupts base decode notExpected exec
  have nextPcAfterExec :
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)).regs.get? nextPC =
        some (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) := by
    change ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert nextPC
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)).get? nextPC =
        some (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have agree : ∀ r : Register, r ≠ nextPC →
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)).regs.get? r =
        (tryStepControlFlowAfterIncrement state).regs.get? r := by
    intro r hr
    calc
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
          (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)).regs.get? r =
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? r := by
            simpa [controlFlowJumpState] using
              writeReg_read_unchanged
                (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) nextPC r
                (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) hr
      _ = (tryStepControlFlowAfterIncrement state).regs.get? r := by
            simpa [coreControlFlowNextState] using
              writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC r
                (Sail.BitVec.addInt pc 4) hr
  rcases platform with ⟨_, _, _, _, _, privilegeAfterInc, _⟩
  exact tryStepControlFlowRetires stepNo state
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1))
    (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) retired inhibit config
    (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3)) privilegeAfterInc active
    nextPcAfterExec agree hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Abstract setup premises and transport into `memcpy`'s abstract premises

The setup steps rename `a1`/`a2` and clobber `t1 = x6`, so the post-setup state does *not*
`StableAgree` (in `memcpy`'s sense, `NonW`) with the entry state: `x6`, `x11`, `x12` change.  We
carry the setup's abstract platform / data-access / landing-pad premises about the entry state `s`
under `CfsStableAgree` — agreement on every `NonW` register *except* `x6`, `x11`, `x12`.  Every setup
write lands in `memcpy`'s `W ∪ {x6, x11, x12}`, so `CfsStableAgree s s_k` is preserved across all
setup steps, and the post-setup state `s6` satisfies `CfsStableAgree s s6`.  The transport lemmas
then discharge `memcpy`'s `AbstractPlatform s6` / `AbstractDataAccess … s6` / `AbstractElp s6` purely
at the `StableAgree` level, never unfolding a genuine platform obligation. -/

/-- Two states agree on every register the setup does not clobber: `NonW` and not in
`{x6, x11, x12}`.  (The setup writes `x14 ∈ W`, `x11`, `x12`, `x6`, and the control registers, all
outside this set.) -/
def CfsStableAgree (base t : State) : Prop :=
  ∀ r : Register, NonW r → r ≠ x6 → r ≠ x11 → r ≠ x12 → t.regs.get? r = base.regs.get? r

theorem CfsStableAgree.refl (s : State) : CfsStableAgree s s := fun _ _ _ _ _ => rfl

/-- `CfsStableAgree` survives the generated counter-increment write. -/
theorem CfsStableAgree.afterInc {base t : State} (h : CfsStableAgree base t) :
    CfsStableAgree base (tryStepControlFlowAfterIncrement t) :=
  fun r hr hr6 hr11 hr12 => (afterIncGet t r hr.2.2.2.1).trans (h r hr hr6 hr11 hr12)

/-- `CfsStableAgree` lifts through the counter-increment and `nextPC` writes of the execute state. -/
theorem cfsCoreStableAgree {s : State} (s_k : State) (pc : BitVec 64)
    (hSt : CfsStableAgree s s_k) :
    CfsStableAgree s (coreControlFlowNextState (tryStepControlFlowAfterIncrement s_k) pc) :=
  fun r hr hr6 hr11 hr12 =>
    (coreGetInc' (tryStepControlFlowAfterIncrement s_k) pc r hr.2.1).trans
      ((afterIncGet s_k r hr.2.2.2.1).trans (hSt r hr hr6 hr11 hr12))

/-- The fetch addresses reachable in this contract: the 6 copy_from_slice setup addresses plus every
`memcpy` fetch address (`IsBodyPc`), positioned to satisfy both the setup fetches and — after
transport — the `memcpy` body fetches. -/
@[reducible] def IsCfsPc (pc : BitVec 64) : Prop :=
  pc = BitVec.ofNat 64 0x10c44 ∨ pc = BitVec.ofNat 64 0x10c48 ∨ pc = BitVec.ofNat 64 0x10c4c ∨
  pc = BitVec.ofNat 64 0x10c50 ∨ pc = BitVec.ofNat 64 0x10c54 ∨ pc = BitVec.ofNat 64 0x10c58 ∨
  IsBodyPc pc

/-- Abstract configured-machine fetch/decode platform for the setup and `memcpy` fetch addresses,
quantified over `CfsStableAgree`-equal states.  Never discharged here (the stage-2 trust boundary). -/
def CfsAbstractPlatform (base : State) : Prop :=
  ∀ (t : State) (pc : BitVec 64), CfsStableAgree base t → t.regs.get? PC = some pc → IsCfsPc pc →
    FetchBasePlatform t pc ∧ FetchMemoryNoMMIO t pc ∧ InterruptDisabled t ∧ LandingPadNotExpected t

/-- Abstract load/store data-access preconditions for the `memcpy` tail-call, quantified over
`CfsStableAgree`-equal states.  Same body as `memcpy`'s `AbstractDataAccess`, weakened to
`CfsStableAgree`.  Never discharged here (the stage-2 trust boundary). -/
def CfsAbstractDataAccess (n dst src : BitVec 64) (base : State) : Prop :=
  ∀ (j : Nat) (t : State), j < n.toNat → CfsStableAgree base t →
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

/-- Abstract Zicfilp landing-pad update, quantified over the register operand (`t1` for the `jr`
tail-call, `ra` for `memcpy`'s `ret`) and over `CfsStableAgree`-equal states.  Never discharged here
(the stage-2 trust boundary). -/
def CfsAbstractElp (base : State) : Prop :=
  ∀ (t : State) (rs1 : regidx), CfsStableAgree base t → Runs (update_elp_state rs1) t t ()

/-- Transport the setup platform premise (about the entry state `s`) into `memcpy`'s
`AbstractPlatform` about the post-setup state `s6`, given `CfsStableAgree s s6`. -/
theorem cfsPlatformTransport {s s6 : State} (hpres : CfsStableAgree s s6)
    (h : CfsAbstractPlatform s) : AbstractPlatform s6 := by
  intro t pc hSt hPC hbody
  exact h t pc (fun r hr hr6 hr11 hr12 => (hSt r hr).trans (hpres r hr hr6 hr11 hr12)) hPC
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbody))))))

/-- Transport the setup data-access premise into `memcpy`'s `AbstractDataAccess` about `s6`. -/
theorem cfsDataTransport {n dst src : BitVec 64} {s s6 : State} (hpres : CfsStableAgree s s6)
    (h : CfsAbstractDataAccess n dst src s) : AbstractDataAccess n dst src s6 := by
  intro j t hj hSt
  exact h j t hj (fun r hr hr6 hr11 hr12 => (hSt r hr).trans (hpres r hr hr6 hr11 hr12))

/-- Transport the setup landing-pad premise into `memcpy`'s `AbstractElp` about `s6` (for `ra`). -/
theorem cfsElpTransport {s s6 : State} (hpres : CfsStableAgree s s6)
    (h : CfsAbstractElp s) : AbstractElp s6 := by
  intro t r hr hSt
  subst hr
  exact h t (.Regidx 1#5) (fun r hr hr6 hr11 hr12 => (hSt r hr).trans (hpres r hr hr6 hr11 hr12))

/-- Assemble a `StepPlatform` bundle for a setup fetch address from the abstract setup platform. -/
theorem mkCfsStepPlatform {s : State} (s_k : State) (mseccfgBits pc : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hplat : CfsAbstractPlatform s) (hcur : s.regs.get? cur_privilege = some Privilege.Machine)
    (hmseccfg : s.regs.get? mseccfg = some mseccfgBits)
    (hSt : CfsStableAgree s s_k)
    (hPCafter : (tryStepControlFlowAfterIncrement s_k).regs.get? PC = some pc)
    (hbody : IsCfsPc pc)
    (hbytes : FetchBytesAt (tryStepControlFlowAfterIncrement s_k) pc b0 b1 b2 b3) :
    StepPlatform s_k pc b0 b1 b2 b3 mseccfgBits := by
  have hStA : CfsStableAgree s (tryStepControlFlowAfterIncrement s_k) := hSt.afterInc
  obtain ⟨hfbp, hmmio, hint, hlp⟩ := hplat _ pc hStA hPCafter hbody
  exact ⟨hfbp, hmmio, hbytes, hint, hlp,
    (hStA cur_privilege (by decide) (by decide) (by decide) (by decide)).trans hcur,
    (hStA mseccfg (by decide) (by decide) (by decide) (by decide)).trans hmseccfg⟩

/-! ### `CfsStableAgree` preservation across the setup step shapes -/

/-- A GP-writing fall-through (`rd ∈ {x6, x11, x12, x14}`) preserves `CfsStableAgree`. -/
theorem cfsAgree_fallThrough (s base : State) (pc ret : BitVec 64) (rd : Register)
    (v : RegisterType rd) (hrd : ∀ r, NonW r → r ≠ x6 → r ≠ x11 → r ≠ x12 → r ≠ rd)
    (h : CfsStableAgree s base) :
    CfsStableAgree s (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc).regs.insert
          rd v }
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr hr6 hr11 hr12
  exact (fallThroughRetiredGet base pc ret rd v r hr.1 hr.2.2.1 (hrd r hr hr6 hr11 hr12) hr.2.1
    hr.2.2.2.1).trans (h r hr hr6 hr11 hr12)

/-- A not-taken branch preserves `CfsStableAgree`. -/
theorem cfsAgree_notTaken (s base : State) (pc ret : BitVec 64) (h : CfsStableAgree s base) :
    CfsStableAgree s (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret) := by
  intro r hr hr6 hr11 hr12
  exact (retiredFrameGet _ _ _ r hr.1 hr.2.2.1).trans
    ((coreGetInc' _ pc r hr.2.1).trans ((afterIncGet base r hr.2.2.2.1).trans
      (h r hr hr6 hr11 hr12)))

/-- A taken branch / jump preserves `CfsStableAgree`. -/
theorem cfsAgree_jump (s base : State) (pc target ret : BitVec 64) (h : CfsStableAgree s base) :
    CfsStableAgree s (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement base) pc target) target ret) := by
  intro r hr hr6 hr11 hr12
  exact (jumpRetiredGet base pc target ret r hr.1 hr.2.2.1 hr.2.1 hr.2.2.2.1).trans
    (h r hr hr6 hr11 hr12)

/-- Compose the setup's `CfsStableAgree` with `memcpy`'s (stronger) `StableAgree`: `memcpy` only
writes registers in `W`, so their composition still agrees off `W ∪ {x6, x11, x12}` — the honest
whole-`copy_from_slice` register postcondition (the setup does clobber `x6`, `x11`, `x12`). -/
theorem cfsAgree_compose {s s6 s' : State} (h1 : CfsStableAgree s s6) (h2 : StableAgree s6 s') :
    CfsStableAgree s s' :=
  fun r hr hr6 hr11 hr12 => (h2 r hr).trans (h1 r hr hr6 hr11 hr12)

/-! ## The six setup step lemmas -/

/-- Step 1: `mv a4, a1` at `0x10c44` (`a4 = dst_len`).  Fetch bytes `13 87 05 00` (`00058713`);
writes `x14 ↦ a1Val + sext 0`. -/
theorem cfs_step_mv_a4_a1 (stepNo : Nat) (state : State)
    (a1Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c44) 0x13#8 0x87#8 0x05#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c44)).regs.get? x11 = some a1Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c44) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c44)).regs.insert x14 (a1Val + sign_extend (m := 64) 0#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c44) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x13#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x13#8 0x87#8 0x05#8 0x00#8 = (0x00058713 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x87#8 0x05#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 11#5, .Regidx 14#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_mv_a4_a1_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (0#12, .Regidx 11#5, .Regidx 14#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c44))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c44) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c44)).regs.insert x14 (a1Val + sign_extend (m := 64) 0#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 11#5) (.Regidx 14#5) .ADDI) _ _ _
    unfold Runs
    exact execute_mv_a4_a1 _ a1Val h11
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10c44) retired inhibit config
    0x13#8 0x87#8 0x05#8 0x00#8 (.ITYPE (0#12, .Regidx 11#5, .Regidx 14#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpNextPc _ _ x14 _ (by decide))
    (gpGet _ _ x14 _ hart_state (by decide) (by decide))
    (gpGet _ _ x14 _ minstret_increment (by decide) (by decide))
    (gpGet _ _ x14 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Step 2: `bne a1, a3, 0x10c5c` at `0x10c48`, NOT taken (`a1 = a3`).  Fetch bytes `63 9a d5 00`
(`00d59a63`); retires with `PC = pc + 4 = 0x10c4c`, skipping the panic branch. -/
theorem cfs_step_bne_not_taken (stepNo : Nat) (state : State)
    (a1v a3v retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c48) 0x63#8 0x9a#8 0xd5#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c48)).regs.get? x11 = some a1v)
    (h13 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c48)).regs.get? x13 = some a3v)
    (heq : a1v = a3v) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c48))
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c48) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x9a#8 0xd5#8 0x00#8 = (0x00d59a63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x9a#8 0xd5#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (20#13, .Regidx 13#5, .Regidx 11#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bne_a1_a3_run _ privRead mseccfgBits mseccfgRead
  have hcond : Runs (bTypeTaken (.Regidx 13#5) (.Regidx 11#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c48))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c48))
      false := by
    have h := bTypeTaken_bne_a1_a3_run _ a1v a3v h11 h13
    rwa [show (a1v != a3v) = false by rw [heq]; simp] at h
  exact tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10c48) retired
    (20#13) (.Regidx 13#5) (.Regidx 11#5) .BNE inhibit config 0x63#8 0x9a#8 0xd5#8 0x00#8
    platform noMMIO bytes interrupts base decode notExpected hcond hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- Step 3: `mv a1, a2` at `0x10c4c` (`a1 = src_ptr`).  Fetch bytes `93 05 06 00` (`00060593`);
writes `x11 ↦ a2Val + sext 0`. -/
theorem cfs_step_mv_a1_a2 (stepNo : Nat) (state : State)
    (a2Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c4c) 0x93#8 0x05#8 0x06#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c4c)).regs.get? x12 = some a2Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c4c) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c4c)).regs.insert x11 (a2Val + sign_extend (m := 64) 0#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c4c) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x05#8 0x06#8 0x00#8 = (0x00060593 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x06#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 12#5, .Regidx 11#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_mv_a1_a2_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (0#12, .Regidx 12#5, .Regidx 11#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c4c))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c4c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c4c)).regs.insert x11 (a2Val + sign_extend (m := 64) 0#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 12#5) (.Regidx 11#5) .ADDI) _ _ _
    unfold Runs
    exact execute_mv_a1_a2 _ a2Val h12
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10c4c) retired inhibit config
    0x93#8 0x05#8 0x06#8 0x00#8 (.ITYPE (0#12, .Regidx 12#5, .Regidx 11#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpNextPc _ _ x11 _ (by decide))
    (gpGet _ _ x11 _ hart_state (by decide) (by decide))
    (gpGet _ _ x11 _ minstret_increment (by decide) (by decide))
    (gpGet _ _ x11 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Step 4: `mv a2, a4` at `0x10c50` (`a2 = len`).  Fetch bytes `13 06 07 00` (`00070613`);
writes `x12 ↦ a4Val + sext 0`. -/
theorem cfs_step_mv_a2_a4 (stepNo : Nat) (state : State)
    (a4Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c50) 0x13#8 0x06#8 0x07#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h14 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c50)).regs.get? x14 = some a4Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c50) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c50)).regs.insert x12 (a4Val + sign_extend (m := 64) 0#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c50) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x13#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x13#8 0x06#8 0x07#8 0x00#8 = (0x00070613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x07#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 14#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_mv_a2_a4_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (0#12, .Regidx 14#5, .Regidx 12#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c50))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c50) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c50)).regs.insert x12 (a4Val + sign_extend (m := 64) 0#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 14#5) (.Regidx 12#5) .ADDI) _ _ _
    unfold Runs
    exact execute_mv_a2_a4 _ a4Val h14
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10c50) retired inhibit config
    0x13#8 0x06#8 0x07#8 0x00#8 (.ITYPE (0#12, .Regidx 14#5, .Regidx 12#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpNextPc _ _ x12 _ (by decide))
    (gpGet _ _ x12 _ hart_state (by decide) (by decide))
    (gpGet _ _ x12 _ minstret_increment (by decide) (by decide))
    (gpGet _ _ x12 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Step 5: `auipc t1, 0x0` at `0x10c54` (`t1 = 0x10c54`).  Fetch bytes `17 03 00 00` (`00000317`);
writes `x6 ↦ pcVal + sext (0 ++ 0)`. -/
theorem cfs_step_auipc (stepNo : Nat) (state : State)
    (pcVal retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c54) 0x17#8 0x03#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hpc : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c54)).regs.get? PC = some pcVal) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c54) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c54)).regs.insert x6
              (pcVal + sign_extend (m := 64) (0#20 ++ 0x000#12)) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c54) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x17#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x17#8 0x03#8 0x00#8 0x00#8 = (0x00000317 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x17#8 0x03#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0#20, .Regidx 6#5, .AUIPC)) := by
    rw [wordEq]; exact ext_decode_auipc_t1_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.UTYPE (0#20, .Regidx 6#5, .AUIPC)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c54))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c54) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c54)).regs.insert x6
            (pcVal + sign_extend (m := 64) (0#20 ++ 0x000#12)) }
      (.Retire_Success ()) := by
    change Runs (execute_UTYPE 0#20 (.Regidx 6#5) .AUIPC) _ _ _
    exact execute_UTYPE_auipc_run _ _ 0#20 (.Regidx 6#5) pcVal
      (readReg_run _ PC pcVal hpc) (wX_bits_x6_run _ _)
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10c54) retired inhibit config
    0x17#8 0x03#8 0x00#8 0x00#8 (.UTYPE (0#20, .Regidx 6#5, .AUIPC))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpNextPc _ _ x6 _ (by decide))
    (gpGet _ _ x6 _ hart_state (by decide) (by decide))
    (gpGet _ _ x6 _ minstret_increment (by decide) (by decide))
    (gpGet _ _ x6 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Step 6: `jr 196(t1)` at `0x10c58` (`jalr x0, 196(t1)`, tail-call `memcpy`).  Fetch bytes
`67 00 43 0c` (`0c430067`); jumps to `(t1Val + sext 196) with bit 0 cleared`. -/
theorem cfs_step_jr (stepNo : Nat) (state : State)
    (t1Val retired mseccfgBits misaBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c58) 0x67#8 0x00#8 0x43#8 0x0c#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hrs1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c58)).regs.get? x6 = some t1Val)
    (hbit1 : Sail.BitVec.access (t1Val + sign_extend (m := 64) 0xc4#12) 1 = 0#1)
    (hElp : Runs (update_elp_state (.Regidx 6#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      ())
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c58)).regs.get? misa = some misaBits) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58)
          (Sail.BitVec.update (t1Val + sign_extend (m := 64) 0xc4#12) 0 0#1))
        (Sail.BitVec.update (t1Val + sign_extend (m := 64) 0xc4#12) 0 0#1) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x67#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x67#8 0x00#8 0x43#8 0x0c#8 = (0x0c430067 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x67#8 0x00#8 0x43#8 0x0c#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0xc4#12, .Regidx 6#5, zreg)) := by
    rw [wordEq]; exact ext_decode_jr_t1_run _ privRead mseccfgBits mseccfgRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c58) 4) := by
    unfold get_next_pc; exact readReg_run _ nextPC _ (coreNextPc _ _)
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepJrRetires stepNo state (BitVec.ofNat 64 0x10c58) retired (.Regidx 6#5) (0xc4#12)
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c58) 4) t1Val inhibit config
    0x67#8 0x00#8 0x43#8 0x0c#8 (_get_Misa_C misaBits == 1#1)
    platform noMMIO bytes interrupts base decode notExpected hElp hlink
    (rX_bits_x6_run _ _ hrs1) hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead

/-! ## Deliverable: capstone contract `copy_from_slice_contract` -/

set_option maxHeartbeats 1600000 in
/-- CAPSTONE.  The equal-length `copy_from_slice_impl(dst_ptr, dst_len, src_ptr, src_len)` at
`0x10c44`, run through the authoritative generated `try_step`.  The equal-length precondition
`a1 == a3` is expressed by both `a1 = dst_len` (`ha1`) and `a3 = src_len` (`ha3`) reading the common
length `n`; this makes the `bne` at `0x10c48` **not taken**, so the assembled `Trace` steps from
`0x10c48` straight to `0x10c4c` and never visits the panic branch at `0x10c5c`.  The panic path is
therefore demonstrably avoided: no panic-branch decode/execute is ever invoked.

After renaming the arguments (`a1 = src_ptr`, `a2 = n`) and forming `t1`, the `jr` tail-call jumps to
`memcpy` at `0x10d18`; the 6-instruction setup trace composes with `memcpy_contract`'s trace via
`Trace.append`.  The genuine setup and `memcpy` platform / data-access / landing-pad preconditions
are carried abstractly (`CfsAbstractPlatform` / `CfsAbstractDataAccess` / `CfsAbstractElp`), never
discharged here (the stage-2 trust boundary), and transport into `memcpy`'s abstract premises about
the post-setup state.  The result: a single `6 + (1 + n*7 + 2)`-step trace to the caller, after which
every destination byte `mem[dst_ptr+j]` equals the original source byte `mem[src_ptr+j]`
(`= srcByte j`), the source region / code image / (renamed) argument registers are preserved, and
`PC = ra` (bit 0 cleared). -/
theorem copy_from_slice_contract (dstPtr srcPtr n retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (srcByte : Nat → BitVec 8) (start : Nat) (s : State)
    (hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10c44))
    (ha0 : s.regs.get? x10 = some dstPtr) (ha1 : s.regs.get? x11 = some n)
    (ha2 : s.regs.get? x12 = some srcPtr) (ha3 : s.regs.get? x13 = some n)
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
    (hsrc : ∀ j : Nat, j < n.toNat →
      s.mem.get? (srcPtr + BitVec.ofNat 64 j).toNat = some (srcByte j))
    (hnLt : n.toNat < 2 ^ 64) (hsrcFits : srcPtr.toNat + n.toNat ≤ 2 ^ 64)
    (hdstFits : dstPtr.toNat + n.toNat ≤ 2 ^ 64)
    (hdstImg : ∀ j : Nat, j < n.toNat → image.readByte? (dstPtr + BitVec.ofNat 64 j).toNat = none)
    (hdisj : ∀ j k : Nat, j < n.toNat → k < n.toNat →
      (dstPtr + BitVec.ofNat 64 j).toNat ≠ (srcPtr + BitVec.ofNat 64 k).toNat)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hplat : CfsAbstractPlatform s) (hdata : CfsAbstractDataAccess n dstPtr srcPtr s)
    (hElp : CfsAbstractElp s) :
    ∃ s'', Trace start (6 + (1 + n.toNat * 7 + 2)) s s'' ∧
      s''.regs.get? PC = some (Sail.BitVec.update retAddr 0 0#1) ∧
      (∀ j : Nat, j < n.toNat →
        s''.mem.get? (dstPtr + BitVec.ofNat 64 j).toNat = some (srcByte j)) ∧
      s''.regs.get? x10 = some dstPtr ∧ s''.regs.get? x11 = some srcPtr ∧
      s''.regs.get? x12 = some n ∧ s''.regs.get? x1 = some retAddr ∧
      image.matchesMemory s''.mem ∧
      -- Compositional framing (Deliverables 1–4), inherited through the `memcpy` tail-call:
      -- every register outside `W ∪ {x6, x11, x12}` is preserved (in particular `x2`/`sp`); the
      -- setup does rename via `x6`/`x11`/`x12`, so this is the honest register postcondition,
      CfsStableAgree s s'' ∧ s''.regs.get? x2 = s.regs.get? x2 ∧
      -- memory changes only inside the destination window `[dst_ptr, dst_ptr+n)`,
      MemFramed dstPtr n s s'' ∧
      -- and the source region is preserved.
      (∀ k : Nat, k < n.toNat →
        s''.mem.get? (srcPtr + BitVec.ofNat 64 k).toNat = s.mem.get? (srcPtr + BitVec.ofNat 64 k).toNat) := by
  obtain ⟨retired0, hret0⟩ := hminstret
  have hsum44 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10c44) 4 = BitVec.ofNat 64 0x10c48 := by decide
  have hsum48 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10c48) 4 = BitVec.ofNat 64 0x10c4c := by decide
  have hsum4c : Sail.BitVec.addInt (BitVec.ofNat 64 0x10c4c) 4 = BitVec.ofNat 64 0x10c50 := by decide
  have hsum50 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10c50) 4 = BitVec.ofNat 64 0x10c54 := by decide
  have hsum54 : Sail.BitVec.addInt (BitVec.ofNat 64 0x10c54) 4 = BitVec.ofNat 64 0x10c58 := by decide
  have hsumJr : (BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12
      = BitVec.ofNat 64 0x10d18 := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  -- Step 1: mv a4, a1 at 0x10c44 (a4 = dst_len = n).
  have hbytes0 : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c44)
      0x13#8 0x87#8 0x05#8 0x00#8 :=
    fetchBytesAt_10c44 (tryStepControlFlowAfterIncrement s) image himageEq hmatches
  have hplat0 : StepPlatform s (BitVec.ofNat 64 0x10c44) 0x13#8 0x87#8 0x05#8 0x00#8 mseccfgBits :=
    mkCfsStepPlatform s mseccfgBits (BitVec.ofNat 64 0x10c44) 0x13#8 0x87#8 0x05#8 0x00#8
      hplat hcur hmseccfg (CfsStableAgree.refl s)
      ((afterIncGet s PC (by decide)).trans hPC) (by decide) hbytes0
  have hcnt0 : StepCounters s retired0 inhibit cfg :=
    ⟨hhart, hinhibit, hcfg, hnotInhibited, hmachineEnabled, hret0⟩
  have h11_0 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
      (BitVec.ofNat 64 0x10c44)).regs.get? x11 = some n :=
    (xGet s (BitVec.ofNat 64 0x10c44) x11 (by decide) (by decide)).trans ha1
  have h1 := cfs_step_mv_a4_a1 start s n retired0 mseccfgBits inhibit cfg hplat0 hcnt0 h11_0
  have hCfs1 : CfsStableAgree s _ :=
    cfsAgree_fallThrough s s (BitVec.ofNat 64 0x10c44) retired0 x14
      (n + sign_extend (m := 64) 0#12) (fun r hr _ _ _ => hr.2.2.2.2.2.1) (CfsStableAgree.refl s)
  have hPC1 := retiredGetPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c44) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
        (BitVec.ofNat 64 0x10c44)).regs.insert x14 (n + sign_extend (m := 64) 0#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c44) 4) retired0
  have hmin1 := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c44) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
        (BitVec.ofNat 64 0x10c44)).regs.insert x14 (n + sign_extend (m := 64) 0#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c44) 4) retired0
  have hmem1 : _ = s.mem :=
    (retiredMem _ (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c44) 4) retired0).trans
      (fallThroughMem s (BitVec.ofNat 64 0x10c44) x14 (n + sign_extend (m := 64) 0#12))
  have hx11_1 : _ = some n :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c44) retired0 x14 (n + sign_extend (m := 64) 0#12)
      x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha1
  have hx13_1 : _ = some n :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c44) retired0 x14 (n + sign_extend (m := 64) 0#12)
      x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha3
  have hx12_1 : _ = some srcPtr :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c44) retired0 x14 (n + sign_extend (m := 64) 0#12)
      x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha2
  have hx14_1 := fallThroughRetiredRd s (BitVec.ofNat 64 0x10c44) retired0 x14
    (n + sign_extend (m := 64) 0#12) (by decide) (by decide)
  generalize hgen1 : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c44) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
          (BitVec.ofNat 64 0x10c44)).regs.insert x14 (n + sign_extend (m := 64) 0#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c44) 4) retired0 = s1
    at h1 hCfs1 hPC1 hmin1 hmem1 hx11_1 hx13_1 hx12_1 hx14_1
  rw [hsum44] at hPC1
  -- Step 2: bne a1, a3 at 0x10c48, NOT taken (a1 = a3 = n) — panic branch skipped.
  have hbytes1 : FetchBytesAt (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c48)
      0x63#8 0x9a#8 0xd5#8 0x00#8 :=
    fetchBytesAt_10c48 (tryStepControlFlowAfterIncrement s1) image himageEq (hmem1.symm ▸ hmatches)
  have hplat1 : StepPlatform s1 (BitVec.ofNat 64 0x10c48) 0x63#8 0x9a#8 0xd5#8 0x00#8 mseccfgBits :=
    mkCfsStepPlatform s1 mseccfgBits (BitVec.ofNat 64 0x10c48) 0x63#8 0x9a#8 0xd5#8 0x00#8
      hplat hcur hmseccfg hCfs1 ((afterIncGet s1 PC (by decide)).trans hPC1) (by decide) hbytes1
  have hcnt1 : StepCounters s1 (Sail.BitVec.addInt retired0 1) inhibit cfg :=
    ⟨(hCfs1 hart_state (by decide) (by decide) (by decide) (by decide)).trans hhart,
      (hCfs1 mcountinhibit (by decide) (by decide) (by decide) (by decide)).trans hinhibit,
      (hCfs1 minstretcfg (by decide) (by decide) (by decide) (by decide)).trans hcfg,
      hnotInhibited, hmachineEnabled, hmin1⟩
  have h11_1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10c48)).regs.get? x11 = some n :=
    (xGet s1 (BitVec.ofNat 64 0x10c48) x11 (by decide) (by decide)).trans hx11_1
  have h13_1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10c48)).regs.get? x13 = some n :=
    (xGet s1 (BitVec.ofNat 64 0x10c48) x13 (by decide) (by decide)).trans hx13_1
  have h2 := cfs_step_bne_not_taken (start + 1) s1 n n (Sail.BitVec.addInt retired0 1) mseccfgBits
    inhibit cfg hplat1 hcnt1 h11_1 h13_1 rfl
  have hCfs2 : CfsStableAgree s _ :=
    cfsAgree_notTaken s s1 (BitVec.ofNat 64 0x10c48) (Sail.BitVec.addInt retired0 1) hCfs1
  have hPC2 := retiredGetPC
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c48))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c48) 4) (Sail.BitVec.addInt retired0 1)
  have hmin2 := retiredMinstret
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c48))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c48) 4) (Sail.BitVec.addInt retired0 1)
  have hmem2 : _ = s.mem :=
    (notTakenMem s1 (BitVec.ofNat 64 0x10c48) (Sail.BitVec.addInt retired0 1)).trans hmem1
  have hx11_2 : _ = some n :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c48) (Sail.BitVec.addInt retired0 1) x11
      (by decide) (by decide) (by decide) (by decide)).trans hx11_1
  have hx12_2 : _ = some srcPtr :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c48) (Sail.BitVec.addInt retired0 1) x12
      (by decide) (by decide) (by decide) (by decide)).trans hx12_1
  have hx14_2 : _ = some (n + sign_extend (m := 64) 0#12) :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c48) (Sail.BitVec.addInt retired0 1) x14
      (by decide) (by decide) (by decide) (by decide)).trans hx14_1
  generalize hgen2 : tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c48))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c48) 4) (Sail.BitVec.addInt retired0 1) = s2
    at h2 hCfs2 hPC2 hmin2 hmem2 hx11_2 hx12_2 hx14_2
  rw [hsum48] at hPC2
  -- Step 3: mv a1, a2 at 0x10c4c (a1 = src_ptr).
  have hbytes2 : FetchBytesAt (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c4c)
      0x93#8 0x05#8 0x06#8 0x00#8 :=
    fetchBytesAt_10c4c (tryStepControlFlowAfterIncrement s2) image himageEq (hmem2.symm ▸ hmatches)
  have hplat2 : StepPlatform s2 (BitVec.ofNat 64 0x10c4c) 0x93#8 0x05#8 0x06#8 0x00#8 mseccfgBits :=
    mkCfsStepPlatform s2 mseccfgBits (BitVec.ofNat 64 0x10c4c) 0x93#8 0x05#8 0x06#8 0x00#8
      hplat hcur hmseccfg hCfs2 ((afterIncGet s2 PC (by decide)).trans hPC2) (by decide) hbytes2
  have hcnt2 : StepCounters s2 (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) inhibit cfg :=
    ⟨(hCfs2 hart_state (by decide) (by decide) (by decide) (by decide)).trans hhart,
      (hCfs2 mcountinhibit (by decide) (by decide) (by decide) (by decide)).trans hinhibit,
      (hCfs2 minstretcfg (by decide) (by decide) (by decide) (by decide)).trans hcfg,
      hnotInhibited, hmachineEnabled, hmin2⟩
  have h12_2 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
      (BitVec.ofNat 64 0x10c4c)).regs.get? x12 = some srcPtr :=
    (xGet s2 (BitVec.ofNat 64 0x10c4c) x12 (by decide) (by decide)).trans hx12_2
  have h3 := cfs_step_mv_a1_a2 (start + 2) s2 srcPtr
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) mseccfgBits inhibit cfg hplat2 hcnt2 h12_2
  have hCfs3 : CfsStableAgree s _ :=
    cfsAgree_fallThrough s s2 (BitVec.ofNat 64 0x10c4c)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x11
      (srcPtr + sign_extend (m := 64) 0#12) (fun r _ _ hr11 _ => hr11) hCfs2
  have hPC3 := retiredGetPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c4c) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
        (BitVec.ofNat 64 0x10c4c)).regs.insert x11 (srcPtr + sign_extend (m := 64) 0#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c4c) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
  have hmin3 := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c4c) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
        (BitVec.ofNat 64 0x10c4c)).regs.insert x11 (srcPtr + sign_extend (m := 64) 0#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c4c) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
  have hmem3 : _ = s.mem :=
    (retiredMem _ (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c4c) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)).trans
      ((fallThroughMem s2 (BitVec.ofNat 64 0x10c4c) x11
        (srcPtr + sign_extend (m := 64) 0#12)).trans hmem2)
  have hx11_3 := fallThroughRetiredRd s2 (BitVec.ofNat 64 0x10c4c)
    (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x11 (srcPtr + sign_extend (m := 64) 0#12)
    (by decide) (by decide)
  have hx14_3 : _ = some (n + sign_extend (m := 64) 0#12) :=
    (fallThroughRetiredGet s2 (BitVec.ofNat 64 0x10c4c)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) x11
      (srcPtr + sign_extend (m := 64) 0#12) x14
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx14_2
  generalize hgen3 : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s2) (BitVec.ofNat 64 0x10c4c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s2)
          (BitVec.ofNat 64 0x10c4c)).regs.insert x11 (srcPtr + sign_extend (m := 64) 0#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c4c) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) = s3
    at h3 hCfs3 hPC3 hmin3 hmem3 hx11_3 hx14_3
  rw [hsum4c] at hPC3
  -- Step 4: mv a2, a4 at 0x10c50 (a2 = len = n).
  have hbytes3 : FetchBytesAt (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c50)
      0x13#8 0x06#8 0x07#8 0x00#8 :=
    fetchBytesAt_10c50 (tryStepControlFlowAfterIncrement s3) image himageEq (hmem3.symm ▸ hmatches)
  have hplat3 : StepPlatform s3 (BitVec.ofNat 64 0x10c50) 0x13#8 0x06#8 0x07#8 0x00#8 mseccfgBits :=
    mkCfsStepPlatform s3 mseccfgBits (BitVec.ofNat 64 0x10c50) 0x13#8 0x06#8 0x07#8 0x00#8
      hplat hcur hmseccfg hCfs3 ((afterIncGet s3 PC (by decide)).trans hPC3) (by decide) hbytes3
  have hcnt3 : StepCounters s3
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) inhibit cfg :=
    ⟨(hCfs3 hart_state (by decide) (by decide) (by decide) (by decide)).trans hhart,
      (hCfs3 mcountinhibit (by decide) (by decide) (by decide) (by decide)).trans hinhibit,
      (hCfs3 minstretcfg (by decide) (by decide) (by decide) (by decide)).trans hcfg,
      hnotInhibited, hmachineEnabled, hmin3⟩
  have h14_3 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
      (BitVec.ofNat 64 0x10c50)).regs.get? x14 = some (n + sign_extend (m := 64) 0#12) :=
    (xGet s3 (BitVec.ofNat 64 0x10c50) x14 (by decide) (by decide)).trans hx14_3
  have h4 := cfs_step_mv_a2_a4 (start + 3) s3 (n + sign_extend (m := 64) 0#12)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) mseccfgBits inhibit
    cfg hplat3 hcnt3 h14_3
  have hCfs4 : CfsStableAgree s _ :=
    cfsAgree_fallThrough s s3 (BitVec.ofNat 64 0x10c50)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x12
      ((n + sign_extend (m := 64) 0#12) + sign_extend (m := 64) 0#12)
      (fun r _ _ _ hr12 => hr12) hCfs3
  have hPC4 := retiredGetPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c50) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
        (BitVec.ofNat 64 0x10c50)).regs.insert x12
          ((n + sign_extend (m := 64) 0#12) + sign_extend (m := 64) 0#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c50) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
  have hmin4 := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c50) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
        (BitVec.ofNat 64 0x10c50)).regs.insert x12
          ((n + sign_extend (m := 64) 0#12) + sign_extend (m := 64) 0#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c50) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
  have hmem4 : _ = s.mem :=
    (retiredMem _ (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c50) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)).trans
      ((fallThroughMem s3 (BitVec.ofNat 64 0x10c50) x12
        ((n + sign_extend (m := 64) 0#12) + sign_extend (m := 64) 0#12)).trans hmem3)
  have hx11_4 : _ = some (srcPtr + sign_extend (m := 64) 0#12) :=
    (fallThroughRetiredGet s3 (BitVec.ofNat 64 0x10c50)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x12
      ((n + sign_extend (m := 64) 0#12) + sign_extend (m := 64) 0#12) x11
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11_3
  have hx12_4 := fallThroughRetiredRd s3 (BitVec.ofNat 64 0x10c50)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) x12
    ((n + sign_extend (m := 64) 0#12) + sign_extend (m := 64) 0#12) (by decide) (by decide)
  generalize hgen4 : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10c50) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3)
          (BitVec.ofNat 64 0x10c50)).regs.insert x12
            ((n + sign_extend (m := 64) 0#12) + sign_extend (m := 64) 0#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c50) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1) = s4
    at h4 hCfs4 hPC4 hmin4 hmem4 hx11_4 hx12_4
  rw [hsum50] at hPC4
  -- Step 5: auipc t1, 0x0 at 0x10c54 (t1 = 0x10c54).
  have hbytes4 : FetchBytesAt (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c54)
      0x17#8 0x03#8 0x00#8 0x00#8 :=
    fetchBytesAt_10c54 (tryStepControlFlowAfterIncrement s4) image himageEq (hmem4.symm ▸ hmatches)
  have hplat4 : StepPlatform s4 (BitVec.ofNat 64 0x10c54) 0x17#8 0x03#8 0x00#8 0x00#8 mseccfgBits :=
    mkCfsStepPlatform s4 mseccfgBits (BitVec.ofNat 64 0x10c54) 0x17#8 0x03#8 0x00#8 0x00#8
      hplat hcur hmseccfg hCfs4 ((afterIncGet s4 PC (by decide)).trans hPC4) (by decide) hbytes4
  have hcnt4 : StepCounters s4
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) inhibit cfg :=
    ⟨(hCfs4 hart_state (by decide) (by decide) (by decide) (by decide)).trans hhart,
      (hCfs4 mcountinhibit (by decide) (by decide) (by decide) (by decide)).trans hinhibit,
      (hCfs4 minstretcfg (by decide) (by decide) (by decide) (by decide)).trans hcfg,
      hnotInhibited, hmachineEnabled, hmin4⟩
  have hpc4core : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4)
      (BitVec.ofNat 64 0x10c54)).regs.get? PC = some (BitVec.ofNat 64 0x10c54) :=
    (xGet s4 (BitVec.ofNat 64 0x10c54) PC (by decide) (by decide)).trans hPC4
  have h5 := cfs_step_auipc (start + 4) s4 (BitVec.ofNat 64 0x10c54)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
      1) mseccfgBits inhibit cfg hplat4 hcnt4 hpc4core
  have hCfs5 : CfsStableAgree s _ :=
    cfsAgree_fallThrough s s4 (BitVec.ofNat 64 0x10c54)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) x6 ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) (0#20 ++ 0x000#12))
      (fun r _ hr6 _ _ => hr6) hCfs4
  have hPC5 := retiredGetPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c54) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4)
        (BitVec.ofNat 64 0x10c54)).regs.insert x6
          ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) (0#20 ++ 0x000#12)) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c54) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
      1)
  have hmin5 := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c54) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4)
        (BitVec.ofNat 64 0x10c54)).regs.insert x6
          ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) (0#20 ++ 0x000#12)) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c54) 4)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1) 1)
      1)
  have hmem5 : _ = s.mem :=
    (retiredMem _ (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c54) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1)).trans
      ((fallThroughMem s4 (BitVec.ofNat 64 0x10c54) x6
        ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) (0#20 ++ 0x000#12))).trans hmem4)
  have hx11_5 : _ = some (srcPtr + sign_extend (m := 64) 0#12) :=
    (fallThroughRetiredGet s4 (BitVec.ofNat 64 0x10c54)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) x6 ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) (0#20 ++ 0x000#12)) x11
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11_4
  have hx12_5 : _ = some ((n + sign_extend (m := 64) 0#12) + sign_extend (m := 64) 0#12) :=
    (fallThroughRetiredGet s4 (BitVec.ofNat 64 0x10c54)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) x6 ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) (0#20 ++ 0x000#12)) x12
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx12_4
  have hx6_5 : _ = some (BitVec.ofNat 64 0x10c54) :=
    (fallThroughRetiredRd s4 (BitVec.ofNat 64 0x10c54)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) x6 ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) (0#20 ++ 0x000#12))
      (by decide) (by decide)).trans (congrArg some (add_auipc_zero (BitVec.ofNat 64 0x10c54)))
  obtain ⟨misaBits5, _mstatus5, _pcr5, misaRead5, _rest5⟩ := hplat4.1
  have hmisa5 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4)
      (BitVec.ofNat 64 0x10c54)).regs.get? misa = some misaBits5 :=
    (coreGetInc' (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c54) misa
      (by decide)).trans misaRead5
  generalize hgen5 : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x10c54) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s4)
          (BitVec.ofNat 64 0x10c54)).regs.insert x6
            ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) (0#20 ++ 0x000#12)) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c54) 4)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt retired0 1) 1)
        1) 1) = s5
    at h5 hCfs5 hPC5 hmin5 hmem5 hx11_5 hx12_5 hx6_5
  rw [hsum54] at hPC5
  -- Step 6: jr 196(t1) at 0x10c58 — tail-call memcpy at 0x10d18.
  have hbytes5 : FetchBytesAt (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c58)
      0x67#8 0x00#8 0x43#8 0x0c#8 :=
    fetchBytesAt_10c58 (tryStepControlFlowAfterIncrement s5) image himageEq (hmem5.symm ▸ hmatches)
  have hplat5 : StepPlatform s5 (BitVec.ofNat 64 0x10c58) 0x67#8 0x00#8 0x43#8 0x0c#8 mseccfgBits :=
    mkCfsStepPlatform s5 mseccfgBits (BitVec.ofNat 64 0x10c58) 0x67#8 0x00#8 0x43#8 0x0c#8
      hplat hcur hmseccfg hCfs5 ((afterIncGet s5 PC (by decide)).trans hPC5) (by decide) hbytes5
  have hcnt5 : StepCounters s5
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) inhibit cfg :=
    ⟨(hCfs5 hart_state (by decide) (by decide) (by decide) (by decide)).trans hhart,
      (hCfs5 mcountinhibit (by decide) (by decide) (by decide) (by decide)).trans hinhibit,
      (hCfs5 minstretcfg (by decide) (by decide) (by decide) (by decide)).trans hcfg,
      hnotInhibited, hmachineEnabled, hmin5⟩
  have hrs1_5 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
      (BitVec.ofNat 64 0x10c58)).regs.get? x6 = some (BitVec.ofNat 64 0x10c54) :=
    (xGet s5 (BitVec.ofNat 64 0x10c58) x6 (by decide) (by decide)).trans hx6_5
  have hbit1_5 : Sail.BitVec.access
      ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 1 = 0#1 := by
    rw [hsumJr]; decide
  have hElp5 : Runs (update_elp_state (.Regidx 6#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c58))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c58)) () :=
    hElp _ (.Regidx 6#5) (cfsCoreStableAgree s5 (BitVec.ofNat 64 0x10c58) hCfs5)
  obtain ⟨misaBits6, _mstatus6, _pcr6, misaRead6, _rest6⟩ := hplat5.1
  have hmisa6 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5)
      (BitVec.ofNat 64 0x10c58)).regs.get? misa = some misaBits6 :=
    (coreGetInc' (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c58) misa
      (by decide)).trans misaRead6
  have h6 := cfs_step_jr (start + 5) s5 (BitVec.ofNat 64 0x10c54)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
      (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) mseccfgBits misaBits6 inhibit cfg hplat5 hcnt5
    hrs1_5 hbit1_5 hElp5 hmisa6
  have hCfs6 : CfsStableAgree s _ :=
    cfsAgree_jump s s5 (BitVec.ofNat 64 0x10c58)
      (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) hCfs5
  have hPC6 := retiredGetPC
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c58)
      (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1))
    (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
      (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1)
  have hmin6 := retiredMinstret
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c58)
      (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1))
    (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1)
    (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
      (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1)
  have hmem6 : _ = s.mem :=
    (retiredMem _
      (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1)).trans
      ((jumpMem s5 (BitVec.ofNat 64 0x10c58)
        (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1)).trans
        hmem5)
  have hx11_6 : _ = some (srcPtr + sign_extend (m := 64) 0#12) :=
    (jumpRetiredGet s5 (BitVec.ofNat 64 0x10c58)
      (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) x11
      (by decide) (by decide) (by decide) (by decide)).trans hx11_5
  have hx12_6 : _ = some ((n + sign_extend (m := 64) 0#12) + sign_extend (m := 64) 0#12) :=
    (jumpRetiredGet s5 (BitVec.ofNat 64 0x10c58)
      (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) x12
      (by decide) (by decide) (by decide) (by decide)).trans hx12_5
  generalize hgen6 : tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10c58)
        (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1))
      (Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1)
      (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt (Sail.BitVec.addInt
        (Sail.BitVec.addInt retired0 1) 1) 1) 1) 1) = s6
    at h6 hCfs6 hPC6 hmin6 hmem6 hx11_6 hx12_6
  -- The 6-instruction setup trace.
  have htrSetup : Trace start 6 s s6 := by trace_steps [h1, h2, h3, h4, h5, h6]
  -- The post-setup state satisfies memcpy's calling convention; compose with memcpy_contract.
  have htargetPc : Sail.BitVec.update ((BitVec.ofNat 64 0x10c54) + sign_extend (m := 64) 0xc4#12) 0 0#1
      = BitVec.ofNat 64 0x10d18 := by rw [hsumJr]; decide
  have hn2 : (n + sign_extend (m := 64) 0#12) + sign_extend (m := 64) 0#12 = n := by
    rw [add_sext_zero, add_sext_zero]
  obtain ⟨s'', htrMemcpy, hPCret, hcopy, hx10'', hx11'', hx12'', hx1'', hmatches'',
      hStable6, _hx2eq6, hFrame6, hsrcPres6⟩ :=
    memcpy_contract dstPtr srcPtr n retAddr image mseccfgBits mstatusBits inhibit cfg srcByte
      (start + 6) s6
      (hPC6.trans (congrArg some htargetPc))
      ((hCfs6 x10 (by decide) (by decide) (by decide) (by decide)).trans ha0)
      (hx11_6.trans (congrArg some (add_sext_zero srcPtr)))
      (hx12_6.trans (congrArg some hn2))
      ((hCfs6 x1 (by decide) (by decide) (by decide) (by decide)).trans hra)
      ((hCfs6 cur_privilege (by decide) (by decide) (by decide) (by decide)).trans hcur)
      ((hCfs6 mstatus (by decide) (by decide) (by decide) (by decide)).trans hmstatus) hmprv
      ((hCfs6 mseccfg (by decide) (by decide) (by decide) (by decide)).trans hmseccfg)
      ((hCfs6 hart_state (by decide) (by decide) (by decide) (by decide)).trans hhart)
      ((hCfs6 mcountinhibit (by decide) (by decide) (by decide) (by decide)).trans hinhibit)
      hnotInhibited
      ((hCfs6 minstretcfg (by decide) (by decide) (by decide) (by decide)).trans hcfg)
      hmachineEnabled ⟨_, hmin6⟩ himageEq (hmem6.symm ▸ hmatches)
      (fun j hj => by rw [hmem6]; exact hsrc j hj)
      hnLt hsrcFits hdstFits hdstImg hdisj hretAlign
      (cfsPlatformTransport hCfs6 hplat) (cfsDataTransport hCfs6 hdata) (cfsElpTransport hCfs6 hElp)
  -- Transport `memcpy`'s framing (about the post-setup state `s6`) back to the entry state `s`:
  -- the setup leaves memory untouched (`hmem6 : s6.mem = s.mem`) and `CfsStableAgree s s6` composes
  -- with `memcpy`'s `StableAgree s6 s''`.
  have hCfsFinal : CfsStableAgree s s'' := cfsAgree_compose hCfs6 hStable6
  have hMemFramedFinal : MemFramed dstPtr n s s'' := by
    intro addr h; rw [hFrame6 addr h, hmem6]
  have hSrcFinal : ∀ k : Nat, k < n.toNat →
      s''.mem.get? (srcPtr + BitVec.ofNat 64 k).toNat = s.mem.get? (srcPtr + BitVec.ofNat 64 k).toNat := by
    intro k hk; rw [hsrcPres6 k hk, hmem6]
  exact ⟨s'', Trace.append htrSetup htrMemcpy, hPCret, hcopy, hx10'', hx11'', hx12'', hx1'',
    hmatches'', hCfsFinal, hCfsFinal x2 (by decide) (by decide) (by decide) (by decide),
    hMemFramedFinal, hSrcFinal⟩

end BinaryFv.Keccak
