import BinaryFv.RiscV.Instruction.Execute.Memory
import BinaryFv.RiscV.Logic.Trace
import BinaryFv.RiscV.Step.Call

/-!
# A small kernel-checked block-stepping tactic

`Trace.step`/`Trace.refl` (from `BinaryFv.RiscV.Logic.Trace`) already chain into a multi-step trace, but
writing the nested applications by hand is noisy for a straight-line block.  This module provides a
minimal, fully kernel-checked convenience: each `trace_step h` discharges one leading `try_step` of a
`Trace` goal using an *established* per-instruction step lemma `h`, and `trace_steps [h₀, …, hₙ]`
does the whole block.  There is no search or decision procedure — the tactic only assembles the
inductive `Trace` constructors, so every result is an ordinary proof term the kernel checks.
-/

namespace BinaryFv.RiscV

/-- Discharge one leading `try_step` of a `Trace _ (_ + 1) _ _` goal with the step lemma `h`
    (`Runs (try_step k false) s s' false`, its concrete post-state `s'` fixing the intermediate
    state), leaving the remaining `Trace` obligation. -/
macro "trace_step " h:term : tactic =>
  `(tactic| refine Trace.step _ _ _ _ _ $h ?_)

/-- Assemble a straight-line block trace from a list of established per-instruction step lemmas
    `[h₀, h₁, …]`, closing the base case by reflexivity. -/
syntax "trace_steps " "[" term,* "]" : tactic
macro_rules
  | `(tactic| trace_steps []) => `(tactic| exact Trace.refl _ _)
  | `(tactic| trace_steps [$h:term]) =>
      `(tactic| refine Trace.step _ _ _ _ _ $h ?_; exact Trace.refl _ _)
  | `(tactic| trace_steps [$h:term, $hs:term,*]) =>
      `(tactic| refine Trace.step _ _ _ _ _ $h ?_; trace_steps [$hs,*])

/--
Close a `Trace` goal using the retiring `try_step` contracts already in the local context. At each
nonempty trace position, unification fixes the next step number and intermediate state, so
`assumption` selects the corresponding generated instruction contract. This constructs only
`Trace.step` and `Trace.refl` proof terms; it never evaluates or trusts a separate executor.
-/
syntax "trace_assumptions" : tactic
macro_rules
  | `(tactic| trace_assumptions) =>
      `(tactic|
        first
        | exact Trace.refl _ _
        | refine Trace.step _ _ _ _ _ (by assumption) ?_
          trace_assumptions)

end BinaryFv.RiscV

/-! ### Sanity checks (private) -/
namespace BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

/-! ### Representative instruction-contract block -/

/-- The concrete premises for a signed word load that retires through `try_step`. -/
structure LoadWordStepContract (stepNo : Nat) (state : State) where
  afterExec : State
  pc : BitVec 64
  retired : BitVec 64
  imm : BitVec 12
  rs1 : regidx
  rd : regidx
  data : BitVec 32
  inhibit : BitVec 32
  config : BitVec 64
  byte0 : BitVec 8
  byte1 : BitVec 8
  byte2 : BitVec 8
  byte3 : BitVec 8
  platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc
  noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc
  bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3
  interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state)
  base : BaseInstructionEncoding byte0
  decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
    (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
    (.LOAD (imm, rs1, rd, false, 4))
  notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state)
  hread : Runs (vmem_read rs1 (sign_extend (m := 64) imm) 4
    (MemoryAccessType.Load mem_payload.Data) false false false)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) (.Ok data)
  hwrite : Runs (wX_bits rd (extend_value false data))
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) afterExec ()
  nextPcAfterExec : afterExec.regs.get? nextPC = some (Sail.BitVec.addInt pc 4)
  hartAgree : afterExec.regs.get? hart_state =
    (tryStepControlFlowAfterIncrement state).regs.get? hart_state
  incrementAgree : afterExec.regs.get? minstret_increment =
    (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment
  retiredAgree : afterExec.regs.get? minstret =
    (tryStepControlFlowAfterIncrement state).regs.get? minstret
  hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ())
  inhibitRead : state.regs.get? mcountinhibit = some inhibit
  configRead : state.regs.get? minstretcfg = some config
  notInhibited : _get_Counterin_IR inhibit = 0#1
  machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1
  retiredRead : state.regs.get? minstret = some retired

/-- The exact generated postlude state of a word-load step. -/
def LoadWordStepContract.afterRetired
    {stepNo : Nat} {state : State} (contract : LoadWordStepContract stepNo state) : State :=
  tryStepControlFlowAfterRetired contract.afterExec (Sail.BitVec.addInt contract.pc 4)
    contract.retired

/-- Derive the `try_step` fact from the actual `lw` memory action and fetch contract. -/
theorem LoadWordStepContract.retire
    {stepNo : Nat} {state : State} (contract : LoadWordStepContract stepNo state) :
    Runs (try_step stepNo false) state contract.afterRetired false := by
  exact tryStepFallThroughRetires stepNo state contract.afterExec contract.pc contract.retired
    contract.inhibit contract.config contract.byte0 contract.byte1 contract.byte2 contract.byte3
    (.LOAD (contract.imm, contract.rs1, contract.rd, false, 4)) contract.platform contract.noMMIO
    contract.bytes contract.interrupts contract.base contract.decode contract.notExpected
    (execute_LOAD_lw_run _ _ contract.imm contract.rs1 contract.rd contract.data contract.hread
      contract.hwrite)
    contract.nextPcAfterExec contract.hartAgree contract.incrementAgree contract.retiredAgree
    contract.hartRead contract.inhibitRead contract.configRead contract.notInhibited
    contract.machineEnabled contract.retiredRead

/-- Concrete premises for an unsigned-byte primitive read retired through generated `try_step`. -/
structure LoadByteStepContract (stepNo : Nat) (state : State) where
  afterExec : State
  pc : BitVec 64
  retired : BitVec 64
  imm : BitVec 12
  rs1 : regidx
  rd : regidx
  srcBits : BitVec 64
  mstatusBits : BitVec 64
  data : BitVec 8
  inhibit : BitVec 32
  config : BitVec 64
  byte0 : BitVec 8
  byte1 : BitVec 8
  byte2 : BitVec 8
  byte3 : BitVec 8
  platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc
  fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc
  bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3
  interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state)
  base : BaseInstructionEncoding byte0
  decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
    (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
    (.LOAD (imm, rs1, rd, true, 1))
  notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state)
  mstatusRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? mstatus =
    some mstatusBits
  privilegeRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get?
    cur_privilege = some .Machine
  mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1
  addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm)
    (MemoryAccessType.Load mem_payload.Data) 1)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits))
  aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true
  physAccess : Runs (phys_access_check (MemoryAccessType.Load mem_payload.Data)
    page_based_mem_type.PBMT_PMA .Machine (physaddr.Physaddr srcBits) 1 false)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) none
  loadNoMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) false
  hmem : ∀ index (h : index < (BinaryFv.RiscV.Sep.leBytes 1 data).length),
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).mem.get?
      (srcBits.toNat + index) = some (BinaryFv.RiscV.Sep.leBytes 1 data)[index]
  hwrite : Runs (wX_bits rd (zero_extend (m := 64) data))
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) afterExec ()
  nextPcAfterExec : afterExec.regs.get? nextPC = some (Sail.BitVec.addInt pc 4)
  hartAgree : afterExec.regs.get? hart_state =
    (tryStepControlFlowAfterIncrement state).regs.get? hart_state
  incrementAgree : afterExec.regs.get? minstret_increment =
    (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment
  retiredAgree : afterExec.regs.get? minstret =
    (tryStepControlFlowAfterIncrement state).regs.get? minstret
  hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ())
  inhibitRead : state.regs.get? mcountinhibit = some inhibit
  configRead : state.regs.get? minstretcfg = some config
  notInhibited : _get_Counterin_IR inhibit = 0#1
  machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1
  retiredRead : state.regs.get? minstret = some retired

def LoadByteStepContract.afterRetired {stepNo : Nat} {state : State}
    (contract : LoadByteStepContract stepNo state) : State :=
  tryStepControlFlowAfterRetired contract.afterExec (Sail.BitVec.addInt contract.pc 4) contract.retired

theorem LoadByteStepContract.retire {stepNo : Nat} {state : State}
    (contract : LoadByteStepContract stepNo state) :
    Runs (try_step stepNo false) state contract.afterRetired false := by
  exact tryStepFallThroughRetires stepNo state contract.afterExec contract.pc contract.retired
    contract.inhibit contract.config contract.byte0 contract.byte1 contract.byte2 contract.byte3
    (.LOAD (contract.imm, contract.rs1, contract.rd, true, 1)) contract.platform contract.fetchNoMMIO
    contract.bytes contract.interrupts contract.base contract.decode contract.notExpected
    (execute_LOAD_lbu_run _ _ contract.imm contract.rs1 contract.rd contract.srcBits contract.mstatusBits
      contract.data contract.mstatusRead contract.privilegeRead contract.mprvZero contract.addrReg
      contract.aligned contract.physAccess contract.loadNoMMIO contract.hmem contract.hwrite)
    contract.nextPcAfterExec contract.hartAgree contract.incrementAgree contract.retiredAgree
    contract.hartRead contract.inhibitRead contract.configRead contract.notInhibited
    contract.machineEnabled contract.retiredRead

/-- Compose two concrete primitive byte-load retirements into a checked trace fragment. -/
theorem traceByteReadBlock (stepNo : Nat) (state : State)
    (first : LoadByteStepContract stepNo state)
    (second : LoadByteStepContract (stepNo + 1) first.afterRetired) :
    Trace stepNo 2 state second.afterRetired := by
  trace_steps [first.retire, second.retire]

/-- The concrete premises for a decoded, not-taken conditional branch. -/
structure NotTakenBranchStepContract (stepNo : Nat) (state : State) where
  pc : BitVec 64
  retired : BitVec 64
  imm : BitVec 13
  rs2 : regidx
  rs1 : regidx
  op : bop
  inhibit : BitVec 32
  config : BitVec 64
  byte0 : BitVec 8
  byte1 : BitVec 8
  byte2 : BitVec 8
  byte3 : BitVec 8
  platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc
  noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc
  bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3
  interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state)
  base : BaseInstructionEncoding byte0
  decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
    (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
    (.BTYPE (imm, rs2, rs1, op))
  notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state)
  hcond : Runs (bTypeTaken rs2 rs1 op)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) false
  hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ())
  inhibitRead : state.regs.get? mcountinhibit = some inhibit
  configRead : state.regs.get? minstretcfg = some config
  notInhibited : _get_Counterin_IR inhibit = 0#1
  machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1
  retiredRead : state.regs.get? minstret = some retired

/-- The exact generated postlude state of a not-taken conditional branch. -/
def NotTakenBranchStepContract.afterRetired
    {stepNo : Nat} {state : State} (contract : NotTakenBranchStepContract stepNo state) : State :=
  tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) contract.pc)
    (Sail.BitVec.addInt contract.pc 4) contract.retired

/-- Derive the `try_step` fact from the decoded branch and its false branch condition. -/
theorem NotTakenBranchStepContract.retire
    {stepNo : Nat} {state : State} (contract : NotTakenBranchStepContract stepNo state) :
    Runs (try_step stepNo false) state contract.afterRetired false := by
  exact tryStepBranchNotTakenRetires stepNo state contract.pc contract.retired contract.imm
    contract.rs2 contract.rs1 contract.op contract.inhibit contract.config contract.byte0
    contract.byte1 contract.byte2 contract.byte3 contract.platform contract.noMMIO contract.bytes
    contract.interrupts contract.base contract.decode contract.notExpected contract.hcond
    contract.hartRead contract.inhibitRead contract.configRead contract.notInhibited
    contract.machineEnabled contract.retiredRead

/-- The concrete premises for a link-writing decoded indirect `jalr` call. -/
structure JalrCallStepContract (stepNo : Nat) (state : State) where
  pc : BitVec 64
  rs1Val : BitVec 64
  retired : BitVec 64
  linkVal : BitVec 64
  imm : BitVec 12
  rs1 : regidx
  rd : regidx
  linkReg : Register
  linkRegVal : RegisterType linkReg
  inhibit : BitVec 32
  config : BitVec 64
  byte0 : BitVec 8
  byte1 : BitVec 8
  byte2 : BitVec 8
  byte3 : BitVec 8
  zcaEnabled : Bool
  hwrite : Runs (wX_bits rd linkVal)
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1))
    (callLinkState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg linkRegVal) ()
  linkNeNext : linkReg ≠ nextPC
  linkNeHart : linkReg ≠ hart_state
  linkNeIncrement : linkReg ≠ minstret_increment
  linkNeRetired : linkReg ≠ minstret
  platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc
  noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc
  bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3
  interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state)
  base : BaseInstructionEncoding byte0
  decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
    (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
    (.JALR (imm, rs1, rd))
  notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state)
  helpElp : Runs (update_elp_state rs1)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) ()
  hlink : Runs (get_next_pc ())
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) linkVal
  hrs1 : Runs (rX_bits rs1)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) rs1Val
  hbit1 : Sail.BitVec.access (rs1Val + sign_extend (m := 64) imm) 1 = 0#1
  hzca : Runs (currentlyEnabled extension.Ext_Zca)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) zcaEnabled
  hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ())
  inhibitRead : state.regs.get? mcountinhibit = some inhibit
  configRead : state.regs.get? minstretcfg = some config
  notInhibited : _get_Counterin_IR inhibit = 0#1
  machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1
  retiredRead : state.regs.get? minstret = some retired

/-- The aligned target selected by the indirect call. -/
def JalrCallStepContract.target
    {stepNo : Nat} {state : State} (contract : JalrCallStepContract stepNo state) : BitVec 64 :=
  Sail.BitVec.update (contract.rs1Val + sign_extend (m := 64) contract.imm) 0 0#1

/-- The exact generated postlude state of a link-writing indirect call. -/
def JalrCallStepContract.afterRetired
    {stepNo : Nat} {state : State} (contract : JalrCallStepContract stepNo state) : State :=
  tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement state) contract.pc contract.target
      contract.linkReg contract.linkRegVal)
    contract.target contract.retired

/-- Derive the `try_step` fact from the decoded indirect-call instruction contract. -/
theorem JalrCallStepContract.retire
    {stepNo : Nat} {state : State} (contract : JalrCallStepContract stepNo state) :
    Runs (try_step stepNo false) state contract.afterRetired false := by
  exact tryStepJalrCallRetires stepNo state contract.pc contract.rs1Val contract.retired
    contract.linkVal contract.imm contract.rs1 contract.rd contract.linkReg contract.linkRegVal
    contract.inhibit contract.config contract.byte0 contract.byte1 contract.byte2 contract.byte3
    contract.zcaEnabled contract.hwrite contract.linkNeNext contract.linkNeHart
    contract.linkNeIncrement contract.linkNeRetired contract.platform contract.noMMIO contract.bytes
    contract.interrupts contract.base contract.decode contract.notExpected contract.helpElp
    contract.hlink contract.hrs1 contract.hbit1 contract.hzca contract.hartRead contract.inhibitRead
    contract.configRead contract.notInhibited contract.machineEnabled contract.retiredRead

/--
Compose an actual `lw`, not-taken conditional branch, and link-writing `jalr` through their
instruction contracts. No `Runs (try_step ...)` fact is supplied: each one is derived above from
the decoded instruction, fetch/platform, and execution premises before `trace_steps` composes them.
-/
theorem traceRepresentativeMemoryBranchIndirectBlock (stepNo : Nat) (state : State)
    (memory : LoadWordStepContract stepNo state)
    (branch : NotTakenBranchStepContract (stepNo + 1) memory.afterRetired)
    (indirectCall : JalrCallStepContract ((stepNo + 1) + 1) branch.afterRetired) :
    Trace stepNo 3 state indirectCall.afterRetired := by
  trace_steps [memory.retire, branch.retire, indirectCall.retire]

private example (s0 s1 s2 s3 : State)
    (h0 : Runs (try_step 0 false) s0 s1 false)
    (h1 : Runs (try_step 1 false) s1 s2 false)
    (h2 : Runs (try_step 2 false) s2 s3 false) :
    Trace 0 3 s0 s3 := by
  trace_steps [h0, h1, h2]

private example (s0 s1 : State) (h0 : Runs (try_step 0 false) s0 s1 false) :
    Trace 0 1 s0 s1 := by
  trace_step h0
  exact Trace.refl _ _

end BinaryFv.RiscV
