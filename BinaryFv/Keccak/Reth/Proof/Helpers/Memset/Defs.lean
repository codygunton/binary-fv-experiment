import BinaryFv.Keccak.Reth.Proof.Helpers.Memset.ByteStore

/-!
# `memset` addresses, abstract premises, and the loop invariant
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

end BinaryFv.Keccak
