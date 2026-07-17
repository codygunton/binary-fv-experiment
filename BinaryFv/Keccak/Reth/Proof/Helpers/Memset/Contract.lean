import BinaryFv.Keccak.Reth.Proof.Helpers.Memset.Loop

/-!
# The `memset` function contract

The capstone: preconditions, postconditions, and the composition of the parts above.
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
