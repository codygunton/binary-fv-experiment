import BinaryFv.Keccak.Reth.Proof.Helpers.Memset.Steps

/-!
# The `memset` loop

Single-iteration advance, the whole-loop trace by induction, and the loop exit.
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

end BinaryFv.Keccak
