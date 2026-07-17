import BinaryFv.Keccak.Reth.Proof.Helpers.Memcpy.Invariant

/-!
# The `memcpy` loop

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
    hInv.hElp _ (.Regidx 1#5) rfl (coreStableAgree s1 (BitVec.ofNat 64 0x10d20) hSt1)
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

end BinaryFv.Keccak
