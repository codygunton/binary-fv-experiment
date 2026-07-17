import BinaryFv.Keccak.Reth.Proof.Helpers.CopyFromSlice.Steps

/-!
# The `copy_from_slice` function contract

The capstone. Conditional on `dst_len = src_len`, under which the panic branch is demonstrably
not taken. Discharging that equality at each real call site belongs to the caller stage.
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
