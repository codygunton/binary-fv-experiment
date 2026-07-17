import BinaryFv.Keccak.Reth.Proof.XorBlock.BodyCore

/-!
# One iteration, and the whole 16-iteration loop
-/

namespace BinaryFv.Keccak.XorBlock
open BinaryFv.Binary
open BinaryFv.Keccak.SpecBridge
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open BinaryFv.Keccak
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Deliverable 4d: one taken loop iteration `xorblock_adv` -/

set_option maxHeartbeats 2000000 in
/-- One taken loop iteration (`k < 16`, so the back-edge `bnez` is taken): a length-29 trace from the
loop head `0x10c74` back to itself, re-establishing `XorBlockInv (k+1)`. -/
theorem xorblock_adv (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (sref : State) (start k : Nat) (s : State)
    (hk16 : k < 16)
    (hInv : XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref k s) :
    ∃ s', Trace (start + k * 29) 29 s s' ∧
      XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
        origLane inByte sref (k + 1) s' := by
  obtain ⟨s28, htr, hAt⟩ := xorblock_body_core state0 input0 retAddr image mseccfgBits mstatusBits
    inhibit cfg origLane inByte sref start k s (by omega) hInv
  obtain ⟨retired28, hret28⟩ := hAt.hminstret
  have hbytes28 : FetchBytesAt (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4)
      0xe3#8 0x18#8 0x06#8 0xf8#8 :=
    fetchBytesAt_10ce4 _ image hAt.himageEq hAt.hmatches
  have hplat28 : StepPlatform s28 (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8 mseccfgBits :=
    mkStepPlatform s28 mseccfgBits (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8
      hAt.hplat hAt.hcur hAt.hmseccfg (StableAgree.refl s28)
      ((afterIncGet s28 PC (by decide)).trans hAt.hPC) (by decide) hbytes28
  have hcnt28 : StepCounters s28 retired28 inhibit cfg :=
    ⟨hAt.hhart, hAt.hinhibit, hAt.hcfg, hAt.hnotInhibited, hAt.hmachineEnabled, hret28⟩
  have h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28)
      (BitVec.ofNat 64 0x10ce4)).regs.get? x12 = some (BitVec.ofNat 64 (136 - 8 * (k + 1))) :=
    (coreGetGP s28 (BitVec.ofNat 64 0x10ce4) x12 (by decide) (by decide)).trans hAt.ha2
  have hpcread : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28)
      (BitVec.ofNat 64 0x10ce4)).regs.get? PC = some (BitVec.ofNat 64 0x10ce4) :=
    (coreGetGP s28 (BitVec.ofNat 64 0x10ce4) PC (by decide) (by decide)).trans hAt.hPC
  obtain ⟨misaBits, _, _, hmisaA, _⟩ := hplat28.1
  have hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28)
      (BitVec.ofNat 64 0x10ce4)).regs.get? misa = some misaBits :=
    (coreGetInc (tryStepControlFlowAfterIncrement s28) _ misa (by decide)).trans hmisaA
  have hsum : BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)
      = BitVec.ofNat 64 0x10c74 := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have halign : Sail.BitVec.access (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) 0 = 0#1 := by rw [hsum]; decide
  have hbit1 : Sail.BitVec.access (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) 1 = 0#1 := by rw [hsum]; decide
  have hbnez := step_bnez_taken (start + k * 29 + 28) s28 (BitVec.ofNat 64 0x10ce4)
    (BitVec.ofNat 64 (136 - 8 * (k + 1))) retired28 mseccfgBits inhibit cfg hplat28 hcnt28 h12
    (a2_ne_zero (k + 1) (by omega)) hpcread misaBits hmisa halign hbit1
  have hSj : StableAgree s28 (tryStepControlFlowAfterRetired (controlFlowJumpState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13))) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28) :=
    stableAgree_jump s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28
  have hmemj : (tryStepControlFlowAfterRetired (controlFlowJumpState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13))) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28).mem = s28.mem :=
    (retiredMem _ _ _).trans (jumpMem s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)))
  refine ⟨(tryStepControlFlowAfterRetired (controlFlowJumpState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13))) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28), by simpa using Trace.append htr (Trace.one _ _ _ hbnez), ?_⟩
  refine ⟨?_, (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 x10 (by decide) (by decide) (by decide) (by decide)).trans hAt.ha0,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 x11 (by decide) (by decide) (by decide) (by decide)).trans hAt.ha1,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 x12 (by decide) (by decide) (by decide) (by decide)).trans hAt.ha2,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 x1 (by decide) (by decide) (by decide) (by decide)).trans hAt.hra,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 cur_privilege (by decide) (by decide) (by decide) (by decide)).trans hAt.hcur,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 mstatus (by decide) (by decide) (by decide) (by decide)).trans hAt.hmstatus,
    hAt.hmprv, (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 mseccfg (by decide) (by decide) (by decide) (by decide)).trans hAt.hmseccfg,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 hart_state (by decide) (by decide) (by decide) (by decide)).trans hAt.hhart,
    (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 mcountinhibit (by decide) (by decide) (by decide) (by decide)).trans hAt.hinhibit,
    hAt.hnotInhibited, (jumpRetiredGet s28 (BitVec.ofNat 64 0x10ce4) (BitVec.ofNat 64 0x10ce4 + sign_extend (m := 64) (0x1f90#13)) retired28 minstretcfg (by decide) (by decide) (by decide) (by decide)).trans hAt.hcfg,
    hAt.hmachineEnabled, ⟨_, retiredMinstret _ _ _⟩, hAt.himageEq, ?_, ?_, ?_, ?_,
    (by omega), hAt.hstateFits, hAt.hinputFits, hAt.hstateImg, hAt.hdisj,
    AbstractPlatform.mono hSj hAt.hplat, AbstractDataAccess.mono hSj hAt.hdata,
    AbstractElp.mono hSj hAt.hElp, hAt.hstable.trans hSj, ?_⟩
  · rw [retiredGetPC _ _ _, hsum]
  · rw [hmemj]; exact hAt.hmatches
  · intro m i hm hm2 hi; rw [hmemj]; exact hAt.hunproc m i hm hm2 hi
  · intro m i hm hi; rw [hmemj]; exact hAt.hproc m i hm hi
  · intro j hj; rw [hmemj]; exact hAt.hinput j hj
  · -- hframe (the taken back-edge writes no memory)
    exact memFramed_rate_intro (fun addr haddr => by
      rw [hmemj]; exact memFramed_rate_apply hAt.hframe addr haddr)

/-! ## Deliverable 5a: the whole 16-iteration taken loop `xorblock_loop` -/

/-- The 16 taken back-edge iterations from `XorBlockInv 0` to `XorBlockInv 16`. -/
theorem xorblock_loop (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (sref : State) (start : Nat) (s0 : State)
    (hInv0 : XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref 0 s0) :
    ∃ sN, Trace start (16 * 29) s0 sN ∧
      XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
        origLane inByte sref 16 sN :=
  Trace.invariantIterate (L := 29) (start := start)
    (Inv := fun k s => XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref k s) 16
    (fun k s hk hInv => xorblock_adv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref start k s hk hInv)
    hInv0

/-! ## Deliverable 5b: the final iteration and return `xorblock_exit` -/

set_option maxHeartbeats 2000000 in
/-- The 17th (last) iteration and return: run the body once more from `XorBlockInv 16` (`bnez` now
NOT taken, since `a2` reaches `0`), then `ret`.  The framed conclusion exposes the exact memory
delta: the 17 rate lanes are XORed, the 8 capacity lanes and the input block are preserved, the code
image (`matchesMemory`) is preserved, `PC = ra`, and — the general frame — every register outside `W`
and every byte outside the rate window still agrees with the reference state `sref`. -/
theorem xorblock_exit (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (sref : State) (start : Nat) (s : State)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hInv : XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte sref 16 s) :
    ∃ s'', Trace (start + 16 * 29) 30 s s'' ∧
      s''.regs.get? PC = some (Sail.BitVec.update retAddr 0 0#1) ∧
      s''.regs.get? x10 = some (state0 + BitVec.ofNat 64 136) ∧
      s''.regs.get? x11 = some (input0 + BitVec.ofNat 64 136) ∧
      s''.regs.get? x1 = some retAddr ∧
      (∀ m i : Nat, m < 17 → i < 8 → s''.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat
        = some ((origLane m ^^^ inputLane inByte m).extractLsb' (8 * i) 8)) ∧
      (∀ m i : Nat, 17 ≤ m → m < 25 → i < 8 → s''.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat
        = some ((origLane m).extractLsb' (8 * i) 8)) ∧
      (∀ j : Nat, j < 136 → s''.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (inByte j)) ∧
      image.matchesMemory s''.mem ∧
      StableAgree sref s'' ∧
      MemFramed state0 (BitVec.ofNat 64 136) sref s'' := by
  obtain ⟨s28, htr, hAt⟩ := xorblock_body_core state0 input0 retAddr image mseccfgBits mstatusBits
    inhibit cfg origLane inByte sref start 16 s (by omega) hInv
  obtain ⟨retired28, hret28⟩ := hAt.hminstret
  -- bnez NOT taken (a2 = 0)
  have hbytes28 : FetchBytesAt (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4)
      0xe3#8 0x18#8 0x06#8 0xf8#8 := fetchBytesAt_10ce4 _ image hAt.himageEq hAt.hmatches
  have hplat28 : StepPlatform s28 (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8 mseccfgBits :=
    mkStepPlatform s28 mseccfgBits (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8
      hAt.hplat hAt.hcur hAt.hmseccfg (StableAgree.refl s28)
      ((afterIncGet s28 PC (by decide)).trans hAt.hPC) (by decide) hbytes28
  have hcnt28 : StepCounters s28 retired28 inhibit cfg :=
    ⟨hAt.hhart, hAt.hinhibit, hAt.hcfg, hAt.hnotInhibited, hAt.hmachineEnabled, hret28⟩
  have h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28)
      (BitVec.ofNat 64 0x10ce4)).regs.get? x12 = some (BitVec.ofNat 64 (136 - 8 * 17)) :=
    (coreGetGP s28 (BitVec.ofNat 64 0x10ce4) x12 (by decide) (by decide)).trans hAt.ha2
  have hbnez := step_bnez_not_taken (start + 16 * 29 + 28) s28 (BitVec.ofNat 64 (136 - 8 * 17))
    retired28 mseccfgBits inhibit cfg hplat28 hcnt28 h12 a2_eq_zero
  have hSt1 : StableAgree s28 _ := stableAgree_notTaken s28 (BitVec.ofNat 64 0x10ce4) retired28
  have hmem1 : _ = s28.mem := notTakenMem s28 (BitVec.ofNat 64 0x10ce4) retired28
  have hPC1 := afterIncRetiredPC
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce4) 4) retired28
  have hmin1 := retiredMinstret
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce4) 4) retired28
  have hx10_1 : _ = some (state0 + BitVec.ofNat 64 (8 * 17)) :=
    (notTakenGet s28 (BitVec.ofNat 64 0x10ce4) retired28 x10 (by decide) (by decide) (by decide)
      (by decide)).trans hAt.ha0
  have hx11_1 : _ = some (input0 + BitVec.ofNat 64 (8 * 17)) :=
    (notTakenGet s28 (BitVec.ofNat 64 0x10ce4) retired28 x11 (by decide) (by decide) (by decide)
      (by decide)).trans hAt.ha1
  have hx1_1 : _ = some retAddr :=
    (notTakenGet s28 (BitVec.ofNat 64 0x10ce4) retired28 x1 (by decide) (by decide) (by decide)
      (by decide)).trans hAt.hra
  generalize hgen1 : tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s28) (BitVec.ofNat 64 0x10ce4))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce4) 4) retired28 = s29
    at hbnez hSt1 hmem1 hPC1 hmin1 hx10_1 hx11_1 hx1_1
  -- ret at 0x10ce8
  have hsum : Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce4) 4 = BitVec.ofNat 64 0x10ce8 := by decide
  have hbytes2 : FetchBytesAt (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8)
      0x67#8 0x80#8 0x00#8 0x00#8 :=
    fetchBytesAt_10ce8 _ image hAt.himageEq (hmem1.symm ▸ hAt.hmatches)
  have hplat2 : StepPlatform s29 (BitVec.ofNat 64 0x10ce8) 0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits :=
    mkStepPlatform s29 mseccfgBits (BitVec.ofNat 64 0x10ce8) 0x67#8 0x80#8 0x00#8 0x00#8
      hAt.hplat hAt.hcur hAt.hmseccfg hSt1 (hsum ▸ hPC1) (by decide) hbytes2
  have hcnt2 : StepCounters s29 (Sail.BitVec.addInt retired28 1) inhibit cfg :=
    ⟨(hSt1 hart_state (by decide)).trans hAt.hhart, (hSt1 mcountinhibit (by decide)).trans hAt.hinhibit,
      (hSt1 minstretcfg (by decide)).trans hAt.hcfg, hAt.hnotInhibited, hAt.hmachineEnabled, hmin1⟩
  have hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8))
      retAddr :=
    rX_bits_x1_run _ retAddr ((coreGetStable s29 _ x1 (by decide) hSt1).trans hAt.hra)
  obtain ⟨misaBits, _, _, hmisaA, _⟩ := hplat2.1
  have hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s29)
      (BitVec.ofNat 64 0x10ce8)).regs.get? misa = some misaBits :=
    (coreGetInc (tryStepControlFlowAfterIncrement s29) _ misa (by decide)).trans hmisaA
  have hElp1 : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8)) () :=
    hAt.hElp _ (.Regidx 1#5) rfl (coreStableAgree s29 (BitVec.ofNat 64 0x10ce8) hSt1)
  have hret := step_ret (start + 16 * 29 + 29) s29 retAddr (Sail.BitVec.addInt retired28 1)
    mseccfgBits misaBits inhibit cfg hplat2 hcnt2 hrs1 hretAlign hElp1 hmisa
  have hSt2 : StableAgree s28 _ :=
    hSt1.trans (stableAgree_jump s29 (BitVec.ofNat 64 0x10ce8)
      (Sail.BitVec.update retAddr 0 0#1) (Sail.BitVec.addInt retired28 1))
  have hmem2 : _ = s28.mem :=
    (retiredMem (controlFlowJumpState (tryStepControlFlowAfterIncrement s29) (BitVec.ofNat 64 0x10ce8)
      (Sail.BitVec.update retAddr 0 0#1)) (Sail.BitVec.update retAddr 0 0#1)
      (Sail.BitVec.addInt retired28 1)).trans
      ((jumpMem s29 (BitVec.ofNat 64 0x10ce8) (Sail.BitVec.update retAddr 0 0#1)).trans hmem1)
  refine ⟨_, ?_, retiredGetPC _ _ _,
    (jumpRetiredGet s29 (BitVec.ofNat 64 0x10ce8) (Sail.BitVec.update retAddr 0 0#1)
      (Sail.BitVec.addInt retired28 1) x10 (by decide) (by decide) (by decide) (by decide)).trans
      hx10_1,
    (jumpRetiredGet s29 (BitVec.ofNat 64 0x10ce8) (Sail.BitVec.update retAddr 0 0#1)
      (Sail.BitVec.addInt retired28 1) x11 (by decide) (by decide) (by decide) (by decide)).trans
      hx11_1,
    (jumpRetiredGet s29 (BitVec.ofNat 64 0x10ce8) (Sail.BitVec.update retAddr 0 0#1)
      (Sail.BitVec.addInt retired28 1) x1 (by decide) (by decide) (by decide) (by decide)).trans
      hx1_1, ?_, ?_, ?_, ?_, hAt.hstable.trans hSt2, ?_⟩
  · exact by simpa using Trace.append htr (Trace.step _ _ _ _ _ hbnez (Trace.one _ _ _ hret))
  · intro m i hm hi; rw [hmem2]; exact hAt.hproc m i (by omega) hi
  · intro m i hm hm2 hi; rw [hmem2]; exact hAt.hunproc m i hm hm2 hi
  · intro j hj; rw [hmem2]; exact hAt.hinput j hj
  · rw [hmem2]; exact hAt.hmatches
  · -- the general memory frame (the two exit steps write no memory)
    exact memFramed_rate_intro (fun addr haddr => by
      rw [hmem2]; exact memFramed_rate_apply hAt.hframe addr haddr)

end BinaryFv.Keccak.XorBlock
