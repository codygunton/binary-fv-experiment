import BinaryFv.Keccak.Reth.Proof.XorBlock.Loop

/-!
# The `xor_block` operational contract

The capstone: the 496-step generated-`try_step` trace, its exact memory frame outside the
136-byte rate region, and the stable-register frame.
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

/-! ## Deliverable 5c: the capstone `xor_block_contract`

DESIGN NOTE (fetch-fact transparency).  This contract depends on the parser-derived fetch facts
(`XorBlockArtifactFetch`) ONLY through their `FetchBytesAt` conclusions — routed through the step
lemmas and `mkStepPlatform` — never through their `native_decide` internals.  That part of the trust
story stands: the fetch facts are closed statements about the pinned Nix-built ELF, and nothing about
the execution semantics, framing or spec correspondence below is decided natively.

CORRECTION (2026-07-16).  An earlier version of this note went on to claim that swapping the fetch
facts for kernel-checked versions would drop `Lean.ofReduceBool` / `Lean.trustCompiler` from this
theorem's axiom footprint.  That claim is FALSE and has been removed.  `bv_decide` discharges its
goals by checking an LRAT certificate whose evaluation goes through `Lean.reduceBool`, so *every*
`bv_decide` call that actually reaches the SAT backend contributes those two axioms on its own,
independently of any artifact fact.  `assemble_leWord` above is a pure `BitVec` identity with no
artifact dependency at all, and already carries them; so do the `Spec` bridges in deliverable 6.
(`bv_decide` calls closed by `bv_normalize` preprocessing alone — `slli_amount`, `li_val`, `sext8` —
do not.)  The honest statement is: this theorem's `Lean.ofReduceBool` / `Lean.trustCompiler`
footprint has two independent sources, the artifact fetch facts and the `bv_decide` LRAT checker, and
removing the former alone would not drop them. -/

/-- The entry `li a2, 136` value equals `136`. -/
theorem li_val : zero_reg + sign_extend (m := 64) 136#12 = BitVec.ofNat 64 136 := by
  have hz : (zero_reg : BitVec 64) = 0#64 := rfl
  rw [hz]
  simp only [sign_extend, Sail.BitVec.signExtend]
  bv_decide

set_option maxHeartbeats 2000000 in
/-- CAPSTONE.  `xor_block(state, input, 136)` at `0x10c6c`, run through the authoritative generated
`try_step` from a configured machine: a single `2 + 16*29 + 30 = 496`-step trace to the caller
(`PC = ra`), after which the 17 rate state lanes at `state0 + 8m` (`m < 17`) each hold
`origLane m ^^^ inputLane inByte m`.

The compositional side of the contract is exported as the *general* frame, not as a list of selected
observations:

* `MemFramed state0 136 s s''` — the exact memory delta.  `s''` agrees with the entry state `s` at
  every address the 136-byte rate window `[state0, state0+136)` does not cover, for an **arbitrary**
  address; the immediately following conjunct is the no-wraparound reading of that
  (`addr < state0` or `state0 + 136 ≤ addr` implies `s''.mem addr = s.mem addr`).
* `StableAgree s s''` — the register frame.  Every register outside `xor_block`'s written set
  `W = {PC, nextPC, minstret, minstret_increment, x5, x10..x17}` still holds its entry value.  This
  is honest about `W`: `a0`/`a1` are advanced by 136 and `a2`/`t0`/`a3..a7` are clobbered, so no
  preservation is claimed for them.

The capacity-lane (`17 ≤ m < 25`), input-block and code-image conclusions are kept, but are now
*derived from* the memory frame (all three regions lie outside the rate window) rather than tracked
as independent ad-hoc conclusions. -/
theorem xor_block_contract (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (origLane : Nat → BitVec 64) (inByte : Nat → BitVec 8) (start : Nat) (s : State)
    (hPC : s.regs.get? PC = some (BitVec.ofNat 64 0x10c6c))
    (ha0 : s.regs.get? x10 = some state0) (ha1 : s.regs.get? x11 = some input0)
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
    (hstate : ∀ m i : Nat, m < 25 → i < 8 →
      s.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat = some ((origLane m).extractLsb' (8 * i) 8))
    (hinput : ∀ j : Nat, j < 136 → s.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (inByte j))
    (hstateFits : state0.toNat + 200 ≤ 2 ^ 64) (hinputFits : input0.toNat + 136 ≤ 2 ^ 64)
    (hstateImg : ∀ j : Nat, j < 200 → image.readByte? (state0 + BitVec.ofNat 64 j).toNat = none)
    (hdisj : ∀ j j' : Nat, j < 200 → j' < 136 →
      (state0 + BitVec.ofNat 64 j).toNat ≠ (input0 + BitVec.ofNat 64 j').toNat)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hplat : AbstractPlatform s) (hdata : AbstractDataAccess state0 input0 s) (hElp : AbstractElp s) :
    ∃ s'', Trace start (2 + 16 * 29 + 30) s s'' ∧
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
      MemFramed state0 (BitVec.ofNat 64 136) s s'' ∧
      (∀ addr : Nat, addr < state0.toNat ∨ state0.toNat + 136 ≤ addr →
        s''.mem.get? addr = s.mem.get? addr) ∧
      StableAgree s s'' := by
  obtain ⟨retired0, hret0⟩ := hminstret
  -- Entry step 0: li a2, 136 at 0x10c6c.
  have hbytesE : FetchBytesAt (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c)
      0x13#8 0x06#8 0x80#8 0x08#8 := fetchBytesAt_10c6c _ image himageEq hmatches
  have hplatE : StepPlatform s (BitVec.ofNat 64 0x10c6c) 0x13#8 0x06#8 0x80#8 0x08#8 mseccfgBits :=
    mkStepPlatform s mseccfgBits (BitVec.ofNat 64 0x10c6c) 0x13#8 0x06#8 0x80#8 0x08#8
      hplat hcur hmseccfg (StableAgree.refl s) ((afterIncGet s PC (by decide)).trans hPC)
      (by decide) hbytesE
  have hcntE : StepCounters s retired0 inhibit cfg :=
    ⟨hhart, hinhibit, hcfg, hnotInhibited, hmachineEnabled, hret0⟩
  have hli := step_li_a2 start s retired0 mseccfgBits inhibit cfg hplatE hcntE
  have hStE : StableAgree s _ :=
    stableAgree_gp s (BitVec.ofNat 64 0x10c6c) retired0 x12 (zero_reg + sign_extend (m := 64) 136#12)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hmemE : _ = s.mem :=
    (retiredMem { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4) retired0).trans
      (fallThroughMem s (BitVec.ofNat 64 0x10c6c) x12 (zero_reg + sign_extend (m := 64) 136#12))
  have hPCE := afterIncRetiredPC
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
        (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4) retired0
  have hminE := retiredMinstret
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
        (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4) retired0
  have hx12E : _ = some (BitVec.ofNat 64 136) :=
    (fallThroughRetiredRd s (BitVec.ofNat 64 0x10c6c) retired0 x12
      (zero_reg + sign_extend (m := 64) 136#12) (by decide) (by decide)).trans (congrArg some li_val)
  have hx10E : _ = some state0 :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c6c) retired0 x12
      (zero_reg + sign_extend (m := 64) 136#12) x10 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ha0
  have hx11E : _ = some input0 :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c6c) retired0 x12
      (zero_reg + sign_extend (m := 64) 136#12) x11 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ha1
  have hx1E : _ = some retAddr :=
    (fallThroughRetiredGet s (BitVec.ofNat 64 0x10c6c) retired0 x12
      (zero_reg + sign_extend (m := 64) 136#12) x1 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hra
  generalize hgenE : tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement s) (BitVec.ofNat 64 0x10c6c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement s)
          (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4) retired0 = s1
    at hli hStE hmemE hPCE hminE hx12E hx10E hx11E hx1E
  -- Entry step 1: beqz a2 at 0x10c70 (NOT taken, a2 = 136).
  have hsumE : Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4 = BitVec.ofNat 64 0x10c70 := by decide
  have hbytes1 : FetchBytesAt (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c70)
      0x63#8 0x0c#8 0x06#8 0x06#8 := fetchBytesAt_10c70 _ image himageEq (hmemE.symm ▸ hmatches)
  have hplat1 : StepPlatform s1 (BitVec.ofNat 64 0x10c70) 0x63#8 0x0c#8 0x06#8 0x06#8 mseccfgBits :=
    mkStepPlatform s1 mseccfgBits (BitVec.ofNat 64 0x10c70) 0x63#8 0x0c#8 0x06#8 0x06#8
      hplat hcur hmseccfg hStE (hsumE ▸ hPCE) (by decide) hbytes1
  have hcnt1 : StepCounters s1 (Sail.BitVec.addInt retired0 1) inhibit cfg :=
    ⟨(hStE hart_state (by decide)).trans hhart, (hStE mcountinhibit (by decide)).trans hinhibit,
      (hStE minstretcfg (by decide)).trans hcfg, hnotInhibited, hmachineEnabled, hminE⟩
  have h12_1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10c70)).regs.get? x12 = some (BitVec.ofNat 64 136) :=
    (coreGetGP s1 (BitVec.ofNat 64 0x10c70) x12 (by decide) (by decide)).trans hx12E
  have hbeqz := step_beqz_not_taken (start + 1) s1 (BitVec.ofNat 64 136) (Sail.BitVec.addInt retired0 1)
    mseccfgBits inhibit cfg hplat1 hcnt1 h12_1 (a2_ne_zero 0 (by omega))
  have hSt1 : StableAgree s _ :=
    hStE.trans (stableAgree_notTaken s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1))
  have hmem1 : _ = s.mem :=
    (notTakenMem s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1)).trans hmemE
  have hPC1 := afterIncRetiredPC
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c70))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4) (Sail.BitVec.addInt retired0 1)
  have hmin1 := retiredMinstret
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c70))
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4) (Sail.BitVec.addInt retired0 1)
  have hx12_1 : _ = some (BitVec.ofNat 64 (136 - 8 * 0)) :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1) x12 (by decide)
      (by decide) (by decide) (by decide)).trans hx12E
  have hx10_1 : _ = some state0 :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1) x10 (by decide)
      (by decide) (by decide) (by decide)).trans hx10E
  have hx11_1 : _ = some input0 :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1) x11 (by decide)
      (by decide) (by decide) (by decide)).trans hx11E
  have hx1_1 : _ = some retAddr :=
    (notTakenGet s1 (BitVec.ofNat 64 0x10c70) (Sail.BitVec.addInt retired0 1) x1 (by decide)
      (by decide) (by decide) (by decide)).trans hx1E
  have hPCval1 : (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c70))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4) (Sail.BitVec.addInt retired0 1)).regs.get? PC
      = some (BitVec.ofNat 64 0x10c74) := by
    rw [retiredGetPC, show Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4
      = BitVec.ofNat 64 0x10c74 from by decide]
  generalize hgen1 : tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10c70))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4) (Sail.BitVec.addInt retired0 1) = s2
    at hbeqz hSt1 hmem1 hPC1 hmin1 hx12_1 hx10_1 hx11_1 hx1_1 hPCval1
  -- Establish `XorBlockInv 0` at `s2` (PC = 0x10c74).
  -- The two entry steps write no memory, so the frame relative to `s` starts trivially.
  have hInv0 : XorBlockInv state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      origLane inByte s 0 s2 := by
    refine ⟨?_, by simpa using hx10_1, by simpa using hx11_1, hx12_1, hx1_1,
      (hSt1 cur_privilege (by decide)).trans hcur,
      (hSt1 mstatus (by decide)).trans hmstatus, hmprv, (hSt1 mseccfg (by decide)).trans hmseccfg,
      (hSt1 hart_state (by decide)).trans hhart, (hSt1 mcountinhibit (by decide)).trans hinhibit,
      hnotInhibited, (hSt1 minstretcfg (by decide)).trans hcfg, hmachineEnabled, ⟨_, hmin1⟩,
      himageEq, ?_, ?_, ?_, ?_, (by omega), hstateFits, hinputFits, hstateImg, hdisj,
      AbstractPlatform.mono hSt1 hplat, AbstractDataAccess.mono hSt1 hdata,
      AbstractElp.mono hSt1 hElp, hSt1, ?_⟩
    · exact hPCval1
    · rw [hmem1]; exact hmatches
    · intro m i _ hm2 hi; rw [hmem1]; exact hstate m i hm2 hi
    · intro m i hm _; exact absurd hm (Nat.not_lt_zero m)
    · intro j hj; rw [hmem1]; exact hinput j hj
    · exact memFramed_rate_intro (fun addr _ => by rw [hmem1])
  -- Loop (16 taken iterations) then exit (final iteration + ret).
  obtain ⟨sN, htrLoop, hInvN⟩ := xorblock_loop state0 input0 retAddr image mseccfgBits mstatusBits
    inhibit cfg origLane inByte s (start + 2) s2 hInv0
  obtain ⟨s'', htrExit, hPCret, hx10N, hx11N, hx1N, hrate, _hcap, _hinp, _hcode, hstableN,
      hframeN⟩ :=
    xorblock_exit state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg origLane inByte
      s (start + 2) sN hretAlign hInvN
  -- The no-wraparound reading of the general frame.
  have hfitsRate : state0.toNat + (BitVec.ofNat 64 136).toNat ≤ 2 ^ 64 := by
    rw [rateWidth_toNat]; omega
  have houtside : ∀ addr : Nat, addr < state0.toNat ∨ state0.toNat + 136 ≤ addr →
      s''.mem.get? addr = s.mem.get? addr := fun addr hout =>
    MemFramed.mem_unchanged_outside hframeN hfitsRate addr (by rw [rateWidth_toNat]; exact hout)
  -- Capacity lanes: `8m + i ∈ [136, 200)` lies above the rate window.
  have hcap : ∀ m i : Nat, 17 ≤ m → m < 25 → i < 8 →
      s''.mem.get? (state0 + BitVec.ofNat 64 (8 * m + i)).toNat
        = some ((origLane m).extractLsb' (8 * i) 8) := by
    intro m i hm hm2 hi
    rw [houtside _ (Or.inr (by rw [dstAddr_toNat state0 (8 * m + i) (by omega)]; omega))]
    exact hstate m i hm2 hi
  -- Input block: disjoint from the state region by `hdisj`, hence outside the rate window.
  have hinp : ∀ j : Nat, j < 136 →
      s''.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (inByte j) := by
    intro j hj
    refine (MemFramed.source_preserved (src := input0) hframeN ?_ j ?_).trans (hinput j hj)
    · intro a b ha hb
      rw [rateWidth_toNat] at ha hb
      exact hdisj a b (by omega) hb
    · rw [rateWidth_toNat]; exact hj
  -- Code image: the image backs no byte of the state region, so the frame carries it.
  have hcode : image.matchesMemory s''.mem :=
    matchesMemory_of_rate_frame hframeN hstateImg hmatches
  refine ⟨s'', ?_, hPCret, hx10N, hx11N, hx1N, hrate, hcap, hinp, hcode, hframeN, houtside,
    hstableN⟩
  have htrEntry : Trace start 2 s s2 :=
    Trace.step _ _ _ _ _ hli (Trace.one _ _ _ hbeqz)
  have hcomb := Trace.append (Trace.append htrEntry htrLoop) htrExit
  simpa using hcomb

end BinaryFv.Keccak.XorBlock
