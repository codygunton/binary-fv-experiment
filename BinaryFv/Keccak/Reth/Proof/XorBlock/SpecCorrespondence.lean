import BinaryFv.Keccak.Reth.Proof.XorBlock.Contract

/-!
# Correspondence with `Spec.Keccak`

Relates the operational contract's memory postcondition to `Spec.Keccak.xorBytesIntoState`, via
the pure bridges in `Keccak.SpecBridge.Lanes`.
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

/-! ## Deliverable 6: correspondence with the executable Keccak-256 specification

`Spec.Keccak.xorBytesIntoState st input 136` (`Spec/Keccak/Keccak256.lean`) is the specification's
rate-block absorb: the 25-lane `Array UInt64` whose lane `i` is `st[i]! ^^^ Spec.Keccak.inputLane
input i` for `i < 136 / 8 = 17`, and `st[i]!` otherwise.  The machine, by contrast, works on a flat
byte memory, so the correspondence needs an explicit memory ↔ `Array UInt64` relation.  We do not
invent one: `StateImage` / `InputImage` below say the machine's memory at `state0` / `input0` *is*
the specification's own serialization (`Spec.Keccak.stateByte`, `ByteArray.data`).  They are stated
as definitions and appear as an explicit hypothesis (on the entry state) and an explicit conclusion
(on the exit state) of `xor_block_matches_spec` — the honest framing, since nothing in the machine
semantics privileges any particular lane encoding.

The two load-bearing bridges are pure `bv_decide` identities. Their LRAT certificates are checked
through native evaluation under the proof-of-concept trust policy recorded in the repository README:

* `specInputLane_toBitVec` — the machine's little-endian `leWord` of the 8 input bytes at
  `input0 + 8k` (produced by the body's 8 `lbu` + 6 `slli` + 6 `or`, cf. `assemble_leWord`) equals
  `Spec.Keccak.inputLane input k`.  This is the `UInt64 ↔ BitVec 64` bridge over the spec's
  `|||` / `<<<` / `toUInt64` fold.
* `specStateByte_toBitVec` — the machine's per-lane byte extraction `lane.extractLsb' (8i) 8` equals
  the spec's `stateByte` at flat index `8m + i`. -/

/-- BRIDGE (input lane).  The spec's `inputLane` fold over `List.range 8` — `acc ||| b <<< 8j` on
`UInt64` — is the machine's little-endian `leWord` of the same 8 bytes. -/
theorem specInputLane_toBitVec (input : ByteArray) (inByte : Nat → BitVec 8) (k : Nat)
    (hsize : input.size = 136) (hk : k < 17)
    (hb : ∀ j : Nat, j < 8 → (input.data[8 * k + j]!).toBitVec = inByte (8 * k + j)) :
    (Spec.Keccak.inputLane input k).toBitVec = inputLane inByte k := by
  unfold Spec.Keccak.inputLane inputLane
  simp only [List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil, List.foldl_append,
    hsize,
    if_pos (show 8 * k + 0 < 136 by omega), if_pos (show 8 * k + 1 < 136 by omega),
    if_pos (show 8 * k + 2 < 136 by omega), if_pos (show 8 * k + 3 < 136 by omega),
    if_pos (show 8 * k + 4 < 136 by omega), if_pos (show 8 * k + 5 < 136 by omega),
    if_pos (show 8 * k + 6 < 136 by omega), if_pos (show 8 * k + 7 < 136 by omega)]
  rw [← hb 0 (by omega), ← hb 1 (by omega), ← hb 2 (by omega), ← hb 3 (by omega),
    ← hb 4 (by omega), ← hb 5 (by omega), ← hb 6 (by omega), ← hb 7 (by omega)]
  simp only [leWord, List.length_cons, List.length_nil,
    show Nat.toUInt64 0 = (0 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 1) = (8 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 2) = (16 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 3) = (24 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 4) = (32 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 5) = (40 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 6) = (48 : UInt64) from rfl,
    show Nat.toUInt64 (8 * 7) = (56 : UInt64) from rfl]
  bv_decide

/-- The machine memory at `[state0, state0+200)` *is* the spec's 200-byte little-endian serialization
of the 25-lane state `st` (`Spec.Keccak.stateByte`). -/
def StateImage (state0 : BitVec 64) (st : Array UInt64) (s : State) : Prop :=
  ∀ i : Nat, i < 200 →
    s.mem.get? (state0 + BitVec.ofNat 64 i).toNat = some (Spec.Keccak.stateByte st i).toBitVec

/-- The machine memory at `[input0, input0+136)` *is* the spec's 136-byte rate block. -/
def InputImage (input0 : BitVec 64) (input : ByteArray) (s : State) : Prop :=
  ∀ j : Nat, j < 136 →
    s.mem.get? (input0 + BitVec.ofNat 64 j).toNat = some (input.data[j]!).toBitVec

set_option maxHeartbeats 1000000 in
/-- SPEC CORRESPONDENCE.  Run from a configured machine whose memory holds the serialized spec state
`st` at `state0` and the spec's 136-byte rate block `input` at `input0`, the operational `xor_block`
(the same 496-step generated-`try_step` trace as `xor_block_contract`) returns to the caller with
memory holding *exactly the serialization of* `Spec.Keccak.xorBytesIntoState st input 136` — all 25
lanes, so this pins the XORed 17 rate lanes and the 8 untouched capacity lanes simultaneously.  The
input block, the code image, and the register/memory frames are carried over from the capstone. -/
theorem xor_block_matches_spec (state0 input0 retAddr : BitVec 64) (image : ProgramImage)
    (mseccfgBits mstatusBits : BitVec 64) (inhibit : BitVec 32) (cfg : BitVec 64)
    (st : Array UInt64) (input : ByteArray) (start : Nat) (s : State)
    (hsize : input.size = 136)
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
    (hstateImage : StateImage state0 st s) (hinputImage : InputImage input0 input s)
    (hstateFits : state0.toNat + 200 ≤ 2 ^ 64) (hinputFits : input0.toNat + 136 ≤ 2 ^ 64)
    (hstateImg : ∀ j : Nat, j < 200 → image.readByte? (state0 + BitVec.ofNat 64 j).toNat = none)
    (hdisj : ∀ j j' : Nat, j < 200 → j' < 136 →
      (state0 + BitVec.ofNat 64 j).toNat ≠ (input0 + BitVec.ofNat 64 j').toNat)
    (hretAlign : Sail.BitVec.access retAddr 1 = 0#1)
    (hplat : AbstractPlatform s) (hdata : AbstractDataAccess state0 input0 s) (hElp : AbstractElp s) :
    ∃ s'', Trace start (2 + 16 * 29 + 30) s s'' ∧
      s''.regs.get? PC = some (Sail.BitVec.update retAddr 0 0#1) ∧
      StateImage state0 (Spec.Keccak.xorBytesIntoState st input 136) s'' ∧
      InputImage input0 input s'' ∧
      image.matchesMemory s''.mem ∧
      MemFramed state0 (BitVec.ofNat 64 136) s s'' ∧
      StableAgree s s'' := by
  obtain ⟨s'', htr, hPCret, _hx10, _hx11, _hx1, hrate, hcap, hinp, hcode, hframe, _houtside,
      hstable⟩ :=
    xor_block_contract state0 input0 retAddr image mseccfgBits mstatusBits inhibit cfg
      (fun m => (st[m]!).toBitVec) (fun j => (input.data[j]!).toBitVec) start s
      hPC ha0 ha1 hra hcur hmstatus hmprv hmseccfg hhart hinhibit hnotInhibited hcfg hmachineEnabled
      hminstret himageEq hmatches
      (fun m i _hm hi =>
        (hstateImage (8 * m + i) (by omega)).trans (congrArg some (specStateByte_toBitVec st m i hi)))
      hinputImage hstateFits hinputFits hstateImg hdisj hretAlign hplat hdata hElp
  refine ⟨s'', htr, hPCret, ?_, hinp, hcode, hframe, hstable⟩
  intro i hi
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 8 ∧ i = 8 * m + r := ⟨i / 8, i % 8, by omega, by omega⟩
  rw [specStateByte_toBitVec _ m r hr, xorBytesIntoState_lane st input m (by omega)]
  rcases Nat.lt_or_ge m 17 with hm17 | hm17
  · -- rate lane: the machine's XOR is the spec's `st[m]! ^^^ inputLane input m`
    have hlane : (st[m]! ^^^ Spec.Keccak.inputLane input m).toBitVec
        = (st[m]!).toBitVec ^^^ inputLane (fun j => (input.data[j]!).toBitVec) m := by
      rw [show ((st[m]! ^^^ Spec.Keccak.inputLane input m).toBitVec)
            = st[m]!.toBitVec ^^^ (Spec.Keccak.inputLane input m).toBitVec from rfl,
        specInputLane_toBitVec input (fun j => (input.data[j]!).toBitVec) m hsize hm17
          (fun j _ => rfl)]
    rw [if_pos hm17, hrate m r hm17 hr, hlane]
  · -- capacity lane: untouched by both
    rw [if_neg (by omega)]
    exact hcap m r hm17 (by omega) hr

end BinaryFv.Keccak.XorBlock
