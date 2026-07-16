import BinaryFv.Keccak.CoreStoreStepContract
import BinaryFv.Keccak.StoreArtifactFetch
import BinaryFv.RISCV.SepLogic

/-!
# CAPSTONE: a separation-logic `Triple` for the real ELF store `sd a3, 0(a0)`

This module states and proves the capstone theorem for the fixed real-ELF store
`10cdc: 00d53023  sd a3, 0(a0)` (little-endian instruction bytes `23 30 d5 00`).  It composes the
authoritative generated `try_step` rule delivered by `tryStepCoreStoreRetires` with the bespoke
memory-only separation logic of `BinaryFv.RISCV.Sep`.

The theorem asserts, through the landed `Sep.Triple` API, that running the store through the
generated `try_step`:

* updates exactly its owned 8-byte destination window to the little-endian word of `a3`
  (`bytes dst vs₀  ↝  wordLE dst dataBits`),
* preserves the owned code bytes at `0x10cdc`,
* preserves an arbitrary disjoint memory frame,
* and lands the architectural PC/`minstret` postcondition.

The non-memory preconditions of the generated rule are bundled verbatim into the ordinary state
assertion `StoreStepPre`; the two memory obligations (`FetchBytesAt` for the owned code and the
physical `writeBytes` run) are *derived* from the owned separation-logic resources rather than
assumed.
-/

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RISCV
open BinaryFv.RISCV.Sep
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-- The fixed program counter of the real ELF store `sd a3, 0(a0)`. -/
def pcAddr : Nat := 0x10cdc

/-- The little-endian instruction bytes of `10cdc: 00d53023  sd a3, 0(a0)`. -/
def sdCodeBytes : List (BitVec 8) := [0x23#8, 0x30#8, 0xd5#8, 0x00#8]

/-- The register file after the generated `try_step` retires the store: exactly the four register
writes performed by `try_step` — the counter-increment flag `minstret_increment ↦ true`, the ticked
`nextPC ↦ pc+4` and `PC ↦ pc+4`, and the bumped `minstret ↦ retired+1` — applied to the pre-step
register file `regs0`.  Everything else is preserved.  Exposing this exact relation (rather than just
the `PC`/`minstret` facts, which it subsumes) lets the next instruction be chained via `triple_bind`. -/
def sdStoreRegsAfter (regs0 : Std.ExtDHashMap Register RegisterType) (pc retired : BitVec 64) :
    Std.ExtDHashMap Register RegisterType :=
  (((regs0.insert minstret_increment true).insert nextPC (Sail.BitVec.addInt pc 4)).insert PC
    (Sail.BitVec.addInt pc 4)).insert minstret (Sail.BitVec.addInt retired 1)

/--
Every non-memory precondition of `tryStepCoreStoreRetires`, bundled as an ordinary
`StateAssertion` about the pre-step state.  The two memory obligations of the generated rule —
`FetchBytesAt` (derived from owned code bytes) and the physical `writeBytes` run (derived from the
owned destination window) — are deliberately excluded; they are discharged from separation-logic
resources at the `Triple` layer.  The fixed program counter is `BitVec.ofNat 64 pcAddr`.
-/
def StoreStepPre (_stepNo : Nat) (dstBits dataBits retired mstatusBits mseccfgBits config : BitVec 64)
    (inhibit : BitVec 32) (regs0 : Std.ExtDHashMap Register RegisterType) : StateAssertion :=
    fun state =>
  FetchBasePlatform (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr) ∧
  FetchMemoryNoMMIO (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr) ∧
  InterruptDisabled (tryStepCoreStoreAfterIncrement state) ∧
  (tryStepCoreStoreAfterIncrement state).regs.get? mseccfg = some mseccfgBits ∧
  LandingPadNotExpected (tryStepCoreStoreAfterIncrement state) ∧
  (coreStoreNextState (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr)).regs.get?
      mstatus = some mstatusBits ∧
  (coreStoreNextState (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr)).regs.get?
      cur_privilege = some Privilege.Machine ∧
  _get_Mstatus_MPRV mstatusBits = 0#1 ∧
  Runs (rX_bits a3reg)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr))
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr))
      dataBits ∧
  Runs (get_transformed_data_addr a0reg (sign_extend (m := 64) 0#12) (Store Data) 8)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr))
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr))
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)) ∧
  is_aligned_vaddr (virtaddr.Virtaddr dstBits) 8 = true ∧
  Runs (phys_access_check (Store Data) PBMT_PMA .Machine (physaddr.Physaddr dstBits) 8 false)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr))
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr)) none ∧
  Runs (within_mmio_writable (physaddr.Physaddr dstBits) 8)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr))
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) (BitVec.ofNat 64 pcAddr)) false ∧
  state.regs.get? hart_state = some (.HART_ACTIVE ()) ∧
  state.regs.get? mcountinhibit = some inhibit ∧
  state.regs.get? minstretcfg = some config ∧
  _get_Counterin_IR inhibit = 0#1 ∧
  _get_CountSmcntrpmf_MINH config = 0#1 ∧
  state.regs.get? minstret = some retired ∧
  state.regs = regs0

/--
CAPSTONE.  The real ELF store `sd a3, 0(a0)` at `0x10cdc`, executed through the authoritative
generated `try_step`, updates exactly its owned 8-byte destination to the little-endian word of
`a3`, preserving the owned code bytes and an arbitrary disjoint memory frame, and lands the
architectural PC/`minstret` postcondition — all expressed through the `Sep.Triple` API.
-/
theorem sd_store_triple (stepNo : Nat) (dstBits : BitVec 64) (dataBits : BitVec (8 * 8))
    (vs₀ : List (BitVec 8)) (hlen : vs₀.length = 8)
    (retired mstatusBits mseccfgBits config : BitVec 64) (inhibit : BitVec 32)
    (regs0 : Std.ExtDHashMap Register RegisterType) :
    Triple
      (StoreStepPre stepNo dstBits dataBits retired mstatusBits mseccfgBits config inhibit regs0)
      (bytes pcAddr sdCodeBytes ⋆ bytes dstBits.toNat vs₀)
      (try_step stepNo false)
      (fun _ s => s.regs = sdStoreRegsAfter regs0 (BitVec.ofNat 64 pcAddr) retired)
      (fun _ => bytes pcAddr sdCodeBytes ⋆ wordLE dstBits.toNat dataBits) := by
  intro s hp hf hS hP hdisj hsplit
  -- The pc as a bit-vector, with the identity `pc.toNat = pcAddr`.
  have hpcNat : (BitVec.ofNat 64 pcAddr).toNat = pcAddr := by
    rw [BitVec.toNat_ofNat]; decide
  -- Memory bridge: apply the framed word-store triple at the pre-write state.  Because that state
  -- differs from `s` only in registers, the heap split `hsplit` transfers verbatim.
  have MW := triple_frame_left (F := bytes pcAddr sdCodeBytes)
    (triple_writeWord (fun _ => True) memInsensitive_true dstBits.toNat dataBits vs₀ hlen)
  obtain ⟨sw, rw, hp', hRunW, _hTW, hQW, hdisj', hsplitW⟩ :=
    MW (coreStoreNextState (tryStepCoreStoreAfterIncrement s) (BitVec.ofNat 64 pcAddr)) hp hf
      trivial hP hdisj hsplit
  obtain ⟨hc, hd, hcd, hp'eq, hbytesC, hrwTrue, hwordLE⟩ := hQW
  subst hrwTrue
  -- Owned code bytes: derive the generated four-byte fetch fact from the owned `bytes` resource.
  obtain ⟨h_code, _h_dst, _hcd_disj, hp_eq, h_code_bytes, _h_dst_bytes⟩ := hP
  have lift : ∀ (a : Nat) (v : BitVec 8), h_code a = some v → s.mem.get? a = some v := by
    intro a v ha
    have hpa : hp a = some v := by rw [hp_eq]; exact union_apply_of_left ha
    have hsa : stateHeap s a = some v := by rw [hsplit]; exact union_apply_of_left hpa
    exact hsa
  have bytesFetch : FetchBytesAt (tryStepCoreStoreAfterIncrement s) (BitVec.ofNat 64 pcAddr)
      0x23#8 0x30#8 0xd5#8 0x00#8 := by
    unfold FetchBytesAt
    rw [hpcNat]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact lift pcAddr 0x23#8 (bytes_get pcAddr sdCodeBytes h_code h_code_bytes 0 (by decide))
    · exact lift (pcAddr + 1) 0x30#8 (bytes_get pcAddr sdCodeBytes h_code h_code_bytes 1 (by decide))
    · exact lift (pcAddr + 2) 0xd5#8 (bytes_get pcAddr sdCodeBytes h_code h_code_bytes 2 (by decide))
    · exact lift (pcAddr + 3) 0x00#8 (bytes_get pcAddr sdCodeBytes h_code h_code_bytes 3 (by decide))
  -- Unpack every non-memory precondition of the generated rule (including the register-frame base).
  obtain ⟨platform, noMMIO, interrupts, mseccfgRead, notExpected, mstatusReadExec, privReadExec,
    mprvZero, dataReg, addrReg, aligned, physAccess, noMMIOwrite, hartRead, inhibitRead, configRead,
    notInhibited, machineEnabled, retiredRead, hRegs0⟩ := hS
  -- Run the authoritative generated `try_step`.
  have hrun := tryStepCoreStoreRetires stepNo s sw (BitVec.ofNat 64 pcAddr) dstBits mstatusBits
    retired dataBits inhibit config platform noMMIO bytesFetch interrupts mseccfgBits mseccfgRead
    notExpected mstatusReadExec privReadExec mprvZero dataReg addrReg aligned physAccess noMMIOwrite
    hRunW hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  -- Architectural postcondition: the exact register-file update after the retirement bookkeeping.
  -- The final `.regs` is `(sw.regs.insert PC (pc+4)).insert minstret (retired+1)`; since `writeBytes`
  -- only touches memory, `sw.regs = (s.regs.insert minstret_increment true).insert nextPC (pc+4)`.
  have hRegsAfter : (tryStepCoreStoreAfterRetired sw (BitVec.ofNat 64 pcAddr) retired).regs
      = sdStoreRegsAfter regs0 (BitVec.ofNat 64 pcAddr) retired := by
    show (sw.regs.insert PC (Sail.BitVec.addInt (BitVec.ofNat 64 pcAddr) 4)).insert minstret
        (Sail.BitVec.addInt retired 1) = sdStoreRegsAfter regs0 (BitVec.ofNat 64 pcAddr) retired
    rw [writeBytes_preserves_regs dstBits.toNat dataBits
      (coreStoreNextState (tryStepCoreStoreAfterIncrement s) (BitVec.ofNat 64 pcAddr)) sw hRunW]
    simp only [coreStoreNextState, tryStepCoreStoreAfterIncrement, sdStoreRegsAfter]
    rw [hRegs0]
  -- Assemble the framed triple's existential witness.
  exact ⟨tryStepCoreStoreAfterRetired sw (BitVec.ofNat 64 pcAddr) retired, false, hp', hrun,
    hRegsAfter, ⟨hc, hd, hcd, hp'eq, hbytesC, hwordLE⟩, hdisj', hsplitW⟩

/--
Every non-memory precondition of `tryStepCoreStoreRetires` (bundled verbatim as `StoreStepPre`),
plus the *persistent code-image assertion*: the embedded canonical Reth Keccak ELF parses to some
`image` whose bytes agree with the sparse memory at the pre-step state.  This replaces owning the
literal code bytes at `0x10cdc`; the fetched instruction bytes are derived from the parser and this
`matchesMemory` assertion rather than assumed.  Recall `(tryStepCoreStoreAfterIncrement state).mem`
is definitionally `state.mem`.
-/
def StoreStepPreElf (stepNo : Nat) (dstBits dataBits retired mstatusBits mseccfgBits config : BitVec 64)
    (inhibit : BitVec 32) (regs0 : Std.ExtDHashMap Register RegisterType) : StateAssertion :=
    fun state =>
  StoreStepPre stepNo dstBits dataBits retired mstatusBits mseccfgBits config inhibit regs0 state ∧
    ∃ image, Artifact.programImage = .ok image ∧
      image.matchesMemory (tryStepCoreStoreAfterIncrement state).mem ∧
      (∀ k, k < 8 → image.readByte? (dstBits.toNat + k) = none)

/--
CAPSTONE (ELF-derived).  Same as `sd_store_triple`, but the fetched code bytes are *derived* from
the embedded canonical ELF and the persistent framed code-image assertion (`matchesMemory`, carried
in the state precondition `StoreStepPreElf`) rather than owned as a literal `bytes` resource.  The
owned memory is only the 8-byte destination window; the code image survives in the arbitrary
disjoint frame, preserved automatically by the `Triple`'s frame guarantee.
-/
theorem sd_store_triple_elf (stepNo : Nat) (dstBits : BitVec 64) (dataBits : BitVec (8 * 8))
    (vs₀ : List (BitVec 8)) (hlen : vs₀.length = 8)
    (retired mstatusBits mseccfgBits config : BitVec 64) (inhibit : BitVec 32)
    (regs0 : Std.ExtDHashMap Register RegisterType) :
    Triple
      (StoreStepPreElf stepNo dstBits dataBits retired mstatusBits mseccfgBits config inhibit regs0)
      (bytes dstBits.toNat vs₀)
      (try_step stepNo false)
      (fun _ s => s.regs = sdStoreRegsAfter regs0 (BitVec.ofNat 64 pcAddr) retired
                  ∧ ∃ image, Artifact.programImage = .ok image ∧ image.matchesMemory s.mem)
      (fun _ => wordLE dstBits.toNat dataBits) := by
  intro s hp hf hS hP hdisj hsplit
  -- Split the precondition into the bundled non-memory facts and the persistent code-image
  -- assertion (the parsed ELF `image`, its pointwise agreement with the pre-step memory, and the
  -- fact that the image does not back the owned destination window).
  obtain ⟨hSbase, image, imageEq, loaded, imgDstNone⟩ := hS
  -- Memory bridge: apply the plain framed word-store triple at the pre-write state.  Because that
  -- state differs from `s` only in registers, the heap split `hsplit` transfers verbatim.
  have MW := triple_writeWord (fun _ => True) memInsensitive_true dstBits.toNat dataBits vs₀ hlen
  obtain ⟨sw, rw, hp', hRunW, _hTW, hQW, hdisj', hsplitW⟩ :=
    MW (coreStoreNextState (tryStepCoreStoreAfterIncrement s) (BitVec.ofNat 64 pcAddr)) hp hf
      trivial hP hdisj hsplit
  obtain ⟨hrwTrue, hwordLE⟩ := hQW
  subst hrwTrue
  -- Code image: derive the generated four-byte fetch fact from the persistent code-image assertion
  -- via the embedded ELF parser, rather than from owned literal code bytes.  The `.mem` of
  -- `tryStepCoreStoreAfterIncrement s` is definitionally `s.mem`, so `loaded` applies directly.
  have bytesFetch : FetchBytesAt (tryStepCoreStoreAfterIncrement s) (BitVec.ofNat 64 pcAddr)
      0x23#8 0x30#8 0xd5#8 0x00#8 :=
    sdStoreWord_fetchBytesAt (tryStepCoreStoreAfterIncrement s) image imageEq loaded
  -- Unpack every non-memory precondition of the generated rule (including the register-frame base).
  obtain ⟨platform, noMMIO, interrupts, mseccfgRead, notExpected, mstatusReadExec, privReadExec,
    mprvZero, dataReg, addrReg, aligned, physAccess, noMMIOwrite, hartRead, inhibitRead, configRead,
    notInhibited, machineEnabled, retiredRead, hRegs0⟩ := hSbase
  -- Run the authoritative generated `try_step`.
  have hrun := tryStepCoreStoreRetires stepNo s sw (BitVec.ofNat 64 pcAddr) dstBits mstatusBits
    retired dataBits inhibit config platform noMMIO bytesFetch interrupts mseccfgBits mseccfgRead
    notExpected mstatusReadExec privReadExec mprvZero dataReg addrReg aligned physAccess noMMIOwrite
    hRunW hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  -- Architectural postcondition (register frame): the exact register-file update after retirement.
  have hRegsAfter : (tryStepCoreStoreAfterRetired sw (BitVec.ofNat 64 pcAddr) retired).regs
      = sdStoreRegsAfter regs0 (BitVec.ofNat 64 pcAddr) retired := by
    show (sw.regs.insert PC (Sail.BitVec.addInt (BitVec.ofNat 64 pcAddr) 4)).insert minstret
        (Sail.BitVec.addInt retired 1) = sdStoreRegsAfter regs0 (BitVec.ofNat 64 pcAddr) retired
    rw [writeBytes_preserves_regs dstBits.toNat dataBits
      (coreStoreNextState (tryStepCoreStoreAfterIncrement s) (BitVec.ofNat 64 pcAddr)) sw hRunW]
    simp only [coreStoreNextState, tryStepCoreStoreAfterIncrement, sdStoreRegsAfter]
    rw [hRegs0]
  -- Architectural postcondition (code image): the persistent `matchesMemory` survives.  The store
  -- window is disjoint from the image, so every image-backed address reads its unchanged frame
  -- value; the final state's `.mem` is `sw.mem` (retirement only inserts registers).
  have hMatchesFinal : ∃ image, Artifact.programImage = .ok image ∧
      image.matchesMemory (tryStepCoreStoreAfterRetired sw (BitVec.ofNat 64 pcAddr) retired).mem := by
    refine ⟨image, imageEq, ?_⟩
    intro a byte hab
    -- `a` lies outside the owned destination window `[dst, dst+8)`: otherwise the image would back a
    -- destination byte, contradicting `imgDstNone`.
    have hout : a < dstBits.toNat ∨ dstBits.toNat + 8 ≤ a := by
      rcases Nat.lt_or_ge a dstBits.toNat with hlt | hge
      · exact Or.inl hlt
      · rcases Nat.lt_or_ge a (dstBits.toNat + 8) with hlt8 | hge8
        · exfalso
          have hnone : image.readByte? a = none := by
            have hk := imgDstNone (a - dstBits.toNat) (by omega)
            rwa [show dstBits.toNat + (a - dstBits.toNat) = a from by omega] at hk
          rw [hnone] at hab
          exact Option.noConfusion hab
        · exact Or.inr hge8
    have hpNone : hp a = none :=
      bytes_none_outside dstBits.toNat vs₀ hp hP a (by rw [hlen]; exact hout)
    have hp'None : hp' a = none :=
      bytes_none_outside dstBits.toNat (leBytes 8 dataBits) hp' hwordLE a
        (by rw [leBytes_length]; exact hout)
    have hframe : sw.mem.get? a = s.mem.get? a := by
      have hst : stateHeap sw a = stateHeap s a := by
        rw [hsplitW, hsplit, union_apply_of_none hp'None, union_apply_of_none hpNone]
      exact hst
    change sw.mem.get? a = some (BitVec.ofNat 8 byte.toNat)
    rw [hframe]
    exact loaded a byte hab
  -- Assemble the framed triple's existential witness.  The owned post-heap is exactly the
  -- little-endian word; the code image lives in the preserved frame.
  exact ⟨tryStepCoreStoreAfterRetired sw (BitVec.ofNat 64 pcAddr) retired, false, hp', hrun,
    ⟨hRegsAfter, hMatchesFinal⟩, hwordLE, hdisj', hsplitW⟩

end BinaryFv.Keccak
