import ZesuExec.Fn.Sha256.Svc

/-!
# `zkvm_sha256`: facts shared by the loop and the tail

The input as numbers and bytes, `Mid` across a service step that writes inside the frame, and
rodata after the prologue.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Fn

/-- A nonempty input: its bytes, its range, and its distance from the frame, the bump words and
the staging word. -/
structure InNums (m0 : Machine) : Prop where
  rd : readBytes m0.mem (m0.reg 10).toNat (m0.reg 11).toNat = some (msgOf m0)
  len : (msgOf m0).length = (m0.reg 11).toNat
  lo : 0x40000000 ≤ (m0.reg 10).toNat
  hi : (m0.reg 10).toNat + (m0.reg 11).toNat ≤ 0xc0000000
  inR : readable (m0.reg 10).toNat (m0.reg 11).toNat = true
  df : (m0.reg 10).toNat + (m0.reg 11).toNat ≤ (spM m0).toNat ∨
    (spM m0).toNat + 0xe0 ≤ (m0.reg 10).toNat
  db : (m0.reg 10).toNat + (m0.reg 11).toNat ≤ 0xa05340b8 ∨ 0xa05340c8 ≤ (m0.reg 10).toNat
  ds : (m0.reg 10).toNat + (m0.reg 11).toNat ≤ 0xa0000f00 ∨ 0xa0000f08 ≤ (m0.reg 10).toNat

theorem inNums {m0 : Machine} (h : Pre m0) (h0 : (m0.reg 11).toNat ≠ 0) : InNums m0 := by
  obtain ⟨-, -, -, hin, -, -, -, -, hdis⟩ := h
  have hin := hin.resolve_left h0
  have hdis := hdis.resolve_left h0
  simp only [srcOk, Bool.and_eq_true] at hin
  obtain ⟨hr, hp⟩ := hin
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hp
  have hmsg : msgOf m0 = bs := by simp [msgOf, hbs]
  have hfr0 : frameR m0 = (spM m0, 0xe0) := rfl
  rw [hfr0] at hdis
  simp only [Disjoint, inR, bumpR, stageR, BitVec.toNat_ofNat, bump, Layout.extraParams] at hdis
  obtain ⟨hdf, hdb, hds⟩ := hdis
  have hr' := hr
  simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Layout.rodataLo, Layout.rodataHi, Layout.inputLo, Layout.inputHi, Layout.ramLo,
    Layout.ramHi] at hr'
  refine ⟨by rw [hmsg]; exact hbs, by rw [hmsg]; exact readBytes_length hbs, by omega, by omega, hr,
    hdf, by omega, by omega⟩

/-- The input bytes, after the prologue. -/
theorem input_at {m0 m : Machine} (hn : Nums m0) (hi : InNums m0) (hmid : Mid m0 m) :
    ∀ t (ht : t < (msgOf m0).length),
      m.mem (BitVec.ofNat 64 ((m0.reg 10).toNat + t)) = some (msgOf m0)[t] := by
  intro t ht
  have hlt := hi.len ▸ ht
  have := hn.fb; have := hn.fs; have := hi.df; have := hi.db; have := hi.ds; have := hi.hi
  rw [hmid.same _ (by
    simp only [WrittenMid, InRange, bumpW, stageW, BitVec.toNat_ofNat, frameSize, bump,
      Layout.extraParams]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega)]
  exact readBytes_get hi.rd t ht

/-- Rodata after the prologue is the entry's. -/
theorem ro_mid {m0 m : Machine} (hpre : Pre m0) (hn : Nums m0) (hmid : Mid m0 m) :
    RodataLoaded zesuImage m := by
  intro a b hb
  have hr := zesu_rodata_range hb
  unfold Layout.rodataLo Layout.rodataHi at hr
  have := hn.lo
  rw [hmid.same _ (by
    simp only [WrittenMid, InRange, bumpW, stageW, BitVec.toNat_ofNat, frameSize, bump,
      Layout.extraParams]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega)]
  exact hpre.1 a b hb

/-- `Mid` across a step that keeps the registers and writes only frame offsets `[lo, lo + len)`
below `0x78`, leaving them present. -/
theorem mid_frame {m0 m m' : Machine} (hn : Nums m0) (hmid : Mid m0 m)
    (hreg : ∀ i, m'.reg i = m.reg i) {lo len : Nat} (hlo : lo + len ≤ 0x78)
    (hout : ∀ x : Word, ¬ ((spM m0).toNat + lo ≤ x.toNat ∧ x.toNat < (spM m0).toNat + lo + len) →
      m'.mem x = m.mem x)
    (hin : ∀ j < len, (m'.mem (spM m0 + BitVec.ofNat 64 (lo + j))).isSome) : Mid m0 m' := by
  have hsp : m'.reg 2 = spM m0 := by rw [hreg, hmid.sp]
  have hfa := fun j (hj : j < 0xe0) => frame_addr hn hj
  have := hn.hi; have := hn.fb; have := hn.fs
  refine ⟨hsp, by rw [hreg, hmid.out], fun p hp => by rw [hreg, hmid.saved p hp], ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [WrittenMid, InRange, frameSize, not_or, not_and, Nat.not_lt] at hx
    rw [hout x (by omega), hmid.same x (by
      simp only [WrittenMid, InRange, frameSize, not_or, not_and, Nat.not_lt]; exact hx)]
  · intro j hj
    rw [hsp]
    unfold frameSize at hj
    by_cases hc : lo ≤ j ∧ j < lo + len
    · have := hin (j - lo) (by omega)
      rwa [show lo + (j - lo) = j by omega] at this
    · rw [hout _ (by rw [hfa j hj]; omega), ← hmid.sp]; exact hmid.frame j (by unfold frameSize; omega)
  · intro p hp i hi
    have hoff := savedRegs_off p hp
    have hi8 : i < 8 := by rw [le8_length] at hi; exact hi
    rw [hsp, hout _ (by rw [hfa _ (by omega)]; omega), ← hmid.sp]
    exact hmid.savedMem p hp i hi
  · intro i hi
    have hi16 : i < 16 := by simpa [bumpBytes] using hi
    have hx : (bumpW + BitVec.ofNat 64 i).toNat = 0xa05340b8 + i := by
      rw [BitVec.toNat_add]; simp [bumpW, bump]; omega
    rw [hout _ (by rw [hx]; omega)]; exact hmid.bump i hi
  · intro j hj
    have hx : (stageW + BitVec.ofNat 64 j).toNat = 0xa0000f00 + j := by
      rw [BitVec.toNat_add]; simp [stageW, Layout.extraParams]; omega
    rw [hout _ (by rw [hx]; omega)]; exact hmid.stage j hj

/-- Frame bytes outside a service's writes keep their values. -/
theorem frameAt_out {m0 m m' : Machine} (hn : Nums m0) (hsp : m.reg 2 = spM m0)
    (hsp' : m'.reg 2 = spM m0) {lo len : Nat}
    (hout : ∀ x : Word, ¬ ((spM m0).toNat + lo ≤ x.toNat ∧ x.toNat < (spM m0).toNat + lo + len) →
      m'.mem x = m.mem x)
    {off : Nat} {L : List Byte} (hfr : FrameAt m off L) (hfit : off + L.length ≤ 0xe0)
    (hdis : off + L.length ≤ lo ∨ lo + len ≤ off) : FrameAt m' off L := by
  intro t ht
  rw [hsp', hout _ (by rw [frame_addr hn (by omega)]; omega), ← hsp]
  exact hfr t ht

/-! ## Service writes into the frame -/

theorem frame_ofNat (m0 : Machine) (j : Nat) :
    BitVec.ofNat 64 ((spM m0).toNat + j) = spM m0 + BitVec.ofNat 64 j := by
  rw [← ofNat_toNat_add]

theorem copy_out {mem : Word → Option Byte} {d s n : Nat} {x : Word}
    (h : ¬ (d ≤ x.toNat ∧ x.toNat < d + n)) : copyMem mem d s n x = mem x := by
  simp only [copyMem]; rw [if_neg (by omega)]

theorem copy_in {mem : Word → Option Byte} {d s n : Nat} {t : Nat} (ht : t < n) (hds : d ≠ s)
    (hd : d + n ≤ 2 ^ 64) :
    copyMem mem d s n (BitVec.ofNat 64 (d + t)) = mem (BitVec.ofNat 64 (s + t)) := by
  simp only [copyMem]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), if_pos (by omega)]
  congr 2; omega

theorem put_out {mem : Word → Option Byte} {d n : Nat} {bs : List Byte} {x : Word}
    (h : ¬ (d ≤ x.toNat ∧ x.toNat < d + n)) : putBytes mem d n bs x = mem x := by
  simp only [putBytes]; rw [if_neg h]

theorem put_in {mem : Word → Option Byte} {d n : Nat} {bs : List Byte} {t : Nat} (ht : t < n)
    (hl : bs.length = n) (hd : d + n ≤ 2 ^ 64) :
    putBytes mem d n bs (BitVec.ofNat 64 (d + t)) = some bs[t] := by
  simp only [putBytes]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), if_pos (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < bs.length by omega)]

theorem fill_out {mem : Word → Option Byte} {d n : Nat} {b : Byte} {x : Word}
    (h : ¬ (d ≤ x.toNat ∧ x.toNat < d + n)) : fillMem mem d n b x = mem x := by
  simp only [fillMem]; rw [if_neg h]

theorem fill_in {mem : Word → Option Byte} {d n : Nat} {b : Byte} {t : Nat} (ht : t < n)
    (hd : d + n ≤ 2 ^ 64) : fillMem mem d n b (BitVec.ofNat 64 (d + t)) = some b := by
  simp only [fillMem]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), if_pos (by omega)]

/-- Frame offset `lo` as an address. -/
theorem frame_toNat {m0 : Machine} (hn : Nums m0) {lo : Nat} (hlo : lo < 0xe0) :
    (spM m0 + BitVec.ofNat 64 lo).toNat = (spM m0).toNat + lo := frame_addr hn hlo

/-- `FrameAt` from bytes at the frame's numeric addresses. -/
theorem frameAt_of {m0 m : Machine} (hsp : m.reg 2 = spM m0) {off : Nat}
    {L : List Byte}
    (h : ∀ t (ht : t < L.length), m.mem (BitVec.ofNat 64 ((spM m0).toNat + off + t)) = some L[t]) :
    FrameAt m off L := by
  intro t ht
  rw [hsp, ← frame_ofNat, ← Nat.add_assoc]; exact h t ht

/-- A CSR `0x805` step with the parameter block at frame offset `P`, the state at frame offset
`8` and the block at `blkA`. -/
theorem compress_step {m0 m : Machine} {w0 : Nat} {P : Nat} {H : List Sha256.W32} {blkA : Word}
    {blk : List Byte} (hn : Nums m0) (hmid : Mid m0 m)
    (hmc : m.pc.toNat ≠ Layout.memcpyEntry) (hf : fetchI zesuImage m.pc.toNat = none)
    (h0 : Svc.fetch zesuImage m.pc.toNat = some w0)
    (hw : Svc.isCsrs w0 0x813 = false ∧ Svc.isCsrs w0 0x816 = false ∧ Svc.isCsrsi816 w0 = false ∧
      Svc.isCsrs w0 0x805 = true)
    (hp : m.reg (Decode.reg w0 15) = spM m0 + BitVec.ofNat 64 P) (hP : P % 8 = 0) (hP' : P + 16 ≤ 0x78)
    (hP8 : 40 ≤ P)
    (hpb : FrameAt m P (le8 (spM m0 + 8))) (hib : FrameAt m (P + 8) (le8 blkA))
    (hH : H.length = 8) (hst : FrameAt m 8 (Sha256.leBytes H))
    (hb8 : blkA.toNat % 8 = 0) (hbs : srcOk m.mem blkA.toNat 64 = true)
    (hblk : readBytes m.mem blkA.toNat 64 = some blk) :
    ∃ m', next zesuImage m = some (m', 1) ∧ m'.pc = m.pc + 4 ∧ Mid m0 m' ∧ (∀ r, m'.reg r = m.reg r) ∧
      FrameAt m' 8 (Sha256.leBytes (Sha256.sha256Compress H blk)) ∧
      (∀ x : Word, ¬ ((spM m0).toNat + 8 ≤ x.toNat ∧ x.toNat < (spM m0).toNat + 8 + 32) →
        m'.mem x = m.mem x) := by
  have := hn.hi; have := hn.lo; have := hn.al
  have hsp := hmid.sp
  have hS8 : (spM m0 + 8).toNat = (spM m0).toNat + 8 := frame_addr hn (j := 8) (by decide)
  have hpn : (m.reg (Decode.reg w0 15)).toNat = (spM m0).toNat + P := by
    rw [hp]; exact frame_addr hn (by omega)
  have hrd : ∀ {off : Nat} {L : List Byte}, FrameAt m off L →
      readBytes m.mem ((spM m0).toNat + off) L.length = some L := fun h => by
    rw [← hsp]; exact readBytes_frame h
  have hlb := Sha256.leBytes_length hH
  have e1 := hrd hpb; rw [le8_length] at e1
  have e2 := hrd hib; rw [le8_length, ← Nat.add_assoc] at e2
  have e3 := hrd hst; rw [hlb] at e3
  have hfrp : ∀ j < 0xe0, (m.mem (BitVec.ofNat 64 ((spM m0).toNat + j))).isSome := fun j hj => by
    rw [frame_ofNat, ← hsp]; exact hmid.frame j (by unfold frameSize; omega)
  have hn1 := next_805 (m := m) (w0 := w0) (p := (spM m0).toNat + P) (st := (spM m0).toNat + 8)
    (inp := blkA.toNat) hmc hf h0 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 hpn (by omega)
    (by
      simp only [srcOk, Bool.and_eq_true]
      refine ⟨by simp [readable, inRange, Layout.ramLo, Layout.ramHi]; omega, ?_⟩
      exact readBytes_isSome_of fun t ht => by rw [Nat.add_assoc]; exact hfrp _ (by omega))
    e1 e2 (by rw [ofBytesLE_le8, hS8]) (by rw [ofBytesLE_le8]) (by omega) hb8
    (by
      simp only [dstOk, Bool.and_eq_true]
      refine ⟨by simp [writable, inRange, Layout.ramLo, Layout.ramHi]; omega, ?_⟩
      exact readBytes_isSome_of fun t ht => by rw [Nat.add_assoc]; exact hfrp _ (by omega))
    hbs e3 hblk
  rw [Sha256.leWords_leBytes H hH] at hn1
  refine ⟨_, hn1, rfl, ?_, fun r => rfl, ?_, fun x hx => put_out hx⟩
  · refine mid_frame hn hmid (fun r => rfl) (lo := 8) (len := 32) (by decide)
      (fun x hx => put_out hx) ?_
    intro j hj
    show (putBytes _ _ _ _ _).isSome = true
    rw [← frame_ofNat, ← Nat.add_assoc, put_in hj (Sha256.leBytes_length (Sha256.compress_length _ _))
      (by omega)]
    rfl
  · intro t ht
    have ht' : t < 32 := by rw [Sha256.leBytes_length (Sha256.compress_length _ _)] at ht; exact ht
    show putBytes m.mem _ 32 _ (m.reg 2 + BitVec.ofNat 64 (8 + t)) = _
    rw [hsp, ← frame_ofNat, ← Nat.add_assoc]
    exact put_in ht' (Sha256.leBytes_length (Sha256.compress_length _ _)) (by omega)

end ZesuExec.Fn.Sha256
