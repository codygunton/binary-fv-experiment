import ZesuExec.Fn.Sha256.Pad

/-!
# `zkvm_sha256`: the output (`0x800ea394` → return)

One symbolic piece in shape `shapeO` (the frame at `sp`, `out` at `a2`): the eight state words
loaded (`lw`), byte-reversed (`rev8`) and stored big-endian to `out`, `a0 = 0`, the saved
registers reloaded, the frame popped, `ret`. `out_post` turns `OAt` into `Post`.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Fn

def envO (m : Machine) : Env := entryEnv m ((shapeO m).map (·.1))

/-- `out` is present RAM after the prologue. -/
theorem out_present {m0 m : Machine} (hpre : Pre m0) (hn : Nums m0) (hmid : Mid m0 m) :
    ∀ j < 32, (m.mem (m0.reg 12 + BitVec.ofNat 64 j)).isSome := by
  intro j hj
  have hout := hpre.2.2.2.2.1
  simp only [dstOk, Bool.and_eq_true] at hout
  have := hn.fo; have := hn.ob; have := hn.os; have := hn.ohi
  have hx : (m0.reg 12 + BitVec.ofNat 64 j).toNat = (m0.reg 12).toNat + j := by
    rw [BitVec.toNat_add]; simp; omega
  rw [hmid.same _ (by
    simp only [WrittenMid, InRange, bumpW, stageW, BitVec.toNat_ofNat, frameSize, bump,
      Layout.extraParams, hx]
    omega)]
  have := present_at hout.2 j hj
  rwa [ofNat_toNat_add] at this

/-- A symbolic piece in shape `shapeO` from a machine satisfying `Mid`. -/
theorem segO {cuts : List Nat} {fuel pc : Nat} {ls : List Leaf}
    (h : run zesuImage cuts fuel pc SO = some ls) {m0 m : Machine} (hpre : Pre m0)
    (hmid : Mid m0 m) (hro : RodataLoaded zesuImage m) (hpc : m.pc.toNat = pc) :
    ∃ l ∈ ls, (∀ c ∈ l.conds, c.eval (envO m) = true) ∧
      ((∀ o ∈ l.obligs, o.holds (envO m)) →
        ∃ m', RunsIn zesuImage l.S.steps m m' ∧ Match (envO m) l.S m' ∧
          ExitOk (envO m) l.exit m' ∧
          SameOutside (fun a => InRange (m.reg 2) 0xe0 a ∨ InRange (m.reg 12) 32 a) m m') := by
  have hn := nums hpre
  have := hn.lo; have := hn.hi; have := hn.al; have := hn.fo; have := hn.olo; have := hn.ohi
  have hsp := hmid.sp
  have h12 := hmid.out
  obtain ⟨l, hl, hc, hr⟩ := seg_sound (ov := ovO) (shape := shapeO m) h
    (by
      simp only [shapeO, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
        RegionOk, frameRg, outRg]
      refine ⟨⟨fun s hs => by cases hs; rfl, by rw [hsp]; omega, ?_⟩,
        ⟨fun s hs => by cases hs; rfl, Nat.mod_one _, ?_⟩⟩
      · simp only [if_true, writable, inRange, Bool.and_eq_true, decide_eq_true_eq, hsp,
          Layout.ramLo, Layout.ramHi]
        omega
      · simp only [if_true, writable, inRange, Bool.and_eq_true, decide_eq_true_eq, h12,
          Layout.ramLo, Layout.ramHi]
        omega)
    (by
      show [(m.reg 2, 0xe0), (m.reg 12, 32)].Pairwise Disjoint
      refine List.Pairwise.cons (fun b hb => ?_) (List.Pairwise.cons (fun _ h => by simp at h) .nil)
      simp only [List.mem_singleton] at hb; subst hb
      unfold Disjoint; dsimp only; rw [hsp, h12]; omega)
    (fun r j hr hj => by
      simp [shapeO] at hr
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · exact hmid.frame j (by simpa [entryEnv, Env.size, shapeO, frameSize] using hj)
      · have := out_present hpre hn hmid j (by simpa [entryEnv, Env.size, shapeO] using hj)
        simpa [entryEnv, Env.base, shapeO, h12] using this)
    (fun i hi s hs => by
      simp only [ovO] at hs
      split at hs
      · next h2 =>
        cases hs
        have : i = 2 := Fin.ext h2
        subst this
        simp [Sym.eval, Env.base, entryEnv, shapeO]
      · split at hs
        · next h2 =>
          cases hs
          have : i = 12 := Fin.ext h2
          subst this
          simp [Sym.eval, Env.base, entryEnv, shapeO]
        · simp at hs)
    hpc hro
  refine ⟨l, hl, hc, fun ho => ?_⟩
  obtain ⟨m', h1, h2, h3, h4⟩ := hr ho
  refine ⟨m', h1, h2, h3, SameOutside.mono h4 fun a ha => ?_⟩
  obtain ⟨p, hp, -, hin⟩ := inWritable_entry ha (by
    simp only [shapeO, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    rw [hsp, h12]; omega)
  simp only [shapeO, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact Or.inl hin
  · exact Or.inr hin

sym_run runO := run zesuImage [] 200 0x800ea394 SO

/-- `ra` as the return reads it. -/
def raSym : Sym := .bin .and (.init 0 216 8) (.lit 18446744073709551614)

/-- Byte `t` of `out` as the piece stores it: word `t / 4` of the state, byte-reversed. -/
def outSym (t : Nat) : Sym :=
  .bin .srl (.bin .rev8 (.sext 32 (.init 0 (8 + 4 * (t / 4)) 4)) (.lit 0)) (.lit (32 + 8 * (t % 4)))

theorem o_facts : runO_leaves = [runO_leaves[0]!] ∧ (runO_leaves[0]!).S.steps = 96 ∧
    (runO_leaves[0]!).obligs = [.aligned raSym 4] ∧ (runO_leaves[0]!).exit = .ret raSym ∧
    (runO_leaves[0]!).S.regions.length = 2 ∧
    (runO_leaves[0]!).S.reg 2 = .ptr 0 224 ∧ (runO_leaves[0]!).S.reg 10 = .lit 0 ∧
    (∀ p ∈ savedRegs, (runO_leaves[0]!).S.reg p.1.val = .init 0 p.2 8) ∧
    (∀ t < 32, (runO_leaves[0]!).S.mem.find? (·.covers 1 t) = some ⟨1, t, 1, outSym t⟩) := by
  decide

theorem byteOf_sext32' (x : Word) {u : Nat} (hu : u < 4) :
    byteOf ((x.setWidth 32).signExtend 64) u = byteOf x u := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [byteOf, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth]
  have h1 : 8 * u + b < 32 := by omega
  simp [h1, show 8 * u + b < 64 by omega]

/-- The frame bytes as region 0 of `envO` reads them. -/
theorem byteList_frame {m : Machine} :
    ∀ {off : Nat} {L : List Byte}, FrameAt m off L →
      byteList ((envO m).byte0 0) off L.length = L
  | _, [], _ => rfl
  | off, b :: L, h => by
    have h0 := h 0 (by simp)
    have hr : byteList ((envO m).byte0 0) (off + 1) L.length = L := byteList_frame fun t ht => by
      have := h (t + 1) (by simp; omega)
      rw [show off + (t + 1) = off + 1 + t by omega] at this
      simpa using this
    simp only [List.length_cons, byteList, hr]
    congr 1
    show (m.mem (m.reg 2 + BitVec.ofNat 64 off)).getD 0 = b
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0]; rfl

theorem init_frame {m : Machine} {off : Nat} {L : List Byte} (h : FrameAt m off L) :
    (Sym.init 0 off L.length).eval (envO m) = ofBytesLE L := by
  simp only [Sym.eval, byteList_frame h]

theorem beBytes_length {H : List Sha256.W32} (hH : H.length = 8) : (Sha256.beBytes H).length = 32 := by
  simp [Sha256.beBytes, List.length_flatMap, List.map_const', hH]

theorem le_be_get {H : List Sha256.W32} (hH : H.length = 8) (t : Nat) (ht : t < 32) :
    (Sha256.leBytes H)[4 * (t / 4) + (3 - t % 4)]'(by rw [Sha256.leBytes_length hH]; omega) =
      (Sha256.beBytes H)[t]'(by rw [beBytes_length hH]; exact ht) := by
  match H, hH with
  | [a, b, c, d, e, f, g, h], _ =>
    match t, ht with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
    | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _
    | 23, _ | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ => rfl
    | _ + 32, h => exact absurd h (by omega)

/-- Byte `t` the piece stores to `out` is byte `t` of the big-endian state. -/
theorem out_byte {m : Machine} {H : List Sha256.W32} (hH : H.length = 8)
    (hst : FrameAt m 8 (Sha256.leBytes H)) (t : Nat) (ht : t < 32) :
    byteOf ((outSym t).eval (envO m)) 0 =
      (Sha256.beBytes H)[t]'(by rw [beBytes_length hH]; exact ht) := by
  have hl := Sha256.leBytes_length hH
  have h4 : FrameAt m (8 + 4 * (t / 4)) (((Sha256.leBytes H).drop (4 * (t / 4))).take 4) := by
    intro u hu
    simp only [List.length_take, List.length_drop, hl] at hu
    rw [List.getElem_take, List.getElem_drop, show 8 + 4 * (t / 4) + u = 8 + (4 * (t / 4) + u) by
      omega]
    exact hst _ (by omega)
  have h4l : (((Sha256.leBytes H).drop (4 * (t / 4))).take 4).length = 4 := by
    simp [hl]; omega
  have hi := byteList_frame h4
  rw [h4l] at hi
  simp only [outSym, Sym.eval, BinOp.eval]
  rw [hi, show (BitVec.ofNat 64 (32 + 8 * (t % 4))).toNat % 64 = 8 * (4 + t % 4) by
    rw [BitVec.toNat_ofNat]; omega, byteOf_rev8_shift _ _ (by omega),
    show 7 - (4 + t % 4) = 3 - t % 4 by omega, byteOf_sext32' _ (by omega),
    byteOf_ofBytesLE _ (by rw [h4l]; decide) _ (by rw [h4l]; omega)]
  rw [List.getElem_take, List.getElem_drop]
  exact le_be_get hH t ht

theorem finish_length (msg : List Byte) (H : List Sha256.W32) : (Sha256.finish msg H).length = 8 := by
  unfold Sha256.finish; split <;> exact Sha256.compress_length _ _


theorem calleeSaved_saved : ∀ i ∈ calleeSaved, i = 2 ∨ ∃ p ∈ savedRegs, p.1 = i := by decide

/-- `0x800ea394` → return, and `Post`. -/
theorem out_post {m0 m : Machine} (hpre : Pre m0) (h : OAt m0 m) :
    ∃ m', RunsIn zesuImage 96 m m' ∧ Post m0 m' := by
  have hn := nums hpre
  have := hn.lo; have := hn.hi; have := hn.al; have := hn.fo; have := hn.fb; have := hn.ob
  have := hn.olo; have := hn.ohi; have := hn.fs; have := hn.os
  have hlen := msg_len hpre
  obtain ⟨l, hl, -, hr⟩ := segO runO hpre h.mid (ro_mid hpre hn h.mid) h.pc
  obtain ⟨hls, hsteps, hob, hex, hrl, hr2, hr10, hrs, hout⟩ := o_facts
  rw [hls, List.mem_singleton] at hl; subst hl
  have hsv : ∀ p ∈ savedRegs, (Sym.init 0 p.2 8).eval (envO m) = m0.reg p.1 := fun p hp => by
    have := init_frame (h.mid.savedMem p hp)
    rwa [le8_length, ofBytesLE_le8] at this
  have hra : raSym.eval (envO m) = m0.reg 1 &&& ~~~(1 : Word) := by
    show (Sym.init 0 216 8).eval (envO m) &&& BitVec.ofNat 64 18446744073709551614 = _
    rw [hsv (1, 0xd8) (by decide)]; rfl
  obtain ⟨m', hrun, hm', hex', hso⟩ := hr (fun o ho => by
    rw [hob, List.mem_singleton] at ho; subst ho
    show (raSym.eval (envO m)).toNat % 4 = 0
    rw [hra]; exact hpre.2.2.1)
  rw [hsteps] at hrun
  have hsp : m.reg 2 = spM m0 := h.mid.sp
  -- memory outside the frame and `out`
  have hkeep : ∀ a : Word, ¬ InRange (spM m0) 0xe0 a → ¬ InRange (m0.reg 12) 32 a →
      m'.mem a = m.mem a := fun a h1 h2 => hso a (by
    rw [hsp, h.mid.out]; rintro (h | h) <;> contradiction)
  have hH := finish_length (msgOf m0) (Sha256.foldBlocks (msgOf m0) ((m0.reg 11).toNat / 64))
  refine ⟨m', hrun, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hex] at hex'; exact hex'.trans hra
  · intro i hi
    rcases calleeSaved_saved i hi with rfl | ⟨p, hp, rfl⟩
    · rw [reg_of_match hm', show ((2 : Fin 32).val) = 2 from rfl, hr2]
      show m.reg 2 + BitVec.ofInt 64 224 = _
      rw [hsp]; exact BitVec.sub_add_cancel _ _
    · rw [reg_of_match hm', hrs p hp, hsv p hp]
  · rw [reg_of_match hm', show ((10 : Fin 32).val) = 10 from rfl, hr10]; rfl
  · rw [Sha256.hash_eq, hlen]
    intro i hi
    have hi32 : i < 32 := by rw [beBytes_length hH] at hi; exact hi
    have := mem_of_find hm' (r := 1) (j := i) (by rw [hrl]; decide)
      (by show i < 32; exact hi32) (hout i hi32)
    rw [show (envO m).base 1 = m.reg 12 from rfl, h.mid.out, Nat.sub_self] at this
    rw [this, out_byte hH h.st i hi32]
  · intro i hi
    have hi16 : i < 16 := by simpa [bumpBytes] using hi
    have hx : (BitVec.ofNat 64 bump + BitVec.ofNat 64 i).toNat = 0xa05340b8 + i := by
      rw [BitVec.toNat_add]; simp [bump]; omega
    rw [hkeep _ (by unfold InRange; rw [hx]; omega) (by unfold InRange; rw [hx]; omega)]
    exact h.mid.bump i hi
  · intro a ha
    simp only [Written, InRange, not_or] at ha
    obtain ⟨h1, h2, h3, h4⟩ := ha
    rw [hkeep a h1 h2, h.mid.same a (by
      rintro (h | h | h)
      · exact h1 h
      · exact h3 h
      · exact h4 h)]

end ZesuExec.Fn.Sha256
