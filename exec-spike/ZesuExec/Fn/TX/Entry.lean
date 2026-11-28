import ZesuExec.Fn.TX.Outer

/-!
# TX: error exits inside one entry (programme plan S6 step 6)

An entry is a list `{eh, el}` at the cursor; a rejection of its address (`0x8000010c`) or of its
keys list (`0x8000015c`) makes `entryWalk` of its payload `none`, hence the walk of the window
(`entries_none_entry`) and `outer_err`.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- The payload length word (bytes `8..15`) of a successful outcome. -/
theorem dec_len {p : Word} {input before : List Byte} {b : Bool} {hh q : Nat}
    (hd : F2.decode input = .success b hh q) :
    ofBytesLE (((F2.result40 p input before).drop 8).take 8) = BitVec.ofNat 64 q := by
  show ofBytesLE [F2.resultByte p input before 8, F2.resultByte p input before 9,
    F2.resultByte p input before 10, F2.resultByte p input before 11,
    F2.resultByte p input before 12, F2.resultByte p input before 13,
    F2.resultByte p input before 14, F2.resultByte p input before 15] = _
  simp only [F2.resultByte, hd, F2.successByte]
  exact ofBytesLE_bytes8 _

/-- The walk of a window whose first item is an entry list with a rejected payload rejects. -/
theorem entries_none_entry {win : List Byte} (hne : win ≠ []) {eh el : Nat}
    (hd : F2.decode win = .success true eh el)
    (h : (entryWalk (itemPayload win eh el)).2 = none) :
    (entriesWalk win.length win).2 = none := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.length_cons, entriesWalk, hd, h]

/-- An entry whose first item is not a 20-byte string rejects. -/
theorem entry_none_addr {e : List Byte} (h : ∀ ah, F2.decode e ≠ .success false ah 20) :
    (entryWalk e).2 = none := by
  unfold entryWalk
  split
  · rename_i ah al hd
    split
    · rename_i h20; subst h20; exact absurd hd (h ah)
    · rfl
  · rfl

/-- The entry payload in input coordinates. -/
theorem ent_eq (σ : Sig) (o : Obs) (k : Kobs) (hk : k.eh + k.el ≤ o.p - o.i) :
    ent σ o k = (σ.input.drop (o.h + o.i + k.eh)).take k.el := by
  simp only [ent, itemPayload, win_eq, List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by omega), Nat.add_comm (o.h + o.i)]

/-! ## `0x8000010c`: after the address's `decodeItem` -/

theorem ret10c {σ : Sig} {m : Machine} (h : ARet f2C (unit Site108) σ m) :
    Common σ m ∧ ∃ o k L, EntryState σ m o k L ∧ ∃ before : List Byte,
      BytesAt m (σ.sl 0x180) (F2.result40 (entPtr σ o k) (ent σ o k) before) := by
  have hcm := A10c_common h
  obtain ⟨mc, _, ⟨o, k, L, ⟨hs, hd, hle, r26⟩, -, -, ha⟩, hpost, hp⟩ := h
  have hc := hs.1
  have hout : mc.reg 10 = σ.sl 0x180 := ha.arg 0 (by simp)
  have hin : mc.reg 11 = entPtr σ o k := ha.arg 1 (by simp)
  have hlen : mc.reg 12 = w k.el := ha.arg 2 (by simp)
  have hok := hs.2.1
  have hi := hs.2.2.1.2.2.1
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hpl := hok.2.1
  have hl : (mc.reg 12).toNat = k.el := by
    rw [hlen]; simp only [w, BitVec.toNat_ofNat]; omega
  obtain ⟨before, -, hb⟩ := f2_result hc hout (by decide) (by decide) (off := o.h + o.i + k.eh)
    (by rw [hin]; simp only [entPtr, curPtr, w]; bv_omega) (by omega) hpost
  rw [hl, ← ent_eq σ o k hle,
    show σ.inp + w (o.h + o.i + k.eh) = entPtr σ o k by simp only [entPtr, curPtr, w]; bv_omega] at hb
  exact ⟨hcm, o, k, L, ⟨outer_keep hs hcm hout (by decide) (by decide) hpost hp,
    hd, hle, (hpost.1.2 26 (by decide)).trans r26⟩, before, hb⟩

/-- The `CutOK` facts of `0x8000010c`'s state under `envP`. -/
theorem envP_ok {σ : Sig} {m : Machine} (hc : Common σ m) {k : Nat} (hk : 8 ≤ k)
    (hk' : k ≤ frameBytes) :
    BaseEnv σ m (envP k σ m) ∧
      Env.WF (envP k σ m) (entryState ovBody baseRegions [vtableKnown, payloadKnown k]) :=
  ⟨BaseEnv.ofP k σ m, (payload_ok hc hk hk').1⟩

/-- An address rejection at `0x8000010c`. -/
theorem addr_err {σ : Sig} {m : Machine} {o : Obs} {k : Kobs} {L : List (Word × Nat)}
    (hcm : Common σ m) (hs : EntryState σ m o k L)
    (hrej : ∀ ah, F2.decode (ent σ o k) ≠ .success false ah 20) : ErrOk σ m :=
  outer_err hcm hs.1.2.1 hs.1.2.2.2.2.2 (entries_none_entry (win_ne hs.1.2.1 hs.1.2.2.1.2.2.1 hcm.2.1)
    hs.2.1 (entry_none_addr hrej))

theorem TX.leaf_8000010c_0 :
    LeafGoal TX.plan TX.plan.cuts[4]! ((TX.plan.leaves 0x8000010c)[0]!) := by
  show LeafGoal TX.plan cut10c (run10c_leaves[0]!)
  have hcs : (run10c_leaves[0]!).conds = [SBool.ne (Sym.init 0 224 2) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envP_ok (A10c_common hA) (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_)
    (fun σ m hA hc => ?_)
  · budget_auto
  obtain ⟨hcm, o, k, L, hs, before, hb⟩ := ret10c hA
  have h1 : SBool.eval (envP 0x180 σ m) (SBool.ne (Sym.init 0 224 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  simp only [SBool.eval] at h1
  rw [show (224 : Nat) = frameBytes - 0x180 + 32 from rfl,
    slot_val (BaseEnv.ofP 0x180 σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h1
  have hdec := dec_err (by simpa [Sym.eval] using h1)
  exact addr_err hcm hs fun ah h => by rw [hdec] at h; cases h

theorem TX.leaf_8000010c_1 :
    LeafGoal TX.plan TX.plan.cuts[4]! ((TX.plan.leaves 0x8000010c)[1]!) := by
  show LeafGoal TX.plan cut10c (run10c_leaves[1]!)
  have hcs : (run10c_leaves[1]!).conds = [SBool.eq (Sym.init 0 224 2) (Sym.lit 0),
      SBool.ne (Sym.bin BinOp.and (Sym.init 0 208 1) (Sym.lit 1)) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envP_ok (A10c_common hA) (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_)
    (fun σ m hA hc => ?_)
  · budget_auto
  obtain ⟨hcm, o, k, L, hs, before, hb⟩ := ret10c hA
  have h1 : SBool.eval (envP 0x180 σ m) (SBool.eq (Sym.init 0 224 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envP 0x180 σ m)
      (SBool.ne (Sym.bin BinOp.and (Sym.init 0 208 1) (Sym.lit 1)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  simp only [SBool.eval] at h1 h2
  replace h2 : ((Sym.init 0 208 1).eval (envP 0x180 σ m) &&& 1#64 != 0#64) = true := h2
  rw [show (224 : Nat) = frameBytes - 0x180 + 32 from rfl,
    slot_val (BaseEnv.ofP 0x180 σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h1
  rw [show (208 : Nat) = frameBytes - 0x180 + 16 from rfl,
    slot_val (BaseEnv.ofP 0x180 σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h2
  obtain ⟨b, hh, q, hd, hl⟩ := dec_ok (by simpa [Sym.eval] using h1)
  rw [hl] at h2
  cases b
  · simp at h2
  · exact addr_err hcm hs fun ah h => by rw [hd] at h; cases h

theorem TX.leaf_8000010c_2 :
    LeafGoal TX.plan TX.plan.cuts[4]! ((TX.plan.leaves 0x8000010c)[2]!) := by
  show LeafGoal TX.plan cut10c (run10c_leaves[2]!)
  have hcs : (run10c_leaves[2]!).conds = [SBool.eq (Sym.init 0 224 2) (Sym.lit 0),
      SBool.eq (Sym.bin BinOp.and (Sym.init 0 208 1) (Sym.lit 1)) (Sym.lit 0),
      SBool.ne (Sym.init 0 200 8) (Sym.var 24)] := by decide
  refine err_leaf rfl (fun σ m hA => envP_ok (A10c_common hA) (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_)
    (fun σ m hA hc => ?_)
  · budget_auto
  obtain ⟨hcm, o, k, L, hs, before, hb⟩ := ret10c hA
  have h1 : SBool.eval (envP 0x180 σ m) (SBool.eq (Sym.init 0 224 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h3 : SBool.eval (envP 0x180 σ m) (SBool.ne (Sym.init 0 200 8) (Sym.var 24)) = true :=
    hc _ (by rw [hcs]; simp)
  simp only [SBool.eval] at h1 h3
  rw [show (224 : Nat) = frameBytes - 0x180 + 32 from rfl,
    slot_val (BaseEnv.ofP 0x180 σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h1
  rw [show (200 : Nat) = frameBytes - 0x180 + 8 from rfl,
    slot_val (BaseEnv.ofP 0x180 σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h3
  have r24 : (Sym.var 24).eval (envP 0x180 σ m) = 20 := by
    simp only [Sym.eval, envP, Env.setVars, envB, entryEnv]
    simpa using hs.1.2.2.2.1.1
  rw [r24] at h3
  refine addr_err hcm hs fun ah h => ?_
  rw [dec_len h] at h3
  simp at h3

end ZesuExec.Fn.TX
