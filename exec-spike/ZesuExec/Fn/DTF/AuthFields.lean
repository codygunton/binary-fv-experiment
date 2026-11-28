import ZesuExec.Fn.DTF.AuthExit

/-!
# DTF: the tuple's fields (programme plan S7 step 4)

The front half of the `txAuthList` loop: `decodeItem` on the list cursor (`0x800024d0`), the tuple a
list (`0x800024ec`, `AuthTup 0 0`), then per field (chainId, address, nonce, yParity, r, s) the
return of its `decodeItem` on the field cursor `s6`/`s7`: the field passes `auth`'s check
(`tupLen`, `TupOk`; not a list, the leaf's bound); an empty field moves the cursor by the consumed
length and calls `decodeItem` on the next field; a nonempty one enters its byte loop (`CurOk` from
the outcome, the `nx` clause); the loop's exit moves the cursor by the consumed word at `S-0x78`
and calls `decodeItem` on the next field. Tools: the tuple state without the field cursor
(`TupC`), a field return site's state and outcome (`tup_ret`, `tup_field`), the cursor's advance
(`tup_adv`), a field's `decodeItem` call (`field_call`), a byte loop's entry (`loop_entry`,
`beL_budget`) and head (`tup_src`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

set_option maxRecDepth 20000

/-! ## The tuple state without the field cursor -/

/-- `AuthTup` without the field cursor and the `nx` clause. -/
def TupC (σ : Sig) (m : Machine) (c h p n j ht pt : Nat) : Prop :=
  AuthOut σ m n j c h p ∧ m.load (σ.fr + w 0x50) 8 = some (w n) ∧ AuthBuf σ m n 0 ∧
    F2.decode ((σ.payload.drop (c + h + j)).take (p - j)) = .success true ht pt ∧
    ht + pt ≤ p - j ∧ m.load (σ.fr + w 0x48) 8 = some (w (ht + pt))

theorem tup_of {σ : Sig} {m : Machine} {c h p n j ht pt b f q : Nat} {nx : Bool}
    (hc : TupC σ m c h p n j ht pt) (hbq : b ≤ q) (hfq : f ≤ q) (hqp : q ≤ pt)
    (r22 : m.reg 22 = σ.inp + w (c + h + j + ht + q)) (r23 : m.reg 23 = w (pt - q))
    (hsf : skip f (tupPay σ c h p j ht pt) = some q) (hok : TupOk (tupPay σ c h p j ht pt) f)
    (hnx : nx = true → TupOk (tupPay σ c h p j ht pt) (f + 1) ∧
      ∃ k, m.load (σ.fr + w 0x2f8) 8 = some (w k) ∧ 1 ≤ k ∧ q + k ≤ pt ∧
        skip (f + 1) (tupPay σ c h p j ht pt) = some (q + k)) :
    AuthTup σ m b f nx := by
  obtain ⟨ho, l50, hb, hd, hle, l48⟩ := hc
  exact ⟨c, h, p, n, j, ht, pt, q, ho, l50, hb, hd, hle, l48, hbq, hfq, hqp, r22, r23, hsf, hok,
    hnx⟩

theorem of_tup {σ : Sig} {m : Machine} {b f : Nat} {nx : Bool} (ht : AuthTup σ m b f nx) :
    ∃ c h p n j ht pt q, TupC σ m c h p n j ht pt ∧ b ≤ q ∧ f ≤ q ∧ q ≤ pt ∧
      m.reg 22 = σ.inp + w (c + h + j + ht + q) ∧ m.reg 23 = w (pt - q) ∧
      skip f (tupPay σ c h p j ht pt) = some q ∧ TupOk (tupPay σ c h p j ht pt) f ∧
      (nx = true → TupOk (tupPay σ c h p j ht pt) (f + 1) ∧
        ∃ k, m.load (σ.fr + w 0x2f8) 8 = some (w k) ∧ 1 ≤ k ∧ q + k ≤ pt ∧
          skip (f + 1) (tupPay σ c h p j ht pt) = some (q + k)) := by
  obtain ⟨c, h, p, n, j, ht, pt, q, ho, l50, hb, hd, hle, l48, hbq, hfq, hqp, r22, r23, hsf, hok,
    hnx⟩ := ht
  exact ⟨c, h, p, n, j, ht, pt, q, ⟨ho, l50, hb, hd, hle, l48⟩, hbq, hfq, hqp, r22, r23, hsf, hok,
    hnx⟩

/-- The frame words `TupC` names. -/
def tupSlots : List Nat := [0x70, 0x68, 0x30, 0x58, 0x60, 0x50, 0x48]

theorem tupC_mono {σ : Sig} {m m' : Machine} {c h p n j ht pt : Nat}
    (hk : ∀ o ∈ tupSlots, m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8)
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) (hc : TupC σ m c h p n j ht pt) :
    TupC σ m' c h p n j ht pt := by
  obtain ⟨ho, l50, hb, hd, hle, l48⟩ := hc
  refine ⟨authOut_mono (hk _ (by decide)) (hk _ (by decide)) (hk _ (by decide)) ho, ?_,
    authBuf_mono (hk _ (by decide)) (hk _ (by decide)) hL hb, hd, hle, ?_⟩
  · rw [hk _ (by decide)]; exact l50
  · rw [hk _ (by decide)]; exact l48

/-- The leaf keeps the frame words `os`. -/
def slotsKept (d : CutData) (l : Leaf) (os : List Nat) : Bool :=
  os.all fun o => (Loc.slot o).sym l.S == (Loc.slot o).sym d.shape.S

theorem kept_load {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {os : List Nat} (hk : slotsKept d l os = true) (hos : ∀ o ∈ os, o + 8 ≤ frameBytes) :
    ∀ o ∈ os, m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8 := by
  intro o ho
  unfold slotsKept at hk
  simp only [List.all_eq_true, beq_iff_eq] at hk
  exact ctx_load C (hos o ho) (hk o ho)

theorem tupC_keep {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (hk : slotsKept d l tupSlots = true) {c h p n j ht pt : Nat}
    (hc : TupC σ m c h p n j ht pt) : TupC σ m' c h p n j ht pt :=
  tupC_mono (kept_load C hk (by decide)) (fun _ _ hl => ctx_live C hl) hc

/-! ## The field return sites' `SiteX` -/

theorem siteX_tup0 {pc : Nat} (hpc : pc = 0x8000252c ∨ pc = 0x80002600) {σ : Sig} {x : Idx}
    {m : Machine} :
    SiteX pc σ x m ↔ AuthTup σ m 0 (tupF pc) false ∧ m.reg 11 = m.reg 22 ∧ m.reg 12 = m.reg 23 := by
  rcases hpc with rfl | rfl <;>
    simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true, or_true, or_false]

theorem siteX_tup21 {pc : Nat} (hpc : pc = 0x80002654 ∨ pc = 0x800026d4 ∨ pc = 0x80002754)
    {σ : Sig} {x : Idx} {m : Machine} :
    SiteX pc σ x m ↔ AuthTup σ m 21 (tupF pc) false ∧ AddrOk σ m ∧ m.reg 11 = m.reg 22 ∧
      m.reg 12 = m.reg 23 := by
  rcases hpc with rfl | rfl | rfl <;>
    simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true, or_true, or_false]

theorem siteX_end {σ : Sig} {x : Idx} {m : Machine} :
    SiteX 0x80002820 σ x m ↔ AuthEnd σ m 5 true := by
  simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true, or_false]

/-- After the tuple's fifth field, `decodeItem` on `s` at `q`: the tuple consumed `ht + pt ≥ 22`
bytes, its first five fields checked. -/
theorem end_of {σ : Sig} {m : Machine} (hpre : Pre σ.A σ.g σ.m) (h4 : σ.t = 4)
    {c h p n j ht pt q : Nat} (hc : TupC σ m c h p n j ht pt) (h22 : 22 ≤ ht + pt)
    (ha : AddrOk σ m) (h5 : 5 ≤ q) (hqp : q ≤ pt)
    (hs5 : skip 5 (tupPay σ c h p j ht pt) = some q) (hok : TupOk (tupPay σ c h p j ht pt) 5)
    (a11 : m.reg 11 = σ.inp + w (c + h + j + ht + q)) (a12 : m.reg 12 = w (pt - q)) :
    AuthEnd σ m 5 true := by
  obtain ⟨ho, l50, hb, hd, hle, l48⟩ := hc
  obtain ⟨hjp, hle', -⟩ := out_n hpre h4 ho
  have hlen := len_lt32 hpre
  refine ⟨c, h, p, n, j, ht, pt, q, ⟨ho, l50, hb, ?_, h22, l48, ha, hd, hle, h5, hqp, hs5, hok⟩,
    fun _ => ⟨a11, a12⟩⟩
  rw [skip_snoc ho.2.1 (by rw [itemPayload_drop]; exact hd), TX.itemConsumed,
    Nat.mod_eq_of_lt (by omega)]


/-! ## Evaluating the leaves' symbols -/

theorem eval_ptr30 (sh : Shape) (σ : Sig) (m : Machine) :
    (Sym.ptr 3 0).eval (envOf sh σ m) = σ.inp := by
  simp only [Sym.eval, env_base3]; simp

theorem eval_var_reg {sh : Shape} {σ : Sig} {m : Machine} {i : Nat} (h1 : 32 ≤ i) (h2 : i < 64) :
    (Sym.var i).eval (envOf sh σ m) = m.reg (Fin.ofNat 32 (i - 32)) - σ.inp := by
  simp [Sym.eval, envOf, show ¬ i < 32 by omega, h2]

theorem eval_var_lo {sh : Shape} {σ : Sig} {m : Machine} {i : Nat} (h : i < 32) :
    (Sym.var i).eval (envOf sh σ m) = m.reg (Fin.ofNat 32 i) := by
  simp [Sym.eval, envOf, h]

/-- `inp + (word − inp)`: a frame word as the leaf reads it. -/
theorem eval_ptr_var {sh : Shape} {σ : Sig} {m : Machine} {i : Nat} (h : 64 ≤ i) :
    (Sym.bin .add (.ptr 3 0) (.var i)).eval (envOf sh σ m) =
      TX.wordAt m (σ.fr + w (8 * (i - 64))) := by
  simp only [Sym.eval_bin, BinOp.eval, eval_ptr30, var_slot h]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

/-- Two registers the leaf sets alike. -/
theorem ctx_same {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {i i' : Nat} (hi : i < 32) (hi' : i' < 32) (h : l.S.reg i = l.S.reg i') :
    m'.reg (Fin.ofNat 32 i) = m'.reg (Fin.ofNat 32 i') := by
  rw [reg_eval C.hm' hi, reg_eval C.hm' hi', h]

/-! ## The field cursor's advance -/

/-- `s6 + k`, `k` the consumed word at `S-0x78`. -/
def advSym : Sym := .bin .add (.bin .add (.ptr 3 0) (.var 54)) (.init 0 760 8)

/-- `s7 - k`. -/
def lenSym : Sym := .bin .sub (.var 23) (.init 0 760 8)

theorem adv_reg {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {r : Nat} (hr : r < 32) (h : l.S.reg r = advSym) {X k : Nat} (h22 : m.reg 22 = σ.inp + w X)
    (hkv : (Sym.init 0 760 8).eval (envOf d.shape σ m) = w k) :
    m'.reg (Fin.ofNat 32 r) = σ.inp + w (X + k) := by
  rw [reg_eval C.hm' hr, h]
  simp only [advSym, Sym.eval_bin, BinOp.eval, hkv, eval_ptr30,
    eval_var_reg (show 32 ≤ 54 by decide) (show 54 < 64 by decide)]
  rw [show (Fin.ofNat 32 (54 - 32) : Fin 32) = 22 from rfl, h22]
  simp only [w]; rw [BitVec.add_comm σ.inp (BitVec.ofNat 64 X), BitVec.add_sub_cancel,
    F1.add_add_ofNat]

theorem len_reg {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {r : Nat} (hr : r < 32) (h : l.S.reg r = lenSym) {N k : Nat} (h23 : m.reg 23 = w N)
    (hkv : (Sym.init 0 760 8).eval (envOf d.shape σ m) = w k) (hkN : k ≤ N) (hN : N < 2 ^ 64) :
    m'.reg (Fin.ofNat 32 r) = w (N - k) := by
  rw [reg_eval C.hm' hr, h]
  simp only [lenSym, Sym.eval_bin, BinOp.eval, hkv, eval_var_lo (show 23 < 32 by decide)]
  rw [show (Fin.ofNat 32 23 : Fin 32) = 23 from rfl, h23]
  apply BitVec.eq_of_toNat_eq
  simp only [w, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The leaf moves the field cursor by `k` (`s6 += k`, `s7 -= k`) past field `f`, the tuple state
kept. -/
theorem tup_adv {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (hks : slotsKept d l tupSlots = true) (h22 : l.S.reg 22 = advSym)
    (h23 : l.S.reg 23 = lenSym) {c h p n j ht pt q k b f : Nat}
    (hc : TupC σ m c h p n j ht pt) (r22 : m.reg 22 = σ.inp + w (c + h + j + ht + q))
    (r23 : m.reg 23 = w (pt - q)) (hkv : (Sym.init 0 760 8).eval (envOf d.shape σ m) = w k)
    (hqk : q + k ≤ pt) (hpt : pt < 2 ^ 64) (hb : b ≤ q + k) (hfk : f + 1 ≤ q + k)
    (hsf : skip (f + 1) (tupPay σ c h p j ht pt) = some (q + k))
    (hok : TupOk (tupPay σ c h p j ht pt) (f + 1)) : AuthTup σ m' b (f + 1) false := by
  have e22 := adv_reg C (by decide) h22 r22 hkv
  have e23 := len_reg C (by decide) h23 r23 hkv (by omega) (by omega)
  refine tup_of (tupC_keep C hks hc) hb hfk hqk ?_ ?_ hsf hok (fun h => absurd h (by decide))
  · rw [show (22 : Fin 32) = Fin.ofNat 32 22 from rfl, e22, Nat.add_assoc]
  · rw [show (23 : Fin 32) = Fin.ofNat 32 23 from rfl, e23, Nat.sub_sub]

/-! ## A field's `decodeItem` return -/

/-- At a field's return site whose `SiteX` is `AuthTup b f false ∧ P` with the field cursor as the
input: the tuple state and the outcome on the field cursor's slice. -/
theorem tup_ret {i b f : Nat} {P : Sig → Machine → Prop} {σ : Sig} {m : Machine}
    (hne : (table[i]!).pc ≠ entry) (hpl : (table[i]!).plain = false)
    (hkd : (siteAt i).kind = .f2) (hSF : (siteAt i).kind.SiteFine (siteAt i) = true)
    (h10 : regFr (siteAt i) 10 = some 0x2e0) (ha : (siteAt i).arms = [4])
    (hsx : ∀ x mc, SiteX (table[i]!).pc σ x mc →
      AuthTup σ mc b f false ∧ P σ mc ∧ mc.reg 11 = mc.reg 22 ∧ mc.reg 12 = mc.reg 23)
    (hP : ∀ mc, (∀ o, o + 8 ≤ 0x2e0 → m.load (σ.fr + w o) 8 = mc.load (σ.fr + w o) 8) →
      P σ mc → P σ m)
    (hA : (mkCut (table[i]!)).A σ m) :
    ∃ c h p n j ht pt q before, TupC σ m c h p n j ht pt ∧ b ≤ q ∧ f ≤ q ∧ q ≤ pt ∧
      m.reg 22 = σ.inp + w (c + h + j + ht + q) ∧ m.reg 23 = w (pt - q) ∧ P σ m ∧
      c + h + p ≤ σ.len ∧ j ≤ p ∧ Pre σ.A σ.g σ.m ∧ σ.t = 4 ∧
      skip f (tupPay σ c h p j ht pt) = some q ∧ TupOk (tupPay σ c h p j ht pt) f ∧
      BytesAt m (σ.fr + w 0x2e0) (F2.result40 (σ.inp + w (c + h + j + ht + q))
        ((σ.payload.drop (c + h + j + ht + q)).take (pt - q)) before) := by
  obtain ⟨mc, x, hsx', harm, hpre, hk, hL, e22, e23, hout⟩ :=
    f2_ret hne hpl hkd hSF h10 (by decide) hA
  obtain ⟨ht, hPm, a11, a12⟩ := hsx x mc hsx'
  obtain ⟨c, h, p, n, j, ht, pt, q, hc, hbq, hfq, hqp, r22, r23, hsf, hok, -⟩ := of_tup ht
  have h4 : σ.t = 4 := arm4 harm ha
  have hc' := tupC_mono (fun o ho => hk o (by
    simp only [tupSlots, List.mem_cons, List.not_mem_nil, or_false] at ho; omega)) hL hc
  obtain ⟨ho, -, -, -, hle, -⟩ := hc
  obtain ⟨hjp, hcl, -⟩ := out_n hpre h4 ho
  obtain ⟨before, hres⟩ := hout _ _ (a11.trans r22) (a12.trans r23) (by omega)
  exact ⟨c, h, p, n, j, ht, pt, q, before, hc', hbq, hfq, hqp, e22.trans r22, e23.trans r23,
    hP mc hk hPm, hcl, hjp, hpre, h4, hsf, hok, hres⟩

/-- At a field's return site (`tup_ret`) with no error, not a list, and a payload length `tupLen`
accepts (`hlen`): the tuple state, the field's payload length `p0` and consumed length `h' + p0`
(within the tuple), its payload at `X + h'` (`X` the field cursor) when nonempty, and field `f`
checked. -/
theorem tup_field {i b f : Nat} {P : Sig → Machine → Prop} {σ : Sig} {m : Machine}
    (hne : (table[i]!).pc ≠ entry) (hpl : (table[i]!).plain = false)
    (hkd : (siteAt i).kind = .f2) (hSF : (siteAt i).kind.SiteFine (siteAt i) = true)
    (h10 : regFr (siteAt i) 10 = some 0x2e0) (ha : (siteAt i).arms = [4])
    (hsx : ∀ x mc, SiteX (table[i]!).pc σ x mc →
      AuthTup σ mc b f false ∧ P σ mc ∧ mc.reg 11 = mc.reg 22 ∧ mc.reg 12 = mc.reg 23)
    (hP : ∀ mc, (∀ o, o + 8 ≤ 0x2e0 → m.load (σ.fr + w o) 8 = mc.load (σ.fr + w o) 8) →
      P σ mc → P σ m)
    (hA : (mkCut (table[i]!)).A σ m) (hav : Avail σ m)
    (herr : (Sym.init 0 768 2).eval (envOf (table[i]!).shape σ m) = 0)
    (hnl : (isL 0x2e0).eval (envOf (table[i]!).shape σ m) = 0)
    (hlen : ∀ p0, p0 < 2 ^ 64 → (Sym.init 0 744 8).eval (envOf (table[i]!).shape σ m) = w p0 →
      tupLen f p0) :
    ∃ c h p n j ht pt q h' p0, TupC σ m c h p n j ht pt ∧ b ≤ q ∧ f ≤ q ∧ q ≤ pt ∧
      m.reg 22 = σ.inp + w (c + h + j + ht + q) ∧ m.reg 23 = w (pt - q) ∧ P σ m ∧
      c + h + j + ht + pt ≤ σ.len ∧
      (Sym.init 0 744 8).eval (envOf (table[i]!).shape σ m) = w p0 ∧ tupLen f p0 ∧
      (Sym.init 0 760 8).eval (envOf (table[i]!).shape σ m) = w (h' + p0) ∧ 1 ≤ h' + p0 ∧
      q + (h' + p0) ≤ pt ∧
      (p0 ≠ 0 → TX.wordAt m (σ.fr + w 0x2e0) = σ.inp + w (c + h + j + ht + q + h')) ∧
      (h' = 0 → p0 = 1) ∧ skip f (tupPay σ c h p j ht pt) = some q ∧
      skip (f + 1) (tupPay σ c h p j ht pt) = some (q + (h' + p0)) ∧
      TupOk (tupPay σ c h p j ht pt) (f + 1) := by
  obtain ⟨c, h, p, n, j, ht, pt, q, before, hC, hbq, hfq, hqp, r22, r23, hPm, hcl, hjp, hpre, h4,
    hsf, hok, hres⟩ := tup_ret hne hpl hkd hSF h10 ha hsx hP hA
  have hlen' := payload_len hpre
  obtain ⟨ho, -, -, hd, hle, -⟩ := id hC
  have hqp' : q < pt := by
    have hne := res_ok (ko := 0x2e0) (sh := (table[i]!).shape) (by decide) hres herr
    refine Nat.lt_of_not_le fun hh' => hne ?_
    rw [show pt - q = 0 by omega]
    simp [F2.decode]
  have hjp' : j < p := by
    have := decode_ne_nil hd
    simp only [List.length_take, List.length_drop] at this
    omega
  have hf := field_fits hpre h4 ho.1 ho.2.1 (by have := ho.2.2.1; omega)
    (by rw [List.length_drop, hlen']; omega) hd hle hsf (by omega)
  rw [tupPay_drop hle] at hf
  obtain ⟨h', p0, hd', hP0, hK, h1, hkn, h64, hW, hh0⟩ := field_dec hav hres hf herr hnl
  have hd'' : F2.decode ((tupPay σ c h p j ht pt).drop q) = .success false h' p0 := by
    rw [tupPay_drop hle]; exact hd'
  have hT := hlen p0 (by omega) hP0
  have hs' := skip_snoc hsf hd''
  rw [TX.itemConsumed, Nat.mod_eq_of_lt h64] at hs'
  exact ⟨c, h, p, n, j, ht, pt, q, h', p0, hC, hbq, hfq, hqp, r22, r23, hPm, by omega, hP0, hT,
    hK, h1, by omega, hW, hh0, hsf, hs', tupOk_succ hok hsf hd'' hT⟩

/-- A `geu (lit B)` bound on the payload length word gives `tupLen f` when it accepts `≤ B`. -/
theorem len_geu {f B : Nat} {v : Word} (h : (!(BitVec.ofNat 64 B).ult v) = true) (hB : B < 2 ^ 64)
    (hf : ∀ p, p ≤ B → tupLen f p) : ∀ p0, p0 < 2 ^ 64 → v = w p0 → tupLen f p0 :=
  fun p0 hp e => by
    have := geu_le h hB
    rw [e] at this
    simp only [w, BitVec.toNat_ofNat] at this
    exact hf p0 (by omega)

/-! ## A field's `decodeItem` call -/

/-- The call of `decodeItem` returning to `table[i']!` (outcome at `fr + ko`) on `n` payload
bytes from `X`, with the return site's `SiteX` and the list term at `0x68` kept: its index and
budget. -/
theorem field_call {d : CutData} {l : Leaf} {i' : Nat} {σ : Sig} {m m' : Machine}
    (C : Ctx d l σ m m') (CF : CallFacts (siteAt i') (table[i']!).pc σ m')
    (hkd : (siteAt i').kind = .f2) (hSF : (siteAt i').kind.SiteFine (siteAt i') = true)
    {ko : Nat} (h10 : regFr (siteAt i') 10 = some ko) (h2 : regFr (siteAt i') 2 = some 0)
    (hko : ko + 40 + 104 ≤ frameBytes) (hko8 : ko % 8 = 0)
    {X n : Nat} (h11 : m'.reg 11 = σ.inp + w X) (h12 : m'.reg 12 = w n) (hXn : X + n ≤ σ.len)
    (hsx : SiteX (table[i']!).pc σ ([], [], ⟨[], []⟩) m')
    (hR : retLen d l (siteAt i') (table[i']!) = true)
    (hk : (Loc.slot 0x68).sym l.S = (Loc.slot 0x68).sym d.shape.S)
    (hko' : (siteAt i').kind.Keeps (siteAt i') 0x68 = true)
    (hlo : listLoc (budgetAt d.pc).2 = some (.slot 0x68))
    (h' : (budgetAt (table[i']!).pc).2 = .list (.slot 0x68))
    (hK : 75 + (budgetAt (table[i']!).pc).1 + (l.S.steps - d.shape.S.steps) ≤
      (budgetAt d.pc).1) :
    ∃ x, IdxOk (siteAt i').kind σ x m' ∧ SiteX (table[i']!).pc σ x m' ∧
      ∀ m'', (calleeOf (siteAt i').kind).Post σ x m' m'' →
        (siteAt i').kind.bound + budgetOf (table[i']!) σ m'' +
          (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m := by
  have hsp : m'.reg 2 = σ.fr + w 0 := CF.shape.1 _ (lookup_mem (regFr_spec h2)) _ rfl
  have hout : m'.reg 10 = σ.fr + w ko := CF.shape.1 _ (lookup_mem (regFr_spec h10)) _ rfl
  have hf2 : F2.Pre m' := f2_pre_cur CF.common hsp hout hko hko8 h11 h12 hXn CF.aligned
  have hidx : IdxOk (siteAt i').kind σ ([], [], ⟨[], []⟩) m' := by
    rw [hkd]; exact ⟨hf2, trivial⟩
  refine ⟨_, hidx, hsx, fun m'' hpost => ?_⟩
  have hfld := CF.fields
  have hsite : SiteA (siteAt i') (table[i']!).pc σ ([], [], ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx, hfld, CF.chk, hsx⟩
  exact call_list_budget C hSF hsite hpost hR (by decide) hko' hk hlo h'
    (by rw [hkd]; exact hK)

/-! ## A byte loop's entry -/

/-- Into a byte loop (`.beL 10 11 (.slot 0x68)`) of at most `B` bytes from a cut whose budget is
the list term at `0x68`, kept. -/
theorem beL_budget {d d' : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (hlen : restLen d' σ m' ≤ restLen d σ m) (hb : (budgetAt d.pc).2 = .list (.slot 0x68))
    (hb' : (budgetAt d'.pc).2 = .beL 10 11 (.slot 0x68))
    (hk : (Loc.slot 0x68).sym l.S = (Loc.slot 0x68).sym d.shape.S) {B : Nat}
    (hK : (budgetAt d'.pc).1 + 22 * B + (l.S.steps - d.shape.S.steps) ≤ (budgetAt d.pc).1)
    {c e : Nat} (h10 : m'.reg 10 = σ.inp + w c) (h11 : m'.reg 11 = σ.inp + w e) (hce : c ≤ e)
    (he : e ≤ c + B) (he64 : e < 2 ^ 64) :
    budgetOf d' σ m' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m := by
  have hw := ctx_slot C (o := 0x68) (by decide) hk
  unfold budgetOf
  rw [hb, hb']
  simp only [innerOf, Loc.word]
  rw [show (Fin.ofNat 32 10 : Fin 32) = 10 from rfl, show (Fin.ofNat 32 11 : Fin 32) = 11 from rfl,
    h10, h11, sub_inp _ hce he64, hw]
  omega

/-! ## The tuple's `decodeItem` and the tuple a list -/

/-- `decodeItem` on the list cursor (`0x800024d0`, leaf 0): the count to `S-0x320`. -/
theorem DTF.leaf_800024d0_0 :
    LeafGoal DTF.plan DTF.plan.cuts[125]! ((DTF.plan.leaves 0x800024d0)[0]!) := by
  refine leaf_call_x (table[125]!) (table[126]!) (siteAt 126) ((leavesAt 0x800024d0)[0]!)
    F2.entry (by decide) DTF.cut_800024d0 (by decide) (by decide) (by decide) rfl rfl
    (by decide) ?_
  intro σ m m' hA hc C CF
  have hpre := C.F.common.2.1
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have hx := extra_of_A (d := table[125]!) (by decide) (by decide) hA
  rw [show (table[125]!).pc = 0x800024d0 by decide] at hx
  obtain ⟨c, h, p, n, j, ho, l78, hb⟩ : AuthLoop σ m := by simpa [Extra, AuthExtra] using hx
  obtain ⟨hjp, hcl, -⟩ := out_n hpre h4 ho
  have l50 : m'.load (σ.fr + w 0x50) 8 = some (w n) := by
    rw [ctx_word C (o := 0x50) (s := .init 0 0x78 8) (by decide) (by decide),
      src_init C (by decide) (by decide), wordAt_of_load l78]
  have r11 : m'.reg 11 = σ.inp + w (c + h + j) := by
    rw [show (11 : Fin 32) = Fin.ofNat 32 11 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x800024d0)[0]!).S.reg 11 = .bin .add (.ptr 3 0) (.var 78) by decide,
      eval_ptr_var (by decide), show 8 * (78 - 64) = 0x70 from rfl, wordAt_of_load ho.2.2.2.1]
  have r12 : m'.reg 12 = w (p - j) := by
    rw [show (12 : Fin 32) = Fin.ofNat 32 12 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x800024d0)[0]!).S.reg 12 = .init 0 0x68 8 by decide,
      src_init C (by decide) (by decide), wordAt_of_load ho.2.2.2.2.1]
  have hpre' : AuthPre σ m' :=
    ⟨c, h, p, n, j, authOut_mono (ctx_load C (by decide) (by decide))
      (ctx_load C (by decide) (by decide)) (ctx_load C (by decide) (by decide)) ho, l50,
      authBuf_mono (ctx_load C (by decide) (by decide)) (ctx_load C (by decide) (by decide))
        (fun _ _ hl => ctx_live C hl) hb, r11, r12⟩
  have hsx : SiteX (table[126]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[126]!).pc = 0x800024ec by decide]
    simpa [SiteX, AuthSite] using hpre'
  exact field_call C CF (ko := 0x2b8) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
    r11 r12 (by omega) hsx (by decide) (by decide) (by decide) rfl rfl (by decide)

/-- A list item's first byte is not `0x80`. -/
theorem decode_list_head {b : List Byte} {h p : Nat} (hd : F2.decode b = .success true h p) :
    b.head? ≠ some 128 := by
  cases b with
  | nil => simp [F2.decode] at hd
  | cons pre rest =>
    intro h128
    simp only [List.head?_cons, Option.some.injEq] at h128
    subst h128
    simp [F2.decode] at hd

/-- The tuple a list (`0x800024ec`, leaf 0): the field cursor at its payload, `decodeItem` on
its first field (chainId). -/
theorem DTF.leaf_800024ec_0 :
    LeafGoal DTF.plan DTF.plan.cuts[126]! ((DTF.plan.leaves 0x800024ec)[0]!) := by
  refine leaf_call_x (table[126]!) (table[127]!) (siteAt 127) ((leavesAt 0x800024ec)[0]!)
    F2.entry (by decide) DTF.cut_800024ec (by decide) (by decide) (by decide) rfl rfl
    (by decide) ?_
  intro σ m m' hA hc C CF
  have hpre := C.F.common.2.1
  have hav := C.F.common.avail
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hlen := payload_len hpre
  obtain ⟨mc, x, hsx', -, -, hk, hL, -, -, hout⟩ := f2_ret (i := 126) (ko := 0x2b8) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hA
  rw [show (table[126]!).pc = 0x800024ec by decide] at hsx'
  obtain ⟨c, h, p, n, j, ho, l50, hb, a11, a12⟩ : AuthPre σ mc := by
    simpa [SiteX, AuthSite] using hsx'
  obtain ⟨hjp, hcl, -⟩ := out_n hpre h4 ho
  obtain ⟨before, hres⟩ := hout _ _ a11 a12 (by omega)
  have herr := hc _ (show SBool.eq (.init 0 728 2) (.lit 0) ∈ _ by decide)
  have hlist := hc _ (show SBool.ne (.bin .and (.init 0 712 1) (.lit 1)) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, bne_iff_ne, ne_eq] at herr hlist
  have hne := res_ok (ko := 0x2b8) (by decide) hres herr
  cases hd : F2.decode ((σ.payload.drop (c + h + j)).take (p - j)) with
  | error => exact absurd hd hne
  | success l ht pt =>
  obtain ⟨hL', hP, hK, hW⟩ := res_words (sh := (table[126]!).shape) hav (by decide) hres hd
  have hl : l = true := by
    cases l
    · simp only [Bool.false_eq_true, if_false] at hL'
      exact absurd hL' hlist
    · rfl
  subst hl
  have hjp' : j < p := by
    refine Nat.lt_of_not_le fun hh => ?_
    rw [show p - j = 0 by omega] at hd
    simp [F2.decode] at hd
  have hf := auth_fits hpre h4 ho.1 ho.2.1 (by have := ho.2.2.1; omega)
    (by rw [List.length_drop, hlen]; omega)
  obtain ⟨-, hle, -⟩ := TX.fits_bounds hf hd
  simp only [List.length_take, List.length_drop, hlen] at hle
  rw [if_neg (decode_list_head hd)] at hW
  -- the target's frame words and registers
  have e := kept_load C (os := [0x70, 0x68, 0x30, 0x58, 0x60, 0x50]) (by decide) (by decide)
  have E : ∀ o ∈ [0x70, 0x68, 0x30, 0x58, 0x60, 0x50],
      m'.load (σ.fr + w o) 8 = mc.load (σ.fr + w o) 8 := fun o ho =>
    (e o ho).trans (hk o (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; omega))
  have l48 : m'.load (σ.fr + w 0x48) 8 = some (w (ht + pt)) := by
    rw [ctx_word C (o := 0x48) (s := .init 0 720 8) (by decide) (by decide)]
    exact congrArg some hK
  have hC : TupC σ m' c h p n j ht pt :=
    ⟨authOut_mono (E _ (by decide)) (E _ (by decide)) (E _ (by decide)) ho,
      by rw [E _ (by decide)]; exact l50,
      authBuf_mono (E _ (by decide)) (E _ (by decide)) (fun _ _ hl => ctx_live C (hL _ _ hl)) hb,
      hd, by omega, l48⟩
  have r22 : m'.reg 22 = σ.inp + w (c + h + j + ht + 0) := by
    rw [show (22 : Fin 32) = Fin.ofNat 32 22 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x800024ec)[0]!).S.reg 22 = .bin .add (.ptr 3 0) (.var 151) by decide,
      eval_ptr_var (by decide), show 8 * (151 - 64) = 0x2b8 from rfl, hW, Nat.add_zero]
    simp only [w]; rw [F1.add_add_ofNat]
  have r23 : m'.reg 23 = w (pt - 0) := by
    rw [show (23 : Fin 32) = Fin.ofNat 32 23 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x800024ec)[0]!).S.reg 23 = .init 0 704 8 by decide, Nat.sub_zero]
    exact hP
  have e11 := ctx_same C (i := 11) (i' := 22) (by decide) (by decide) (by decide)
  have e12 := ctx_same C (i := 12) (i' := 23) (by decide) (by decide) (by decide)
  have hsx : SiteX (table[127]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[127]!).pc = 0x8000252c by decide, siteX_tup0 (.inl rfl),
      show tupF 0x8000252c = 0 by decide]
    exact ⟨tup_of hC (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _) r22 r23 rfl (tupOk_zero _)
      (fun h => absurd h (by decide)), e11, e12⟩
  exact field_call C CF (ko := 0x2e0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (e11.trans r22) (e12.trans r23) (by omega) hsx (by decide)
    (by decide) (by decide) rfl rfl (by decide)

/-! ## A field's return -/

/-- chainId empty (`0x8000252c`, leaf 0): the cursor past it, `decodeItem` on the address. -/
theorem DTF.leaf_8000252c_0 :
    LeafGoal DTF.plan DTF.plan.cuts[127]! ((DTF.plan.leaves 0x8000252c)[0]!) := by
  refine leaf_call_x (table[127]!) (table[129]!) (siteAt 129) ((leavesAt 0x8000252c)[0]!)
    F2.entry (by decide) DTF.cut_8000252c (by decide) (by decide) (by decide) rfl rfl
    (by decide) ?_
  intro σ m m' hA hc C CF
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have herr := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have hnl := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have hge := hc _ (show SBool.geu (.lit 32) (.init 0 744 8) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, Sym.eval_lit] at herr hnl hge
  obtain ⟨c, h, p, n, j, ht, pt, q, h', p0, hC, -, hfq, hqp, r22, r23, -, hcl, -, -, hkv, hk1, hqk,
    -, -, -, hsf, hok⟩ := tup_field (i := 127) (f := 0) (P := fun _ _ => True) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun x mc hs => by
        rw [show (table[127]!).pc = 0x8000252c by decide, siteX_tup0 (.inl rfl),
          show tupF 0x8000252c = 0 by decide] at hs
        exact ⟨hs.1, trivial, hs.2⟩)
      (fun _ _ _ => trivial) hA C.F.common.avail herr hnl
      (len_geu hge (by decide) fun p hp => by simp [tupLen]; omega)
  have ht' := tup_adv C (b := 0) (by decide) (by decide) (by decide) hC r22 r23 hkv hqk
    (by omega) (Nat.zero_le _) (by omega) hsf hok
  have a11 := adv_reg C (r := 11) (by decide) (by decide) r22 hkv
  have a12 := len_reg C (r := 12) (by decide) (by decide) r23 hkv (by omega) (by omega)
  have e11 := ctx_same C (i := 11) (i' := 22) (by decide) (by decide) (by decide)
  have e12 := ctx_same C (i := 12) (i' := 23) (by decide) (by decide) (by decide)
  have hsx : SiteX (table[129]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[129]!).pc = 0x80002600 by decide, siteX_tup0 (.inr rfl),
      show tupF 0x80002600 = 0 + 1 by decide]
    exact ⟨ht', e11, e12⟩
  exact field_call C CF (ko := 0x2e0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a11 a12 (by omega) hsx (by decide) (by decide)
    (by decide) rfl rfl (by decide)

/-- The address (`0x80002600`, leaf 0): 20 bytes, its pointer to `S-0x2f8`, the cursor past it,
`decodeItem` on the nonce. -/
theorem DTF.leaf_80002600_0 :
    LeafGoal DTF.plan DTF.plan.cuts[129]! ((DTF.plan.leaves 0x80002600)[0]!) := by
  refine leaf_call_x (table[129]!) (table[130]!) (siteAt 130) ((leavesAt 0x80002600)[0]!)
    F2.entry (by decide) DTF.cut_80002600 (by decide) (by decide) (by decide) rfl rfl
    (by decide) ?_
  intro σ m m' hA hc C CF
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have herr := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have hnl := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have h20 := hc _ (show SBool.eq (.init 0 744 8) (.lit 20) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, Sym.eval_lit] at herr hnl h20
  obtain ⟨c, h, p, n, j, ht, pt, q, h', p0, hC, -, hfq, hqp, r22, r23, -, hcl, -, hp20, hkv, -,
    hqk, hW, hh0, -, hsf, hok⟩ := tup_field (i := 129) (f := 1) (P := fun _ _ => True) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun x mc hs => by
        rw [show (table[129]!).pc = 0x80002600 by decide, siteX_tup0 (.inr rfl),
          show tupF 0x80002600 = 1 by decide] at hs
        exact ⟨hs.1, trivial, hs.2⟩)
      (fun _ _ _ => trivial) hA C.F.common.avail herr hnl
      (fun p0 hp e => by
        rw [h20] at e
        have := congrArg BitVec.toNat e
        simp only [w, BitVec.toNat_ofNat] at this
        simp only [tupLen, if_true]; omega)
  have hp20' : p0 = 20 := by simpa [tupLen] using hp20
  subst hp20'
  have hh1 : 1 ≤ h' := by
    rcases Nat.eq_zero_or_pos h' with h0 | h0
    · have := hh0 h0; omega
    · exact h0
  have hW' := hW (by decide)
  have ht' := tup_adv C (b := 21) (by decide) (by decide) (by decide) hC r22 r23 hkv hqk
    (by omega) (by omega) (by omega) hsf hok
  have l78 : m'.load (σ.fr + w 0x78) 8 = some (σ.inp + w (c + h + j + ht + q + h')) := by
    rw [ctx_word C (o := 0x78) (s := .bin .add (.ptr 3 0) (.var 156)) (by decide) (by decide),
      eval_ptr_var (by decide), show 8 * (156 - 64) = 0x2e0 from rfl, hW']
  have hadd : AddrOk σ m' := ⟨_, l78, by omega⟩
  have a11 := adv_reg C (r := 11) (by decide) (by decide) r22 hkv
  have a12 := len_reg C (r := 12) (by decide) (by decide) r23 hkv (by omega) (by omega)
  have e11 := ctx_same C (i := 11) (i' := 22) (by decide) (by decide) (by decide)
  have e12 := ctx_same C (i := 12) (i' := 23) (by decide) (by decide) (by decide)
  have hsx : SiteX (table[130]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[130]!).pc = 0x80002654 by decide, siteX_tup21 (.inl rfl),
      show tupF 0x80002654 = 1 + 1 by decide]
    exact ⟨ht', hadd, e11, e12⟩
  exact field_call C CF (ko := 0x2e0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a11 a12 (by omega) hsx (by decide) (by decide)
    (by decide) rfl rfl (by decide)

/-- `AddrOk` survives a call below the outcome slot. -/
theorem addr_low {σ : Sig} {m mc : Machine}
    (hk : ∀ o, o + 8 ≤ 0x2e0 → m.load (σ.fr + w o) 8 = mc.load (σ.fr + w o) 8)
    (ha : AddrOk σ mc) : AddrOk σ m := by
  obtain ⟨a, la, hle⟩ := ha
  exact ⟨a, (hk 0x78 (by decide)).trans la, hle⟩

/-- nonce empty (`0x80002654`, leaf 0): the cursor past it, `decodeItem` on yParity. -/
theorem DTF.leaf_80002654_0 :
    LeafGoal DTF.plan DTF.plan.cuts[130]! ((DTF.plan.leaves 0x80002654)[0]!) := by
  refine leaf_call_x (table[130]!) (table[132]!) (siteAt 132) ((leavesAt 0x80002654)[0]!)
    F2.entry (by decide) DTF.cut_80002654 (by decide) (by decide) (by decide) rfl rfl
    (by decide) ?_
  intro σ m m' hA hc C CF
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have herr := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have hnl := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have hge := hc _ (show SBool.geu (.lit 8) (.init 0 744 8) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, Sym.eval_lit] at herr hnl hge
  obtain ⟨c, h, p, n, j, ht, pt, q, h', p0, hC, hbq, hfq, hqp, r22, r23, hadd, hcl, -, -, hkv, -,
    hqk, -, -, -, hsf, hok⟩ := tup_field (i := 130) (f := 2) (P := AddrOk) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (fun x mc hs => by
        rw [show (table[130]!).pc = 0x80002654 by decide, siteX_tup21 (.inl rfl),
          show tupF 0x80002654 = 2 by decide] at hs
        exact hs)
      (fun _ hk ha => addr_low hk ha) hA C.F.common.avail herr hnl
      (len_geu hge (by decide) fun p hp => by simp [tupLen]; omega)
  have ht' := tup_adv C (b := 21) (by decide) (by decide) (by decide) hC r22 r23 hkv hqk
    (by omega) (by omega) (by omega) hsf hok
  have a11 := adv_reg C (r := 11) (by decide) (by decide) r22 hkv
  have a12 := len_reg C (r := 12) (by decide) (by decide) r23 hkv (by omega) (by omega)
  have e11 := ctx_same C (i := 11) (i' := 22) (by decide) (by decide) (by decide)
  have e12 := ctx_same C (i := 12) (i' := 23) (by decide) (by decide) (by decide)
  have hsx : SiteX (table[132]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[132]!).pc = 0x800026d4 by decide, siteX_tup21 (.inr (.inl rfl)),
      show tupF 0x800026d4 = 2 + 1 by decide]
    exact ⟨ht', addr_keep C (regs := false) (by decide) hadd, e11, e12⟩
  exact field_call C CF (ko := 0x2e0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a11 a12 (by omega) hsx (by decide) (by decide)
    (by decide) rfl rfl (by decide)

/-- yParity empty (`0x800026d4`, leaf 0): the cursor past it, `decodeItem` on r. -/
theorem DTF.leaf_800026d4_0 :
    LeafGoal DTF.plan DTF.plan.cuts[132]! ((DTF.plan.leaves 0x800026d4)[0]!) := by
  refine leaf_call_x (table[132]!) (table[134]!) (siteAt 134) ((leavesAt 0x800026d4)[0]!)
    F2.entry (by decide) DTF.cut_800026d4 (by decide) (by decide) (by decide) rfl rfl
    (by decide) ?_
  intro σ m m' hA hc C CF
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have herr := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have hnl := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have hge := hc _ (show SBool.geu (.lit 8) (.init 0 744 8) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, Sym.eval_lit] at herr hnl hge
  obtain ⟨c, h, p, n, j, ht, pt, q, h', p0, hC, hbq, hfq, hqp, r22, r23, hadd, hcl, -, -, hkv, -,
    hqk, -, -, -, hsf, hok⟩ := tup_field (i := 132) (f := 3) (P := AddrOk) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (fun x mc hs => by
        rw [show (table[132]!).pc = 0x800026d4 by decide, siteX_tup21 (.inr (.inl rfl)),
          show tupF 0x800026d4 = 3 by decide] at hs
        exact hs)
      (fun _ hk ha => addr_low hk ha) hA C.F.common.avail herr hnl
      (len_geu hge (by decide) fun p hp => by simp [tupLen]; omega)
  have ht' := tup_adv C (b := 21) (by decide) (by decide) (by decide) hC r22 r23 hkv hqk
    (by omega) (by omega) (by omega) hsf hok
  have a11 := adv_reg C (r := 11) (by decide) (by decide) r22 hkv
  have a12 := len_reg C (r := 12) (by decide) (by decide) r23 hkv (by omega) (by omega)
  have e11 := ctx_same C (i := 11) (i' := 22) (by decide) (by decide) (by decide)
  have e12 := ctx_same C (i := 12) (i' := 23) (by decide) (by decide) (by decide)
  have hsx : SiteX (table[134]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[134]!).pc = 0x80002754 by decide, siteX_tup21 (.inr (.inr rfl)),
      show tupF 0x80002754 = 3 + 1 by decide]
    exact ⟨ht', addr_keep C (regs := false) (by decide) hadd, e11, e12⟩
  exact field_call C CF (ko := 0x2e0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a11 a12 (by omega) hsx (by decide) (by decide)
    (by decide) rfl rfl (by decide)

/-- r empty (`0x80002754`, leaf 0): the tuple consumed (`AuthEnd`), `decodeItem` on s at the
cursor past r. -/
theorem DTF.leaf_80002754_0 :
    LeafGoal DTF.plan DTF.plan.cuts[134]! ((DTF.plan.leaves 0x80002754)[0]!) := by
  refine leaf_call_x (table[134]!) (table[136]!) (siteAt 136) ((leavesAt 0x80002754)[0]!)
    F2.entry (by decide) DTF.cut_80002754 (by decide) (by decide) (by decide) rfl rfl
    (by decide) ?_
  intro σ m m' hA hc C CF
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have herr := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have hnl := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have hge := hc _ (show SBool.geu (.lit 32) (.init 0 744 8) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, Sym.eval_lit] at herr hnl hge
  obtain ⟨c, h, p, n, j, ht, pt, q, h', p0, hC, hbq, hfq, hqp, r22, r23, hadd, hcl, -, -, hkv, hk1,
    hqk, -, -, -, hsf, hok⟩ := tup_field (i := 134) (f := 4) (P := AddrOk) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (fun x mc hs => by
        rw [show (table[134]!).pc = 0x80002754 by decide, siteX_tup21 (.inr (.inr rfl)),
          show tupF 0x80002754 = 4 by decide] at hs
        exact hs)
      (fun _ hk ha => addr_low hk ha) hA C.F.common.avail herr hnl
      (len_geu hge (by decide) fun p hp => by simp [tupLen]; omega)
  have a11 := adv_reg C (r := 11) (by decide) (by decide) r22 hkv
  have a12 := len_reg C (r := 12) (by decide) (by decide) r23 hkv (by omega) (by omega)
  have he : AuthEnd σ m' 5 true := end_of C.F.common.2.1 (arm4 C.F.arms (by decide))
    (tupC_keep C (by decide) hC) (by omega) (addr_keep C (regs := false) (by decide) hadd)
    (by omega) hqk hsf hok (by rw [show (11 : Fin 32) = Fin.ofNat 32 11 from rfl, a11,
      Nat.add_assoc]) (by rw [show (12 : Fin 32) = Fin.ofNat 32 12 from rfl, a12, Nat.sub_sub])
  have hsx : SiteX (table[136]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[136]!).pc = 0x80002820 by decide, siteX_end]
    exact he
  exact field_call C CF (ko := 0x2e0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a11 a12 (by omega) hsx (by decide) (by decide)
    (by decide) rfl rfl (by decide)

/-! ## Into a field's byte loop -/

/-- A field's nonempty payload at `X + h'` (`p0 ≤ B` bytes) as the byte loop's cursor and end
(`a0`, `a1`): the loop head's `CurOk` and budget. -/
theorem loop_entry {d d' : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (h10 : l.S.reg 10 = .bin .add (.ptr 3 0) (.var 156))
    (h11 : l.S.reg 11 = .bin .add (.bin .add (.ptr 3 0) (.var 156)) (.init 0 744 8))
    (hlen : restLen d' σ m' ≤ restLen d σ m) (hb : (budgetAt d.pc).2 = .list (.slot 0x68))
    (hb' : (budgetAt d'.pc).2 = .beL 10 11 (.slot 0x68))
    (hk : (Loc.slot 0x68).sym l.S = (Loc.slot 0x68).sym d.shape.S) {B : Nat} (hB32 : B ≤ 32)
    (hK : (budgetAt d'.pc).1 + 22 * B + (l.S.steps - d.shape.S.steps) ≤ (budgetAt d.pc).1)
    {X h' p0 : Nat} (hP0 : (Sym.init 0 744 8).eval (envOf d.shape σ m) = w p0) (hp0 : p0 ≠ 0)
    (hB : p0 ≤ B) (hW : TX.wordAt m (σ.fr + w 0x2e0) = σ.inp + w (X + h'))
    (hle : X + h' + p0 ≤ σ.len) :
    CurOk σ m' (budgetAt d'.pc).2 ∧
      budgetOf d' σ m' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m := by
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have r10 : m'.reg 10 = σ.inp + w (X + h') := by
    rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, reg_eval C.hm' (by decide), h10,
      eval_ptr_var (by decide), show 8 * (156 - 64) = 0x2e0 from rfl, hW]
  have r11 : m'.reg 11 = σ.inp + w (X + h' + p0) := by
    rw [show (11 : Fin 32) = Fin.ofNat 32 11 from rfl, reg_eval C.hm' (by decide), h11]
    have e := eval_ptr_var (sh := d.shape) (σ := σ) (m := m) (show 64 ≤ 156 by decide)
    simp only [Sym.eval_bin, BinOp.eval] at e
    simp only [Sym.eval_bin, BinOp.eval, hP0]
    rw [e, show 8 * (156 - 64) = 0x2e0 from rfl, hW]
    simp only [w]; rw [F1.add_add_ofNat]
  refine ⟨?_, beL_budget C hlen hb hb' hk hK r10 r11 (by omega) (by omega) (by omega)⟩
  rw [hb']
  exact ⟨X + h', X + h' + p0, r10, r11, by omega, hle, by omega⟩


/-- chainId nonempty (`0x8000252c`, leaf 1): into its byte loop (`0x80002574`). -/
theorem DTF.leaf_8000252c_1 :
    LeafGoal DTF.plan DTF.plan.cuts[127]! ((DTF.plan.leaves 0x8000252c)[1]!) := by
  refine leaf_at_x (table[127]!) (table[128]!) ((leavesAt 0x8000252c)[1]!) (by decide)
    DTF.cut_8000252c (by decide) (by decide) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have herr := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have hnl := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have hge := hc _ (show SBool.geu (.lit 32) (.init 0 744 8) ∈ _ by decide)
  have hne := hc _ (show SBool.ne (.init 0 744 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, bne_iff_ne, ne_eq, Sym.eval_lit] at herr hnl hge hne
  obtain ⟨c, h, p, n, j, ht, pt, q, h', p0, hC, hbq, hfq, hqp, r22, r23, -, hcl, hP0, hT, hkv,
    hk1, hqk, hW, -, hsf0, hsf, hok⟩ := tup_field (i := 127) (f := 0) (P := fun _ _ => True) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun x mc hs => by
        rw [show (table[127]!).pc = 0x8000252c by decide, siteX_tup0 (.inl rfl),
          show tupF 0x8000252c = 0 by decide] at hs
        exact ⟨hs.1, trivial, hs.2⟩)
      (fun _ _ _ => trivial) hA C.F.common.avail herr hnl
      (len_geu hge (by decide) fun p hp => by simp [tupLen]; omega)
  have hp0' : p0 ≠ 0 := fun h0 => hne (by rw [hP0, h0])
  have hpB : p0 ≤ 32 := by simpa [tupLen] using hT
  have e22 := ctx_reg C (i := 22) (i' := 22) (by decide) (by decide) (by decide)
  have e23 := ctx_reg C (i := 23) (i' := 23) (by decide) (by decide) (by decide)
  have l2f8 : m'.load (σ.fr + w 0x2f8) 8 = some (w (h' + p0)) := by
    rw [ctx_word C (o := 0x2f8) (s := .init 0 760 8) (by decide) (by decide)]
    exact congrArg some hkv
  have ht' : AuthTup σ m' 0 0 true := tup_of (tupC_keep C (by decide) hC) hbq hfq hqp
    (e22.trans r22) (e23.trans r23) hsf0 (tupOk_mono hok (by omega))
    fun _ => ⟨hok, _, l2f8, hk1, hqk, hsf⟩
  refine ⟨?_, loop_entry C (by decide) (by decide)
    (lenFrom_sound C (rs' := (table[128]!).rest) (by decide)) rfl rfl (by decide) (B := 32)
    (by decide) (by decide) hP0 hp0' hpB (hW hp0') (by omega)⟩
  rw [show (table[128]!).pc = 0x80002574 by decide]
  simpa [Extra, AuthExtra] using ht'

/-- nonce nonempty (`0x80002654`, leaf 1): into its byte loop (`0x80002690`). -/
theorem DTF.leaf_80002654_1 :
    LeafGoal DTF.plan DTF.plan.cuts[130]! ((DTF.plan.leaves 0x80002654)[1]!) := by
  refine leaf_at_x (table[130]!) (table[131]!) ((leavesAt 0x80002654)[1]!) (by decide)
    DTF.cut_80002654 (by decide) (by decide) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have herr := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have hnl := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have hge := hc _ (show SBool.geu (.lit 8) (.init 0 744 8) ∈ _ by decide)
  have hne := hc _ (show SBool.ne (.init 0 744 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, bne_iff_ne, ne_eq, Sym.eval_lit] at herr hnl hge hne
  obtain ⟨c, h, p, n, j, ht, pt, q, h', p0, hC, hbq, hfq, hqp, r22, r23, hadd, hcl, hP0, hT, hkv,
    hk1, hqk, hW, -, hsf0, hsf, hok⟩ := tup_field (i := 130) (f := 2) (P := AddrOk) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun x mc hs => by
        rw [show (table[130]!).pc = 0x80002654 by decide, siteX_tup21 (.inl rfl),
          show tupF 0x80002654 = 2 by decide] at hs
        exact hs)
      (fun _ hk ha => addr_low hk ha) hA C.F.common.avail herr hnl
      (len_geu hge (by decide) fun p hp => by simp [tupLen]; omega)
  have hp0' : p0 ≠ 0 := fun h0 => hne (by rw [hP0, h0])
  have hpB : p0 ≤ 8 := by simpa [tupLen] using hT
  have e22 := ctx_reg C (i := 22) (i' := 22) (by decide) (by decide) (by decide)
  have e23 := ctx_reg C (i := 23) (i' := 23) (by decide) (by decide) (by decide)
  have l2f8 : m'.load (σ.fr + w 0x2f8) 8 = some (w (h' + p0)) := by
    rw [ctx_word C (o := 0x2f8) (s := .init 0 760 8) (by decide) (by decide)]
    exact congrArg some hkv
  have ht' : AuthTup σ m' 21 2 true := tup_of (tupC_keep C (by decide) hC) hbq hfq hqp
    (e22.trans r22) (e23.trans r23) hsf0 (tupOk_mono hok (by omega))
    fun _ => ⟨hok, _, l2f8, hk1, hqk, hsf⟩
  refine ⟨?_, loop_entry C (by decide) (by decide)
    (lenFrom_sound C (rs' := (table[131]!).rest) (by decide)) rfl rfl (by decide) (B := 8)
    (by decide) (by decide) hP0 hp0' hpB (hW hp0') (by omega)⟩
  rw [show (table[131]!).pc = 0x80002690 by decide]
  simpa [Extra, AuthExtra, tupF] using
    (⟨ht', addr_keep C (regs := false) (by decide) hadd⟩ : AuthTup σ m' 21 2 true ∧ AddrOk σ m')

/-- yParity nonempty (`0x800026d4`, leaf 1): into its byte loop (`0x80002710`). -/
theorem DTF.leaf_800026d4_1 :
    LeafGoal DTF.plan DTF.plan.cuts[132]! ((DTF.plan.leaves 0x800026d4)[1]!) := by
  refine leaf_at_x (table[132]!) (table[133]!) ((leavesAt 0x800026d4)[1]!) (by decide)
    DTF.cut_800026d4 (by decide) (by decide) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have herr := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have hnl := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have hge := hc _ (show SBool.geu (.lit 8) (.init 0 744 8) ∈ _ by decide)
  have hne := hc _ (show SBool.ne (.init 0 744 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, bne_iff_ne, ne_eq, Sym.eval_lit] at herr hnl hge hne
  obtain ⟨c, h, p, n, j, ht, pt, q, h', p0, hC, hbq, hfq, hqp, r22, r23, hadd, hcl, hP0, hT, hkv,
    hk1, hqk, hW, -, hsf0, hsf, hok⟩ := tup_field (i := 132) (f := 3) (P := AddrOk) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun x mc hs => by
        rw [show (table[132]!).pc = 0x800026d4 by decide, siteX_tup21 (.inr (.inl rfl)),
          show tupF 0x800026d4 = 3 by decide] at hs
        exact hs)
      (fun _ hk ha => addr_low hk ha) hA C.F.common.avail herr hnl
      (len_geu hge (by decide) fun p hp => by simp [tupLen]; omega)
  have hp0' : p0 ≠ 0 := fun h0 => hne (by rw [hP0, h0])
  have hpB : p0 ≤ 8 := by simpa [tupLen] using hT
  have e22 := ctx_reg C (i := 22) (i' := 22) (by decide) (by decide) (by decide)
  have e23 := ctx_reg C (i := 23) (i' := 23) (by decide) (by decide) (by decide)
  have l2f8 : m'.load (σ.fr + w 0x2f8) 8 = some (w (h' + p0)) := by
    rw [ctx_word C (o := 0x2f8) (s := .init 0 760 8) (by decide) (by decide)]
    exact congrArg some hkv
  have ht' : AuthTup σ m' 21 3 true := tup_of (tupC_keep C (by decide) hC) hbq hfq hqp
    (e22.trans r22) (e23.trans r23) hsf0 (tupOk_mono hok (by omega))
    fun _ => ⟨hok, _, l2f8, hk1, hqk, hsf⟩
  refine ⟨?_, loop_entry C (by decide) (by decide)
    (lenFrom_sound C (rs' := (table[133]!).rest) (by decide)) rfl rfl (by decide) (B := 8)
    (by decide) (by decide) hP0 hp0' hpB (hW hp0') (by omega)⟩
  rw [show (table[133]!).pc = 0x80002710 by decide]
  simpa [Extra, AuthExtra, tupF] using
    (⟨ht', addr_keep C (regs := false) (by decide) hadd⟩ : AuthTup σ m' 21 3 true ∧ AddrOk σ m')

/-- r nonempty (`0x80002754`, leaf 1): into its byte loop (`0x8000279c`). -/
theorem DTF.leaf_80002754_1 :
    LeafGoal DTF.plan DTF.plan.cuts[134]! ((DTF.plan.leaves 0x80002754)[1]!) := by
  refine leaf_at_x (table[134]!) (table[135]!) ((leavesAt 0x80002754)[1]!) (by decide)
    DTF.cut_80002754 (by decide) (by decide) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have herr := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have hnl := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have hge := hc _ (show SBool.geu (.lit 32) (.init 0 744 8) ∈ _ by decide)
  have hne := hc _ (show SBool.ne (.init 0 744 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, bne_iff_ne, ne_eq, Sym.eval_lit] at herr hnl hge hne
  obtain ⟨c, h, p, n, j, ht, pt, q, h', p0, hC, hbq, hfq, hqp, r22, r23, hadd, hcl, hP0, hT, hkv,
    hk1, hqk, hW, -, hsf0, hsf, hok⟩ := tup_field (i := 134) (f := 4) (P := AddrOk) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun x mc hs => by
        rw [show (table[134]!).pc = 0x80002754 by decide, siteX_tup21 (.inr (.inr rfl)),
          show tupF 0x80002754 = 4 by decide] at hs
        exact hs)
      (fun _ hk ha => addr_low hk ha) hA C.F.common.avail herr hnl
      (len_geu hge (by decide) fun p hp => by simp [tupLen]; omega)
  have hp0' : p0 ≠ 0 := fun h0 => hne (by rw [hP0, h0])
  have hpB : p0 ≤ 32 := by simpa [tupLen] using hT
  have e22 := ctx_reg C (i := 22) (i' := 22) (by decide) (by decide) (by decide)
  have e23 := ctx_reg C (i := 23) (i' := 23) (by decide) (by decide) (by decide)
  have l2f8 : m'.load (σ.fr + w 0x2f8) 8 = some (w (h' + p0)) := by
    rw [ctx_word C (o := 0x2f8) (s := .init 0 760 8) (by decide) (by decide)]
    exact congrArg some hkv
  have ht' : AuthTup σ m' 21 4 true := tup_of (tupC_keep C (by decide) hC) hbq hfq hqp
    (e22.trans r22) (e23.trans r23) hsf0 (tupOk_mono hok (by omega))
    fun _ => ⟨hok, _, l2f8, hk1, hqk, hsf⟩
  refine ⟨?_, loop_entry C (by decide) (by decide)
    (lenFrom_sound C (rs' := (table[135]!).rest) (by decide)) rfl rfl (by decide) (B := 32)
    (by decide) (by decide) hP0 hp0' hpB (hW hp0') (by omega)⟩
  rw [show (table[135]!).pc = 0x8000279c by decide]
  simpa [Extra, AuthExtra, tupF] using
    (⟨ht', addr_keep C (regs := false) (by decide) hadd⟩ : AuthTup σ m' 21 4 true ∧ AddrOk σ m')

/-- s nonempty (`0x80002820`, leaf 4): `s` checked, into its byte loop (`0x80002868`). -/
theorem DTF.leaf_80002820_4 :
    LeafGoal DTF.plan DTF.plan.cuts[136]! ((DTF.plan.leaves 0x80002820)[4]!) := by
  refine leaf_at_x (table[136]!) (table[137]!) ((leavesAt 0x80002820)[4]!) (by decide)
    DTF.cut_80002820 (by decide) (by decide) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have herr := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have hnl := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have hge := hc _ (show SBool.geu (.lit 32) (.init 0 744 8) ∈ _ by decide)
  have hne := hc _ (show SBool.ne (.init 0 744 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, bne_iff_ne, ne_eq, Sym.eval_lit] at herr hnl hge hne
  have hpre := C.F.common.2.1
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  obtain ⟨c, hh, p, n, j, ht, pt, q, before, he, hres⟩ := end_2820 hA
  obtain ⟨he6, h', p0, hP0, hp0, -, -, hkn, hW⟩ :=
    end_s hpre h4 C.F.common.avail he hres herr hnl (geu_le hge (by decide))
  obtain ⟨hjp, hcl, -⟩ := out_n hpre h4 he.1
  have hle := he.2.2.2.2.2.2.2.2.1
  have hp0' : p0 ≠ 0 := fun h0 => hne (by rw [hP0, h0])
  refine ⟨?_, loop_entry C (by decide) (by decide)
    (lenFrom_sound C (rs' := (table[137]!).rest) (by decide)) rfl rfl (by decide) (B := 32)
    (by decide) (by decide) hP0 hp0' hp0 (hW hp0') (by omega)⟩
  rw [show (table[137]!).pc = 0x80002868 by decide]
  simpa [Extra, AuthExtra] using end_keep C (regs := false) (by decide)
    (⟨c, hh, p, n, j, ht, pt, q, he6, fun h => absurd h (by decide)⟩ : AuthEnd σ m 6 false)

/-! ## Out of a field's byte loop -/

/-- At a byte loop's head (`AuthTup b f true`): the tuple state, the field's consumed length `k`
(the word at `S-0x78`) within the tuple, field `f` checked. -/
theorem tup_src {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (h4 : σ.t = 4) (hi : (Loc.slot 0x2f8).sym d.shape.S = .init 0 0x2f8 8) {b f : Nat}
    (ht : AuthTup σ m b f true) :
    ∃ c h p n j ht pt q k, TupC σ m c h p n j ht pt ∧ b ≤ q ∧ f ≤ q ∧
      m.reg 22 = σ.inp + w (c + h + j + ht + q) ∧ m.reg 23 = w (pt - q) ∧
      (Sym.init 0 760 8).eval (envOf d.shape σ m) = w k ∧ 1 ≤ k ∧ q + k ≤ pt ∧
      c + h + j + ht + pt ≤ σ.len ∧ skip (f + 1) (tupPay σ c h p j ht pt) = some (q + k) ∧
      TupOk (tupPay σ c h p j ht pt) (f + 1) := by
  obtain ⟨c, h, p, n, j, ht, pt, q, hC, hbq, hfq, -, r22, r23, -, -, hnx⟩ := of_tup ht
  obtain ⟨hok, k, lk, hk1, hqk, hsf⟩ := hnx rfl
  obtain ⟨hjp, hcl, -⟩ := out_n C.F.common.2.1 h4 hC.1
  have hle := hC.2.2.2.2.1
  exact ⟨c, h, p, n, j, ht, pt, q, k, hC, hbq, hfq, r22, r23,
    by rw [src_init C (by decide) hi, wordAt_of_load lk], hk1, hqk, by omega, hsf, hok⟩

/-- chainId's loop done (`0x80002574`, leaf 1): the cursor past it, `decodeItem` on the address. -/
theorem DTF.leaf_80002574_1 :
    LeafGoal DTF.plan DTF.plan.cuts[128]! ((DTF.plan.leaves 0x80002574)[1]!) := by
  refine leaf_call_xo (table[128]!) (table[129]!) (siteAt 129) ((leavesAt 0x80002574)[1]!)
    F2.entry (by decide) DTF.cut_80002574 (by decide) (coreChkL_0 (by decide))
    (coreChkL_obl (by decide) DTF.cut_80002574 (by decide)) (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hx := extra_of_A (d := table[128]!) (by decide) (by decide) hA
  rw [show (table[128]!).pc = 0x80002574 by decide] at hx
  obtain ⟨c, h, p, n, j, ht, pt, q, k, hC, -, hfq, r22, r23, hkv, hk1, hqk, hcl, hsf, hok⟩ :=
    tup_src C (arm4 C.F.arms (by decide)) (by decide)
      (show AuthTup σ m 0 0 true by simpa [Extra, AuthExtra] using hx)
  have ht' := tup_adv C (b := 0) (by decide) (by decide) (by decide) hC r22 r23 hkv hqk
    (by omega) (Nat.zero_le _) (by omega) hsf hok
  have a11 := adv_reg C (r := 11) (by decide) (by decide) r22 hkv
  have a12 := len_reg C (r := 12) (by decide) (by decide) r23 hkv (by omega) (by omega)
  have e11 := ctx_same C (i := 11) (i' := 22) (by decide) (by decide) (by decide)
  have e12 := ctx_same C (i := 12) (i' := 23) (by decide) (by decide) (by decide)
  have hsx : SiteX (table[129]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[129]!).pc = 0x80002600 by decide, siteX_tup0 (.inr rfl),
      show tupF 0x80002600 = 0 + 1 by decide]
    exact ⟨ht', e11, e12⟩
  exact field_call C CF (ko := 0x2e0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a11 a12 (by omega) hsx (by decide) (by decide)
    (by decide) rfl rfl (by decide)

/-- nonce's loop done (`0x80002690`, leaf 1): the cursor past it, `decodeItem` on yParity. -/
theorem DTF.leaf_80002690_1 :
    LeafGoal DTF.plan DTF.plan.cuts[131]! ((DTF.plan.leaves 0x80002690)[1]!) := by
  refine leaf_call_xo (table[131]!) (table[132]!) (siteAt 132) ((leavesAt 0x80002690)[1]!)
    F2.entry (by decide) DTF.cut_80002690 (by decide) (coreChkL_0 (by decide))
    (coreChkL_obl (by decide) DTF.cut_80002690 (by decide)) (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hx := extra_of_A (d := table[131]!) (by decide) (by decide) hA
  rw [show (table[131]!).pc = 0x80002690 by decide] at hx
  obtain ⟨htm, hadd⟩ : AuthTup σ m 21 2 true ∧ AddrOk σ m := by
    simpa [Extra, AuthExtra, tupF] using hx
  obtain ⟨c, h, p, n, j, ht, pt, q, k, hC, hbq, hfq, r22, r23, hkv, hk1, hqk, hcl, hsf, hok⟩ :=
    tup_src C (arm4 C.F.arms (by decide)) (by decide) htm
  have ht' := tup_adv C (b := 21) (by decide) (by decide) (by decide) hC r22 r23 hkv hqk
    (by omega) (by omega) (by omega) hsf hok
  have a11 := adv_reg C (r := 11) (by decide) (by decide) r22 hkv
  have a12 := len_reg C (r := 12) (by decide) (by decide) r23 hkv (by omega) (by omega)
  have e11 := ctx_same C (i := 11) (i' := 22) (by decide) (by decide) (by decide)
  have e12 := ctx_same C (i := 12) (i' := 23) (by decide) (by decide) (by decide)
  have hsx : SiteX (table[132]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[132]!).pc = 0x800026d4 by decide, siteX_tup21 (.inr (.inl rfl)),
      show tupF 0x800026d4 = 2 + 1 by decide]
    exact ⟨ht', addr_keep C (regs := false) (by decide) hadd, e11, e12⟩
  exact field_call C CF (ko := 0x2e0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a11 a12 (by omega) hsx (by decide) (by decide)
    (by decide) rfl rfl (by decide)

/-- yParity's loop done (`0x80002710`, leaf 1): the cursor past it, `decodeItem` on r. -/
theorem DTF.leaf_80002710_1 :
    LeafGoal DTF.plan DTF.plan.cuts[133]! ((DTF.plan.leaves 0x80002710)[1]!) := by
  refine leaf_call_xo (table[133]!) (table[134]!) (siteAt 134) ((leavesAt 0x80002710)[1]!)
    F2.entry (by decide) DTF.cut_80002710 (by decide) (coreChkL_0 (by decide))
    (coreChkL_obl (by decide) DTF.cut_80002710 (by decide)) (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hx := extra_of_A (d := table[133]!) (by decide) (by decide) hA
  rw [show (table[133]!).pc = 0x80002710 by decide] at hx
  obtain ⟨htm, hadd⟩ : AuthTup σ m 21 3 true ∧ AddrOk σ m := by
    simpa [Extra, AuthExtra, tupF] using hx
  obtain ⟨c, h, p, n, j, ht, pt, q, k, hC, hbq, hfq, r22, r23, hkv, hk1, hqk, hcl, hsf, hok⟩ :=
    tup_src C (arm4 C.F.arms (by decide)) (by decide) htm
  have ht' := tup_adv C (b := 21) (by decide) (by decide) (by decide) hC r22 r23 hkv hqk
    (by omega) (by omega) (by omega) hsf hok
  have a11 := adv_reg C (r := 11) (by decide) (by decide) r22 hkv
  have a12 := len_reg C (r := 12) (by decide) (by decide) r23 hkv (by omega) (by omega)
  have e11 := ctx_same C (i := 11) (i' := 22) (by decide) (by decide) (by decide)
  have e12 := ctx_same C (i := 12) (i' := 23) (by decide) (by decide) (by decide)
  have hsx : SiteX (table[134]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[134]!).pc = 0x80002754 by decide, siteX_tup21 (.inr (.inr rfl)),
      show tupF 0x80002754 = 3 + 1 by decide]
    exact ⟨ht', addr_keep C (regs := false) (by decide) hadd, e11, e12⟩
  exact field_call C CF (ko := 0x2e0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a11 a12 (by omega) hsx (by decide) (by decide)
    (by decide) rfl rfl (by decide)

/-- r's loop done (`0x8000279c`, leaf 1): the tuple consumed (`AuthEnd`), `decodeItem` on s at
the cursor past r. -/
theorem DTF.leaf_8000279c_1 :
    LeafGoal DTF.plan DTF.plan.cuts[135]! ((DTF.plan.leaves 0x8000279c)[1]!) := by
  refine leaf_call_xo (table[135]!) (table[136]!) (siteAt 136) ((leavesAt 0x8000279c)[1]!)
    F2.entry (by decide) DTF.cut_8000279c (by decide) (coreChkL_0 (by decide))
    (coreChkL_obl (by decide) DTF.cut_8000279c (by decide)) (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have hx := extra_of_A (d := table[135]!) (by decide) (by decide) hA
  rw [show (table[135]!).pc = 0x8000279c by decide] at hx
  obtain ⟨htm, hadd⟩ : AuthTup σ m 21 4 true ∧ AddrOk σ m := by
    simpa [Extra, AuthExtra, tupF] using hx
  obtain ⟨c, h, p, n, j, ht, pt, q, k, hC, hbq, hfq, r22, r23, hkv, hk1, hqk, hcl, hsf, hok⟩ :=
    tup_src C h4 (by decide) htm
  have a11 := adv_reg C (r := 11) (by decide) (by decide) r22 hkv
  have a12 := len_reg C (r := 12) (by decide) (by decide) r23 hkv (by omega) (by omega)
  have he : AuthEnd σ m' 5 true := end_of C.F.common.2.1 h4 (tupC_keep C (by decide) hC)
    (by omega) (addr_keep C (regs := false) (by decide) hadd) (by omega) hqk hsf hok
    (by rw [show (11 : Fin 32) = Fin.ofNat 32 11 from rfl, a11, Nat.add_assoc])
    (by rw [show (12 : Fin 32) = Fin.ofNat 32 12 from rfl, a12, Nat.sub_sub])
  have hsx : SiteX (table[136]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[136]!).pc = 0x80002820 by decide, siteX_end]
    exact he
  exact field_call C CF (ko := 0x2e0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a11 a12 (by omega) hsx (by decide) (by decide)
    (by decide) rfl rfl (by decide)

end ZesuExec.Fn.DTF
