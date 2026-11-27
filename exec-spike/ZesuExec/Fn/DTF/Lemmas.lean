import ZesuExec.Fn.DTF.Cuts
import ZesuExec.Fn.Stage
import ZesuExec.Fn.F1.Lemmas
import ZesuExec.Sym.Summary

/-!
# DTF: lemmas for the cut lemmas and leaves (programme plan S7 step 4)

`cut_plain`: the cut lemma of every cut reached only by jumps and branches whose state has no
extra region (70 of the 161): its `Common`, `ShapeOk` and the entry's `Pre` give `Env.WF`,
`Match` (registers by the shape, the base regions present, the vtable word and the shape's frame
slots as known facts) and `RodataLoaded`.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## The entry's numbers -/

theorem pre_sp {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    Layout.ramLo + stackBytes ≤ σ.S.toNat ∧ σ.S.toNat ≤ Layout.ramHi ∧ σ.S.toNat % 16 = 0 := by
  obtain ⟨-, ⟨hal, hlo, hhi, -⟩, -⟩ := hpre
  exact ⟨hlo, hhi, hal⟩

theorem S_sub_toNat {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {k : Nat} (hk : k ≤ stackBytes) :
    (σ.S - w k).toNat = σ.S.toNat - k := by
  have := pre_sp hpre
  simp only [w, BitVec.toNat_sub, BitVec.toNat_ofNat]
  unfold Layout.ramLo stackBytes TX.stackBytes at *; omega

theorem fr_toNat {σ : Sig} (hpre : Pre σ.A σ.g σ.m) : σ.fr.toNat = σ.S.toNat - frameBytes :=
  S_sub_toNat hpre (by decide)

/-- The base regions with their executor view. -/
def shapeFull (σ : Sig) : Fn.Shape :=
  [((σ.fr, frameBytes), frameR), ((σ.res, resultBytes), resR), ((σ.ao, 16), aoR),
    ((σ.inp, σ.len), inR)]

theorem regionsOf_base {sh : Shape} (hx : sh.extra = []) (σ : Sig) (m : Machine) :
    regionsOf sh σ m = (shapeFull σ).map (·.1) := by
  simp [regionsOf, hx, shapeFull]

theorem shapeFull_snd (σ : Sig) : (shapeFull σ).map (·.2) = baseRegions := rfl

theorem pre_ok {σ : Sig} (hpre : Pre σ.A σ.g σ.m) : ∀ p ∈ shapeFull σ, RegionOk p := by
  have hsp := pre_sp hpre
  have hfr := fr_toNat hpre
  obtain ⟨-, -, -, hres, -, hao, -, -, -, -, hin, -⟩ := hpre
  simp only [shapeFull, List.mem_cons, List.not_mem_nil, or_false]
  unfold RamRange at hres hao
  unfold TX.InputArea RamRange at hin
  rintro p (rfl | rfl | rfl | rfl) <;>
    simp [RegionOk, frameR, resR, aoR, inR, frameBytes, resultBytes, Machine.writable,
      Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi, Layout.rodataLo,
      Layout.rodataHi, Layout.inputLo, Layout.inputHi, stackBytes, TX.stackBytes, Sig.res,
      Sig.ao, Sig.inp, Sig.len, Sig.S, Sig.fr] at * <;> omega

theorem pre_disj {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    ((shapeFull σ).map (·.1)).Pairwise Fn.Disjoint := by
  have hsp := pre_sp hpre
  have hfr := fr_toNat hpre
  have hst := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d1, d2, d3, d4, d5, d6, -⟩ := hpre
  unfold TX.Apart at d1 d2 d3 d4 d5 d6
  simp only [Sig.S, w] at hst
  rw [hst] at d4 d5 d6
  simp only [shapeFull, List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true,
    Fn.Disjoint, hfr]
  simp only [Sig.S, Sig.res, Sig.ao, Sig.inp, Sig.len, stackBytes, TX.stackBytes, frameBytes,
    resultBytes, false_implies, implies_true, and_true] at hsp d1 d2 d3 d4 d5 d6 ⊢
  simp only [Layout.ramLo, Layout.ramHi] at hsp
  omega

theorem pre_wf {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (mh : Machine) (ov : Nat → Option Sym)
    (ks : List Write) :
    Env.WF (entryEnv mh ((shapeFull σ).map (·.1))) (entryState ov baseRegions ks) := by
  rw [← shapeFull_snd]
  exact entry_wf (shapeFull σ) (pre_ok hpre) (pre_disj hpre)

theorem pre_fit {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    ∀ p ∈ shapeFull σ, p.1.1.toNat + p.1.2 < 2 ^ 64 := by
  have hfr := fr_toNat hpre
  have hsp := pre_sp hpre
  obtain ⟨-, -, -, hres, -, hao, -, -, -, -, hin, -⟩ := hpre
  unfold RamRange at hres hao
  unfold TX.InputArea RamRange at hin
  simp only [shapeFull, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl) <;>
    simp [Sig.res, Sig.ao, Sig.inp, Sig.len, frameBytes, resultBytes, Layout.ramLo,
      Layout.ramHi, Layout.inputLo, Layout.inputHi, stackBytes, TX.stackBytes] at * <;> omega

/-! ## Memory a `Common` machine keeps from the entry -/

theorem Present.of_preserved {m m' : Machine} {a : Word} {n : Nat} (h : Present m a n)
    (hp : Preserved m m') : Present m' a n := fun j hj => hp.1 _ (h j hj)

theorem isSome_of_load {m : Machine} {a v : Word} (h : m.load a 8 = some v) :
    ∀ t < 8, (m.mem (a + BitVec.ofNat 64 t)).isSome := F1.present_of_load h (Nat.le_refl _)

theorem present16 {m : Machine} {a : Word} (h0 : (m.load a 8).isSome)
    (h8 : (m.load (a + 8) 8).isSome) : Present m a 16 := by
  obtain ⟨v0, e0⟩ := Option.isSome_iff_exists.mp h0
  obtain ⟨v8, e8⟩ := Option.isSome_iff_exists.mp h8
  intro j hj
  rcases Nat.lt_or_ge j 8 with h | h
  · exact isSome_of_load e0 j h
  · have := isSome_of_load e8 (j - 8) (by omega)
    rwa [show (8 : Word) = BitVec.ofNat 64 8 from rfl, F1.add_add_ofNat,
      show 8 + (j - 8) = j by omega] at this

/-- A byte outside DTF's owned memory and the allocator's private memory is as at the entry. -/
theorem same_of_apart {σ : Sig} {m : Machine} (hc : Common σ m) {a : Word}
    (hown : ¬ Owned σ a) (hpriv : ¬ σ.A.Priv σ.g.L a) : m.mem a = σ.m.mem a :=
  hc.2.2.2.2.2.2.2.1 a fun h => h.elim hown hpriv

theorem ao_same {σ : Sig} {m : Machine} (hc : Common σ m) {j : Nat} (hj : j < 16) :
    m.mem (σ.ao + BitVec.ofNat 64 j) = σ.m.mem (σ.ao + BitVec.ofNat 64 j) := by
  have hpre := hc.2.1
  have hsp := pre_sp hpre
  have hst := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
  obtain ⟨-, -, -, -, -, hao, -, -, -, -, -, -, -, -, -, -, d1, -, d3, -, d5, -, -, d8, -, -,
    hP⟩ := hpre
  have hr : InRange σ.ao 16 (σ.ao + BitVec.ofNat 64 j) := by
    unfold RamRange Layout.ramHi at hao
    simp only [InRange]; rw [toNat_add_ofNat (by simp [Sig.ao]; omega)]; omega
  refine same_of_apart hc (fun h => ?_) (hP _ (.inr (.inl hr)))
  unfold TX.Apart at d1 d3 d5 d8
  simp only [Sig.S, w] at hst
  rw [hst] at d5
  unfold Owned InRange at h; unfold InRange at hr
  simp only [Sig.S, w] at h
  rw [hst] at h
  simp only [Sig.res, Sig.ao, Sig.S, TX.scratch, BitVec.toNat_ofNat, Layout.extraParams,
    resultBytes, stackBytes, TX.stackBytes] at h hr d1 d3 d5 d8 hst ⊢
  unfold Layout.ramLo Layout.ramHi at *
  omega

theorem input_same {σ : Sig} {m : Machine} (hc : Common σ m) {j : Nat} (hj : j < σ.len) :
    m.mem (σ.inp + BitVec.ofNat 64 j) = σ.m.mem (σ.inp + BitVec.ofNat 64 j) := by
  have hpre := hc.2.1
  have hfit := pre_fit hpre ((σ.inp, σ.len), inR) (by simp [shapeFull])
  have hst := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d2, -, -, -, d6, -, -, d9, -,
    hP⟩ := hpre
  have hr : InRange σ.inp σ.len (σ.inp + BitVec.ofNat 64 j) := by
    simp only [InRange]; rw [toNat_add_ofNat (by simp at hfit; omega)]; omega
  refine same_of_apart hc (fun h => ?_) (hP _ (.inr (.inr (.inl hr))))
  unfold TX.Apart at d2 d6 d9
  simp only [Sig.S, w] at hst
  rw [hst] at d6
  unfold Owned InRange at h; unfold InRange at hr
  simp only [Sig.S, w] at h
  rw [hst] at h
  simp only [Sig.res, Sig.inp, Sig.len, Sig.S, TX.scratch, BitVec.toNat_ofNat, Layout.extraParams,
    resultBytes, stackBytes, TX.stackBytes] at h hr d2 d6 d9 hst ⊢
  omega

/-- What `Match` needs of a machine: the entry's `Pre`, the stack and the result present, the
allocator object and the input as at the entry. `Common` gives it, and so does the entry. -/
structure Avail (σ : Sig) (m : Machine) : Prop where
  pre : Pre σ.A σ.g σ.m
  stack : Present m (σ.S - w stackBytes) stackBytes
  res : Present m σ.res resultBytes
  ao : ∀ {j}, j < 16 → m.mem (σ.ao + BitVec.ofNat 64 j) = σ.m.mem (σ.ao + BitVec.ofNat 64 j)
  inp : ∀ {j}, j < σ.len → m.mem (σ.inp + BitVec.ofNat 64 j) = σ.m.mem (σ.inp + BitVec.ofNat 64 j)

theorem Common.avail {σ : Sig} {m : Machine} (hc : Common σ m) : Avail σ m :=
  ⟨hc.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, ao_same hc, input_same hc⟩

theorem avail_entry {σ : Sig} (hpre : Pre σ.A σ.g σ.m) : Avail σ σ.m :=
  ⟨hpre, hpre.2.1.2.2.2, hpre.2.2.2.2.1, fun _ => rfl, fun _ => rfl⟩

theorem input_present {σ : Sig} {m : Machine} (hc : Avail σ m) {j : Nat} (hj : j < σ.len) :
    (m.mem (σ.inp + BitVec.ofNat 64 j)).isSome := by
  rw [hc.inp hj]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hb, hl, -⟩ := hc.pre
  rw [hb j (by simp only [Sig.len] at hj hl ⊢; omega)]; rfl

theorem stack_present {σ : Sig} {m : Machine} (hc : Avail σ m) {j : Nat} (hj : j < frameBytes) :
    (m.mem (σ.fr + BitVec.ofNat 64 j)).isSome := by
  have := hc.stack (stackBytes - frameBytes + j) (by
    unfold stackBytes TX.stackBytes frameBytes at *; omega)
  rwa [show σ.S - w stackBytes + BitVec.ofNat 64 (stackBytes - frameBytes + j) =
    σ.fr + BitVec.ofNat 64 j by
      simp only [Sig.fr, Sig.S, w]; unfold stackBytes TX.stackBytes frameBytes at *; bv_omega] at this

theorem common_vtable {σ : Sig} {m : Machine} (hc : Avail σ m) :
    m.load (σ.ao + 8) 8 = some (w TX.vtable) := by
  rw [load_congr (m := σ.m) fun t ht => by
    rw [show σ.ao + 8 + BitVec.ofNat 64 t = σ.ao + BitVec.ofNat 64 (8 + t) by bv_omega]
    exact hc.ao (by omega)]
  exact hc.pre.2.2.2.2.2.2.2.2.1

theorem common_present {σ : Sig} {m : Machine} (hc : Avail σ m) (r j : Nat) (hr : r < 4)
    (hj : j < (entryEnv m ((shapeFull σ).map (·.1))).size r) :
    (m.mem ((entryEnv m ((shapeFull σ).map (·.1))).base r + BitVec.ofNat 64 j)).isSome := by
  have hpre := hc.pre
  simp only [entryEnv, Env.size, Env.base, shapeFull] at hj ⊢
  obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  all_goals simp at hj ⊢
  · exact stack_present hc hj
  · exact hc.res j hj
  · rw [hc.ao hj]
    obtain ⟨-, -, -, -, -, -, -, hao0, hao8, -⟩ := hpre
    exact present16 hao0 (Option.isSome_iff_exists.mpr ⟨_, hao8⟩) j hj
  · exact input_present hc hj

/-- A frame word is loadable. -/
theorem frame_load {σ : Sig} {m : Machine} (hc : Avail σ m) {o : Nat} (ho : o + 8 ≤ frameBytes) :
    m.load (σ.fr + w o) 8 = some (TX.wordAt m (σ.fr + w o)) := by
  have hpre := hc.pre
  have hsp := pre_sp hpre
  have hfr := fr_toNat hpre
  have ho' : (σ.fr + w o).toNat = σ.fr.toNat + o := toNat_add_ofNat (by
    unfold Layout.ramHi frameBytes at *; omega)
  have hr : Machine.readable (σ.fr + w o).toNat 8 = true := by
    rw [ho', hfr]; unfold frameBytes stackBytes TX.stackBytes at *
    simp [Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi] at hsp ⊢; omega
  have hb : (readBytes m.mem (σ.fr + w o).toNat 8).isSome := readBytes_isSome_of fun t ht => by
    rw [ofNat_toNat_add]
    have := stack_present hc (j := o + t) (by omega)
    rwa [← F1.add_add_ofNat] at this
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hb
  have hl : m.load (σ.fr + w o) 8 = some (ofBytesLE bs) := by
    unfold Machine.load; rw [if_pos hr, hbs]; rfl
  rw [hl]; simp [TX.wordAt, hl]

/-! ## `Match` at a plain cut -/

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (x, y) :: l, a, b, h => by
    cases hxa : a == x with
    | true =>
      have := beq_iff_eq.mp hxa; subst this
      simp [List.lookup, hxa] at h; subst h; exact List.mem_cons_self
    | false =>
      simp [List.lookup, hxa] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- No register or frame slot of the shape is a slot base, except register 10 when the shape has
region 4; frame slots are 8-aligned words in the frame; registers are below 32. -/
def Shape.Fine (sh : Shape) : Bool :=
  sh.regs.all (fun p => decide (p.1 < 32) && (p.2 != .slot || (p.1 == 10 && !sh.extra.isEmpty))) &&
    sh.slots.all (fun p => decide (p.1 % 8 = 0) && decide (p.1 + 8 ≤ frameBytes) && p.2 != .slot)

theorem env_base0 (sh : Shape) (σ : Sig) (m : Machine) : (envOf sh σ m).base 0 = σ.fr := by
  simp [envOf, entryEnv, Env.base, regionsOf]

theorem env_base1 (sh : Shape) (σ : Sig) (m : Machine) : (envOf sh σ m).base 1 = σ.res := by
  simp [envOf, entryEnv, Env.base, regionsOf]

theorem env_base2 (sh : Shape) (σ : Sig) (m : Machine) : (envOf sh σ m).base 2 = σ.ao := by
  simp [envOf, entryEnv, Env.base, regionsOf]

theorem env_base3 (sh : Shape) (σ : Sig) (m : Machine) : (envOf sh σ m).base 3 = σ.inp := by
  simp [envOf, entryEnv, Env.base, regionsOf]

/-- A shape value with a word evaluates to that word; a payload pointer to the register. -/
theorem val_reg {sh : Shape} {σ : Sig} {m : Machine} (hs : ShapeOk σ sh m) {i : Nat} {v : Val}
    (hi : i < 32) (hmem : (i, v) ∈ sh.regs) (hv : v ≠ .slot) :
    (v.sym (regVar i)).eval (envOf sh σ m) = m.reg (Fin.ofNat 32 i) := by
  have hw := hs.1 _ hmem
  cases v with
  | fr k => have h := hw _ rfl; simp only at h; rw [h]; simp [Val.sym, Sym.eval, env_base0, w]
  | res k => have h := hw _ rfl; simp only at h; rw [h]; simp [Val.sym, Sym.eval, env_base1, w]
  | ao k => have h := hw _ rfl; simp only at h; rw [h]; simp [Val.sym, Sym.eval, env_base2, w]
  | vt => have h := hw _ rfl; simp only at h; rw [h]; rfl
  | inp =>
    simp only [Val.sym, Sym.eval, BinOp.eval, env_base3, regVar]
    simp only [envOf, show ¬ 32 + i < 32 by omega, if_false, show 32 + i < 64 by omega, if_true,
      show 32 + i - 32 = i by omega]
    bv_omega
  | slot => exact absurd rfl hv

theorem env_base4 (sh : Shape) {R : Region} (hx : sh.extra = [R]) (σ : Sig) (m : Machine) :
    (envOf sh σ m).base 4 = m.reg 10 := by
  simp [envOf, entryEnv, Env.base, regionsOf, hx]

theorem env_size4 (sh : Shape) {R : Region} (hx : sh.extra = [R]) (σ : Sig) (m : Machine) :
    (envOf sh σ m).size 4 = R.size.getD 0 := by
  simp [envOf, entryEnv, Env.size, regionsOf, hx]

theorem extra_one {sh : Shape} (hx : sh.extra.length ≤ 1) (hne : sh.extra ≠ []) :
    ∃ R, sh.extra = [R] := by
  rcases h : sh.extra with _ | ⟨R, _ | ⟨R', l⟩⟩
  · exact absurd h hne
  · exact ⟨R, rfl⟩
  · rw [h] at hx; simp at hx

/-- `Match` at a cut whose state is the shape's: base regions from `Avail`, region 4 (at most
one extra region, based at `a0`) from `h4`. -/
theorem match_gen {sh : Shape} {σ : Sig} {m : Machine} (hc : Avail σ m) (hs : ShapeOk σ sh m)
    (hx : sh.extra.length ≤ 1) (h4 : ∀ R ∈ sh.extra, Present m (m.reg 10) (R.size.getD 0))
    (hfine : sh.Fine = true) : Match (envOf sh σ m) sh.S m := by
  simp only [Shape.Fine, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at hfine
  obtain ⟨hfr, hfs⟩ := hfine
  refine ⟨by simp [Shape.S, entryState], fun i => ?_, fun r j hr hj => ?_, fun k hk t ht => ?_⟩
  · rw [Shape.S, entryState_reg]
    split
    · next h0 => simp [Sym.eval, Machine.reg, h0]
    · next h0 =>
      cases h : sh.ov i.val with
      | none => simp [Sym.eval, envOf, i.isLt]
      | some s =>
        simp only [Shape.ov, Option.map_eq_some_iff] at h
        obtain ⟨v, hl, rfl⟩ := h
        have hmem := lookup_mem hl
        by_cases hv : v = .slot
        · subst hv
          have h10 := (hfr _ hmem).2
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_true_eq_false, false_or,
            Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h10
          obtain ⟨hi, hne⟩ := h10
          obtain ⟨R, hR⟩ := extra_one hx hne
          have : i = 10 := Fin.ext hi
          subst this
          simp [Val.sym, Sym.eval, env_base4 sh hR]
        · have := val_reg hs i.isLt hmem hv
          simpa using this
  · have hpres : (m.mem ((envOf sh σ m).base r + BitVec.ofNat 64 j)).isSome := by
      have hr' : r < 4 + sh.extra.length := by
        simp [Shape.S, entryState, baseRegions] at hr; omega
      rcases Nat.lt_or_ge r 4 with hr4 | hr4
      · have hb : (envOf sh σ m).base r = (entryEnv m ((shapeFull σ).map (·.1))).base r := by
          obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
          all_goals simp [envOf, entryEnv, Env.base, regionsOf, shapeFull]
        have hsz : (envOf sh σ m).size r = (entryEnv m ((shapeFull σ).map (·.1))).size r := by
          obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
          all_goals simp [envOf, entryEnv, Env.size, regionsOf, shapeFull]
        rw [hb]; exact common_present hc r j hr4 (hsz ▸ hj)
      · obtain ⟨R, hR⟩ := extra_one hx (by intro h; simp [h] at hr'; omega)
        obtain rfl : r = 4 := by simp [hR] at hr'; omega
        rw [env_base4 sh hR]
        rw [env_size4 sh hR] at hj
        exact h4 R (by simp [hR]) j hj
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hpres
    simp only [memByte, Shape.S, entryState, List.find?_nil, Env.byte0, envOf, entryEnv,
      Env.base] at hb ⊢
    rw [hb]; rfl
  · simp only [Shape.S, entryState, Shape.known, List.mem_cons, List.mem_map] at hk
    rcases hk with rfl | ⟨⟨o, v⟩, hov, rfl⟩
    · have := load_bytes (common_vtable hc) (Nat.le_refl _) t ht
      simp only [vtableKnown, Env.byte0, envOf, entryEnv, regionsOf, shapeFull, List.map_cons,
        List.cons_append, List.getD_cons_succ, List.getD_cons_zero, Sym.eval]
      rw [← F1.add_add_ofNat, show BitVec.ofNat 64 8 = (8 : Word) from rfl, this]; rfl
    · obtain ⟨⟨h8, hle⟩, hv⟩ := hfs _ hov
      simp only at h8 hle hv ⊢
      have hl := frame_load hc hle
      have hbyte := load_bytes hl (Nat.le_refl _) t ht
      have ha : σ.fr + BitVec.ofNat 64 (o + t) = σ.fr + w o + BitVec.ofNat 64 t := by
        rw [F1.add_add_ofNat]
      simp only [Env.byte0, envOf, entryEnv, regionsOf, shapeFull, List.map_cons,
        List.cons_append, List.getD_cons_zero]
      rw [ha, hbyte]
      simp only [Option.getD_some]
      congr 1
      cases v with
      | inp =>
        simp only [Val.sym, Sym.eval, BinOp.eval, Env.base, envOf, entryEnv, regionsOf,
          shapeFull, List.map_cons, List.cons_append, List.getD_cons_succ, List.getD_cons_zero,
          slotVar]
        simp only [show ¬ 64 + o / 8 < 32 by omega, show ¬ 64 + o / 8 < 64 by omega, if_false,
          show 64 + o / 8 - 64 = o / 8 by omega, show 8 * (o / 8) = o by omega]
        bv_omega
      | slot => exact absurd rfl hv
      | _ =>
        have := hs.2 _ hov _ rfl
        rw [hl] at this
        simp only [Option.some.injEq] at this
        rw [this]
        simp [Val.sym, Val.word, Sym.eval, Env.base, entryEnv, regionsOf, shapeFull, w]

theorem match_plain {sh : Shape} {σ : Sig} {m : Machine} (hc : Avail σ m) (hs : ShapeOk σ sh m)
    (hx : sh.extra = []) (hfine : sh.Fine = true) : Match (envOf sh σ m) sh.S m :=
  match_gen hc hs (by simp [hx]) (by simp [hx]) hfine

/-- The cut lemma of a cut reached only by jumps and branches, with no extra region. -/
theorem cut_plain (d : CutData) (hpc : d.pc ≠ entry) (hs : d.site = none)
    (hx : d.shape.extra = []) (hfine : d.shape.Fine = true) : CutOK vcPlan (mkCut d) := by
  intro σ m hA
  simp only [mkCut, if_neg hpc, ACut, hs, reduceCtorEq, false_and, exists_false,
    or_false] at hA
  obtain ⟨-, hpcm, hc, hsh, -⟩ := hA
  have hwf : Env.WF (envOf d.shape σ m) d.shape.S := by
    have := pre_wf hc.2.1 m d.shape.ov d.shape.known
    rw [Shape.S, hx, List.append_nil]
    exact Env.WF.of_regions this (regionsOf_base hx σ m)
  exact ⟨hwf, match_plain hc.avail hsh hx hfine, hc.2.2.1, hpcm⟩

/-- The entry's shape: no frame slots; registers are payload pointers, `sp`, `a0` or `a1`. -/
def EntryShape (sh : Shape) : Bool :=
  sh.slots.isEmpty && sh.regs.all fun p =>
    p.2 == .inp || p == (2, .fr frameBytes) || p == (10, .res 0) || p == (11, .ao 0)

/-- The cut lemma of the entry. -/
theorem cut_entry (d : CutData) (hpc : d.pc = entry) (hx : d.shape.extra = [])
    (hfine : d.shape.Fine = true) (hes : EntryShape d.shape = true) : CutOK vcPlan (mkCut d) := by
  intro σ m hA
  simp only [mkCut, if_pos hpc] at hA
  obtain ⟨rfl, hpcm, hpre⟩ := hA
  simp only [EntryShape, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at hes
  obtain ⟨hsl, hrg⟩ := hes
  have hsh : ShapeOk σ d.shape σ.m := by
    refine ⟨fun p hp v hv => ?_, fun p hp => by simp [hsl] at hp⟩
    rcases hrg p hp with ((h | h) | h) | h
    · rw [h] at hv; cases hv
    · subst h; simp only [Val.word, Option.some.injEq] at hv; subst hv
      simp [Sig.fr, Sig.S, w, BitVec.sub_add_cancel]
    · subst h; simp only [Val.word, Option.some.injEq] at hv; subst hv
      simp [Sig.res, w]
    · subst h; simp only [Val.word, Option.some.injEq] at hv; subst hv
      simp [Sig.ao, w]
  have hwf : Env.WF (envOf d.shape σ σ.m) d.shape.S := by
    have := pre_wf hpre σ.m d.shape.ov d.shape.known
    rw [Shape.S, hx, List.append_nil]
    exact Env.WF.of_regions this (regionsOf_base hx σ σ.m)
  exact ⟨hwf, match_plain (avail_entry hpre) hsh hx hfine, hpre.1, hpcm.trans hpc.symm⟩

/-! ## Cuts with region 4 (`0x80000574`, `0x80002138`, `0x80002434`) -/

/-- No byte of `a` is a byte of `b` (a region of size 0 is apart from everything). -/
def PDisjoint (a b : Word × Nat) : Prop :=
  ∀ j < a.2, ∀ j' < b.2, a.1.toNat + j ≠ b.1.toNat + j'

theorem Disjoint.pd {a b : Word × Nat} (h : Fn.Disjoint a b) : PDisjoint a b := by
  intro j hj j' hj'; simp only [Fn.Disjoint] at h; omega

/-- `entry_wf` with pointwise disjointness. -/
theorem entry_wf' {m : Machine} {ov : Nat → Option Sym} {ks : List Write} (shape : Fn.Shape)
    (hok : ∀ p ∈ shape, RegionOk p) (hdisj : (shape.map (·.1)).Pairwise PDisjoint) :
    Env.WF (entryEnv m (shape.map (·.1))) (entryState ov (shape.map (·.2)) ks) := by
  have hfield : ∀ r (R : Region), (entryState ov (shape.map (·.2)) ks).regions[r]? = some R →
      ∃ hl : r < (entryEnv m (shape.map (·.1))).regions.length,
        R = (shape[r]'(by simpa [entryEnv] using hl)).2 := by
    intro r R hR
    obtain ⟨hr, hR⟩ := List.getElem?_eq_some_iff.mp hR
    simp [entryState] at hr hR
    exact ⟨by simpa [entryEnv] using hr, hR.symm⟩
  refine ⟨by simp [entryEnv, entryState], fun r r' j j' hne hj hj' => ?_,
    fun r R s hR hs => ?_, fun r R hR => ?_, fun r R hR => ?_⟩
  · have hr : r < shape.length := by
      rcases Nat.lt_or_ge r shape.length with h | hc
      · exact h
      · simp [Env.size, entryEnv, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simpa using hc)] at hj
    have hr' : r' < shape.length := by
      rcases Nat.lt_or_ge r' shape.length with h | hc
      · exact h
      · simp [Env.size, entryEnv, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simpa using hc)] at hj'
    have hl : r < (entryEnv m (shape.map (·.1))).regions.length := by simpa [entryEnv] using hr
    have hl' : r' < (entryEnv m (shape.map (·.1))).regions.length := by simpa [entryEnv] using hr'
    rw [Env.size_of_lt hl] at hj
    rw [Env.size_of_lt hl'] at hj'
    rw [Env.base_of_lt hl, Env.base_of_lt hl']
    have hp := List.pairwise_iff_getElem.mp hdisj
    simp only [entryEnv] at hj hj' ⊢
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hp r r' (by simpa using hr) (by simpa using hr') h j hj j' hj'
    · exact fun e => hp r' r (by simpa using hr') (by simpa using hr) h j' hj' j hj e.symm
  · obtain ⟨hl, rfl⟩ := hfield r R hR
    rw [Env.size_of_lt hl]
    simpa [entryEnv] using (hok _ (List.getElem_mem _)).1 s hs
  · obtain ⟨hl, rfl⟩ := hfield r R hR
    rw [Env.base_of_lt hl]
    simpa [entryEnv] using (hok _ (List.getElem_mem _)).2.1
  · obtain ⟨hl, rfl⟩ := hfield r R hR
    rw [Env.base_of_lt hl, Env.size_of_lt hl]
    simpa [entryEnv] using (hok _ (List.getElem_mem _)).2.2

/-- `Env.WF` at a cut with region 4: the region is fine and apart from the base regions. -/
theorem wf_slot {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (m : Machine) {sh : Shape} {R : Region}
    (hx : sh.extra = [R]) (hok : RegionOk ((m.reg 10, R.size.getD 0), R))
    (hap : ∀ p ∈ (shapeFull σ).map (·.1), PDisjoint p (m.reg 10, R.size.getD 0)) :
    Env.WF (envOf sh σ m) sh.S := by
  have := entry_wf' (m := m) (ov := sh.ov) (ks := sh.known)
    (shapeFull σ ++ [((m.reg 10, R.size.getD 0), R)]) (fun p hp => by
      rcases List.mem_append.mp hp with h | h
      · exact pre_ok hpre p h
      · simp only [List.mem_singleton] at h; subst h; exact hok) (by
      rw [List.map_append, List.pairwise_append]
      refine ⟨(pre_disj hpre).imp Disjoint.pd, by simp, fun a ha b hb => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb; exact hap a ha)
  simp only [List.map_append, shapeFull_snd, List.map_cons, List.map_nil] at this
  rw [Shape.S, hx]
  exact Env.WF.of_regions this (by simp [envOf, entryEnv, regionsOf, hx, shapeFull])

theorem inRange_self {b : Word} {n j : Nat} (hfit : b.toNat + n < 2 ^ 64) (hj : j < n) :
    InRange b n (b + BitVec.ofNat 64 j) := by
  simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega

/-- A byte of a base region is not the allocator's. -/
theorem base_not_priv {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    ∀ p ∈ (shapeFull σ).map (·.1), ∀ j < p.2,
      ¬ σ.A.Priv σ.g.L (p.1 + BitVec.ofNat 64 j) := by
  have hfit := pre_fit hpre
  have hfr := fr_toNat hpre
  have hsp := pre_sp hpre
  have hst := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hP⟩ := hpre
  simp only [shapeFull, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hfit ⊢
  have hf := hfit _ (.inl rfl)
  have hr := hfit _ (.inr (.inl rfl))
  have ha := hfit _ (.inr (.inr (.inl rfl)))
  have hi := hfit _ (.inr (.inr (.inr rfl)))
  simp only at hf hr ha hi
  rintro p (rfl | rfl | rfl | rfl) j hj <;> simp only at hj <;> apply hP
  · refine .inr (.inr (.inr (.inl ?_)))
    have h1 := inRange_self hf hj
    simp only [InRange] at h1 ⊢
    have h2 : (σ.m.reg 2 - BitVec.ofNat 64 stackBytes).toNat = (σ.m.reg 2).toNat - stackBytes :=
      hst
    rw [h2]
    simp only [Sig.S] at hfr hsp h1 ⊢
    unfold frameBytes stackBytes TX.stackBytes at *
    omega
  · exact .inl (inRange_self hr hj)
  · exact .inr (.inl (inRange_self ha hj))
  · exact .inr (.inr (.inl (inRange_self hi hj)))

/-- A slot of the allocator's private memory is apart from the base regions. -/
theorem slot_apart {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {m : Machine} {n : Nat}
    (hs : SlotOk σ m n) : ∀ p ∈ (shapeFull σ).map (·.1), PDisjoint p (m.reg 10, n) := by
  intro p hp j hj j' hj' he
  have hfit := pre_fit hpre
  have hp' : p.1.toNat + p.2 < 2 ^ 64 := by
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hfit q hq
  obtain ⟨hram, -, hpriv⟩ := hs
  unfold RamRange Layout.ramHi at hram
  simp only at hj'
  apply base_not_priv hpre p hp j hj
  have heq : p.1 + BitVec.ofNat 64 j = m.reg 10 + BitVec.ofNat 64 j' := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    exact he
  rw [heq]
  refine hpriv _ ?_
  simp only [InRange]
  rw [toNat_add_ofNat (by omega)]
  omega

/-- The cut lemma of a buffer-store cut (`0x80002138`, `0x80002434`): region 4 is the slot. -/
theorem cut_slot (d : CutData) (n : Nat) (hpc : d.pc ≠ entry) (hs : d.site = none)
    (hx : d.shape.extra = [⟨some n, 1, true⟩]) (hfine : d.shape.Fine = true)
    (hext : (d.pc = 0x80002138 ∧ n = 32) ∨ (d.pc = 0x80002434 ∧ n = 0x90)) :
    CutOK vcPlan (mkCut d) := by
  intro σ m hA
  simp only [mkCut, if_neg hpc, ACut, hs, reduceCtorEq, false_and, exists_false,
    or_false] at hA
  obtain ⟨-, hpcm, hc, hsh, -, -, hex, -⟩ := hA
  have hslot : SlotOk σ m n := by
    rcases hext with ⟨he, rfl⟩ | ⟨he, rfl⟩ <;> simpa [Extra, he] using hex
  have hok : RegionOk ((m.reg 10, (some n : Option Nat).getD 0), ⟨some n, 1, true⟩) := by
    obtain ⟨hram, -⟩ := hslot
    unfold RamRange at hram
    simp [RegionOk, Machine.writable, Machine.inRange, hram.1, hram.2, Nat.mod_one]
  have hwf := wf_slot hc.2.1 m hx hok (slot_apart hc.2.1 hslot)
  exact ⟨hwf, match_gen hc.avail hsh (by simp [hx]) (by simpa [hx] using hslot.2.1) hfine,
    hc.2.2.1, hpcm⟩

/-- The five jump-table words are rodata. -/
theorem table_rodata : ∀ t < 5, ∀ j < 8, (zesuImage.rodataByte? (0x80110050 + 8 * t + j)).isSome := by
  decide

/-- The cut lemma of the jump-table load `0x80000574`: region 4 is the table word. -/
theorem cut_table (d : CutData) (hpc : d.pc ≠ entry) (hs : d.site = none)
    (hx : d.shape.extra = [⟨some 8, 1, false⟩]) (hfine : d.shape.Fine = true)
    (hp : d.pc = 0x80000574) : CutOK vcPlan (mkCut d) := by
  intro σ m hA
  simp only [mkCut, if_neg hpc, ACut, hs, reduceCtorEq, false_and, exists_false,
    or_false] at hA
  obtain ⟨-, hpcm, hc, hsh, -, -, hex, -⟩ := hA
  have hpre := hc.2.1
  have h10 : m.reg 10 = w (0x80110050 + 8 * σ.t) := by simpa [Extra, hp] using hex
  have ht : σ.t ≤ 4 := hpre.2.2.2.2.2.2.2.2.2.1
  have h10n : (m.reg 10).toNat = 0x80110050 + 8 * σ.t := by
    rw [h10]; simp only [w, BitVec.toNat_ofNat]; omega
  have hok : RegionOk ((m.reg 10, (some 8 : Option Nat).getD 0), ⟨some 8, 1, false⟩) := by
    simp [RegionOk, Machine.readable, Machine.inRange, h10n, Layout.rodataLo, Layout.rodataHi,
      Nat.mod_one]
    omega
  have hap : ∀ p ∈ (shapeFull σ).map (·.1), PDisjoint p (m.reg 10, (some 8 : Option Nat).getD 0) := by
    have hfr := fr_toNat hpre
    have hsp := pre_sp hpre
    obtain ⟨-, -, -, hres, -, hao, -, -, -, -, hin, -⟩ := hpre
    unfold RamRange at hres hao
    unfold TX.InputArea RamRange at hin
    intro p hp' j hj j' hj' he
    simp only [shapeFull, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hp'
    simp only [Option.getD_some, h10n] at hj' he
    rcases hp' with rfl | rfl | rfl | rfl <;> simp only at hj he <;>
      simp only [Sig.res, Sig.ao, Sig.inp, Sig.len, Sig.S] at * <;>
      unfold Layout.ramLo Layout.ramHi Layout.inputLo Layout.inputHi frameBytes stackBytes
        TX.stackBytes at * <;> omega
  have hpres : Present m (m.reg 10) 8 := fun j hj => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (table_rodata σ.t (by omega) j hj)
    have := hc.2.2.1 _ _ hb
    rw [show m.reg 10 + BitVec.ofNat 64 j = BitVec.ofNat 64 (0x80110050 + 8 * σ.t + j) by
      rw [h10]; simp only [w]; rw [BitVec.ofNat_add (0x80110050 + 8 * σ.t) j]]
    rw [this]; rfl
  have hwf := wf_slot hpre m hx hok hap
  exact ⟨hwf, match_gen hc.avail hsh (by simp [hx]) (by simpa [hx] using hpres) hfine,
    hc.2.2.1, hpcm⟩

end ZesuExec.Fn.DTF
