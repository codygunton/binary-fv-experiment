import ZesuExec.Fn.TX.Grow

/-!
# TX: the entry store and the success exit (programme plan S6 step 6, third hand)

`0x80000460` stores the finished entry `{kp', |keys|, address, padding}` into slot `|done|` of
the entries buffer and advances the outer walk past the entry: back to the loop head
`0x800000c4`, or to `toOwnedSlice` of the entries list when the payload is walked.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## The walk past a finished entry -/

theorem walked_step {σ : Sig} {m : Machine} {o : Obs} {k : Kobs} (hok : OuterOk σ m o)
    (hEO : EntryOk σ m o k) (hAO : AddrOk σ m o k) (hKLO : KeysListOk σ o k)
    (hkw : KeysWalked (kpl σ o k) k.kl k.keys) :
    OuterWalked (pl σ o) (o.i + (k.eh + k.el)) (o.done ++ [entryValue σ o k]) := by
  obtain ⟨hil, heq, hfit⟩ := hok.2.2.2.2
  have hd : F2.decode (win σ o) = .success true k.eh k.el := hEO.1
  have hne : win σ o ≠ [] := by intro h; rw [h] at hd; simp [F2.decode] at hd
  have hkw2 : (keysWalk (kpl σ o k).length (kpl σ o k)).2 = some k.keys := by
    obtain ⟨-, he, -⟩ := hkw
    rw [he, List.drop_eq_nil_of_le (by simp [kpl, itemPayload]; omega)]
    simp [keysWalk]
  have hr : (entryWalk (itemPayload (win σ o) k.eh k.el)).2 = some (entryValue σ o k) := by
    show (entryWalk (ent σ o k)).2 = _
    simp only [entryWalk, hAO.1, if_true]
    rw [show itemRest (ent σ o k) k.ah 20 = aft σ o k from rfl, hKLO.1]
    simp only [show itemPayload (aft σ o k) k.kh k.kl = kpl σ o k from rfl, hkw2]
    rfl
  have hfw : WalkFits (win σ o) := hfit
  obtain ⟨hfit', hstep⟩ := walkFits_tail hfw hne hd hr
  obtain ⟨hrest, -⟩ := fits_rest (walkFits_head hfw hne) hd
  have hle := fits_le (walkFits_head hfw hne) hd
  have hwl : (win σ o).length = (pl σ o).length - o.i := List.length_drop ..
  have hdrop : itemRest (win σ o) k.eh k.el = (pl σ o).drop (o.i + (k.eh + k.el)) := by
    rw [hrest]; simp only [win, List.drop_drop]
  refine ⟨by omega, ?_, by rw [← hdrop]; exact hfit'⟩
  rw [heq]
  change ((entriesWalk (win σ o).length (win σ o)).2).map (o.done ++ ·) = _
  rw [hstep, hdrop, Option.map_map]
  congr 1; funext x; simp

/-! ## The slot store -/

/-- A store leaf writes only its `n`-byte slot. -/
theorem slot_so {σ : Sig} {m m' : Machine} {S S' : SState} {n : Nat} (hc : Common σ m)
    (hS : S.regions = baseRegions ++ [slotR n])
    (hm' : Match (envS n σ m) S' m') (hS' : S'.regions = baseRegions ++ [slotR n])
    (hfr : SameOutside (InWritable (envS n σ m) S) m m')
    (hall : S'.mem.all (fun w => w.r == 5) = true) (hram : RamRange (m.reg 10) n) :
    SameOutside (InRange (m.reg 10) n) m m' := by
  intro a ha
  by_cases hw : InWritable (envS n σ m) S a
  · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
    have hr6 : r < 6 := by
      have := (List.getElem?_eq_some_iff.mp hR).1
      rw [hS] at this; simpa [baseRegions] using this
    rcases Nat.lt_or_ge r 5 with h5 | h5
    · have hp := common_present hc r j h5 (by rwa [← envS_size (n := n) h5])
      rw [← envS_base (n := n) h5] at hp
      refine byte_keep hm' (by rw [hS']; simp [baseRegions]; omega) hj (fun w hw => ?_)
        (mem0_entry hp)
      have := List.all_eq_true.mp hall w hw
      simp only [beq_iff_eq] at this
      simp only [Write.covers, this, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        decide_eq_false_iff_not]
      omega
    · obtain rfl : r = 5 := by omega
      exfalso; apply ha
      have hb : (envS n σ m).base 5 = m.reg 10 := rfl
      have hs : (envS n σ m).size 5 = n := rfl
      rw [hb]; rw [hs] at hj
      unfold RamRange Layout.ramHi at hram
      exact in_self (by omega) hj
  · exact hfr a hw

theorem bytesAt_append {m : Machine} {a : Word} {xs ys : List Byte} (h1 : BytesAt m a xs)
    (h2 : BytesAt m (a + w xs.length) ys) : BytesAt m a (xs ++ ys) := fun i hi => by
  rcases Nat.lt_or_ge i xs.length with h | h
  · rw [List.getElem_append_left h]; exact h1 i h
  · rw [List.getElem_append_right h]
    have := h2 (i - xs.length) (by simp at hi; omega)
    rwa [show a + w xs.length + BitVec.ofNat 64 (i - xs.length) = a + BitVec.ofNat 64 i by
      simp only [w, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega] at this

theorem entriesBytes_snoc (es : List EntryValue) (is : List EntryImage) (e : EntryValue)
    (i : EntryImage) (h : is.length = es.length) :
    entriesBytes (es ++ [e]) (is ++ [i]) = entriesBytes es is ++ entryBytes e i := by
  simp [entriesBytes, List.zipWith_append, h]

theorem keysBlocks_snoc (es : List EntryValue) (is : List EntryImage) (e : EntryValue)
    (i : EntryImage) (h : is.length = es.length) :
    keysBlocks (es ++ [e]) (is ++ [i]) = keysBlocks es is ++
      (if e.keys = [] then [] else [(i.keysPtr, keySize * e.keys.length)]) := by
  unfold keysBlocks
  rw [List.zip_append (by omega), List.filterMap_append]
  congr 1
  by_cases he : e.keys = [] <;> simp [he]

theorem wordBytes_get (v : Word) (u : Nat) (hu : u < (wordBytes v).length) :
    (wordBytes v)[u] = byteOf v u := by
  simp [wordBytes]

/-- Bytes laid out one list after another. -/
theorem bytes_cat {m : Machine} {s : Word} {k : Nat} {xs ys : List Byte}
    (h1 : ∀ i (h : i < xs.length), m.mem (s + BitVec.ofNat 64 (k + i)) = some xs[i])
    (h2 : ∀ i (h : i < ys.length), m.mem (s + BitVec.ofNat 64 (k + xs.length + i)) = some ys[i]) :
    ∀ i (h : i < (xs ++ ys).length), m.mem (s + BitVec.ofNat 64 (k + i)) = some (xs ++ ys)[i] := by
  intro i hi
  rcases Nat.lt_or_ge i xs.length with h | h
  · rw [List.getElem_append_left h]; exact h1 i h
  · rw [List.getElem_append_right h]
    have := h2 (i - xs.length) (by simp at hi; omega)
    rwa [show k + xs.length + (i - xs.length) = k + i by omega] at this

theorem envS_var (n : Nat) (σ : Sig) (m : Machine) (i : Fin 32) :
    (Sym.var i.val).eval (envS n σ m) = m.reg i := by
  simp [Sym.eval, envS, entryEnv]

/-- The state after the entry store `0x80000460`, on both of its leaves: the entry is the last
of the entries list and the outer cursor is past it. -/
theorem after460 {σ : Sig} {m m' : Machine} {S' : SState} (hA : AEntryStore σ m)
    (hm' : Match (envS entrySize σ m) S' m') (hS' : S'.regions = baseRegions ++ [slotR 40])
    (hfr : SameOutside (InWritable (envS entrySize σ m) S460) m m')
    (hall : S'.mem.all (fun w => w.r == 5) = true) (hpad : ∀ wr ∈ S'.mem, wr.off + wr.n ≤ 36)
    (hw : readConst S' 5 0 8 = .var 14 ∧ readConst S' 5 8 8 = .var 15 ∧
      readConst S' 5 16 8 = .init 0 416 8 ∧ readConst S' 5 24 8 = .init 0 424 8 ∧
      readConst S' 5 32 4 = .bytes (.sext 32 (.init 0 432 4)) 0 4)
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19, 24, 25, 27] : List (Fin 32)), S'.reg i.val = S460.reg i.val)
    (h20 : S'.reg 20 = .bin .add (.var 20) (.var 26))
    (h21 : S'.reg 21 = .bin .sub (.var 21) (.var 26)) :
    ∃ o L, Common σ m' ∧ OuterOk σ m' o ∧ EList σ m' o o.done.length ∧ Live σ m' L (EX o) ∧
      Consts m' ∧ m'.reg 20 = curPtr σ o ∧ m'.reg 21 = w (o.p - o.i) ∧ o.i ≤ o.p ∧
      o.p < 2 ^ 64 ∧ m'.load (σ.sl 0x1f0) 8 = some magic ∧
      (m'.reg 21).toNat = (m.reg 21).toNat - (m.reg 26).toNat := by
  obtain ⟨-, o, k, L, kp', hc, hok, ⟨r20, r21, hi, hmag⟩, ⟨c24, c25, c27⟩, hEL, hroom, hlive,
    hEO, hAO, hKLO, hkw, hram, hkb, hkeys, hB, h10, h14, h15⟩ := hA
  have hpre := hc.2.1
  have hk0 : 0 < o.ec.toNat := by omega
  have hEX : (o.ep, entrySize * o.ec.toNat) ∈ EX o := by simp [EX, hk0]
  have hbram := hEL.2.2.2.2.2.1 hk0
  have hcapb : entrySize * o.done.length + entrySize ≤ entrySize * o.ec.toNat := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hroom
  obtain ⟨hpriv, hramS, hpresS⟩ := slot_of_block hlive (p := o.ep)
    (sz := entrySize * o.ec.toNat) (off := entrySize * o.done.length) (n := entrySize)
    (List.mem_append_left _ hEX) hbram hcapb h10
  have hwf : Env.WF (envS entrySize σ m) S460 := (slot_ok hc hpriv hramS hpresS).1
  have hm0 : Match (envS entrySize σ m) S460 m := (slot_ok hc hpriv hramS hpresS).2.1
  have hreg : ∀ i ∈ ([2, 8, 9, 18, 19, 24, 25, 27] : List (Fin 32)), m'.reg i = m.reg i :=
    fun i hi => by rw [Match.reg_eq hm' i i.val rfl, hr i hi, ← Match.reg_eq hm0 i i.val rfl]
  have reg : ∀ (i : Fin 32) (s : Sym), S'.reg i.val = s →
      m'.reg i = s.eval (envS entrySize σ m) := fun i s h => by
    rw [Match.reg_eq hm' i i.val rfl, h]
  have hwf' : Env.WF (envS entrySize σ m) S' := hwf.congr (by rw [hS']; rfl)
  have hso := slot_so hc rfl hm' hS' hfr hall hramS
  have hp : Preserved m m' := F1.preserved_of_leaf hwf hm' (by rw [hS']; decide) hfr
  have hbram' := hbram
  unfold RamRange Layout.ramHi at hbram
  have h10n : (m.reg 10).toNat = o.ep.toNat + entrySize * o.done.length := by
    rw [h10]; exact toNat_add_ofNat (by omega)
  have hinB : ∀ a, InRange (m.reg 10) entrySize a →
      InRange o.ep (entrySize * o.ec.toNat) a := fun a ha => by unfold InRange at ha ⊢; omega
  have hsP : ∀ a, InRange (m.reg 10) entrySize a → σ.A.Priv σ.g.L a := fun a ha =>
    (hlive.2.2 _ (List.mem_append_left _ hEX)).2.2 a (hinB a ha)
  have hc' : Common σ m' := common_keep hc (fun i hi => hreg i (by simp at hi ⊢; omega)) hp hso
    fun a ha => ⟨.inr (hsP a ha), fun hs => stack_not_priv hpre (save_in_stack hpre hs) (hsP a ha)⟩
  have hfs : ∀ kk, kk ≤ 576 → ∀ t < kk,
      m'.mem (σ.sl kk + BitVec.ofNat 64 t) = m.mem (σ.sl kk + BitVec.ofNat 64 t) := by
    intro kk hkk t ht
    have h3 := sl_toNat hpre (k := kk) (by unfold stackBytes; omega)
    have hS := (entry_nums hpre).2.1; unfold Layout.ramHi at hS
    refine hso _ fun hin => stack_not_priv hpre (sl_in_stack hpre (k := kk) (n := kk)
      (by unfold stackBytes; omega) (Nat.le_refl _) (in_self (by rw [h3]; omega) ht)) (hsP _ hin)
  have hlive2 : Live σ m L ([(o.ep, entrySize * o.ec.toNat)] ++
      (keysBlocks o.done o.is ++ KD k kp')) := by
    rw [show [(o.ep, entrySize * o.ec.toNat)] ++ (keysBlocks o.done o.is ++ KD k kp') =
      EX o ++ KD k kp' by simp [EX, hk0]]
    exact hlive
  have hbs : ∀ b ∈ keysBlocks o.done o.is ++ KD k kp', ∀ t < b.2,
      m'.mem (b.1 + BitVec.ofNat 64 t) = m.mem (b.1 + BitVec.ofNat 64 t) := by
    intro b hb t ht
    have hr := (hlive2.2.2 b (List.mem_append_right _ hb)).2.1
    unfold RamRange Layout.ramHi at hr
    refine hso _ fun hin => ?_
    have h1 := in_self (a := b.1) (by omega) ht
    have h2 := hinB _ hin
    have := live_apart hlive2 (List.mem_singleton_self _) hb
    dsimp only at this
    simp only [InRange] at h1 h2; omega
  have hL : (o.ep, entrySize * o.ec.toNat) ∈ L :=
    hlive.2.1.symm.subset (List.mem_append_right _ (List.mem_append_left _ hEX))
  have hheap : σ.A.Heap L m' := σ.A.heap_frame' L m m' hlive.1
    (fun a hPa => hso a fun hin => σ.A.priv_not_live L a hPa ⟨_, hL, hinB a hin⟩) hp
  -- the bytes of the slot
  have sb : ∀ off n, n ≤ 8 → off + n ≤ 40 → ∀ u < n,
      m'.mem (m.reg 10 + BitVec.ofNat 64 (off + u)) =
        some (byteOf ((readConst S' 5 off n).eval (envS entrySize σ m)) u) := by
    intro off n hn ho u hu
    have l := load_cst hwf' hm' (r := 5) (R := slotR 40) (off := off) (n := n) (by rw [hS']; rfl)
      (by show off + n ≤ entrySize; unfold entrySize; omega)
    have b := load_bytes l hn u hu
    rwa [show (envS entrySize σ m).base 5 + BitVec.ofNat 64 off + BitVec.ofNat 64 u =
      m.reg 10 + BitVec.ofNat 64 (off + u) by
        show m.reg 10 + _ + _ = _; rw [BitVec.add_assoc, ← BitVec.ofNat_add]] at b
  obtain ⟨w0, w8, w16, w24, w32⟩ := hw
  have v14 : (Sym.var 14).eval (envS entrySize σ m) = m.reg 14 := envS_var _ σ m 14
  have v15 : (Sym.var 15).eval (envS entrySize σ m) = m.reg 15 := envS_var _ σ m 15
  have fb : ∀ j, j < 576 → some ((envS entrySize σ m).byte0 0 j) =
      m.mem (σ.sl 576 + BitVec.ofNat 64 j) := fun j hj => by
    rw [envS_byte0 (by decide)]; exact frame_byte0 hc hj
  let addr := itemPayload (ent σ o k) k.ah 20
  have hil : σ.input.length = σ.len := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hok2 := hok.2.1
  have hal : addr.length = 20 := by
    have := hAO.2.1; have := hEO.2.1; have := hi
    show (itemPayload (ent σ o k) k.ah 20).length = 20
    rw [itemPayload, ent_eq σ o k hEO.2.1]
    simp only [List.length_take, List.length_drop]; omega
  have pA : ∀ i (h : i < addr.length), m'.mem (m.reg 10 + BitVec.ofNat 64 (16 + i)) =
      some addr[i] := by
    intro i hi
    rw [hal] at hi
    rw [← hB i (by rw [hal]; exact hi)]
    rcases Nat.lt_or_ge i 8 with h8 | h8
    · rw [sb 16 8 (by decide) (by decide) i h8, w16]
      show some (byteOf (ofBytesLE (byteList ((envS entrySize σ m).byte0 0) 416 8)) i) = _
      rw [byteOf_byteList (by decide) h8, fb _ (by omega)]
      congr 1; simp only [Sig.sl, w]; bv_omega
    rcases Nat.lt_or_ge i 16 with h16 | h16
    · rw [show 16 + i = 24 + (i - 8) by omega, sb 24 8 (by decide) (by decide) _ (by omega), w24]
      show some (byteOf (ofBytesLE (byteList ((envS entrySize σ m).byte0 0) 424 8)) _) = _
      rw [byteOf_byteList (by decide) (by omega), fb _ (by omega)]
      congr 1; simp only [Sig.sl, w]; bv_omega
    · rw [show 16 + i = 32 + (i - 16) by omega, sb 32 4 (by decide) (by decide) _ (by omega), w32]
      show some (byteOf (ofBytesLE (byteList (byteOf ((((Sym.init 0 432 4).eval
        (envS entrySize σ m)).setWidth 32).signExtend 64)) 0 4)) _) = _
      rw [byteOf_byteList (by decide) (by omega), Nat.zero_add, byteOf_sext32 _ (by omega)]
      show some (byteOf (ofBytesLE (byteList ((envS entrySize σ m).byte0 0) 432 4)) _) = _
      rw [byteOf_byteList (by decide) (by omega), fb _ (by omega)]
      congr 1; simp only [Sig.sl, w]; bv_omega
  let pad : List Byte := (List.range 4).map fun j => (m.mem (m.reg 10 + BitVec.ofNat 64 (36 + j))).getD 0
  have pP : ∀ i (h : i < pad.length), m'.mem (m.reg 10 + BitVec.ofNat 64 (36 + i)) =
      some pad[i] := by
    intro i hi
    have hi4 : i < 4 := by simpa [pad] using hi
    have hk := byte_keep hm' (r := 5) (j := 36 + i) (by rw [hS']; simp [baseRegions])
      (by show 36 + i < entrySize; unfold entrySize; omega) (fun wr hwr => by
        have := hpad wr hwr
        simp only [Write.covers, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
      (mem0_entry (hpresS (36 + i) (by unfold entrySize; omega)))
    rw [show (envS entrySize σ m).base 5 = m.reg 10 from rfl] at hk
    rw [hk]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hpresS (36 + i) (by unfold entrySize; omega))
    simp [pad, hb]
  -- the new entries list
  let v : EntryValue := entryValue σ o k
  let img : EntryImage := ⟨kp', pad⟩
  have hentry : ∀ i (h : i < (entryBytes v img).length),
      m'.mem (m.reg 10 + BitVec.ofNat 64 (0 + i)) = some (entryBytes v img)[i] := by
    refine bytes_cat (bytes_cat (bytes_cat (fun i h => ?_) (fun i h => ?_)) ?_) ?_
    · have h8 : i < 8 := by simpa [wordBytes] using h
      rw [sb 0 8 (by decide) (by decide) i h8, w0, v14, h14, wordBytes_get]
    · have h8 : i < 8 := by simpa [wordBytes] using h
      rw [show 0 + (wordBytes img.keysPtr).length + i = 8 + i by simp [wordBytes],
        sb 8 8 (by decide) (by decide) i h8, w8, v15, h15, wordBytes_get]; rfl
    · intro i h
      rw [show 0 + (wordBytes img.keysPtr ++ wordBytes (BitVec.ofNat 64 v.keys.length)).length + i
        = 16 + i by simp [wordBytes]]
      exact pA i h
    · intro i h
      have hva : v.address.length = 20 := hal
      rw [show 0 + (wordBytes img.keysPtr ++ wordBytes (BitVec.ofNat 64 v.keys.length) ++
        v.address).length + i = 36 + i by simp [wordBytes, hva]]
      exact pP i h
  have hil' := hEL.2.2.2.2.2.2.1
  have hz := hEL.2.2.2.2.2.2.2.2
  have hlenOld := entriesBytes_length o.done o.is hil' fun x hx => ⟨(hz x hx).1, (hz x hx).2.1⟩
  let o' : Obs := { o with i := o.i + (k.eh + k.el), done := o.done ++ [v], is := o.is ++ [img] }
  have hEX' : EX o' = EX o ++ KD k kp' := by
    simp only [EX, o', keysBlocks_snoc _ _ _ _ hil', List.append_assoc, KD, v, img, entryValue]
  have hBy : BytesAt m' o.ep (entriesBytes (o.done ++ [v]) (o.is ++ [img])) := by
    rw [entriesBytes_snoc _ _ _ _ hil']
    have := bytes_cat (m := m') (s := o.ep) (k := 0) (xs := entriesBytes o.done o.is)
      (ys := entryBytes v img) (fun i h => by
        rw [Nat.zero_add]
        refine (hso _ fun hin => ?_).trans (hEL.2.2.2.2.2.2.2.1 i h)
        rw [hlenOld] at h
        unfold InRange at hin
        rw [toNat_add_ofNat (by omega)] at hin
        omega) (fun i h => by
        rw [Nat.zero_add, hlenOld, show o.ep + BitVec.ofNat 64 (entrySize * o.done.length + i) =
          m.reg 10 + BitVec.ofNat 64 (0 + i) by rw [h10]; simp only [w]; bv_omega]
        exact hentry i h)
    intro i hi
    have := this i hi
    rwa [Nat.zero_add] at this
  have hrestB : ∀ t < 16, m'.mem (σ.rest + BitVec.ofNat 64 t) = m.mem (σ.rest + BitVec.ofNat 64 t) :=
    fun t ht => hso _ fun hin => by
      have hfit := pre_fit hpre ((σ.rest, 16), restR) (by simp [shapeFull])
      exact owned_not_priv hpre (.inr (.inl (in_self (by simpa using hfit) ht))) (hsP _ hin)
  have hOK := outer_bytes hok hrestB
  have hW := walked_step hok hEO hAO hKLO hkw
  have hlenNew : (o.done ++ [v]).length = o.done.length + 1 := by simp
  have hEL' : EList σ m' o' o'.done.length := by
    obtain ⟨hH, -, hp0, hc0, hc32, hram', -, -, -⟩ := hEL
    refine ⟨?_, by show (o.done ++ [v]).length ≤ _; rw [hlenNew]; exact hroom, hp0, hc0, hc32,
      hram', by simp [o', hil'], hBy, fun x hx => ?_⟩
    · show F1.HeaderIs m' (σ.sl 0x1c0) o.ep (w (o.done ++ [v]).length) o.ec
      rw [hlenNew]; exact hdr_congr hH fun t ht => hfs 0x1c0 (by decide) t (by omega)
    · have hx' : x ∈ List.zip o.done o.is ++ [(v, img)] := by
        change x ∈ List.zip (o.done ++ [v]) (o.is ++ [img]) at hx
        rw [List.zip_append (by simp [hil'])] at hx; simpa using hx
      rcases List.mem_append.mp hx' with hx | hx
      · obtain ⟨hpd, had', hkl', hkram, hkb'⟩ := hz x hx
        refine ⟨hpd, had', hkl', hkram, ?_⟩
        by_cases hk : x.1.keys = []
        · rw [hk]; intro i hi; simp at hi
        · exact bytes_congr hkb' fun t ht => hbs _ (List.mem_append_left _ (mem_keysBlocks hx hk))
            t (by rw [flatten_length _ hkl'] at ht; exact ht)
      · rw [List.mem_singleton] at hx; subst hx
        refine ⟨by simp [img, pad], hal, hkeys, hram, ?_⟩
        by_cases hk : k.keys = []
        · show BytesAt m' kp' k.keys.flatten
          rw [hk]; intro i hi; simp at hi
        · exact bytes_congr hkb fun t ht => hbs (kp', keySize * k.keys.length)
            (List.mem_append_right _ (by simp [KD, hk])) t
            (by dsimp only; rw [← flatten_length _ hkeys]; exact ht)
  have hlen64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hp64 : o.p < 2 ^ 64 := by have := hok.2.1; omega
  have e21 : m'.reg 21 = w (o.p - (o.i + (k.eh + k.el))) := by
    rw [reg 21 _ h21]
    show (Sym.var 21).eval (envS entrySize σ m) - (Sym.var 26).eval (envS entrySize σ m) = _
    rw [show (Sym.var 21).eval (envS entrySize σ m) = m.reg 21 from envS_var _ σ m 21,
      show (Sym.var 26).eval (envS entrySize σ m) = m.reg 26 from envS_var _ σ m 26, r21, hEO.2.2]
    apply BitVec.eq_of_toNat_eq
    simp only [w, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := hEO.2.1
    omega
  have hle := hEO.2.1
  refine ⟨o', L, hc', ⟨hOK.1, hOK.2.1, hOK.2.2.1, hOK.2.2.2.1, hW⟩, hEL',
    ⟨hheap, by rw [hEX']; exact hlive.2.1, by rw [hEX']; exact hlive.2.2⟩,
    ⟨(hreg 24 (by simp)).trans c24, (hreg 25 (by simp)).trans c25,
      (hreg 27 (by simp)).trans c27⟩, ?_, e21, by show o.i + (k.eh + k.el) ≤ o.p; omega,
    by show o.p < 2 ^ 64; omega,
    (load_congr fun t ht => hfs 0x1f0 (by decide) t (by omega)).trans hmag, ?_⟩
  · rw [reg 20 _ h20]
    show (Sym.var 20).eval (envS entrySize σ m) + (Sym.var 26).eval (envS entrySize σ m) = _
    rw [show (Sym.var 20).eval (envS entrySize σ m) = m.reg 20 from envS_var _ σ m 20,
      show (Sym.var 26).eval (envS entrySize σ m) = m.reg 26 from envS_var _ σ m 26, r20, hEO.2.2]
    show σ.inp + w (o.h + o.i) + w (k.eh + k.el) = σ.inp + w (o.h + (o.i + (k.eh + k.el)))
    simp only [w, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  · rw [e21, r21, hEO.2.2]; simp only [w, BitVec.toNat_ofNat]; omega

theorem TX.leaf_80000460_0 :
    LeafGoal TX.plan TX.plan.cuts[15]! ((TX.plan.leaves 0x80000460)[0]!) := by
  show LeafGoal TX.plan cut460 (run460_leaves[0]!)
  have hcs : (run460_leaves[0]!).conds =
      [SBool.ne (Sym.bin .sub (Sym.var 21) (Sym.var 26)) (Sym.lit 0)] := by decide
  have hsteps : (run460_leaves[0]!).S.steps - cut460.S.steps = 11 := by decide
  intro σ m hA hc
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run460_leaves[0]!).exit = .at 0x800000c4 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800000c4 at hex
  change Match (envS entrySize σ m) _ m' at hm'
  change SameOutside (InWritable (envS entrySize σ m) S460) m m' at hfr
  have h1 : SBool.eval (envS entrySize σ m)
      (SBool.ne (Sym.bin .sub (Sym.var 21) (Sym.var 26)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  obtain ⟨o, L, hc', hok, hEL, hlive, hC, r20, r21, hip, hp64, hmag, hb21⟩ := after460 hA hm'
    (by decide) hfr (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
  have e21 : m'.reg 21 = (Sym.bin .sub (Sym.var 21) (Sym.var 26)).eval (envS entrySize σ m) := by
    rw [Match.reg_eq hm' 21 21 rfl,
      show (run460_leaves[0]!).S.reg 21 = .bin .sub (.var 21) (.var 26) by decide]
  have hlt : o.i < o.p := by
    rcases Nat.lt_or_ge o.i o.p with h | h
    · exact h
    · exfalso
      have h0 : m'.reg 21 = 0 := by rw [r21, show o.p - o.i = 0 by omega]; rfl
      rw [e21] at h0
      simp only [SBool.eval] at h1; rw [h0] at h1; simp [Sym.eval_lit] at h1
  refine ExitGoal.at_cut rfl ⟨cut0c4, by simp [TX.plan, vcPlan], hex,
    ⟨hex, o, L, hc', hok, ⟨r20, r21, hlt, hmag⟩, hC, hEL, hlive⟩, ?_⟩
  show bOuter m' ≤ bTail m 311 - _
  rw [hsteps]; unfold bOuter bTail outerLeft afterEntry; rw [hb21]; omega

theorem TX.leaf_80000460_1 :
    LeafGoal TX.plan TX.plan.cuts[15]! ((TX.plan.leaves 0x80000460)[1]!) := by
  show LeafGoal TX.plan cut460 (run460_leaves[1]!)
  have hcs : (run460_leaves[1]!).conds =
      [SBool.eq (Sym.bin .sub (Sym.var 21) (Sym.var 26)) (Sym.lit 0)] := by decide
  have hsteps : (run460_leaves[1]!).S.steps - cut460.S.steps = 16 := by decide
  intro σ m hA hc
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run460_leaves[1]!).exit = .call 0x800d6554 0x800004a0 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800d6554 at hex
  change Match (envS entrySize σ m) _ m' at hm'
  change SameOutside (InWritable (envS entrySize σ m) S460) m m' at hfr
  have h1 : SBool.eval (envS entrySize σ m)
      (SBool.eq (Sym.bin .sub (Sym.var 21) (Sym.var 26)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  obtain ⟨o, L, hc', hok, hEL, hlive, -, -, r21, hip, hp64, -, hb21⟩ := after460 hA hm'
    (by decide) hfr (by decide) (by decide)
    ⟨by decide, by decide, by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
  have hpre := hc'.2.1
  have reg : ∀ (i : Fin 32) (s : Sym), (run460_leaves[1]!).S.reg i.val = s →
      m'.reg i = s.eval (envS entrySize σ m) := fun i s h => by
    rw [Match.reg_eq hm' i i.val rfl, h]
  have e21 := reg 21 _ (by decide : (run460_leaves[1]!).S.reg 21 = .bin .sub (.var 21) (.var 26))
  have hip' : o.i = o.p := by
    have h0 : m'.reg 21 = 0 := by rw [e21]; simpa [SBool.eval] using h1
    rw [r21] at h0
    have := congrArg BitVec.toNat h0
    simp [w] at this
    omega
  have r1 := reg 1 _ (by decide : (run460_leaves[1]!).S.reg 1 = .lit 0x800004a0)
  have r10 := reg 10 _ (by decide : (run460_leaves[1]!).S.reg 10 = .ptr 0 440)
  have r11 := reg 11 _ (by decide : (run460_leaves[1]!).S.reg 11 = .ptr 0 128)
  have r12 := reg 12 _ (by decide : (run460_leaves[1]!).S.reg 12 = .ptr 3 0)
  simp only [Sym.eval, Env.base, envS, entryEnv, shapeOf, List.cons_append, List.getD_cons_zero,
    List.getD_cons_succ, Sig.sl, w, frameBytes] at r1 r10 r11 r12
  rw [show σ.S - 576#64 + BitVec.ofInt 64 440 = σ.sl 0x88 by simp only [Sig.sl, w]; bv_omega]
    at r10
  rw [show σ.S - 576#64 + BitVec.ofInt 64 128 = σ.sl 0x1c0 by simp only [Sig.sl, w]; bv_omega]
    at r11
  rw [show σ.ao + BitVec.ofInt 64 0 = σ.ao by simp] at r12
  have hra : RetAligned m' := by unfold RetAligned; rw [r1]; decide
  obtain ⟨hH, hle, hp0, hc0, hc32, hram, hil, hby, hz⟩ := hEL
  have hn : (w o.done.length).toNat = o.done.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have hlenB := entriesBytes_length o.done o.is hil fun x hx => ⟨(hz x hx).1, (hz x hx).2.1⟩
  have hpre2 : F5.Pre σ.A L (entriesBytes o.done o.is) m' :=
    towned_pre hc' hlive r10 r11 r12 hra (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hH (by rw [hn]; exact hle)
      (by rw [hlenB, hn]; simp only [entrySize, F5.elemBytes]; omega) hp0
      (fun h0 => ⟨by rw [show o.ec.toNat * F5.elemBytes = entrySize * o.ec.toNat by
          simp only [F5.elemBytes, entrySize]; omega]; exact hram h0,
        by rw [show o.ec.toNat * F5.elemBytes = entrySize * o.ec.toNat by
          simp only [F5.elemBytes, entrySize]; omega]; simp [EX, h0]⟩) hby
  have hsite : Site49c σ (L, entriesBytes o.done o.is) m' := ⟨o, hc', hok, hip',
    ⟨hH, hle, hp0, hc0, hc32, hram, hil, hby, hz⟩, hlive, rfl, by rw [r1]; rfl, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      · exact r10
      · exact r11
      · exact r12⟩
  refine ⟨f5C, (L, entriesBytes o.done o.is), rfl, hex, hpre2, fun m'' hpost =>
    ⟨cut4a0, by simp [TX.plan, vcPlan], rfl, ?_, ⟨m', _, hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1, r1]; decide
  · show F5.bound + 23 ≤ bTail m 311 - _
    rw [hsteps]; unfold bTail F5.bound; omega

end ZesuExec.Fn.TX
