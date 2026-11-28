import ZesuExec.Fn.DTF.Hand
import ZesuExec.Fn.DTF.Leaves
import ZesuExec.Fn.DTF.Bridge

/-!
# DTF: the `txHashList` loop (arm 3, programme plan S7 step 4)

The loop over top-level item 10's payload (`0x800020ac..0x80002168`): `decodeItem` on the cursor
`s7`/`s6`, a 32-byte string, `ensureTotalCapacity(S-0x118, ao, n + 1)` (F1), the store into the
slot `p + 32 n` (`0x80002138`), and `toOwnedSlice` (F4) once the payload is used up. Its state is
`HashLoop`/`HashItem` (`Cuts.lean`); the leaves are `leaf_at_x`/`leaf_call_x` instances whose
hypotheses carry that state from the source's assertion to the target's.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## What a leaf keeps -/

/-- A register the leaf leaves as the source had it. -/
theorem ctx_reg {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {i i' : Nat} (hi : i < 32) (hi' : i' < 32) (h : l.S.reg i = d.shape.S.reg i') :
    m'.reg (Fin.ofNat 32 i) = m.reg (Fin.ofNat 32 i') := by
  rw [reg_eval C.hm' hi, reg_eval C.hm hi', h]

/-- A frame word the leaf leaves as the source had it. -/
theorem ctx_slot {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {o : Nat} (ho : o + 8 ≤ frameBytes) (h : (Loc.slot o).sym l.S = (Loc.slot o).sym d.shape.S) :
    TX.wordAt m' (σ.fr + w o) = TX.wordAt m (σ.fr + w o) := by
  have e' := loc_word_eval C.wf' C.hm' C.hS' (loc := .slot o) (by simp [Loc.fine]; omega)
  have e := loc_word_eval C.wf C.hm C.hS (loc := .slot o) (by simp [Loc.fine]; omega)
  simp only [Loc.word] at e e'
  rw [e', h, ← e]

theorem ctx_common {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m') :
    Common σ m' :=
  common_leaf C.F.common C.wf C.hS C.hS' C.hm' C.so C.low

theorem ctx_preserved {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m') :
    Preserved m m' :=
  F1.preserved_of_leaf C.wf C.hm' (Nat.le_of_eq (congrArg List.length
    ((show d.shape.S.regions = baseRegions from C.hS).trans
      (show l.S.regions = baseRegions from C.hS').symm))) C.so

theorem ctx_live {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {L X : List (Word × Nat)} (h : Live σ m L X) : Live σ m' L X := by
  have hpre := C.F.common.2.1
  exact live_keep h C.so (ctx_preserved C) fun a ha hP =>
    owned_not_priv hpre (inWritable_owned hpre C.hS ha).1 (priv_sub hpre h hP)

/-- A frame word's load the leaf leaves as the source had it. -/
theorem ctx_load {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {o : Nat} (ho : o + 8 ≤ frameBytes) (h : (Loc.slot o).sym l.S = (Loc.slot o).sym d.shape.S) :
    m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8 := by
  rw [frame_load (ctx_common C).avail ho, frame_load C.F.common.avail ho, ctx_slot C ho h]

theorem hdr_keep {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {o n r : Nat} (ho : o + 24 ≤ frameBytes)
    (h0 : (Loc.slot o).sym l.S = (Loc.slot o).sym d.shape.S)
    (h8 : (Loc.slot (o + 8)).sym l.S = (Loc.slot (o + 8)).sym d.shape.S)
    (h16 : (Loc.slot (o + 16)).sym l.S = (Loc.slot (o + 16)).sym d.shape.S)
    (hh : ListHdr σ m o n r) : ListHdr σ m' o n r := by
  obtain ⟨p, cap, l0, l8, l16, hnr, hp, L, X, hlive, hb⟩ := hh
  refine ⟨p, cap, ?_, ?_, ?_, hnr, hp, L, X, ctx_live C hlive, hb⟩
  · rw [ctx_load C (by omega) h0]; exact l0
  · rw [ctx_load C (by omega) h8]; exact l8
  · rw [ctx_load C (by omega) h16]; exact l16

/-! ## `decodeItem` on the list cursor -/

/-- `decodeItem`'s precondition on `n` payload bytes from `inp + c` (the list cursor). -/
theorem f2_pre_cur {σ : Sig} {m : Machine} (hc : Common σ m) {ko c n : Nat}
    (hsp : m.reg 2 = σ.fr + w 0) (hout : m.reg 10 = σ.fr + w ko) (hko : ko + 40 + 104 ≤ frameBytes)
    (hko8 : ko % 8 = 0) (hin : m.reg 11 = σ.inp + w c) (hlen : m.reg 12 = w n)
    (hcl : c + n ≤ σ.len) (hra : RetAligned m) : F2.Pre m := by
  have hpre := hc.2.1
  have hav := hc.avail
  obtain ⟨hlo, hhi, hal⟩ := pre_sp hpre
  have hF : σ.fr.toNat = σ.S.toNat - frameBytes := fr_toNat hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hia, -, -, -, -, -, -, -, -, -, -, hfi, -⟩ := hpre
  have h2 : (σ.S - w stackBytes).toNat = σ.S.toNat - stackBytes :=
    S_sub_toNat hc.2.1 (Nat.le_refl _)
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hia' : (Layout.inputLo ≤ σ.inp.toNat ∧ σ.inp.toNat + σ.len ≤ Layout.inputHi) ∨
      (Layout.ramLo ≤ σ.inp.toNat ∧ σ.inp.toNat + σ.len ≤ Layout.ramHi) := hia
  have hfi' : σ.S.toNat - stackBytes + stackBytes ≤ σ.inp.toNat ∨
      σ.inp.toNat + σ.len ≤ σ.S.toNat - stackBytes := by
    unfold TX.Apart at hfi; rw [← h2]; exact hfi
  clear hia hfi
  have hsp0 : (m.reg 2).toNat = σ.fr.toNat := by rw [hsp]; simp [w]
  have hio : (m.reg 11).toNat = σ.inp.toNat + c := by
    rw [hin]; exact toNat_add_ofNat (by
      unfold Layout.inputHi Layout.ramHi at hia'; omega)
  have hfrk : (m.reg 10).toNat = σ.fr.toNat + ko := by
    rw [hout]; exact toNat_add_ofNat (by unfold Layout.ramHi frameBytes at *; omega)
  have hl12 : (m.reg 12).toNat = n := by
    rw [hlen]; simp only [w, BitVec.toNat_ofNat]; omega
  have hsub : (m.reg 2 - 16).toNat = σ.fr.toNat - 16 := by
    rw [BitVec.toNat_sub, hsp0]
    rw [show (16 : Word).toNat = 16 from rfl]
    unfold Layout.ramLo stackBytes TX.stackBytes frameBytes at *; omega
  refine ⟨hc.2.2.1, stack16 hc hsp, hra, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hio, hl12]
    simp only [Machine.readable, Machine.inRange, Layout.rodataLo, Layout.rodataHi,
      Layout.inputLo, Layout.inputHi, Layout.ramLo, Layout.ramHi, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq]
    unfold Layout.inputLo Layout.inputHi Layout.ramLo Layout.ramHi at hia'
    omega
  · intro j hj
    rw [hl12] at hj
    have := input_present hav (j := c + j) (by omega)
    rwa [hin, show σ.inp + w c + BitVec.ofNat 64 j = σ.inp + BitVec.ofNat 64 (c + j) by
      simp only [w]; rw [F1.add_add_ofNat]]
  · rw [hfrk]
    simp only [Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi,
      Bool.and_eq_true, decide_eq_true_eq]
    unfold Layout.ramLo Layout.ramHi stackBytes TX.stackBytes frameBytes at *; omega
  · rw [hfrk, hF]; unfold frameBytes at *; omega
  · intro j hj
    rw [hout, show σ.fr + w ko + BitVec.ofNat 64 j = σ.fr + BitVec.ofNat 64 (ko + j) by
      simp only [w]; rw [F1.add_add_ofNat]]
    exact stack_present hav (by unfold frameBytes at *; omega)
  · unfold Fn.Disjoint; simp only; rw [hio, hfrk, hl12, hF]
    unfold stackBytes TX.stackBytes frameBytes at *; omega
  · unfold Fn.Disjoint; simp only; rw [hio, hl12, hsub, hF]
    unfold stackBytes TX.stackBytes frameBytes at *; omega
  · have h16 : 16 ≤ σ.fr.toNat := by
      rw [hF]; simp only [Layout.ramLo, stackBytes, TX.stackBytes, frameBytes] at hlo ⊢; omega
    unfold Fn.Disjoint; simp only; rw [hfrk, hsub]; omega

/-- The list item's payload lies in the payload: `c + h + p ≤ len`. -/
theorem hashList_le {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (h3 : σ.t = 3) {c h p : Nat}
    (hl : HashList σ c h p) : c + h + p ≤ σ.len := by
  obtain ⟨hs, hd⟩ := hl
  have hf := fit_of_arms hpre (arms := [3]) (.inr (by simp [h3])) (by decide) hs
  obtain ⟨-, hle, -⟩ := TX.fits_bounds hf hd
  rw [List.length_drop, payload_len hpre] at hle
  have := skip_le hs
  rw [payload_len hpre] at this
  omega

theorem hashesOk_zero (pl : List Byte) : HashesOk pl 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)

/-- One more 32-byte string at the cursor `j` after `n` items. -/
theorem hashesOk_succ {pl : List Byte} {n j h : Nat} (hok : HashesOk pl n)
    (hs : skip n pl = some j) (hd : F2.decode (pl.drop j) = .success false h 32) :
    HashesOk pl (n + 1) := by
  intro i hi c hc
  rcases Nat.lt_or_ge i n with hlt | hge
  · exact hok i hlt c hc
  · obtain rfl : i = n := by omega
    rw [hs, Option.some.injEq] at hc
    subst hc
    exact ⟨h, hd⟩

/-- `Fits`'s `inner` holds for the payload of a list item among the first `n`. -/
theorem fits_inner {inner : List Byte → Prop} : ∀ {k n : Nat} {b : List Byte} {c : Nat},
    ItemsFit inner n b → skip k b = some c → k < n → ∀ {h p : Nat},
    F2.decode (b.drop c) = .success true h p → inner (TX.itemPayload (b.drop c) h p)
  | 0, _ + 1, b, c, hf, hs, _, h, p, hd => by
    simp only [skip, Option.some.injEq] at hs; subst hs
    simp only [List.drop_zero] at hd ⊢
    simp only [ItemsFit, hd] at hf
    exact hf.2.1 trivial
  | k + 1, n + 1, b, c, hf, hs, hk, h, p, hd => by
    simp only [skip] at hs
    split at hs
    · next l h0 p0 hd0 =>
      obtain ⟨c', h', rfl⟩ := Option.map_eq_some_iff.mp hs
      simp only [ItemsFit, hd0] at hf
      have hd' : F2.decode ((TX.itemRest b h0 p0).drop c') = .success true h p := by
        rwa [TX.itemRest, List.drop_drop]
      have := fits_inner hf.2.2 h' (by omega) hd'
      rwa [TX.itemRest, List.drop_drop] at this
    · cases hs
  | _, 0, _, _, _, _, hk, _, _, _ => absurd hk (Nat.not_lt_zero _)

theorem walkList_nil {α : Type} (f : P α) (fuel : Nat) : walkList f fuel [] = some [] := by
  cases fuel <;> rfl

/-- One 32-byte string: `hash` reads it. -/
theorem hash_run {b : List Byte} {h : Nat} (hf : TX.HeaderFits b)
    (hd : F2.decode b = .success false h 32) :
    hash.run b = some (TX.itemPayload b h 32, TX.itemRest b h 32) := by
  simp only [hash, StateT.run_bind, bytesView_run hd, Option.bind_eq_bind, Option.bind_some,
    payload_length hf hd, if_true]
  rfl

/-- The walk over `n` 32-byte strings that fill `b` succeeds. -/
theorem walk_hash : ∀ (n : Nat) (b : List Byte) (fuel : Nat), n ≤ fuel →
    (∀ i < n, ∀ c, skip i b = some c → TX.HeaderFits (b.drop c)) → HashesOk b n →
    skip n b = some b.length → ∃ hs, walkList hash fuel b = some hs
  | 0, b, fuel, _, _, _, hs => by
    simp only [skip, Option.some.injEq] at hs
    rw [List.eq_nil_of_length_eq_zero hs.symm]
    exact ⟨[], walkList_nil _ _⟩
  | n + 1, b, fuel, hn, hfit, hok, hs => by
    obtain ⟨h, hd⟩ := hok 0 (by omega) 0 rfl
    simp only [List.drop_zero] at hd
    have hf := hfit 0 (by omega) 0 rfl
    simp only [List.drop_zero] at hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    cases b with
    | nil => simp [F2.decode] at hd
    | cons x xs =>
    have hrun := hash_run hf hd
    have hsk : ∀ i c, skip i (TX.itemRest (x :: xs) h 32) = some c →
        skip (i + 1) (x :: xs) = some (TX.itemConsumed h 32 + c) := by
      intro i c hc
      simp only [skip, hd]; rw [← TX.itemRest, hc]; rfl
    have hdrop : ∀ c, (TX.itemRest (x :: xs) h 32).drop c =
        (x :: xs).drop (TX.itemConsumed h 32 + c) := by
      intro c; rw [TX.itemRest, List.drop_drop]
    have hs' : skip n (TX.itemRest (x :: xs) h 32) = some (TX.itemRest (x :: xs) h 32).length := by
      simp only [skip, hd] at hs
      obtain ⟨c', h', hc'⟩ := Option.map_eq_some_iff.mp hs
      rw [← TX.itemRest] at h'
      rw [h']
      simp only [TX.itemRest, List.length_drop]
      congr 1; omega
    obtain ⟨hs2, hw⟩ := walk_hash n _ f (by omega)
      (fun i hi c hc => by rw [hdrop]; exact hfit (i + 1) (by omega) _ (hsk i c hc))
      (fun i hi c hc => by rw [hdrop]; exact hok (i + 1) (by omega) _ (hsk i c hc)) hs'
    refine ⟨TX.itemPayload (x :: xs) h 32 :: hs2, ?_⟩
    simp only [walkList]
    rw [show hash (x :: xs) = hash.run (x :: xs) from rfl, hrun]
    simp only [hw, Option.map_some]

/-- The hash list's walk succeeds once its `n` items were 32-byte strings filling its payload. -/
theorem hash_walk_ok {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (h3 : σ.t = 3) {c h p n : Nat}
    (hl : HashList σ c h p) (hs : skip n (TX.itemPayload (σ.payload.drop c) h p) = some p)
    (hn : n ≤ p) (hok : HashesOk (TX.itemPayload (σ.payload.drop c) h p) n) :
    ∃ hs, walkList hash (TX.itemPayload (σ.payload.drop c) h p).length
      (TX.itemPayload (σ.payload.drop c) h p) = some hs := by
  obtain ⟨hs10, hd⟩ := hl
  have hfits := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  have h3' : (σ.m.reg 12).toNat = 3 := h3
  have hf := fits_at hfits hs10 (by rw [h3']; decide)
  have hlen := payload_length hf hd
  have hin := fits_inner hfits hs10 (by rw [h3']; decide) hd
  refine walk_hash n _ _ (by rw [hlen]; exact hn) (fun i hi c' hc => ?_) hok
    (by rw [hlen]; exact hs)
  exact fits_at hin hc (by omega)

/-- Call-site entries that are all the hash walk of item 10 hold once the walk succeeds. -/
theorem hwalk_fields {σ : Sig} {m : Machine} {fs : List Field}
    (hv : ∀ f ∈ fs, f.v = .hwalk 10) {c h p : Nat} (hl : HashList σ c h p)
    (hw : ∃ hs, walkList hash (TX.itemPayload (σ.payload.drop c) h p).length
      (TX.itemPayload (σ.payload.drop c) h p) = some hs) : FieldsOk σ m fs := by
  intro f hf _
  rw [hv f hf]
  intro c' hs' l' h' p' hd'
  obtain ⟨hs10, hd⟩ := hl
  simp only [FieldVal.k] at hs'
  rw [hs10, Option.some.injEq] at hs'
  subst hs'
  rw [hd] at hd'
  cases hd'
  exact hw

/-- The entries `!(f.v != .hwalk 10)` selects are the hash walk. -/
theorem hwalk_sel {fs : List Field} :
    ∀ f ∈ fs.filter (fun f => !(f.v != .hwalk 10)), f.v = .hwalk 10 := fun f hf => by
  simpa using (List.mem_filter.mp hf).2

/-! ## The loop's leaves -/

/-- The call site of the return site `table[i]!`. -/
def siteAt (i : Nat) : Site := (table[i]!).site.getD default

/-- The source's `HashLoop` from its assertion (a plain cut whose `Extra` it is). -/
theorem hashLoop_of {d : CutData} {σ : Sig} {m : Machine} (hpc : d.pc = 0x800020ac)
    (hs : d.site = none) (hA : (mkCut d).A σ m) : HashLoop σ m := by
  simp only [mkCut, hpc, show (0x800020ac : Nat) ≠ entry by decide, if_false, ACut, hs,
    reduceCtorEq, false_and, exists_false, or_false] at hA
  obtain ⟨-, -, -, -, -, -, hx, -, -⟩ := hA
  simpa [Extra, hpc] using hx

/-- Arm 3 at a cut only arm 3 reaches. -/
theorem arm3 {σ : Sig} {arms : List Nat} (h : ArmOk σ arms) (ha : arms = [3]) : σ.t = 3 := by
  rcases h with h | h
  · rw [ha] at h; cases h
  · rw [ha] at h; simpa using h

/-- `decodeItem` on the list cursor (`0x800020ac`, leaf 0). -/
theorem DTF.leaf_800020ac_0 :
    LeafGoal DTF.plan DTF.plan.cuts[107]! ((DTF.plan.leaves 0x800020ac)[0]!) := by
  refine leaf_call_x (table[107]!) (table[108]!) (siteAt 108) ((leavesAt 0x800020ac)[0]!)
    F2.entry (by decide) DTF.cut_800020ac (by decide) (by decide) (by decide) rfl rfl
    (by decide) ?_
  intro σ m m' hA hc C CF
  have hpre := C.F.common.2.1
  have h3 : σ.t = 3 := arm3 C.F.arms (by decide)
  obtain ⟨c, h, p, n, j, hl, hsk, hnj, r23, r22, r25, hdr, hok⟩ :=
    hashLoop_of (by decide) (by decide) hA
  have e23 := ctx_reg C (i := 23) (i' := 23) (by decide) (by decide) (by decide)
  have e22 := ctx_reg C (i := 22) (i' := 22) (by decide) (by decide) (by decide)
  have e25 := ctx_reg C (i := 25) (i' := 25) (by decide) (by decide) (by decide)
  have e11 := ctx_reg C (i := 11) (i' := 23) (by decide) (by decide) (by decide)
  have e12 := ctx_reg C (i := 12) (i' := 22) (by decide) (by decide) (by decide)
  have hdr' := hdr_keep C (o := 0x258) (by decide) (by decide) (by decide) (by decide) hdr
  have hloop : HashLoop σ m' := ⟨c, h, p, n, j, hl, hsk, hnj, e23.trans r23, e22.trans r22,
    e25.trans r25, hdr', hok⟩
  have hjp : j ≤ p := by
    have := skip_le hsk
    simp only [TX.itemPayload, List.length_take, List.length_drop] at this
    omega
  have hle := hashList_le hpre h3 hl
  have hsp : m'.reg 2 = σ.fr + w 0 := CF.shape.1 (2, .fr 0) (by decide) _ rfl
  have hout : m'.reg 10 = σ.fr + w 0x2e0 := CF.shape.1 (10, .fr 0x2e0) (by decide) _ rfl
  have hf2 : F2.Pre m' := f2_pre_cur CF.common hsp hout (by decide) (by decide)
    (e11.trans r23) (e12.trans r22) (by omega) CF.aligned
  have hsx : SiteX (table[108]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[108]!).pc = 0x800020c0 by decide]
    simp only [SiteX, if_true]
    exact ⟨hloop, e11.trans e23.symm, e12.trans e22.symm⟩
  have hidx : IdxOk (siteAt 108).kind σ ([], [], ⟨[], []⟩) m' := by
    rw [show (siteAt 108).kind = .f2 by decide]; exact ⟨hf2, trivial⟩
  refine ⟨_, hidx, hsx, fun m'' hpost => ?_⟩
  have hfld := CF.fields
  have hsite : SiteA (siteAt 108) (table[108]!).pc σ ([], [], ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx, hfld, CF.chk, hsx⟩
  have hSF : (siteAt 108).kind.SiteFine (siteAt 108) = true := by decide
  have hR := ret_len C hSF hsite hpost (by decide)
  have e22' : m''.reg 22 = m'.reg 22 := (ret_common hSF hsite hpost).1.2 22 (by decide)
  rw [show (siteAt 108).kind.bound = 75 by decide]
  unfold budgetOf
  rw [show budgetAt (table[108]!).pc = (2791, .list (.reg 22)) from rfl,
    show budgetAt (table[107]!).pc = (2871, .list (.reg 22)) from rfl,
    show ((leavesAt 0x800020ac)[0]!).S.steps - (table[107]!).shape.S.steps = 5 by decide]
  simp only [innerOf, Loc.word]
  rw [show (Fin.ofNat 32 22 : Fin 32) = 22 from rfl, e22', show (22 : Fin 32) = Fin.ofNat 32 22
    from rfl, e22]
  omega

/-- A frame word a leaf writes, as the leaf's state says. -/
theorem ctx_word {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {o : Nat} (ho : o + 8 ≤ frameBytes) {s : Sym} (h : (Loc.slot o).sym l.S = s) :
    m'.load (σ.fr + w o) 8 = some (s.eval (envOf d.shape σ m)) := by
  rw [frame_load (ctx_common C).avail ho]
  have e := loc_word_eval C.wf' C.hm' C.hS' (loc := .slot o) (by simp [Loc.fine]; omega)
  simp only [Loc.word] at e
  rw [e, h]

/-- The list item's `decodeItem` at `0x80002064` (outcome at `S-0xb8`) succeeded on a list. -/
theorem list_out {σ : Sig} {m : Machine} (hA : (mkCut (table[106]!)).A σ m)
    (herr : (Sym.init 0 728 2).eval (envOf (table[106]!).shape σ m) = 0)
    (hlist : (Sym.bin .and (.init 0 712 1) (.lit 1)).eval (envOf (table[106]!).shape σ m) ≠ 0) :
    ∃ c h p, HashList σ c h p ∧ (Sym.init 0 704 8).eval (envOf (table[106]!).shape σ m) = w p ∧
      (p ≠ 0 → TX.wordAt m (σ.fr + w 696) = σ.inp + w (c + h)) := by
  have hadv : advOf (table[106]!) = some (696, 10) := by decide
  obtain ⟨c, l, h, p, hs, hd⟩ := f2_ok (by decide) (by decide) hadv hA herr
  have hL := f2_list (by decide) (by decide) hadv hA c hs l h p hd
  obtain ⟨hpw, hptr⟩ := f2_words (by decide) (by decide) hadv hA c hs l h p hd
  have hlt : l = true := by
    cases l
    · exact absurd hL (by simpa [isL] using hlist)
    · rfl
  subst hlt
  refine ⟨c, h, p, ⟨hs, hd⟩, hpw, fun hp0 => ?_⟩
  rw [hptr, if_neg fun h128 => hp0 ((decode_hdr hd).2 h128)]

/-- Into the loop (`0x80002064`, leaf 3): a nonempty list payload, the header `{1, 0, 0}`. -/
theorem DTF.leaf_80002064_3 :
    LeafGoal DTF.plan DTF.plan.cuts[106]! ((DTF.plan.leaves 0x80002064)[3]!) := by
  refine leaf_at_x (table[106]!) (table[107]!) ((leavesAt 0x80002064)[3]!) (by decide)
    DTF.cut_80002064 (by decide) (by decide) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have hpre := C.F.common.2.1
  have h3 : σ.t = 3 := arm3 C.F.arms (by decide)
  have herr := hc _ (show SBool.eq (.init 0 728 2) (.lit 0) ∈ _ by decide)
  have hlist := hc _ (show SBool.ne (.bin .and (.init 0 712 1) (.lit 1)) (.lit 0) ∈ _ by decide)
  have hp0 := hc _ (show SBool.ne (.init 0 704 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, bne_iff_ne, ne_eq] at herr hlist hp0
  obtain ⟨c, h, p, hl, hpw, hptr⟩ := list_out hA (by simpa using herr) (by simpa using hlist)
  have hle := hashList_le hpre h3 hl
  have hp64 : p < 2 ^ 64 := by have : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt; omega
  have hpn : p ≠ 0 := fun h0 => hp0 (by rw [hpw, h0]; rfl)
  have hptr' := hptr hpn
  -- the registers and the header at the target
  have r23 : m'.reg 23 = σ.inp + w (c + h + 0) := by
    rw [show (23 : Fin 32) = Fin.ofNat 32 23 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x80002064)[3]!).S.reg 23 = .bin .add (.ptr 3 0) (.var 151) by decide]
    simp only [Sym.eval, BinOp.eval, envOf, show ¬ (151 < 32) by decide,
      show ¬ (151 < 64) by decide, if_false, env_base3, Int.cast_ofNat_Int]
    rw [show 8 * (151 - 64) = 696 from rfl, hptr']
    simp [entryEnv, Env.base, regionsOf, w]
    bv_omega
  have r22 : m'.reg 22 = w (p - 0) := by
    rw [show (22 : Fin 32) = Fin.ofNat 32 22 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x80002064)[3]!).S.reg 22 = .init 0 704 8 by decide, hpw, Nat.sub_zero]
  have r25 : m'.reg 25 = w 0 := by
    rw [show (25 : Fin 32) = Fin.ofNat 32 25 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x80002064)[3]!).S.reg 25 = .lit 0 by decide]
    rfl
  obtain ⟨L, X, hlive⟩ := (ctx_common C).2.2.2.2.2.2.2.2
  have hdr : ListHdr σ m' 0x258 0 0 :=
    ⟨1, 0, ctx_word C (o := 0x258) (s := .lit 1) (by decide) (by decide),
      ctx_word C (o := 0x258 + 8) (s := .lit 0) (by decide) (by decide),
      ctx_word C (o := 0x258 + 16) (s := .lit 0) (by decide) (by decide), by decide, by decide,
      L, X, hlive, fun h0 => absurd h0 (by decide)⟩
  have hloop : HashLoop σ m' :=
    ⟨c, h, p, 0, 0, hl, rfl, Nat.le_refl _, r23, r22, r25, hdr, hashesOk_zero _⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [show (table[107]!).pc = 0x800020ac by decide]; simpa [Extra] using hloop
  · rw [show budgetAt (table[107]!).pc = (2871, .list (.reg 22)) from rfl]; trivial
  -- the budget: `rest` moved past the list, the bytes left are the list payload
  have hR' := restFrom_sound C (rs' := (table[107]!).rest) (by decide)
    ⟨.slot 0x158, true, 11⟩ (by decide)
  obtain ⟨c11, hs11, hw11⟩ := hR'
  obtain ⟨c10, hs10, hw10⟩ := C.rest ⟨.reg 25, true, 10⟩ (by decide)
  obtain ⟨hs, hd⟩ := hl
  rw [hs, Option.some.injEq] at hs10
  subst hs10
  rw [skip_snoc hs hd, Option.some.injEq] at hs11
  subst hs11
  have hf := fit_of_arms hpre (arms := [3]) (.inr (by simp [h3])) (by decide) hs
  obtain ⟨-, -, h64⟩ := TX.fits_bounds hf hd
  have hic : TX.itemConsumed h p = h + p := Nat.mod_eq_of_lt h64
  unfold budgetOf restLen
  rw [show budgetAt (table[107]!).pc = (2871, .list (.reg 22)) from rfl,
    show budgetAt (table[106]!).pc = (2889, .none) from rfl,
    show (table[107]!).rest.find? (·.len) = some ⟨.slot 0x158, true, 11⟩ by decide,
    show (table[106]!).rest.find? (·.len) = some ⟨.reg 25, true, 10⟩ by decide,
    show ((leavesAt 0x80002064)[3]!).S.steps - (table[106]!).shape.S.steps = 18 by decide]
  simp only [innerOf, Loc.word] at hw11 hw10 ⊢
  rw [hw11, hw10, show (Fin.ofNat 32 22 : Fin 32) = 22 from rfl, r22, hic]
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  simp only [if_true, w, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-! ## The list buffer at a call -/

/-- Two nonempty ranges, one of the allocator's private memory and one outside it, are apart. -/
theorem apart_priv {σ : Sig} {p q : Word} {k k' : Nat}
    (hp : ∀ a, InRange p k a → σ.A.Priv σ.g.L a) (hq : ∀ a, InRange q k' a → ¬ σ.A.Priv σ.g.L a)
    (hk : 0 < k) (hk' : 0 < k') (hpk : p.toNat + k ≤ 2 ^ 64) (hqk : q.toNat + k' ≤ 2 ^ 64) :
    p.toNat + k ≤ q.toNat ∨ q.toNat + k' ≤ p.toNat := by
  refine Classical.byContradiction fun hn => ?_
  have h1 : q.toNat < p.toNat + k := by omega
  have h2 : p.toNat < q.toNat + k' := by omega
  by_cases hpq : p.toNat ≤ q.toNat
  · exact hq q (by simp only [InRange]; omega) (hp q (by simp only [InRange]; omega))
  · exact hq p (by simp only [InRange]; omega) (hp p (by simp only [InRange]; omega))

/-- The bytes at `p`, read off a machine where they are present. -/
def bytesOf (m : Machine) (p : Word) (k : Nat) : List Byte :=
  (List.range k).map fun j => (m.mem (p + BitVec.ofNat 64 j)).getD 0

theorem bytesOf_at {m : Machine} {p : Word} {k : Nat} (h : Present m p k) :
    BytesAt m p (bytesOf m p k) := by
  intro i hi
  simp only [bytesOf, List.length_map, List.length_range] at hi
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h i hi)
  simp [bytesOf, hb]

theorem bytesOf_length (m : Machine) (p : Word) (k : Nat) : (bytesOf m p k).length = k := by
  simp [bytesOf]

/-- What a list header gives at a call: the words, the live list with the buffer, its bytes. -/
theorem hdr_facts {σ : Sig} {m : Machine} (hc : Common σ m) {o n r : Nat}
    (hh : ListHdr σ m o n r) :
    ∃ p cap : Word, ∃ L X, m.load (σ.fr + w o) 8 = some p ∧
      m.load (σ.fr + w (o + 8)) 8 = some (w n) ∧ m.load (σ.fr + w (o + 16)) 8 = some cap ∧
      n + r ≤ cap.toNat ∧ 0 < p.toNat ∧ Live σ m L X ∧ BufOwn X p cap ∧
      (0 < cap.toNat → RamRange p (cap.toNat * 32) ∧ (p, cap.toNat * 32) ∈ L ∧
        ∀ a, InRange p (cap.toNat * 32) a → σ.A.Priv σ.g.L a) ∧
      Present m p (n * 32) := by
  obtain ⟨p, cap, l0, l8, l16, hnr, hp0, L, X, hlive, hbuf⟩ := hh
  have hb : 0 < cap.toNat → RamRange p (cap.toNat * 32) ∧ (p, cap.toNat * 32) ∈ L ∧
      ∀ a, InRange p (cap.toNat * 32) a → σ.A.Priv σ.g.L a := fun h0 => by
    obtain ⟨-, hram, hpriv⟩ := hlive.2.2 _ (hbuf h0)
    exact ⟨hram, hlive.2.1.symm.subset (List.mem_append_right _ (hbuf h0)), hpriv⟩
  refine ⟨p, cap, L, X, l0, l8, l16, hnr, hp0, hlive, hbuf, hb, fun j hj => ?_⟩
  rcases Nat.eq_zero_or_pos cap.toNat with h0 | h0
  · omega
  · exact ((σ.A.live_ok L m hlive.1).2 _ (hb h0).2.1).2 j (by simp; omega)

/-- `toOwnedSlice`'s precondition at a call with `sp = fr`, the result slot `fr + ko` and the
list header `fr + ho` below the save area and apart, `a2` the allocator object; the items are
the buffer's first `32 n` bytes, the live list DTF's. -/
theorem f4_pre_dtf {σ : Sig} {m : Machine} (hc : Common σ m) {ko ho n : Nat}
    (hsp : m.reg 2 = σ.fr + w 0) (hres : m.reg 10 = σ.fr + w ko) (hhdr : m.reg 11 = σ.fr + w ho)
    (hao : m.reg 12 = σ.ao + w 0) (hko : ko + 24 + 104 ≤ frameBytes)
    (hho : ho + 24 + 104 ≤ frameBytes) (hko8 : ko % 8 = 0) (hho8 : ho % 8 = 0)
    (hkh : ko + 24 ≤ ho ∨ ho + 24 ≤ ko) (hh : ListHdr σ m ho n 0) (hra : RetAligned m) :
    ∃ L X items, F4.Pre σ.A L items m ∧ Live σ m L X ∧
      BufOwn X (ToOwned.listPtr m) (ToOwned.listCap m) := by
  obtain ⟨p, cap, L, X, l0, l8, l16, hnr, hp0, hlive, hbuf, hb, hpres⟩ := hdr_facts hc hh
  have hpre := hc.2.1
  have hav := hc.avail
  have hS := pre_sp hpre
  have hF : σ.fr.toNat = σ.S.toNat - frameBytes := fr_toNat hpre
  have hst : (σ.S - w stackBytes).toNat = σ.S.toNat - stackBytes :=
    S_sub_toNat hpre (Nat.le_refl _)
  have e8 : σ.fr + w ho + 8 = σ.fr + w (ho + 8) := by
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl]; simp only [w]; rw [F1.add_add_ofNat]
  have e16 : σ.fr + w ho + 16 = σ.fr + w (ho + 16) := by
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl]; simp only [w]; rw [F1.add_add_ofNat]
  have ep : ToOwned.listPtr m = p := by simp [ToOwned.listPtr, ToOwned.wordAt, hhdr, l0]
  have en : ToOwned.listLen m = w n := by
    simp only [ToOwned.listLen, ToOwned.wordAt, hhdr]; rw [e8, l8]; rfl
  have ec : ToOwned.listCap m = cap := by
    simp only [ToOwned.listCap, ToOwned.wordAt, hhdr]; rw [e16, l16]; rfl
  have hP : ∀ a, InRange σ.res resultBytes a ∨ InRange σ.ao 16 a ∨ InRange σ.inp σ.len a ∨
      InRange (σ.S - w stackBytes) stackBytes a ∨ InRange TX.scratch 8 a →
      ¬ σ.A.Priv σ.g.L a := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- the entry's separation facts, kept folded (`omega` would split every disjunction)
  obtain ⟨-, -, -, -, -, haoR, hao8, haoS, -, -, -, -, -, -, -, -, -, -, -, -, d5, -,
    -, d8, -, d10, -⟩ := hpre
  have haoR' : Layout.ramLo ≤ σ.ao.toNat ∧ σ.ao.toNat + 16 ≤ Layout.ramHi := haoR
  have hao8' : σ.ao.toNat % 8 = 0 := hao8
  have d5' : TX.Apart (σ.S - w stackBytes) stackBytes σ.ao 16 := d5
  have d8' : TX.Apart TX.scratch 8 σ.ao 16 := d8
  have d10' : TX.Apart TX.scratch 8 (σ.S - w stackBytes) stackBytes := d10
  clear haoR hao8 d5 d8 d10
  have hn : (w n).toNat = n := by
    rcases Nat.eq_zero_or_pos cap.toNat with h0 | h0
    · simp only [w, BitVec.toNat_ofNat]; omega
    · simp only [w, BitVec.toNat_ofNat]; have := cap.isLt; omega
  have hsb : stackBytes = 1584 := rfl
  have hfb : frameBytes = 880 := rfl
  have hfS : σ.fr.toNat + 880 = σ.S.toNat := by
    rw [hF]; simp only [hfb, stackBytes, TX.stackBytes] at hS ⊢; omega
  have eko : (σ.fr + w ko).toNat = σ.fr.toNat + ko := fr_add_toNat hc.2.1 (by omega)
  have eho : (σ.fr + w ho).toNat = σ.fr.toNat + ho := fr_add_toNat hc.2.1 (by omega)
  have esp : (σ.fr - 112).toNat = σ.fr.toNat - 112 := by
    have := below_fr_toNat' hc.2.1 (n := 112) (by decide)
    simpa [w] using this
  have hscr : ToOwned.scratch.toNat = Layout.extraParams := rfl
  have hscr' : TX.scratch.toNat = Layout.extraParams := rfl
  have hao0 : σ.ao + w 0 = σ.ao := by simp [w]
  have hsp0 : σ.fr + w 0 = σ.fr := by simp [w]
  have hnot : ∀ a, (InRange (σ.fr + w ko) 24 a ∨ InRange (σ.fr + w ho) 24 a ∨
      InRange (σ.fr - 112) 112 a) → ¬ σ.A.Priv σ.g.L a := fun a ha =>
    hP a (.inr (.inr (.inr (.inl (by
      simp only [InRange, hst, eko, eho, esp] at ha ⊢
      simp only [hsb] at hfS ⊢; omega)))))
  refine ⟨L, X, bytesOf m p (n * 32), ?_, hlive, by rw [ep, ec]; exact hbuf⟩
  show ToOwned.Pre F4.elemBytes σ.A L (bytesOf m p (n * 32)) m
  unfold ToOwned.Pre
  simp only [ep, en, ec, hsp, hres, hhdr, hao, hao0, hsp0]
  unfold ToOwned.Apart RamRange InRange
  simp only [eko, eho, esp, hscr, hn, F4.elemBytes]
  have hbA : ∀ q k', 0 < k' → q.toNat + k' ≤ 2 ^ 64 →
      (∀ a, InRange q k' a → ¬ σ.A.Priv σ.g.L a) →
      0 < cap.toNat → p.toNat + cap.toNat * 32 ≤ q.toNat ∨ q.toNat + k' ≤ p.toNat :=
    fun q k' hk' hq hn h0 => by
      have hr := (hb h0).1
      unfold RamRange Layout.ramHi at hr
      exact apart_priv (hb h0).2.2 hn (by omega) hk' (by omega) hq
  have hlo := hS.1
  have hhi := hS.2.1
  simp only [Layout.ramLo, Layout.ramHi, hsb] at hlo hhi haoR' ⊢
  refine ⟨hc.2.2.1, ⟨?_, ?_, ?_, fun j hj => ?_⟩, hra, ⟨by omega, by omega⟩, by omega,
    fun j hj => ?_, ⟨by omega, by omega⟩, by omega,
    ⟨l0, by rw [e8]; exact l8, by rw [e16]; exact l16⟩, by omega, bytesOf_length _ _ _, hp0,
    fun h0 => ⟨(hb h0).1, (hb h0).2.1⟩, bytesOf_at hpres, haoR', hao8', ?_, common_vtable hav,
    hc.2.2.2.2.2.2.1, hlive.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h0 => ⟨?_, ?_, ?_, ?_, ?_⟩, fun a ha hPa => ?_⟩
  · rw [hsp, hsp0, hF]; omega
  · rw [hsp, hsp0, hF]; omega
  · rw [hsp, hsp0, hF]; omega
  · rw [hsp, hsp0]
    have := hav.stack (1584 - 880 - 112 + j) (by omega)
    rwa [show σ.S - w stackBytes + BitVec.ofNat 64 (1584 - 880 - 112 + j) =
      σ.fr - BitVec.ofNat 64 112 + BitVec.ofNat 64 j by
        apply BitVec.eq_of_toNat_eq
        simp only [Sig.fr, w, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hfb, hsb]
        omega] at this
  · rw [show σ.fr + w ko + BitVec.ofNat 64 j = σ.fr + BitVec.ofNat 64 (ko + j) by
      simp only [w]; rw [F1.add_add_ofNat]]
    exact stack_present hav (by omega)
  · rw [load_congr (m := σ.m) fun t ht => hav.ao (by omega)]; exact haoS
  -- the ten `Apart`s of the call's own ranges, each from at most one of the entry's
  all_goals first
    | omega
    | (have := d5'; unfold TX.Apart at this; rw [hst] at this; omega)
    | (have := d8'; unfold TX.Apart at this; rw [hscr'] at this; omega)
    | (have := d10'; unfold TX.Apart at this; rw [hscr', hst] at this; omega)
    | skip
  -- the buffer, one of DTF's blocks, against the call's ranges
  · have := hbA (σ.fr + w ko) 24 (by decide) (by rw [eko]; omega)
      (fun a ha => hnot a (.inl ha)) h0
    rwa [eko] at this
  · have := hbA (σ.fr + w ho) 24 (by decide) (by rw [eho]; omega)
      (fun a ha => hnot a (.inr (.inl ha))) h0
    rwa [eho] at this
  · exact hbA σ.ao 16 (by decide) (by omega) (fun a ha => hP a (.inr (.inl ha))) h0
  · have := hbA (σ.fr - 112) 112 (by decide) (by rw [esp]; omega)
      (fun a ha => hnot a (.inr (.inr ha))) h0
    rwa [esp] at this
  · have := hbA TX.scratch 8 (by decide) (by rw [hscr']; unfold Layout.extraParams; omega)
      (fun a ha => hP a (.inr (.inr (.inr (.inr ha))))) h0
    rwa [hscr'] at this
  -- the owned ranges are not the allocator's
  have hP' := priv_sub hc.2.1 hlive hPa
  rcases ha with h | h | h | h | h
  · exact hnot a (.inl (by simpa only [InRange, eko] using h)) hP'
  · exact hnot a (.inr (.inl (by simpa only [InRange, eho] using h))) hP'
  · exact hP a (.inr (.inl h)) hP'
  · exact hnot a (.inr (.inr (by simpa only [InRange, esp] using h))) hP'
  · exact hP a (.inr (.inr (.inr (.inr (by simpa only [InRange, hscr'] using h))))) hP'

/-- The empty list (`0x80002064`, leaf 2): `toOwnedSlice` on the header `{1, 0, 0}`. -/
theorem DTF.leaf_80002064_2 :
    LeafGoal DTF.plan DTF.plan.cuts[106]! ((DTF.plan.leaves 0x80002064)[2]!) := by
  refine leaf_call_xf (fun f => f.v != .hwalk 10) (table[106]!) (table[111]!) (siteAt 111)
    ((leavesAt 0x80002064)[2]!) F4.entry (by decide) DTF.cut_80002064 (by decide) (by decide)
    (by decide) rfl rfl (by decide) ?_ ?_
  · -- the empty list's walk
    intro σ m m' hA hc C
    have herr := hc _ (show SBool.eq (.init 0 728 2) (.lit 0) ∈ _ by decide)
    have hlist := hc _ (show SBool.ne (.bin .and (.init 0 712 1) (.lit 1)) (.lit 0) ∈ _ by decide)
    have hp0 := hc _ (show SBool.eq (.init 0 704 8) (.lit 0) ∈ _ by decide)
    simp only [SBool.eval, beq_iff_eq, bne_iff_ne, ne_eq] at herr hlist hp0
    obtain ⟨c, h, p, hl, hpw, -⟩ := list_out hA (by simpa using herr) (by simpa using hlist)
    have hpz : p = 0 := by
      have hp64 := decode_p_lt hl.2
      rw [hpw] at hp0
      have := congrArg BitVec.toNat hp0
      simp only [w, BitVec.toNat_ofNat, Sym.eval_lit] at this
      omega
    subst hpz
    refine hwalk_fields hwalk_sel hl ⟨[], ?_⟩
    simp only [TX.itemPayload, List.take_zero, List.length_nil]
    exact walkList_nil _ _
  intro σ m m' hA hc C CF
  obtain ⟨L0, X0, hlive0⟩ := (ctx_common C).2.2.2.2.2.2.2.2
  have hdr : ListHdr σ m' 0x258 0 0 :=
    ⟨1, 0, ctx_word C (o := 0x258) (s := .lit 1) (by decide) (by decide),
      ctx_word C (o := 0x258 + 8) (s := .lit 0) (by decide) (by decide),
      ctx_word C (o := 0x258 + 16) (s := .lit 0) (by decide) (by decide), by decide, by decide,
      L0, X0, hlive0, fun h0 => absurd h0 (by decide)⟩
  have hsp : m'.reg 2 = σ.fr + w 0 := CF.shape.1 (2, .fr 0) (by decide) _ rfl
  have hres : m'.reg 10 = σ.fr + w 0x270 := CF.shape.1 (10, .fr 0x270) (by decide) _ rfl
  have hhdr : m'.reg 11 = σ.fr + w 0x258 := CF.shape.1 (11, .fr 0x258) (by decide) _ rfl
  have hao : m'.reg 12 = σ.ao + w 0 := CF.shape.1 (12, .ao 0) (by decide) _ rfl
  obtain ⟨L, X, items, hpre4, hlive, hbuf⟩ := f4_pre_dtf CF.common hsp hres hhdr hao
    (by decide) (by decide) (by decide) (by decide) (by decide) hdr CF.aligned
  have hsx : SiteX (table[111]!).pc σ (L, items, ⟨[], []⟩) m' := by
    rw [show (table[111]!).pc = 0x80002180 by decide]; exact siteX_of_no (by decide) σ _ m'
  have hidx : IdxOk (siteAt 111).kind σ (L, items, ⟨[], []⟩) m' := by
    rw [show (siteAt 111).kind = .f4 by decide]; exact ⟨hpre4, X, hlive, hbuf⟩
  refine ⟨_, hidx, hsx, fun m'' hpost => ?_⟩
  have hfld := CF.fields
  have hsite : SiteA (siteAt 111) (table[111]!).pc σ (L, items, ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx, hfld, CF.chk, hsx⟩
  have hSF : (siteAt 111).kind.SiteFine (siteAt 111) = true := by decide
  have hR := ret_len C hSF hsite hpost (by decide)
  rw [show (siteAt 111).kind.bound = 194 by decide]
  unfold budgetOf
  rw [show budgetAt (table[111]!).pc = (2352, .none) from rfl,
    show budgetAt (table[106]!).pc = (2889, .none) from rfl,
    show ((leavesAt 0x80002064)[2]!).S.steps - (table[106]!).shape.S.steps = 22 by decide]
  simp only [innerOf]
  omega

end ZesuExec.Fn.DTF
