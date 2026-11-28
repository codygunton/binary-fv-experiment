import ZesuExec.Fn.TX.Room

/-!
# TX: the success exit (`0x800004a0`, leaf 0)

`toOwnedSlice` of the entries list (F5) returned the slice `{p', n}` at `S-0x88` with error code 0;
the leaf copies it to `res` and returns. The outer payload is walked, so the decision accepts the
finished entries (`accepted_of`), and the allocator's list is the caller's with the returned
blocks: the entries slice and the finished keys slices (`ok_post`).
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- A walked outer payload: the decision accepts the finished entries, consuming the item. -/
theorem accepted_of {σ : Sig} {m : Machine} {o : Obs} (hok : OuterOk σ m o) (hip : o.i = o.p) :
    OutcomeAllowed σ.input (.ok o.done) (itemConsumed o.h o.p) := by
  obtain ⟨hdec, -, -, -, hw⟩ := hok
  rw [hip] at hw
  have hdrop : (pl σ o).drop o.p = [] := List.drop_eq_nil_of_le (by
    simp only [pl, itemPayload, List.length_take]; omega)
  have h2 := hw.2.1
  rw [hdrop] at h2
  simp only [entriesWalk, List.length_nil, Option.map_some, List.append_nil] at h2
  show (walk σ.input).2 = .accepted o.done (itemConsumed o.h o.p)
  simp only [walk, hdec]
  rw [show (entriesWalk (itemPayload σ.input o.h o.p).length (itemPayload σ.input o.h o.p)).2 =
    some o.done from h2]

theorem TX.leaf_800004a0_0 :
    LeafGoal TX.plan TX.plan.cuts[16]! ((TX.plan.leaves 0x800004a0)[0]!) := by
  show LeafGoal TX.plan cut4a0 (run4a0_leaves[0]!)
  have hcs : (run4a0_leaves[0]!).conds = [SBool.eq (Sym.init 0 456 2) (Sym.lit 0)] := by decide
  have hobl : (run4a0_leaves[0]!).obligs = [.aligned retTarget 4] := by decide
  intro σ m hA hc
  have hcm := (ret_4a0 hA).1
  have hpre := hcm.2.1
  obtain ⟨hbe, hwf⟩ := envB_ok (ov := ovBody) (ks := [vtableKnown]) hcm
  refine ⟨?_, ?_, fun m' hm' hex hfr => ?_⟩
  · rw [hobl]; intro o ho; simp only [List.mem_singleton] at ho; subst ho
    show (retTarget.eval (envB σ m)).toNat % 4 = 0
    have := saved_eval hcm hbe (k := 0) (by decide)
    simp only [retTarget, Sym.eval, BinOp.eval] at this ⊢
    rw [this]; exact hcm.2.1.2.2.1
  · budget_auto
  have hx : (run4a0_leaves[0]!).exit = .ret retTarget := by decide
  rw [hx] at hex ⊢
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 456 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  have h1' : (Sym.init 0 456 2).eval (envB σ m) = 0 := by
    simpa [SBool.eval, Sym.eval] using h1
  obtain ⟨mc, ⟨L, items⟩, ⟨o, hc0, hok, hip, hEL, hlive, hitems, ha⟩, ⟨⟨hret, hso, hbr⟩, -⟩⟩ := hA
  dsimp only at hlive hitems hso hbr
  subst hitems
  have hres : mc.reg 10 = σ.sl 0x88 := ha.arg 0 (by simp)
  have hhdr : mc.reg 11 = σ.sl 0x1c0 := ha.arg 1 (by simp)
  have hok' : OuterOk σ m o :=
    outerOk_keep hc0.2.1 hso (fun a h => f5_rcls hc0 hEL hlive hres hhdr h) hok
  have hEL0 := hEL
  obtain ⟨hH, hle', hp0, hc0', hc32, hram', hil, hbytes, hz⟩ := hEL
  have hnN : (w o.done.length).toNat = o.done.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  simp only [ToOwned.listPtr, ToOwned.listLen, ToOwned.listCap, hhdr, hres, f4w hH.1, f4w hH.2.1,
    f4w hH.2.2, show mc.reg 2 - 112 = σ.sl 688 from sp_sub hc0 112, hnN] at hso hbr
  -- the result words at `S-0x88`
  have e80 : σ.sl 0x88 + 8 = σ.sl 0x80 := by simp only [Sig.sl, w]; bv_omega
  have hres440 : ∀ {v : Word}, m.load (σ.sl 0x88) 8 = some v →
      (Sym.init 0 440 8).eval (envB σ m) = v := fun h =>
    frame_init hpre (k := 0x88) (by decide) (by decide) h
  have hres448 : ∀ {v : Word}, m.load (σ.sl 0x88 + 8) 8 = some v →
      (Sym.init 0 448 8).eval (envB σ m) = v := fun h =>
    frame_init hpre (k := 0x80) (by decide) (by decide) (by rw [← e80]; exact h)
  -- the consumed count and `rest`
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hcons : itemConsumed o.h o.p = o.h + o.p := Nat.mod_eq_of_lt (by have := hok.2.1; omega)
  have hall := accepted_of hok hip
  have hr0 : m.load σ.rest 8 = some (σ.inp + w (itemConsumed o.h o.p)) := by
    rw [hcons]; exact hok'.2.2.1
  have hr8 : m.load (σ.rest + 8) 8 = some (wordAt σ.m (σ.rest + 8) - w (itemConsumed o.h o.p)) := by
    rw [hcons, hok'.2.2.2.1, w_len]
  have hsave : ∀ k < 13, (run4a0_leaves[0]!).S.reg (savedReg k).val = .init 0 (576 - 8 * (k + 1)) 8 :=
    by decide
  have hsp : (run4a0_leaves[0]!).S.reg 2 = .ptr 0 576 := by decide
  have hmem : (run4a0_leaves[0]!).S.mem = okWrites := by decide
  have hEX : ∀ b ∈ EX o, b ∈ L := fun b hb =>
    hlive.2.1.symm.subset (List.mem_append_right _ hb)
  split at hbr
  · -- no entries: the empty slice
    rename_i hn0
    obtain ⟨-, ⟨r0, r8, -, -⟩, hheap, -⟩ := hbr
    have hd : o.done = [] := List.eq_nil_of_length_eq_zero hn0
    have his : o.is = [] := List.eq_nil_of_length_eq_zero (by rw [hil, hd]; rfl)
    have hperm : (if 0 < o.ec.toNat then L.erase (o.ep, o.ec.toNat * F5.elemBytes) else L).Perm
        (σ.g.L ++ []) := by
      split
      · rename_i h0
        have hl1 : Live σ mc L ([] ++ [(o.ep, entrySize * o.ec.toNat)]) := by
          have : EX o = [(o.ep, entrySize * o.ec.toNat)] := by simp [EX, h0, hd, his, keysBlocks]
          rw [List.nil_append, ← this]; exact hlive
        have := erase_perm hl1 (by show 0 < entrySize * o.ec.toNat; unfold entrySize; omega)
        rwa [show entrySize * o.ec.toNat = o.ec.toNat * F5.elemBytes by
          simp [Nat.mul_comm, entrySize, F5.elemBytes]] at this
      · rename_i h0
        have : EX o = [] := by simp [EX, h0, hd, his, keysBlocks]
        have hP := hlive.2.1; rwa [this] at hP
    have hl' : Live σ m _ (returnedBlocks o.ep [] []) := ⟨hheap, by simpa [returnedBlocks] using hperm,
      fun b hb => by simp [returnedBlocks] at hb⟩
    have r8' : m.load (σ.sl 0x88 + 8) 8 = some 0 := r8
    refine ok_post (es := []) (is := []) hcm hl' hbe hwf rfl hm' (by decide) hfr hsave hsp hex hmem
      (by rw [← hd]; exact hall) hr0 hr8 (hres440 r0) (by rw [hres448 r8']; rfl) rfl
      (fun h => absurd rfl h) (fun i hi => by simp [entriesBytes] at hi) (by simp [entriesBytes])
      (fun x hx => by simp at hx)
  · rename_i hn0
    rcases hbr with ⟨p', hp', hR', hB', -, ⟨r0, r8, -, -⟩, hheap, -⟩ | ⟨-, ⟨-, e16, -⟩, -, -⟩
    rotate_left
    · exfalso
      have := frame_init_n hpre (k := 0x88) (off := 16) (n := 2) (by decide) (by decide)
        (by rw [show (16 : Word) = w 16 from rfl] at e16; exact e16)
      rw [show 576 - 0x88 + 16 = 456 from rfl, h1'] at this
      exact absurd this (by decide)
    -- the entries slice `p'` and the finished keys slices
    have hdne : o.done ≠ [] := fun h => hn0 (by simp [h])
    have hn1 : 0 < o.done.length := List.length_pos_iff.mpr hdne
    have hec : 0 < o.ec.toNat := by omega
    have hEXe : EX o = [(o.ep, entrySize * o.ec.toNat)] ++ keysBlocks o.done o.is := by
      simp [EX, hec]
    have hl1 : Live σ mc L (keysBlocks o.done o.is ++ [(o.ep, entrySize * o.ec.toNat)]) :=
      live_perm hlive (by rw [hEXe]; exact List.perm_append_comm)
    have he1 := erase_perm hl1 (by show 0 < entrySize * o.ec.toNat; unfold entrySize; omega)
    rw [show entrySize * o.ec.toNat = o.ec.toNat * F5.elemBytes by
      simp [Nat.mul_comm, entrySize, F5.elemBytes]] at he1
    have hret' : returnedBlocks p' o.done o.is =
        [(p', entrySize * o.done.length)] ++ keysBlocks o.done o.is := by
      simp [returnedBlocks, hdne, keysBlocks]
    have hperm : (L.erase (o.ep, o.ec.toNat * F5.elemBytes) ++
        [(p', o.done.length * F5.elemBytes)]).Perm (σ.g.L ++ returnedBlocks p' o.done o.is) := by
      rw [hret', show o.done.length * F5.elemBytes = entrySize * o.done.length by
        simp [Nat.mul_comm, entrySize, F5.elemBytes]]
      refine (List.Perm.append_right _ he1).trans ?_
      rw [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    have hl' : Live σ m _ (returnedBlocks p' o.done o.is) := live_of_heap hpre hheap hperm
      fun b hb => by
        rw [hret'] at hb
        rcases List.mem_append.mp hb with hb | hb
        · simp only [List.mem_singleton] at hb; subst hb
          show 0 < entrySize * o.done.length; unfold entrySize; omega
        · exact (hlive.2.2 b (by rw [hEXe]; exact List.mem_append_right _ hb)).1
    -- the keys slices are not written by `toOwnedSlice`
    have hkeep : ∀ b ∈ keysBlocks o.done o.is, ∀ t < b.2,
        m.mem (b.1 + BitVec.ofNat 64 t) = mc.mem (b.1 + BitVec.ofNat 64 t) := by
      intro b hb t ht
      have hbX : b ∈ EX o := by rw [hEXe]; exact List.mem_append_right _ hb
      have hram := (hlive.2.2 b hbX).2.1
      unfold RamRange Layout.ramHi at hram
      have hin : InRange b.1 b.2 (b.1 + BitVec.ofNat 64 t) := in_self (by omega) ht
      have hP := (hlive.2.2 b hbX).2.2 _ hin
      refine hso _ fun h => ?_
      rcases h with h | h | h | h | h | ⟨-, h⟩
      · exact stack_not_priv hpre (sl_in_stack hpre (by decide) (by decide) h) hP
      · exact stack_not_priv hpre (sl_in_stack hpre (by decide) (by decide) h) hP
      · exact stack_not_priv hpre (sl_in_stack hpre (by decide) (by decide) h) hP
      · exact owned_not_priv hpre (.inr (.inr (.inr h))) hP
      · exact σ.A.priv_not_live L _ h ⟨b, hEX b hbX, hin⟩
      · have hl2 : Live σ mc L ([(o.ep, entrySize * o.ec.toNat)] ++ keysBlocks o.done o.is) := by
          rw [← hEXe]; exact hlive
        have := live_apart hl2 (List.mem_singleton_self _) hb
        simp only [InRange, F5.elemBytes, entrySize] at h hin this; omega
    have hr8' : m.load (σ.sl 0x88 + 8) 8 = some (BitVec.ofNat 64 o.done.length) := r8
    refine ok_post hcm hl' hbe hwf rfl hm' (by decide) hfr hsave hsp hex hmem hall hr0 hr8
      (hres440 r0) (hres448 hr8') hil (fun _ => by
        rw [show entrySize * o.done.length = o.done.length * F5.elemBytes by
          simp [Nat.mul_comm, entrySize, F5.elemBytes]]; exact hR') hB'
      (Nat.le_of_eq (entriesBytes_length o.done o.is hil fun x hx => ⟨(hz x hx).1, (hz x hx).2.1⟩))
      fun x hx => ?_
    obtain ⟨hpad, -, hkl, hkram, hkb⟩ := hz x hx
    refine ⟨hpad, hkram, Nat.le_of_eq (flatten_length _ hkl), ?_⟩
    by_cases hk : x.1.keys = []
    · rw [hk]; intro i hi; simp at hi
    · exact bytes_congr hkb fun t ht => hkeep _ (mem_keysBlocks hx hk) t
        (by rw [flatten_length _ hkl] at ht; exact ht)

end ZesuExec.Fn.TX
