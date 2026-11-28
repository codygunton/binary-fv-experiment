import ZesuExec.Fn.DTF.Head

/-!
# DTF: the reference decoder's values on checked items (programme plan S7, success write)

`Head.lean`'s `Reads` says a parser succeeds on checked items; here `ReadsV` also names the value:
each field helper returns a function of the item's bytes (`numOf`, `payOf`, `addrOf`, `alOf`), and
`body t` for `t ≤ 2` returns the transaction those values make (`legacyOf`, `typedOf`), so
`decode t payload` is that transaction when every item passes its check (`decode_legacy`,
`decode_typed`). The success write's `TxAt` compares the stored item values (`FieldsOk`) with
these. Arms 3 and 4 also need the hash and authorization walks (`hashList`, `authList`), which
`ChecksOk` does not state.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec

/-- The header and payload length of the item at the head of `b` (zero when it does not decode). -/
def hdOf (b : List Byte) : Nat × Nat :=
  match F2.decode b with
  | .success _ h p => (h, p)
  | .error => (0, 0)

/-- The bytes after the item at the head of `b`. Irreducible: nested `restOf`s would otherwise
unfold to exponentially many `F2.decode`s whenever a goal is put in weak head normal form. -/
@[irreducible] def restOf (b : List Byte) : List Byte := TX.itemRest b (hdOf b).1 (hdOf b).2

/-- The item's payload. -/
def payOf (b : List Byte) : List Byte := TX.itemPayload b (hdOf b).1 (hdOf b).2

/-- The item's number of at most `n` bytes (`numVal`). -/
def numOf (n : Nat) (b : List Byte) : Nat := numVal n (hdOf b).2 (payOf b)

/-- `txAddr`'s value: `null` for the empty string. -/
def addrOf (b : List Byte) : Option (List Byte) := if (hdOf b).2 = 0 then none else some (payOf b)

/-- The access list's entries (`TX.candidate`). -/
def alOf (b : List Byte) : List TX.EntryValue :=
  match TX.candidate b with
  | .accepted es _ => es
  | .rejected _ => []

theorem hdOf_eq {b : List Byte} {l : Bool} {h p : Nat} (hd : F2.decode b = .success l h p) :
    hdOf b = (h, p) := by
  simp only [hdOf, hd]

/-- `x` reads one item checked by `ch` and returns `f` of the bytes it starts at. -/
def StepV {α : Type} (x : P α) (ch : Chk) (f : List Byte → α) : Prop :=
  ∀ b, TX.HeaderFits b → ch.Ok b → x.run b = some (f b, restOf b)

/-- `x` reads exactly the items `chs` describe and returns `v` of the bytes it starts at. -/
def ReadsV {α : Type} (x : P α) (chs : List Chk) (v : List Byte → α) : Prop :=
  ∀ b c, ChecksL chs b → skip chs.length b = some c → x.run b = some (v b, b.drop c)

/-- Every check is of an item that decodes. -/
theorem chk_decodes {ch : Chk} {b : List Byte} (h : ch.Ok b) :
    ∃ l hh p, F2.decode b = .success l hh p := by
  cases ch with
  | str => obtain ⟨hh, p, hd⟩ := h; exact ⟨_, _, _, hd⟩
  | le n => obtain ⟨hh, p, hd, -⟩ := h; exact ⟨_, _, _, hd⟩
  | addr => obtain ⟨hh, p, hd, -⟩ := h; exact ⟨_, _, _, hd⟩
  | list => obtain ⟨hh, p, hd⟩ := h; exact ⟨_, _, _, hd⟩
  | al =>
    obtain ⟨es, n, hc⟩ := h
    unfold TX.candidate TX.walk at hc
    split at hc
    · next hh p hd => exact ⟨_, _, _, hd⟩
    · simp at hc

theorem readsV_pure {α : Type} (a : α) : ReadsV (pure a : P α) [] (fun _ => a) := by
  intro b c _ hs
  simp only [List.length_nil, skip, Option.some.injEq] at hs
  subst hs
  simp [StateT.run_pure]

theorem readsV_bind {α β : Type} {x : P α} {g : α → P β} {ch : Chk} {chs : List Chk}
    {f : List Byte → α} {vg : α → List Byte → β}
    (hx : StepV x ch f) (hg : ∀ a, ReadsV (g a) chs (vg a)) :
    ReadsV (x >>= g) (ch :: chs) (fun b => vg (f b) (restOf b)) := by
  intro b c hck hs
  obtain ⟨hfit, hok, htl⟩ := hck
  obtain ⟨l, h, p, hd⟩ := chk_decodes hok
  have hr : restOf b = TX.itemRest b h p := by simp only [restOf, hdOf_eq hd]
  simp only [List.length_cons, skip, hd] at hs
  obtain ⟨c', hs', rfl⟩ := Option.map_eq_some_iff.mp hs
  have hu := hg (f b) _ c' (htl l h p hd) hs'
  simp only [StateT.run_bind, hx b hfit hok, Option.bind_eq_bind, Option.bind_some, hr]
  rw [hu, TX.itemRest, List.drop_drop]

theorem stepV_map {α β : Type} {x : P α} {ch : Chk} {f : List Byte → α} (g : α → β)
    (hx : StepV x ch f) : StepV (g <$> x) ch (fun b => g (f b)) := by
  intro b hf hok
  simp [StateT.run_map, hx b hf hok]

theorem stepV_bytesView : StepV bytesView .str payOf := by
  rintro b - ⟨h, p, hd⟩
  rw [bytesView_run hd]
  simp only [payOf, restOf, hdOf_eq hd]

theorem stepV_u64 : StepV u64 (.le 8) (numOf 8) := by
  rintro b hf ⟨h, p, hd, hp⟩
  simp only [u64, StateT.run_bind, bytesView_run hd, Option.bind_eq_bind, Option.bind_some,
    payload_length hf hd, show ¬ p > 8 by omega, if_false]
  simp only [numOf, numVal, payOf, restOf, hdOf_eq hd, show ¬ 8 < p by omega, if_false]
  rfl

theorem stepV_nonce : StepV nonce .str (numOf 8) := by
  rintro b hf ⟨h, p, hd⟩
  simp only [nonce, StateT.run_bind, bytesView_run hd, Option.bind_eq_bind, Option.bind_some,
    payload_length hf hd]
  simp only [numOf, numVal, payOf, restOf, hdOf_eq hd, gt_iff_lt]
  rfl

theorem stepV_u128 : StepV u128 .str (numOf 16) := by
  rintro b hf ⟨h, p, hd⟩
  simp only [u128, StateT.run_bind, bytesView_run hd, Option.bind_eq_bind, Option.bind_some,
    payload_length hf hd]
  simp only [numOf, numVal, payOf, restOf, hdOf_eq hd, gt_iff_lt]
  rfl

theorem stepV_u256 : StepV u256 (.le 32) (numOf 32) := by
  rintro b hf ⟨h, p, hd, hp⟩
  simp only [u256, StateT.run_bind, bytesView_run hd, Option.bind_eq_bind, Option.bind_some,
    payload_length hf hd, show ¬ p > 32 by omega, if_false]
  simp only [numOf, numVal, payOf, restOf, hdOf_eq hd, show ¬ 32 < p by omega, if_false]
  rfl

theorem stepV_addr : StepV addr .addr addrOf := by
  rintro b hf ⟨h, p, hd, hp⟩
  have hl := payload_length hf hd
  simp only [addr, StateT.run_bind, item_run hd, Option.bind_eq_bind, Option.bind_some]
  simp only [addrOf, payOf, restOf, hdOf_eq hd]
  rcases hp with rfl | rfl
  · simp [hl]
  · simp [hl]

theorem stepV_accessList : StepV accessList .al alOf := by
  rintro b - ⟨es, n, hc⟩
  obtain ⟨l, h, p, hd⟩ := chk_decodes (ch := .al) ⟨es, n, hc⟩
  have hc' := hc
  simp only [TX.candidate, TX.walk] at hc'
  split at hc'
  · next kh kl heq =>
    rw [hd] at heq
    injection heq with hl hh hp
    subst hh hp
    split at hc'
    · simp only [TX.Candidate.accepted.injEq] at hc'
      simp only [StateT.run, accessList, hc, alOf, restOf, hdOf_eq hd, TX.itemRest, hc'.2]
    · simp at hc'
  · simp at hc'

/-! ## `body t` from its field helpers' runs -/

theorem body_legacy {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : List Byte} {n gp gl val vr r s : Nat}
    {to : Option (List Byte)} {d : List Byte}
    (h0 : nonce.run b0 = some (n, b1)) (h1 : u128.run b1 = some (gp, b2))
    (h2 : u64.run b2 = some (gl, b3)) (h3 : addr.run b3 = some (to, b4))
    (h4 : u256.run b4 = some (val, b5)) (h5 : bytesView.run b5 = some (d, b6))
    (h6 : u256.run b6 = some (vr, b7)) (h7 : u256.run b7 = some (r, b8))
    (h8 : u256.run b8 = some (s, b9)) :
    (body 0).run b0 = some (⟨0, (legacyV vr).1, n, gp, none, gl, to, val, d, [], [], 0, [],
      (legacyV vr).2, r, s⟩, b9) := by
  simp only [body, StateT.run_bind, h0, h1, h2, h3, h4, h5, h6, h7, h8, Option.bind_eq_bind,
    Option.bind_some]
  rfl

/-- The typed head's run (`maxPriorityFee` read when `pr`). -/
theorem head_run {pr : Bool} {b0 b1 b2 b3 b4 b5 b6 b7 b8 : List Byte} {c n gl val : Nat}
    {pf : Option Nat} {gp : Nat} {to : Option (List Byte)} {d : List Byte}
    (h0 : u64.run b0 = some (c, b1)) (h1 : nonce.run b1 = some (n, b2))
    (hpf : (if pr then (some <$> u128 : P (Option Nat)) else pure none).run b2 = some (pf, b3))
    (h3 : u128.run b3 = some (gp, b4)) (h4 : u64.run b4 = some (gl, b5))
    (h5 : addr.run b5 = some (to, b6)) (h6 : u256.run b6 = some (val, b7))
    (h7 : bytesView.run b7 = some (d, b8)) :
    (typedHead pr).run b0 = some ((c, n, pf, gp, gl, to, val, d), b8) := by
  cases pr
  · simp only [Bool.false_eq_true, if_false, StateT.run_pure] at hpf
    obtain ⟨rfl, rfl⟩ := hpf
    simp [typedHead, StateT.run_bind, h0, h1, h3, h4, h5, h6, h7]
  · simp only [if_true, StateT.run_map] at hpf
    cases hu : u128.run b2 with
    | none => simp [hu] at hpf
    | some q =>
      obtain ⟨q1, q2⟩ := q
      simp only [hu] at hpf
      obtain ⟨rfl, rfl⟩ := hpf
      simp [typedHead, StateT.run_bind, StateT.run_map, h0, h1, hu, h3, h4, h5, h6, h7]

theorem body_typed {t : Nat} (ht : t = 1 ∨ t = 2) {b0 b8 b9 b10 b11 b12 : List Byte}
    {c n gl val gp v r s : Nat} {pf : Option Nat} {to : Option (List Byte)} {d : List Byte}
    {al : List TX.EntryValue}
    (hh : (typedHead (t == 2)).run b0 = some ((c, n, pf, gp, gl, to, val, d), b8))
    (h8 : accessList.run b8 = some (al, b9)) (h9 : u64.run b9 = some (v, b10))
    (h10 : u256.run b10 = some (r, b11)) (h11 : u256.run b11 = some (s, b12)) :
    (body t).run b0 = some (⟨t, some c, n, gp, pf, gl, to, val, d, al, [], 0, [], v, r, s⟩,
      b12) := by
  rcases ht with rfl | rfl
  all_goals
    simp only [body, StateT.run_bind, hh, h8, h9, h10, h11, Option.bind_eq_bind, Option.bind_some]
    rfl

theorem body_blob {b0 b8 b9 b10 b11 b12 b13 b14 : List Byte}
    {c n gl val gp bf v r s : Nat} {pf : Option Nat} {to : Option (List Byte)} {d : List Byte}
    {al : List TX.EntryValue} {bh : List (List Byte)}
    (hh : (typedHead true).run b0 = some ((c, n, pf, gp, gl, to, val, d), b8))
    (h8 : accessList.run b8 = some (al, b9)) (h9 : u128.run b9 = some (bf, b10))
    (h10 : hashList.run b10 = some (bh, b11)) (h11 : u64.run b11 = some (v, b12))
    (h12 : u256.run b12 = some (r, b13)) (h13 : u256.run b13 = some (s, b14)) :
    (body 3).run b0 = some (⟨3, some c, n, gp, pf, gl, to, val, d, al, bh, bf, [], v, r, s⟩,
      b14) := by
  simp only [body, StateT.run_bind, hh, h8, h9, h10, h11, h12, h13, Option.bind_eq_bind,
    Option.bind_some]
  rfl

theorem body_auth {b0 b8 b9 b10 b11 b12 b13 : List Byte}
    {c n gl val gp v r s : Nat} {pf : Option Nat} {to : Option (List Byte)} {d : List Byte}
    {al : List TX.EntryValue} {au : List Auth}
    (hh : (typedHead true).run b0 = some ((c, n, pf, gp, gl, to, val, d), b8))
    (h8 : accessList.run b8 = some (al, b9)) (h9 : authList.run b9 = some (au, b10))
    (h10 : u64.run b10 = some (v, b11)) (h11 : u256.run b11 = some (r, b12))
    (h12 : u256.run b12 = some (s, b13)) :
    (body 4).run b0 = some (⟨4, some c, n, gp, pf, gl, to, val, d, al, [], 0, au, v, r, s⟩,
      b13) := by
  simp only [body, StateT.run_bind, hh, h8, h9, h10, h11, h12, Option.bind_eq_bind,
    Option.bind_some]
  rfl

theorem decode_of_run {t : Nat} {b r : List Byte} {tx : Tx} (h : (body t).run b = some (tx, r)) :
    decode t b = some tx := by
  simp only [decode, StateT.run', StateT.run] at h ⊢
  rw [h]
  rfl

/-! ## `body t` on checked items -/

theorem checksL_cons {ch : Chk} {chs : List Chk} {b : List Byte} (h : ChecksL (ch :: chs) b) :
    TX.HeaderFits b ∧ ch.Ok b ∧ ChecksL chs (restOf b) := by
  obtain ⟨hf, hok, htl⟩ := h
  obtain ⟨l, hh, p, hd⟩ := chk_decodes hok
  refine ⟨hf, hok, ?_⟩
  rw [restOf, hdOf_eq hd]
  exact htl l hh p hd

/-- The bytes after `n` items. -/
def restN : Nat → List Byte → List Byte
  | 0, b => b
  | n + 1, b => restN n (restOf b)

theorem checksL_append : ∀ {chs chs' : List Chk} {b : List Byte},
    ChecksL (chs ++ chs') b → ChecksL chs b ∧ ChecksL chs' (restN chs.length b)
  | [], _, _, h => ⟨trivial, h⟩
  | ch :: chs, chs', b, h => by
    obtain ⟨hf, hok, htl⟩ := h
    obtain ⟨l, hh, p, hd⟩ := chk_decodes hok
    obtain ⟨h1, h2⟩ := checksL_append (htl l hh p hd)
    refine ⟨⟨hf, hok, fun l' h' p' hd' => ?_⟩, ?_⟩
    · rw [hd] at hd'
      cases hd'
      exact h1
    · simp only [List.length_cons, restN]
      rw [restOf, hdOf_eq hd]
      exact h2

/-- The item values of the typed head at `b`. -/
def headOf (pr : Bool) (b : List Byte) :
    Nat × Nat × Option Nat × Nat × Nat × Option (List Byte) × Nat × List Byte :=
  let b1 := restOf b; let b2 := restOf b1
  let b3 := if pr then restOf b2 else b2
  let b4 := restOf b3; let b5 := restOf b4; let b6 := restOf b5; let b7 := restOf b6
  (numOf 8 b, numOf 8 b1, if pr then some (numOf 16 b2) else none, numOf 16 b3, numOf 8 b4,
    addrOf b5, numOf 32 b6, payOf b7)

/-- The bytes after the typed head at `b`. -/
def headRest (pr : Bool) (b : List Byte) : List Byte :=
  let b2 := restOf (restOf b)
  let b3 := if pr then restOf b2 else b2
  restOf (restOf (restOf (restOf (restOf b3))))

theorem head_checked {pr : Bool} {b : List Byte} (h : ChecksL (headChecks pr) b) :
    (typedHead pr).run b = some (headOf pr b, headRest pr b) := by
  cases pr
  · simp only [headChecks, Bool.false_eq_true, if_false] at h
    obtain ⟨f0, k0, h⟩ := checksL_cons h
    obtain ⟨f1, k1, h⟩ := checksL_cons h
    obtain ⟨f3, k3, h⟩ := checksL_cons h
    obtain ⟨f4, k4, h⟩ := checksL_cons h
    obtain ⟨f5, k5, h⟩ := checksL_cons h
    obtain ⟨f6, k6, h⟩ := checksL_cons h
    obtain ⟨f7, k7, -⟩ := checksL_cons h
    exact head_run (stepV_u64 _ f0 k0) (stepV_nonce _ f1 k1) (by simp [StateT.run_pure])
      (stepV_u128 _ f3 k3) (stepV_u64 _ f4 k4) (stepV_addr _ f5 k5) (stepV_u256 _ f6 k6)
      (stepV_bytesView _ f7 k7)
  · simp only [headChecks, if_true] at h
    obtain ⟨f0, k0, h⟩ := checksL_cons h
    obtain ⟨f1, k1, h⟩ := checksL_cons h
    obtain ⟨f2, k2, h⟩ := checksL_cons h
    obtain ⟨f3, k3, h⟩ := checksL_cons h
    obtain ⟨f4, k4, h⟩ := checksL_cons h
    obtain ⟨f5, k5, h⟩ := checksL_cons h
    obtain ⟨f6, k6, h⟩ := checksL_cons h
    obtain ⟨f7, k7, -⟩ := checksL_cons h
    have hpf : (if true = true then (some <$> u128 : P (Option Nat)) else pure none).run
        (restOf (restOf b)) =
        some (some (numOf 16 (restOf (restOf b))), restOf (restOf (restOf b))) := by
      simp [StateT.run_map, stepV_u128 _ f2 k2]
    rw [head_run (stepV_u64 _ f0 k0) (stepV_nonce _ f1 k1) hpf (stepV_u128 _ f3 k3)
      (stepV_u64 _ f4 k4) (stepV_addr _ f5 k5) (stepV_u256 _ f6 k6) (stepV_bytesView _ f7 k7)]
    simp only [headOf, headRest, if_true]

/-- The legacy transaction the nine items at `b` make. -/
def legacyOf (b : List Byte) : Tx :=
  let b1 := restOf b; let b2 := restOf b1; let b3 := restOf b2; let b4 := restOf b3
  let b5 := restOf b4; let b6 := restOf b5; let b7 := restOf b6; let b8 := restOf b7
  ⟨0, (legacyV (numOf 32 b6)).1, numOf 8 b, numOf 16 b1, none, numOf 8 b2, addrOf b3,
    numOf 32 b4, payOf b5, [], [], 0, [], (legacyV (numOf 32 b6)).2, numOf 32 b7, numOf 32 b8⟩

theorem decode_legacy {b : List Byte} (h : ChecksL (armChecks 0) b) :
    decode 0 b = some (legacyOf b) := by
  simp only [armChecks] at h
  obtain ⟨f0, k0, h⟩ := checksL_cons h
  obtain ⟨f1, k1, h⟩ := checksL_cons h
  obtain ⟨f2, k2, h⟩ := checksL_cons h
  obtain ⟨f3, k3, h⟩ := checksL_cons h
  obtain ⟨f4, k4, h⟩ := checksL_cons h
  obtain ⟨f5, k5, h⟩ := checksL_cons h
  obtain ⟨f6, k6, h⟩ := checksL_cons h
  obtain ⟨f7, k7, h⟩ := checksL_cons h
  obtain ⟨f8, k8, -⟩ := checksL_cons h
  have := body_legacy (stepV_nonce _ f0 k0) (stepV_u128 _ f1 k1) (stepV_u64 _ f2 k2)
    (stepV_addr _ f3 k3) (stepV_u256 _ f4 k4) (stepV_bytesView _ f5 k5) (stepV_u256 _ f6 k6)
    (stepV_u256 _ f7 k7) (stepV_u256 _ f8 k8)
  exact decode_of_run this

/-- The EIP-2930/1559 transaction the items at `b` make. -/
def typedOf (t : Nat) (b : List Byte) : Tx :=
  let hd := headOf (t == 2) b
  let b8 := headRest (t == 2) b; let b9 := restOf b8; let b10 := restOf b9; let b11 := restOf b10
  ⟨t, some hd.1, hd.2.1, hd.2.2.2.1, hd.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2, alOf b8, [], 0, [], numOf 8 b9, numOf 32 b10, numOf 32 b11⟩

theorem decode_typed {t : Nat} (ht : t = 1 ∨ t = 2) {b : List Byte}
    (h : ChecksL (armChecks t) b) : decode t b = some (typedOf t b) := by
  have hsplit : armChecks t = headChecks (t == 2) ++ [.al, .le 8, .le 32, .le 32] := by
    rcases ht with rfl | rfl <;> rfl
  rw [hsplit] at h
  obtain ⟨hh, h⟩ := checksL_append h
  have hr : restN (headChecks (t == 2)).length b = headRest (t == 2) b := by
    cases (t == 2) <;> rfl
  rw [hr] at h
  obtain ⟨f8, k8, h⟩ := checksL_cons h
  obtain ⟨f9, k9, h⟩ := checksL_cons h
  obtain ⟨f10, k10, h⟩ := checksL_cons h
  obtain ⟨f11, k11, -⟩ := checksL_cons h
  have := body_typed ht (head_checked hh) (stepV_accessList _ f8 k8) (stepV_u64 _ f9 k9)
    (stepV_u256 _ f10 k10) (stepV_u256 _ f11 k11)
  exact decode_of_run this

end ZesuExec.Fn.DTF
