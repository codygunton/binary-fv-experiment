import ZesuExec.Fn.DTF.Keep

/-!
# DTF: the typed head and `txAccessList`'s precondition (programme plan S7 step 4)

`al_input`: when the typed head's items (`armChecks t` before the access list) pass their checks
and fit (`Fits`), the reference decoder's `accessListInput` is the payload after them, the slice
the binary hands `txAccessList`; with `Domain`'s first conjunct that is TX's `Domain`.
`tx_pre_dtf` builds `TX.Pre` at a call site from the site's shape (result and `rest` slots in the
frame below the save area, `sp = fr`), the `rest` slice after the head and DTF's live list.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- The item after `k` top-level items fits (`Fits`'s `ItemsFit`, `k` below its count). -/
theorem fits_at {inner : List Byte → Prop} : ∀ {k n : Nat} {b : List Byte} {c : Nat},
    ItemsFit inner n b → skip k b = some c → k < n → TX.HeaderFits (b.drop c)
  | 0, _ + 1, b, c, hf, hs, _ => by
    simp only [skip, Option.some.injEq] at hs; subst hs; exact hf.1
  | k + 1, n + 1, b, c, hf, hs, hk => by
    simp only [skip] at hs
    split at hs
    · next l h p hd =>
      obtain ⟨c', h', rfl⟩ := Option.map_eq_some_iff.mp hs
      simp only [ItemsFit, hd] at hf
      have := fits_at hf.2.2 h' (by omega)
      rwa [TX.itemRest, List.drop_drop] at this
    · cases hs
  | _, 0, _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)

/-! ## Field parsers on checked items -/

/-- Each item of `b` with its check, front to back: the header fits, the check passes, and the
items after it pass theirs. -/
def ChecksL : List Chk → List Byte → Prop
  | [], _ => True
  | ch :: chs, b => TX.HeaderFits b ∧ ch.Ok b ∧
      ∀ l h p, F2.decode b = .success l h p → ChecksL chs (TX.itemRest b h p)

/-- `x` reads exactly the items `chs` describe: on checked items it succeeds and leaves the bytes
after them. -/
def Reads {α : Type} (x : P α) (chs : List Chk) : Prop :=
  ∀ b c, ChecksL chs b → skip chs.length b = some c → ∃ v, x.run b = some (v, b.drop c)

/-- `x` reads one item checked by `ch`. -/
def StepOk {α : Type} (x : P α) (ch : Chk) : Prop :=
  ∀ b, TX.HeaderFits b → ch.Ok b →
    ∃ l h p, F2.decode b = .success l h p ∧ ∃ v, x.run b = some (v, TX.itemRest b h p)

theorem reads_pure {α : Type} (a : α) : Reads (pure a : P α) [] := by
  intro b c _ hs
  simp only [List.length_nil, skip, Option.some.injEq] at hs
  subst hs
  exact ⟨a, by simp [StateT.run_pure]⟩

theorem reads_bind {α β : Type} {x : P α} {f : α → P β} {ch : Chk} {chs : List Chk}
    (hx : StepOk x ch) (hf : ∀ a, Reads (f a) chs) : Reads (x >>= f) (ch :: chs) := by
  intro b c hck hs
  obtain ⟨hfit, hok, htl⟩ := hck
  obtain ⟨l, h, p, hd, v, hxv⟩ := hx b hfit hok
  simp only [List.length_cons, skip, hd] at hs
  obtain ⟨c', hs', rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨u, hu⟩ := hf v _ c' (htl l h p hd) hs'
  refine ⟨u, ?_⟩
  simp only [StateT.run_bind, hxv, Option.bind_eq_bind, Option.bind_some]
  rw [hu, TX.itemRest, List.drop_drop]

theorem stepOk_map {α β : Type} {x : P α} {ch : Chk} (g : α → β) (hx : StepOk x ch) :
    StepOk (g <$> x) ch := by
  intro b hf hok
  obtain ⟨l, h, p, hd, v, hv⟩ := hx b hf hok
  exact ⟨l, h, p, hd, g v, by simp [StateT.run_map, hv]⟩

theorem item_run {b : List Byte} {l : Bool} {h p : Nat} (hd : F2.decode b = .success l h p) :
    item.run b = some ((l, TX.itemPayload b h p), TX.itemRest b h p) := by
  simp only [StateT.run, item, hd]

theorem payload_length {b : List Byte} {l : Bool} {h p : Nat} (hf : TX.HeaderFits b)
    (hd : F2.decode b = .success l h p) : (TX.itemPayload b h p).length = p := by
  obtain ⟨-, hle, -⟩ := TX.fits_bounds hf hd
  simp only [TX.itemPayload, List.length_take, List.length_drop]
  omega

/-- A string item: `bytesView` gives its payload. -/
theorem bytesView_run {b : List Byte} {h p : Nat} (hd : F2.decode b = .success false h p) :
    bytesView.run b = some (TX.itemPayload b h p, TX.itemRest b h p) := by
  simp only [bytesView, StateT.run_bind, item_run hd, Option.bind_eq_bind, Option.bind_some]
  rfl

theorem step_bytesView : StepOk bytesView .str := by
  rintro b - ⟨h, p, hd⟩
  exact ⟨false, h, p, hd, _, bytesView_run hd⟩

theorem step_u64 : StepOk u64 (.le 8) := by
  rintro b hf ⟨h, p, hd, hp⟩
  refine ⟨false, h, p, hd, ?_⟩
  simp only [u64, StateT.run_bind, bytesView_run hd, Option.bind_eq_bind, Option.bind_some,
    payload_length hf hd, show ¬ p > 8 by omega, if_false]
  exact ⟨_, rfl⟩

theorem step_nonce : StepOk nonce .str := by
  rintro b - ⟨h, p, hd⟩
  refine ⟨false, h, p, hd, ?_⟩
  simp only [nonce, StateT.run_bind, bytesView_run hd, Option.bind_eq_bind, Option.bind_some]
  exact ⟨_, rfl⟩

theorem step_u128 : StepOk u128 .str := by
  rintro b - ⟨h, p, hd⟩
  refine ⟨false, h, p, hd, ?_⟩
  simp only [u128, StateT.run_bind, bytesView_run hd, Option.bind_eq_bind, Option.bind_some]
  exact ⟨_, rfl⟩

theorem step_u256 : StepOk u256 (.le 32) := by
  rintro b hf ⟨h, p, hd, hp⟩
  refine ⟨false, h, p, hd, ?_⟩
  simp only [u256, StateT.run_bind, bytesView_run hd, Option.bind_eq_bind, Option.bind_some,
    payload_length hf hd, show ¬ p > 32 by omega, if_false]
  exact ⟨_, rfl⟩

theorem step_addr : StepOk addr .addr := by
  rintro b hf ⟨h, p, hd, hp⟩
  refine ⟨false, h, p, hd, ?_⟩
  have hl := payload_length hf hd
  simp only [addr, StateT.run_bind, item_run hd, Option.bind_eq_bind, Option.bind_some]
  rcases hp with rfl | rfl
  · exact ⟨none, by simp [hl]⟩
  · exact ⟨some (TX.itemPayload b h 20), by simp [hl]⟩

/-! ## The typed head -/

/-- The checks of the typed head's items (`armChecks t` before the access list). -/
def headChecks (priority : Bool) : List Chk :=
  if priority then [.le 8, .str, .str, .str, .le 8, .addr, .le 32, .str]
  else [.le 8, .str, .str, .le 8, .addr, .le 32, .str]

theorem head_reads (pr : Bool) : Reads (typedHead pr) (headChecks pr) := by
  cases pr
  · simp only [typedHead, headChecks, Bool.false_eq_true, if_false, pure_bind]
    exact reads_bind step_u64 fun _ => reads_bind step_nonce fun _ =>
      reads_bind step_u128 fun _ => reads_bind step_u64 fun _ => reads_bind step_addr fun _ =>
      reads_bind step_u256 fun _ => reads_bind step_bytesView fun _ => reads_pure _
  · simp only [typedHead, headChecks, if_true, bind_map_left]
    exact reads_bind step_u64 fun _ => reads_bind step_nonce fun _ =>
      reads_bind step_u128 fun _ => reads_bind step_u128 fun _ =>
      reads_bind step_u64 fun _ => reads_bind step_addr fun _ =>
      reads_bind step_u256 fun _ => reads_bind step_bytesView fun _ => reads_pure _

/-- The access list's item index: after the typed head. -/
def alIdx (t : Nat) : Nat := if t = 1 then 7 else 8

theorem headChecks_eq {t : Nat} (h1 : 1 ≤ t) (h4 : t ≤ 4) :
    headChecks (t == 2 || 3 ≤ t) = (armChecks t).take (alIdx t) := by
  obtain rfl | rfl | rfl | rfl : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
  all_goals rfl

/-- `ChecksL` from the checks stated per index (`ChecksOk`'s form) and the header fits. -/
theorem checksL_of : ∀ {chs : List Chk} {b : List Byte},
    (∀ i < chs.length, ∀ c, skip i b = some c → TX.HeaderFits (b.drop c)) →
    (∀ i < chs.length, ∀ c, skip i b = some c → ∀ ch, chs[i]? = some ch → ch.Ok (b.drop c)) →
    ChecksL chs b
  | [], _, _, _ => trivial
  | ch :: chs, b, hf, hk => by
    refine ⟨by simpa using hf 0 (by simp) 0 rfl, by simpa using hk 0 (by simp) 0 rfl ch rfl,
      fun l h p hd => checksL_of (fun i hi c hs => ?_) (fun i hi c hs ch' hch => ?_)⟩
    · have := hf (i + 1) (by simp; omega) (TX.itemConsumed h p + c)
        (by simp only [skip, hd]; rw [← TX.itemRest, hs]; rfl)
      rwa [TX.itemRest, List.drop_drop]
    · have := hk (i + 1) (by simp; omega) (TX.itemConsumed h p + c)
        (by simp only [skip, hd]; rw [← TX.itemRest, hs]; rfl) ch'
        (by simpa using hch)
      rwa [TX.itemRest, List.drop_drop]

/-- The typed head's checked items leave `accessListInput` the payload after them. -/
theorem al_input {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (h1 : 1 ≤ σ.t)
    (hchk : ChecksOk σ (alIdx σ.t)) {c : Nat} (hs : skip (alIdx σ.t) σ.payload = some c) :
    accessListInput σ.t σ.payload = some (σ.payload.drop c) := by
  have h4 : σ.t ≤ 4 := hpre.2.2.2.2.2.2.2.2.2.1
  have hidx : alIdx σ.t ≤ (armChecks σ.t).length := by
    obtain h | h | h | h : σ.t = 1 ∨ σ.t = 2 ∨ σ.t = 3 ∨ σ.t = 4 := by omega
    all_goals simp only [alIdx, h]; decide
  have hlen : ((armChecks σ.t).take (alIdx σ.t)).length = alIdx σ.t := by
    simp only [List.length_take]; omega
  have hck : ChecksL ((armChecks σ.t).take (alIdx σ.t)) σ.payload := by
    refine checksL_of (fun i hi c hs => ?_) (fun i hi c hs ch hch => ?_)
    · have hfit := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
      refine fits_at hfit hs ?_
      rw [hlen] at hi
      obtain h | h | h | h : σ.t = 1 ∨ σ.t = 2 ∨ σ.t = 3 ∨ σ.t = 4 := by omega
      all_goals simp [alIdx, fieldCount, h] at hi ⊢ <;> omega
    · rw [hlen] at hi
      rw [List.getElem?_take, if_pos hi] at hch
      exact hchk i hi c hs ch hch
  rw [← headChecks_eq h1 h4] at hck hlen
  obtain ⟨v, hv⟩ := head_reads _ _ c hck (by rw [hlen]; exact hs)
  unfold accessListInput
  rw [if_neg (by omega)]
  simp only [StateT.run', SeqRight.seqRight]
  change Option.map _ (StateT.run (typedHead _ >>= fun _ => get) σ.payload) = _
  rw [StateT.run_bind, hv]
  rfl

end ZesuExec.Fn.DTF
