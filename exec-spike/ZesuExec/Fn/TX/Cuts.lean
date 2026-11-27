import ZesuExec.Fn.TX.Runs
import ZesuExec.Fn.F0.Proof
import ZesuExec.Fn.F1.Proof
import ZesuExec.Fn.F2.Proof
import ZesuExec.Fn.F4.Proof
import ZesuExec.Fn.F5.Proof
import ZesuExec.Vc.Tactics

/-!
# TX cut assertions, callees, budgets and plan (programme plan S6 steps 3-5)

`σ` = `Sig`: the allocator assumptions, the parameters (`input`, `L`) and the entry machine.
Everything an assertion says about the entry is read off `σ.m`: `S` = the entry `sp`,
`res`/`ao`/`rest` = `a0`/`a1`/`a2`, `inp`/`len` = the two words of `rest`.

Assertions (`OPEN/TX/CUTS.md`):
* the entry: `σ.m` itself with `Pre`;
* the loop heads `0x800000c4`, `0x8000018c` and the store sites `0x80000230`, `0x80000460`: the
  common facts `Common` (registers `sp`, `s0`, `s1`, `s2`, `s3`, the saved registers, the frame
  `SameOutside` from the entry, presence), the walk state `OuterOk` (`txAccessListOuterWalked`
  over `entriesWalk`), the entries list `EList`, the live list `Live`, and for the keys loop
  `KeysOk` (`txAccessListKeysWalked` over `keysWalk`) and the keys list `KList`;
* a call return site: the call-site predicate of the call that returns there, at the machine of
  the call, and the callee's `Post` from that machine (`∃ mc, Site mc ∧ Post mc m`). Its `CutOK`
  and the leaves of its segment read the callee's effect out of `Post`; the leaf that makes the
  call proves `Site`. `0x8000042c` is also reached from `0x80000400` without the `free` call
  (old capacity 0), so its assertion is a disjunction.

Budgets: `32` instructions per outer payload byte still ahead of the current read position plus
a constant per cut (derivation in `OPEN/TX/CUTS.md`, section Budgets, revised: the keys loop
also counts 32 per byte, an accepted key costs 319 ≤ 32 · 33).
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Parameters and the entry's shape -/

structure Sig where
  A : AllocAssumptions zesuImage
  g : Params
  m : Machine

abbrev w (n : Nat) : Word := BitVec.ofNat 64 n

namespace Sig
variable (σ : Sig)
abbrev res : Word := σ.m.reg 10
abbrev ao : Word := σ.m.reg 11
abbrev rest : Word := σ.m.reg 12
abbrev S : Word := σ.m.reg 2
abbrev inp : Word := wordAt σ.m σ.rest
abbrev len : Nat := (wordAt σ.m (σ.rest + 8)).toNat
/-- The frame slot `S - k`. -/
abbrev sl (k : Nat) : Word := σ.S - w k
abbrev input : List Byte := σ.g.input
end Sig

/-- Region bases and sizes, indices as in `Regions.lean`. -/
def shapeOf (σ : Sig) : List (Word × Nat) :=
  [(σ.sl frameBytes, frameBytes), (σ.res, 24), (σ.rest, 16), (σ.ao, 16), (σ.inp, σ.len)]

def envB (σ : Sig) (m : Machine) : Env := entryEnv m (shapeOf σ)

/-- With `var 40` = the payload word at `S - k` minus the input pointer. -/
def envP (k : Nat) (σ : Sig) (m : Machine) : Env :=
  (envB σ m).setVars 40 fun _ => wordAt m (σ.sl k) - σ.inp

/-- With region 5 = `n` bytes at `a0`. -/
def envS (n : Nat) (σ : Sig) (m : Machine) : Env := entryEnv m (shapeOf σ ++ [(m.reg 10, n)])

/-! ## The walk (`TxAccessListLoopFacts.v:19-36`) -/

/-- Every `decodeItem` call the outer walk of `win` reaches has a header that does not wrap
(`accessListHeadersFit` for the rest of the walk, from `Domain`). -/
def WalkFits (win : List Byte) : Prop := ∀ c ∈ (entriesWalk win.length win).1, HeaderFits c.2

/-- The same for the keys walk of `kw`. -/
def KeysFits (kw : List Byte) : Prop := ∀ c ∈ (keysWalk kw.length kw).1, HeaderFits c.2

/-- `txAccessListOuterWalked` over the outer payload `pl`: `done` are the entries before offset
`i`, the walk of the whole payload is `done` followed by the walk of the rest, and the rest's
calls fit. -/
def OuterWalked (pl : List Byte) (i : Nat) (done : List EntryValue) : Prop :=
  i ≤ pl.length ∧
  (entriesWalk pl.length pl).2 = ((entriesWalk (pl.drop i).length (pl.drop i)).2).map (done ++ ·) ∧
  WalkFits (pl.drop i)

/-- `txAccessListKeysWalked` over the keys payload `kp`, with the rest's calls fitting. -/
def KeysWalked (kp : List Byte) (j : Nat) (doneKeys : List (List Byte)) : Prop :=
  j ≤ kp.length ∧
  (keysWalk kp.length kp).2 = ((keysWalk (kp.drop j).length (kp.drop j)).2).map (doneKeys ++ ·) ∧
  KeysFits (kp.drop j)

/-- A fitting header: `decodeItem`'s header plus payload is nonempty, lies in the input and does
not wrap. -/
theorem fits_bounds {xs : List Byte} (hf : HeaderFits xs) {b : Bool} {h q : Nat}
    (hd : F2.decode xs = .success b h q) : 0 < h + q ∧ h + q ≤ xs.length ∧ h + q < 2 ^ 64 := by
  cases xs with
  | nil => simp [F2.decode] at hd
  | cons x rest =>
    have hb : x.toNat < 256 := x.isLt
    simp only [HeaderFits, longLengthWidth] at hf
    simp only [F2.decode, F2.checkedPayload] at hd
    simp only [List.length_cons]
    repeat' (split at hd)
    all_goals first
      | (simp at hd; done)
      | (simp only [F2.Item.success.injEq] at hd
         obtain ⟨-, rfl, rfl⟩ := hd
         first
           | omega
           | (rename_i hc
              first
                | (rw [Nat.mod_eq_of_lt (by omega)] at hc; omega)
                | (rw [if_pos (by omega)] at hf; rw [Nat.mod_eq_of_lt (by omega)] at hc; omega)
                | (rw [if_neg (by omega), if_pos (by omega)] at hf
                   rw [Nat.mod_eq_of_lt (by omega)] at hc; omega)))

theorem fits_le {xs : List Byte} (hf : HeaderFits xs) {b : Bool} {h q : Nat}
    (hd : F2.decode xs = .success b h q) : h + q ≤ xs.length := (fits_bounds hf hd).2.1

/-- After a fitting item, the rest is shorter. -/
theorem fits_rest {xs : List Byte} (hf : HeaderFits xs) {b : Bool} {h q : Nat}
    (hd : F2.decode xs = .success b h q) :
    itemRest xs h q = xs.drop (h + q) ∧ (itemRest xs h q).length < xs.length := by
  obtain ⟨h0, h1, h2⟩ := fits_bounds hf hd
  have : itemRest xs h q = xs.drop (h + q) := by simp only [itemRest, itemConsumed, Nat.mod_eq_of_lt h2]
  refine ⟨this, ?_⟩
  rw [this, List.length_drop]; omega

/-- The keys walk does not depend on its fuel once it covers the input and the calls fit. -/
theorem keysWalk_fuel : ∀ (n : Nat) (xs : List Byte), xs.length ≤ n → ∀ f g, xs.length ≤ f →
    xs.length ≤ g → (∀ c ∈ (keysWalk f xs).1, HeaderFits c.2) → keysWalk f xs = keysWalk g xs := by
  intro n
  induction n with
  | zero =>
    intro xs hn f g _ _ _
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; cases f <;> cases g <;> rfl
  | succ n ih =>
    intro xs hn f g hf hg hfit
    cases xs with
    | nil => cases f <;> cases g <;> rfl
    | cons x r =>
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by simp at hg; omega⟩
    have hx : HeaderFits (x :: r) := hfit (keyCall, x :: r) (by
      simp only [keysWalk]; split
      · split <;> simp
      · simp)
    cases hd : F2.decode (x :: r) with
    | error => simp only [keysWalk, hd]
    | success b h q =>
      cases b with
      | true => simp only [keysWalk, hd]
      | false =>
        by_cases h32 : q = 32
        · subst h32
          obtain ⟨-, hlt⟩ := fits_rest hx hd
          have ht : ∀ c ∈ (keysWalk f (itemRest (x :: r) h 32)).1, HeaderFits c.2 := fun c hc =>
            hfit c (by simp only [keysWalk, hd, if_true, List.mem_cons]; exact .inr hc)
          have he := ih (itemRest (x :: r) h 32) (by simp at hn hlt ⊢; omega) f g
            (by simp at hf hlt ⊢; omega) (by simp at hg hlt ⊢; omega) ht
          simp only [keysWalk, hd, if_true, he]
        · simp only [keysWalk, hd, h32, if_false]

/-- The outer walk does not depend on its fuel once it covers the input and the calls fit. -/
theorem entriesWalk_fuel : ∀ (n : Nat) (xs : List Byte), xs.length ≤ n → ∀ f g, xs.length ≤ f →
    xs.length ≤ g → (∀ c ∈ (entriesWalk f xs).1, HeaderFits c.2) →
    entriesWalk f xs = entriesWalk g xs := by
  intro n
  induction n with
  | zero =>
    intro xs hn f g _ _ _
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; cases f <;> cases g <;> rfl
  | succ n ih =>
    intro xs hn f g hf hg hfit
    cases xs with
    | nil => cases f <;> cases g <;> rfl
    | cons x r =>
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by simp at hg; omega⟩
    have hx : HeaderFits (x :: r) := hfit (entryCall, x :: r) (by
      simp only [entriesWalk]; split
      · split <;> simp
      · simp)
    cases hd : F2.decode (x :: r) with
    | error => simp only [entriesWalk, hd]
    | success b h q =>
      cases b with
      | false => simp only [entriesWalk, hd]
      | true =>
        cases hr : (entryWalk (itemPayload (x :: r) h q)).2 with
        | none => simp only [entriesWalk, hd, hr]
        | some v =>
          obtain ⟨-, hlt⟩ := fits_rest hx hd
          have ht : ∀ c ∈ (entriesWalk f (itemRest (x :: r) h q)).1, HeaderFits c.2 := fun c hc =>
            hfit c (by simp only [entriesWalk, hd, hr, List.cons_append, List.mem_cons,
              List.mem_append]; exact .inr (.inr hc))
          have he := ih (itemRest (x :: r) h q) (by simp at hn hlt ⊢; omega) f g
            (by simp at hf hlt ⊢; omega) (by simp at hg hlt ⊢; omega) ht
          simp only [entriesWalk, hd, hr, he]

/-! ### Fitting calls of a window -/

theorem walkFits_head {win : List Byte} (hf : WalkFits win) (hne : win ≠ []) :
    HeaderFits win := by
  obtain ⟨x, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact hf (entryCall, x :: r) (by
    simp only [List.length_cons, entriesWalk]; split
    · split <;> simp
    · simp)

/-- The calls of an entry the walk reaches fit. -/
theorem walkFits_entry {win : List Byte} (hf : WalkFits win) (hne : win ≠ []) {eh el : Nat}
    (hd : F2.decode win = .success true eh el) :
    ∀ c ∈ (entryWalk (itemPayload win eh el)).1, HeaderFits c.2 := by
  obtain ⟨x, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  intro c hc
  apply hf c
  simp only [List.length_cons, entriesWalk, hd]
  split <;> simp [hc]

/-- After an accepted entry, the rest of the window fits. -/
theorem walkFits_tail {win : List Byte} (hf : WalkFits win) (hne : win ≠ []) {eh el : Nat}
    (hd : F2.decode win = .success true eh el) {v : EntryValue}
    (hr : (entryWalk (itemPayload win eh el)).2 = some v) :
    WalkFits (itemRest win eh el) ∧
      entriesWalk win.length win = ((entryCall, win) :: (entryWalk (itemPayload win eh el)).1 ++
        (entriesWalk (itemRest win eh el).length (itemRest win eh el)).1,
        (entriesWalk (itemRest win eh el).length (itemRest win eh el)).2.map (v :: ·)) := by
  have hx := walkFits_head hf hne
  obtain ⟨-, hlt⟩ := fits_rest hx hd
  obtain ⟨x, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hw : entriesWalk (x :: r).length (x :: r) =
      ((entryCall, x :: r) :: (entryWalk (itemPayload (x :: r) eh el)).1 ++
        (entriesWalk r.length (itemRest (x :: r) eh el)).1,
        (entriesWalk r.length (itemRest (x :: r) eh el)).2.map (v :: ·)) := by
    simp only [List.length_cons, entriesWalk, hd, hr]
  have ht : ∀ c ∈ (entriesWalk r.length (itemRest (x :: r) eh el)).1, HeaderFits c.2 :=
    fun c hc => hf c (by rw [hw]; simp [hc])
  have he := entriesWalk_fuel _ (itemRest (x :: r) eh el) (Nat.le_refl _) r.length
    (itemRest (x :: r) eh el).length (by simp at hlt; omega) (Nat.le_refl _) ht
  rw [he] at hw ht
  exact ⟨ht, hw⟩

theorem keysFits_head {kw : List Byte} (hf : KeysFits kw) (hne : kw ≠ []) : HeaderFits kw := by
  obtain ⟨x, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact hf (keyCall, x :: r) (by
    simp only [List.length_cons, keysWalk]; split
    · split <;> simp
    · simp)

/-- After an accepted key, the rest of the keys window fits. -/
theorem keysFits_tail {kw : List Byte} (hf : KeysFits kw) (hne : kw ≠ []) {kh : Nat}
    (hd : F2.decode kw = .success false kh 32) :
    KeysFits (itemRest kw kh 32) ∧
      keysWalk kw.length kw = ((keyCall, kw) :: (keysWalk (itemRest kw kh 32).length
        (itemRest kw kh 32)).1, (keysWalk (itemRest kw kh 32).length
        (itemRest kw kh 32)).2.map (itemPayload kw kh 32 :: ·)) := by
  have hx := keysFits_head hf hne
  obtain ⟨-, hlt⟩ := fits_rest hx hd
  obtain ⟨x, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hw : keysWalk (x :: r).length (x :: r) =
      ((keyCall, x :: r) :: (keysWalk r.length (itemRest (x :: r) kh 32)).1,
        (keysWalk r.length (itemRest (x :: r) kh 32)).2.map (itemPayload (x :: r) kh 32 :: ·)) := by
    simp only [List.length_cons, keysWalk, hd, if_true]
  have ht : ∀ c ∈ (keysWalk r.length (itemRest (x :: r) kh 32)).1, HeaderFits c.2 :=
    fun c hc => hf c (by rw [hw]; simp [hc])
  have he := keysWalk_fuel _ (itemRest (x :: r) kh 32) (Nat.le_refl _) r.length
    (itemRest (x :: r) kh 32).length (by simp at hlt; omega) (Nat.le_refl _) ht
  rw [he] at hw ht
  exact ⟨ht, hw⟩

/-- The logical state of the outer walk. -/
structure Obs where
  /-- outer item header and payload length -/
  h : Nat
  p : Nat
  /-- payload bytes before the current entry -/
  i : Nat
  done : List EntryValue
  is : List EntryImage
  /-- entries list pointer and capacity -/
  ep : Word
  ec : Word

/-- The logical state inside one entry. -/
structure Kobs where
  eh : Nat
  el : Nat
  ah : Nat
  kh : Nat
  kl : Nat
  /-- keys payload bytes before the current key -/
  j : Nat
  keys : List (List Byte)
  kq : Word
  kc : Word

section
variable (σ : Sig) (o : Obs) (k : Kobs)

def pl : List Byte := itemPayload σ.input o.h o.p
/-- The remaining outer payload from the current entry on. -/
def win : List Byte := (pl σ o).drop o.i
def ent : List Byte := itemPayload (win σ o) k.eh k.el
def aft : List Byte := itemRest (ent σ o k) k.ah 20
def kpl : List Byte := itemPayload (aft σ o k) k.kh k.kl
/-- The remaining keys payload from the current key on. -/
def kwin : List Byte := (kpl σ o k).drop k.j

def curPtr : Word := σ.inp + w (o.h + o.i)
def entPtr : Word := curPtr σ o + w k.eh
def aftPtr : Word := entPtr σ o k + w (k.ah + 20)
def kplPtr : Word := aftPtr σ o k + w k.kh
def keyPtr : Word := kplPtr σ o k + w k.j

/-- The blocks of finished entries' keys slices. -/
def keysBlocks (es : List EntryValue) (is : List EntryImage) : List (Word × Nat) :=
  (List.zip es is).filterMap fun (e, i) =>
    if e.keys = [] then none else some (i.keysPtr, keySize * e.keys.length)

/-- TX's own live blocks: the entries buffer, the finished keys slices. -/
def EX : List (Word × Nat) :=
  (if 0 < o.ec.toNat then [(o.ep, entrySize * o.ec.toNat)] else []) ++ keysBlocks o.done o.is

/-- The current keys buffer. -/
def KX : List (Word × Nat) := if 0 < k.kc.toNat then [(k.kq, keySize * k.kc.toNat)] else []
end

/-! ## Common facts -/

def magic : Word := 0xffffffffcccccccd

/-- Register `k` of the save area `S - 8(k+1)`: `ra`, `s0`, `s1`, `s2`, …, `s11`. -/
def savedReg (k : Nat) : Fin 32 :=
  if k = 0 then 1 else if k = 1 then 8 else if k = 2 then 9 else Fin.ofNat 32 (k + 15)

/-- The caller's memory TX owns or may change: the result, `rest`, its stack, the scratch word. -/
def Owned (σ : Sig) (a : Word) : Prop :=
  InRange σ.res 24 a ∨ InRange σ.rest 16 a ∨ InRange (σ.sl stackBytes) stackBytes a ∨
    InRange scratch 8 a

/-- After the prologue. -/
def Common (σ : Sig) (m : Machine) : Prop :=
  σ.m.pc.toNat = entry ∧ Pre σ.A σ.g σ.m ∧ RodataLoaded zesuImage m ∧
  m.reg 2 = σ.sl frameBytes ∧ m.reg 8 = σ.S ∧ m.reg 9 = σ.res ∧ m.reg 18 = σ.ao ∧
  m.reg 19 = σ.m.reg 1 ∧
  (∀ k < 13, m.load (σ.sl (8 * (k + 1))) 8 = some (σ.m.reg (savedReg k))) ∧
  Present m (σ.sl stackBytes) stackBytes ∧ Present m σ.res 24 ∧ Present m σ.rest 16 ∧
  Present m scratch 8 ∧
  SameOutside (fun a => Owned σ a ∨ σ.A.Priv σ.g.L a) σ.m m

/-- The live list `L` is the caller's `g.L` and TX's blocks `X`, each carved from `Priv g.L`. -/
def Live (σ : Sig) (m : Machine) (L X : List (Word × Nat)) : Prop :=
  σ.A.Heap L m ∧ L.Perm (σ.g.L ++ X) ∧
  ∀ b ∈ X, 0 < b.2 ∧ RamRange b.1 b.2 ∧ ∀ a, InRange b.1 b.2 a → σ.A.Priv σ.g.L a

/-- The outer item is a list `{h, p}`, `rest` advanced past it, the walk at offset `i`. -/
def OuterOk (σ : Sig) (m : Machine) (o : Obs) : Prop :=
  F2.decode σ.input = .success true o.h o.p ∧ o.h + o.p ≤ σ.len ∧
  m.load σ.rest 8 = some (σ.inp + w (o.h + o.p)) ∧
  m.load (σ.rest + 8) 8 = some (w σ.len - w (o.h + o.p)) ∧
  OuterWalked (pl σ o) o.i o.done

/-- The entries list header `S-0x1c0` = `{ep, n, ec}`; its first `|done|` slots hold the
finished entries. -/
def EList (σ : Sig) (m : Machine) (o : Obs) (n : Nat) : Prop :=
  F1.HeaderIs m (σ.sl 0x1c0) o.ep (w n) o.ec ∧ o.done.length ≤ o.ec.toNat ∧ 0 < o.ep.toNat ∧
  (o.ec.toNat = 0 → o.ep = 8) ∧ o.ec.toNat < 2 ^ 32 ∧
  (0 < o.ec.toNat → RamRange o.ep (entrySize * o.ec.toNat)) ∧
  o.is.length = o.done.length ∧ BytesAt m o.ep (entriesBytes o.done o.is) ∧
  ∀ x ∈ List.zip o.done o.is, x.2.padding.length = 4 ∧ x.1.address.length = 20 ∧
    (∀ y ∈ x.1.keys, y.length = keySize) ∧
    (x.1.keys ≠ [] → RamRange x.2.keysPtr (keySize * x.1.keys.length)) ∧
    BytesAt m x.2.keysPtr x.1.keys.flatten

/-- The loop registers of the outer walk: cursor `s4`, bytes left `s5`, constants `s8 = 20`,
`s9 = 1`, `s11 = 32`; the magic multiplier spilled. -/
def OuterRegs (σ : Sig) (m : Machine) (o : Obs) : Prop :=
  m.reg 20 = curPtr σ o ∧ m.reg 21 = w (o.p - o.i) ∧ o.i < o.p ∧
  m.load (σ.sl 0x1f0) 8 = some magic

def Consts (m : Machine) : Prop := m.reg 24 = 20 ∧ m.reg 25 = 1 ∧ m.reg 27 = 32

/-- The current entry: a list `{eh, el}` at the cursor, `s10` = its size. -/
def EntryOk (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) : Prop :=
  F2.decode (win σ o) = .success true k.eh k.el ∧ k.eh + k.el ≤ o.p - o.i ∧
  m.reg 26 = w (k.eh + k.el)

/-- Its address: a 20-byte string, copied to `S-0x158`. -/
def AddrOk (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) : Prop :=
  F2.decode (ent σ o k) = .success false k.ah 20 ∧ k.ah + 20 ≤ k.el ∧
  BytesAt m (σ.sl 0x158) (itemPayload (ent σ o k) k.ah 20)

/-- Its keys list `{kh, kl}` after the address. -/
def KeysListOk (σ : Sig) (o : Obs) (k : Kobs) : Prop :=
  F2.decode (aft σ o k) = .success true k.kh k.kl ∧ k.ah + 20 + k.kh + k.kl ≤ k.el

/-- The keys list header `S-0x118` = `{kq, n, kc}` holding the keys so far. -/
def KList (σ : Sig) (m : Machine) (k : Kobs) (n : Nat) : Prop :=
  F1.HeaderIs m (σ.sl 0x118) k.kq (w n) k.kc ∧ k.keys.length ≤ k.kc.toNat ∧ 0 < k.kq.toNat ∧
  (k.kc.toNat = 0 → k.kq = 1) ∧ k.kc.toNat < 2 ^ 32 ∧
  (0 < k.kc.toNat → RamRange k.kq (keySize * k.kc.toNat)) ∧
  (∀ y ∈ k.keys, y.length = keySize) ∧ BytesAt m k.kq k.keys.flatten

/-- The keys walk at offset `j`: cursor `s7`, bytes left `s6`, keys so far `s8`. -/
def KeysOk (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) : Prop :=
  KeysWalked (kpl σ o k) k.j k.keys ∧ m.reg 23 = keyPtr σ o k ∧ m.reg 22 = w (k.kl - k.j) ∧
  m.reg 24 = w k.keys.length

/-- The walk state of an entry's keys loop (all but the loop registers). -/
def InEntry (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) (L : List (Word × Nat)) : Prop :=
  Common σ m ∧ OuterOk σ m o ∧ OuterRegs σ m o ∧ EList σ m o o.done.length ∧
  Live σ m L (EX o ++ KX k) ∧ EntryOk σ m o k ∧ AddrOk σ m o k ∧ KeysListOk σ o k ∧
  m.reg 27 = 32

/-! ## Cut assertions without a call before them -/

def AEntry (σ : Sig) (m : Machine) : Prop := m = σ.m ∧ m.pc.toNat = entry ∧ Pre σ.A σ.g m

/-- `0x800000c4` (`loop-c4`). -/
def OuterState (σ : Sig) (m : Machine) (o : Obs) (L : List (Word × Nat)) : Prop :=
  Common σ m ∧ OuterOk σ m o ∧ OuterRegs σ m o ∧ Consts m ∧ EList σ m o o.done.length ∧
    Live σ m L (EX o)

def AOuter (σ : Sig) (m : Machine) : Prop := m.pc.toNat = c0c4 ∧ ∃ o L, OuterState σ m o L

/-- `0x8000018c` (`loop-18c`): keys left. -/
def AKeys (σ : Sig) (m : Machine) : Prop :=
  m.pc.toNat = c18c ∧ ∃ o k L, InEntry σ m o k L ∧ KeysOk σ m o k ∧
    KList σ m k k.keys.length ∧ k.j < k.kl

/-- `0x80000230`: a key was accepted and the keys buffer has room; `a0` = its slot, `a1..a4`
the key's words, `s8` the new length (already stored), `s6` the bytes left after it, `s9` its
size. -/
def AKeyStore (σ : Sig) (m : Machine) : Prop :=
  m.pc.toNat = c230 ∧ ∃ (o : Obs) (k : Kobs) (L : List (Word × Nat)) (key : List Byte) (kh' : Nat),
    InEntry σ m o k L ∧ KeysWalked (kpl σ o k) k.j k.keys ∧ k.j < k.kl ∧
    F2.decode (kwin σ o k) = .success false kh' keySize ∧ k.j + kh' + keySize ≤ k.kl ∧
    key = itemPayload (kwin σ o k) kh' keySize ∧
    KList σ m k (k.keys.length + 1) ∧ k.keys.length + 1 ≤ k.kc.toNat ∧
    m.reg 10 = k.kq + w (keySize * k.keys.length) ∧
    BytesAt m (σ.sl 0xd8) key ∧
    (∀ t < 4, m.load (σ.sl 0xd8 + w (8 * t)) 8 = some (m.reg (Fin.ofNat 32 (11 + t)))) ∧
    m.reg 23 = keyPtr σ o k ∧ m.reg 22 = w (k.kl - k.j - (kh' + keySize)) ∧
    m.reg 25 = w (kh' + keySize) ∧ m.reg 24 = w (k.keys.length + 1)

/-- The finished entry value of the current entry, once its keys slice is `{kp', nk}`. -/
def entryValue (σ : Sig) (o : Obs) (k : Kobs) : EntryValue :=
  ⟨itemPayload (ent σ o k) k.ah 20, k.keys⟩

/-- `0x80000460`: the entry is finished and the entries buffer has room; `a0` = the slot of
entry `|done|`, `a4`/`a5` its keys slice `{kp', |keys|}`; the header already holds length
`|done| + 1`; copy B (`S-0xa0`) holds the address. -/
def AEntryStore (σ : Sig) (m : Machine) : Prop :=
  m.pc.toNat = c460 ∧ ∃ (o : Obs) (k : Kobs) (L : List (Word × Nat)) (kp' : Word),
    Common σ m ∧ OuterOk σ m o ∧ OuterRegs σ m o ∧ Consts m ∧
    EList σ m o (o.done.length + 1) ∧ o.done.length + 1 ≤ o.ec.toNat ∧
    Live σ m L (EX o ++ (if k.keys = [] then [] else [(kp', keySize * k.keys.length)])) ∧
    EntryOk σ m o k ∧ AddrOk σ m o k ∧ KeysListOk σ o k ∧
    KeysWalked (kpl σ o k) k.kl k.keys ∧
    (k.keys ≠ [] → RamRange kp' (keySize * k.keys.length)) ∧ BytesAt m kp' k.keys.flatten ∧
    (∀ y ∈ k.keys, y.length = keySize) ∧
    BytesAt m (σ.sl 0xa0) (itemPayload (ent σ o k) k.ah 20) ∧
    m.reg 10 = o.ep + w (entrySize * o.done.length) ∧ m.reg 14 = kp' ∧
    m.reg 15 = w k.keys.length

/-! ## Call sites: the machine at the call instruction -/

/-- The register facts of a call: arguments `a0..` and the return address. -/
def Args (m : Machine) (ret : Nat) (as : List Word) : Prop :=
  m.reg 1 = w ret ∧ ∀ t < as.length, m.reg (Fin.ofNat 32 (10 + t)) = as.getD t 0

/-- `+0x64`: `decodeItem(S-0x1e8, inp, len)`; `s6`/`s7`/`s8` = `rest`, `inp`, `len`. -/
def Site064 (σ : Sig) (m : Machine) : Prop :=
  Common σ m ∧ (∃ L, Live σ m L []) ∧
  m.load σ.rest 8 = some σ.inp ∧ m.load (σ.rest + 8) 8 = some (w σ.len) ∧
  m.reg 22 = σ.rest ∧ m.reg 23 = σ.inp ∧ m.reg 24 = w σ.len ∧
  Args m c068 [σ.sl 0x1e8, σ.inp, w σ.len]

/-- `+0xd4`: the entry item at the cursor. -/
def Site0d4 (σ : Sig) (m : Machine) : Prop :=
  ∃ o L, OuterState σ m o L ∧ Args m c0d8 [σ.sl 0x1a8, curPtr σ o, w (o.p - o.i)]

/-- The entry's facts before its keys: `s7`/`s6` the entry payload, `s10` its size. -/
def EntryState (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) (L : List (Word × Nat)) : Prop :=
  OuterState σ m o L ∧ EntryOk σ m o k

/-- `+0x108`: the address item at the start of the entry payload. -/
def Site108 (σ : Sig) (m : Machine) : Prop :=
  ∃ o k L, EntryState σ m o k L ∧ m.reg 23 = entPtr σ o k ∧ m.reg 22 = w k.el ∧
    Args m c10c [σ.sl 0x180, entPtr σ o k, w k.el]

/-- `+0x158`: the keys list after the address. -/
def Site158 (σ : Sig) (m : Machine) : Prop :=
  ∃ o k L, EntryState σ m o k L ∧ AddrOk σ m o k ∧
    Args m c15c [σ.sl 0x140, aftPtr σ o k, w (k.el - (k.ah + 20))]

/-- `+0x19c`: the key item at the keys cursor. -/
def Site19c (σ : Sig) (m : Machine) : Prop :=
  ∃ o k L, InEntry σ m o k L ∧ KeysOk σ m o k ∧ KList σ m k k.keys.length ∧ k.j < k.kl ∧
    Args m c1a0 [σ.sl 0x100, keyPtr σ o k, w (k.kl - k.j)]

/-- A 32-byte key at the keys cursor, copied to `S-0xd8`; `s9` = its size. -/
def KeyOk (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) (kh' : Nat) : Prop :=
  F2.decode (kwin σ o k) = .success false kh' keySize ∧ k.j + kh' + keySize ≤ k.kl ∧
  BytesAt m (σ.sl 0xd8) (itemPayload (kwin σ o k) kh' keySize) ∧ m.reg 25 = w (kh' + keySize)

/-- `+0x1f4`: `ensureTotalCapacity(K, ao, n + 1)`. -/
def Site1f4 (σ : Sig) (x : List (Word × Nat) × List Byte) (m : Machine) : Prop :=
  ∃ o k kh', InEntry σ m o k x.1 ∧ x.2 = k.keys.flatten ∧ KeysOk σ m o k ∧ KList σ m k k.keys.length ∧ k.j < k.kl ∧
    KeyOk σ m o k kh' ∧ Args m c1f8 [σ.sl 0x118, σ.ao, w (k.keys.length + 1)]

/-- `+0x258`: `toOwnedSlice(S-0xb8, K, ao)` once every key is in `K`. -/
def Site258 (σ : Sig) (x : List (Word × Nat) × List Byte) (m : Machine) : Prop :=
  ∃ o k, InEntry σ m o k x.1 ∧ x.2 = k.keys.flatten ∧ KeysWalked (kpl σ o k) k.kl k.keys ∧
    KList σ m k k.keys.length ∧ Args m c25c [σ.sl 0xb8, σ.sl 0x118, σ.ao]

/-- The keys slice of the finished entry. -/
def KD (k : Kobs) (kp' : Word) : List (Word × Nat) :=
  if k.keys = [] then [] else [(kp', keySize * k.keys.length)]

/-- The entry is finished: its keys slice `{kp', |keys|}` (F4's result), copies A and B hold
the address. -/
def EntryDone (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) (L : List (Word × Nat))
    (kp' : Word) (X : List (Word × Nat)) : Prop :=
  Common σ m ∧ OuterOk σ m o ∧ OuterRegs σ m o ∧ EList σ m o o.done.length ∧
  Live σ m L (EX o ++ KD k kp' ++ X) ∧ EntryOk σ m o k ∧ AddrOk σ m o k ∧ KeysListOk σ o k ∧
  KeysWalked (kpl σ o k) k.kl k.keys ∧
  (k.keys ≠ [] → RamRange kp' (keySize * k.keys.length)) ∧ BytesAt m kp' k.keys.flatten ∧
  (∀ y ∈ k.keys, y.length = keySize) ∧
  BytesAt m (σ.sl 0xa0) (itemPayload (ent σ o k) k.ah 20)

/-- Zig's growth `n + 1 + (n + 1) / 2 + 1` for a full list of `n` entries. -/
def grownCap (n : Nat) : Nat := n + 1 + (n + 1) / 2 + 1

/-- Growth of a full entries list: registers `s7 = n + 1`, `s9 = c'`, the spills
`S-0x200 = 32 n`, `S-0x1f8 = 8 n`, `S-0x210 = |keys|`, `S-0x208 = kp'`, `S-0x218` = the
allocator context, `S-0x220` = the vtable. (`s11 = ec` holds up to the `free` call, where the
leaf overwrites it; the call sites before it say so.) -/
def Growing (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) (kp' : Word) : Prop :=
  o.done.length = o.ec.toNat ∧
  m.reg 23 = w (o.done.length + 1) ∧ m.reg 25 = w (grownCap o.done.length) ∧
  m.load (σ.sl 0x200) 8 = some (w (32 * o.done.length)) ∧
  m.load (σ.sl 0x1f8) 8 = some (w (8 * o.done.length)) ∧
  m.load (σ.sl 0x210) 8 = some (w k.keys.length) ∧ m.load (σ.sl 0x208) 8 = some kp' ∧
  m.load (σ.sl 0x218) 8 = some (wordAt σ.m σ.ao) ∧ m.load (σ.sl 0x220) 8 = some (w vtable)

/-- `+0x33c`: `remap(ctx, ep, 40 ec, 3, 40 c', ra)` (vtable slot 2, F0). -/
def Site33c (σ : Sig) (m : Machine) : Prop :=
  ∃ o k L kp', EntryDone σ m o k L kp' [] ∧ Growing σ m o k kp' ∧ m.reg 27 = o.ec ∧
    0 < o.ec.toNat ∧
    m.reg 22 = 0 ∧
    m.load (σ.sl 0x228) 8 = some o.ep ∧
    m.load (σ.sl 0x230) 8 = some (w (8 * grownCap o.done.length)) ∧
    m.load (σ.sl 0x238) 8 = some (w (32 * grownCap o.done.length)) ∧
    m.load (σ.sl 0x240) 8 = some (w (entrySize * grownCap o.done.length)) ∧
    Args m c340 [wordAt σ.m σ.ao, o.ep, w (entrySize * o.ec.toNat), 3,
      w (entrySize * grownCap o.done.length), σ.m.reg 1]

/-- `+0x3d0`: `alloc(ctx, 40 c', 3, ra)` (vtable slot 0); `s6` = the old buffer. -/
def Site3d0 (σ : Sig) (L : List (Word × Nat)) (m : Machine) : Prop :=
  ∃ o k kp', EntryDone σ m o k L kp' [] ∧ Growing σ m o k kp' ∧ m.reg 27 = o.ec ∧
    m.reg 22 = o.ep ∧
    Args m c3d4 [wordAt σ.m σ.ao, w (entrySize * grownCap o.done.length), 3, σ.m.reg 1]

/-- After a successful `alloc`: the new block `(p'', 40 c')` is TX's, `s8 = p''`. -/
def Allocated (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) (L : List (Word × Nat))
    (kp' p'' : Word) : Prop :=
  EntryDone σ m o k L kp' [(p'', entrySize * grownCap o.done.length)] ∧ Growing σ m o k kp' ∧
  m.reg 22 = o.ep ∧ m.reg 24 = p'' ∧ 0 < p''.toNat ∧
  Present m p'' (entrySize * grownCap o.done.length)

/-- `+0x3fc`: `memcpy(p'', ep, 40 n)`. -/
def Site3fc (σ : Sig) (m : Machine) : Prop :=
  ∃ o k L kp' p'', Allocated σ m o k L kp' p'' ∧ m.reg 27 = o.ec ∧
    Args m c400 [p'', o.ep, w (entrySize * o.done.length)]

/-- After `memcpy`: the new block starts with the finished entries. -/
def Copied (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) (L : List (Word × Nat))
    (kp' p'' : Word) : Prop :=
  Allocated σ m o k L kp' p'' ∧ BytesAt m p'' (entriesBytes o.done o.is)

/-- `+0x428`: `free(ctx, ep, 40 ec, 3, ra)` (vtable slot 3). -/
def Site428 (σ : Sig) (L : List (Word × Nat)) (m : Machine) : Prop :=
  ∃ o k kp' p'', Copied σ m o k L kp' p'' ∧ 0 < o.ec.toNat ∧
    Args m c42c [wordAt σ.m σ.ao, o.ep, w (entrySize * o.ec.toNat), 3, σ.m.reg 1]

/-- `+0x49c`: `toOwnedSlice(S-0x88, E, ao)` once the outer payload is walked. -/
def Site49c (σ : Sig) (x : List (Word × Nat) × List Byte) (m : Machine) : Prop :=
  ∃ o, Common σ m ∧ OuterOk σ m o ∧ o.i = o.p ∧ EList σ m o o.done.length ∧
    Live σ m x.1 (EX o) ∧ x.2 = entriesBytes o.done o.is ∧ Args m c4a0 [σ.sl 0x88, σ.sl 0x1c0, σ.ao]

/-! ## Callees -/

/-- A callee whose contract is a family of `Spec`s indexed by `x` (lists, items); `Post` adds
`Preserved`. -/
def famCallee {X : Type} (entry bound : Nat) (P : Sig → X → Machine → Prop)
    (Q : Sig → X → Machine → Machine → Prop)
    (h : ∀ σ x, Spec zesuImage entry bound (P σ x) (Q σ x)) : Callee Sig zesuImage where
  X := X
  entry := entry
  bound := bound
  Pre := P
  Post := fun σ x m m' => Q σ x m m' ∧ Preserved m m'
  spec := fun σ x m hpc hx => Reaches.preserve (h σ x m hpc hx)

def f2C : Callee Sig zesuImage :=
  famCallee (X := Unit) F2.entry F2.bound (fun _ _ => F2.Pre) (fun _ _ => F2.Post)
    fun _ _ => F2.f2_spec

def f1C : Callee Sig zesuImage :=
  famCallee (X := List (Word × Nat) × List Byte) F1.entry F1.bound
    (fun σ x => F1.Pre σ.A x.1 x.2) (fun σ x => F1.PostKeep σ.A x.1 x.2)
    fun σ x => F1.f1_spec_keep σ.A x.1 x.2

def f4C : Callee Sig zesuImage :=
  famCallee (X := List (Word × Nat) × List Byte) F4.entry F4.bound
    (fun σ x => F4.Pre σ.A x.1 x.2) (fun σ x => F4.Post σ.A x.1 x.2)
    fun σ x => F4.f4_spec σ.A x.1 x.2

def f5C : Callee Sig zesuImage :=
  famCallee (X := List (Word × Nat) × List Byte) F5.entry F5.bound
    (fun σ x => F5.Pre σ.A x.1 x.2) (fun σ x => F5.Post σ.A x.1 x.2)
    fun σ x => F5.f5_spec σ.A x.1 x.2

def remapC : Callee Sig zesuImage :=
  famCallee (X := Unit) F0.entry F0.bound (fun _ _ => F0.Pre) (fun _ _ => F0.Post)
    fun _ _ => F0.f0_spec

def memcpyC : Callee Sig zesuImage :=
  famCallee (X := Unit) Layout.memcpyEntry 3 (fun _ _ => MemcpyPre) (fun _ _ => MemcpyPost)
    fun _ _ => memcpy_spec zesuImage

def allocPre (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m : Machine) : Prop :=
  A.Heap L m ∧ 0 < (m.reg 11).toNat ∧ (m.reg 11).toNat < 2 ^ 63 ∧ (m.reg 12).toNat ≤ 3 ∧
    StackOk m 16 ∧ RetAligned m ∧ CalleeFrameFree (A.Priv L) m

def allocPost (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m m' : Machine) : Prop :=
  Returns m m' ∧ SameOutside (fun a => A.Priv L a ∨ InRange (m.reg 2 - 16) 16 a) m m' ∧
  ((m'.reg 10 = 0 ∧ A.Heap L m') ∨
   (m'.reg 10 ≠ 0 ∧ A.Heap (L ++ [(m'.reg 10, (m.reg 11).toNat)]) m' ∧
    RamRange (m'.reg 10) (m.reg 11).toNat ∧ Present m' (m'.reg 10) (m.reg 11).toNat ∧
    (∀ a, InRange (m'.reg 10) (m.reg 11).toNat a → A.Priv L a) ∧
    (∀ a, A.Priv (L ++ [(m'.reg 10, (m.reg 11).toNat)]) a → A.Priv L a)))

def allocC : Callee Sig zesuImage :=
  famCallee (X := List (Word × Nat)) allocEntry 53 (fun σ L => allocPre σ.A L)
    (fun σ L => allocPost σ.A L) fun σ L => σ.A.alloc_spec L

def freePre (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m : Machine) : Prop :=
  A.Heap L m ∧ (m.reg 11, (m.reg 12).toNat) ∈ L ∧ 0 < (m.reg 12).toNat ∧
    (m.reg 12).toNat < 2 ^ 63 ∧ (m.reg 13).toNat ≤ 3 ∧ StackOk m 16 ∧ RetAligned m ∧
    CalleeFrameFree (A.Priv L) m

def freePost (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m m' : Machine) : Prop :=
  Returns m m' ∧
  SameOutside (fun a => A.Priv L a ∨ InRange (m.reg 11) (m.reg 12).toNat a ∨
    InRange (m.reg 2 - 16) 16 a) m m' ∧
  A.Heap (L.erase (m.reg 11, (m.reg 12).toNat)) m' ∧
  (∀ a, A.Priv (L.erase (m.reg 11, (m.reg 12).toNat)) a →
    A.Priv L a ∨ InRange (m.reg 11) (m.reg 12).toNat a)

def freeC : Callee Sig zesuImage :=
  famCallee (X := List (Word × Nat)) freeEntry 42 (fun σ L => freePre σ.A L)
    (fun σ L => freePost σ.A L) fun σ L => σ.A.free_spec L

/-- A call return site: the call-site predicate at the machine of the call, for the callee's
index `x`, and the callee's `Post` from it. -/
def ARet (k : Callee Sig zesuImage) (site : Sig → k.X → Machine → Prop) (σ : Sig) (m : Machine) :
    Prop :=
  ∃ mc x, site σ x mc ∧ k.Post σ x mc m

/-- A site that does not depend on the callee's index. -/
abbrev unit (site : Sig → Machine → Prop) : Sig → Unit → Machine → Prop := fun σ _ m => site σ m

/-- `0x8000042c`: after `free`, or straight from `0x80000400` when the old capacity was 0. -/
def A42c (σ : Sig) (m : Machine) : Prop :=
  (m.pc.toNat = c42c ∧ ∃ o k L kp' p'', Copied σ m o k L kp' p'' ∧ o.ec.toNat = 0) ∨
  ARet freeC Site428 σ m

/-! ## Budgets -/

/-- Outer bytes after the current entry (`s5 - s10`) and keys bytes left (`s6`). -/
abbrev outerLeft (m : Machine) : Nat := (m.reg 21).toNat
abbrev afterEntry (m : Machine) : Nat := (m.reg 21).toNat - (m.reg 26).toNat
abbrev keysLeft (m : Machine) : Nat := (m.reg 22).toNat

def bEntry (σ : Sig) : Nat := 32 * σ.len + 424
def bOuter (m : Machine) : Nat := 32 * outerLeft m + 300
def bKeys (m : Machine) : Nat := 32 * (afterEntry m + keysLeft m) + 738
def bTail (m : Machine) (c : Nat) : Nat := 32 * afterEntry m + c

/-! ## Cut points -/

def mkCut (pc : Nat) (S : SState) (A : Sig → Machine → Prop) (env : Sig → Machine → Env)
    (budget : Sig → Machine → Nat) : Cut Sig := ⟨pc, S, A, env, budget⟩

def cutEntry : Cut Sig := mkCut cEntry SEntry AEntry envB fun σ _ => bEntry σ
def cut068 : Cut Sig := mkCut c068 S068 (ARet f2C (unit Site064)) envB fun σ _ => 32 * σ.len + 323
def cut0c4 : Cut Sig := mkCut c0c4 SBody AOuter envB fun _ m => bOuter m
def cut0d8 : Cut Sig := mkCut c0d8 SBody (ARet f2C (unit Site0d4)) envB
  fun _ m => 32 * outerLeft m + 220
def cut10c : Cut Sig := mkCut c10c S10c (ARet f2C (unit Site108)) (envP 0x180)
  fun _ m => 32 * outerLeft m + 132
def cut15c : Cut Sig := mkCut c15c SBody (ARet f2C (unit Site158)) envB
  fun _ m => 32 * outerLeft m + 37
def cut18c : Cut Sig := mkCut c18c SBody AKeys envB fun _ m => bKeys m
def cut1a0 : Cut Sig := mkCut c1a0 S1a0 (ARet f2C (unit Site19c)) (envP 0x100)
  fun _ m => 32 * (afterEntry m + keysLeft m) + 658
def cut1f8 : Cut Sig := mkCut c1f8 SBody (ARet f1C Site1f4) envB
  fun _ m => 32 * (afterEntry m + keysLeft m) + 439
def cut230 : Cut Sig := mkCut c230 S230 AKeyStore (envS keySize)
  fun _ m => 32 * (afterEntry m + keysLeft m) + 744
def cut25c : Cut Sig := mkCut c25c SBody (ARet f4C Site258) envB fun _ m => bTail m 539
def cut340 : Cut Sig := mkCut c340 SSpill (ARet remapC (unit Site33c)) envB fun _ m => bTail m 478
def cut3d4 : Cut Sig := mkCut c3d4 SBody (ARet allocC Site3d0) envB fun _ m => bTail m 389
def cut400 : Cut Sig := mkCut c400 SSpill (ARet memcpyC (unit Site3fc)) envB fun _ m => bTail m 377
def cut42c : Cut Sig := mkCut c42c SBody A42c envB fun _ m => bTail m 324
def cut460 : Cut Sig := mkCut c460 S460 AEntryStore (envS entrySize) fun _ m => bTail m 311
def cut4a0 : Cut Sig := mkCut c4a0 SBody (ARet f5C Site49c) envB fun _ _ => 23

/-! ## The plan -/

def calleeAt (r : Nat) : Option (Callee Sig zesuImage) :=
  if r = c068 ∨ r = c0d8 ∨ r = c10c ∨ r = c15c ∨ r = c1a0 then some f2C
  else if r = c1f8 then some f1C else if r = c25c then some f4C
  else if r = c340 then some remapC else if r = c3d4 then some allocC
  else if r = c400 then some memcpyC else if r = c42c then some freeC
  else if r = c4a0 then some f5C else none

def leavesAt (pc : Nat) : List Leaf :=
  if pc = cEntry then runEntry_leaves else if pc = c068 then run068_leaves
  else if pc = c0c4 then run0c4_leaves else if pc = c0d8 then run0d8_leaves
  else if pc = c10c then run10c_leaves else if pc = c15c then run15c_leaves
  else if pc = c18c then run18c_leaves else if pc = c1a0 then run1a0_leaves
  else if pc = c1f8 then run1f8_leaves else if pc = c230 then run230_leaves
  else if pc = c25c then run25c_leaves else if pc = c340 then run340_leaves
  else if pc = c3d4 then run3d4_leaves else if pc = c400 then run400_leaves
  else if pc = c42c then run42c_leaves else if pc = c460 then run460_leaves
  else if pc = c4a0 then run4a0_leaves else []

def vcPlan : Plan Sig zesuImage where
  cuts := [cutEntry, cut068, cut0c4, cut0d8, cut10c, cut15c, cut18c, cut1a0, cut1f8, cut230,
    cut25c, cut340, cut3d4, cut400, cut42c, cut460, cut4a0]
  fuel := 300
  leaves := leavesAt
  callee := calleeAt
  Post := fun σ => Post σ.A σ.g σ.m

zesu_plan TX := vcPlan

zesu_auto TX

end ZesuExec.Fn.TX
