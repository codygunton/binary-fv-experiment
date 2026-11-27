import ZesuExec.Fn.Common
import ZesuExec.Sym.Compose

/-!
# Helpers for multi-run function proofs

Facts that turn an entry machine's loads into evaluations of `Sym.init`, and the step from a
call leaf over the callee's contract to the next run (`after_call`).
-/

namespace ZesuExec.Fn
open ZesuExec.Sym ZesuExec.Machine

theorem readBytes_some_eq {mem : Word → Option Byte} :
    ∀ {a n : Nat} {bs : List Byte}, readBytes mem a n = some bs →
      bs = byteList (fun j => (mem (BitVec.ofNat 64 j)).getD 0) a n
  | _, 0, bs, h => by simp [readBytes] at h; subst h; rfl
  | a, n + 1, bs, h => by
    simp only [readBytes] at h
    cases hb : mem (BitVec.ofNat 64 a) with
    | none => simp [hb] at h
    | some b =>
      cases hr : readBytes mem (a + 1) n with
      | none => simp [hb, hr] at h
      | some rest =>
        simp [hb, hr] at h; subst h
        simp [byteList, hb, readBytes_some_eq hr]

/-- An entry region's initial word is what the entry machine loads there. -/
theorem init_eval_load {m : Machine} {regs : List (Word × Nat)} {r off n : Nat} {v : Word}
    (hr : r < regs.length) (hload : m.load (regs[r].1 + BitVec.ofNat 64 off) n = some v)
    (hfit : regs[r].1.toNat + off + n < 2 ^ 64) :
    (Sym.init r off n).eval (entryEnv m regs) = v := by
  have ha : (regs[r].1 + BitVec.ofNat 64 off).toNat = regs[r].1.toNat + off :=
    toNat_add_ofNat (by omega)
  unfold Machine.load at hload
  rw [ha] at hload
  split at hload
  · cases hb : readBytes m.mem (regs[r].1.toNat + off) n with
    | none => rw [hb] at hload; simp at hload
    | some bs =>
      rw [hb] at hload; simp only [Option.map_some, Option.some.injEq] at hload; subst hload
      rw [readBytes_some_eq hb]
      simp only [Sym.eval]
      congr 1
      apply byteList_congr
      intro t ht
      simp only [Env.byte0, entryEnv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr,
        Option.getD_some]
      rw [Nat.add_assoc, ofNat_toNat_add]
  · simp at hload

theorem _root_.ZesuExec.Sym.Env.Ext.mono0 {e e' : Env} {K R : Nat} (h : Env.Ext e e' K R) :
    Env.Ext e e' 0 R :=
  ⟨fun _ h0 => absurd h0 (Nat.not_lt_zero _), h.base, h.size, h.mem0⟩

/-- A call leaf, the callee's contract, and the next run's state: the registers `ov` replaces
take `m₂`'s values through fresh variables from `F` on; the others are callee-saved; the
callee touched none of the state's regions. -/
theorem after_call {env : Env} {S : SState} {m₁ m₂ : Machine} {F : Nat} {ov : Nat → Option Sym}
    (hm : Match env S m₁) (hwf : Env.WF env S) (hwfB : S.wfB F = true) (h0 : ov 0 = none)
    (hret : Returns m₁ m₂)
    (hkept : ∀ i : Fin 32, ov i.val = none → i.val = 0 ∨ i ∈ calleeSaved)
    (hnew : ∀ i : Fin 32, ∀ s, ov i.val = some s →
      s.eval (env.setVars F fun i => m₂.reg (Fin.ofNat 32 i)) = m₂.reg i)
    (hframe : ∀ r j, r < S.regions.length → j < env.size r →
      m₂.mem (env.base r + BitVec.ofNat 64 j) = m₁.mem (env.base r + BitVec.ofNat 64 j)) :
    Match (env.setVars F fun i => m₂.reg (Fin.ofNat 32 i)) (S.override ov) m₂ ∧
      Env.WF (env.setVars F fun i => m₂.reg (Fin.ofNat 32 i)) (S.override ov) := by
  refine ⟨hm.override hwfB (Env.setVars_ext env F _ S.regions.length) h0 ?_ hnew hframe, ?_⟩
  · intro i hi
    rcases hkept i hi with h | h
    · simp [Machine.reg, h]
    · exact hret.2 i h
  · exact (hwf.ext (Env.setVars_ext env F _ S.regions.length).mono0 hwf.len).congr rfl

/-- Leaf, variable, pointer or initial word: kept across a call when callee-saved. -/
def _root_.ZesuExec.Sym.Sym.simple : Sym → Bool
  | .lit _ | .var _ | .ptr _ _ | .init _ _ _ => true
  | _ => false

/-- The register replacement after a call: caller-saved registers become `var (F + i)`
(`a0` may be given), callee-saved ones stay unless their term is not `Sym.simple`. -/
def callOv (S : SState) (F : Nat) (a0 : Option Sym) (i : Nat) : Option Sym :=
  if i = 0 then none
  else if (calleeSaved.map Fin.val).contains i then
    (if (S.reg i).simple then none else some (.var (F + i)))
  else if i = 10 then (a0 <|> some (.var (F + 10)))
  else some (.var (F + i))

theorem callOv_zero (S : SState) (F : Nat) (a0 : Option Sym) : callOv S F a0 0 = none := by
  simp [callOv]

theorem callOv_kept {S : SState} {F : Nat} {a0 : Option Sym} (i : Fin 32)
    (h : callOv S F a0 i.val = none) : i.val = 0 ∨ i ∈ calleeSaved := by
  unfold callOv at h
  by_cases h0 : i.val = 0
  · exact .inl h0
  · right
    simp only [h0, if_false] at h
    split at h
    · next hc =>
      simp only [List.contains_iff_mem, List.mem_map] at hc
      obtain ⟨j, hj, hji⟩ := hc
      have : j = i := Fin.ext hji
      exact this ▸ hj
    · split at h
      · cases a0 <;> simp at h
      · simp at h

theorem callOv_new {S : SState} {F : Nat} {a0 : Option Sym} {i : Nat} {s : Sym}
    (h : callOv S F a0 i = some s) : s = .var (F + i) ∨ (i = 10 ∧ a0 = some s) := by
  unfold callOv at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · exact .inl (Option.some.inj h).symm
    · split at h
      · next h10 =>
        subst h10
        cases a0 with
        | none => exact .inl (Option.some.inj h).symm
        | some x => exact .inr ⟨rfl, by simpa using h⟩
      · exact .inl (Option.some.inj h).symm

theorem setVars_var (env : Env) (F : Nat) (m : Machine) (i : Fin 32) :
    (Sym.var (F + i.val)).eval (env.setVars F fun j => m.reg (Fin.ofNat 32 j)) = m.reg i := by
  simp [Sym.eval, Env.setVars]

/-- `after_call` for `callOv`: only the returned `a0`, if given, needs a proof. -/
theorem after_call_ov {env : Env} {S : SState} {m₁ m₂ : Machine} {F : Nat} {a0 : Option Sym}
    (hm : Match env S m₁) (hwf : Env.WF env S) (hwfB : S.wfB F = true) (hret : Returns m₁ m₂)
    (ha0 : ∀ s, a0 = some s → s.eval (env.setVars F fun i => m₂.reg (Fin.ofNat 32 i)) = m₂.reg 10)
    (hframe : ∀ r j, r < S.regions.length → j < env.size r →
      m₂.mem (env.base r + BitVec.ofNat 64 j) = m₁.mem (env.base r + BitVec.ofNat 64 j)) :
    Match (env.setVars F fun i => m₂.reg (Fin.ofNat 32 i)) (S.override (callOv S F a0)) m₂ ∧
      Env.WF (env.setVars F fun i => m₂.reg (Fin.ofNat 32 i)) (S.override (callOv S F a0)) :=
  after_call hm hwf hwfB (callOv_zero S F a0) hret (fun i h => callOv_kept i h)
    (fun i s h => by
      rcases callOv_new h with rfl | ⟨h10, rfl⟩
      · exact setVars_var env F m₂ i
      · have : i = 10 := Fin.ext h10
        subst this; exact ha0 s rfl) hframe

/-- A `ret` leaf whose callee-saved registers are the entry variables returns. -/
theorem returns_leaf {env : Env} {S : SState} {m mf : Machine} (hm : Match env S mf)
    (hvars : ∀ i : Fin 32, env.vars i.val = m.reg i)
    (hregs : (calleeSaved.filter (· ≠ 2)).all (fun i => S.reg i.val == .var i.val) = true)
    (hsp : (S.reg 2).eval env = m.reg 2)
    (hpc : mf.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env) :
    Returns m mf := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hpc]; simp only [Sym.eval, BinOp.eval]
    rw [show env.vars 1 = m.reg 1 from hvars 1]; rfl
  · by_cases h2 : i = 2
    · subst h2; rw [← hm.regs 2]; exact hsp
    · have := List.all_eq_true.mp hregs i (List.mem_filter.mpr ⟨hi, by simpa using h2⟩)
      simp only [beq_iff_eq] at this
      rw [← hm.regs i, this]; exact hvars i

/-! ## Loads as bytes -/

theorem getLsbD_ofBytesLE : ∀ (bs : List Byte) (i : Nat), bs.length ≤ 8 → i < 64 →
    (ofBytesLE bs).getLsbD i = (bs.getD (i / 8) 0).getLsbD (i % 8)
  | [], i, _, _ => by simp [ofBytesLE]
  | b :: bs, i, hl, hi => by
    simp only [ofBytesLE, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h8 : i < 8
    · have : i / 8 = 0 := Nat.div_eq_of_lt h8
      simp [h8, hi, this, Nat.mod_eq_of_lt h8]
    · rw [getLsbD_ofBytesLE bs (i - 8) (by simp at hl; omega) (by omega)]
      have hd : i / 8 = (i - 8) / 8 + 1 := by omega
      have hm : i % 8 = (i - 8) % 8 := by omega
      simp [h8, hi, hd, hm, BitVec.getLsbD_of_ge b i (by omega)]

theorem byteOf_ofBytesLE (bs : List Byte) (hl : bs.length ≤ 8) (t : Nat) (ht : t < bs.length) :
    byteOf (ofBytesLE bs) t = bs[t] := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [byteOf, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  rw [getLsbD_ofBytesLE bs (8 * t + k) hl (by omega)]
  have h1 : (8 * t + k) / 8 = t := by omega
  have h2 : (8 * t + k) % 8 = k := by omega
  simp [h1, h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

theorem readBytes_length {mem : Word → Option Byte} : ∀ {a n : Nat} {bs : List Byte},
    readBytes mem a n = some bs → bs.length = n
  | _, 0, bs, h => by simp [readBytes] at h; subst h; rfl
  | a, n + 1, bs, h => by
    simp only [readBytes] at h
    cases hb : mem (BitVec.ofNat 64 a) with
    | none => simp [hb] at h
    | some b =>
      cases hr : readBytes mem (a + 1) n with
      | none => simp [hb, hr] at h
      | some rest => simp [hb, hr] at h; subst h; simp [readBytes_length hr]

theorem readBytes_get {mem : Word → Option Byte} : ∀ {a n : Nat} {bs : List Byte},
    readBytes mem a n = some bs → ∀ t (ht : t < bs.length), mem (BitVec.ofNat 64 (a + t)) = some bs[t]
  | _, 0, bs, h, t, ht => by simp [readBytes] at h; subst h; simp at ht
  | a, n + 1, bs, h, t, ht => by
    simp only [readBytes] at h
    cases hb : mem (BitVec.ofNat 64 a) with
    | none => simp [hb] at h
    | some b =>
      cases hr : readBytes mem (a + 1) n with
      | none => simp [hb, hr] at h
      | some rest =>
        simp [hb, hr] at h; subst h
        cases t with
        | zero => simpa using hb
        | succ t =>
          have := readBytes_get hr t (by simp at ht; omega)
          simp only [List.getElem_cons_succ]
          rw [show a + (t + 1) = a + 1 + t by omega]; exact this

theorem load_bytes {m : Machine} {a v : Word} {n : Nat} (h : m.load a n = some v) (hn : n ≤ 8) :
    ∀ t < n, m.mem (a + BitVec.ofNat 64 t) = some (byteOf v t) := by
  intro t ht
  unfold Machine.load at h
  split at h
  · cases hb : readBytes m.mem a.toNat n with
    | none => rw [hb] at h; simp at h
    | some bs =>
      rw [hb] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      have hl := readBytes_length hb
      rw [← ofNat_toNat_add, readBytes_get hb t (by omega), byteOf_ofBytesLE bs (by omega) t (by omega)]
  · simp at h

theorem readBytes_congr {mem mem' : Word → Option Byte} :
    ∀ {a n : Nat}, (∀ t < n, mem' (BitVec.ofNat 64 (a + t)) = mem (BitVec.ofNat 64 (a + t))) →
      readBytes mem' a n = readBytes mem a n
  | _, 0, _ => rfl
  | a, n + 1, h => by
    simp only [readBytes]
    have h1 : readBytes mem' (a + 1) n = readBytes mem (a + 1) n :=
      readBytes_congr fun t ht => by
        have := h (t + 1) (by omega)
        rwa [show a + (t + 1) = a + 1 + t by omega] at this
    rw [show mem' (BitVec.ofNat 64 a) = mem (BitVec.ofNat 64 a) by simpa using h 0 (by omega), h1]

/-- A load only depends on the bytes it reads. -/
theorem load_congr {m m' : Machine} {a : Word} {n : Nat}
    (h : ∀ t < n, m'.mem (a + BitVec.ofNat 64 t) = m.mem (a + BitVec.ofNat 64 t)) :
    m'.load a n = m.load a n := by
  unfold Machine.load
  rw [readBytes_congr (mem := m.mem) (mem' := m'.mem) fun t ht => by rw [ofNat_toNat_add]; exact h t ht]

/-- A region the run never wrote keeps the entry machine's bytes. -/
theorem region_same {env : Env} {S : SState} {m mf : Machine} {r : Nat} (hm : Match env S mf)
    (hr : r < S.regions.length) (hnw : S.mem.all (fun w => w.r != r) = true)
    (hmem0 : ∀ j < env.size r, some (env.mem0 r j) = m.mem (env.base r + BitVec.ofNat 64 j)) :
    ∀ j < env.size r, mf.mem (env.base r + BitVec.ofNat 64 j) = m.mem (env.base r + BitVec.ofNat 64 j) := by
  intro j hj
  rw [hm.mem r j hr hj, ← hmem0 j hj]
  have : S.mem.find? (·.covers r j) = none := List.find?_eq_none.mpr fun w hw => by
    have := List.all_eq_true.mp hnw w hw
    simp [Write.covers] at this ⊢; intro h; exact absurd h this
  simp [memByte, this, Env.byte0]

end ZesuExec.Fn
