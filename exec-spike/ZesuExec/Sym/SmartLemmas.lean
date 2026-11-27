import ZesuExec.Sym.Smart

/-!
# Evaluation lemmas of the smart constructors in `ZesuExec.Sym.Smart`
-/

namespace ZesuExec.Sym
open ZesuExec.Machine

theorem ofInt_toInt64 (c : Nat) : BitVec.ofInt 64 (toInt64 c) = BitVec.ofNat 64 c := by
  simp [toInt64]

theorem addConst_eval {env : Env} {a s : Sym} {c : Int} (h : addConst a c = some s) :
    s.eval env = a.eval env + BitVec.ofInt 64 c := by
  unfold addConst at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · simp [Sym.eval, BitVec.ofInt_add, BitVec.add_assoc]
  · simp only [Sym.eval, BinOp.eval, BitVec.ofInt_add]
    ac_rfl

theorem lit_zero_of_mod {c : Nat} (h : c % 2 ^ 64 = 0) : BitVec.ofNat 64 c = 0 := by
  apply BitVec.eq_of_toNat_eq; simp [h]

theorem addLit_eval (env : Env) (a : Sym) (c : Nat) :
    (addLit a c).eval env = a.eval env + BitVec.ofNat 64 c := by
  unfold addLit
  split
  · simp [lit_zero_of_mod ‹_›]
  · cases h : addConst a (toInt64 c) with
    | none => simp [Sym.eval, BinOp.eval]
    | some s => simp [addConst_eval h, ofInt_toInt64]

theorem subLit_eval (env : Env) (a : Sym) (c : Nat) :
    (subLit a c).eval env = a.eval env - BitVec.ofNat 64 c := by
  unfold subLit
  split
  · simp [lit_zero_of_mod ‹_›]
  · cases h : addConst a (-toInt64 c) with
    | none => simp [Sym.eval, BinOp.eval]
    | some s =>
      simp [addConst_eval h, toInt64, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

@[simp] theorem mkAdd_eval (env : Env) (a b : Sym) : (mkAdd a b).eval env = a.eval env + b.eval env := by
  unfold mkAdd
  split
  · simp only [Sym.eval]; apply BitVec.eq_of_toNat_eq; simp
  · simp [addLit_eval, Sym.eval]
  · simp [addLit_eval, Sym.eval, BitVec.add_comm]
  · simp [Sym.eval, BinOp.eval, BitVec.add_comm]
  · simp [Sym.eval, BinOp.eval]

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

@[simp] theorem mkSub_eval (env : Env) (a b : Sym) : (mkSub a b).eval env = a.eval env - b.eval env := by
  unfold mkSub
  split
  · simp only [Sym.eval]; rw [ofNat_toNat64]
  · split
    · subst_vars
      simp only [Sym.eval]
      rw [ofNat_toNat64]
      simp only [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]
      bv_omega
    · simp [Sym.eval, BinOp.eval]
  · simp [subLit_eval, Sym.eval]
  · simp [Sym.eval, BinOp.eval]

@[simp] theorem mkBin_eval (env : Env) (op : BinOp) (a b : Sym) :
    (mkBin op a b).eval env = op.eval (a.eval env) (b.eval env) := by
  unfold mkBin
  split <;> simp [Sym.eval, BinOp.eval]

@[simp] theorem mkSext_eval (env : Env) (bits : Nat) (a : Sym) :
    (mkSext bits a).eval env = ((a.eval env).setWidth bits).signExtend 64 := by
  unfold mkSext
  split <;> simp [Sym.eval]

theorem getLsbD_ofBytesLE_bytes (x : Word) : ∀ (n k i : Nat), i < 64 →
    (ofBytesLE (byteList (byteOf x) k n)).getLsbD i = (decide (i < 8 * n) && x.getLsbD (8 * k + i))
  | 0, k, i, _ => by simp [byteList, ofBytesLE]
  | n + 1, k, i, hi => by
    have ih := getLsbD_ofBytesLE_bytes x n (k + 1)
    simp only [byteList, ofBytesLE, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h8 : i < 8
    · simp [h8, hi]
      intro _; omega
    · rw [ih (i - 8) (by omega)]
      simp [h8, hi]
      rw [show 8 * (k + 1) + (i - 8) = 8 * k + i by omega]
      have hiff : (i - 8 < 8 * n) ↔ (i < 8 * (n + 1)) := by omega
      simp only [hiff]

theorem ofBytesLE_bytes8 (x : Word) : ofBytesLE (byteList (byteOf x) 0 8) = x := by
  ext i hi
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem, getLsbD_ofBytesLE_bytes x 8 0 i hi]
  simp [hi]

@[simp] theorem mkBytes_eval (env : Env) (a : Sym) (k n : Nat) :
    (mkBytes a k n).eval env = ofBytesLE (byteList (byteOf (a.eval env)) k n) := by
  unfold mkBytes
  split
  · next h => obtain ⟨rfl, rfl⟩ := h; rw [ofBytesLE_bytes8]
  · simp [Sym.eval]

theorem zeroExtend_and_255 (b : Byte) : b.zeroExtend 64 &&& BitVec.ofNat 64 255 = b.zeroExtend 64 := by
  ext i hi
  simp
  intro h
  have : i < 8 := by
    false_or_by_contra
    rw [BitVec.getLsbD_of_ge b i (by omega)] at h; contradiction
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [← BitVec.getLsbD_eq_getElem]; decide)
/-- Joining single-byte values gives the little-endian word of the bytes. -/
theorem joinBytes_eval (env : Env) (f : Sym → Byte) (bs : List Sym)
    (h : ∀ s ∈ bs, s.eval env = (f s).zeroExtend 64) :
    (joinBytes bs).eval env = ofBytesLE (bs.map f) := by
  induction bs with
  | nil => simp [joinBytes, Sym.eval, ofBytesLE]
  | cons s rest ih =>
    have hs := h s (by simp)
    have ih := ih (fun s' hs' => h s' (by simp [hs']))
    cases rest with
    | nil => simp [joinBytes, ofBytesLE, hs]
    | cons s₂ rest₂ =>
      rw [show joinBytes (s :: s₂ :: rest₂) = .cat s (joinBytes (s₂ :: rest₂)) 1 from rfl]
      simp only [Sym.eval]
      rw [ih, hs, List.map_cons, ofBytesLE]
      simp [zeroExtend_and_255]
      rfl

end ZesuExec.Sym
