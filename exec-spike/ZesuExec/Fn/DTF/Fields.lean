import ZesuExec.Fn.DTF.Head

/-!
# DTF: arithmetic of item values (programme plan S7, open assertion items 1 and 4)

The facts `Gen.lean`'s carry rules (`fieldsCarry`) use: a byte loop's step on the limbs of a
big-endian number (`limb_step0`, `limb_stepS`), `be` of one more byte (`be_take_succ`), a
`decodeItem` payload length below `2^64` (`decode_p_lt`), and item values free of the machine
(`holds_free`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine

theorem be_take_succ (b : List Byte) {j : Nat} (hj : j < b.length) :
    be (b.take (j + 1)) = 256 * be (b.take j) + b[j].toNat := by
  rw [List.take_succ_eq_append_getElem hj]
  simp only [be, F2.bigEndian, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem fold_be_lt : ∀ (bs : List Byte) (acc : Nat),
    bs.foldl (fun acc b => 256 * acc + b.toNat) acc < (acc + 1) * 256 ^ bs.length
  | [], acc => by simp
  | b :: bs, acc => by
    simp only [List.foldl_cons, List.length_cons]
    have := fold_be_lt bs (256 * acc + b.toNat)
    have hb := b.isLt
    have h1 : (256 * acc + b.toNat + 1) * 256 ^ bs.length ≤ (acc + 1) * 256 * 256 ^ bs.length :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm (acc + 1) (256 ^ bs.length) 256,
      Nat.mul_right_comm (acc + 1) 256] at *
    omega

theorem be_lt (bs : List Byte) : be bs < 256 ^ bs.length := by
  have := fold_be_lt bs 0
  simpa [be, F2.bigEndian] using this

/-- A `decodeItem` success's payload length is below `2^64` (at most eight length bytes). -/
theorem decode_p_lt {b : List Byte} {l : Bool} {h p : Nat} (hd : F2.decode b = .success l h p) :
    p < 2 ^ 64 := by
  cases b with
  | nil => simp [F2.decode] at hd
  | cons pre rest =>
    have hlt := pre.isLt
    simp only [F2.decode, F2.checkedPayload] at hd
    repeat' split at hd
    all_goals (try simp only [F2.Item.success.injEq, reduceCtorEq] at hd)
    all_goals (try (obtain ⟨-, rfl, rfl⟩ := hd))
    all_goals (try omega)
    all_goals
      refine Nat.lt_of_lt_of_le (be_lt _) ?_
      rw [show (2 : Nat) ^ 64 = 256 ^ 8 by decide]
      exact Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega)

theorem or_byte {x y : Nat} (hy : y < 256) (hx : x % 256 = 0) : x ||| y = x + y := by
  obtain ⟨a, rfl⟩ : ∃ a, x = a * 256 := ⟨x / 256, by omega⟩
  rw [show a * 256 = a <<< 8 by rw [Nat.shiftLeft_eq]]
  exact (Nat.shiftLeft_add_eq_or_of_lt (by omega) a).symm

/-- The low limb after one more byte `y`. -/
theorem limb_step0 (A y : Nat) (hy : y < 256) :
    limb (256 * A + y) 0 = (limb A 0 <<< 8) ||| w y := by
  apply BitVec.eq_of_toNat_eq
  simp only [limb, w, Nat.mul_zero, Nat.pow_zero, Nat.div_one, BitVec.toNat_or,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq, or_byte (by omega) (by omega)]
  omega

/-- Limb `i + 1` after one more byte: limb `i + 1` shifted by a byte over limb `i`'s top byte. -/
theorem limb_stepS (A y i : Nat) (hy : y < 256) :
    limb (256 * A + y) (i + 1) = (limb A (i + 1) <<< 8) ||| (limb A i >>> 56) := by
  have hP : 0 < 2 ^ (64 * i) := Nat.two_pow_pos _
  generalize hPd : 2 ^ (64 * i) = P at hP
  have hpow : 2 ^ (64 * (i + 1)) = P * 2 ^ 64 := by
    rw [← hPd, Nat.mul_succ, Nat.pow_add]
  have ha := Nat.div_add_mod A P
  generalize A / P = a1 at ha
  have ha0 : A % P < P := Nat.mod_lt _ hP
  generalize A % P = a0 at ha ha0
  have he : (256 * a0 + y) / P < 256 := (Nat.div_lt_iff_lt_mul hP).mpr (by
    have : a0 + 1 ≤ P := ha0
    have := Nat.mul_le_mul_left 256 this
    omega)
  have hN : (256 * A + y) / P = 256 * a1 + (256 * a0 + y) / P := by
    rw [← ha, show 256 * (P * a1 + a0) + y = 256 * a0 + y + P * (256 * a1) by
      rw [Nat.mul_add, Nat.mul_left_comm]; omega, Nat.add_mul_div_left _ _ hP]
    omega
  have hA1 : A / P = a1 := by
    rw [← ha, Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt ha0]
    omega
  generalize (256 * a0 + y) / P = e at he hN
  apply BitVec.eq_of_toNat_eq
  simp only [limb, w, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, hpow, hPd]
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hN, hA1, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [or_byte (by omega) (by omega)]
  omega

theorem ofBytesLE_one (y : Byte) : ofBytesLE [y] = w y.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [ofBytesLE, w]

/-- An item value free of the machine holds at any machine. -/
theorem holds_free {σ : Sig} {m m' : Machine} {v : FieldVal} {x : Word} (hv : v.free = true)
    (h : v.Holds σ m x) : v.Holds σ m' x := by
  cases v <;> simp only [FieldVal.free, Bool.false_eq_true] at hv <;> exact h

end ZesuExec.Fn.DTF
