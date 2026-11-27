import ZesuExec.Fn.F2.Regions
import ZesuExec.Sym.Compose

/-!
# Lemmas for the F2 proof

Generic: `entry_match_vars` (`entry_match` for an entry environment with extra variables from
`F ≥ 32`), struct views (`viewOK`: the newest write covering each byte of a 40-byte region,
checked by evaluation), memory facts after a run, byte and big-endian arithmetic.
-/

namespace ZesuExec.Fn.F2
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-! ## Entry match with extra variables -/

theorem entry_match_vars {m : Machine} {regs : List (Word × Nat)} {ov : Nat → Option Sym}
    {rs : List Region} {ks : List Write} {F : Nat} {f : Nat → Word} (hF : 32 ≤ F)
    (hov : ∀ i : Fin 32, i.val ≠ 0 → ∀ s, ov i.val = some s →
      s.eval ((entryEnv m regs).setVars F f) = m.reg i)
    (hpres : ∀ r j, r < rs.length → j < (entryEnv m regs).size r →
      (m.mem ((entryEnv m regs).base r + BitVec.ofNat 64 j)).isSome)
    (hknown : ∀ k ∈ ks, ∀ t < k.n,
      (entryEnv m regs).byte0 k.r (k.off + t) = byteOf (k.v.eval ((entryEnv m regs).setVars F f)) t) :
    Match ((entryEnv m regs).setVars F f) (entryState ov rs ks) m where
  regsLen := by simp [entryState]
  regs i := by
    rw [entryState_reg]
    split
    · next h0 => simp [Sym.eval, Machine.reg, h0]
    · next h0 =>
      cases h : ov i.val with
      | none =>
        simp only [Option.getD_none, Sym.eval, Env.setVars]
        rw [if_neg (by omega)]
        exact entryEnv_var m regs i
      | some s => simpa using hov i h0 s h
  mem r j hr hj := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hpres r j hr hj)
    simp [memByte, entryState, Env.byte0, Env.base, entryEnv, Env.setVars] at hb ⊢
    simp [hb]
  known := by simpa [entryState] using hknown

theorem setVars_wf {env : Env} {S : SState} (hwf : Env.WF env S) (F : Nat) (f : Nat → Word) :
    Env.WF (env.setVars F f) S :=
  hwf.ext ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
    (by simpa [Env.setVars] using hwf.len)

/-! ## Struct views -/

/-- The newest write covering byte `j` of region `r`, and the byte index inside it. -/
def wview (ws : List Write) (r j : Nat) : Option (Sym × Nat) :=
  (ws.find? (·.covers r j)).map fun w => (w.v, j - w.off)

theorem memByte_wview (env : Env) (ws : List Write) (r j : Nat) :
    memByte env ws r j = match wview ws r j with
      | some (v, k) => byteOf (v.eval env) k
      | none => env.byte0 r j := by
  unfold memByte wview
  cases ws.find? (·.covers r j) <;> rfl

/-- The 40 bytes of region 2 are as `v` says. -/
def viewOK (ws : List Write) (v : Nat → Option (Sym × Nat)) : Bool :=
  (List.range 40).all fun j => wview ws 2 j == v j

theorem wview_of_viewOK {ws : List Write} {v : Nat → Option (Sym × Nat)} (h : viewOK ws v = true)
    {j : Nat} (hj : j < 40) : wview ws 2 j = v j := by
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simpa using this

/-- A success return: pointer, length, flag byte, consumed, zero error halfword. -/
def succView (p l f c : Sym) (j : Nat) : Option (Sym × Nat) :=
  if j < 8 then some (p, j) else if j < 16 then some (l, j - 8) else if j = 16 then some (f, 0)
  else if j < 24 then none else if j < 32 then some (c, j - 24)
  else if j < 34 then some (.lit 0, j - 32) else none

/-- An error return: four zero words and the word 4. -/
def errView (j : Nat) : Option (Sym × Nat) :=
  if j < 32 then some (.lit 0, j % 8) else some (.lit 4, j - 32)

theorem byteOf_zero (k : Nat) : byteOf (BitVec.ofNat 64 0) k = 0 := by
  simp [byteOf]

theorem byteOf_four : ∀ k < 8, byteOf (BitVec.ofNat 64 4) k = if k = 0 then 4 else 0 := by decide

theorem succ_bytes {env : Env} {ws : List Write} {p l f c : Sym} {isList : Bool}
    {before : List Byte} (hv : viewOK ws (succView p l f c) = true)
    (hf : byteOf (f.eval env) 0 = if isList then 1 else 0)
    (hb : ∀ j < 40, env.byte0 2 j = before.getD j 0) {j : Nat} (hj : j < 40) :
    memByte env ws 2 j = successByte (p.eval env) (l.eval env) (c.eval env) isList before j := by
  rw [memByte_wview, wview_of_viewOK hv hj]
  unfold succView successByte
  by_cases h1 : j < 8
  · simp [h1]
  by_cases h2 : j < 16
  · simp [h1, h2]
  by_cases h3 : j = 16
  · subst h3; simp [hf]
  by_cases h4 : j < 24
  · simp [h1, h2, h3, h4, hb j hj]
  by_cases h5 : j < 32
  · simp [h1, h2, h3, h4, h5]
  by_cases h6 : j < 34
  · simp [h1, h2, h3, h4, h5, h6, Sym.eval]
  · simp [h1, h2, h3, h4, h5, h6, hb j hj]

theorem err_bytes {env : Env} {ws : List Write} (hv : viewOK ws errView = true) {j : Nat}
    (hj : j < 40) : memByte env ws 2 j = errorByte j := by
  rw [memByte_wview, wview_of_viewOK hv hj]
  unfold errView errorByte
  by_cases h1 : j < 32
  · simp [h1, Sym.eval]; omega
  · simp only [h1, if_false, Sym.eval]
    rw [byteOf_four (j - 32) (by omega)]
    by_cases h : j = 32
    · simp [h]
    · simp [h]; omega

/-! ## Memory after a run -/

/-- A region the leaf never wrote keeps its initial bytes. -/
theorem match_nowrite {env : Env} {S : SState} {m : Machine} (hm : Match env S m) {r : Nat}
    (hr : r < S.regions.length) (hw : S.mem.all (·.r != r) = true) {j : Nat}
    (hj : j < env.size r) : m.mem (env.base r + BitVec.ofNat 64 j) = some (env.byte0 r j) := by
  rw [hm.mem r j hr hj]
  have : S.mem.find? (·.covers r j) = none := by
    rw [List.find?_eq_none]
    intro w hw' hc
    have := List.all_eq_true.mp hw w hw'
    simp [Write.covers] at hc this
    exact this hc.1.1
  simp [memByte, this]

/-- A leaf without writes leaves memory as it was at the start of the run, provided the
environment's initial bytes are the start machine's. -/
theorem mem_eq_of_nowrite {env : Env} {S lS : SState} {m m' : Machine}
    (hm' : Match env lS m') (hfr : SameOutside (InWritable env S) m m') (hnil : lS.mem = [])
    (hreg : lS.regions = S.regions)
    (hinit : ∀ r j, r < S.regions.length → j < env.size r →
      m.mem (env.base r + BitVec.ofNat 64 j) = some (env.byte0 r j)) :
    m'.mem = m.mem := by
  funext a
  by_cases ha : InWritable env S a
  · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := ha
    have hr := (List.getElem?_eq_some_iff.mp hR).1
    rw [hm'.mem r j (by rw [hreg]; exact hr) hj, hinit r j hr hj, hnil]
    rfl
  · exact hfr a ha

/-- Memory after a leaf differs from the start only inside written regions, which `R` covers. -/
theorem so_of_leaf {env : Env} {S lS : SState} {m m' : Machine} {R : Word → Prop}
    (hfr : SameOutside (InWritable env S) m m') (hm' : Match env lS m')
    (hreg : lS.regions = S.regions)
    (hinit : ∀ r j, r < S.regions.length → j < env.size r →
      m.mem (env.base r + BitVec.ofNat 64 j) = some (env.byte0 r j))
    (hR : ∀ r j, r < S.regions.length → j < env.size r → lS.mem.all (·.r != r) = false →
      R (env.base r + BitVec.ofNat 64 j)) :
    SameOutside R m m' := by
  intro a ha
  by_cases hw : InWritable env S a
  · obtain ⟨r, R', j, hR', -, hj, rfl⟩ := hw
    have hr := (List.getElem?_eq_some_iff.mp hR').1
    by_cases hn : lS.mem.all (·.r != r) = true
    · rw [match_nowrite hm' (by rw [hreg]; exact hr) hn hj, hinit r j hr hj]
    · exact absurd (hR r j hr hj (by simpa using hn)) ha
  · exact hfr a hw

/-- The frame after `sd s0, 0(sp)` and `sd ra, 8(sp)`. -/
theorem frame_bytes (env : Env) (a b : Sym) {t : Nat} (ht : t < 8) :
    memByte env [⟨0, 0, 8, a⟩, ⟨0, 8, 8, b⟩] 0 (8 + t) = byteOf (b.eval env) t ∧
      memByte env [⟨0, 0, 8, a⟩, ⟨0, 8, 8, b⟩] 0 t = byteOf (a.eval env) t := by
  constructor
  · rw [memByte_cons, memByte_cons]
    simp [Write.covers, show ¬ 8 + t < 8 by omega]
    omega
  · rw [memByte_cons]
    simp [Write.covers, ht]

theorem SameOutside.trans' {R : Word → Prop} {m₁ m₂ m₃ : Machine} (h₁ : SameOutside R m₁ m₂)
    (h₂ : SameOutside R m₂ m₃) : SameOutside R m₁ m₃ := fun a ha => (h₂ a ha).trans (h₁ a ha)

/-! ## Byte arithmetic -/

theorem land_255 (n : Nat) : n &&& 255 = n % 256 := Nat.and_two_pow_sub_one_eq_mod n 8
theorem land_127 (n : Nat) : n &&& 127 = n % 128 := Nat.and_two_pow_sub_one_eq_mod n 7

theorem sext_and_255 : ∀ b : Byte, b.signExtend 64 &&& BitVec.ofNat 64 255 = BitVec.ofNat 64 b.toNat := by
  decide

theorem sext_slt_zero : ∀ b : Byte, (b.signExtend 64).slt (BitVec.ofNat 64 0) = decide (128 ≤ b.toNat) := by
  decide

theorem eval_sext_init (env : Env) (r off : Nat) :
    (Sym.sext 8 (Sym.init r off 1)).eval env = (env.byte0 r off).signExtend 64 := by
  simp [Sym.eval, byteList, ofBytesLE]

theorem ofBytes1 (f : Nat → Byte) (off : Nat) : ofBytesLE (byteList f off 1) = (f off).setWidth 64 := by
  simp [byteList, ofBytesLE]

theorem eval_and_sext_init (env : Env) (r off : Nat) :
    (Sym.bin .and (Sym.sext 8 (Sym.init r off 1)) (.lit 255)).eval env =
      BitVec.ofNat 64 (env.byte0 r off).toNat := by
  rw [← sext_and_255]
  simp only [Sym.eval, BinOp.eval]
  simp [byteList, ofBytesLE]

theorem eval_initx1 (env : Env) (r off : Nat) (i : Sym) :
    (Sym.initx r off i 1 1).eval env = (env.byte0 r (off + (i.eval env).toNat)).setWidth 64 := by
  simp [Sym.eval, byteList, ofBytesLE]

/-- `bigEndian` of a list with one more byte. -/
theorem bigEndian_append (l : List Byte) (c : Byte) :
    bigEndian (l ++ [c]) = 256 * bigEndian l + c.toNat := by
  simp [bigEndian, List.foldl_append]

theorem foldl_lt (l : List Byte) : ∀ acc,
    l.foldl (fun acc b => 256 * acc + b.toNat) acc < (acc + 1) * 256 ^ l.length := by
  induction l with
  | nil => intro acc; simp
  | cons c l ih =>
    intro acc
    have hc := c.isLt
    simp only [Nat.reducePow] at hc
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    refine Nat.lt_of_lt_of_le (ih _) ?_
    rw [Nat.mul_comm (256 ^ l.length) 256, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (by omega)

theorem bigEndian_lt (l : List Byte) : bigEndian l < 256 ^ l.length := by
  have := foldl_lt l 0
  simpa [bigEndian] using this

/-- One loop step on the accumulator: `(a << 8) | c`. -/
theorem shl_or (a : Nat) (c : Byte) (ha : a < 2 ^ 56) :
    (BitVec.ofNat 64 a <<< ((BitVec.ofNat 64 8).toNat % 64)) ||| c.setWidth 64 =
      BitVec.ofNat 64 (256 * a + c.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hc := c.isLt
  simp only [Nat.reducePow] at hc
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  have h2 : (8 % 2 ^ 64) % 64 = 8 := by decide
  have h3 : c.toNat % 2 ^ 64 = c.toNat := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3, Nat.shiftLeft_eq]
  have h4 : a * 2 ^ 8 % 2 ^ 64 = a * 2 ^ 8 := Nat.mod_eq_of_lt (by omega)
  rw [h4, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (i := 8) (by omega)]
  have : (2 ^ 8 * a + c.toNat) % 2 ^ 64 = 2 ^ 8 * a + c.toNat := Nat.mod_eq_of_lt (by omega)
  rw [this]

/-! ## Lists read from memory -/

/-- The `n` bytes at `a` (absent bytes read as 0). -/
def bytesOf (m : Machine) (a : Word) (n : Nat) : List Byte :=
  (List.range n).map fun j => (m.mem (a + BitVec.ofNat 64 j)).getD 0

theorem eq_bytesOf {m : Machine} {a : Word} {l : List Byte} (h : BytesAt m a l) :
    l = bytesOf m a l.length := by
  apply List.ext_getElem (by simp [bytesOf])
  intro i h1 h2
  simp [bytesOf, h i h1]

theorem bytesOf_getD (m : Machine) (a : Word) (n j : Nat) (hj : j < n) :
    (bytesOf m a n).getD j 0 = (m.mem (a + BitVec.ofNat 64 j)).getD 0 := by
  simp [bytesOf, hj]

theorem bytesOf_length (m : Machine) (a : Word) (n : Nat) : (bytesOf m a n).length = n := by
  simp [bytesOf]

theorem bytesOf_zero (m : Machine) (a : Word) : bytesOf m a 0 = [] := rfl

/-- A nonempty read splits into its first byte and the rest. -/
theorem bytesOf_cons (m : Machine) (a : Word) {n : Nat} (hn : 0 < n) :
    bytesOf m a n = (m.mem (a + BitVec.ofNat 64 0)).getD 0 :: (bytesOf m a n).drop 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [bytesOf, List.range_succ_eq_map]

theorem bytesOf_drop_getElem (m : Machine) (a : Word) (n j : Nat) (hj : j + 1 < n) :
    ((bytesOf m a n).drop 1)[j]'(by simp [bytesOf]; omega) =
      (m.mem (a + BitVec.ofNat 64 (1 + j))).getD 0 := by
  simp [bytesOf, Nat.add_comm]

/-- The first input byte. -/
def firstByte (m : Machine) : Byte := (m.mem (m.reg 11)).getD 0

theorem input_cons (m : Machine) (h : 0 < (m.reg 12).toNat) :
    bytesOf m (m.reg 11) (m.reg 12).toNat =
      firstByte m :: (bytesOf m (m.reg 11) (m.reg 12).toNat).drop 1 := by
  rw [bytesOf_cons m _ h]; simp [firstByte]

theorem input_head (m : Machine) (h : 0 < (m.reg 12).toNat) :
    (bytesOf m (m.reg 11) (m.reg 12).toNat).head? = some (firstByte m) := by
  rw [input_cons m h]; rfl

/-! ## Assembling `Post` -/

theorem notOne : BitVec.ofNat 64 18446744073709551614 = ~~~(1 : Word) := by decide

theorem post_of {m m' : Machine} (hret : Returns m m')
    (hso : SameOutside (fun a => InRange (m.reg 10) 40 a ∨ InRange (m.reg 2 - 16) 16 a) m m')
    (hbytes : ∀ j < 40, m'.mem (m.reg 10 + BitVec.ofNat 64 j) =
      some (resultByte (m.reg 11) (bytesOf m (m.reg 11) (m.reg 12).toNat)
        (bytesOf m (m.reg 10) 40) j)) : Post m m' := by
  refine ⟨hret, hso, fun input before hi hil hb hbl => ?_⟩
  rw [eq_bytesOf hi, eq_bytesOf hb, hil, hbl]
  intro i hi'
  simp only [result40, List.length_map, List.length_range] at hi'
  simpa [result40] using hbytes i hi'

/-- Callee-saved registers at a return leaf: `sp = ptr 0 16`, `s0` as given, the others their
own variables. -/
def savedOK (lS : SState) (s0 : Sym) : Bool :=
  lS.reg 2 == .ptr 0 16 && lS.reg 8 == s0 &&
    [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27].all fun i => lS.reg i == .var i

theorem returns_of {env : Env} {lS : SState} {m m' : Machine} {s0 : Sym} (hm' : Match env lS m')
    (hpc : m'.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env)
    (h1 : env.vars 1 = m.reg 1) (hok : savedOK lS s0 = true)
    (h2 : env.base 0 + BitVec.ofInt 64 16 = m.reg 2) (h8 : s0.eval env = m.reg 8)
    (hv : ∀ i : Fin 32, i.val ∈ [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
      env.vars i.val = m.reg i) : Returns m m' := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hpc]; simp only [Sym.eval, BinOp.eval, h1, notOne]
  · rw [← hm'.regs i]
    unfold savedOK at hok
    rw [Bool.and_eq_true, Bool.and_eq_true] at hok
    obtain ⟨⟨e2, e8⟩, eall⟩ := hok
    have ev : ∀ k ∈ [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], lS.reg k = .var k :=
      fun k hk => eq_of_beq (List.all_eq_true.mp eall k hk)
    have hvv : ∀ i : Fin 32, i.val ∈ [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        (lS.reg i.val).eval env = m.reg i := fun i hi => by
      rw [ev _ hi]; exact hv i hi
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show (lS.reg 2).eval env = _
      rw [eq_of_beq e2]; exact h2
    · show (lS.reg 8).eval env = _
      rw [eq_of_beq e8]; exact h8
    all_goals exact hvv _ (by decide)

/-- The outcome bytes of a success leaf. -/
theorem bytes_succ {env : Env} {lS : SState} {m m' : Machine} {p l f c : Sym} {isList : Bool}
    {h pl : Nat} (hm' : Match env lS m') (hlen : lS.regions.length = 3)
    (hb2 : env.base 2 = m.reg 10) (hs2 : env.size 2 = 40)
    (hv : viewOK lS.mem (succView p l f c) = true)
    (hf : byteOf (f.eval env) 0 = if isList then 1 else 0)
    (hb : ∀ j < 40, env.byte0 2 j = (bytesOf m (m.reg 10) 40).getD j 0)
    (hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .success isList h pl)
    (hp : p.eval env = if (bytesOf m (m.reg 11) (m.reg 12).toNat).head? = some 128 then 1
      else m.reg 11 + BitVec.ofNat 64 h)
    (hl : l.eval env = BitVec.ofNat 64 pl) (hc : c.eval env = BitVec.ofNat 64 (h + pl)) :
    ∀ j < 40, m'.mem (m.reg 10 + BitVec.ofNat 64 j) =
      some (resultByte (m.reg 11) (bytesOf m (m.reg 11) (m.reg 12).toNat)
        (bytesOf m (m.reg 10) 40) j) := by
  intro j hj
  have hmj := hm'.mem 2 j (by omega) (by omega)
  rw [hb2] at hmj
  rw [hmj, succ_bytes hv hf hb hj, resultByte, hdec]
  simp only [hp, hl, hc]

/-- The outcome bytes of an error leaf. -/
theorem bytes_err {env : Env} {lS : SState} {m m' : Machine} (hm' : Match env lS m')
    (hlen : lS.regions.length = 3) (hb2 : env.base 2 = m.reg 10) (hs2 : env.size 2 = 40)
    (hv : viewOK lS.mem errView = true)
    (hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error) :
    ∀ j < 40, m'.mem (m.reg 10 + BitVec.ofNat 64 j) =
      some (resultByte (m.reg 11) (bytesOf m (m.reg 11) (m.reg 12).toNat)
        (bytesOf m (m.reg 10) 40) j) := by
  intro j hj
  have hmj := hm'.mem 2 j (by omega) (by omega)
  rw [hb2] at hmj
  rw [hmj, err_bytes hv hj, resultByte, hdec]

end ZesuExec.Fn.F2
