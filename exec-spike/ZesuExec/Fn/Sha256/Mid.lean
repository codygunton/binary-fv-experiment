import ZesuExec.Fn.Sha256.Seg
import ZesuExec.Fn.Sha256.Facts

/-!
# `zkvm_sha256`: what holds between the prologue and the output (`Mid`)

`Mid m0 m`: `sp` is the entry `sp` less the frame, `a2`, `ra` and `s0`–`s11` are the entry's, the
frame holds the saved registers at `0x78 … 0xd8`, the bump words hold `bumpBytes`, the frame and
the staging word are present, and memory outside the frame, the bump words and the staging word
is the entry's. `segM` runs a symbolic piece in shape `shapeM`; `mid_leaf` keeps `Mid` across a
piece that writes only frame offsets below `0x78` and keeps those registers.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Fn

/-- The registers the prologue saves, with their frame offsets. -/
def savedRegs : List (Fin 32 × Nat) :=
  [(1, 0xd8), (8, 0xd0), (9, 0xc8), (18, 0xc0), (19, 0xb8), (20, 0xb0), (21, 0xa8), (22, 0xa0),
   (23, 0x98), (24, 0x90), (25, 0x88), (26, 0x80), (27, 0x78)]

/-- The saved registers are not the ones the body uses as temporaries. -/
theorem savedRegs_ne : ∀ p ∈ savedRegs, p.1 ≠ 0 ∧ p.1 ≠ 2 ∧ p.1 ≠ 5 ∧ p.1 ≠ 6 ∧ p.1 ≠ 7 ∧
    p.1 ≠ 10 ∧ p.1 ≠ 11 ∧ p.1 ≠ 12 ∧ p.1 ≠ 13 ∧ p.1 ≠ 14 ∧ p.1 ≠ 15 ∧ p.1 ≠ 16 ∧ p.1 ≠ 17 := by
  decide

/-- `sp` after the prologue. -/
def spM (m0 : Machine) : Word := m0.reg 2 - BitVec.ofNat 64 frameSize

def bumpW : Word := BitVec.ofNat 64 bump
def stageW : Word := BitVec.ofNat 64 Layout.extraParams

/-- What the code may write before the output: the frame, the bump words, the staging word. -/
def WrittenMid (m0 : Machine) (a : Word) : Prop :=
  InRange (spM m0) frameSize a ∨ InRange bumpW 16 a ∨ InRange stageW 8 a

/-- The bytes `bs` at frame offset `off`. -/
def FrameAt (m : Machine) (off : Nat) (bs : List Byte) : Prop :=
  ∀ i (h : i < bs.length), m.mem (m.reg 2 + BitVec.ofNat 64 (off + i)) = some bs[i]

/-- The eight little-endian bytes of a word. -/
def le8 (v : Word) : List Byte := byteList (byteOf v) 0 8

structure Mid (m0 m : Machine) : Prop where
  sp : m.reg 2 = spM m0
  out : m.reg 12 = m0.reg 12
  saved : ∀ p ∈ savedRegs, m.reg p.1 = m0.reg p.1
  same : SameOutside (WrittenMid m0) m0 m
  frame : ∀ j < frameSize, (m.mem (m.reg 2 + BitVec.ofNat 64 j)).isSome
  savedMem : ∀ p ∈ savedRegs, FrameAt m p.2 (le8 (m0.reg p.1))
  bump : BytesAt m bumpW bumpBytes
  stage : ∀ j < 8, (m.mem (stageW + BitVec.ofNat 64 j)).isSome

/-- The numbers `Pre` gives about the stack: `spM` is 16-aligned and its frame lies in RAM. -/
theorem spM_facts {m0 : Machine} (h : Pre m0) :
    (spM m0).toNat = (m0.reg 2).toNat - frameSize ∧ (spM m0).toNat % 16 = 0 ∧
      Layout.ramLo ≤ (spM m0).toNat ∧ (spM m0).toNat + frameSize ≤ Layout.ramHi := by
  obtain ⟨-, ⟨hal, hlo, hhi, -⟩, -⟩ := h
  have : (spM m0).toNat = (m0.reg 2).toNat - frameSize := by
    simp only [spM, frameSize, BitVec.toNat_sub, BitVec.toNat_ofNat]
    unfold frameSize Layout.ramLo at hlo; omega
  refine ⟨this, ?_, ?_, ?_⟩ <;> rw [this] <;> unfold frameSize at * <;>
    unfold Layout.ramLo Layout.ramHi at * <;> omega

def envM (m : Machine) : Env := entryEnv m ((shapeM m).map (·.1))

theorem envM_base0 (m : Machine) : (envM m).base 0 = m.reg 2 := rfl
theorem envM_size0 (m : Machine) : (envM m).size 0 = 0xe0 := rfl

@[simp] theorem envM_vars (m : Machine) (i : Nat) : (envM m).vars i = m.reg (Fin.ofNat 32 i) := rfl

/-- A symbolic piece in shape `shapeM` from a machine satisfying `Mid`. -/
theorem segM {cuts : List Nat} {fuel pc : Nat} {ls : List Leaf}
    (h : run zesuImage cuts fuel pc SM = some ls) {m0 m : Machine} (hpre : Pre m0)
    (hmid : Mid m0 m) (hro : RodataLoaded zesuImage m) (hpc : m.pc.toNat = pc) :
    ∃ l ∈ ls, (∀ c ∈ l.conds, c.eval (envM m) = true) ∧
      ((∀ o ∈ l.obligs, o.holds (envM m)) →
        ∃ m', RunsIn zesuImage l.S.steps m m' ∧ Match (envM m) l.S m' ∧
          ExitOk (envM m) l.exit m' ∧ SameOutside (InRange (m.reg 2) 0xe0) m m') := by
  obtain ⟨_, hal, hlo, hhi⟩ := spM_facts hpre
  rw [← hmid.sp] at hal hlo hhi
  obtain ⟨l, hl, hc, hr⟩ := seg_sound (ov := ovM) (shape := shapeM m) h
    (by
      simp only [shapeM, List.mem_singleton, forall_eq, RegionOk, frameRg]
      refine ⟨by simp, by simpa using hal, ?_⟩
      simp only [if_true, writable, inRange, Bool.and_eq_true, decide_eq_true_eq]
      unfold frameSize at *; exact ⟨hlo, hhi⟩)
    (by simp [shapeM])
    (fun r j hr hj => by
      simp [shapeM] at hr; subst hr
      exact hmid.frame j (by simpa [entryEnv, Env.size, shapeM, frameSize] using hj))
    (fun i hi s hs => by
      simp only [ovM] at hs
      split at hs
      · next h2 =>
        cases hs
        have : i = 2 := Fin.ext h2
        subst this
        simp [Sym.eval, Env.base, entryEnv, shapeM]
      · simp at hs)
    hpc hro
  refine ⟨l, hl, hc, fun ho => ?_⟩
  obtain ⟨m', h1, h2, h3, h4⟩ := hr ho
  refine ⟨m', h1, h2, h3, SameOutside.mono h4 fun a ha => ?_⟩
  obtain ⟨p, hp, -, hin⟩ := inWritable_entry ha (by
    simp [shapeM]; unfold frameSize Layout.ramHi at hhi; omega)
  simp [shapeM] at hp; subst hp
  exact hin

/-- An address `a + t` of a range disjoint from `[lo, lo + n)` is outside it. -/
theorem notIn_of_disjoint {lo : Word} {n a k t : Nat} (hd : lo.toNat + n ≤ a ∨ a + k ≤ lo.toNat)
    (ht : t < k) (ha : a + k ≤ 2 ^ 64) : ¬ InRange lo n (BitVec.ofNat 64 (a + t)) := by
  unfold InRange
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The bytes of a present range, one at a time. -/
theorem present_at {mem : Word → Option Byte} {a n : Nat} (h : present mem a n = true) :
    ∀ t < n, (mem (BitVec.ofNat 64 (a + t))).isSome := readBytes_isSome_get h

theorem present_keep {R : Word → Prop} {m m' : Machine} (h : SameOutside R m m') {a n : Nat}
    (hR : ∀ t < n, ¬ R (BitVec.ofNat 64 (a + t))) (hp : present m.mem a n = true) :
    (readBytes m'.mem a n).isSome := by
  apply readBytes_isSome_of
  intro t ht
  rw [h _ (hR t ht)]
  exact present_at hp t ht

theorem writeBytes_out {mem : Word → Option Byte} {a : Nat} {v : Word} {n : Nat} {x : Word}
    (ha : a + n ≤ 2 ^ 64) (h : ¬ (a ≤ x.toNat ∧ x.toNat < a + n)) : writeBytes mem a v n x = mem x := by
  rw [writeBytes_apply ha, if_neg h]

theorem le8_length (v : Word) : (le8 v).length = 8 := byteList_length _ _ _

theorem le8_get (v : Word) (i : Nat) (h : i < (le8 v).length) : (le8 v)[i] = byteOf v i := by
  have h8 : i < 8 := by rw [le8_length] at h; exact h
  unfold le8
  match i, h8 with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

theorem ofBytesLE_le8 (v : Word) : ofBytesLE (le8 v) = v := ofBytesLE_bytes8 v

/-- A list of bytes, one address at a time. -/
theorem readBytes_of_list {mem : Word → Option Byte} :
    ∀ {a : Nat} {L : List Byte}, (∀ t (h : t < L.length), mem (BitVec.ofNat 64 (a + t)) = some L[t]) →
      readBytes mem a L.length = some L
  | _, [], _ => rfl
  | a, b :: L, h => by
    have h0 := h 0 (by simp)
    have hr : readBytes mem (a + 1) L.length = some L := readBytes_of_list fun t ht => by
      have := h (t + 1) (by simp; omega)
      rw [show a + (t + 1) = a + 1 + t by omega] at this
      simpa using this
    simp only [List.length_cons, readBytes]
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0, hr]

/-- The bytes at a frame offset, read from the frame's address. -/
theorem readBytes_frame {m : Machine} {off : Nat} {L : List Byte} (h : FrameAt m off L) :
    readBytes m.mem ((m.reg 2).toNat + off) L.length = some L :=
  readBytes_of_list fun t ht => by
    rw [← h t ht, ← ofNat_toNat_add, Nat.add_assoc]

/-! ## Reading a leaf's memory -/

theorem mem_of_find {env : Env} {S : SState} {m' : Machine} (hm : Match env S m') {r j : Nat}
    (hr : r < S.regions.length) (hj : j < env.size r) {w : Write}
    (hw : S.mem.find? (·.covers r j) = some w) :
    m'.mem (env.base r + BitVec.ofNat 64 j) = some (byteOf (w.v.eval env) (j - w.off)) := by
  rw [hm.mem r j hr hj]; simp [memByte, hw]

theorem mem_of_none {env : Env} {S : SState} {m' : Machine} (hm : Match env S m') {r j : Nat}
    (hr : r < S.regions.length) (hj : j < env.size r)
    (hw : S.mem.find? (·.covers r j) = none) :
    m'.mem (env.base r + BitVec.ofNat 64 j) = some (env.byte0 r j) := by
  rw [hm.mem r j hr hj]; simp [memByte, hw]

/-- An untouched byte of an entry region keeps its value. -/
theorem mem_keep {m m' : Machine} {regs : List (Word × Nat)} {S : SState}
    (hm : Match (entryEnv m regs) S m') {r j : Nat} (hr : r < S.regions.length)
    (hj : j < (entryEnv m regs).size r) (hw : S.mem.find? (·.covers r j) = none)
    (hp : (m.mem ((entryEnv m regs).base r + BitVec.ofNat 64 j)).isSome) :
    m'.mem ((entryEnv m regs).base r + BitVec.ofNat 64 j) =
      m.mem ((entryEnv m regs).base r + BitVec.ofNat 64 j) := by
  rw [mem_of_none hm hr hj hw]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hp
  rw [hb]
  simp [Env.byte0, entryEnv, Env.base] at hb ⊢
  simp [hb]

theorem reg_of_match {env : Env} {S : SState} {m' : Machine} (hm : Match env S m') (i : Fin 32) :
    m'.reg i = (S.reg i.val).eval env := (hm.regs i).symm

/-- A register the leaf did not write reads as at the start. -/
theorem reg_kept {m m' : Machine} {regs : List (Word × Nat)} {S : SState}
    (hm : Match (entryEnv m regs) S m') {i : Fin 32}
    (h : S.reg i.val = if i.val = 0 then .lit 0 else .var i.val) : m'.reg i = m.reg i := by
  rw [reg_of_match hm, h]
  split
  · next h0 => simp [Sym.eval, Machine.reg, h0]
  · simp [Sym.eval, entryEnv]

/-! ## One ordinary instruction -/

@[simp] theorem mk_reg (m : Machine) (pc : Word) (mem : Word → Option Byte) (i : Fin 32) :
    (Machine.mk m.regs pc mem).reg i = m.reg i := rfl
@[simp] theorem advance_reg (m : Machine) (i : Fin 32) : m.advance.reg i = m.reg i := rfl
@[simp] theorem advance_mem (m : Machine) : m.advance.mem = m.mem := rfl
@[simp] theorem advance_pc (m : Machine) : m.advance.pc = m.pc + 4 := rfl
@[simp] theorem setReg_mem (m : Machine) (i : Fin 32) (v : Word) : (m.setReg i v).mem = m.mem := by
  unfold Machine.setReg; split <;> rfl
@[simp] theorem setReg_pc (m : Machine) (i : Fin 32) (v : Word) : (m.setReg i v).pc = m.pc := by
  unfold Machine.setReg; split <;> rfl
theorem setReg_reg (m : Machine) (i j : Fin 32) (v : Word) :
    (m.setReg i v).reg j = if j = i ∧ i.val ≠ 0 then v else m.reg j := by
  unfold Machine.setReg Machine.reg
  by_cases h : i.val = 0
  · simp only [h, if_true, ne_eq, not_true_eq_false, and_false, if_false]
  · simp only [h, if_false, ne_eq, not_false_eq_true, and_true]
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj]

theorem reg_adv_ne {m : Machine} {rd i : Fin 32} {v : Word} (h : i ≠ rd) :
    ((m.setReg rd v).advance).reg i = m.reg i := by
  rw [advance_reg, setReg_reg, if_neg (fun h' => h h'.1)]

theorem reg_adv_eq {m : Machine} {rd : Fin 32} {v : Word} (h : rd.val ≠ 0) :
    ((m.setReg rd v).advance).reg rd = v := by
  rw [advance_reg, setReg_reg, if_pos ⟨rfl, h⟩]

/-- A store of `n` bytes of `rs2` at `rs1 + imm`, all in present RAM. -/
theorem exec_store {m : Machine} {rs1 rs2 : Fin 32} {imm : BitVec 12} {n : Nat}
    (hw : writable (m.reg rs1 + Machine.sx imm).toNat n = true)
    (hp : (readBytes m.mem (m.reg rs1 + Machine.sx imm).toNat n).isSome = true) :
    m.storeFrom rs1 rs2 imm n = some { m with
      mem := writeBytes m.mem (m.reg rs1 + Machine.sx imm).toNat (m.reg rs2) n, pc := m.pc + 4 } := by
  simp only [Machine.storeFrom, Machine.store]
  rw [if_pos ⟨hw, hp⟩]; rfl

end ZesuExec.Fn.Sha256
