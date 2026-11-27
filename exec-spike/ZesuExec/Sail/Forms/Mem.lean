import ZesuExec.Sail.Forms.Common

/-!
# Memory-access lemmas shared by the load and store simulations

Byte lists: `Machine.readBytes` against Sail's byte map, the little-endian value of a byte list
(`leNat`) as both `Machine.ofBytesLE` and the generated `leWord`, alignment, and the PMA checks of
the profile's regions for the accesses `Machine.load` and `Machine.store` admit.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- Little-endian value of a byte list. -/
def leNat : List (BitVec 8) → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

theorem leNat_lt : ∀ bs : List (BitVec 8), leNat bs < 256 ^ bs.length
  | [] => by simp [leNat]
  | b :: bs => by
    have := leNat_lt bs; have := b.isLt
    simp only [leNat, List.length_cons, Nat.pow_succ]
    omega

theorem toNat_leWord : ∀ bs : List (BitVec 8), (leWord bs).toNat = leNat bs
  | [] => by simp [leWord, leNat]
  | b :: bs => by
    simp only [leWord, BitVec.toNat_cast, toNat_append_add, toNat_leWord bs, leNat]
    omega

theorem toNat_ofBytesLE : ∀ bs : List (BitVec 8), bs.length ≤ 8 →
    (Machine.ofBytesLE bs).toNat = leNat bs
  | [] => by simp [Machine.ofBytesLE, leNat]
  | b :: bs => by
    intro h
    have ih := toNat_ofBytesLE bs (by simp at h; omega)
    have hl := leNat_lt bs
    have hb := b.isLt
    have hp : 256 ^ bs.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by simp at h; omega)
    simp only [Machine.ofBytesLE, leNat]
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, ih, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (a := leNat bs * 2 ^ 8) (by simp only [Nat.reducePow] at hp ⊢; omega),
      Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      Nat.shiftLeft_eq]
    omega

/-- The bytes `Machine.readBytes` returns are the bytes at `a, a+1, …`. -/
theorem readBytes_spec {mem : Word → Option Byte} :
    ∀ (n a : Nat) (bs : List Byte), Machine.readBytes mem a n = some bs →
      bs.length = n ∧ ∀ i (h : i < bs.length), mem (BitVec.ofNat 64 (a + i)) = some bs[i]
  | 0, a, bs, h => by
    simp only [Machine.readBytes, Option.some.injEq] at h; subst h; simp
  | n + 1, a, bs, h => by
    unfold Machine.readBytes at h
    split at h
    · rename_i b bs' hb hbs
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hl, hi⟩ := readBytes_spec n (a + 1) bs' hbs
      refine ⟨by simp [hl], fun i hi' => ?_⟩
      cases i with
      | zero => simpa using hb
      | succ i =>
        have := hi i (by simp at hi'; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    · cases h

/-- Present bytes of `m` are present in Sail's byte map, at addresses below `2^64`. -/
theorem Rel.memAt {img : Image} {m : Machine} {s : State} (hR : Rel img m s) {x : Nat}
    {b : Byte} (hx : x < 2 ^ 64) (h : m.mem (BitVec.ofNat 64 x) = some b) :
    s.mem.get? x = some b := by
  have := hR.mem _ _ h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this

theorem aligned_of_mod {a : BitVec 64} {n : Nat} (h : a.toNat % n = 0) :
    is_aligned_vaddr (virtaddr.Virtaddr a) n = true ∧
      is_aligned_paddr (physaddr.Physaddr a) n = true := by
  have h' : (a.toNat : Int).tmod n = 0 := by
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]; exact_mod_cast h
  constructor
  · unfold is_aligned_vaddr; simp only [Sail.BitVec.toNatInt]; simp [h']
  · unfold is_aligned_paddr; simp only [Sail.BitVec.toNatInt]; simp [h']

/-- A range `Machine.readable` admits passes the profile's load PMA check. -/
theorem loadPma {st : State} (hp : st.regs.get? pma_regions = some zesuPmaRegions)
    {a : BitVec 64} {n : Nat} (hn : 0 < n) (h : Machine.readable a.toNat n = true) :
    DataPmaAllows .load st a n := by
  simp only [Machine.readable, Machine.inRange, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Layout.rodataLo, Layout.rodataHi, Layout.inputLo, Layout.inputHi,
    Layout.ramLo, Layout.ramHi] at h
  rcases h with (h | h) | h
  · exact ⟨_, _, hp, matching_rom a n hn (by omega), rfl⟩
  · exact ⟨_, _, hp, matching_input a n (by omega), rfl⟩
  · exact ⟨_, _, hp, matching_ram a n (by omega), rfl⟩

/-- A range `Machine.writable` admits passes the profile's store PMA check. -/
theorem storePma {st : State} (hp : st.regs.get? pma_regions = some zesuPmaRegions)
    {a : BitVec 64} {n : Nat} (h : Machine.writable a.toNat n = true) :
    DataPmaAllows .store st a n := by
  simp only [Machine.writable, Machine.inRange, Bool.and_eq_true, decide_eq_true_eq,
    Layout.ramLo, Layout.ramHi] at h
  exact ⟨_, _, hp, matching_ram a n (by omega), rfl⟩

/-! ## Stores -/

theorem extractLsb'_ushiftRight (v : Word) (j : Nat) :
    (v >>> 8).extractLsb' (8 * j) 8 = v.extractLsb' (8 * (j + 1)) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3; omega

/-- `Machine.writeBytes` puts byte `j` of `v` at `a + j`. -/
theorem writeBytes_at (mem : Word → Option Byte) :
    ∀ (n a : Nat) (v : Word) (j : Nat), j < n → a + n ≤ 2 ^ 64 →
      Machine.writeBytes mem a v n (BitVec.ofNat 64 (a + j)) = some (v.extractLsb' (8 * j) 8)
  | 0, _, _, _, hj, _ => absurd hj (by omega)
  | n + 1, a, v, j, hj, ha => by
    simp only [Machine.writeBytes]
    cases j with
    | zero => simp
    | succ j =>
      have hne : BitVec.ofNat 64 (a + (j + 1)) ≠ BitVec.ofNat 64 a := by
        intro h; have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
      rw [if_neg hne, show a + (j + 1) = a + 1 + j by omega,
        writeBytes_at mem n (a + 1) (v >>> 8) j (by omega) (by omega), extractLsb'_ushiftRight]

/-- `Machine.writeBytes` leaves every other address alone. -/
theorem writeBytes_outside (mem : Word → Option Byte) :
    ∀ (n a : Nat) (v : Word) (x : Word), (∀ j, j < n → x ≠ BitVec.ofNat 64 (a + j)) →
      Machine.writeBytes mem a v n x = mem x
  | 0, _, _, _, _ => rfl
  | n + 1, a, v, x, hx => by
    simp only [Machine.writeBytes]
    rw [if_neg (by simpa using hx 0 (by omega))]
    exact writeBytes_outside mem n (a + 1) (v >>> 8) x
      (fun j hj => by rw [show a + 1 + j = a + (j + 1) by omega]; exact hx (j + 1) (by omega))

/-- A write list whose writes to `x` all store `b`, with at least one, leaves `b` at `x`. -/
theorem afterByteWrites_get?_of_mem (st : State) :
    ∀ (writes : List (Nat × BitVec 8)) (x : Nat) (b : BitVec 8),
      (∃ wr ∈ writes, wr.1 = x) → (∀ wr ∈ writes, wr.1 = x → wr.2 = b) →
      (afterByteWrites st writes).mem.get? x = some b
  | [], _, _, ⟨_, h, _⟩, _ => by cases h
  | wr :: ws, x, b, hex, hall => by
    change (afterByteWrites { st with mem := st.mem.insert wr.1 wr.2 } ws).mem.get? x = some b
    by_cases ht : ∃ wr' ∈ ws, wr'.1 = x
    · exact afterByteWrites_get?_of_mem _ ws x b ht (fun wr' h => hall wr' (by simp [h]))
    · have hnot : ∀ wr' ∈ ws, wr'.1 ≠ x := fun wr' h e => ht ⟨wr', h, e⟩
      rw [afterByteWrites_mem_get?_of_not_written _ ws x hnot]
      obtain ⟨wr0, hm, he⟩ := hex
      have hhd : wr.1 = x := by
        rcases List.mem_cons.mp hm with h | h
        · subst h; exact he
        · exact absurd he (hnot wr0 h)
      change (st.mem.insert wr.1 wr.2).get? x = some b
      rw [← hhd, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert_self,
        hall wr (by simp) hhd]

theorem afterWriteBytes_at (st : State) (a : Nat) {n : Nat} (data : BitVec (8 * n)) (j : Nat)
    (hj : j < n) :
    (afterWriteBytes st a data).mem.get? (a + j) = some (data.extractLsb' (8 * j) 8) := by
  apply afterByteWrites_get?_of_mem
  · exact ⟨_, List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩, rfl⟩
  · intro wr hwr he
    obtain ⟨⟨j', hj'⟩, rfl⟩ := List.mem_ofFn.mp hwr
    simp only at he ⊢
    have : j' = j := by omega
    subst this; rfl

/-- **Generic store step.** An `execute` run that writes the `n` bytes `data` at `addr` (and
nothing else) simulates `Machine.store` of `v` at `addr`, provided `data`'s bytes are `v`'s. -/
theorem sim_store_of_exec {img : Image} {m : Machine} {s : State} {w : Nat} {i : Instr}
    (hR : Rel img m s) (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some i)
    (hpc : Layout.textLo ≤ m.pc.toNat ∧ m.pc.toNat < Layout.textHi ∧ m.pc.toNat % 4 = 0)
    {addr v : Word} {n : Nat} {data : BitVec (8 * n)}
    (hwr : Machine.writable addr.toNat n = true)
    (hbytes : ∀ j, j < n → data.extractLsb' (8 * j) 8 = v.extractLsb' (8 * j) 8)
    (hexec : Runs (execute (toSail i)) (T s m.pc) (afterWriteBytes (T s m.pc) addr.toNat data)
      (.Retire_Success ()))
    (n' : Nat) :
    ∃ s', Runs (try_step n' false) s s' false ∧
      Rel img ({ m with mem := Machine.writeBytes m.mem addr.toNat v n } : Machine).advance s' := by
  simp only [Machine.writable, Machine.inRange, Bool.and_eq_true, decide_eq_true_eq,
    Layout.ramLo, Layout.ramHi] at hwr
  have hregs : (afterWriteBytes (T s m.pc) addr.toNat data).regs = (T s m.pc).regs :=
    afterWriteBytes_regs _ _ _
  have hout : ∀ x, (x < addr.toNat ∨ addr.toNat + n ≤ x) →
      (afterWriteBytes (T s m.pc) addr.toNat data).mem.get? x = s.mem.get? x :=
    fun x hx => afterWriteBytes_mem_get?_of_outside _ _ _ _ (fun j => by omega)
  refine sim_of_exec hR hw hd hpc hexec ?_ ?_ ?_ ?_ ?_ n'
  · rw [hregs, T_nextPC]; rfl
  · intro r _ _; rw [hregs]
  · intro j hj; rw [hregs]; exact RegsAgree.T (m := m) hR.regs m.pc j hj
  · intro x b hb
    simp only [Machine.advance] at hb
    by_cases hin : addr.toNat ≤ x.toNat ∧ x.toNat < addr.toNat + n
    · have hx : x = BitVec.ofNat 64 (addr.toNat + (x.toNat - addr.toNat)) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [hx, writeBytes_at _ _ _ _ _ (by omega) (by omega)] at hb
      cases hb
      rw [show x.toNat = addr.toNat + (x.toNat - addr.toNat) by omega,
        afterWriteBytes_at _ _ _ _ (by omega), hbytes _ (by omega), Nat.add_sub_cancel_left]
    · rw [writeBytes_outside _ _ _ _ _ (fun j hj e => hin (by
          rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))] at hb
      rw [hout _ (by omega)]; exact hR.mem x b hb
  · intro seg hseg k w' hk h1 h2 j hj
    simp only [Layout.textLo, Layout.textHi] at h1 h2
    rw [hout _ (by omega)]
    exact hR.code seg hseg k w' hk h1 h2 j hj

end ZesuExec.SailLink
