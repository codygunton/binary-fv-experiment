import ZesuExec.Fn.Stage

/-!
# Where a leaf's memory bytes come from

`memSrc ws r j` reads off a leaf's write list which initial byte (region, offset) ends up at
offset `j` of region `r`: the newest write covering it, through `init`, `bytes` and the 16/32-bit
sign extensions `lh`/`lw` produce; `memSrc_sound` makes that a `memByte` equation. A leaf that
moves whole elements (the copies into the frame, the swaps of the inlined `mem.rotate`) is then
checked byte by byte with `decide` on its literal write list.
-/

namespace ZesuExec.Fn.MergeInPlace
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-- Byte `t` of `v`'s value as a byte of a region's initial memory, read off the form. -/
def srcB : Sym → Nat → Option (Nat × Nat)
  | .init r off n, t => if t < n ∧ n ≤ 8 then some (r, off + t) else none
  | .sext bits a, t => if (bits = 32 ∧ t < 4) ∨ (bits = 16 ∧ t < 2) then srcB a t else none
  | .bytes a k n, t => if t < n ∧ n ≤ 8 ∧ k + t < 8 then srcB a (k + t) else none
  | _, _ => none

theorem byteList_getElem' (f : Nat → Byte) : ∀ (k n u : Nat) (h : u < (byteList f k n).length),
    (byteList f k n)[u] = f (k + u)
  | k, 0, u, h => by simp [byteList] at h
  | k, n + 1, 0, _ => by simp [byteList]
  | k, n + 1, u + 1, h => by
    simp only [byteList, List.getElem_cons_succ]
    rw [byteList_getElem' f (k + 1) n u (by simp only [byteList, List.length_cons] at h; omega)]
    congr 1; omega

theorem byteOf_byteList' {f : Nat → Byte} {k n u : Nat} (hn : n ≤ 8) (hu : u < n) :
    byteOf (ofBytesLE (byteList f k n)) u = f (k + u) := by
  rw [byteOf_ofBytesLE _ (by rw [byteList_length]; exact hn) u (by rw [byteList_length]; exact hu),
    byteList_getElem']

theorem byteOf_sext (x : Word) {bits u : Nat} (hb : bits = 32 ∧ u < 4 ∨ bits = 16 ∧ u < 2) :
    byteOf ((x.setWidth bits).signExtend 64) u = byteOf x u := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb'
  simp only [byteOf, BitVec.getLsbD_extractLsb', hb', decide_true, Bool.true_and,
    BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth]
  rcases hb with ⟨rfl, hu⟩ | ⟨rfl, hu⟩
  · simp [show 8 * u + b < 32 by omega, show 8 * u + b < 64 by omega]
  · simp [show 8 * u + b < 16 by omega, show 8 * u + b < 64 by omega]

theorem srcB_sound (env : Env) : ∀ {v : Sym} {t r o : Nat}, srcB v t = some (r, o) →
    t < 8 ∧ byteOf (v.eval env) t = env.byte0 r o
  | .init r' off n, t, r, o, h => by
    simp only [srcB] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, by simp only [Sym.eval]; rw [byteOf_byteList' hc.2 hc.1]⟩
    · cases h
  | .sext bits a, t, r, o, h => by
    simp only [srcB] at h
    split at h
    · next hc =>
      obtain ⟨ht, he⟩ := srcB_sound env h
      exact ⟨ht, by simp only [Sym.eval]; rw [byteOf_sext _ hc, he]⟩
    · cases h
  | .bytes a k n, t, r, o, h => by
    simp only [srcB] at h
    split at h
    · next hc =>
      obtain ⟨-, he⟩ := srcB_sound env h
      refine ⟨by omega, ?_⟩
      simp only [Sym.eval]
      rw [byteOf_byteList' hc.2.1 hc.1, he]
    · cases h
  | .lit _, _, _, _, h => by simp [srcB] at h
  | .var _, _, _, _, h => by simp [srcB] at h
  | .ptr _ _, _, _, _, h => by simp [srcB] at h
  | .initx _ _ _ _ _, _, _, _, h => by simp [srcB] at h
  | .bin _ _ _, _, _, _, h => by simp [srcB] at h
  | .cat _ _ _, _, _, _, h => by simp [srcB] at h

/-- The initial byte at offset `j` of region `r` after the writes `ws`. -/
def memSrc (ws : List Write) (r j : Nat) : Option (Nat × Nat) :=
  match ws.find? (·.covers r j) with
  | some w => srcB w.v (j - w.off)
  | none => some (r, j)

theorem memSrc_sound {env : Env} {ws : List Write} {r j r' o : Nat} (h : memSrc ws r j = some (r', o)) :
    memByte env ws r j = env.byte0 r' o := by
  unfold memSrc at h; unfold memByte
  split at h
  · next w hw => rw [hw]; exact (srcB_sound env h).2
  · next hw =>
    rw [hw]; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl

end ZesuExec.Fn.MergeInPlace
