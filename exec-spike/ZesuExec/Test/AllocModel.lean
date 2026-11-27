import ZesuExec.Fn.Assumed
import ZesuExec.Image

/-!
# `AllocAssumptions` has a model with a non-empty live block

Before `heap_frame` required the live blocks to stay present, its premises let a machine drop
a live block's bytes and keep `Heap L`, so `live_ok` forced every live block to be empty
(`heap_blocks_empty`, found by S1StaticMap): `alloc`'s non-null answer was unsatisfiable. This
file builds an instance of the strengthened structure over `zesuImage` whose heap has one live
block of one byte, so no such argument goes through any more.

The model: the one live block is the first byte of RAM, the only present byte; `Priv L` is every
address outside the live blocks. `alloc` and `free` hold vacuously: their precondition asks for
16 present stack bytes. `Arena` is every address (`Priv L` and the live blocks cover it).
-/

namespace ZesuExec.Test.AllocModel
open ZesuExec ZesuExec.Fn

def blk : Word × Nat := (BitVec.ofNat 64 Layout.ramLo, 1)

/-- One live block, its byte present, every other byte absent. -/
def MHeap (L : List (Word × Nat)) (m : Machine) : Prop :=
  L = [blk] ∧ (m.mem blk.1).isSome ∧ ∀ a, a ≠ blk.1 → m.mem a = none

def MPriv (L : List (Word × Nat)) (a : Word) : Prop := ¬ InLive L a

theorem inLive_blk {a : Word} : InLive [blk] a ↔ a = blk.1 := by
  constructor
  · rintro ⟨b, hb, h1, h2⟩
    simp only [List.mem_singleton] at hb; subst hb
    simp only [blk] at h1 h2 ⊢
    exact BitVec.eq_of_toNat_eq (by omega)
  · rintro rfl; exact ⟨blk, List.mem_singleton_self _, Nat.le_refl _, by simp [blk]⟩

/-- Two neighbouring bytes are never both present. -/
theorem no_stack {L : List (Word × Nat)} {m : Machine} (h : MHeap L m) : ¬ StackOk m 16 := by
  rintro ⟨-, -, -, hs⟩
  have h0 := hs 0 (by decide); have h1 := hs 1 (by decide)
  have e0 : m.reg 2 - BitVec.ofNat 64 16 + BitVec.ofNat 64 0 = blk.1 :=
    Classical.byContradiction fun hne => by rw [h.2.2 _ hne] at h0; cases h0
  have e1 : m.reg 2 - BitVec.ofNat 64 16 + BitVec.ofNat 64 1 = blk.1 :=
    Classical.byContradiction fun hne => by rw [h.2.2 _ hne] at h1; cases h1
  rw [← e0] at e1
  have := congrArg BitVec.toNat e1
  simp at this; bv_omega

def model : AllocAssumptions zesuImage where
  Heap := MHeap
  Priv := MPriv
  priv_not_live _ _ h := h
  heap_frame L m m' h hpriv hpres := by
    obtain ⟨rfl, -, hz⟩ := h
    refine ⟨rfl, by simpa [blk] using hpres blk (List.mem_singleton_self _) 0 (by decide),
      fun a ha => ?_⟩
    rw [hpriv a (fun hl => ha (inLive_blk.mp hl)), hz a ha]
  live_ok L m h := by
    obtain ⟨rfl, hb, -⟩ := h
    refine ⟨List.pairwise_singleton _ _, fun b hb' => ?_⟩
    simp only [List.mem_singleton] at hb'; subst hb'
    exact ⟨by simp [RamRange, blk, Layout.ramLo, Layout.ramHi],
      fun j hj => by
        simp only [blk] at hj; obtain rfl : j = 0 := by omega
        simpa using hb⟩
  alloc_spec _ _ _ hpre := (no_stack hpre.1 hpre.2.2.2.2.1).elim
  free_spec _ _ _ hpre := (no_stack hpre.1 hpre.2.2.2.2.2.1).elim
  Arena _ := True
  arena_split L _ a _ := ⟨fun _ => (Classical.em (InLive L a)).symm, fun _ => trivial⟩

/-- A machine whose only present byte is the block's. -/
def m0 : Machine := ⟨fun _ => 0, 0, fun a => if a = blk.1 then some 0 else none⟩

theorem heap_nonempty :
    ∃ A : AllocAssumptions zesuImage, ∃ L m, A.Heap L m ∧ ∃ b ∈ L, 0 < b.2 :=
  ⟨model, [blk], m0, ⟨rfl, by simp [m0], fun a ha => by simp [m0, ha]⟩,
    blk, List.mem_singleton_self _, by decide⟩

end ZesuExec.Test.AllocModel
