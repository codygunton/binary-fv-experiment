import BinaryFv.RISCV.SepLogic

/-!
# Shared compositional framing for the memory helpers

The helper capstones (`memcpy`, `memset`, `copy_from_slice`) prove the destination-content and
trace/count conclusions, but callers in the sponge/runner stage also need the *compositional*
side of the contract: which memory and which registers the run leaves alone.  This module factors
the pieces those framing conclusions share.

The helper loop invariants already track every per-byte write (`hcopy`/`hset`).  Rather than redo a
separate pointwise `Std.ExtHashMap` induction, we thread one extra invariant field — the exact
memory delta relative to a fixed reference state — and lift it here to a clean frame statement.
`MemFramed dst n s0 s` says `s` and `s0` agree at every address the `n`-byte destination fill does
*not* write; combined with the destination-content postcondition it pins `s.mem` exactly.  This is
the byte-memory analogue of the separation-logic frame (`BinaryFv.RISCV.Sep.bytes_none_outside`,
`Triple.frame_preserved`): the owned window is `[dst, dst+n)` and the framed complement is
everything else.

The two consumer-facing corollaries live here as well: reading the frame off *outside* the window
`[dst, dst+n)` (`MemFramed.mem_unchanged_outside`), and source-region preservation for the copying
helpers (`MemFramed.source_preserved`), which follows from the frame plus the contracts' existing
non-overlap premise.
-/

namespace BinaryFv.Keccak

open BinaryFv.RISCV

/-- No-wraparound address arithmetic for an in-range destination offset: `(base + j)` as a machine
word has `toNat` exactly `base.toNat + j` when that sum does not overflow.  (Self-contained twin of
`MemcpyContract.dstAddr_toNat`, kept below the helper contracts so they can import this module.) -/
theorem windowAddr_toNat (base : BitVec 64) (j : Nat) (hfit : base.toNat + j < 2 ^ 64) :
    (base + BitVec.ofNat 64 j).toNat = base.toNat + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- Reading an address distinct from the just-inserted key is unaffected by the insert.  (Local
twin of the helpers' `getInsertNe`, phrased for reuse across the framing lemmas.) -/
theorem getElem?_insert_ne (mem : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (v : BitVec 8)
    (h : k ≠ a) : (mem.insert k v).get? a = mem.get? a := by
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]; simp [h]

/-- The exact memory delta of an `n`-byte destination fill starting at `dst`: state `s` agrees with
the reference memory `s0` at every address the fill does not write — i.e. every address distinct
from all `(dst + j)` with `j < n`.  Combined with the helper's destination-content postcondition,
this characterizes `s.mem` completely. -/
def MemFramed (dst n : BitVec 64) (s0 s : State) : Prop :=
  ∀ addr : Nat, (∀ j : Nat, j < n.toNat → addr ≠ (dst + BitVec.ofNat 64 j).toNat) →
    s.mem.get? addr = s0.mem.get? addr

/-- One more byte-store at `(dst + i)` extends a frame from window prefix `i` to `i + 1`: a write
inside the destination window never disturbs the already-framed complement.  This is the per-step
lemma the loop-invariant advance re-establishes. -/
theorem frame_insert_step {s0 : State} {mem : Std.ExtHashMap Nat (BitVec 8)}
    {dst : BitVec 64} {i : Nat} {v : BitVec 8}
    (hframe : ∀ addr : Nat, (∀ j : Nat, j < i → addr ≠ (dst + BitVec.ofNat 64 j).toNat) →
      mem.get? addr = s0.mem.get? addr) :
    ∀ addr : Nat, (∀ j : Nat, j < i + 1 → addr ≠ (dst + BitVec.ofNat 64 j).toNat) →
      (mem.insert (dst + BitVec.ofNat 64 i).toNat v).get? addr = s0.mem.get? addr := by
  intro addr haddr
  rw [getElem?_insert_ne _ _ _ _ (haddr i (Nat.lt_succ_self i)).symm]
  exact hframe addr (fun j hj => haddr j (Nat.lt_succ_of_lt hj))

/-- Read the frame off *outside* the destination window `[dst, dst+n)`: with no address wraparound,
every address strictly below `dst` or at/above `dst + n` is left untouched by the run.  This is the
caller-facing arbitrary-frame statement (`s.mem addr = s0.mem addr` for `addr ∉ [dst, dst+n)`). -/
theorem MemFramed.mem_unchanged_outside {dst n : BitVec 64} {s0 s : State}
    (hfr : MemFramed dst n s0 s) (hdstFits : dst.toNat + n.toNat ≤ 2 ^ 64)
    (addr : Nat) (hout : addr < dst.toNat ∨ dst.toNat + n.toNat ≤ addr) :
    s.mem.get? addr = s0.mem.get? addr := by
  refine hfr addr (fun j hj => ?_)
  rw [windowAddr_toNat dst j (by omega)]
  omega

/-- Source-region preservation for the copying helpers: every source address `(src + k)` with
`k < n` is disjoint from every written destination address (by the contract's non-overlap premise
`hdisj`), hence untouched by the run. -/
theorem MemFramed.source_preserved {dst src n : BitVec 64} {s0 s : State}
    (hfr : MemFramed dst n s0 s)
    (hdisj : ∀ j k : Nat, j < n.toNat → k < n.toNat →
      (dst + BitVec.ofNat 64 j).toNat ≠ (src + BitVec.ofNat 64 k).toNat)
    (k : Nat) (hk : k < n.toNat) :
    s.mem.get? (src + BitVec.ofNat 64 k).toNat = s0.mem.get? (src + BitVec.ofNat 64 k).toNat :=
  hfr _ (fun j hj => (hdisj j k hj hk).symm)

end BinaryFv.Keccak
