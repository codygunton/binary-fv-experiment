import Std.Tactic.BVDecide
import Spec.Keccak.Keccak256

/-!
# Pure lane/byte correspondence with `Spec.Keccak`

The specification stores its state as 25 `UInt64` lanes and addresses it as a flat byte array. These
are the pure serialization facts relating the two views, plus which lanes `xorBytesIntoState` touches.

Deliberately pure: no ELF address, no artifact, no runner, no machine state. Only `Spec.Keccak` and
core `BitVec`/`UInt64`/`ByteArray`. The proofs that connect these to the *machine's* memory are
Reth spec-correlation proofs and live under `Reth/Proof/`.
-/

namespace BinaryFv.Keccak.SpecBridge

/-- Extracting byte `r` of a 64-bit lane the way `Spec.Keccak.stateByte` does (`>>> 8r`, `&&& 0xFF`,
`toUInt8`) is `BitVec.extractLsb' (8r) 8`. -/
theorem uint64_byte (x : UInt64) (r : Nat) (hr : r < 8) :
    (((x >>> (8 * r).toUInt64) &&& 255).toUInt8).toBitVec = x.toBitVec.extractLsb' (8 * r) 8 := by
  match r, hr with
  | 0, _ => simp only [show Nat.toUInt64 (8 * 0) = (0 : UInt64) from rfl]; bv_decide
  | 1, _ => simp only [show Nat.toUInt64 (8 * 1) = (8 : UInt64) from rfl]; bv_decide
  | 2, _ => simp only [show Nat.toUInt64 (8 * 2) = (16 : UInt64) from rfl]; bv_decide
  | 3, _ => simp only [show Nat.toUInt64 (8 * 3) = (24 : UInt64) from rfl]; bv_decide
  | 4, _ => simp only [show Nat.toUInt64 (8 * 4) = (32 : UInt64) from rfl]; bv_decide
  | 5, _ => simp only [show Nat.toUInt64 (8 * 5) = (40 : UInt64) from rfl]; bv_decide
  | 6, _ => simp only [show Nat.toUInt64 (8 * 6) = (48 : UInt64) from rfl]; bv_decide
  | 7, _ => simp only [show Nat.toUInt64 (8 * 7) = (56 : UInt64) from rfl]; bv_decide
/-- BRIDGE (state serialization).  The spec's flat state byte `8m + r` is the machine's `r`-th
little-endian byte of lane `m`. -/
theorem specStateByte_toBitVec (st : Array UInt64) (m r : Nat) (hr : r < 8) :
    (Spec.Keccak.stateByte st (8 * m + r)).toBitVec = (st[m]!.toBitVec).extractLsb' (8 * r) 8 := by
  unfold Spec.Keccak.stateByte
  rw [show (8 * m + r) / 8 = m by omega, show (8 * m + r) % 8 = r by omega]
  exact uint64_byte st[m]! r hr
/-- Lane `m` of `xorBytesIntoState st input 136`: XORed for the 17 rate lanes, untouched otherwise
(`136 / 8 = 17`). -/
theorem xorBytesIntoState_lane (st : Array UInt64) (input : ByteArray) (m : Nat) (hm : m < 25) :
    (Spec.Keccak.xorBytesIntoState st input 136)[m]!
      = if m < 17 then st[m]! ^^^ Spec.Keccak.inputLane input m else st[m]! := by
  unfold Spec.Keccak.xorBytesIntoState
  rw [getElem!_pos _ _ (by simp; omega)]
  simp

end BinaryFv.Keccak.SpecBridge
