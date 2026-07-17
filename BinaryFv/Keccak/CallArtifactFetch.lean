import BinaryFv.Keccak.ArtifactFetch

/-!
# Parser-derived fetch of the `reth_keccak256` CALL-site instruction words

The Reth Keccak ELF is position-independent: every genuine call is the two-word idiom
`auipc <link>, <hi>` immediately followed by `jalr <rd>, <lo>(<link>)`, and every tail call the
analogous `auipc <tmp>; jr <lo>(<tmp>)`.  This module derives, straight from the embedded canonical
ELF through the bounded parser, the exact four fetch bytes for the representative CALL sites — both
the `auipc` that forms the target *and* the `jalr` that performs the jump/link.  These bytes are not
trusted input: they are read from `Artifact.programImage`, exactly as the store fetch already does
(`StoreArtifactFetch.sdStoreWord_fetchBytesAt`).  The only `native_decide` here is the closed parser
fact that the parsed image backs each word — the established artifact trust policy.

Representative sites (all inside / reached from `reth_keccak256` at `0x10a2c`):

* `0x10ad4 auipc ra,0x0` + `0x10ad8 jalr 408(ra)`   — standard `ra`-link call of `xor_block` (0x10c6c).
* `0x10c64 auipc ra,0xfffff` + `0x10c68 jalr 1164(ra)` — `ra`-link call with a *negative* `auipc`
  (target 0x100f0).
* `0x10844 auipc t0,0x0` + `0x10848 jalr t0,1192(t0)` — genuine call writing a *non-`ra`* link
  register `t0` (target `OUTLINED_FUNCTION_0` 0x10cec).
* `0x10c54 auipc t1,0x0` + `0x10c58 jr 196(t1)`     — tail call that *discards* the link (`rd = x0`),
  `t1`-relative (target `memcpy` 0x10d18).
* `0x101f8 jal reth_keccak256`                       — a direct `jal ra` call (target 0x10a2c).
-/

namespace BinaryFv.Keccak

open BinaryFv.RiscV

/-- Closed parser fact: the image's four consecutive little-endian bytes at `address` are
    `b0 b1 b2 b3`.  Decidable over the embedded ELF, discharged by `native_decide`. -/
def callBytesOwned (address : Nat) (b0 b1 b2 b3 : UInt8) : Bool :=
  match Artifact.programImage with
  | .ok image =>
    decide (image.readByte? address = some b0 ∧ image.readByte? (address + 1) = some b1 ∧
      image.readByte? (address + 2) = some b2 ∧ image.readByte? (address + 3) = some b3)
  | .error _ => false

theorem callBytesOwned_readBytes (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (address : Nat) (b0 b1 b2 b3 : UInt8)
    (h : callBytesOwned address b0 b1 b2 b3 = true) :
    image.readByte? address = some b0 ∧ image.readByte? (address + 1) = some b1 ∧
      image.readByte? (address + 2) = some b2 ∧ image.readByte? (address + 3) = some b3 := by
  unfold callBytesOwned at h
  rw [imageEq] at h
  simpa using h

/-- Derive the exact four fetch bytes at `address` directly from the persistent code-image
    assertion (`matchesMemory`): given the parsed ELF agrees with sparse memory and the parser owns
    the four bytes there, the generated fetch reads exactly `b0 b1 b2 b3`. -/
theorem callWord_fetchBytesAt (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem)
    (address : Nat) (addressFits : address < 2 ^ 64) (b0 b1 b2 b3 : UInt8)
    (owned : callBytesOwned address b0 b1 b2 b3 = true) :
    FetchBytesAt state (BitVec.ofNat 64 address)
      (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
      (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat) := by
  obtain ⟨r0, r1, r2, r3⟩ := callBytesOwned_readBytes image imageEq address b0 b1 b2 b3 owned
  exact image.fetchBytesAt_of_image_bytes state address addressFits loaded b0 b1 b2 b3 r0 r1 r2 r3

/-! ## Closed parser byte facts for the representative CALL words -/

/-- `auipc ra,0x0` at `0x10ad4` (word `0x00000097`, little-endian `97 00 00 00`). -/
theorem xorCallAuipc_owned : callBytesOwned 0x10ad4 0x97 0x00 0x00 0x00 = true := by native_decide

/-- `jalr ra,408(ra)` at `0x10ad8` (word `0x198080e7`, little-endian `e7 80 80 19`). -/
theorem xorCallJalr_owned : callBytesOwned 0x10ad8 0xe7 0x80 0x80 0x19 = true := by native_decide

/-- `auipc ra,0xfffff` at `0x10c64` (word `0xfffff097`, little-endian `97 f0 ff ff`). -/
theorem negCallAuipc_owned : callBytesOwned 0x10c64 0x97 0xf0 0xff 0xff = true := by native_decide

/-- `jalr ra,1164(ra)` at `0x10c68` (word `0x48c080e7`, little-endian `e7 80 c0 48`). -/
theorem negCallJalr_owned : callBytesOwned 0x10c68 0xe7 0x80 0xc0 0x48 = true := by native_decide

/-- `auipc t0,0x0` at `0x10844` (word `0x00000297`, little-endian `97 02 00 00`). -/
theorem t0CallAuipc_owned : callBytesOwned 0x10844 0x97 0x02 0x00 0x00 = true := by native_decide

/-- `jalr t0,1192(t0)` at `0x10848` (word `0x4a8282e7`, little-endian `e7 82 82 4a`). -/
theorem t0CallJalr_owned : callBytesOwned 0x10848 0xe7 0x82 0x82 0x4a = true := by native_decide

/-- `auipc t1,0x0` at `0x10c54` (word `0x00000317`, little-endian `17 03 00 00`). -/
theorem t1TailAuipc_owned : callBytesOwned 0x10c54 0x17 0x03 0x00 0x00 = true := by native_decide

/-- `jr 196(t1)` (`jalr x0,196(t1)`) at `0x10c58` (word `0x0c430067`, little-endian `67 00 43 0c`). -/
theorem t1TailJr_owned : callBytesOwned 0x10c58 0x67 0x00 0x43 0x0c = true := by native_decide

/-- `jal ra,reth_keccak256` at `0x101f8` (word `0x035000ef`, little-endian `ef 00 50 03`). -/
theorem jalCall_owned : callBytesOwned 0x101f8 0xef 0x00 0x50 0x03 = true := by native_decide

end BinaryFv.Keccak
