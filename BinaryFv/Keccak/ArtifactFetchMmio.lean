import BinaryFv.Keccak.ArtifactFetch
import BinaryFv.Keccak.ArtifactCodeRange

namespace BinaryFv.Keccak

open BinaryFv.RiscV
open Register

/--
Parser-image and layout assumptions sufficient for one sparse-RAM fetch at an encoded word.

This only reconstructs the generated fetch inputs. It does not establish executable-word
membership, decoder agreement, execution, or control-flow reachability.
-/
theorem artifactFetchableWord_fetchMemoryNoMMIOAndBytes (state : State) (word : EncodedWord)
    (fetchable : ArtifactFetchableWord state word)
    (inCode : ArtifactCodeFetchPc (BitVec.ofNat 64 word.address))
    (htifDisabled : state.regs.get? htif_tohost_base = some none) :
    FetchMemoryNoMMIO state (BitVec.ofNat 64 word.address) ∧
      ∃ (byte0 byte1 byte2 byte3 : UInt8),
        FetchBytesAt state (BitVec.ofNat 64 word.address)
          (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
          (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) ∧
            fetchWord (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
              (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) = word.bits := by
  constructor
  · exact fetchMemoryNoMMIO_of_state_layout_excluded state (BitVec.ofNat 64 word.address)
      (fetch_mmio_state_layout_excluded_of_artifact_code state
        (BitVec.ofNat 64 word.address) inCode htifDisabled)
  · exact artifactFetchableWord_fetchBytes state word fetchable

end BinaryFv.Keccak
