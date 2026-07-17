import BinaryFv.Keccak.Artifact
import BinaryFv.RiscV.Proof.ImageFetch

/-!
# Artifact-owned fetchable words

The pinned Reth image's half of fetching: which encoded words this artifact owns. The lift to the
generated fetch inputs is generic (`BinaryFv.RiscV.Proof.ImageFetch`).
-/

namespace BinaryFv.Keccak

open BinaryFv.RiscV

/--
Conditional parser-image facts sufficient for one generated fetch. This reconstructs bytes only;
it asserts neither a decoder result nor execution or CFG reachability.
-/
def ArtifactFetchableWord (state : State) (word : EncodedWord) : Prop :=
  ∃ image,
    Artifact.programImage = .ok image ∧ image.matchesMemory state.mem ∧
      image.ownsEncodedWord word ∧ word.address < 2 ^ 64

theorem artifactFetchableWord_fetchBytes (state : State) (word : EncodedWord)
    (fetchable : ArtifactFetchableWord state word) :
    ∃ (byte0 byte1 byte2 byte3 : UInt8),
      FetchBytesAt state (BitVec.ofNat 64 word.address)
        (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
        (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) ∧
          fetchWord (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
            (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) = word.bits := by
  rcases fetchable with ⟨image, _, loaded, owned, addressFits⟩
  exact image.fetchBytesAt_of_ownedEncodedWord state word addressFits loaded owned

end BinaryFv.Keccak
