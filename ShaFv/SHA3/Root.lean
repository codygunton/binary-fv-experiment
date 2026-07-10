import «Cryptography».Hashes.SHA3.Basic

namespace ShaFv.SHA3

structure Binary where
  image : ByteArray

def sha3Binary : Binary where
  image := ByteArray.empty

namespace Spec

def hashData (msg : ByteArray) : ByteArray :=
  SHA3_256.hashData msg

end Spec

namespace Binary

def sha3_256 (_binary : Binary) (_msg : ByteArray) : ByteArray :=
  ByteArray.empty

end Binary

theorem root_compliance :
    ∀ msg : ByteArray,
      Binary.sha3_256 sha3Binary msg = Spec.hashData msg := by
  intro _msg
  sorry

end ShaFv.SHA3
