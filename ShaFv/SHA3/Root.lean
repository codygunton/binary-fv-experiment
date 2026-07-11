import «Cryptography».Hashes.SHA3.Basic

namespace ShaFv.SHA3

namespace Spec

def exec (msg : ByteArray) : ByteArray :=
  SHA3_256.hashData msg

end Spec

namespace Bin

def main (_msg : ByteArray) : ByteArray :=
  ByteArray.empty

end Bin

theorem root_compliance :
    ∀ msg : ByteArray,
      Bin.main msg = Spec.exec msg := by
  intro _msg
  sorry

end ShaFv.SHA3
