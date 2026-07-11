import «Cryptography».Hashes.SHA3.Basic

namespace ShaFv.SHA3

namespace Sha3Spec

def hashData (msg : ByteArray) : ByteArray :=
  SHA3_256.hashData msg

end Sha3Spec

namespace RiscvSpec

abbrev Binary := ByteArray

inductive ExecutionError where
  | notImplemented

def execute (_binary : Binary) (_msg : ByteArray) : Except ExecutionError ByteArray :=
  .error .notImplemented

end RiscvSpec

/-- The fixed SHA-3 ELF. Its bytes will be embedded by the artifact-loading layer. -/
def binary : RiscvSpec.Binary :=
  ByteArray.empty

theorem root_compliance :
    ∀ msg : ByteArray,
      RiscvSpec.execute binary msg = .ok (Sha3Spec.hashData msg) := by
  intro _msg
  sorry

end ShaFv.SHA3
