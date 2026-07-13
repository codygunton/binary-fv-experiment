import «Cryptography».Hashes.SHA3.Basic
import ShaFv.RISCV.ABI

namespace ShaFv.SHA3

namespace Sha3Spec

def hashData (msg : ByteArray) : ByteArray :=
  SHA3_256.hashData msg

end Sha3Spec

namespace RiscvSpec

abbrev Binary := ByteArray

def maxMessageSize : Nat := ShaFv.RISCV.maxMessageSize

inductive ExecutionError where
  | unsupportedMessage
  | notImplemented

abbrev ObservableResult := Except ExecutionError ByteArray

def execute (_binary : Binary) (msg : ByteArray) : ObservableResult :=
  if msg.size < maxMessageSize then .error .notImplemented else .error .unsupportedMessage

theorem execute_unsupportedMessage (binary : Binary) (msg : ByteArray)
    (messageH : maxMessageSize ≤ msg.size) :
    execute binary msg = .error .unsupportedMessage := by
  simp [execute, Nat.not_lt_of_ge messageH]

end RiscvSpec

/-- The fixed SHA-3 ELF. Its bytes will be embedded by the artifact-loading layer. -/
def binary : RiscvSpec.Binary :=
  ByteArray.empty

theorem root_compliance :
    ∀ msg : ByteArray,
      msg.size < RiscvSpec.maxMessageSize →
      RiscvSpec.execute binary msg = .ok (Sha3Spec.hashData msg) := by
  intro _msg _messageH
  sorry

end ShaFv.SHA3
