import «Cryptography».Hashes.SHA3.Basic
import ShaFv.RISCV.ABI
import ShaFv.RISCV.Elf64
import Sha3Elf

namespace ShaFv.SHA3

open ShaFv.RISCV

namespace Sha3Spec

def hashData (msg : ByteArray) : ByteArray :=
  SHA3_256.hashData msg

end Sha3Spec

namespace RiscvSpec

/-- A fixed executable together with its executable parser result. -/
structure Binary where
  bytes : ByteArray
  parsed : Except ElfError Elf64
  parsed_eq : Elf64.parse bytes = parsed

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

/-- The fixed SHA-3 ELF, generated directly from the canonical Nix build. -/
def binary : RiscvSpec.Binary :=
  {
    bytes := Artifact.bytes
    parsed := Elf64.parse Artifact.bytes
    parsed_eq := rfl
  }

theorem root_compliance :
    ∀ msg : ByteArray,
      msg.size < RiscvSpec.maxMessageSize →
      RiscvSpec.execute binary msg = .ok (Sha3Spec.hashData msg) := by
  intro _msg _messageH
  sorry

end ShaFv.SHA3
