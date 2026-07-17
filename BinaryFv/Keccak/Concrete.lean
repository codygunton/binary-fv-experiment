import BinaryFv.Keccak.Execution
import Spec.Keccak.Keccak256

namespace BinaryFv.Keccak.Concrete

open BinaryFv.RiscV

def concreteFuel : Nat := 2_000_000

def directCallMatches (message : ByteArray) : Bool :=
  match Artifact.codeRange, runConcrete message concreteFuel with
  | .ok code, .ok result =>
    result.steps != 0 &&
      result.returnCode == 0 &&
        result.pc == returnAddress code &&
          result.ra == returnAddress code &&
            result.sp == stackTop &&
              result.digest == Spec.Keccak.keccak256 message &&
                result.codeUnchanged &&
                  result.messageUnchanged &&
                    result.outputGuardsUnchanged &&
                      result.messageGuardsUnchanged && result.stackBottomGuardUnchanged
  | _, _ => false

def patterned (length : Nat) : ByteArray :=
  ByteArray.mk <| (Array.range length).map fun index =>
    UInt8.ofNat ((0x9d * index + 0x31) % 256)

def message0 : ByteArray :=
  ByteArray.empty

def message1 : ByteArray :=
  patterned 1

def message3 : ByteArray :=
  "abc".toUTF8

def message135 : ByteArray :=
  patterned 135

def message136 : ByteArray :=
  patterned 136

def message137 : ByteArray :=
  patterned 137

def message200 : ByteArray :=
  patterned 200

def message4096 : ByteArray :=
  patterned 4096

theorem concrete_len_0 : directCallMatches message0 = true := by
  native_decide

theorem concrete_len_1 : directCallMatches message1 = true := by
  native_decide

theorem concrete_len_3 : directCallMatches message3 = true := by
  native_decide

theorem concrete_len_135 : directCallMatches message135 = true := by
  native_decide

theorem concrete_len_136 : directCallMatches message136 = true := by
  native_decide

theorem concrete_len_137 : directCallMatches message137 = true := by
  native_decide

theorem concrete_len_200 : directCallMatches message200 = true := by
  native_decide

theorem concrete_len_4096 : directCallMatches message4096 = true := by
  native_decide

end BinaryFv.Keccak.Concrete
