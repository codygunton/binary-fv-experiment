import Evm

open Sail
open Evm
open Evm.Defs
open Evm.Functions

private def putByte (bytes : Array UInt8) (offset value : Nat) : Array UInt8 :=
  bytes.set! offset (UInt8.ofNat value)

private def putU32LE (bytes : Array UInt8) (offset value : Nat) : Array UInt8 :=
  Id.run do
    let mut result := bytes
    for index in [0:4] do
      result := putByte result (offset + index) (value / 256 ^ index)
    return result

private def putU64LE (bytes : Array UInt8) (offset value : Nat) : Array UInt8 :=
  Id.run do
    let mut result := bytes
    for index in [0:8] do
      result := putByte result (offset + index) (value / 256 ^ index)
    return result

/-- A structurally valid, empty Amsterdam stateless-input envelope. -/
private def minimalInput : Array UInt8 := Id.run do
  let mut bytes := Array.replicate 666 0
  bytes := putByte bytes 0 0x15
  bytes := putByte bytes 1 0x01
  bytes := putU32LE bytes 2 16
  bytes := putU32LE bytes 6 620
  bytes := putU32LE bytes 10 632
  bytes := putU32LE bytes 14 664
  bytes := putU32LE bytes 18 44
  bytes := putU32LE bytes 22 584
  bytes := putU32LE bytes 58 584
  bytes := putU32LE bytes 498 540
  bytes := putU32LE bytes 566 540
  bytes := putU32LE bytes 570 540
  bytes := putU32LE bytes 590 540
  for offset in [602, 606, 610, 614, 618] do
    bytes := putU32LE bytes offset 20
  for offset in [622, 626, 630] do
    bytes := putU32LE bytes offset 12
  bytes := putU64LE bytes 634 1
  bytes := putU32LE bytes 642 12
  bytes := putU32LE bytes 646 4
  bytes := putU32LE bytes 650 8
  bytes := putU32LE bytes 654 16
  return bytes

private def modelBytes (input : Array UInt8) : Array byte :=
  input.map fun value => BitVec.ofNat 8 value.toNat

private def decodeAccepted (input : Array UInt8) : Bool :=
  let hostState := { initialHostState with inputBytes := modelBytes input }
  let action : Evm.SailM Unit := do
    let inputRef ← decode_stateless_input_ref ⟨0, ⟨input.size, {}⟩⟩
    let _ ← decode_stateless_input inputRef
  match (action.run hostState).run default with
  | .ok .. => true
  | .error .. => false

example : decodeAccepted minimalInput = true := by native_decide

example : decodeAccepted (putByte minimalInput 1 0xff) = false := by native_decide
