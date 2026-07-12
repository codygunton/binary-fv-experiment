import ShaFv.RISCV.Machine

namespace SailSha3Smoke

open PreSail
open LeanRV64DExecutable
open LeanRV64DExecutable.Functions
open Register
open ExecutionResult FetchResult

def loadBytes (base : Nat) (bytes : ByteArray) : SailM Unit := do
  for h : i in [:bytes.size] do
    writeByte (base + i) (BitVec.ofNat 8 bytes[i].toNat)

def readByteArray (base len : Nat) : SailM ByteArray := do
  let mut result := ByteArray.emptyWithCapacity len
  for i in [:len] do
    result := result.push (UInt8.ofNat (← readByte (base + i)).toNat)
  return result

def runUserStep : SailM Unit := do
  let .F_Base bits ← fetch ()
    | throw <| Sail.Error.Assertion "non-base fetch"
  writeReg nextPC (Sail.BitVec.addInt (← readReg PC) 4)
  match ← execute (← ext_decode bits) with
  | .Retire_Success () => tick_pc ()
  | result => throw <| Sail.Error.Assertion (reprStr result)

def runUntilPC (stop : BitVec 64) : Nat → Nat → SailM Nat
  | 0, _ => throw Sail.Error.Unreachable
  | fuel + 1, steps => do
      if (← readReg PC) == stop then
        return steps
      runUserStep
      runUntilPC stop fuel (steps + 1)

def loadBase : Nat := 0x10000
def loadSize : Nat := 0x778
def sha3Address : Nat := 0x10540
def messageAddress : Nat := 0x70000
def outputAddress : Nat := 0x71000
def stackAddress : Nat := 0x80000
def returnAddress : Nat := 0x18000

def initializeIntegerRegisters : SailM Unit := do
  writeReg x3 (0 : BitVec 64)
  writeReg x4 (0 : BitVec 64)
  writeReg x5 (0 : BitVec 64)
  writeReg x6 (0 : BitVec 64)
  writeReg x7 (0 : BitVec 64)
  writeReg x8 (0 : BitVec 64)
  writeReg x9 (0 : BitVec 64)
  writeReg x10 (0 : BitVec 64)
  writeReg x11 (0 : BitVec 64)
  writeReg x12 (0 : BitVec 64)
  writeReg x13 (0 : BitVec 64)
  writeReg x14 (0 : BitVec 64)
  writeReg x15 (0 : BitVec 64)
  writeReg x16 (0 : BitVec 64)
  writeReg x17 (0 : BitVec 64)
  writeReg x18 (0 : BitVec 64)
  writeReg x19 (0 : BitVec 64)
  writeReg x20 (0 : BitVec 64)
  writeReg x21 (0 : BitVec 64)
  writeReg x22 (0 : BitVec 64)
  writeReg x23 (0 : BitVec 64)
  writeReg x24 (0 : BitVec 64)
  writeReg x25 (0 : BitVec 64)
  writeReg x26 (0 : BitVec 64)
  writeReg x27 (0 : BitVec 64)
  writeReg x28 (0 : BitVec 64)
  writeReg x29 (0 : BitVec 64)
  writeReg x30 (0 : BitVec 64)
  writeReg x31 (0 : BitVec 64)

def executeSha3 (elf message : ByteArray) : SailM (ByteArray × Nat) := do
  sail_model_init ()
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 12 12 1#1)
  let some mainMemory := (← readReg pma_regions).getLast?
    | throw Sail.Error.Unreachable
  writeReg pma_regions [{ mainMemory with
    base := (0 : BitVec 64)
    size := (0x100000 : BitVec 64) }]
  writeReg pmpcfg_n default
  writeReg pmpaddr_n default
  writeReg mcountinhibit (0 : BitVec 32)
  writeReg minstretcfg (0 : BitVec 64)
  writeReg minstret (0 : BitVec 64)
  writeReg minstret_increment false
  writeReg satp (0 : BitVec 64)
  writeReg cur_privilege Privilege.Machine
  loadBytes loadBase (elf.extract 0 loadSize)
  loadBytes messageAddress message
  initializeIntegerRegisters
  writeReg x1 (BitVec.ofNat 64 returnAddress)
  writeReg x2 (BitVec.ofNat 64 stackAddress)
  writeReg x10 (BitVec.ofNat 64 messageAddress)
  writeReg x11 (BitVec.ofNat 64 message.size)
  writeReg x12 (BitVec.ofNat 64 outputAddress)
  writeReg x13 (32 : BitVec 64)
  writeReg PC (BitVec.ofNat 64 sha3Address)
  writeReg nextPC (BitVec.ofNat 64 sha3Address)
  let steps ← runUntilPC (BitVec.ofNat 64 returnAddress) 100000 0
  return (← readByteArray outputAddress 32, steps)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

def toHex (bytes : ByteArray) : String :=
  String.ofList <| bytes.data.toList.flatMap fun b =>
    [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def message : ByteArray :=
  String.ofList (List.replicate 200 'a') |>.toUTF8

def expectedDigest : String :=
  "cce34485baf2bf2aca99b94833892a4f52896d3d153f7b840cc4f9fe695f1387"

def smoke : IO Unit := do
  let elf ← IO.FS.readBinFile "build/sha3/bin/sha3"
  match (executeSha3 elf message).run ShaFv.RISCV.initialState with
  | .ok (digest, steps) _ =>
      let digestHex := toHex digest
      if digestHex != expectedDigest then
        throw <| IO.userError s!"unexpected digest: {digestHex}"
      IO.println s!"Sail executed {steps} instructions; digest {digestHex}"
  | .error error state =>
      let pc : Option (BitVec 64) := state.regs.get? PC
      throw <| IO.userError s!"{error.print}; PC={pc.map (·.toNat)}"

end SailSha3Smoke

#eval SailSha3Smoke.smoke
