import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.RegisterRuns

/-! # Exact r7 execution-witness result stores

The pinned production ELF has the six `sd` words below.  This module records their literal
addresses, encodings, source register and stack offset for the succeeding Sail corridor proof. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register RegisterWriteStep

structure Level4ExecutionWitnessResultStore where
  pc : Nat
  word : UInt32
  source : Register
  offset : Nat

def level4ExecutionWitnessResultStores : List Level4ExecutionWitnessResultStore :=
  [ { pc := 0x12924, word := 0x59613023, source := x22, offset := 0x580 }
  , { pc := 0x12928, word := 0x59513423, source := x21, offset := 0x588 }
  , { pc := 0x1292c, word := 0x59813823, source := x24, offset := 0x590 }
  , { pc := 0x12930, word := 0x59713c23, source := x23, offset := 0x598 }
  , { pc := 0x12944, word := 0x5aa13023, source := x10, offset := 0x5a0 }
  , { pc := 0x12948, word := 0x5ab13423, source := x11, offset := 0x5a8 } ]

theorem level4ExecutionWitnessResultStores_exact :
    level4ExecutionWitnessResultStores.length = 6 := by native_decide

end BinaryFv.Zesu.MachineExecution
