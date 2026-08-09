import BinaryFv.Zesu.MachineExecution.Level4RequireU32LengthSteps
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4Contracts
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.Seg

/-! # Remaining direct entry/envelope/offset instructions of `ssz_raw.decodeRaw`

The preceding prologue owns sixteen direct PCs.  The selected `requireU32Length` occurrence owns
three further PCs but is intentionally not counted in this parent-owned list.  These twenty-nine
literal PCs are therefore exactly the unfinished direct part of the reviewed forty-five-PC phase.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- Direct parent PCs after the prologue in the successful entry/envelope/offset route. -/
def level4EntryEnvelopeOffsetsRemainingDirectPcs : List Nat :=
  [ 0x10490, 0x10498
  , 0x104a8, 0x104ac, 0x104b0, 0x104b4, 0x104b8, 0x104bc, 0x104c0, 0x104c4
  , 0x104c8, 0x104cc, 0x104d0, 0x104d4, 0x104d8
  , 0x105d4, 0x105d8, 0x105dc, 0x105e0, 0x105e4, 0x105e8, 0x105ec, 0x105f0
  , 0x105f4, 0x105f8, 0x105fc, 0x10600, 0x10604, 0x10608 ]

abbrev Level4EntryEnvelopeOffsetsRemainingDirectPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4EntryEnvelopeOffsetsRemainingDirectPcs

theorem level4EntryEnvelopeOffsetsRemainingDirectPcs_count :
    level4EntryEnvelopeOffsetsRemainingDirectPcs.length = 29 := rfl

theorem level4EntryEnvelopeOffsetsRemainingDirectPcs_exact :
    decodeRawEntryEnvelopeOffsetsPcs =
      level4DecodeRawEntryProloguePcs ++ level4EntryEnvelopeOffsetsRemainingDirectPcs := rfl

theorem level4EntryEnvelopeOffsetsRemainingDirectPcs_subset_direct :
    level4EntryEnvelopeOffsetsRemainingDirectPcs.all decodeRawDirectPcs.contains = true := by
  native_decide

theorem level4EntryEnvelopeOffsetsRemainingDirectPcs_subset_phase :
    level4EntryEnvelopeOffsetsRemainingDirectPcs.all decodeRawEntryEnvelopeOffsetsPcs.contains = true := by
  native_decide

end BinaryFv.Zesu.MachineExecution
