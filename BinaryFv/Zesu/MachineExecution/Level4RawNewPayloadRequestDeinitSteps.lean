import BinaryFv.Zesu.MachineExecution.Level4DecodeRawParentInvariant

/-! # Exact parent continuation for excluded `RawNewPayloadRequest.deinit` -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The exact 45 generated PCs of excluded `RawNewPayloadRequest.deinit`. -/
abbrev Level4RawNewPayloadRequestDeinitPcs : BitVec 64 → Prop :=
  RegionPcs excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions

/-- Current parent facts at the selected excluded-region entry. -/
structure Level4RawNewPayloadRequestDeinitPre {margs : DecoderMachineArgs} {origin current : State}
    (frame : Level4DecodeRawParentFrame margs origin current) : Prop where
  pc : current.regs.get? PC = some (BitVec.ofNat 64 0x131ec)
  sp : current.regs.get? x2 = some (BitVec.ofNat 64 (frame.stack - 0x690))
  preservation : frame.PreservedTo current

end BinaryFv.Zesu.MachineExecution
