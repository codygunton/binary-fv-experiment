import BinaryFv.Ssz.Relation
import BinaryFv.Ssz.ZigRepresentation
import BinaryFv.Ssz.Generated.Level1
import BinaryFv.Ssz.MachineContract

/-!
# Typed boundary shared by the Level 1 decode and observation contracts

This file states the semantic and machine values crossing the optimized inlined `ssz.decode`
boundary. It deliberately does not claim a step bound or implementation theorem yet.
-/

namespace BinaryFv.Ssz

open PreSail LeanRV64DExecutable.Functions Register

structure DecodeBoundaryArgs where
  inputAddress : Nat
  input : Array UInt8

inductive DecodeBoundaryOutcome where
  | failure
  | success (decoded : ZesuDecodedResult)

/-- Strict common-revision meaning. Reviewed version divergences widen this relation separately. -/
def StrictDecodeMeaning (args : DecodeBoundaryArgs) : DecodeBoundaryOutcome → Prop
  | .failure => ¬∃ decoded, SailDecode args.input decoded
  | .success zesu => ∃ sail, SailDecode args.input sail ∧
      decodedResultRelModuloKnownBugs args.input zesu sail

/-- Same-ELF DWARF binds the inlined decode input pointer to `s7` and length to `s2`. -/
def DecodeBoundaryEntry (args : DecodeBoundaryArgs) (state : MachineState) : Prop :=
  state.regs.get? PC = some (BitVec.ofNat 64 Generated.sszDecodeEntry) ∧
  args.inputAddress < 2 ^ 64 ∧
  state.regs.get? x23 = some (BitVec.ofNat 64 args.inputAddress) ∧
  state.regs.get? x18 = some (BitVec.ofNat 64 args.input.size) ∧
  BytesRep state.mem args.inputAddress args.input

/-- The source `catch` routes failure to `writeFailure`; success passes the concrete 848-byte
`StatelessInput` address in `a0` to `writeSuccess`. -/
def DecodeBoundaryExit (outcome : DecodeBoundaryOutcome) (state : MachineState) : Prop :=
  match outcome with
  | .failure => state.regs.get? PC = some (BitVec.ofNat 64 Generated.writeFailureEntry)
  | .success decoded => ∃ address : Nat,
      address < 2 ^ 64 ∧
      state.regs.get? PC = some (BitVec.ofNat 64 Generated.writeSuccessEntry) ∧
      state.regs.get? x10 = some (BitVec.ofNat 64 address) ∧
      StatelessInputRep state.mem address decoded

/-- The strict contract shape. The reviewed Level 1 contract will instantiate its bound and widen
only the fixed accept/reject domains represented by `knownBugs`. -/
def strictDecodeContract (stepBound : DecodeBoundaryArgs → Nat) :
    RelationalMachineContract DecodeBoundaryArgs DecodeBoundaryOutcome :=
  { allows := StrictDecodeMeaning
    entry := DecodeBoundaryEntry
    exit := fun _ outcome _ after => DecodeBoundaryExit outcome after
    stepBound }

def DecodeExecutionPc : BitVec 64 → Prop :=
  pcInRanges Generated.sszDecodeExecutionPcRanges

def DecodeExitPc (pc : BitVec 64) : Prop :=
  pc = BitVec.ofNat 64 Generated.writeSuccessEntry ∨
    pc = BitVec.ofNat 64 Generated.writeFailureEntry

/-- The exact strict implementation obligation at the generated production boundary. -/
abbrev StrictDecodeInstanceContract (stepBound : DecodeBoundaryArgs → Nat) : Prop :=
  (strictDecodeContract stepBound).Implements DecodeExecutionPc DecodeExitPc

end BinaryFv.Ssz
