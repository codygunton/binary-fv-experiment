import BinaryFv.Ssz.Relation
import BinaryFv.Ssz.ZigRepresentation

/-!
# Typed boundary shared by the Level 1 decode and observation contracts

This file states the semantic and machine values crossing the optimized inlined `ssz.decode`
boundary. It deliberately does not claim a step bound or implementation theorem yet.
-/

namespace BinaryFv.Ssz

open PreSail LeanRV64DExecutable.Functions Register

private abbrev MachineState :=
  PreSail.SequentialState RegisterType Sail.trivialChoiceSource

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
  state.regs.get? PC = some (BitVec.ofNat 64 0x121e0) ∧
  args.inputAddress < 2 ^ 64 ∧
  state.regs.get? x23 = some (BitVec.ofNat 64 args.inputAddress) ∧
  state.regs.get? x18 = some (BitVec.ofNat 64 args.input.size) ∧
  BytesRep state.mem args.inputAddress args.input

/-- The source `catch` routes failure to `writeFailure`; success passes the concrete 848-byte
`StatelessInput` address in `a0` to `writeSuccess`. -/
def DecodeBoundaryExit (outcome : DecodeBoundaryOutcome) (state : MachineState) : Prop :=
  match outcome with
  | .failure => state.regs.get? PC = some (BitVec.ofNat 64 0x15b9c)
  | .success decoded => ∃ address : Nat,
      address < 2 ^ 64 ∧
      state.regs.get? PC = some (BitVec.ofNat 64 0x1470c) ∧
      state.regs.get? x10 = some (BitVec.ofNat 64 address) ∧
      StatelessInputRep state.mem address decoded

end BinaryFv.Ssz
