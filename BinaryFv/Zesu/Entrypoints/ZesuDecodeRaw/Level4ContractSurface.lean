import BinaryFv.RiscV.Elfling.Contract
import BinaryFv.RiscV.Elfling.ProgramGeometry
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4BoundaryInventory

/-!
# Static contract surface for the eight `decodeRaw` children

`decodeRaw`'s Level 4 proof will consume eight semantic child contracts.  This module fixes the
machine boundary for each one before an argument binding, result location, write set, preserved
register set, or step bound is extracted.  Those latter facts are absent from `GeneratedProgram`;
the definition `Level4ChildImplements` therefore takes a completed `FunctionInstanceContract`
explicitly instead of manufacturing a source ABI for an inlined instance.

The entries, execution extent, and exit predicate below are derived from the selected generated
`FunctionInstance`, so a later semantic contract cannot silently select a different instance or
choose a convenient exit.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Elflings.Generated

/-- The eight immediate children selected for the Level 4 `decodeRaw` refinement. -/
inductive Level4Child where
  | readOffsetAt199_23
  | readOffsetAt200_23
  | readOffsetAt201_23
  | readOffsetAt202_23
  | decodeNewPayloadRequestAt207_61
  | decodeExecutionWitnessAt209_48
  | decodeChainConfigAt211_48
  | decodePublicKeysAt212_46
deriving DecidableEq, Repr

/-- The source-function role of a selected instance.  This is a classification of the eight
already-selected generated instances, not an ABI or semantic binding. -/
inductive Level4ChildRole where
  | readOffset
  | decodeNewPayloadRequest
  | decodeExecutionWitness
  | decodeChainConfig
  | decodePublicKeys
deriving DecidableEq, Repr

def Level4Child.role : Level4Child → Level4ChildRole
  | .readOffsetAt199_23 | .readOffsetAt200_23 | .readOffsetAt201_23 | .readOffsetAt202_23 =>
      .readOffset
  | .decodeNewPayloadRequestAt207_61 => .decodeNewPayloadRequest
  | .decodeExecutionWitnessAt209_48 => .decodeExecutionWitness
  | .decodeChainConfigAt211_48 => .decodeChainConfig
  | .decodePublicKeysAt212_46 => .decodePublicKeys

/-- The generated inlined function instance selected by each Level 4 child name. -/
def Level4Child.instance : Level4Child → FunctionInstance
  | .readOffsetAt199_23 =>
      functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23
  | .readOffsetAt200_23 =>
      functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23
  | .readOffsetAt201_23 =>
      functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23
  | .readOffsetAt202_23 =>
      functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_202_23
  | .decodeNewPayloadRequestAt207_61 =>
      functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61
  | .decodeExecutionWitnessAt209_48 =>
      functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48
  | .decodeChainConfigAt211_48 =>
      functionInstance_ssz_raw_decodeChainConfig_in_ssz_raw_decodeRaw_at_211_48
  | .decodePublicKeysAt212_46 =>
      functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46

/-- The machine-code trace boundary fixed by generated data for one Level 4 child. -/
structure Level4StaticTraceBoundary where
  functionInstance : BinaryFv.Binary.Elfling.FunctionInstance
  executionPcs : BitVec 64 → Prop
  entry : BitVec 64
  exit : BitVec 64 → Prop

/-- The exact trace boundary a future semantic contract for `child` must implement. -/
def Level4Child.staticTraceBoundary (child : Level4Child) : Level4StaticTraceBoundary where
  functionInstance := child.instance
  executionPcs := functionInstanceExecutionPcs generatedProgram child.instance
  entry := BitVec.ofNat 64 child.instance.entryPc
  exit := functionInstanceExitPred child.instance

/-- The eight static boundaries in the same order as `level4BoundaryInstances`. -/
def level4StaticTraceBoundaries : List Level4StaticTraceBoundary :=
  [ .readOffsetAt199_23, .readOffsetAt200_23, .readOffsetAt201_23, .readOffsetAt202_23,
    .decodeNewPayloadRequestAt207_61, .decodeExecutionWitnessAt209_48,
    .decodeChainConfigAt211_48, .decodePublicKeysAt212_46 ].map Level4Child.staticTraceBoundary

theorem level4StaticTraceBoundaries_count : level4StaticTraceBoundaries.length = 8 := rfl

theorem level4StaticTraceBoundaries_instances :
    level4StaticTraceBoundaries.map (·.functionInstance) = level4BoundaryInstances := rfl

theorem level4Child_is_direct_decodeRaw_child (child : Level4Child) :
    child.instance.parent? = some functionInstance_ssz_raw_decodeRawId := by
  cases child <;> rfl

theorem level4Child_entry (child : Level4Child) :
    (child.staticTraceBoundary.entry).toNat = child.instance.entryPc := by
  cases child <;> rfl

/-- A completed Level 4 semantic contract must run at exactly `child`'s generated entry, extent,
and exits.  This definition supplies none of the binding fields: a proof must first extract the
actual optimized interface for this specific inlined instance. -/
def Level4ChildImplements {Args Outcome : Type} (child : Level4Child)
    (contract : FunctionInstanceContract Args Outcome) : Prop :=
  let boundary := child.staticTraceBoundary
  contract.ImplementsFunctionInstance boundary.functionInstance
    (functionInstanceReachedPcs generatedProgram boundary.functionInstance) boundary.entry boundary.exit

theorem level4ChildImplements_uses_generated_boundary {Args Outcome : Type}
    (child : Level4Child) (contract : FunctionInstanceContract Args Outcome) :
    Level4ChildImplements child contract =
      contract.ImplementsFunctionInstance child.instance
        (functionInstanceReachedPcs generatedProgram child.instance)
        (BitVec.ofNat 64 child.instance.entryPc)
        (functionInstanceExitPred child.instance) := rfl

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
