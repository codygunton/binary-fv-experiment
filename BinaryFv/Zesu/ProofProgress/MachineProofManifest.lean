import Lean.Data.Json

namespace BinaryFv.Zesu.ProofProgress

/-- How far a kernel-checked local machine proof has been connected into the public proof. -/
inductive ProofConnection where
  | local
  | level4
  | root
  deriving DecidableEq, Repr

def ProofConnection.label : ProofConnection → String
  | .local => "local"
  | .level4 => "level4"
  | .root => "root"

/-- A proof-bearing registry row for one exact machine-code region.

`compositionClaim` is deliberately stored beside its proof.  The JSON exporter erases both the
claim and proof, but it can only run after Lean has accepted the concrete record.  `exactRegion`
ties the predicate used by that claim's trace confinement to the displayed PC list. -/
structure MachineProofManifest where
  id : String
  owner : String
  sourceIdentity : String
  theoremName : String
  theoremFile : String
  instructionSchema : String
  frameSchema : String
  prerequisiteContracts : List String
  pcs : List Nat
  region : BitVec 64 → Prop
  exactRegion : ∀ pc, region pc ↔ pc.toNat ∈ pcs
  compositionClaim : Prop
  composition : compositionClaim
  connection : ProofConnection

def MachineProofManifest.toJson (manifest : MachineProofManifest) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", manifest.id),
    ("owner", manifest.owner),
    ("sourceIdentity", manifest.sourceIdentity),
    ("theorem", manifest.theoremName),
    ("theoremFile", manifest.theoremFile),
    ("instructionSchema", manifest.instructionSchema),
    ("frameSchema", manifest.frameSchema),
    ("prerequisiteContracts", Lean.Json.arr <| manifest.prerequisiteContracts.toArray.map Lean.toJson),
    ("pcs", Lean.Json.arr <| manifest.pcs.toArray.map Lean.toJson),
    ("connection", manifest.connection.label)
  ]

end BinaryFv.Zesu.ProofProgress
