import Lean.Data.Json

namespace BinaryFv.ProofProgress

/-- How far a kernel-checked local machine proof is connected into a public proof. -/
inductive ProofConnection where
  | local
  | selectedLevel
  | root
  deriving DecidableEq, Repr

def ProofConnection.label : ProofConnection → String
  | .local => "local"
  | .selectedLevel => "selected-level"
  | .root => "root"

/-- A proof-bearing registry row for one exact machine-code region.

The exporter erases `compositionClaim` and its proof, but can run only after Lean accepts the record.
`exactRegion` ties the trace-confinement predicate to the displayed PC list. -/
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

end BinaryFv.ProofProgress
