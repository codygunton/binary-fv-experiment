import BinaryFv.Zesu.ProofProgress.Level4MachineProofManifests

open BinaryFv.Zesu.ProofProgress

private def exactPcUnion : List Nat :=
  (level4MachineProofManifests.flatMap (·.pcs)).eraseDups

private def output : Lean.Json :=
  Lean.Json.mkObj [
    ("schemaVersion", 1),
    ("owner", "ssz_raw.decodeRaw"),
    ("ownerInstructionCount", 172),
    ("formalCoverage", Lean.Json.mkObj [
      ("localPcCount", exactPcUnion.length),
      ("level4PcCount", 0),
      ("rootPcCount", 0)
    ]),
    ("manifests", Lean.Json.arr <| level4MachineProofManifests.toArray.map (·.toJson))
  ]

#eval IO.println s!"MACHINE_PROOF_MANIFEST_JSON={output.compress}"
