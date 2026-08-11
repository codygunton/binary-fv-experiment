import BinaryFv.Zesu.ProofProgress.Level4MachineProofManifests

open BinaryFv.Zesu.ProofProgress
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

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
    ("phases", Lean.Json.arr #[
      Lean.Json.mkObj [("id", "entry-envelope-offsets"),
        ("label", "entry, envelope, and four readOffset occurrences"),
        ("pcs", Lean.Json.arr <| decodeRawEntryEnvelopeOffsetsPcs.toArray.map Lean.toJson)],
      Lean.Json.mkObj [("id", "specialized-dispatch-success"),
        ("label", "specialized dispatch, returns, and success construction"),
        ("pcs", Lean.Json.arr <| decodeRawSpecializedDispatchReturnsSuccessPcs.toArray.map Lean.toJson)],
      Lean.Json.mkObj [("id", "rejection-cleanup-epilogue"),
        ("label", "rejection, cleanup, status copy, and epilogue"),
        ("pcs", Lean.Json.arr <| decodeRawRejectionCleanupStatusCopyEpiloguePcs.toArray.map Lean.toJson)]
    ]),
    ("manifests", Lean.Json.arr <| level4MachineProofManifests.toArray.map (·.toJson))
  ]

#eval IO.println s!"MACHINE_PROOF_MANIFEST_JSON={output.compress}"
