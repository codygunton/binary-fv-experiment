/-
Emits the falsification-evidence tables under `BinaryFv/SSZ/Zesu/Validation/` as a markdown report.

Not part of any lake library or executable target: `tools/` is outside every `lean_lib` root, so this
file is only ever elaborated when run explicitly. Regenerate the committed report with

    lake env lean tools/emit_ground_truth_report.lean > targets/ssz/zesu/trace/CONTRACT_GROUND_TRUTH.md

The numbers it prints are produced by the same definitions the modules pin with `native_decide`, so
the text cannot disagree with the kernel-checked constants without the build failing first.
-/
import BinaryFv.SSZ.Zesu.Validation.BoundarySatisfiability
import BinaryFv.SSZ.Zesu.Validation.ContractGroundTruth

open BinaryFv.SSZ.Zesu.Validation

def preamble : String := String.intercalate "\n"
  [ "# Contract ground truth — per function instance"
  , ""
  , "GENERATED. Regenerate with"
  , ""
  , "```"
  , "lake env lean tools/emit_ground_truth_report.lean \\"
  , "  > targets/ssz/zesu/trace/CONTRACT_GROUND_TRUTH.md"
  , "```"
  , ""
  , "This is **falsification evidence about the pinned artifact**, never a proof premise. Every"
  , "number below is computed by a definition that a `native_decide` theorem in the same module also"
  , "pins to an exact value, so this file cannot drift from the kernel-checked constants without"
  , "`lake build BinaryFv.SSZ.Zesu.Validation.BoundarySatisfiability` or"
  , "`… .ContractGroundTruth` failing."
  , ""
  , "A `gap` is never a pass. It means the row was not decided, and the reason is printed with it."
  , ""
  ]

def emitReport : IO Unit := do
  IO.println preamble
  IO.println Boundary.report
  IO.println GroundTruth.report

#eval emitReport
