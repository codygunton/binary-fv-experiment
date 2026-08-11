import BinaryFv.Ssz.Relation

open BinaryFv.Ssz

private def readSuccess (path : System.FilePath) : IO ZesuDecodedResult := do
  let bytes ← IO.FS.readBinFile path
  match decodeZesuObservation bytes.data with
  | some (.success decoded) => pure decoded
  | _ => throw (IO.userError s!"invalid success observation: {path}")

private def tryRunSail (input : Array UInt8) : Option SailDecoded :=
  let initial := { Evm.initialHostState with inputBytes := modelBytes input }
  match ((sailDecodeAction input.size).run initial).run default with
  | .ok (decoded, _) _ => some decoded
  | .error .. => none

private def runSail (input : Array UInt8) : IO SailDecoded := do
  match tryRunSail input with
  | some decoded => pure decoded
  | none => throw (IO.userError "EVM-Sail rejected the shared accepted fixture")

def differentialSmokeMain (arguments : List String) : IO Unit := do
  let [inputPath, observationPath, changedPath, zeroInputPath, zeroObservationPath,
      legacyInputPath, legacyObservationPath] := arguments
    | throw (IO.userError "expected ordinary and zero-chain differential fixtures")
  let input := (← IO.FS.readBinFile inputPath).data
  let zesu ← readSuccess observationPath
  let sail ← runSail input
  unless decodedResultRel input zesu sail do
    throw (IO.userError "Zesu and EVM-Sail common decoded results differ")
  for bug in knownBugs do
    if KnownBugApplies input zesu bug then
      throw (IO.userError s!"ordinary fixture matched compatibility domain: {repr bug}")
  let changed ← readSuccess changedPath
  if decodedResultRel input changed sail then
    throw (IO.userError "common-result checker accepted a mutated block number")
  let zeroInput := (← IO.FS.readBinFile zeroInputPath).data
  let zeroZesu ← readSuccess zeroObservationPath
  let zeroSail ← runSail zeroInput
  if decodedResultRel zeroInput zeroZesu zeroSail then
    throw (IO.userError "exact relation hid the zero-chain-id divergence")
  unless decodedResultRelModuloKnownBugs zeroInput zeroZesu zeroSail do
    throw (IO.userError "fixed zero-chain-id clause did not admit its exact divergence")
  let legacyInput := (← IO.FS.readBinFile legacyInputPath).data
  let legacyZesu ← readSuccess legacyObservationPath
  unless (tryRunSail legacyInput).isNone do
    throw (IO.userError "EVM-Sail accepted the legacy three-request table")
  unless KnownBugApplies legacyInput legacyZesu .legacyRequestTableArity do
    throw (IO.userError "legacy request fixture missed its fixed domain classifier")

private def assertAcceptanceDivergence (bug : KnownBug)
    (inputPath observationPath : System.FilePath) : IO Unit := do
  let input := (← IO.FS.readBinFile inputPath).data
  let zesu ← readSuccess observationPath
  unless (tryRunSail input).isNone do
    throw (IO.userError s!"EVM-Sail accepted divergence fixture {inputPath}")
  unless KnownBugApplies input zesu bug do
    throw (IO.userError s!"fixture missed its fixed domain classifier: {repr bug}")

#eval differentialSmokeMain
  ["@INPUT@", "@SUCCESS@", "@CHANGED@", "@ZERO_INPUT@", "@ZERO_SUCCESS@",
    "@LEGACY_INPUT@", "@LEGACY_SUCCESS@"]

#eval assertAcceptanceDivergence .legacyPayloadSize "@V3_INPUT@" "@V3_SUCCESS@"
#eval assertAcceptanceDivergence .futureForkActivation "@FUTURE_INPUT@" "@FUTURE_SUCCESS@"
#eval assertAcceptanceDivergence .extraDataLength "@EXTRA_INPUT@" "@EXTRA_SUCCESS@"
#eval assertAcceptanceDivergence .publicKeyCount "@KEYS_INPUT@" "@KEYS_SUCCESS@"
#eval assertAcceptanceDivergence .versionedHashCount "@HASHES_INPUT@" "@HASHES_SUCCESS@"
