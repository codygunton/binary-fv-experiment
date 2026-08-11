import BinaryFv.Ssz.Relation

open BinaryFv.Ssz

private def readSuccess (path : System.FilePath) : IO ZesuDecodedResult := do
  let bytes ← IO.FS.readBinFile path
  match decodeZesuObservation bytes.data with
  | some (.success decoded) => pure decoded
  | _ => throw (IO.userError s!"invalid success observation: {path}")

private def runSail (input : Array UInt8) : IO SailDecoded := do
  let initial := { Evm.initialHostState with inputBytes := modelBytes input }
  match ((sailDecodeAction input.size).run initial).run default with
  | .ok (decoded, _) _ => pure decoded
  | .error .. => throw (IO.userError "EVM-Sail rejected the shared accepted fixture")

def differentialSmokeMain (arguments : List String) : IO Unit := do
  let [inputPath, observationPath, changedPath, zeroInputPath, zeroObservationPath] := arguments
    | throw (IO.userError "expected ordinary and zero-chain differential fixtures")
  let input := (← IO.FS.readBinFile inputPath).data
  let zesu ← readSuccess observationPath
  let sail ← runSail input
  unless decodedResultRel input zesu sail do
    throw (IO.userError "Zesu and EVM-Sail common decoded results differ")
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

#eval differentialSmokeMain
  ["@INPUT@", "@SUCCESS@", "@CHANGED@", "@ZERO_INPUT@", "@ZERO_SUCCESS@"]
