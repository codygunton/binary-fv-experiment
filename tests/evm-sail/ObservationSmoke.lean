import BinaryFv.Zesu.DecodedValue.Observers

open BinaryFv.Zesu

private def readObservation (path : System.FilePath) : IO ZesuObservation := do
  let bytes ← IO.FS.readBinFile path
  match decodeZesuObservation bytes.data with
  | some observation => pure observation
  | none => throw (IO.userError s!"invalid observation: {path}")

def observationSmokeMain (arguments : List String) : IO Unit := do
  let [successPath, failurePath, changedPath] := arguments
    | throw (IO.userError "expected success, failure, and changed observation paths")
  let .success success ← readObservation successPath
    | throw (IO.userError "minimal input did not produce a success observation")
  let .failure ← readObservation failurePath
    | throw (IO.userError "invalid schema did not produce the exact failure observation")
  let .success changed ← readObservation changedPath
    | throw (IO.userError "block-number mutation did not produce a success observation")
  unless success.chainConfig.chainId = 1 do
    throw (IO.userError "minimal observation has the wrong chain id")
  unless success.payload.blockNumber = 0 && changed.payload.blockNumber = 1 do
    throw (IO.userError "block-number mutation was not reflected by the typed decoder")
  let encoded ← IO.FS.readBinFile successPath
  unless decodeZesuObservation (encoded.data.push 0) = none do
    throw (IO.userError "typed decoder accepted trailing bytes")
  unless decodeZesuObservation encoded.data.pop = none do
    throw (IO.userError "typed decoder accepted a truncated observation")

#eval observationSmokeMain ["@SUCCESS@", "@FAILURE@", "@CHANGED@"]
