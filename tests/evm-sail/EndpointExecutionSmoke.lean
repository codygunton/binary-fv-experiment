import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Executable

open BinaryFv.Zesu

private def endpointExecutionSmoke (path : System.FilePath) : IO Unit := do
  let input := (← IO.FS.readBinFile path).data
  match RiscvSpec.execute zesuSszBinary input with
  | .decoded _ => pure ()
  | outcome => throw (IO.userError s!"endpoint execution failed for {path}: {repr outcome}")

def endpointExecutionSmokeMain (paths : List String) : IO Unit :=
  paths.forM fun path => endpointExecutionSmoke path

#eval endpointExecutionSmokeMain ["@MINIMAL@", "@TRANSACTION@", "@WITHDRAWAL@"]
