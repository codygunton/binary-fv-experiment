import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Executable

open BinaryFv.Zesu

def endpointExecutionSmoke (path : System.FilePath) : IO Unit := do
  let input := (← IO.FS.readBinFile path).data
  match RiscvSpec.execute zesuSszBinary input with
  | .decoded _ => pure ()
  | outcome => throw (IO.userError s!"minimal endpoint execution failed: {repr outcome}")

#eval endpointExecutionSmoke "@INPUT@"
