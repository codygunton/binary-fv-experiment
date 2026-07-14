import SszBridge.Core

namespace SszBridge

/-- Read one raw V4 fixture and print the complete `ssz-value-v1` raw value. -/
def run (args : List String) : IO UInt32 :=
  match args with
  | [path] => do
      let input ← IO.FS.readBinFile path
      match decodeStatelessInput input with
      | .ok normalized =>
          IO.println normalized.render
          pure 0
      | .error error =>
          IO.println s!"error\t{error.label}"
          pure 1
  | _ => do
      IO.eprintln "usage: ssz_bridge <raw-ssz-fixture>"
      pure 64

end SszBridge

def main (args : List String) : IO UInt32 := SszBridge.run args

