import Lake

open Lake DSL System

unsafe def runPkgConfig (args : Array String) (fallback : Array String) : Array String :=
  Id.run <| unsafeBaseIO do
    let result ← (IO.Process.output { cmd := "pkg-config", args }).toBaseIO
    match result with
    | .ok response =>
        if response.exitCode == 0 then
          let output := response.stdout.trimAscii.toString
          if output.isEmpty then
            return fallback
          return (output.splitOn " ").toArray.filter (fun arg => !arg.isEmpty)
        else
          return fallback
    | .error _ => return fallback

unsafe def opensslLinkArgs : Array String :=
  let libraryDirs := runPkgConfig #["--variable=libdir", "libcrypto"] #[]
  let libraries := runPkgConfig #["--libs", "libcrypto"] #["-lcrypto"]
  (libraryDirs.map (fun directory => "-L" ++ directory)) ++ libraries

package sszBridge where
  moreLinkArgs := unsafe opensslLinkArgs

require repl from git "https://github.com/leanprover-community/repl.git" @ "v4.29.0"
require SizzLean from git "https://github.com/etheorem/etheorem.git" @
  "032ab6c6d67186ba60b734e0f2c44ba1bb8b6fb0" / "packages/SizzLean"

lean_lib SszBridge

lean_exe ssz_bridge where
  root := `SszBridge.Main

lean_exe ssz_bridge_test where
  root := `SszBridgeTest
