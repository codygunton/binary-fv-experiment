import SszBridge.Core
import Lean.Data.Json

/-!
# Row B Lean runner over the pinned decode spec

A **validation-only** executable that reads the `ssz-contract-corpus-v1` JSONL corpus and, for each
top-level `ssz_raw.decode` case, runs the pinned oracle `SszBridge.decodeStatelessInput` and emits a
canonical JSONL outcome. The host Zig probe over the pinned decoder must emit the same outcomes;
agreement is the oracle≈Zig half of Row B (the meanings≈oracle half is a kernel-checked Lean check —
see `Validation/MeaningAgreement.lean`).

This module imports only the Sail-free pinned spec, so it can be an executable (the Sail model carries
a top-level `main`; see `DECISIONS.md`). It is **not** imported by the theorem umbrella (`BinaryFv`).
-/

namespace BinaryFv.SSZ.Zesu.Validation

open SszBridge
open Lean (Json)

/-- A single hex digit's value. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + (c.toNat - 'a'.toNat))
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + (c.toNat - 'A'.toNat))
  else none

/-- Decode a lowercase/uppercase hex string to bytes. Iterative, so a multi-megabyte case does not
overflow the runtime stack. -/
def hexToBytes? (s : String) : Option ByteArray := Id.run do
  let cs := s.toList.toArray
  if cs.size % 2 ≠ 0 then return none
  let mut out := ByteArray.empty
  let mut i := 0
  while h : i + 1 < cs.size do
    match hexDigit? cs[i]!, hexDigit? cs[i + 1]! with
    | some hi, some lo => out := out.push (UInt8.ofNat (hi * 16 + lo)); i := i + 2
    | _, _ => return none
  return some out

/-- The canonical JSONL outcome of decoding one case. A success carries the exact `ssz-value-v1`
render of the decoded value; a rejection carries the exact error label. -/
def decodeOutcome (id : String) (input : ByteArray) : Json :=
  match decodeStatelessInput input with
  | .ok value =>
      Json.mkObj [("id", Json.str id), ("routine", Json.str "ssz_raw.decode"),
        ("outcome", Json.str "accept"), ("value", Json.str value.render)]
  | .error e =>
      Json.mkObj [("id", Json.str id), ("routine", Json.str "ssz_raw.decode"),
        ("outcome", Json.str "reject"), ("error", Json.str e.label)]

/-- Extract a top-level string field, or `""` if absent. -/
def strField (j : Json) (key : String) : String :=
  (j.getObjVal? key |>.bind Json.getStr?).toOption.getD ""

/-- Extract a nested string field `j[k1][k2]`, or `""` if absent. -/
def nestedStrField (j : Json) (k1 k2 : String) : String :=
  ((j.getObjVal? k1).bind (·.getObjVal? k2) |>.bind Json.getStr?).toOption.getD ""

/-- Run one corpus line and print its canonical outcome, if it is a `ssz_raw.decode` case. -/
def runLine (line : String) : IO Unit := do
  match Json.parse line with
  | .error _ => pure ()
  | .ok j =>
      if strField j "routine" == "ssz_raw.decode" then
        match hexToBytes? (nestedStrField j "args" "input") with
        | some input => IO.println (decodeOutcome (strField j "id") input).compress
        | none => pure ()

def runCorpus (corpusPath : String) : IO UInt32 := do
  let content ← IO.FS.readFile corpusPath
  for line in content.splitOn "\n" do
    if line.trim ≠ "" then runLine line
  pure 0

end BinaryFv.SSZ.Zesu.Validation

/-- Executable entry point: `ssz_contract_runner <corpus.jsonl>`. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [corpusPath] => BinaryFv.SSZ.Zesu.Validation.runCorpus corpusPath
  | _ => do IO.eprintln "usage: ssz_contract_runner <corpus.jsonl>"; pure 64

