import BinaryFv
import Evm.Lib.Ssz.StatelessInput

/-!
# SSZ spike specification boundary

The reference decoder is the pinned EVM-Sail computation itself.  This file does not restate SSZ:
`SailDecode` records successful execution of `decode_stateless_input_ref` followed by
`decode_stateless_input` from concrete input bytes.  Transaction comparison will additionally run
`decode_transaction` pairwise when the common decoded-result relation is introduced.
-/

namespace BinaryFv.Ssz

open Sail Evm Evm.Defs Evm.Functions

def modelBytes (input : Array UInt8) : Array byte :=
  input.map fun value => BitVec.ofNat 8 value.toNat

def sailDecodeAction (inputLength : Nat) : Evm.SailM Evm.Defs.StatelessInput := do
  let inputRef ← decode_stateless_input_ref ⟨0, ⟨inputLength, {}⟩⟩
  decode_stateless_input inputRef

/-- The concrete EVM-Sail decode relation used by the compliance theorem. -/
def SailDecode (input : Array UInt8) (decoded : Evm.Defs.StatelessInput) : Prop :=
  let initial := { Evm.initialHostState with inputBytes := modelBytes input }
  ∃ finalHost finalSailState,
    ((sailDecodeAction input.size).run initial).run default =
      .ok (decoded, finalHost) finalSailState

/-- Reviewed divergence classes between the pinned Zesu and EVM-Sail revisions. -/
inductive KnownBug where
  | chainIdZeroNormalization
  | requestTableArity
  | legacyPayloadAndForkActivation
  | protocolListBounds
  | publicKeyCount
  | transactionAndBlobLimits
  deriving DecidableEq, Repr

/-- The fixed exception set.  Callers of `root_compliance` cannot add exceptions. -/
def knownBugs : List KnownBug :=
  [.chainIdZeroNormalization, .requestTableArity, .legacyPayloadAndForkActivation,
    .protocolListBounds, .publicKeyCount, .transactionAndBlobLimits]

theorem mem_knownBugs (bug : KnownBug) : bug ∈ knownBugs := by
  cases bug <;> decide

/-- The four-byte Ere length prefix is transport framing, not a semantic exception. -/
def stripErePrefix (input : Array UInt8) : Option (Array UInt8) := do
  if input.size < 4 then none else
  let length := (input[0]!).toNat + 256 * (input[1]!).toNat +
    65536 * (input[2]!).toNat + 16777216 * (input[3]!).toNat
  if length = input.size - 4 then some (input.extract 4 input.size) else none

end BinaryFv.Ssz
