import BinaryFv
import Evm.Lib.Ssz.StatelessInput

/-!
# EVM-Sail SSZ decoding specification

The reference decoder is the pinned EVM-Sail computation itself.  This file does not restate SSZ:
`SailDecode` records successful execution of `decode_stateless_input_ref` followed by
`decode_stateless_input` from concrete input bytes.  Transaction comparison will additionally run
`decode_transaction` pairwise when the common decoded-result relation is introduced.
-/

namespace BinaryFv.Specs.SSZ

open Sail Evm Evm.Defs Evm.Functions

def modelBytes (input : Array UInt8) : Array byte :=
  input.map fun value => BitVec.ofNat 8 value.toNat

structure SailDecoded where
  inputRef : Evm.Defs.StatelessInputRef
  input : Evm.Defs.StatelessInput
  transactions : Array Evm.Defs.Transaction
  rawTransactions : Array Evm.Defs.StatelessInputSlice
  versionedHashes : Array Evm.Defs.StatelessInputSlice
  withdrawals : Array Evm.Defs.Withdrawal
  witnessNodes : Array Evm.Defs.StatelessInputSlice
  witnessCodes : Array Evm.Defs.StatelessInputSlice
  witnessHeaders : Array Evm.Defs.StatelessInputSlice
  publicKeys : Array Evm.Defs.StatelessInputSlice

private def collectVariableItems {maximum : Nat} (items : Evm.Defs.BoundedSszListRef maximum) :
    Evm.SailM (Array Evm.Defs.StatelessInputSlice) := do
  let mut result := #[]
  for index in [0:items.count] do
    result := result.push (← ssz_list_at items index)
  pure result

private def collectWithdrawals (items : Evm.Defs.WithdrawalListRef) :
    Evm.SailM (Array Evm.Defs.Withdrawal) := do
  let mut result := #[]
  for index in [0:items.count] do
    let item ← ssz_fixed_list_at items index 44
    result := result.push (← decode_withdrawal item)
  pure result

private def collectFixedItems {maximum : Nat} (items : Evm.Defs.BoundedSszListRef maximum)
    (width : Nat) : Evm.SailM (Array Evm.Defs.StatelessInputSlice) := do
  let mut result := #[]
  for index in [0:items.count] do
    result := result.push (← ssz_fixed_list_at items index width)
  pure result

private def collectTransactions (inputRef : Evm.Defs.StatelessInputRef) :
    Evm.SailM (Array Evm.Defs.Transaction) := do
  let publicKeys : Evm.Defs.BoundedSszListRef (2 ^ 20) := {
    bytes := inputRef.public_keys
    count := inputRef.transactions.count
    max_item_length := 65
  }
  let mut result := #[]
  for index in [0:inputRef.transactions.count] do
    let ⟨_, ⟨_, transaction⟩⟩ ← ssz_list_at inputRef.transactions index
    let ⟨publicKeyOffset, _⟩ ← ssz_fixed_list_at publicKeys index 65
    let publicKey : Evm.Defs.StatelessInputSliceFields publicKeyOffset 65 := {}
    result := result.push (← decode_transaction transaction publicKey)
  pure result

def sailDecodeAction (inputLength : Nat) : Evm.SailM SailDecoded := do
  let inputRef ← decode_stateless_input_ref ⟨0, ⟨inputLength, {}⟩⟩
  let input ← decode_stateless_input inputRef
  pure {
    inputRef
    input
    transactions := ← collectTransactions inputRef
    rawTransactions := ← collectVariableItems inputRef.transactions
    versionedHashes := ← do
      let items ← ssz_bounded_fixed_list_ref inputRef.versioned_hashes 32 4096
      collectFixedItems items 32
    withdrawals := ← collectWithdrawals inputRef.withdrawals
    witnessNodes := ← collectVariableItems inputRef.witness_state
    witnessCodes := ← collectVariableItems inputRef.witness_codes
    witnessHeaders := ← collectVariableItems inputRef.witness_headers
    publicKeys := ← do
      let items : Evm.Defs.BoundedSszListRef (2 ^ 20) := {
        bytes := inputRef.public_keys
        count := inputRef.transactions.count
        max_item_length := 65
      }
      collectFixedItems items 65
  }

/-- The concrete EVM-Sail decode relation used by the compliance theorem. -/
def SailDecode (input : Array UInt8) (decoded : SailDecoded) : Prop :=
  let initial := { Evm.initialHostState with inputBytes := modelBytes input }
  ∃ finalHost finalSailState,
    ((sailDecodeAction input.size).run initial).run default =
      .ok (decoded, finalHost) finalSailState

/-- The four-byte Ere length prefix is transport framing, not a semantic exception. -/
def stripErePrefix (input : Array UInt8) : Option (Array UInt8) := do
  if input.size < 4 then none else
  let length := (input[0]!).toNat + 256 * (input[1]!).toNat +
    65536 * (input[2]!).toNat + 16777216 * (input[3]!).toNat
  if length = input.size - 4 then some (input.extract 4 input.size) else none

end BinaryFv.Specs.SSZ
