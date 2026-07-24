import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Runner
import BinaryFv.SSZ.Zesu.Validation.MeaningAgreement

/-!
# Is the value observer actually sensitive to the layout?

`observe_raw_v4_of_rep` proves the observer reads back whatever the representation says is in memory.
That direction cannot catch an observer that ignores a field: one which never looked at
`parentHash` would still satisfy the correspondence for every state where `parentHash` happens to
match. What rules that out is the other direction — corrupt a byte and check the observation moves.

So this module takes the memory a **real accepted decode** leaves behind (the pinned binary, run in
the Sail model) and corrupts one byte per layout family, checking each time that the observation
changes: either it now reports a different value, or it fails outright. The families are the ones
the plan enumerates — fixed field, optional tag, optional payload, slice pointer, slice length, list
count, list base, and nested base — each at an address the ABI pins.

The negative control matters as much as the mutations. Corrupting the payload of an **absent**
optional changes nothing, because an absent option's payload is deliberately unconstrained by the
representation and never read by the observer. That one case proves the checks below are detecting
real dependence rather than the trivial fact that any change perturbs everything.

Like the other `Validation` modules this is falsification evidence, never a proof premise.
-/

namespace BinaryFv.SSZ.Zesu.Validation

open BinaryFv.SSZ
open BinaryFv.SSZ.Zesu
open BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.RiscV
open PreSail

/-- The corpus case used here: the accepted V4 input with *non-empty* collections. That matters —
against a case whose lists are all empty, corrupting a list base or a slice pointer changes nothing,
because a zero count means the pointer is never followed. -/
def mutationCase : ByteArray :=
  match GeneratedCorpus.corpus.find? (fun c => c.1 == "valid-v4-raw") with
  | some c => hexToBytes c.2.2
  | none => ByteArray.empty

/-- The machine memory a real accepted decode leaves behind. -/
def acceptedFinalState? : Option State :=
  match (do
      buildZesuEntryState mutationCase
      let _ ← runToOutcome sentinelWord (zesuFuel mutationCase.size) 0
      EStateM.get : SailM State).run initialState with
  | .ok final _ => some final
  | .error _ _ => none

/-- The observed value, rendered so two observations can be compared. -/
def observedRender? (state : State) : Option String :=
  (observeRawV4? state Elfling.canonicalResultBuffer).map (·.render)

/-- Overwrite one byte of machine memory. -/
def corruptByte (state : State) (address value : Nat) : State :=
  { state with mem := state.mem.insert address (BitVec.ofNat 8 value) }

/-- One corruption: which layout family it belongs to, the offset from the result base, and the
byte written there. Tag bytes are corrupted to `7`, which is neither of the two documented
discriminant values, so the tag guard is what has to reject it. -/
structure LayoutMutation where
  family : String
  offset : Nat
  byte : Nat

/-- One corruption per layout family, at offsets the ABI pins (the same ones `RawV4FixedFieldsRep`
and `RawV4DescriptorRep` name). -/
def layoutMutations : List LayoutMutation :=
  [ { family := "fixed vector byte (parent_hash)",        offset := 152, byte := 0xAA },
    { family := "fixed scalar (block_number)",            offset := 32,  byte := 0xAA },
    { family := "slice pointer (extra_data)",             offset := 64,  byte := 0xAA },
    { family := "slice length (extra_data)",              offset := 72,  byte := 0xAA },
    { family := "list base (transactions)",               offset := 80,  byte := 0xAA },
    { family := "list count (transactions)",              offset := 88,  byte := 0xAA },
    { family := "nested base (withdrawals)",              offset := 96,  byte := 0xAA },
    { family := "nested base (public_keys)",              offset := 816, byte := 0xAA },
    { family := "list count (public_keys)",               offset := 824, byte := 0xAA },
    { family := "nested scalar (chain_config.fork)",      offset := 744, byte := 0xAA },
    { family := "optional tag (activation.block_number)", offset := 760, byte := 0x07 },
    { family := "optional tag (blob_schedule)",           offset := 808, byte := 0x07 },
    { family := "optional payload, present (blob_schedule.target)", offset := 784, byte := 0xAA } ]

/-- The payload of an **absent** optional: `activation.block_number`, whose tag reads `0` in this
case. The representation leaves it unconstrained and the observer never reads it, so corrupting it
must change nothing. -/
def absentOptionPayloadOffset : Nat := 752

/-- The whole evidence, computed from a single decode: the unmutated state observes; every layout
mutation changes the observation; and the absent optional's payload does not. -/
def observerMutationEvidence : Bool :=
  match acceptedFinalState? with
  | none => false
  | some final =>
    match observedRender? final with
    | none => false
    | some baseline =>
      let changed (mutation : LayoutMutation) : Bool :=
        match observedRender?
            (corruptByte final (Elfling.canonicalResultBuffer + mutation.offset) mutation.byte) with
        | none => true
        | some other => other != baseline
      let absentPayloadUnread : Bool :=
        observedRender?
            (corruptByte final (Elfling.canonicalResultBuffer + absentOptionPayloadOffset) 0xAA)
          == some baseline
      layoutMutations.all changed && absentPayloadUnread

/-- **The observer depends on every layout family, and only on what the representation constrains.**

Thirteen corruptions of a real post-decode memory, one per family, each of which the observer
notices — by reporting a different value or by refusing to report one. Plus the control: the payload
of an absent optional can be corrupted freely without moving the observation, which is exactly what
the representation promises about it. -/
theorem observer_detects_every_layout_family : observerMutationEvidence = true := by native_decide

/-- Per-mutation detail, for diagnosing a failure of the theorem above. Not used by any check, so it
costs nothing unless evaluated. -/
def mutationReport : List (String × Bool) :=
  match acceptedFinalState?, acceptedFinalState?.bind observedRender? with
  | some final, some baseline =>
    layoutMutations.map fun mutation =>
      (mutation.family,
        match observedRender?
            (corruptByte final (Elfling.canonicalResultBuffer + mutation.offset) mutation.byte) with
        | none => true
        | some other => other != baseline)
  | _, _ => []

end BinaryFv.SSZ.Zesu.Validation
