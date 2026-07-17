import BinaryFv.Keccak.Reth.Artifact.Facts.Words
import BinaryFv.Keccak.Reth.Execution.DirectCall
import BinaryFv.RiscV.ELF.CFG

namespace BinaryFv.Keccak

open BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

def decodeWithCanonicalConfiguration (words : Array EncodedWord) : Option (Array DecodedWord) :=
  match (do
    configureDirectCallMachine
    decodeWords words).run initialState with
  | .ok decoded _ => some decoded
  | .error _ _ => none

def artifactDecodedWords? : Option (Array DecodedWord) :=
  match artifactWords with
  | .ok words => decodeWithCanonicalConfiguration words
  | .error _ => none

def portableCoreDecodedWords? : Option (Array DecodedWord) :=
  match portableCoreWords with
  | .ok words => decodeWithCanonicalConfiguration words
  | .error _ => none

def artifactControlFlow? : Option (Array ControlFlowNode) :=
  artifactDecodedWords?.map controlFlowNodes

def portableCoreControlFlow? : Option (Array ControlFlowNode) :=
  portableCoreDecodedWords?.map controlFlowNodes

def artifactControlFlowResolves : Bool :=
  artifactControlFlow?.isSome

def artifactDirectTargetsPresent : Bool :=
  match artifactControlFlow? with
  | some nodes => directTargetsPresent nodes
  | none => false

def directEntryReachesPortableCore : Bool :=
  match Artifact.entryAddress, portableCore, artifactControlFlow? with
  | .ok entry, .ok core, some nodes =>
    (directReachable nodes entry).any fun address => address == core.value
  | _, _, _ => false

/-- Decode the fixed artifact only after the canonical normal direct-call configuration. -/
def artifactWordsLegal : Bool :=
  match artifactDecodedWords? with
  | some decoded => decoded.all DecodedWord.legal
  | none => false

/-- Closed coverage fact: no executable base word in the embedded artifact decodes as illegal. -/
theorem artifact_words_legal : artifactWordsLegal = true := by
  native_decide

theorem portable_core_resolves : portableCore.isOk = true := by
  native_decide

theorem artifact_control_flow_resolves : artifactControlFlowResolves = true := by
  native_decide

theorem artifact_direct_targets_present : artifactDirectTargetsPresent = true := by
  native_decide

theorem direct_entry_reaches_portable_core : directEntryReachesPortableCore = true := by
  native_decide

end BinaryFv.Keccak
